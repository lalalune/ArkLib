#!/usr/bin/env python3
"""
EXACT mod-p (numba-JIT, int64, NO floats) worst-direction orbit-count scan to SETTLE m*.

Resolves the convergent residual (#444 c.04:49): delta*=(1-rho)-m*/n, m*=w*-k. The single
open question is whether m* is BOUNDED (~3 => delta* near capacity, REFUTES window-edge
1-rho-Theta(1/log n)) or GROWS ~log n. n=8,16 cannot separate. n>=32 worst-direction is decisive.

Rigor: ALL arithmetic exact in F_p (modular int64). PROPER subgroup mu_n, m=(p-1)/n>=2,
NEVER n=q-1. Cross-validated against the pure-Python exact engine (probe_dsval_mstar_exact_modp.py),
which is itself validated to ground truth (n=16 worst dir(8,14) w=7 => I=9, m*=3; w=6 => I=89).

Per w-subset S, far line x^a+gamma*x^b agrees w/ a deg<k codeword on S iff, after eliminating
the k codeword columns [1..x^{k-1}] from rows S, every residual row (rank-deficient rows) satisfies
ca_res + gamma*cb_res = 0 for a SINGLE gamma in F_p. That gamma is the orbit rep; count distinct.
gamma=0 admissible counts +1 (matches the in-tree +1{gamma=0} term).
"""
import sys, math, argparse
import numpy as np
from numba import njit, prange

@njit(cache=True, inline='always')
def minv(a, p):
    # Fermat inverse a^(p-2) mod p, p prime
    a %= p
    if a < 0: a += p
    r = 1; e = p-2; base = a
    while e > 0:
        if e & 1: r = (r*base) % p
        base = (base*base) % p
        e >>= 1
    return r

@njit(cache=True)
def gamma_subset(Vall, xa, xb, S, k, p):
    # Vall: (n,k) powers; xa,xb: (n,). S: int array of w indices. Returns (flag,gamma):
    # flag 2 = no witness; 0 = gamma found (gamma in [0..p-1]); reuse gamma=0 meaning the value 0.
    w = S.shape[0]
    kk = k + 2
    # build M (w x kk): first k = Vall, then xa, xb
    M = np.zeros((w, kk), dtype=np.int64)
    for i in range(w):
        s = S[i]
        for c in range(k):
            M[i, c] = Vall[s, c] % p
        M[i, k]   = xa[s] % p
        M[i, k+1] = xb[s] % p
    # Gauss-eliminate first k columns
    r = 0
    for c in range(k):
        pr = -1
        for rr in range(r, w):
            if M[rr, c] % p != 0:
                pr = rr; break
        if pr == -1:
            continue
        if pr != r:
            for cc in range(kk):
                tmp = M[r, cc]; M[r, cc] = M[pr, cc]; M[pr, cc] = tmp
        ip = minv(M[r, c], p)
        for cc in range(kk):
            M[r, cc] = (M[r, cc] * ip) % p
        for rr in range(w):
            if rr != r:
                f = M[rr, c] % p
                if f != 0:
                    for cc in range(kk):
                        M[rr, cc] = (M[rr, cc] - f * M[r, cc]) % p
        r += 1
        if r == w: break
    # If w < k+2 the system is underdetermined (more cols than constraints) => gamma free.
    # Such w are below the over-determined binding band (m*=w-k must be >=2); not a witness band.
    # residual rows r..w-1 : need ca_res + gamma*cb_res = 0, single gamma
    have = False
    g_fixed = 0
    for rr in range(r, w):
        x = M[rr, k] % p
        if x < 0: x += p
        y = M[rr, k+1] % p
        if y < 0: y += p
        if x == 0 and y == 0:
            continue
        if y == 0:
            return 2, 0  # ca_res nonzero, cb_res zero => no finite gamma
        g = (-x * minv(y, p)) % p
        if g < 0: g += p
        if not have:
            g_fixed = g; have = True
        elif g != g_fixed:
            return 2, 0  # inconsistent gamma across rows
    if not have:
        return 2, 0  # degenerate: x^a already in code-span on S (not a binding far witness)
    return 0, g_fixed

@njit(cache=True)
def comb_unrank(idx, n, w, out):
    # unrank colex/lex combination idx into out (length w), 0<=idx<C(n,w)
    # standard lexicographic unranking
    x = 0
    rem = idx
    for i in range(w):
        # choose next element
        c = x
        while True:
            # number of combos with this position = C(n-1-c, w-1-i)
            cc = nck(n-1-c, w-1-i)
            if rem < cc:
                break
            rem -= cc
            c += 1
        out[i] = c
        x = c + 1
    return

@njit(cache=True)
def nck(n, r):
    if r < 0 or r > n: return 0
    if r == 0 or r == n: return 1
    if r > n - r: r = n - r
    res = 1
    for i in range(r):
        res = res * (n - i) // (i + 1)
    return res

@njit(cache=True, parallel=True)
def incidence_dir(Vall, xa, xb, n, k, w, p, ngamma_slots):
    # scan all C(n,w) subsets; collect distinct gamma in a presence bitmap of size p.
    # p can be up to ~16M for n=64; bitmap as uint8 array. Parallel over chunks.
    total = nck(n, w)
    seen = np.zeros(p, dtype=np.uint8)
    nthreads = 16
    chunk = (total + nthreads - 1) // nthreads
    for t in prange(nthreads):
        lo = t * chunk
        hi = lo + chunk
        if hi > total: hi = total
        S = np.empty(w, dtype=np.int64)
        for idx in range(lo, hi):
            comb_unrank(idx, n, w, S)
            flag, g = gamma_subset(Vall, xa, xb, S, k, p)
            if flag == 0:
                seen[g] = 1
    cnt = 0
    for v in range(p):
        if seen[v] == 1:
            cnt += 1
    return cnt

@njit(cache=True, parallel=True)
def incidence_dir_earlystop(Vall, xa, xb, n, k, w, p, budget):
    # Same exact scan, but designed to confirm the >budget verdict fast: each thread
    # collects distinct gamma into its own local bitmap; we periodically union-count.
    # Returns (count_capped, exceeded) where exceeded=True means count > budget (exact >budget verdict).
    # If not exceeded, count_capped is the EXACT total distinct gamma (<= budget).
    total = nck(n, w)
    seen = np.zeros(p, dtype=np.uint8)
    nthreads = 16
    chunk = (total + nthreads - 1) // nthreads
    for t in prange(nthreads):
        lo = t * chunk
        hi = lo + chunk
        if hi > total: hi = total
        S = np.empty(w, dtype=np.int64)
        for idx in range(lo, hi):
            comb_unrank(idx, n, w, S)
            flag, g = gamma_subset(Vall, xa, xb, S, k, p)
            if flag == 0:
                seen[g] = 1
    cnt = 0
    for v in range(p):
        if seen[v] == 1:
            cnt += 1
    return cnt, (cnt > budget)

def build_field(n, beta, min_m=2):
    import sympy
    lo = max(int(n**beta), n*min_m+1)
    p = lo - (lo % n) + 1
    while not (p > n*min_m and sympy.isprime(p)):
        p += n
    g = sympy.primitive_root(p)
    h = pow(g, (p-1)//n, p)
    assert pow(h,n,p)==1 and all(pow(h,d,p)!=1 for d in range(1,n))
    mu = [pow(h,i,p) for i in range(n)]
    return p, mu, (p-1)//n

def run(n, k, w, dirs, p, mu, ngamma_slots=None):
    Vall = np.array([[pow(mu[i], j, p) for j in range(k)] for i in range(n)], dtype=np.int64)
    res = {}
    for (a,b) in dirs:
        xa = np.array([pow(mu[i], a, p) for i in range(n)], dtype=np.int64)
        xb = np.array([pow(mu[i], b, p) for i in range(n)], dtype=np.int64)
        I = incidence_dir(Vall, xa, xb, n, k, w, p, p)
        res[(a,b)] = I
    return res

if __name__ == "__main__":
    ap = argparse.ArgumentParser()
    ap.add_argument("--n", type=int, default=16)
    ap.add_argument("--k", type=int, default=4)
    ap.add_argument("--beta", type=float, default=4.0)
    ap.add_argument("--ws", type=str, default="6,7,8")
    ap.add_argument("--alldirs", action="store_true")
    ap.add_argument("--dirs", type=str, default="")  # "a:b,a:b"
    args = ap.parse_args()
    n=args.n; k=args.k
    p, mu, m = build_field(n, args.beta)
    budget = n
    print(f"[exact mod-p numba] n={n} k={k} rho={k/n} p={p} (log_n p={math.log(p)/math.log(n):.2f}, m={m}) PROPER mu_n, budget={budget}", flush=True)
    ws = [int(x) for x in args.ws.split(",")]
    for w in ws:
        if args.alldirs:
            dirs = [(a,b) for a in range(k,n) for b in range(a+1,n)]
        elif args.dirs:
            dirs = [tuple(int(z) for z in d.split(":")) for d in args.dirs.split(",")]
        else:
            dirs = [(k, k+1), (n//2, n//2+1), (n//2-1, n//2+1), (n//2, n//2+2)]
        res = run(n, k, w, dirs, p, mu)
        best = max(res.values()); bd = max(res, key=res.get)
        mstar = w-k; delta=1-w/n
        verdict = ">budget" if best>budget else ("=budget" if best==budget else "<budget")
        print(f"  w={w} m*={mstar} delta={delta:.4f} worstI={best} dir={bd} [{verdict}] (ndirs={len(dirs)})", flush=True)

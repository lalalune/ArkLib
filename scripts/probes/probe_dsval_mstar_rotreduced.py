#!/usr/bin/env python3
"""
ROTATION-REDUCED exact mod-p worst-direction orbit-count scan (the n=32/64-feasible engine).

Symmetry: the cyclic dilation z -> h*z (h = generator of mu_n) acts on subsets S of mu_n.
A far-line witness (S, gamma) for direction (a,b) maps under z->h*z to (h.S, gamma * h^{(b-a)}):
  the codeword space [1..x^{k-1}] is dilation-invariant (deg<k -> deg<k); x^a -> h^a x^a,
  x^b -> h^b x^b, so x^a + gamma x^b agrees on S  <=>  x^a + (gamma h^{b-a}) x^b agrees on h.S.
Hence the set of witnessing gamma is CLOSED under multiplication by h^{(b-a)}, i.e. it is a union
of cosets of the cyclic subgroup <h^{(b-a)}> of order S_orb = n/gcd(b-a,n). So:
  I(a,b;w) = (#distinct gamma-orbits) * S_orb   [+ the gamma=0 fixed point if admissible].
Therefore we only need to enumerate subsets up to rotation: fix the LEX-MIN rotation representative
(equivalently, scan subsets and for each record gamma, but we can restrict to a transversal). The
clean exact reduction: scan ALL subsets that CONTAIN index 0 (x=1) -- every rotation orbit of subsets
has >=1 member containing 0 -- and for the gamma found, take its orbit under *h^{b-a}; union all such
orbits. This counts EVERY witnessing gamma exactly while scanning only C(n-1, w-1) subsets (n x fewer).

Validation: must reproduce the full-scan engine EXACTLY (n=16 dir(8,14) w=7 => 9, dir(9,15) w=6 => 89,
dir(8,9) w=7 => 16). NO floats; PROPER mu_n; NEVER n=q-1.
"""
import sys, math, argparse, time
import numpy as np
from numba import njit, prange

@njit(cache=True)
def nck(n, r):
    if r < 0 or r > n: return 0
    if r == 0 or r == n: return 1
    if r > n - r: r = n - r
    res = 1
    for i in range(r): res = res * (n - i) // (i + 1)
    return res

@njit(cache=True)
def comb_unrank(idx, n, w, out):
    rem = idx; x = 0
    for i in range(w):
        c = x
        while True:
            cc = nck(n-1-c, w-1-i)
            if rem < cc: break
            rem -= cc; c += 1
        out[i] = c; x = c + 1

@njit(cache=True)
def gamma_subset0(Vall, xa, xb, rest, w, k, p, INV):
    # subset = {0} ∪ rest (rest has w-1 indices in 1..n-1). builds rows incl index 0.
    kk = k + 2
    M = np.empty((w, kk), dtype=np.int64)
    for i in range(w):
        s = 0 if i == 0 else rest[i-1]
        for c in range(k): M[i, c] = Vall[s, c]
        M[i, k] = xa[s]; M[i, k+1] = xb[s]
    r = 0
    for c in range(k):
        pr = -1
        for rr in range(r, w):
            if M[rr, c] != 0: pr = rr; break
        if pr == -1: continue
        if pr != r:
            for cc in range(kk):
                tmp = M[r, cc]; M[r, cc] = M[pr, cc]; M[pr, cc] = tmp
        ip = INV[M[r, c]]
        for cc in range(kk): M[r, cc] = (M[r, cc] * ip) % p
        for rr in range(w):
            if rr != r:
                f = M[rr, c]
                if f != 0:
                    for cc in range(kk):
                        M[rr, cc] = (M[rr, cc] - f * M[r, cc]) % p
        r += 1
        if r == w: break
    have = False; g_fixed = 0
    for rr in range(r, w):
        x = M[rr, k] % p
        if x < 0: x += p
        y = M[rr, k+1] % p
        if y < 0: y += p
        if x == 0 and y == 0: continue
        if y == 0: return 2, 0
        g = (p - x) * INV[y] % p
        if not have: g_fixed = g; have = True
        elif g != g_fixed: return 2, 0
    if not have: return 2, 0
    return 0, g_fixed

@njit(cache=True, parallel=True)
def incidence_dir_rot(Vall, xa, xb, n, k, w, p, INV):
    # scan subsets containing index 0: choose w-1 from {1..n-1} => C(n-1,w-1) subsets.
    total = nck(n-1, w-1)
    seen = np.zeros(p, dtype=np.uint8)
    nthreads = 16
    chunk = (total + nthreads - 1) // nthreads
    for t in prange(nthreads):
        lo = t * chunk; hi = lo + chunk
        if hi > total: hi = total
        rest = np.empty(w-1, dtype=np.int64)
        for idx in range(lo, hi):
            comb_unrank(idx, n-1, w-1, rest)
            for j in range(w-1): rest[j] += 1   # shift to 1..n-1
            flag, g = gamma_subset0(Vall, xa, xb, rest, w, k, p, INV)
            if flag == 0: seen[g] = 1
    # now seen marks gamma found from subsets-containing-0. Expand each by the <h^{b-a}> orbit:
    # but since EVERY rotation orbit of subsets hits a 0-containing member, and gamma of a rotated
    # subset = gamma * h^{(b-a)}, the FULL gamma set is the closure of `seen` under *mult_factor.
    # We compute mult_factor outside; here just return raw seen count + the seen bitmap is expanded
    # by caller. To keep it simple+exact we instead return the count of the ORBIT-CLOSURE here.
    cnt = 0
    for v in range(p):
        if seen[v] == 1: cnt += 1
    return cnt, seen

def build_field(n, beta, min_m=2):
    import sympy
    lo = max(int(n**beta), n*min_m+1)
    p = lo - (lo % n) + 1
    while not (p > n*min_m and sympy.isprime(p)): p += n
    g = sympy.primitive_root(p)
    h = pow(g, (p-1)//n, p)
    assert pow(h,n,p)==1 and all(pow(h,d,p)!=1 for d in range(1,n))
    mu = [pow(h,i,p) for i in range(n)]
    return p, mu, (p-1)//n, h

def build_inv_table(p):
    INV = np.zeros(p, dtype=np.int64); INV[1] = 1
    for i in range(2, p): INV[i] = (-(p//i) * INV[p % i]) % p
    return INV

def orbit_closure_count(seen, h, step, n, p):
    # close `seen` (bitmap) under multiplication by mult = h^step mod p; count distinct.
    mult = pow(int(h), int(step), p)
    full = set()
    # collect raw seen gammas
    raw = np.nonzero(seen)[0]
    for g in raw:
        g = int(g)
        if g == 0:
            full.add(0); continue
        cur = g
        for _ in range(n):  # orbit size divides n
            if cur in full: break
            full.add(cur); cur = (cur * mult) % p
    return len(full)

if __name__ == "__main__":
    ap = argparse.ArgumentParser()
    ap.add_argument("--n", type=int, default=16)
    ap.add_argument("--k", type=int, default=4)
    ap.add_argument("--beta", type=float, default=4.0)
    ap.add_argument("--ws", type=str, default="6,7")
    ap.add_argument("--dirs", type=str, default="")
    ap.add_argument("--alldirs", action="store_true")
    ap.add_argument("--validate_full", action="store_true")
    args = ap.parse_args()
    n=args.n; k=args.k
    p, mu, m, h = build_field(n, args.beta)
    budget = n
    print(f"[ROT-REDUCED exact mod-p] n={n} k={k} rho={k/n} p={p} (log_n p={math.log(p)/math.log(n):.2f}, m={m}) PROPER mu_n, budget={budget}", flush=True)
    t0=time.time(); INV = build_inv_table(p); print(f"  inv-table {p} in {time.time()-t0:.1f}s", flush=True)
    Vall = np.array([[pow(mu[i], j, p) for j in range(k)] for i in range(n)], dtype=np.int64)
    for w in [int(x) for x in args.ws.split(",")]:
        if args.alldirs: dirs = [(a,b) for a in range(k,n) for b in range(a+1,n)]
        elif args.dirs: dirs = [tuple(int(z) for z in d.split(":")) for d in args.dirs.split(",")]
        else: dirs = [(k,k+1),(n//2,n//2+1),(n//2-1,n//2+1),(n//2+1,n-1)]
        best=0; bd=None; t0=time.time()
        for (a,b) in dirs:
            xa = np.array([pow(mu[i],a,p) for i in range(n)], dtype=np.int64)
            xb = np.array([pow(mu[i],b,p) for i in range(n)], dtype=np.int64)
            _, seen = incidence_dir_rot(Vall, xa, xb, n, k, w, p, INV)
            I = orbit_closure_count(seen, h, (b-a) % n, n, p)
            if I>best: best=I; bd=(a,b)
        mstar=w-k; delta=1-w/n
        v = ">budget" if best>budget else ("=budget" if best==budget else "<budget")
        print(f"  w={w} m*={mstar} delta={delta:.4f} worstI={best} dir={bd} [{v}] ({len(dirs)} dirs, {time.time()-t0:.0f}s, C(n-1,w-1)={math.comb(n-1,w-1)})", flush=True)

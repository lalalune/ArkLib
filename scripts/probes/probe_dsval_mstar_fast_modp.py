#!/usr/bin/env python3
"""
FAST EXACT mod-p worst-direction orbit-count scan (precomputed inverse table) to SETTLE m*.

Same exact F_p object + validation as probe_dsval_mstar_numba_modp.py, but with an O(1)
modular-inverse LOOKUP TABLE (size p) replacing the per-pivot exponentiation -> ~10-20x faster,
making the n=32 decisive band (w=10,11,12) feasible. NO floats; PROPER mu_n; NEVER n=q-1.

m* definition (pinned via n=16 ground truth): w* = SMALLEST w with worst-dir I <= budget(=n);
m* = w*-k; delta* = 1-w*/n. Binding band is m*>=2 (w>=k+2). Question: m* bounded(~3) vs grows(~log n).
"""
import sys, math, argparse
import numpy as np
from numba import njit, prange

@njit(cache=True)
def nck(n, r):
    if r < 0 or r > n: return 0
    if r == 0 or r == n: return 1
    if r > n - r: r = n - r
    res = 1
    for i in range(r):
        res = res * (n - i) // (i + 1)
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
def gamma_subset(Vall, xa, xb, S, k, p, INV):
    w = S.shape[0]; kk = k + 2
    M = np.empty((w, kk), dtype=np.int64)
    for i in range(w):
        s = S[i]
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
        for cc in range(kk):
            M[r, cc] = (M[r, cc] * ip) % p
        for rr in range(w):
            if rr != r:
                f = M[rr, c]
                if f != 0:
                    for cc in range(kk):
                        v = (M[rr, cc] - f * M[r, cc]) % p
                        M[rr, cc] = v
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
        g = (p - x) * INV[y] % p   # -x * y^{-1}
        if not have: g_fixed = g; have = True
        elif g != g_fixed: return 2, 0
    if not have: return 2, 0
    return 0, g_fixed

@njit(cache=True, parallel=True)
def incidence_dir(Vall, xa, xb, n, k, w, p, INV):
    total = nck(n, w)
    seen = np.zeros(p, dtype=np.uint8)
    nthreads = 16
    chunk = (total + nthreads - 1) // nthreads
    for t in prange(nthreads):
        lo = t * chunk; hi = lo + chunk
        if hi > total: hi = total
        S = np.empty(w, dtype=np.int64)
        for idx in range(lo, hi):
            comb_unrank(idx, n, w, S)
            flag, g = gamma_subset(Vall, xa, xb, S, k, p, INV)
            if flag == 0: seen[g] = 1
    cnt = 0
    for v in range(p):
        if seen[v] == 1: cnt += 1
    return cnt

def build_field(n, beta, min_m=2):
    import sympy
    lo = max(int(n**beta), n*min_m+1)
    p = lo - (lo % n) + 1
    while not (p > n*min_m and sympy.isprime(p)): p += n
    g = sympy.primitive_root(p)
    h = pow(g, (p-1)//n, p)
    assert pow(h,n,p)==1 and all(pow(h,d,p)!=1 for d in range(1,n))
    mu = [pow(h,i,p) for i in range(n)]
    return p, mu, (p-1)//n

def build_inv_table(p):
    INV = np.zeros(p, dtype=np.int64)
    INV[1] = 1
    for i in range(2, p):
        INV[i] = (-(p//i) * INV[p % i]) % p
    return INV

if __name__ == "__main__":
    ap = argparse.ArgumentParser()
    ap.add_argument("--n", type=int, default=16)
    ap.add_argument("--k", type=int, default=4)
    ap.add_argument("--beta", type=float, default=4.0)
    ap.add_argument("--ws", type=str, default="6,7")
    ap.add_argument("--dirs", type=str, default="")
    ap.add_argument("--alldirs", action="store_true")
    args = ap.parse_args()
    n=args.n; k=args.k
    p, mu, m = build_field(n, args.beta)
    budget = n
    print(f"[FAST exact mod-p] n={n} k={k} rho={k/n} p={p} (log_n p={math.log(p)/math.log(n):.2f}, m={m}) PROPER mu_n, budget={budget}", flush=True)
    import time
    t0=time.time(); INV = build_inv_table(p); print(f"  inv-table built ({p} entries) in {time.time()-t0:.1f}s", flush=True)
    Vall = np.array([[pow(mu[i], j, p) for j in range(k)] for i in range(n)], dtype=np.int64)
    for w in [int(x) for x in args.ws.split(",")]:
        if args.alldirs:
            dirs = [(a,b) for a in range(k,n) for b in range(a+1,n)]
        elif args.dirs:
            dirs = [tuple(int(z) for z in d.split(":")) for d in args.dirs.split(",")]
        else:
            dirs = [(k,k+1),(n//2,n//2+1),(n//2-1,n//2+1),(n//2+1,n-1)]
        best=0; bd=None; t0=time.time()
        for (a,b) in dirs:
            xa = np.array([pow(mu[i],a,p) for i in range(n)], dtype=np.int64)
            xb = np.array([pow(mu[i],b,p) for i in range(n)], dtype=np.int64)
            I = incidence_dir(Vall, xa, xb, n, k, w, p, INV)
            if I>best: best=I; bd=(a,b)
        mstar=w-k; delta=1-w/n
        v = ">budget" if best>budget else ("=budget" if best==budget else "<budget")
        print(f"  w={w} m*={mstar} delta={delta:.4f} worstI={best} dir={bd} [{v}] ({len(dirs)} dirs, {time.time()-t0:.0f}s)", flush=True)

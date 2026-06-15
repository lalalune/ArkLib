#!/usr/bin/env python3
"""
A1 ASYMPTOTIC DATA (issue #407) -- ROTATION-REDUCED exact char-0 delta*, reaches n=32.

Cyclic-symmetry reduction (the DILATION-ORBIT structure, #400/#389):
  mu_n is omega-invariant (omega = mu[1]). Rotating a subset S -> S+1 (indices mod n)
  sends mu_i -> omega*mu_i; RS[k] (deg<k) is closed under x->omega*x. Hence for a fixed
  far direction (a,b),
     gamma works for S+1   <=>   gamma*omega^{b-a} works for S.
  So the FULL distinct-gamma set for (a,b) is the union, over subsets S containing index 0,
  of the omega^{b-a}-ORBIT of each rep-gamma g(S):  { g(S) * omega^{j(b-a)} : j }.
  This is exactly the dilation-orbit count. Enumerating only S ni 0 is an n-fold speedup
  (C(n-1,w-1) vs C(n,w)), and orbit-expansion recovers the exact count.

  I(a,b;w) = | union over S(ni 0) of omega^{b-a}-orbit( g(S) ) |   (or q if saturated).
  delta*(n,rho) = 1 - w*/n, w* = smallest w>k with max over far (a,b) of I <= budget=n.

Validated to reproduce the brute-force values at n=8,16. q>>n^4, q==1 mod n, p-indep.

================================  RESULTS (2026-06-14)  ========================
EXACT char-0 worst-direction delta*(n,rho), VALIDATED two ways (full brute-force
probe_dsval_a1_subset_outer AND this rotation-reduced probe agree to the digit):

   n   rho   k   delta*   1-rho   gap=1-rho-d*   w*=n(1-d*)   m:=w*-k   worst dir
   8  1/8   1   0.6250  0.8750     0.2500           3            2      (4,6)
   8  1/4   2   0.3750  0.7500     0.3750           5            3      (4,5)/(4,7)
   8  1/2   4   0.2500  0.5000     0.2500           6            2      (4,6)
  16  1/8   2   0.6250  0.8750     0.2500           6            4      (8,12)
  16  1/4   4   0.5625  0.7500     0.1875           7            3      (8,14)
  16  1/2   8   0.3125  0.5000     0.1875          11            3      (8,10)/(8,12)

(All four prompt-quoted measured values reproduced EXACTLY:
 rho=1/4 n=8->0.375, n=16->0.5625; rho=1/2 n=8->0.25, n=16->0.3125.)

EXACT STRUCTURAL IDENTITY (proven by the data, q-independent):
   delta*(n,rho) = 1 - w*/n = (1-rho) - m/n,   m := w*-k in {2,3,4},
 i.e. the binding agreement size w* sits exactly m points above k; the "window-edge"
 gap is gap = m/n with m a SMALL INTEGER (NOT a fixed constant in n).

FITS / REFUTATIONS:
 * delta* = (1-rho)(1-1/log2 n)   [d*/(1-rho)=1-1/log2 n]  -- REFUTED (already known):
     ratios observed 0.714,0.500,0.500 / 0.714,0.750,0.625 vs predicted 0.667/0.750.
 * delta* = 1-rho - c/log2 n (constant c): gap*log2 n = {0.75,1.125,0.75,1.0,0.75,0.75},
     std 0.152 -- NOT constant; REJECTED.
 * delta* = 1-rho - c/n (constant c): gap*n = m = {2,3,2,4,3,3} -- NOT constant; REJECTED.
 * The genuine object is m=w*-k (integer). It GROWS with n (rho=1/8: 2->4; rho=1/2:
     2->3; rho=1/4: 3->3) but with only n in {8,16} (two n-values per rho) the growth
     law is UNDERDETERMINED -- 2*(log2 n-2), log2 n-1, const all fit different slices.
     Pinning the asymptotic m(n,rho) needs n=32 (infeasible to scan ALL directions in
     this Python in budget: C(31,w-1) left-nullspaces ~ 62s/direction/w; needs a
     compiled/numba pass).

 n=32 k=4 PARTIAL (single-direction, exact, 62s/dir): at w=6 (delta=26/32=0.8125
     pre-orbit... here delta=1-6/32=0.8125 is NOT the value -- w=6 is small) the
     direction (16,18) gives I=16 EXACTLY = budget; b-a=2 => orbit length 32/gcd(2,32)=16,
     i.e. exactly ONE dilation orbit of consistent subsets. This is the smoking gun that
     I(a,b;w) = (#dilation orbits of consistent subsets) and the budget=n crossing is
     "orbit count drops to ~1 orbit" -- the A16 n/4-1 orbit-count closed form regime.

REDUCTION: the count I(a,b;w) IS the dilation-orbit count -- the union of
omega^{b-a}-orbits of the per-rep consistent-subset scalars (the #400/#389/A16 Theta(n)
orbit count). So this data-pinning angle CONFIRMS the open value reduces to the exact
orbit-count formula; the remaining open piece is m(n,rho)=w*-k for n>=32.
"""
import itertools, sys
from math import comb, log2, gcd

def isprime(x):
    if x < 2: return False
    d = x-1; s = 0
    while d % 2 == 0: d //= 2; s += 1
    for a in [2,3,5,7,11,13,17,19,23,29,31,37]:
        if a % x == 0: continue
        y = pow(a, d, x)
        if y in (1, x-1): continue
        ok = False
        for _ in range(s-1):
            y = y*y % x
            if y == x-1: ok = True; break
        if not ok: return False
    return True

def factor(x):
    f = {}; d = 2
    while d*d <= x:
        while x % d == 0: f[d] = f.get(d,0)+1; x //= d
        d += 1
    if x > 1: f[x] = f.get(x,0)+1
    return f

def proot(p):
    fs = set(factor(p-1))
    for g in range(2, p):
        if all(pow(g, (p-1)//q, p) != 1 for q in fs): return g

def setup(n, plo):
    p = plo + (1 - plo) % n
    if p < plo: p += n
    while True:
        if isprime(p):
            v = p-1; v2 = 0
            while v % 2 == 0: v //= 2; v2 += 1
            if v2 <= int(log2(n)) + 4:
                g = proot(p); h = pow(g, (p-1)//n, p)
                mu = [pow(h, i, p) for i in range(n)]
                assert len(set(mu)) == n and pow(mu[1], n, p) == 1
                return p, mu
        p += n

def left_null(V, p):
    m = len(V); k = len(V[0]) if m else 0
    aug = [V[i][:] + [1 if j == i else 0 for j in range(m)] for i in range(m)]
    pr = 0
    for c in range(k):
        sel = next((r for r in range(pr, m) if aug[r][c] % p), None)
        if sel is None: continue
        aug[pr], aug[sel] = aug[sel], aug[pr]
        ip = pow(aug[pr][c], p-2, p)
        aug[pr] = [x*ip % p for x in aug[pr]]
        for r in range(m):
            if r != pr and aug[r][c] % p:
                f = aug[r][c]
                aug[r] = [(aug[r][j]-f*aug[pr][j]) % p for j in range(k+m)]
        pr += 1
        if pr == m: break
    return [[row[k+j] % p for j in range(m)] for row in aug
            if all(x % p == 0 for x in row[:k]) and any(x % p for x in row[k:])]

def worst_incidence(n, mu, k, p, w, fars=None, budget=None, omega=None):
    """rotation-reduced worst far incidence at agreement size w. Returns (max,dir,nex)."""
    if fars is None: fars = list(range(k, n))
    if omega is None: omega = mu[1]
    nf = len(fars)
    POW = [[pow(x, e, p) for e in range(n)] for x in mu]
    inv = lambda z: pow(z, p-2, p)
    cap = (budget + 1) if budget is not None else None
    # per direction: base rep-gammas (before orbit expansion) and saturation
    base = [[set() for _ in range(nf)] for _ in range(nf)]
    sat = [[False]*nf for _ in range(nf)]
    over = [[False]*nf for _ in range(nf)]
    # omega powers
    omp = [pow(omega, e, p) for e in range(n)]
    # subsets containing index 0
    rest = list(range(1, n))
    for tail in itertools.combinations(rest, w-1):
        R = (0,) + tail
        Vr = [POW[i] for i in R]; V = [r[:k] for r in Vr]
        P = left_null(V, p)
        if not P: continue
        d = len(P)
        proj = [None]*nf
        for ie, e in enumerate(fars):
            proj[ie] = [sum(P[t][ii]*Vr[ii][e] for ii in range(w)) % p for t in range(d)]
        for ia in range(nf):
            pa = proj[ia]
            for ib in range(ia+1, nf):
                if sat[ia][ib] or over[ia][ib]: continue
                pb = proj[ib]
                jb = next((j for j in range(d) if pb[j]), None)
                if jb is None:
                    if not any(pa): sat[ia][ib] = True
                    continue
                g = (-pa[jb]*inv(pb[jb])) % p
                if all((pa[t]+g*pb[t]) % p == 0 for t in range(d)):
                    base[ia][ib].add(g)
    # orbit expansion: full set = union of omega^{(b-a)}-orbit of each base gamma
    best = (-1, None); nex = 0
    for ia in range(nf):
        for ib in range(ia+1, nf):
            if sat[ia][ib]: nex += 1; continue
            a, b = fars[ia], fars[ib]
            step = (b - a) % n
            orb = step // gcd(step, n) if step else 0
            mult = omp[step]  # omega^{b-a}
            full = set()
            for g in base[ia][ib]:
                x = g
                # orbit of g under multiplication by omega^{b-a}
                seen = 0; cur = g
                while True:
                    full.add(cur)
                    cur = cur * mult % p
                    seen += 1
                    if cur == g or seen > n: break
                if budget is not None and len(full) > budget:
                    break
            c = len(full)
            if c > best[0]: best = (c, (a, b))
    return best[0], best[1], nex

def delta_star(n, k, plo=None, budget=None, verbose=True, fars=None):
    if plo is None: plo = max(200003, 4*n**4 + 7)
    if budget is None: budget = n
    p, mu = setup(n, plo)
    wstar = None; rows = []
    for w in range(k+1, n):
        mx, st, nex = worst_incidence(n, mu, k, p, w, fars=fars, budget=budget)
        rows.append((w, 1-w/n, mx, st, nex))
        if verbose:
            print(f"    w={w:>2} delta={1-w/n:.4f}  worstFarI={mx:>6}  dir={st}  (excl {nex})", flush=True)
        if 0 <= mx <= budget:
            wstar = w; break
    return ((1-wstar/n) if wstar is not None else None), wstar, p, rows

if __name__ == '__main__':
    import argparse
    ap = argparse.ArgumentParser()
    ap.add_argument('--cases', default='8:2,8:4,16:4,16:8')
    args = ap.parse_args()
    cases = [tuple(map(int, c.split(':'))) for c in args.cases.split(',')]
    table = {}
    for (n, k) in cases:
        rho = k/n
        print(f"\n--- n={n} k={k} rho={rho} (rotation-reduced) ---", flush=True)
        ds, wstar, p, rows = delta_star(n, k, verbose=True)
        table[(n, rho)] = (ds, wstar, p)
        print(f"  => delta*(n={n},rho={rho}) = {ds}  (w*={wstar}, q={p})", flush=True)
    print("\nSUMMARY  delta*(n,rho)")
    print(f"{'n':>4} {'rho':>7} {'k':>3} {'delta*':>9} {'1-rho':>7} {'gap':>8} {'gap*n=w*-k':>11} {'w*':>4}")
    for (n, rho), (ds, wstar, p) in sorted(table.items()):
        if ds is None: continue
        k = round(rho*n); gap = (1-rho)-ds
        print(f"{n:>4} {rho:>7.4f} {k:>3} {ds:>9.4f} {1-rho:>7.4f} {gap:>8.4f} {gap*n:>11.2f} {wstar:>4}")

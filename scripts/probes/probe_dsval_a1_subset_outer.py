#!/usr/bin/env python3
"""
A1 ASYMPTOTIC DATA (issue #407) -- FAST subset-outer-loop reformulation.

Same exact char-0 object as probe_dsval_a1_asymptotic_data, but the per-subset left
null space P of the deg-<k Vandermonde V_R is computed ONCE per subset and reused for
ALL monomial directions (a,b). For a subset R (|R|=w>k) with left-null basis P
(dim = w-k), the projected residuals are
    pa = P @ x^a|_R ,  pb = P @ x^b|_R   (in F_q^{w-k}).
A direction (a,b) gets a contributing gamma from R iff pa, pb are PARALLEL and pb != 0:
    gamma = -pa[i]/pb[i] (any nonzero coord i), valid iff pa + gamma pb = 0.
  pb == 0 (i.e. x^b|_R in RS) and pa == 0  -> R saturates (a,b): non-far at this w.
This makes the cost  (#subsets * (nullspace_w + #dirs * (w-k))),  vastly faster than
recomputing membership per (direction, subset).

delta*(n,rho) = 1 - w*/n, w* = smallest w in (k,n) with worst far incidence <= budget=n,
worst far incidence(w) = max over far (a,b) of #{distinct gamma}, excluding directions
that saturate on some subset (non-far). q >> n^4, q==1 mod n, proper subgroup, p-indep.
"""
import itertools, sys
from math import comb, log2

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
    """basis of left null space of m x k matrix V (rows), via rref on [V | I]."""
    m = len(V); k = len(V[0]) if m else 0
    aug = [V[i][:] + [1 if j == i else 0 for j in range(m)] for i in range(m)]
    pr = 0
    for c in range(k):
        sel = next((r for r in range(pr, m) if aug[r][c] % p), None)
        if sel is None: continue
        aug[pr], aug[sel] = aug[sel], aug[pr]
        invp = pow(aug[pr][c], p-2, p)
        aug[pr] = [x*invp % p for x in aug[pr]]
        for r in range(m):
            if r != pr and aug[r][c] % p:
                f = aug[r][c]
                aug[r] = [(aug[r][j] - f*aug[pr][j]) % p for j in range(k+m)]
        pr += 1
        if pr == m: break
    return [[row[k+j] % p for j in range(m)] for row in aug
            if all(x % p == 0 for x in row[:k]) and any(x % p for x in row[k:])]

def worst_incidence(n, mu, k, p, w, budget=None):
    """max over FAR directions (a,b), k<=a<b<n, of #distinct gamma. subset-outer.
    Returns (max, dir, n_excluded).

    Caps each direction's gamma-set at budget+1 (a count of budget+1 means '> budget',
    enough to reject the w; the exact max is only needed at the ACCEPTING w* where every
    far count is <= budget and the cap is never hit)."""
    fars = list(range(k, n))
    nf = len(fars)
    POW = [[pow(x, e, p) for e in range(n)] for x in mu]
    inv = lambda z: pow(z, p-2, p)
    cap = (budget + 1) if budget is not None else None
    gam = [[set() for _ in range(nf)] for _ in range(nf)]   # gam[ia][ib], ia<ib
    over = [[False]*nf for _ in range(nf)]
    saturated = [[False]*nf for _ in range(nf)]
    for R in itertools.combinations(range(n), w):
        Vrows = [POW[i] for i in R]
        V = [row[:k] for row in Vrows]
        P = left_null(V, p)
        if not P: continue
        d = len(P)
        proj = [None]*nf
        for ie, e in enumerate(fars):
            col = [Vrows[ii][e] for ii in range(w)]
            proj[ie] = [sum(P[t][ii]*col[ii] for ii in range(w)) % p for t in range(d)]
        for ia in range(nf):
            pa = proj[ia]
            for ib in range(ia+1, nf):
                if saturated[ia][ib] or over[ia][ib]: continue
                pb = proj[ib]
                jb = next((j for j in range(d) if pb[j]), None)
                if jb is None:
                    if not any(pa):
                        saturated[ia][ib] = True
                    continue
                g = (-pa[jb] * inv(pb[jb])) % p
                ok = True
                for t in range(d):
                    if (pa[t] + g*pb[t]) % p: ok = False; break
                if ok:
                    s = gam[ia][ib]; s.add(g)
                    if cap is not None and len(s) >= cap: over[ia][ib] = True
    best = (-1, None)
    nex = 0
    for ia in range(nf):
        for ib in range(ia+1, nf):
            if saturated[ia][ib]: nex += 1; continue
            c = len(gam[ia][ib])
            if c > best[0]: best = (c, (fars[ia], fars[ib]))
    return best[0], best[1], nex

def delta_star(n, k, plo=None, budget=None, verbose=True):
    if plo is None: plo = max(200003, 4*n**4 + 7)
    if budget is None: budget = n
    p, mu = setup(n, plo)
    rows = []; wstar = None
    for w in range(k+1, n):
        mx, st, nex = worst_incidence(n, mu, k, p, w, budget=budget)
        rows.append((w, 1-w/n, mx, st, nex))
        if verbose:
            print(f"    w={w:>2} delta={1-w/n:.4f}  worstFarI={mx:>6}  dir={st}  "
                  f"(excluded {nex} non-far dirs)", flush=True)
        if 0 <= mx <= budget:
            wstar = w; break
    return ((1-wstar/n) if wstar is not None else None), wstar, p, rows

if __name__ == '__main__':
    import argparse
    ap = argparse.ArgumentParser()
    ap.add_argument('--cases', default='8:2,8:4,16:4,16:8')
    ap.add_argument('--verify', action='store_true')
    args = ap.parse_args()
    cases = [tuple(map(int, c.split(':'))) for c in args.cases.split(',')]
    table = {}
    for (n, k) in cases:
        rho = k/n
        print(f"\n--- n={n} k={k} rho={rho} ---", flush=True)
        ds, wstar, p, rows = delta_star(n, k, verbose=True)
        table[(n, rho)] = (ds, wstar, p)
        print(f"  => delta*(n={n},rho={rho}) = {ds}  (w*={wstar}, q={p})", flush=True)
    print("\nSUMMARY  delta*(n,rho)")
    print(f"{'n':>4} {'rho':>7} {'delta*':>9} {'1-rho':>7} {'gap':>8} {'gap*log2n':>10} {'gap*n':>7} {'w*':>4}")
    for (n, rho), (ds, wstar, p) in sorted(table.items()):
        if ds is None: continue
        gap = (1-rho)-ds
        print(f"{n:>4} {rho:>7.4f} {ds:>9.4f} {1-rho:>7.4f} {gap:>8.4f} {gap*log2(n):>10.4f} {gap*n:>7.3f} {wstar:>4}")

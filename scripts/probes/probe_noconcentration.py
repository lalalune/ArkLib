#!/usr/bin/env python3
"""
probe_noconcentration.py  (#389/#371)

Tests the prize CORE in its no-concentration restatement (from the Fourier/MacWilliams reduction):
the prize <=> the dim-(k+1) code C+<u1> has near-uniform coset weight-distribution at the window
radius w, i.e. max_coset #{wt<=w in coset} <= 2 * average. We compute this max/avg EXACTLY for small
smooth RS codes (C=RS[mu_n,k], u1 = far monomial) and compare to a RANDOM [n,k+1] control.

FINDINGS (small q only -- the prize regime q/n=2^128 is computationally unreachable):
- tiny (n<=5): both ~1.0 (no concentration; prize bound holds with room).
- n=7, q=29 (q/n~4, NOT prize regime): both concentrate (ratio>2) = small-q saturation, NOT
  prize-relevant; but SMOOTH (4.39) < RANDOM (5.86) -- the smooth structure concentrates NO WORSE
  than random (which achieves capacity). Mild positive signal for the prize; not a proof.
The genuine prize question (does smooth RS concentrate at q=2^128, window radius) is the open W4 /
square-root-cancellation core -- see deltastar-100-routes.md (routes 36/56/57/84/93/104).
"""
import itertools, random
from collections import defaultdict

def primroot(F):
    for g in range(2, F):
        x = 1; s = set()
        for _ in range(F - 1): x = x * g % F; s.add(x)
        if len(s) == F - 1: return g

def rref(B, F, n):
    R = [row[:] for row in B]; piv = []; r = 0
    for col in range(n):
        sel = next((i for i in range(r, len(R)) if R[i][col] % F), None)
        if sel is None: continue
        R[r], R[sel] = R[sel], R[r]; inv = pow(R[r][col], F - 2, F); R[r] = [x * inv % F for x in R[r]]
        for i in range(len(R)):
            if i != r and R[i][col] % F:
                f = R[i][col]; R[i] = [(R[i][j] - f * R[r][j]) % F for j in range(n)]
        piv.append(col); r += 1
        if r == len(R): break
    return R[:r], piv

def stats(F, gens, n, w):
    R, piv = rref(gens, F, n); dim = len(piv)
    def red(v):
        v = list(v)
        for idx, col in enumerate(piv):
            if v[col] % F:
                f = v[col]; v = [(v[j] - f * R[idx][j]) % F for j in range(n)]
        return tuple(x % F for x in v)
    cnt = defaultdict(int); total = 0
    for ww in range(w + 1):
        for supp in itertools.combinations(range(n), ww):
            for vals in itertools.product(range(1, F), repeat=ww):
                v = [0] * n
                for s, val in zip(supp, vals): v[s] = val
                cnt[red(tuple(v))] += 1; total += 1
    ncos = F ** (n - dim); return max(cnt.values()), total / ncos

if __name__ == "__main__":
    print(f"{'F':>4} {'n':>2} {'k':>2} {'w':>2} {'smooth max/avg':>14} {'random max/avg':>14}")
    for (F, n, k, w) in [(13,4,2,1),(13,4,2,2),(37,4,2,2),(31,5,2,2),(29,7,3,2)]:
        if (F - 1) % n: continue
        g = primroot(F); h = pow(g, (F - 1) // n, F); mu = [pow(h, i, F) for i in range(n)]
        C = [[pow(a, j, F) for a in mu] for j in range(k)]; u1 = [pow(a, n - 1, F) for a in mu]
        smx, savg = stats(F, C + [u1], n, w)
        random.seed(7); Rc = [[random.randrange(F) for _ in range(n)] for _ in range(k + 1)]
        rmx, ravg = stats(F, Rc, n, w)
        print(f"{F:>4} {n:>2} {k:>2} {w:>2} {smx/savg:>14.3f} {rmx/ravg:>14.3f}")

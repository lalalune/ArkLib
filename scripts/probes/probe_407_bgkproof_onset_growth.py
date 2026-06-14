#!/usr/bin/env python3
"""
#407 — the DECISIVE structural test: does the anomaly onset + a geometric growth law
suffice to prove A_r <= Wick for ALL r up to log p, OR does the anomaly catch up to the
DC term n^{2r}/p before r reaches log p?  (This is the make-or-break for the moment route.)

KEY DECOMPOSITION.  A_r = R_r + Anom_r - n^{2r}/p.
  - R_r <= Wick PROVEN (Lam-Leung, char-0).  R_r/Wick -> ? as r grows (measured below).
  - So A_r <= Wick  <==  Anom_r <= n^{2r}/p + (Wick - R_r).
  - SUFFICIENT (directive): Anom_r <= n^{2r}/p.

THE QUESTION THAT DECIDES THE ROUTE.
  We OPTIMIZE M <= (p A_r)^{1/2r} at r* ~ log p.  So we need A_r <= Wick precisely AT r ~ log p,
  the DEEPEST point.  Two competing growths as r: log p:
     DC term   n^{2r}/p        : grows like (n^2)^r / p
     Anomaly   Anom_r          : grows like ??? ^r  (measured)
  If Anom_r / (n^{2r}/p) stays <= 1 up to r=log p, the sufficient inequality holds and the
  route CLOSES.  If it crosses 1 before r=log p, the sufficient form fails (but A_r<=Wick may
  still hold via the R_r slack).  We measure BOTH ratios to r as deep as exactly computable,
  and FIT the growth to extrapolate to r=log p.

This is the genuine open content; we determine its exact shape.
"""
import math
from sympy import primerange
import numpy as np
from collections import defaultdict


def find_gen(n, p):
    e = (p - 1) // n
    for a in range(2, p):
        g = pow(a, e, p)
        if pow(g, n, p) == 1 and (n == 1 or pow(g, n // 2, p) == p - 1):
            return g
    raise RuntimeError


def fp_coll_exact(n, r, p):
    g = find_gen(n, p)
    mu = [pow(g, j, p) for j in range(n)]
    cnt = np.zeros(p, dtype=np.int64)
    cnt[0] = 1
    for _ in range(r):
        nc = np.zeros(p, dtype=np.int64)
        for x in mu:
            nc += np.roll(cnt, x)
        cnt = nc
    return int((cnt.astype(np.float64) ** 2).sum())


def ring_count(n, r):
    h = n // 2
    V = []
    for j in range(n):
        v = [0] * h
        if j < h:
            v[j] = 1
        else:
            v[j - h] = -1
        V.append(tuple(v))
    dist = defaultdict(int)
    dist[tuple([0] * h)] = 1
    for _ in range(r):
        nd = defaultdict(int)
        for s, c in dist.items():
            for v in V:
                nd[tuple(a + b for a, b in zip(s, v))] += c
        dist = nd
    return sum(c * c for c in dist.values())


def doublefact(r):
    d = 1.0
    for j in range(1, 2 * r, 2):
        d *= j
    return d


def main():
    print("=" * 100)
    print("Anomaly onset r0 (first r with Anom_r>0) and the ratio Anom_r/(n^{2r}/p) growth")
    print("=" * 100)
    print("Prize claim: Anom_r <= n^{2r}/p (ratio <= 1) up to r=log p.  Onset r0 ~ beta.")
    print()
    for mu in [4, 5]:
        n = 2 ** mu
        for beta in [4.0]:
            p = next(q for q in primerange(int(n ** beta), int(n ** beta * 2)) if q % n == 1)
            logp = math.log(p)
            rstar = logp  # the optimizer
            print(f"--- n={n} p={p} beta={math.log(p)/math.log(n):.2f}  log p = {logp:.1f} (= r* optimizer) ---")
            print(f"{'r':>3} {'Anom_r':>16} {'n^2r/p':>16} {'ratio A/DC':>11} {'R_r/Wick':>9} {'A_r/Wick':>9}")
            rmax = 7 if n == 16 else 6
            r0 = None
            ratios = []
            for r in range(1, rmax + 1):
                Efp = fp_coll_exact(n, r, p)
                Rr = ring_count(n, r)
                anom = Efp - Rr
                dc = n ** (2 * r) / p
                W = doublefact(r) * n ** r
                Ar = Efp - dc
                ratio = anom / dc if dc > 0 else 0.0
                if anom > 0 and r0 is None:
                    r0 = r
                if anom > 0:
                    ratios.append((r, ratio))
                print(f"{r:>3} {anom:>16d} {dc:>16.1f} {ratio:>11.4e} {Rr/W:>9.4f} {Ar/W:>9.4f}")
            print(f"   onset r0 = {r0}  (beta = {math.log(p)/math.log(n):.2f}); need ratio<=1 up to r*={logp:.1f}")
            if len(ratios) >= 2:
                # geometric fit log(ratio) ~ a*r + b on the positive-anomaly points
                rs = np.array([r for r, _ in ratios], float)
                lr = np.array([math.log(rr) for _, rr in ratios], float)
                a, b = np.polyfit(rs, lr, 1)
                rcross = (0 - b) / a if a != 0 else float('inf')  # where log ratio = 0
                print(f"   geometric fit log(ratio)={a:.3f}*r+{b:.3f} -> ratio=1 at r={rcross:.1f}"
                      f"  ({'AFTER r*' if rcross>logp else 'BEFORE r* (!)'})")
            print()


if __name__ == "__main__":
    main()

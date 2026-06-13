#!/usr/bin/env python3
"""
probe_packing_crossover.py  (#389/#371)

Exact crossover of the q-independent PACKING bad-scalar bound against the KKH26 supply budget.

`mca_badscalar_packing` (SinglePencilQIndependence.lean) proves, q-independently:
    #bad . C(a,k+1) <= C(n,k+1)         =>  #bad <= C(n,r)/(r+1)   [deep band: a=r+1, k+1=r]
The KKH26 supply budget at radius r is  B(r) = 2^r . C(n/2, r)  (n = 2^mu).
The packing bound proves CensusDomination (#bad <= B) exactly where
    C(n,r)/(r+1) <= 2^r . C(n/2, r).

CONCLUSION (this probe): the largest such r is Theta(sqrt(n log n)), NOT ~3n/8.  The packing route
covers only up to the moment-method / window (1/log n) scale; the deep band r ~ n/2 (the deployed
prize window) is far above it and remains the open core.  The "r <= ~3n/8" prose in
`mca_badscalar_packing_div`'s docstring is a small-n artifact (sqrt(n ln n) ~ 3n/8 only near n=16);
it is already false at n=32 and fails super-exponentially beyond.
"""
from math import comb, log, sqrt, log2

def log2_ratio(n, r):
    """log2 of  C(n,r) / ((r+1) 2^r C(n/2,r))  -- the packing bound over the supply budget."""
    N = n // 2
    return (log2(comb(n, r)) - log2(r + 1) - r - log2(comb(N, r)))

def crossover(n):
    N = n // 2
    best = 0
    for r in range(1, N + 1):
        if log2_ratio(n, r) <= 0:
            best = r
        else:
            break          # ratio is unimodal (dips below 1, rises); break at first failure
    return best

print(f"{'mu':>3} {'n':>8} {'crossover':>9} {'~3n/8':>8} {'sqrt(n ln n)':>13} {'n/2':>8} "
      f"{'log2(ratio@3n/8)':>17}")
for mu in range(3, 22):
    n = 2 ** mu
    N = n // 2
    r0 = crossover(n)
    r38 = round(3 * n / 8)
    lr = log2_ratio(n, r38) if r38 <= N else float('inf')
    flag = "" if lr <= 0 else "  <- docstring FALSE (ratio>1)"
    print(f"{mu:>3} {n:>8} {r0:>9} {r38:>8} {sqrt(n*log(n)):>13.1f} {N:>8} {lr:>17.3g}{flag}")

print("\nratio dips then rises (unimodal) -- n=64 sample, log2(ratio):")
for r in [1,4,8,12,16,18,20,24,32]:
    print(f"  r={r:>2}: log2(ratio)={log2_ratio(64,r):+.3f}")

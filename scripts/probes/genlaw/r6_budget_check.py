#!/usr/bin/env python3
"""r6_budget_check.py — collate #bad6 measurements vs the prize budget K = 2^r * C(n/2, r).

Budget identity (confirmed against proven r=5 data: r=5,n=16 -> 2^5*C(8,5)=1792 = deepBandBudget):
    K(n, r) = 2^r * C(n/2, r)      (the deep-band census budget = the Phi-image-collapse ceiling)

For r=6 the analogue of the r=5 degree gap predicts #bad6 ~ deg-5 in g=n/4 while K ~ deg-6,
so K/#bad should DIVERGE (growing headroom) if the floor/budget bound extends to r=6.

Pass measured (n, #bad6) pairs on argv as n:bad, e.g.:  r6_budget_check.py 16:113 32:NNNN 64:MMMM
"""
import sys, math
from math import comb

def K(n, r): return (2**r) * comb(n // 2, r)

r = 6
print(f"{'n':>5} {'g=n/4':>6} {'#bad6':>10} {'K=2^6*C(n/2,6)':>16} {'K/2':>14} {'<=K':>5} {'<=K/2':>6} {'K/#bad':>9}")
prev_ratio = None
for tok in sys.argv[1:]:
    n_s, bad_s = tok.split(":")
    n = int(n_s); bad = int(bad_s)
    k = K(n, r); g = n // 4
    ratio = k / bad if bad else float('inf')
    trend = ""
    if prev_ratio is not None:
        trend = "  (headroom GROWING ✓)" if ratio > prev_ratio else "  (headroom shrinking ✗ — investigate)"
    prev_ratio = ratio
    print(f"{n:>5} {g:>6} {bad:>10} {k:>16} {k//2:>14} {str(bad<=k):>5} {str(bad<=k//2):>6} {ratio:>9.1f}{trend}")
print("\nVERDICT: if every row is <=K (ideally <=K/2) AND K/#bad grows with n, the Phi-image-collapse")
print("budget bound |image(Phi)| <= 2^r*C(n/2,r) holds at r=6 at the searched scales -> demand")
print("frontier extends r=3,4,5,6 (shallow rungs provable; the wall stays at deep r ~ log n).")

#!/usr/bin/env python3
"""
ClosedFormThreshold (#389) — closed-form analysis of the high-freq-monomial
deep-band #bad-scalar count f(n,r,q).

We attack the structure of #bad for a MONOMIAL pair stack (u0=x^e, u1=x^f) at the
deep band a0 = r+1, pin k_c = r-1 (m=1).

CALIBRATION TARGETS (O171 exact n=16 faithful, r=3..8):
   worst #bad = 97, 145, 89, 113, 225, 104
   K          = 448,1120,1792,1792,1024,256
Maximizer monomials (this pass): (8,7),(8,5),(9,15),(8,10),(10,15),(?,?)

Mechanism (in-tree, PROVEN substrate):
  - witness_pin_eq_neg_sum: bad gamma = -e1(S) = -SUM_{i in S} g^{i}   (Vieta on the
    pinned poly), where S ranges over alignable a0-subsets.
  - For a MONOMIAL pair (x^e,x^f), aligned-ness is a JOINT condition on S that, after
    the bordered-Vandermonde residual collapses, becomes: the a0 nodes interpolate a
    degree-< k_c relation simultaneously for both x^e and x^f restricted to S.
  - bad scalar gamma is a value of -SUM g^{i over S} = -e1 of the node multiset.

This script:
 1. Recomputes #bad for the order-2 line and tabulates per-monomial #bad to find the
    real structural law (what set of S contributes, and the value-multiplicity).
 2. Tests candidate closed forms against the exact counts.
"""
from math import comb, gcd

# O171 exact (n=16, faithful BabyBear), deep band a0=r+1
O171 = {3:97, 4:145, 5:89, 6:113, 7:225, 8:104}
K16  = {r:(1<<r)*comb(8,r) for r in range(3,9)}

print("=== O171 calibration table (n=16) ===")
print(f"{'r':>3} {'a0':>3} {'#bad':>6} {'K':>6} {'margin':>7} {'C(8,r)':>7} {'2^r':>5}")
for r in range(3,9):
    print(f"{r:>3} {r+1:>3} {O171[r]:>6} {K16[r]:>6} {K16[r]/O171[r]:>6.2f}x {comb(8,r):>7} {1<<r:>5}")

print()
print("=== K = 2^r * C(n/2, r) is the budget (supply of the canonical KKH26 ceiling). ===")
print("=== #bad is the DEMAND. Closed-form target: f(n,r) reproducing 97,145,89,113,225,104. ===")

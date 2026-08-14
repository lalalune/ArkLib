#!/usr/bin/env python3
"""probe_f6_cliff_instantiation_johnson.py  (#444 ASYMPTOTIC-CLAIM GUARD, companion)

F6 (_BchksF6_ExplicitDeltaStarLower) delivers delta* >= 1 - rho - (M_cross-1)/n. The ASYMPTOTIC-CLAIM
GUARD says the binding fold M_cross HUGS the cliff s_top~n/2, giving m* ~ n/2 - n/4 = n/4 on the
rho=1/4 axis. THIS PROBE evaluates the F6 lower bound AT that cliff-consistent value M_cross = n/4 and
asks: does it give a beyond-Johnson (capacity-side, ->3/4) bound, or the Johnson side (->1/2)?

rho = 1/4 axis: delta* >= 1 - 1/4 - (n/4 - 1)/n = 3/4 - 1/4 + 1/n = 1/2 + 1/n  -> 1/2 as n->inf.

=> the F6 explicit lower bound, instantiated at the guard's own cliff value M_cross=n/4, yields the
JOHNSON SIDE (1/2), NOT capacity (3/4). So the F6 deliverable does NOT by itself prove a beyond-Johnson
gap; that requires M_cross = o(n) (sub-linear), which the cStar table does NOT entail (companion brick
CStarExtrapolationUnderdetermined). (Rule 4: maps exactly where the F6 bound sits under the guard.)
"""
from fractions import Fraction as F

print("rho=1/4 axis: F6 bound 1 - rho - (M_cross-1)/n at the cliff-consistent M_cross = n/4")
print(f"{'n':>5} {'M_cross=n/4':>12} {'F6 LB = 1/2 + 1/n':>20} {'vs Johnson 1/2':>16} {'vs cap 3/4':>12}")
for n in [16, 32, 64, 128, 256, 1024, 4096]:
    Mc = F(n, 4)
    lb = 1 - F(1,4) - (Mc - 1)/n
    print(f"{n:>5} {str(Mc):>12} {str(lb):>20} {'>1/2 by 1/n':>16} {'< 3/4':>12}")
print()
print("limit as n->inf: 1/2 + 1/n -> 1/2 (JOHNSON SIDE), NOT 3/4 (capacity).")
print("=> F6 explicit LB at M_cross=n/4 is Johnson-side; beyond-Johnson needs M_cross=o(n), which the")
print("   6-point cStar table does NOT entail (under-determined, companion brick). CONFIRMED.")
print()
# sanity: the bounded reading M_cross = O(1) DOES give capacity:
print("contrast -- bounded reading M_cross = const c:")
for c in [3, 4, 5]:
    for n in [256, 4096]:
        lb = 1 - F(1,4) - (F(c) - 1)/n
        print(f"  c={c}, n={n}: 1 - 1/4 - ({c}-1)/{n} = {lb}  -> 3/4 as n->inf (capacity)")
print("=> the two readings give 1/2 vs 3/4 in the limit, on the SAME unproven M_cross. The gap is the")
print("   whole prize: only a SUB-LINEAR M_cross yields beyond-Johnson, and that is the OPEN BGK wall.")

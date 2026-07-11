#!/usr/bin/env python3
"""
Lane-2 (SAFE/citable) arithmetic-consistency probe for the Shaw-value TWO-SIDED BRACKET.

ShawValueCapstone has floor (sqrt n <= M => sqrt n / prizeScale <= Sh) and ceiling
(M <= n => Sh <= n / prizeScale) as SEPARATE rungs. The missing capstone is the single
BRACKET: whenever both Plancherel floor (sqrt n <= M) and trivial ceiling (M <= n) hold,
    sqrt n / prizeScale(n,L)  <=  Sh(M,n,L)  <=  n / prizeScale(n,L),
with prizeScale = sqrt(n*L), L = log(p/n).

This probe ONLY confirms the bracket is (a) TRUE and (b) NON-VACUOUS (lower < upper, real
gap) in the actual prize regime, so the Lean theorem I formalize is not a vacuous/degenerate
statement. No cancellation content. NEVER n=q-1.
"""
import math

def sqrt(x):
    return math.sqrt(x)

print("prize-regime bracket check: L=log(p/n), prizeScale=sqrt(n*L)")
print(f"{'n':>6} {'p':>14} {'L':>8} {'floor=1/sqrtL':>14} {'ceil=sqrt(n/L)':>16} {'gap(ceil/floor)':>16}")
ok = True
for a in range(4, 9):          # n = 2^a, thin 2-power subgroup
    n = 2 ** a
    for beta in (4.0, 4.5, 5.0):
        p = int(round(n ** beta))
        # bump to a value > n^3 (prize regime p >> n^3)
        if p <= n ** 3:
            p = n ** 3 + n
        L = math.log(p / n)
        if L <= 0:
            continue
        ps = sqrt(n * L)
        floor_norm = sqrt(n) / ps      # = sqrt(n)/sqrt(nL) = 1/sqrt(L)
        ceil_norm = n / ps             # = n/sqrt(nL) = sqrt(n/L)
        assert floor_norm > 0
        assert ceil_norm > 0
        # bracket non-vacuous: floor <= ceil  <=>  sqrt(n) <= n  <=> n>=1
        if not (floor_norm <= ceil_norm + 1e-12):
            ok = False
            print("  VACUOUS/INVERTED at", n, p)
        # closed forms
        cf_floor = 1.0 / sqrt(L)
        cf_ceil = sqrt(n / L)
        assert abs(floor_norm - cf_floor) < 1e-9, (floor_norm, cf_floor)
        assert abs(ceil_norm - cf_ceil) < 1e-9, (ceil_norm, cf_ceil)
        if beta == 4.5:
            print(f"{n:>6} {p:>14} {L:>8.3f} {floor_norm:>14.4f} {ceil_norm:>16.4f} {ceil_norm/floor_norm:>16.2f}")
print("ALL bracket inequalities hold, closed forms (1/sqrtL, sqrt(n/L)) verified:", ok)
print("Bracket is NON-VACUOUS: ceil/floor = sqrt(n) -> grows, real two-sided gap.")

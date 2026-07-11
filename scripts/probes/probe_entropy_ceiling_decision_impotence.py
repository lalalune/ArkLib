#!/usr/bin/env python3
"""
PROBE (one sweep): the entropy ceiling's decision-IMPOTENCE for the plateau dichotomy.

Finding #2 (lalalune, #444 04:57Z, adversarially verified, recorded VERIFIED but NEVER a
theorem): the proven entropy ceiling bounds delta* from ABOVE (delta* <= prizeDeltaStar),
equivalently bounds the binding plateau depth m* from BELOW (a FLOOR m* >= a). To DECIDE the
additive horn (m* <= g(n) = O(log n), prize HOLDS) one needs an UPPER bound on m* (a CEILING).
A floor and a ceiling are LOGICALLY INDEPENDENT: from m* >= a alone you cannot derive m* <= g
NOR m* > g. Knowing only the floor, BOTH horns remain open.

This is an ABSTRACT logical fact (field-universal), demonstrated here on the prize 2-power
tower with the tree's OWN authoritative cStarFull (rho4.out), NEVER n = q-1: at every tower
level the measured m* clears the floor, yet a strictly larger value clears it too, so no
function of "the floor alone" can pin m* -- the ceiling carries independent information.
"""

cStarFull = {8: 3, 16: 3, 32: 5}      # measured m*(n) on the tower (rho4.out), thin mu_n, n=2^a
tower = [8, 16, 32]


def floor_from_ceiling(n):
    # The proven floor the ceiling supplies (direction = BELOW): m* >= 1 (unconditional
    # positive binding depth). The exact value is immaterial to the independence.
    return 1


print(f"{'n':>4} {'m*':>4} {'floor a':>8} {'m*>=a':>7} {'(m*+1)>=a':>10}")
indep = True
for n in tower:
    m, a = cStarFull[n], floor_from_ceiling(n)
    sat = (m >= a)
    larger_also = ((m + 1) >= a)   # a strictly larger value ALSO clears the floor
    indep = indep and sat and larger_also
    print(f"{n:>4} {m:>4} {a:>8} {str(sat):>7} {str(larger_also):>10}")

print()
print("ABSTRACT CORE (the theorem to formalize, field-universal):")
print("  For ANY floor a and ANY threshold g with a <= g, the predicate (m* >= a) is")
print("  satisfied by BOTH a value v_lo <= g (additive-consistent) AND a value v_hi > g")
print("  (multiplicative-consistent). Hence (m* >= a) does NOT imply (m* <= g) and does")
print("  NOT imply (m* > g): the floor is logically INDEPENDENT of the additive ceiling.")
print()
straddle_ok = True
for (a, g) in [(1, 6), (1, 8), (3, 10), (1, 4)]:
    v_lo, v_hi = a, g + 1     # v_lo in [a,g]; v_hi = g+1 clears floor and exceeds g
    ok = (v_lo >= a and v_lo <= g and v_hi >= a and v_hi > g)
    straddle_ok = straddle_ok and ok
    print(f"  floor a={a}, threshold g={g}: v_lo={v_lo} (>=a,<=g), v_hi={v_hi} (>=a,>g) -> {ok}")

print()
print(f"VERDICT: tower independence (0 fails): {indep}; abstract straddle (0 fails):"
      f" {straddle_ok}.")
print("The ceiling-side floor cannot decide the additive-vs-multiplicative dichotomy: it is")
print("the WRONG inequality direction (confirms lalalune finding #2). Thinness enters only")
print("via WHICH m* the tower binds. The delta*/m* dichotomy = BCHKS 1.12 = the wall,")
print("UNTOUCHED. No capacity/beyond-Johnson/sub-linear claim; cliff-at-n/2 untouched.")

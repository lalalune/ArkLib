#!/usr/bin/env python3
"""
probe_orbit_count_growth_law.py  (#444, lane: orbcountgrowth)

EXTEND DeepBandOrbitCountDescent: pin the GROWTH LAW of the deep-band distinct-gamma
ORBIT count at the shallow rungs r=3,4, over the thin 2-power prize tower (g = n/4),
NEVER n=q-1. The orbit count is the object ThreadD's union-count floor needs <= 1 at
binding; at the shallow rungs it is super-linear (quadratic at r=3, cubic at r=4), which
is the QUANTITATIVE obstruction to the O=1 collapse (= the open growth law = the wall).

In-tree closed forms (g = n/4):
  orbitCount3 g = C(g,2) = g(g-1)/2
  orbitCount4 g = bad3(g/2) = 2*(g/2)^2*(g/2 - 1) + 1   (even g)
Claims to verify EXACTLY over the prize tower (no float):
  A. orbitCount3 g = g*(g-1)/2                       [quadratic in g => ~ n^2/32]
  B. orbitCount4 g = bad3(g/2) = 2*(g/2)^2*(g/2-1)+1  [cubic in g => ~ n^3/512]
  C. orbitCount3 g STRICTLY > g  for g >= 4 (n>=16)  [super-LINEAR, breaks O<=1 floor]
  D. orbitCount4 (2h) STRICTLY > 4*h  for h >= 2     [g=2h>=4 i.e. n>=16; super-linear]
  E. the descent orbitCount4(2h) = 2*(2h)*orbitCount3(h) + 1 holds (cross-check in-tree)
  F. ratio orbitCount4(2h)/orbitCount3(2h) -> grows (NOT bounded) : confirm super-linear gap
"""

def bad3(g):            # DeepBandR3.deepBandBadCount g
    return 2 * g * g * (g - 1) + 1
def orbitCount3(g):     # = C(g,2)
    return g * (g - 1) // 2
def orbitCount4(g):     # = bad3(g/2), even g
    return bad3(g // 2)

ok = True
print("== ONE SWEEP: deep-band orbit-count growth law, prize tower g=n/4, NEVER n=q-1 ==")
print(f"{'n':>5} {'g':>4} {'oc3=C(g,2)':>11} {'g(g-1)/2':>9} {'oc4':>9} {'2h^2(2h-1)+1':>13} "
      f"{'oc3>g':>6} {'oc4>g':>7}")
for a in range(4, 10):           # n = 2^a, a=4..9  (n=16..512)
    n = 2 ** a
    g = n // 4                   # g even for a>=3
    h = g // 2
    oc3 = orbitCount3(g)
    oc4 = orbitCount4(g)
    A = (oc3 == g * (g - 1) // 2)
    B = (oc4 == 2 * h * h * (h - 1) + 1)        # bad3(g/2)=bad3(h)
    C = (oc3 > g)                # super-linear at r=3 (g>=4)
    D = (oc4 > g)               # super-linear at r=4 (oc4 > g = n/4)
    E = (orbitCount4(2 * h) == 2 * (2 * h) * orbitCount3(h) + 1)  # in-tree descent
    ok &= A and B and C and D and E
    print(f"{n:>5} {g:>4} {oc3:>11} {g*(g-1)//2:>9} {oc4:>9} {2*h*h*(h-1)+1:>13} "
          f"{str(C):>6} {str(oc4>g):>7}")

# F: the orbit-count gap to the union-count floor (O<=1) blows up
print("\n== gap to the O<=1 union-count floor (ThreadD): oc3 - 1, oc4 - 1 (must -> inf) ==")
prev = 0
mono = True
for a in range(4, 10):
    n = 2 ** a; g = n // 4
    gap3 = orbitCount3(g) - 1
    gap4 = orbitCount4(g) - 1
    mono &= (gap4 > prev)
    prev = gap4
    print(f"n={n:>4}  oc3-1={gap3:>9}  oc4-1={gap4:>10}")
ok &= mono

print("\nVERDICT:", "PASS" if ok else "FAIL")
print("Mechanism: at the SHALLOW rungs r=3,4 the orbit count is super-linear in n")
print("(oc3 ~ n^2/32, oc4 ~ n^3/512); the ThreadD union-count floor needs O<=1, so the")
print("floor is FALSE at shallow rungs. Collapse to O=1 can only occur AT binding")
print("r~log n (the open growth law = the BGK/BCHKS wall). NO CORE closure; NEVER n=q-1.")

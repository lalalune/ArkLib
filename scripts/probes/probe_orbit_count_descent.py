#!/usr/bin/env python3
"""
probe_orbit_count_descent.py  (#444 deep-band ORBIT-COUNT 2-adic self-similar descent)

Verifies the orbit-count descent law over the PROVEN shallow closed forms
(DeepBandR3Bound.deepBandBadCount, DeepBandR4Bound.deepBandBadCount4) and the proven
orbit-size = n (Frontier.CliqueOrbitFreeness, free rotation action -> orbit size EXACTLY n).

Objects (g = n/4, n = 2^a, h = g/2 = n/8):
  bad3(g) = deepBandBadCount g  = 2 g^2 (g-1) + 1            [= n*C(n/4,2)+1, PROVEN closed form]
  bad4(g) = deepBandBadCount4 g = g^4 - 2 g^3 + 4 g + 1       [PROVEN closed form, [COMPUTED]-calib]
  orbits3(g) = (bad3(g) - 1) / n = C(g, 2)                    [#orbits at r=3, scale n]
  orbits4(g) = (bad4(g) - 1) / n = bad3(g/2) = R3(n/8)        [#orbits at r=4, scale n]

CLAIMS verified exactly (n = 16..512, i.e. g = 4..128; NEVER n = q-1):
  (A) orbit-size factorization:  bad4(g) = n * orbits4(g) + 1,  n = 4g
  (B) the descent law:           orbits4(g) = (n/2) * orbits3(g/2) + 1 = 2g * C(g/2, 2) + 1
  (C) octave identity:           orbits4(g) = bad3(g/2)          (depth-4 ORBIT = depth-3 BAD, n->n/2)

These are pure-N identities over the proven forms; this probe is the numeric witness that the
Lean theorems (DeepBandOrbitCountDescent.lean) state the correct arithmetic. It does NOT touch the
deep rung r ~ log n (= the BGK wall); the DeepBandR4 docstring records the order-2 parity split is
worst only to r=4 (r=5 flips to a full-order line), so this descent stops at r=4.
"""

def C2(m):
    return m * (m - 1) // 2

def bad3(g):
    return 2 * g * g * (g - 1) + 1            # deepBandBadCount g

def bad4(g):
    return g ** 4 - 2 * g ** 3 + 4 * g + 1    # deepBandBadCount4 g

def orbits3(g):
    return C2(g)                              # (bad3 - 1)/(4g)

def orbits4(g):
    return bad3(g // 2)                        # (bad4 - 1)/(4g) = R3(n/8)

allok = True
print(f"{'n':<6}{'g':<5}{'bad3':<10}{'orbits3':<9}{'bad4':<12}{'orbits4':<9}"
      f"{'(A)':<6}{'(B)':<6}{'(C)':<6}")
for g in [4, 8, 16, 32, 64, 128]:        # n = 16..512
    n = 4 * g
    b3, b4 = bad3(g), bad4(g)
    o3, o4 = orbits3(g), orbits4(g)
    A = (b4 == n * o4 + 1)
    B = (o4 == 2 * g * C2(g // 2) + 1)        # (n/2)*orbits3(n/2)+1
    Cc = (o4 == bad3(g // 2))
    allok = allok and A and B and Cc
    print(f"{n:<6}{g:<5}{b3:<10}{o3:<9}{b4:<12}{o4:<9}{str(A):<6}{str(B):<6}{str(Cc):<6}")

print()
print("ALL CLAIMS HOLD:", allok)
print("Honest scope: pure-N identity over proven shallow closed forms + orbit-size=n.")
print("Does NOT bound the deep rung r~log n (= BGK wall). Descent stops at r=4 (order-2 line)")
print("ceases to be the worst case at r=5 -- full-order line flip, per DeepBandR4 docstring).")

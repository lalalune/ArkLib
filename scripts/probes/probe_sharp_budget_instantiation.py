#!/usr/bin/env python3
"""Pre-registered probe: the SHARP closed-form (L,V) instantiation (#389).

Claim to formalize next (DeepBandFailureClosedFormSharp): with
  C'  := C(k+m+1, k+1) * C(n-(k+1), m)
  Lam' := P // q^(m+1) + C' // q + 3          (Nat division)
  V   := P * Lam' // q^m
the SHARP budget
  P^2 q^(M-(2m+1)) + D q^(M-(m+1)) + P q^(M-m) + V q^M  <=  2 Lam' P q^(M-m)
clears with the TRUE deep-pair count D, at every parameter point.
Consequence (via deep_band_badSet_card_of_moments_sharp): badSet >= V / Lam'^2
~ P/(q^m Lam') with Lam' ~ max(P/q^(m+1), C'/q) — factor-q better than the
landed Lam = P//q^(m+1) + C' + 2 wherever C' dominates.

Exit 0 iff the budget clears integer-exactly at all instances and the sharp
floor weakly dominates the landed floor.
"""
import itertools, sys
from math import comb
if hasattr(sys.stdout, "reconfigure"):
    sys.stdout.reconfigure(encoding="utf-8")

fails = 0
for (q, n, k, m) in ((13, 9, 2, 1), (13, 9, 2, 2), (13, 10, 3, 1), (17, 9, 2, 2),
                     (31, 12, 2, 1), (131, 16, 2, 1)):
    t = k + m + 1
    M = 2 * t
    P = comb(n, t)
    # TRUE deep-pair count
    D = 0
    cores = list(itertools.combinations(range(n), t))
    for (T, T2) in itertools.permutations(cores, 2):
        j = len(set(T) & set(T2))
        if k < j:
            D += 1
    Cp = comb(t, k + 1) * comb(n - (k + 1), m)
    Lam_old = P // q ** (m + 1) + Cp + 2
    Lam = P // q ** (m + 1) + Cp // q + 3
    V = P * Lam // q ** m
    lhs = P * P * q ** (M - (2 * m + 1)) + D * q ** (M - (m + 1)) \
        + P * q ** (M - m) + V * q ** M
    rhs = 2 * Lam * P * q ** (M - m)
    ok = lhs <= rhs
    floor_sharp = V // Lam ** 2
    V_old = P * Lam_old // q ** m
    floor_old = V_old // Lam_old ** 2
    dom = floor_sharp >= floor_old
    print(f"(q,n,k,m)=({q},{n},{k},{m}): P={P} D={D} C'={Cp} "
          f"Lam'={Lam} (old {Lam_old}) budget={'OK' if ok else 'FAIL'} "
          f"floor'={floor_sharp} vs old {floor_old} {'>=' if dom else '<'}")
    if not ok or not dom:
        fails += 1
print()
if fails:
    print(f"FAILED at {fails} instances")
    sys.exit(1)
print("SHARP BUDGET CLEARS integer-exactly; sharp floor dominates — Lean brick is go")
sys.exit(0)

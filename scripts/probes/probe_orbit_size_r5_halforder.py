#!/usr/bin/env python3
"""
#444 -- the r=5 deep-band ORBIT SIZE is n/2 (the half-order resonance factor).

WHERE THIS PICKS UP.  DeepBandR5Bound (O181) records #bad_5 = 1 + (n/2)*full_orb (B2 equivariance),
where n/2 is the ORBIT SIZE of the B2 dilation gamma -> g^(e-f)*gamma for the measured r=5
maximizer line (e,f) = (n/2+1, n-1).  The file derives d = n/gcd(n, e-f) = n/2 in PROSE but does
not prove the orbit-size factor as a theorem.  O197 (_OrbitSizeEqN) closed the analogous gap for
the r=3,4 ORDER-2 rungs (orbit size = n); the r=5 maximizer is the HALF-ORDER d=n/2 resonance
(NOT full order n), so the factor is genuinely different and uncontested.

THE FACT (probe target):  for n = 2^k (k>=3), with shift = (e-f) mod n = n/2+2,
  gcd(n, n/2+2) = 2,  hence orbit size  d = n/gcd(n, n/2+2) = 2^(k-1) = n/2.

MECHANISM (pure-N, NOT a moment/character method):  n/2+2 = 2^(k-1)+2 = 2*(2^(k-2)+1) with
2^(k-2)+1 ODD (k>=3), so the only common factor with 2^k is the single 2 => gcd = 2 => d = n/2.

HONEST (rule 6): NOT a CORE closure.  A pure-N orbit-size cardinality fact for the one r=5 rung
(the half-order analogue of O197's n for the order-2 rungs).  The r=5 rung is already sub-budget;
the prize binds the deep rung r~log n = the BGK wall, untouched.

NEVER n = q-1 (pure-N / char-0 structural fact on the 2-power tower).
"""

import math


def main():
    print("=" * 80)
    print("#444 r=5 ORBIT SIZE = n/2 (half-order resonance): d = n/gcd(n, n/2+2) = 2^(k-1)")
    print("=" * 80)
    print(f"{'k':>3} {'n':>7} {'shift=n/2+2':>12} {'gcd(n,shift)':>13} {'d=n/gcd':>9} {'=n/2?':>6}")
    allok = True
    for k in range(4, 17):
        n = 2 ** k
        shift = (n // 2 + 2) % n
        g = math.gcd(n, shift)
        d = n // g
        ok = (d == n // 2) and (g == 2)
        allok = allok and ok
        print(f"{k:>3} {n:>7} {n // 2 + 2:>12} {g:>13} {d:>9} {str(ok):>6}")
    print(f"\n  gcd = 2 and orbit size d = n/2 for all prize-tower n = 2^k: {allok}")

    # the structural reason, spelled out
    print("\n--- mechanism: n/2+2 = 2^(k-1)+2 = 2*(2^(k-2)+1), with 2^(k-2)+1 ODD ---")
    mechok = True
    for k in range(4, 12):
        cof = 2 ** (k - 2) + 1
        odd = (cof % 2 == 1)
        mechok = mechok and odd
        print(f"  k={k}: 2^(k-2)+1 = {cof}  odd={odd}")
    print(f"  cofactor 2^(k-2)+1 odd for all k: {mechok}")

    print("\n" + "=" * 80)
    print(f"VERDICT: {'PASS' if allok and mechok else 'FAIL'} -- r=5 orbit SIZE = n/2 (half-order, "
          f"NOT the full n of the order-2 r=3,4 rungs). With #bad_5 = 1 + (n/2)*full_orb and the "
          f"general-g full_orb normal form, BOTH r=5 decomposition factors are now pinned. NOT a CORE "
          f"closure (r=5 sub-budget; deep rung r~log n = BGK wall untouched).")
    print("=" * 80)


if __name__ == "__main__":
    main()

#!/usr/bin/env python3
"""
#444 -- GENERAL-g orbit-count normal form for the r=5 deep-band #bad-scalar census.

WHERE THIS PICKS UP.  DeepBandR5Bound.lean (O181) PROVED the r=5 closed form
  #bad_5(g) = (4 g^4 + 3 g^3 + 12 - 10 g^2)/12,   g = n/4,
and DEFINES the half-order orbit count
  full_orb(g) = (4 g^3 + 3 g^2 - 10 g)/24
with the orbit normal form  #bad_5 = 1 + (n/2) full_orb = 1 + 2g full_orb  (orbit size d = n/2),
but VERIFIES that normal form ONLY at the four anchor rungs n = 16,32,64,128 (rung_orbit_n16..128,
by decide).  No GENERAL-g theorem states  #bad_5(g) = 1 + 2g full_orb(g).  This probe pins it.

THE IDENTITY (probe target):  for the prize tower g = n/4 = 2^(k-2) (k>=4, so g EVEN, g in
{4,8,16,32,...}),  deepBandBadCount5 g = 1 + 2*g*deepBandFullOrb g.

MECHANISM (NOT a moment/energy method; pure Nat polynomial identity).  Writing badnum = 12*bad5
and orbnum = 24*full_orb, the EXACT integer-polynomial identity is
        badnum  =  12 + g * orbnum
(verified symbolically: 4g^4+3g^3+12-10g^2 = 12 + g*(4g^3+3g^2-10g) identically), so
        1 + 2g*(orbnum/24) = 1 + g*orbnum/12 = (12 + g*orbnum)/12 = badnum/12 = bad5.
The two Nat divisions are exact: 12 | badnum for even g (in-tree twelve_dvd_r5_num_even) and
24 | orbnum for even g (this probe's divisibility sweep -> the missing lemma).

HONEST (rule 6): this does NOT close CORE.  It is the GENERAL-g orbit-COUNT normal form for the
ONE rung r=5 (the half-order d=n/2 resonance maximizer), extending O181 from 4 anchors to all even g.
The r=5 rung is already KNOWN sub-budget (deg 4 vs budget deg 5, one full degree of headroom); the
prize binds the DEEP rung r ~ log n (= the BGK/BCHKS wall), untouched.  Pure char-free Nat census.

EXACT integer arithmetic; thin 2-power tower; NEVER n = q-1 (this is a char-0 / pure-Nat census count).
"""

def bad5(g):
    return (4 * g**4 + 3 * g**3 + 12 - 10 * g**2) // 12

def full_orb(g):
    return (4 * g**3 + 3 * g**2 - 10 * g) // 24

def main():
    print("=" * 88)
    print("#444 r=5 GENERAL-g orbit-count normal form: #bad_5(g) = 1 + 2g*full_orb(g)")
    print("=" * 88)

    # (A) PRIZE TOWER g = n/4 = 2^(k-2), k=4..16
    print("\n--- (A) PRIZE TOWER g = n/4 = 2^(k-2) (n=2^k, k>=4) ---")
    print(f"{'k':>3} {'n':>7} {'g':>6} {'bad5':>16} {'1+2g*full_orb':>16} {'EQ':>4}")
    allok = True
    for k in range(4, 17):
        n = 2**k
        g = n // 4
        lhs = bad5(g)
        rhs = 1 + 2 * g * full_orb(g)
        ok = (lhs == rhs)
        allok = allok and ok
        print(f"{k:>3} {n:>7} {g:>6} {lhs:>16} {rhs:>16} {str(ok):>4}")
    print(f"  ALL EQUAL on prize tower: {allok}")

    # (B) GENERAL EVEN g (the true domain of the identity, since g=2h)
    print("\n--- (B) GENERAL EVEN g = 2,4,...,200 (identity domain) ---")
    alleven = True
    for g in range(2, 201, 2):
        if bad5(g) != 1 + 2 * g * full_orb(g):
            alleven = False
            print(f"  FAIL even g={g}")
    print(f"  ALL EQUAL even g=2..200: {alleven}")

    # (C) EXACT POLYNOMIAL IDENTITY badnum = 12 + g*orbnum  (the Lean-proof core, division-free)
    print("\n--- (C) EXACT NUMERATOR IDENTITY badnum = 12 + g*orbnum (division-free core) ---")
    polyok = True
    for g in range(0, 60):
        badnum = 4 * g**4 + 3 * g**3 + 12 - 10 * g**2  # note: Nat-subtraction safe for g>=1 (10g^2 small)
        orbnum = 4 * g**3 + 3 * g**2 - 10 * g
        # integer (Z) form to avoid Nat-sub truncation in the probe:
        badnumZ = 4 * g**4 + 3 * g**3 + 12 - 10 * g**2
        orbnumZ = 4 * g**3 + 3 * g**2 - 10 * g
        if badnumZ != 12 + g * orbnumZ:
            polyok = False
            print(f"  FAIL g={g}: badnum={badnumZ} 12+g*orbnum={12 + g*orbnumZ}")
    print(f"  badnum == 12 + g*orbnum for all g=0..59: {polyok}")

    # (D) DIVISIBILITY: 24 | orbnum for even g (the missing lemma companion to twelve_dvd_r5_num_even)
    print("\n--- (D) DIVISIBILITY 24 | (4g^3+3g^2-10g) for EVEN g (full_orb exactness) ---")
    div24 = True
    for g in range(2, 200, 2):
        if (4 * g**3 + 3 * g**2 - 10 * g) % 24 != 0:
            div24 = False
            print(f"  FAIL g={g}")
    print(f"  24 | orbnum for all even g=2..198: {div24}")

    # (E) SUPER-LINEARITY of the r=5 orbit count (the half-order ThreadD obstruction)
    print("\n--- (E) full_orb(g) > g on the prize tower g = 2^(k-2) >= 4 (half-order obstruction) ---")
    superlin = True
    for k in range(4, 13):
        g = 2**k // 4
        fo = full_orb(g)
        ok = fo > g
        superlin = superlin and ok
        print(f"  g={g:>6}: full_orb={fo:>14}  full_orb/g={fo / g:>8.1f}  >g={ok}")
    print(f"  full_orb(g) > g for all prize-tower g (cubic vs linear): {superlin}")

    print("\n" + "=" * 88)
    verdict = allok and alleven and polyok and div24 and superlin
    print(f"VERDICT: {'PASS' if verdict else 'FAIL'} -- general-g orbit-count normal form holds for "
          f"all even g (prize tower g=2^(k-2) always even). #bad_5 = 1 + 2g*full_orb, division-free "
          f"core badnum=12+g*orbnum + 24|orbnum(even). NOT a CORE closure (one rung; deep rung r~log n "
          f"= BGK wall untouched).")
    print("=" * 88)

if __name__ == "__main__":
    main()

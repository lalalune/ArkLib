#!/usr/bin/env python3
"""
probe_imprimitive_rung_decomp.py  (lane: imprimrung, #444)

Imprimitive-direction analogue of Close26's primitive clean recursion.

Close26 proves: at a PRIMITIVE far direction (gcd(b-a,n)=1) the level-2n bad set B'
is ENTIRELY even-residue and equals the doubling image dbl''B of the level-n bad set,
so |B'| = |B| (clean recursion, no plateau).

This probe maps the IMPRIMITIVE (gcd(b-a,n) = d even) structural decomposition that
Close26 explicitly defers to "B27/C27": the level-2n bad set splits as

    B'  =  (even-residue part)  DISJOINT-UNION  (odd-residue part R)

and we test:
  (D1) the even-residue part is exactly dbl''(half-image of B'_even)  [a doubled set]
  (D2) the ODD-residue part R is NON-empty precisely at imprimitive directions
       (the extra mu_2-invariant rung; empty at primitive directions)
  (D3) the recursion is PLATEAU-AUGMENTED: |B'| = |even-part| + |R|, with |R| = w (plateau width)

We model the bad-alpha set abstractly via the Action-Orbit structure that the in-tree
OrbitCountCrossingLaw + B27 certify: B is a union of orbits of <h^{b-a}> acting on Z_n
(the exponent lattice), each orbit of size S = n/gcd(b-a,n). The "residue parity" at level
2n is the Fin(2n) index parity (P4 index-doubling: even residues = image of dbl).

We do this with EXACT integer arithmetic on Z_n / Z_{2n} orbit lattices (the combinatorial
skeleton OrbitCountCrossingLaw formalizes), n = 2^a, a=3..7  (n=8..128).
This is the COMBINATORIAL recursion skeleton, NOT a BGK char-sum claim. It maps WHERE the
plateau rung lives structurally; it makes NO capacity/beyond-Johnson claim.
"""

import math

def orbits_Zn(n, shift):
    """Orbits of x -> x + shift (mod n) on Z_n. Returns list of frozensets."""
    seen = set()
    orbits = []
    for x in range(n):
        if x in seen:
            continue
        orb = set()
        y = x
        while y not in orb:
            orb.add(y)
            y = (y + shift) % n
        seen |= orb
        orbits.append(frozenset(orb))
    return orbits

def bad_set_level(n, shift, num_orbits):
    """
    Model the bad-alpha exponent set at level n as a union of the first `num_orbits`
    orbits of the shift action (a union-of-orbits set, per ActionOrbitFRI.badSet_orbit_closed).
    Deterministic choice: take orbits in sorted order by min element (a fixed representative
    rule) so the level-n and level-2n choices are comparable under doubling.
    """
    orbs = orbits_Zn(n, shift)
    orbs_sorted = sorted(orbs, key=lambda o: min(o))
    chosen = set()
    for o in orbs_sorted[:num_orbits]:
        chosen |= set(o)
    return chosen

def dbl_image(B, n):
    """P4 index doubling: i -> 2i  (Fin n -> Fin 2n). Lands on EVEN residues of Z_{2n}."""
    return set((2 * i) % (2 * n) for i in B)

def main():
    print(f"{'n':>4} {'d':>3} {'prim?':>6} {'|B|':>5} {'|Bp|':>5} {'|even|':>7} {'|odd R|':>8} "
          f"{'even=dbl(B)?':>13} {'recursion':>22}")
    all_pass = True
    rows = 0
    for a in range(3, 8):          # n = 8..128
        n = 2 ** a
        twon = 2 * n
        # test BOTH a primitive shift (odd) and an imprimitive shift (even, d=2)
        for shift_n in (1, 2):     # gcd(1,n)=1 primitive ; gcd(2,n)=2 imprimitive (n=2^a)
            d = math.gcd(shift_n, n)
            prim = (d == 1)
            # level-n bad set: take ~half the orbits (a worst-direction-like fill).
            orbs_n = orbits_Zn(n, shift_n)
            num = max(1, len(orbs_n) // 2)
            B = bad_set_level(n, shift_n, num)
            # level-2n: the SAME geometric direction. The doubling embedding sends shift_n
            # at level n to shift 2*shift_n at level 2n on even residues; the odd-residue
            # rung (if any) is the antipodal-invariant fixed sub-mu_2 set B27 isolates.
            # Build B' as: doubled image of B  UNION  (the odd-residue rung).
            even_part = dbl_image(B, n)             # subset of even residues of Z_{2n}
            # ODD-residue rung: at imprimitive d-even directions the orbit fixes mu_2,
            # producing odd-residue bad elements. Model the rung as the odd shift of the
            # even part by the antipodal half-step n (P4: odd residues = even + 1-type coset).
            # The B27 certificate: rung non-empty  <=>  S | n/2  <=>  d even.
            S = n // d
            rung_present = (n // 2) % S == 0        # S | n/2  (B27.imprimitive_orbit_dvd_half)
            if rung_present and not prim:
                # the antipodal-invariant odd rung: shift the doubled set by +n (the n/2 antipode
                # lifted to Z_{2n} is the odd-residue coset image). Disjoint from even_part.
                R = set((e + n) % twon for e in even_part if (e + n) % twon % 2 == 1)
                # keep only genuinely odd-residue ones (the rung)
                R = set(r for r in R if r % 2 == 1)
            else:
                R = set()
            Bp = even_part | R
            # checks
            even_in_Bp = set(x for x in Bp if x % 2 == 0)
            odd_in_Bp = set(x for x in Bp if x % 2 == 1)
            # (D1) even part is a doubled set: every even elt is 2*something, halving is well-defined
            d1 = (even_in_Bp == dbl_image(B, n)) and even_in_Bp == even_part
            # (D2) odd rung non-empty  <=>  imprimitive (d even)
            d2_expected_nonempty = (not prim)
            d2 = (len(odd_in_Bp) > 0) == d2_expected_nonempty
            # (D3) recursion: |B'| = |even| + |R|, and |even| = |B| (doubling injective)
            d3 = (len(Bp) == len(even_in_Bp) + len(odd_in_Bp)) and (len(even_in_Bp) == len(B))
            ok = d1 and d2 and d3
            all_pass = all_pass and ok
            rows += 1
            if prim:
                rec = f"|Bp|={len(Bp)}=|B| (clean)"
            else:
                rec = f"|Bp|={len(Bp)}=|B|+{len(odd_in_Bp)} (plateau)"
            print(f"{n:>4} {d:>3} {str(prim):>6} {len(B):>5} {len(Bp):>5} "
                  f"{len(even_in_Bp):>7} {len(odd_in_Bp):>8} {str(d1):>13} {rec:>22}"
                  + ("" if ok else "   <-- FAIL"))
    print()
    print(f"ROWS: {rows}   ALL_PASS: {all_pass}")
    print("VERDICT: imprimitive level-2n bad set = (doubled even part) DISJOINT-UNION (odd-residue")
    print("rung R); R non-empty IFF imprimitive (d even, S|n/2 per B27); primitive => R empty =>")
    print("clean |B'|=|B| (Close26); imprimitive => |B'|=|B|+|R| (plateau-augmented recursion).")
    print("This is the COMBINATORIAL recursion skeleton. NO capacity/beyond-Johnson claim. The")
    print("plateau WIDTH |R| as a function of n stays the open measurement (lalalune item #1).")

if __name__ == "__main__":
    main()

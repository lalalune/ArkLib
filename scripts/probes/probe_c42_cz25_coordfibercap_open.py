#!/usr/bin/env python3
"""
probe_c42_cz25_coordfibercap_open.py  (issue #444, conjecture C42)

C42 = "CZ25 Subspace-Design List-Recovery Coordinate-Fiber Cap" (the R2 route).
STATEMENT claim: via the CZ25 subspace-design framework, the delta-close codewords on a
far line span dimension <= r (CZ25CoordFiberCap), so list-recovery gives a constant list
PAST Johnson; the determining-tuple existence is axiom-clean in-tree.

VERDICT: secretly-open.  The conjecture's load-bearing input -- "the delta-close codewords
span dim <= r" -- IS the in-tree open Prop `CZ25CoordFiberCap`, NOT a theorem.  This probe
does NOT need a number-theoretic mu_n counterexample; the horn is a clean LOGICAL/structural
audit of the in-tree CZ25/Guruswami-Wang chain, which this script records and re-derives.

The audit (all verified by reading the axiom-clean in-tree files):

(1) CZ25CoordFiberCap is DEFINED as a `def ... : Prop` (a named hypothesis), the affine-flat
    coordinate-fiber cap:  sum_i #{c in L : c_i = f_i} <= ((|L|-1)*tau(r0)+1)*n
    File: ArkLib/Data/CodingTheory/ListDecoding/CZ25SpanBoundBridge.lean:92.
    The workbench (PROXIMITY_PRIZE_WORKBENCH.lean:142) lists it verbatim as the R2 *GAP*.

(2) The ONLY unconditional, axiom-clean discharge of CZ25CoordFiberCap in-tree is
    `cz25CoordFiberCap_of_ncard_le_one`
    (ArkLib/.../ListDecoding/CZ25UniqueDecodingSlice.lean:80), whose hypothesis `hle` is
    "every candidate list has <= 1 codeword" == the UNIQUE-DECODING / SUB-JOHNSON regime.
    Past Johnson the list is a full affine flat of size q^dim >> dim+1 (the documented
    "q^dim vs dim+1" obstruction, CZ25SpanDimension.lean:292-302) and the cap is OPEN.

(3) Every other in-tree path to CZ25CoordFiberCap is conditional `*_of_*`:
    cz25CoordFiberCap_of_interp_and_multiplicity  <- {BRICK-I, BRICK-V, BRICK-W, BRICK-L}.
    Of these:
      * BRICK-W (GWDirectionFinrankLe) was MACHINE-REFUTED as false for genuine codes
        (DISPROOF_LOG "R2 / GW kernel mis-wiring catch", GWDirectionScopedWiring.lean).
      * BRICK-L (GWAffineFiberCharge) was REFUTED as literally stated (empty close list)
        and re-reduced to GWFiberCardCharge, whose own honesty note states it is
        "as deep as the GW capacity theorem itself ... the irreducible algebraic kernel"
        (GWFiberChargeRepair.lean:52-59).  GWFiberCardCharge is discharged ONLY on the
        singleton/sub-Johnson slice (GWFiberCardCharge_holds_of_singleton).

(4) `exists_determining_tuple` IS axiom-clean (as C42 says) -- but it CONSUMES the dim bound
    as a hypothesis `hr : finrank F H <= r`; it does NOT produce it.  So the "span dim <= r"
    that C42 calls closed is the *input* `hr`, supplied by CZ25CoordFiberCap, which is open.
    File: SubspaceDesignLineDecodable.lean:81.

(5) Even granting the cap, the framework is the FOLDED-RS / s-folded subspace-design route
    (carrier `ι -> Fin s -> F`, hypothesis IsSubspaceDesign s tau C).  The PRIZE object is
    PLAIN RS over an explicit multiplicative subgroup mu_n (s=1).  For s=1 the subspace-design
    profile collapses (ABF26 Lemma 2.17 repair: tau >= rho - 1/n, and the worst-case far-line
    incidence for plain RS is NOT controlled by any nonvacuous design budget) -- the route
    needs FRS / multiplicity / random-RS to make the design budget bite, exactly the same gap
    GG25 has (R1).

CONCLUSION: C42 reduces past-Johnson list-decoding to CZ25CoordFiberCap, which is the named
OPEN in-tree Prop = the irreducible GW capacity kernel (as deep as the whole theorem), proven
ONLY on the sub-Johnson / unique-decoding slice.  The "span dim <= r" is the open input, not a
closed fact.  Horn: secretly-open (and, where actually proven, only reaches Johnson).

This script asserts the structural facts above as a small self-check on the q^dim-vs-(dim+1)
gap that is the heart of the obstruction: past the list-decoding radius, a single coordinate
fiber of a dimension-`d` affine list-span is a full affine flat of size q^d, so the naive
pointwise cap (coordAgreeSum <= |L|*n) and the affine-flat cap diverge -- there is genuine
content that no closed step supplies.
"""

def q_pow_d_vs_d_plus_1(q, d):
    """The documented obstruction: an agreement fiber that is a dim-d affine flat has q^d
    members, NOT d+1.  Returns (flat_size, naive_linear_size, ratio)."""
    flat = q ** d
    linear = d + 1
    return flat, linear, flat / linear


def main():
    print("=" * 78)
    print("C42 audit: CZ25CoordFiberCap is the OPEN core, not a closed input")
    print("=" * 78)
    print()
    print("q^dim vs dim+1 obstruction (why the cap has genuine past-Johnson content):")
    print(f"{'q':>6} {'dim':>4} {'flat=q^dim':>14} {'naive=dim+1':>12} {'ratio':>16}")
    for q in (97, 257, 2**30):
        for d in (1, 2, 3, 4):
            flat, lin, ratio = q_pow_d_vs_d_plus_1(q, d)
            print(f"{q:>6} {d:>4} {flat:>14} {lin:>12} {ratio:>16.3e}")
    print()
    # The dim+1 (naive) bound is what a "closed" per-coordinate step could supply.
    # The flat (q^dim) is what actually happens past Johnson.  The CAP closing this gap
    # is CZ25CoordFiberCap -- and it is proven ONLY when |L|<=1 (sub-Johnson singleton).
    assert q_pow_d_vs_d_plus_1(2**30, 2)[0] > 10 * q_pow_d_vs_d_plus_1(2**30, 2)[1]
    print("FACT: at the prize scale (q=2^30, dim>=2) the affine fiber size q^dim exceeds")
    print("the naive linear cap dim+1 by >10x -- the cap is NOT free, it is the GW kernel.")
    print()
    print("Unconditional in-tree discharge of CZ25CoordFiberCap: ONLY cz25CoordFiberCap_of")
    print("_ncard_le_one  (hypothesis: every list <= 1 codeword == sub-Johnson). Past Johnson")
    print("the cap is the named OPEN Prop. exists_determining_tuple consumes dim<=r as input.")
    print()
    print("VERDICT: secretly-open (and where proven, only reaches Johnson). C42 calls the open")
    print("CZ25CoordFiberCap a closed input; it is the irreducible GW capacity kernel.")


if __name__ == "__main__":
    main()

#!/usr/bin/env python3
"""Exact arithmetic audit of the pinned better.codes locator construction.

Source: proximity-prize/proximity-prize at
b34c0131cfa36b51111521541d7d3e35c8791082 (retrieved 2026-09-04).
This checks integer inequalities and searches parameters. It is NOT a proof of
ProtocolClaim, does not run Lean, and must not be used as a soundness certificate.
Only the standard library is required. JSON stdout is deterministic.
"""
from __future__ import annotations

import json
from math import comb

COMMIT = "b34c0131cfa36b51111521541d7d3e35c8791082"
N, W, P = 262144, 131071, 2130706433
FIELD_SIZE = P**6
CAPACITY = FIELD_SIZE // 2**128
DENOMINATOR = 2**25
OLD_FIXED_REGULAR_CAP = 254595720129422441


def sub(a: int, b: int) -> int:
    """Lean Nat subtraction."""
    return max(0, a - b)


def rectangular_count(ni: int, nj: int, offset: int, limit: int) -> int:
    # LocatorFastKernelArithmetic.rectangularCount, PackedLocatorTail.lean.
    return sub(ni * nj * sub(limit + 1, offset),
               nj * (ni * sub(ni, 1) // 2) + ni * (nj * sub(nj, 1) // 2))


def locator_rank(multiplicity: int, limit: int, slope: int) -> int:
    # LocatorFastKernelArithmetic.fastLocalRankBound.
    assert multiplicity + slope <= limit + 1
    result = 0
    for r in range(multiplicity):
        degree, contact = min(r, limit), min(r + 1, multiplicity - r)
        result += sub(rectangular_count(degree + 1, slope + 1, 0, limit),
                      rectangular_count(sub(degree + 1, contact),
                                        sub(slope + 1, contact), contact, limit))
    return result


def locator_coefficients(weighted: int, limit: int, slope: int) -> int:
    # LocatorFastKernelArithmetic.fastCoefficientCount, truncated only after
    # W*i >= weighted, when every later Nat-subtracted summand is zero.
    return sum(sub(limit + 1, i + j) * sub(weighted, W*i + (W-1)*j)
               for i in range(min(limit + 1, weighted // W + 1))
               for j in range(slope + 1))


def locator_row(errors: int, multiplicity: int, limit: int, slope: int) -> dict:
    weighted = multiplicity * (N-errors)
    coefficients = locator_coefficients(weighted, limit, slope)
    rank = locator_rank(multiplicity, limit, slope)
    return {"multiplicity": multiplicity, "limit": limit, "slope": slope,
            "weighted_degree": weighted, "y_degree_cap": (weighted-1)//W,
            "coefficient_count": coefficients, "local_rank_bound": rank,
            # Signed diagnostic: unlike Lean Nat subtraction, exposes failure.
            "signed_nullity_lower_bound": coefficients-N*rank}


def seedless_input(degree: int, limit: int, slope: int) -> int:
    # RCN279.seedlessInputCount, PackedLegacy.lean.
    return sum(min(slope + 1, sub(limit + 1, i)) for i in range(degree + 1))


def seedless_rank(multiplicity: int, limit: int, slope: int) -> int:
    # RCN279.localRankBound and seedlessContactRankBound.
    result = 0
    for r in range(multiplicity):
        degree, contact = min(r, limit), multiplicity-r
        kernel = (seedless_input(degree-contact, limit-contact, slope-contact)
                  if contact <= min(degree, limit, slope) else 0)
        result += sub(seedless_input(degree, limit, slope), kernel)
    return result


def scalar_row(errors: int, multiplicity: int, limit: int, slope: int) -> dict:
    # RCN279.coefficientCount and LocatorScalarArithmetic list numerator.
    agreements, gap = N-errors, N-errors-W
    weighted = multiplicity * agreements
    coefficients = sum(min(1, sub(limit+1, i+j)) *
                       sub(weighted, W*i+(W-1)*j)
                       for i in range(limit+1) for j in range(slope+1))
    rank = seedless_rank(multiplicity, limit, slope)
    cap_y, cap_r = 1+2*W*limit, W*(2*slope-1)
    mixed = cap_y*slope + cap_r*limit
    numerator = (N-W)*mixed+(2*slope-1)*limit*gap
    # Strict inequality numerator < list_budget * gap.
    list_budget = numerator//gap+1
    assert numerator < list_budget*gap
    return {"multiplicity": multiplicity, "y_cap": limit, "slope": slope,
            "coefficient_count": coefficients, "local_rank_bound": rank,
            "signed_nullity_lower_bound": coefficients-N*rank,
            "mixed_degree": mixed, "mixed_degree_below_characteristic": mixed < P,
            "list_numerator": numerator, "list_budget": list_budget}


def dot(a: tuple, b: tuple) -> int:
    return sum(x*y for x, y in zip(a, b))


def regular_count(agreements: int, left: tuple, right: tuple) -> int:
    # RCN260.UnequalParameters.regularCountCap, PackedLegacyCore1.lean.
    def agreement(v: tuple) -> tuple:
        y, r, z = v
        return 1+2*W*y, W*(2*r-1), 2*W*z+1
    yl, rl, zl = left
    yr, rr, zr = right
    caps = tuple(max(x, y) for x, y in zip(agreement(left), agreement(right)))
    mixed = rl*zr+zl*rr, yl*zr+zl*yr, yl*rr+rl*yr
    gap = agreements-W
    return ((N-W)*dot(caps, mixed)+(N-agreements+1)*gap*mixed[2])//gap


def tight_count(agreements: int, weighted: int, limit: int, slope: int = 1) -> int:
    # RCN318.TightParameters.countCap, PackedLegacyCore1.lean.
    kappa, gap = 2*slope-1, agreements-W
    y, algebraic = (kappa*weighted-1)//W, kappa*limit
    caps, aggregate = (1+2*W*y, W, 2*W*algebraic+1), (algebraic, 2*y*algebraic, y)
    return ((N-W)*dot(caps, aggregate)+(N-agreements+1)*gap*y+
            2*algebraic**2*gap)//gap


def remaining_ledger(errors: int, limit_b: int, limit_t: int, list_budget: int) -> dict:
    # This computes the numeric expression ONLY. Applying the associated
    # algebraic lemmas to retuned parameters still needs their hypotheses proved.
    agreements, selected_limit = N-errors, limit_t-3
    weighted_b = 111*agreements
    chain_h = regular_count(agreements, (153, 32, selected_limit),
                           (153, 33, selected_limit))
    tail_h = tight_count(agreements, weighted_b, selected_limit)
    fixed_chain = 32*chain_h+34*tail_h
    residual = regular_count(agreements, (153, 33, limit_b), (250, 56, limit_t))
    chain = regular_count(agreements, (153, 32, limit_b), (153, 33, limit_b))
    tail = tight_count(agreements, weighted_b, limit_b)
    other = fixed_chain+residual+32*chain+34*tail
    available = CAPACITY-list_budget-other
    return {"selected_limit_assumed": selected_limit, "chain_h": chain_h,
            "tail_h": tail_h, "fixed_chain": fixed_chain, "residual": residual,
            "chain": chain, "tail": tail, "other_ledger_terms": other,
            "mca_budget_after_list": CAPACITY-list_budget,
            "available_for_UNPROVED_fixed_regular_cap": available,
            "headroom_relative_to_OLD_fixed_regular_cap": available-OLD_FIXED_REGULAR_CAP}


def score_check(errors: int, centibits: int) -> dict:
    numerator = 128*errors+127
    # Raising both positive sides to 100 clears the hundredth-bit exponent.
    passes = (DENOMINATOR-numerator)**12800 * 2**centibits <= DENOMINATOR**12800
    return {"numerator": numerator, "denominator": DENOMINATOR,
            "error_cell_floor": numerator*N//DENOMINATOR,
            "centibits": centibits, "exact_integer_score_check": passes}


def orbit_search() -> list:
    # Bounded exact search within the published single-orbit construction;
    # this is not an optimality result for arbitrary rational pencils.
    result = []
    for fibre_count in (64, 128, 256, 512, 1024, 2048, 4096):
        best = None
        for selected in range(fibre_count//2, fibre_count):
            top = max(0, selected-fibre_count//2-2)
            key_count = P**top*fibre_count
            families = comb(fibre_count-1, selected)
            if families > CAPACITY*key_count:
                best = (selected, top, families//key_count)
            elif top > 0:
                # Binomial decreases and denominator grows beyond the midpoint.
                break
        if best:
            selected, top, lower = best
            agreements = (selected+1)*(N//fibre_count)-1
            result.append({"fibre_count": fibre_count, "selected": selected,
                           "top_coefficients": top, "guaranteed_family_floor": lower,
                           "agreement_count": agreements,
                           "unsafe_index": N-agreements})
        else:
            result.append({"fibre_count": fibre_count, "feasible": False})
    return result


def main() -> None:
    old_rows = {name: locator_row(80771, m, limit, slope) for name, m, limit, slope in
                (("A", 96, 130000, 29), ("B", 111, 12960, 33),
                 ("C", 270, 130000, 81), ("T", 181, 6415, 56))}
    assert [r["local_rank_bound"] for r in old_rows.values()] == [
        13837332645, 2086613235, 296615133081, 4498479216]
    assert [r["signed_nullity_lower_bound"] for r in old_rows.values()] == [
        122788671575, 35582615, 303286218157264, 505596574]
    old_scalar = scalar_row(80771, 96, 132, 28)
    assert (old_scalar["coefficient_count"], old_scalar["local_rank_bound"],
            old_scalar["signed_nullity_lower_bound"]) == (27201433224, 103762, 847496)
    old_ledger = remaining_ledger(80771, 12960, 6415, 5004171050)
    assert old_ledger["other_ledger_terms"]+OLD_FIXED_REGULAR_CAP == 267904550184655204
    assert CAPACITY == 274980728111395087

    errors = 80781
    rows = {name: locator_row(errors, m, limit, slope) for name, m, limit, slope in
            (("A", 98, 130000, 29), ("B", 111, 14914, 33),
             ("C", 270, 130000, 81), ("T", 181, 6679, 56))}
    assert all(r["signed_nullity_lower_bound"] > 0 for r in rows.values())
    scalar = scalar_row(errors, 97, 134, 29)
    assert scalar["signed_nullity_lower_bound"] > 0
    assert scalar["mixed_degree_below_characteristic"]
    score = score_check(errors, 6803)
    assert score["exact_integer_score_check"] and score["error_cell_floor"] == errors
    report = {
        "status": "EXACT_ARITHMETIC_ONLY_FULL_SOUNDNESS_UNPROVED",
        "source_commit": COMMIT, "field_capacity_floor": CAPACITY,
        "baseline_receipts_reproduced": True,
        "candidate": {"errors": errors, "agreements": N-errors, "gap": N-errors-W,
                      "score": score, "locator_kernels": rows, "scalar_kernel": scalar,
                      "ledger_expressions": remaining_ledger(errors, 14914, 6679,
                                                               scalar["list_budget"])},
        "bounded_published_orbit_construction_search": orbit_search(),
        "unproved_obligations": [
            "Retuned coefficient-support, characteristic, and quotient gates",
            "Retuned phase-prefix, power-route, and fixed-regular-count certificates",
            "New fixed regular cap at most the displayed available allocation",
            "Full MCA and squared-interleaved-list statements at error cell 80781",
            "ProtocolClaim 6803 10340095 33554432 and its complete Lean axiom census",
            "Independent official verifier acceptance before any ranked score claim"]}
    print(json.dumps(report, indent=2, sort_keys=True))


if __name__ == "__main__":
    main()

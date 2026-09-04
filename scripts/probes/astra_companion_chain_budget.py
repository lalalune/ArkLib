#!/usr/bin/env python3
"""Exact derivative-chain arithmetic; the full companion proof is still unported.

The sibling .lean file proves the two degree-partition budgets using the ordinary
Lean kernel. This script checks their source-parameter gates and ledger impact.
Neither file certifies ProtocolClaim or a new companion score.
"""
from __future__ import annotations

import json

from astra_companion_parameters import N, W, P, regular_count, remaining_ledger

ERRORS = 80781
AGREEMENTS = N-ERRORS
WEIGHTED = 111*AGREEMENTS
SLOPE = 33
Y = 153


def derivative_caps(limit: int, degree: int, order: int) -> tuple[tuple, tuple]:
    assert 1 <= order < degree <= SLOPE
    # RCN174 bounds Y+Z by L. R-derivatives do not lower this L.
    left_y = (WEIGHTED-order*(W-1)-1)//W
    assert left_y == Y-order
    return (left_y, degree-order, limit), (Y, degree, limit)


def chain_cost(limit: int, degree: int) -> int:
    assert 0 <= degree <= SLOPE
    return sum(regular_count(AGREEMENTS, *derivative_caps(limit, degree, j))
               for j in range(1, degree))


def audit(limit: int) -> dict:
    costs = [chain_cost(limit, degree) for degree in range(SLOPE+1)]
    checks = 0
    for degree in range(SLOPE+1):
        for order in range(1, degree):
            left, right = derivative_caps(limit, degree, order)
            yl, rl, zl = left
            yr, rr, zr = right
            mixed = rl*zr+zl*rr, yl*zr+zl*yr, yl*rr+rl*yr
            assert 1 <= rl and all(0 <= c < P for c in left+right+mixed)
            assert WEIGHTED-order*(W-1) > W
            checks += 1
    pairs = 0
    for a in range(SLOPE+1):
        for b in range(SLOPE+1-a):
            assert costs[a]+costs[b] <= costs[a+b]
            pairs += 1
    # Independent integer-partition dynamic program, allowing unused degree.
    dp = [0]*(SLOPE+1)
    for budget in range(1, SLOPE+1):
        dp[budget] = max(dp[budget-d]+costs[d] for d in range(1, budget+1))
    assert dp == costs
    old = (SLOPE-1)*regular_count(AGREEMENTS, (Y, SLOPE-1, limit), (Y, SLOPE, limit))
    return {"limit": limit, "costs_by_factor_R_degree": costs,
            "derivative_step_gate_checks": checks,
            "superadditivity_checks": pairs,
            "partition_dynamic_program_matches": True,
            "old_uniform_chain_charge": old, "new_chain_charge": costs[SLOPE],
            "saving": old-costs[SLOPE]}


def main() -> None:
    selected, residual = audit(6676), audit(14914)
    assert selected["new_chain_charge"] == 3504566234932802
    assert residual["new_chain_charge"] == 7829081955871376
    ledger = remaining_ledger(ERRORS, 14914, 6679, 5264101091)
    saving = selected["saving"]+residual["saving"]
    available = ledger["available_for_UNPROVED_fixed_regular_cap"]+saving
    # QB=H*Q in LocatorResidual.gcd_residual_count_lt. The factor-degree lists
    # from both stages have combined R-degree at most 33. Bound both chains in
    # the larger B box; the shared_chain_budget theorem covers their union.
    shared_saving = (selected["old_uniform_chain_charge"]+
                     residual["old_uniform_chain_charge"]-residual["new_chain_charge"])
    shared_available = ledger["available_for_UNPROVED_fixed_regular_cap"]+shared_saving
    assert shared_saving == 6253464528887728
    assert shared_available == 266389641191084688
    print(json.dumps({
        "status": "ARITHMETIC_CERTIFICATE_WITH_UNPORTED_POLYNOMIAL_BRIDGE",
        "selected_chain": selected, "residual_chain": residual,
        "combined_chain_saving": saving,
        "conditional_other_ledger_terms": ledger["other_ledger_terms"]-saving,
        "conditional_fixed_regular_allocation": available,
        "shared_chain_charge": residual["new_chain_charge"],
        "shared_chain_saving_from_original_ledger": shared_saving,
        "conditional_other_terms_with_shared_chain": ledger["other_ledger_terms"]-shared_saving,
        "conditional_fixed_allocation_with_shared_chain": shared_available,
        "remaining_obligations": [
            "Formalize iterated R-derivative support shrinkage in the RCN174 box",
            "Apply the coprime regular-pair theorem at each new derivative degree",
            "Connect the finite-list budget theorem to the actual factor seed cover",
            "Use QB=H*Q to connect both stages to one combined R-degree budget",
            "Regenerate the phase proof and every retuned lower-track gate",
            "Build and independently verify the complete ProtocolClaim"]
    }, indent=2, sort_keys=True))


if __name__ == "__main__":
    main()

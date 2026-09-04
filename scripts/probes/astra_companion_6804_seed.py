#!/usr/bin/env python3
"""Necessary interpolation checks for 68.04 after the upstream 68.03 update.

This has no phase-ledger bound and proves no ProtocolClaim. The previous
68.03 certificates do not automatically apply to these new parameters.
"""
import json

from astra_companion_parameters import N, P, W, locator_rank, scalar_row, score_check
from astra_companion_shared_candidate import coefficients_fast

ERRORS = 80791
UPSTREAM = "032154395c51fd6f77715a7f42d9a987ab9fb48a"


def main() -> None:
    rows = {}
    for name, m, limit, slope in (("A", 99, 217071, 30), ("B", 111, 17568, 33),
                                  ("C", 270, 130000, 81), ("T", 194, 6922, 60)):
        weighted = m*(N-ERRORS)
        y = (weighted-1)//W
        rank = locator_rank(m, limit, slope)
        nullity = coefficients_fast(weighted, limit, slope)-N*rank
        assert nullity > 0 and m+slope <= limit
        assert weighted+slope <= W*(y+1) and slope <= m < P
        rows[name] = {"multiplicity": m, "limit": limit, "slope": slope,
                      "weighted_degree": weighted, "y_cap": y,
                      "rank": rank, "signed_nullity_lower_bound": nullity}
    quotient = coefficients_fast(rows["T"]["weighted_degree"], 2, rows["T"]["slope"])
    assert rows["T"]["signed_nullity_lower_bound"]-quotient == 194725418
    scalar = scalar_row(ERRORS, 99, 136, 30)
    assert scalar["signed_nullity_lower_bound"] == 1496153
    assert scalar["mixed_degree"] == 2121253094 < P
    assert scalar["list_budget"] == 5529601254
    ordinary_mixed = (1+(W+1)*(2*136-2))*30+136*((2*30-1)*(W+1))
    assert ordinary_mixed == 2113404958 < P
    score = score_check(ERRORS, 6804)
    assert score["exact_integer_score_check"]
    assert not score_check(ERRORS-1, 6804)["exact_integer_score_check"]
    print(json.dumps({
        "status": "SEED_KERNELS_ONLY_PHASE_LEDGER_UNEVALUATED",
        "upstream_baseline_commit": UPSTREAM, "upstream_score": 6803,
        "target_score": score, "kernels": rows, "scalar": scalar,
        "T_quotient_dimension": quotient,
        "T_quotient_margin": rows["T"]["signed_nullity_lower_bound"]-quotient,
        "proposed_selected_total_cap": 6919,
        "ordinary_mixed_characteristic_endpoint": ordinary_mixed,
        "warning": "No 68.04 phase cap, combined-count estimate, or Lean proof has been established"
    }, indent=2, sort_keys=True))


if __name__ == "__main__":
    main()

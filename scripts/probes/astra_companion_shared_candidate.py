#!/usr/bin/env python3
"""Reproduce a numerically feasible 68.03 companion proof candidate.

No ProtocolClaim is proved here. The chain arithmetic has a separate Std Lean
certificate; its polynomial bridge and the phase certificate remain unported.
Use --check-phases to compile the exact C++ evaluator and replay the six sources
in three orders. This requires a compiler supporting signed 128-bit integers.
"""
from __future__ import annotations

import argparse
import json
from pathlib import Path
import re
import shutil
import subprocess
import tempfile

from astra_companion_chain_budget import audit
from astra_companion_parameters import (
    CAPACITY, COMMIT, FIELD_SIZE, N, P, W, locator_coefficients, locator_rank,
    locator_row, remaining_ledger, scalar_row, score_check,
)

SOURCES = [(8000, 560000, 2464), (4000, 280000, 1232),
           (1600, 112000, 492), (1200, 84000, 369),
           (650, 52000, 200), (250, 20000, 77)]
PHASE_CAP = 266199718851190708
FIXED_ALLOCATION = 266389641191084688


def coefficients_fast(weighted: int, limit: int, slope: int) -> int:
    """Same double sum, with the inner linear/quadratic sums evaluated exactly."""
    result = 0
    for j in range(slope+1):
        a, b = weighted-(W-1)*j, limit+1-j
        if a <= 0 or b <= 0:
            break
        last = min(b-1, (a-1)//W)
        sum1, sum2 = last*(last+1)//2, last*(last+1)*(2*last+1)//6
        result += (last+1)*b*a-(b*W+a)*sum1+W*sum2
    return result


def source_row(m: int, limit: int, slope: int) -> dict:
    weighted = m*(N-80781)
    y = (weighted-1)//W
    nullity = coefficients_fast(weighted, limit, slope)-N*locator_rank(m, limit, slope)
    mixed = 29*limit+6676*slope, 135*limit+6676*y, 135*slope+29*y
    assert nullity > 0 and m+slope <= limit and 0 < slope <= m < P
    assert weighted+slope <= W*(y+1)
    assert limit >= 6676 and y >= 135 and slope >= 29
    assert all(value < P for value in mixed)
    return {"multiplicity": m, "limit": limit, "slope": slope,
            "weighted_degree": weighted, "y_cap": y,
            "signed_nullity_lower_bound": nullity,
            "helper_mixed_degrees": mixed, "necessary_numeric_gates_pass": True}


def replay(sanitize: bool) -> dict:
    compiler = shutil.which("clang++") or shutil.which("g++")
    if not compiler:
        raise RuntimeError("a C++17 compiler supporting __int128 is required")
    source = Path(__file__).with_name("astra_companion_phases.cpp")
    flags = (["-O1", "-g", "-fsanitize=undefined", "-fno-sanitize-recover=all"]
             if sanitize else ["-O3"])
    results = {}
    with tempfile.TemporaryDirectory(prefix="astra-shared-chain-") as folder:
        binary = str(Path(folder)/"phases")
        subprocess.run([compiler, *flags, "-std=c++17", str(source), "-o", binary], check=True)
        for name, shapes in (("forward", SOURCES), ("reverse", SOURCES[::-1]),
                             ("rotated", SOURCES[2:]+SOURCES[:2])):
            run = subprocess.run([binary, "candidate-closure",
                                  *[str(x) for row in shapes for x in row]],
                                 capture_output=True, text=True, check=True)
            match = re.search(r"^FINAL .* max (\d+) at (\d+) (\d+) (\d+)",
                              run.stdout, re.MULTILINE)
            assert match and int(match[1]) == PHASE_CAP, run.stdout
            assert tuple(map(int, match.groups()[1:])) == (14, 35, 6523)
            assert not run.stderr, run.stderr
            results[name] = {"cap": int(match[1]), "maximizer": [14, 35, 6523],
                             "stdout": run.stdout.splitlines()}
    return results


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--check-phases", action="store_true")
    parser.add_argument("--sanitize", action="store_true",
                        help="run phase replay with undefined-behavior checks")
    args = parser.parse_args()
    kernels = {name: locator_row(80781, m, limit, slope)
               for name, m, limit, slope in
               (("A", 98, 130000, 29), ("B", 111, 14914, 33),
                ("C", 270, 130000, 81), ("T", 181, 6679, 56))}
    assert all(row["signed_nullity_lower_bound"] > 0 for row in kernels.values())
    for row in kernels.values():
        d, limit, slope = row["weighted_degree"], row["limit"], row["slope"]
        assert coefficients_fast(d, limit, slope) == locator_coefficients(d, limit, slope)
    scalar = scalar_row(80781, 97, 134, 29)
    assert scalar["signed_nullity_lower_bound"] > 0
    assert scalar["mixed_degree_below_characteristic"]
    quotient = locator_coefficients(kernels["T"]["weighted_degree"], 2, 56)
    assert kernels["T"]["signed_nullity_lower_bound"]-quotient == 40459519
    selected, residual = audit(6676), audit(14914)
    old = remaining_ledger(80781, 14914, 6679, scalar["list_budget"])
    shared_chain = residual["new_chain_charge"]
    other = (old["other_ledger_terms"]-selected["old_uniform_chain_charge"]-
             residual["old_uniform_chain_charge"]+shared_chain)
    assert CAPACITY-scalar["list_budget"]-other == FIXED_ALLOCATION
    combined_count = PHASE_CAP+other+scalar["list_budget"]
    margin = CAPACITY-combined_count
    assert margin == 189922339893980 and combined_count*2**128 <= FIELD_SIZE
    score = score_check(80781, 6803)
    assert score["error_cell_floor"] == 80781 and score["exact_integer_score_check"]
    print(json.dumps({
        "status": "NUMERICALLY_FEASIBLE_CANDIDATE_FULL_PROTOCOL_PROOF_UNPORTED",
        "source_commit": COMMIT, "score": score, "root_kernels": kernels,
        "scalar_kernel": scalar, "phase_sources": [source_row(*s) for s in SOURCES],
        "shared_chain_cap": shared_chain, "conditional_other_ledger_terms": other,
        "conditional_fixed_regular_allocation": FIXED_ALLOCATION,
        "phase_cap": PHASE_CAP, "phase_maximizer": [14, 35, 6523],
        "combined_count_including_list": combined_count, "field_capacity": CAPACITY,
        "count_margin": margin, "integer_capacity_inequality_passes": True,
        "phase_runs_this_invocation": replay(args.sanitize)
            if args.check_phases or args.sanitize else None,
        "lean_run_this_invocation": False,
        "lean_arithmetic_certificate": "scripts/probes/astra_companion_chain_budget.lean",
        "unproved_obligations": [
            "Port the polynomial derivative-support and regular-pair bridges",
            "Combine the fixed and residual covers using QB=H*Q",
            "Prove the strict-slope recursion for the six-source phase envelope",
            "Prove every retuned ordinary-factor, kernel, support, quotient, and characteristic gate",
            "Build ProtocolClaim 6803 10340095 33554432 with an allowed axiom census",
            "Obtain acceptance from the pinned independent verifier before claiming a score"]
    }, indent=2, sort_keys=True))


if __name__ == "__main__":
    main()

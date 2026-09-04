#!/usr/bin/env python3
"""Audit the correlated 68.03 formulas and failed 68.04 numerical candidates.

Optional --check-phases rebuilds/replays the C++ simultaneous-source closure.
That recursion is tighter than the official five-phase certificate and has a
separate generic Std Lean theorem; its numerical tables and polynomial bridges
have NOT been certified. No score or ProtocolClaim is proved by this script.
"""
from __future__ import annotations

import argparse
import json
from pathlib import Path
import re
import shutil
import subprocess
import tempfile

from astra_companion_parameters import (
    CAPACITY, N, P, W, locator_rank, regular_count, scalar_row, tight_count,
)
from astra_companion_shared_candidate import coefficients_fast

UPSTREAM = "032154395c51fd6f77715a7f42d9a987ab9fb48a"
OFFICIAL_SOURCES = [(7938, 526750, 2450), (4800, 328400, 1480),
                    (2400, 165000, 750), (1200, 82100, 370), (390, 19500, 120)]
FIRST_SOURCES = [(7999, 560000, 2464), (4000, 280000, 1232),
                 (1600, 112000, 492), (1200, 84000, 369),
                 (650, 52000, 200), (250, 20000, 77)]


def potential(errors: int, limit: int, y: int, slope: int,
              wide_y: int = 0, wide_slope: int = 0, padding: int = 0) -> tuple:
    gap = N-W-errors
    ay, ar, az = 1+2*W*max(y, wide_y), W*(2*max(slope, wide_slope)-1), 2*W*limit+1
    ceiling = lambda value: (value+gap-1)//gap
    return (ceiling((N-W)*(ay*slope+ar*y))+padding,
            ceiling((N-W)*(ar*limit+az*slope))+(errors+1)*slope+padding,
            ceiling((N-W)*(ay*limit+az*y))+(errors+1)*y+padding)


def chain_majorant(errors: int, z: int, r: int, y: int) -> int:
    """ChainGroupMaj.chainMaj, with ordinary Nat subtraction at zero."""
    gap = N-W-errors
    a = ((N-W)*((1+2*W*y)*z*r+W*max(0, 2*r-1)*2*z*y+(2*W*z+1)*y*r)
         +(errors+1)*gap*y*r)
    b = (N-W)*((1+2*W*y)*z+(2*W*z+1)*y)+(errors+1)*gap*y
    return (max(0, r-1)*a+b*r*max(0, r-1)//2)//gap


def correlated(errors: int, total: int, limit_b: int, t_y: int, t_s: int,
               r: int, v: int) -> int:
    agreements, residual_r = N-errors, 33-r
    return (chain_majorant(errors, total, r, r+v)
            +chain_majorant(errors, total, residual_r, 153-v)
            +regular_count(agreements, (153, max(1, residual_r), limit_b),
                           (t_y, t_s, total+3))
            +chain_majorant(errors, limit_b, residual_r, 153)
            +2*tight_count(agreements, 111*agreements, limit_b))


def dense_sources() -> list:
    """Reproduce a bounded 29-source ladder, not an optimality search."""
    sources = []
    for nominal in (96000, 48000, 24000, 12000, 8000, 6000, 4000, 3000, 2400,
                    2000, 1600, 1400, 1200, 1000, 900, 800, 700, 650, 600,
                    550, 500, 450, 400, 350, 300, 275, 250, 225, 200):
        slope, limit = (nominal*308+500)//1000, nominal*70
        for delta in (0, -1, 1, -2, 2):
            m = nominal+delta
            weighted = m*(N-80791)
            y = (weighted-1)//W
            if weighted+slope <= W*(y+1):
                break
        else:
            raise AssertionError("ladder shape needs a wider multiplicity search")
        assert coefficients_fast(weighted, limit, slope)-N*locator_rank(m, limit, slope) > 0
        sources.append((m, limit, slope))
    assert len(sources) == 29
    return sources


def source_rows(errors: int, root: tuple, shapes: list, padding: int) -> list:
    total, root_y, root_s, _, _, _ = root
    rows = []
    for m, limit, slope in shapes:
        weighted = m*(N-errors)
        y = (weighted-1)//W
        nullity = coefficients_fast(weighted, limit, slope)-N*locator_rank(m, limit, slope)
        assert nullity > 0 and m+slope <= limit and 0 < slope <= m < P
        assert weighted+slope <= W*(y+1)
        assert total <= limit and root_y <= y and root_s <= slope
        assert max(root_s*limit+total*slope, root_y*limit+total*y,
                   root_y*slope+root_s*y) < P
        rows.append({"multiplicity": m, "limit": limit, "slope": slope,
                     "y_cap": y, "nullity": nullity,
                     "potential": potential(errors, limit, y, slope, padding=padding)})
    return rows


def cases() -> list:
    return [
        {"name": "official_6803_sources_with_research_closure", "errors": 80781,
         "root": (6677, 135, 29, 153, 33, 130000), "joint": (111, 14915, 250, 56, 6680),
         "padding": 10000, "sources": OFFICIAL_SOURCES,
         "phase_cap": 271913004621405880, "maximizer": (12, 53, 2534), "scalar": (97, 133, 29)},
        {"name": "6804_first_valid_six_sources", "errors": 80791,
         "root": (6919, 136, 30, 153, 33, 217071), "joint": (111, 17568, 268, 60, 6922),
         "padding": 0, "sources": FIRST_SOURCES,
         "phase_cap": 295186676786672598, "maximizer": (12, 37, 4371), "scalar": (99, 136, 30)},
        {"name": "6804_dense_29_sources", "errors": 80791,
         "root": (6919, 136, 30, 153, 33, 217071), "joint": (111, 17568, 268, 60, 6922),
         "padding": 0, "sources": dense_sources(),
         "phase_cap": 293829520755502835, "maximizer": (10, 37, 2331), "scalar": (99, 136, 30)},
    ]


def arguments(case: dict, sources: list | None = None) -> list:
    values = ["candidate-closure", "--root", *case["root"], "--errors", case["errors"],
              "--padding", case["padding"], "--joint", *case["joint"],
              *[x for row in (case["sources"] if sources is None else sources) for x in row]]
    return [str(value) for value in values]


def check_phase(binary: str, case: dict, reverse: bool = False) -> dict:
    sources = case["sources"][::-1] if reverse else case["sources"]
    run = subprocess.run([binary, *arguments(case, sources)], capture_output=True,
                         text=True, check=True)
    assert not run.stderr, run.stderr
    match = re.search(r"^FINAL .* max (\d+) at (\d+) (\d+) (\d+)", run.stdout, re.MULTILINE)
    assert match and int(match[1]) == case["phase_cap"], run.stdout
    assert tuple(map(int, match.groups()[1:])) == case["maximizer"], run.stdout
    total, root_y, root_s, wide_y, wide_s, initial_limit = case["root"]
    initial = potential(case["errors"], initial_limit, root_y, root_s,
                        wide_y, wide_s, case["padding"])
    assert "initial_potential "+" ".join(map(str, initial)) in run.stdout
    _, limit_b, t_y, t_s, _ = case["joint"]
    r, v, _ = case["maximizer"]
    extra = correlated(case["errors"], total, limit_b, t_y, t_s, r, v)
    assert f"correlated_at_max {extra}\n" in run.stdout
    tails = 34*tight_count(N-case["errors"], 111*(N-case["errors"]), total)
    assert f"fixed_tails {tails} " in run.stdout
    return {"reverse_order": reverse, "stdout": run.stdout.splitlines()}


def fixtures() -> dict:
    """Literal current-upstream values and independent floor checks."""
    assert chain_majorant(80781, 6677, 33, 153) == 3662856455802725
    assert chain_majorant(80781, 14915, 33, 153) == 8182019282937326
    assert tight_count(181363, 111*181363, 6677) == 2093948826742
    assert tight_count(181363, 111*181363, 14915) == 4677667475173
    assert regular_count(181363, (153, 33, 14915), (250, 56, 6680)) == 531828045547854
    rows = source_rows(80781, cases()[0]["root"], OFFICIAL_SOURCES, 10000)
    assert [row["nullity"] for row in rows] == [36963750380693986577, 5090867013182078230,
        315862958949324685, 18278038734560710, 91073661700890]
    assert [row["potential"] for row in rows] == [
        (36764078701232, 1763223219624231, 7905084447061489),
        (13427735141811, 664006777607640, 2980009468608277),
        (3401226049834, 169036896818327, 748519503389805),
        (838681789895, 41479411858231, 186222646970525),
        (88195266130, 3190747159490, 14361692776390)]
    checks = 0
    for errors, limit in ((80781, 6677), (80781, 14915), (80791, 6919), (80791, 17568)):
        for r in range(34):
            for y in range(154):
                level_sum = sum(regular_count(N-errors, (y, t, limit), (y, r, limit))
                                for t in range(1, r))
                assert level_sum <= chain_majorant(errors, limit, r, y)
                assert chain_majorant(errors, limit, r, y)-level_sum <= max(0, r-2)
                checks += 1
    return {"upstream_literals_match": True, "independent_sum_of_floors_checks": checks}


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--check-phases", action="store_true")
    parser.add_argument("--reverse", action="store_true", help="also verify reversed source order")
    parser.add_argument("--sanitize", action="store_true", help="run phase checks with UBSan")
    args = parser.parse_args()
    result = {"upstream_commit": UPSTREAM, "fixtures": fixtures(), "cases": []}
    work = cases()
    for case in work:
        row = {key: value for key, value in case.items() if key not in ("sources", "scalar")}
        row["source_rows"] = source_rows(case["errors"], case["root"], case["sources"], case["padding"])
        scalar = scalar_row(case["errors"], *case["scalar"])
        assert scalar["signed_nullity_lower_bound"] > 0 and scalar["mixed_degree_below_characteristic"]
        row["list_budget"] = scalar["list_budget"]
        row["fixed_tails"] = 34*tight_count(N-case["errors"], 111*(N-case["errors"]), case["root"][0])
        row["combined_count"] = row["phase_cap"]+row["fixed_tails"]+row["list_budget"]
        row["margin"] = CAPACITY-row["combined_count"]
        row["numeric_budget_passes"] = row["margin"] >= 0
        assert row["numeric_budget_passes"] == (case["errors"] == 80781)
        result["cases"].append(row)
    if args.check_phases or args.sanitize or args.reverse:
        compiler = shutil.which("clang++") or shutil.which("g++")
        if not compiler:
            raise RuntimeError("a C++17 compiler supporting __int128 is required")
        with tempfile.TemporaryDirectory(prefix="astra-joint-") as folder:
            binary = str(Path(folder)/"phases")
            flags = ["-O1", "-fsanitize=undefined", "-fno-sanitize-recover=all"] if args.sanitize else ["-O3"]
            subprocess.run([compiler, *flags, "-std=c++17", str(Path(__file__).with_name(
                "astra_companion_phases.cpp")), "-o", binary], check=True)
            for case, row in zip(work, result["cases"]):
                row["phase_runs"] = [check_phase(binary, case)]
                if args.reverse:
                    row["phase_runs"].append(check_phase(binary, case, True))
    result["capacity"] = CAPACITY
    result["lean_certificate"] = "scripts/probes/astra_companion_phase_closure.lean"
    result["status"] = "CORRELATED_ARITHMETIC_AUDITED_6804_CANDIDATES_FAIL_NO_PROTOCOL_PROOF"
    print(json.dumps(result, indent=2, sort_keys=True))


if __name__ == "__main__":
    main()

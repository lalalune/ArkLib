#!/usr/bin/env python3
"""Reproduce the refined 49-source 68.04 candidate, which still fails.

The separate Lean strip projection is checked, but the source selector,
finite phase table, retuned ordinary gates, and ProtocolClaim are unproved.
"""
from __future__ import annotations

import argparse
import json
from pathlib import Path
import re
import shutil
import subprocess
import tempfile

from astra_companion_band_audit import clipped
from astra_companion_joint_audit import arguments, cases, potential, source_rows
from astra_companion_parameters import CAPACITY, N, W, locator_rank, scalar_row, tight_count
from astra_companion_shared_candidate import coefficients_fast

EXTRA_SOURCES = [
    (6800, 374000, 2097), (6600, 353813, 2048), (6600, 354151, 2047),
    (6600, 353821, 2049), (6700, 352579, 2080), (7900, 433893, 2451),
    (7900, 434129, 2450), (8100, 430245, 2513), (5200, 743497, 1594),
    (5200, 793272, 1593), (6500, 792924, 1985), (6300, 908306, 1920),
    (1320, 139822, 404), (1340, 139503, 410), (8100, 441374, 2513),
    (9000, 498998, 2791), (8300, 450469, 2575), (9200, 513485, 2853),
    (1340, 140119, 410), (1340, 143197, 410),
]
PHASE_CAP = 292132464649766823
POINT = (10, 37, 2317)


def strip_margin(shape: tuple, point: tuple) -> int:
    """Python count with direct kernel sums, independent of the affine search."""
    m, limit, slope = shape
    r, v, z = point
    d, delta = m*(N-80791), N-80791-W+1
    total, y = r+v+z, r+v
    source_y = (d-1)//W
    nullity = coefficients_fast(d, limit, slope)-N*locator_rank(m, limit, slope)
    fuel = min(limit//total, source_y//y, slope//r)
    high, cost = d-(W*y-r), 0
    for j in range(1, fuel+1):
        cost += clipped(high, delta, limit-j*total, source_y-j*y, slope-j*r)
        high = max(0, high-delta-(W*y-r))
    return nullity-cost


def search_checks(binary: str) -> list:
    records = []
    for z, passing in ((2250, 0), (2320, 4816)):
        run = subprocess.run([binary, "10", "37", str(z)], capture_output=True,
                             text=True, check=True)
        assert not run.stderr, run.stderr
        result = json.loads(run.stdout)
        assert result["tested_shapes"] == 8773 and result["passing_shapes"] == passing
        if passing:
            first = result["best_sources"][0]
            assert first == {"source": [7900, 433893, 2451],
                             "point_charge": 219771540758329579,
                             "strip_margin": 216537635742,
                             "kernel_nullity": 27098820480559716359}
        # Every reported witness is checked with Python integer kernel sums.
        for candidate in result["best_sources"]:
            m, limit, slope = shape = tuple(candidate["source"])
            point = (10, 37, z)
            assert strip_margin(shape, point) == candidate["strip_margin"] > 0
            assert strip_margin((m, limit-1, slope), point) <= 0
            d = m*(N-80791)
            assert coefficients_fast(d, limit, slope)-N*locator_rank(m, limit, slope) == candidate["kernel_nullity"]
            charge = potential(80791, limit, (d-1)//W, slope)
            assert sum(a*b for a, b in zip(charge, (47+z, 47, 10))) == candidate["point_charge"]
        records.append(result)
    for bad in ([], ["0", "37", "2320"], ["10x", "37", "2320"],
                ["10", "137", "2320"], ["10", "37", "-1"],
                ["10", "37", "2320", "100001"]):
        run = subprocess.run([binary, *bad], capture_output=True, text=True)
        assert run.returncode != 0 and "source search error:" in run.stderr
    return records


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--check-search", action="store_true")
    parser.add_argument("--check-phases", action="store_true")
    parser.add_argument("--reverse", action="store_true")
    parser.add_argument("--sanitize", action="store_true")
    args = parser.parse_args()
    case = cases()[2]
    case["sources"] += EXTRA_SOURCES
    assert len(case["sources"]) == len(set(case["sources"])) == 49
    roots = source_rows(80791, case["root"], case["sources"], 0)
    scalar = scalar_row(80791, 99, 136, 30)
    assert scalar["signed_nullity_lower_bound"] > 0 and scalar["mixed_degree_below_characteristic"]
    tails = 34*tight_count(N-80791, 111*(N-80791), case["root"][0])
    combined = PHASE_CAP+tails+scalar["list_budget"]
    assert tails == 73789382345390 and scalar["list_budget"] == 5529601254
    assert combined == 292206259561713467 > CAPACITY
    assert strip_margin((7900, 433893, 2451), (10, 37, 2320)) == 216537635742
    result = {"status": "REFINED_49_SOURCE_CANDIDATE_FAILS_NO_PROTOCOL_PROOF",
              "phase_cap": PHASE_CAP, "maximizer": POINT, "root": case["root"],
              "joint": case["joint"], "errors": 80791, "band_rule": "clipped",
              "sources": roots, "fixed_tails": tails, "list_count": scalar["list_budget"],
              "combined_count": combined, "capacity": CAPACITY,
              "excess": combined-CAPACITY, "budget_passes": False}
    if args.check_search or args.check_phases or args.reverse or args.sanitize:
        compiler = shutil.which("clang++") or shutil.which("g++")
        if not compiler:
            raise RuntimeError("a C++17 compiler supporting signed __int128 is required")
        flags = ["-O1", "-fsanitize=undefined", "-fno-sanitize-recover=all"] if args.sanitize else ["-O3"]
        with tempfile.TemporaryDirectory(prefix="astra-limit-") as folder:
            if args.check_search or args.sanitize:
                search = str(Path(folder)/"search")
                subprocess.run([compiler, *flags, "-std=c++17", str(Path(__file__).with_name(
                    "astra_companion_source_limit.cpp")), "-o", search], check=True)
                result["search_replays"] = search_checks(search)
                result["malformed_argument_rejections"] = 6
            if args.check_phases or args.reverse or args.sanitize:
                phase = str(Path(folder)/"phases")
                subprocess.run([compiler, *flags, "-std=c++17", str(Path(__file__).with_name(
                    "astra_companion_phases.cpp")), "-o", phase], check=True)
                runs = []
                for reverse in ([False, True] if args.reverse else [False]):
                    sources = case["sources"][::-1] if reverse else case["sources"]
                    command = [phase, "candidate-closure", "--clipped-band", *arguments(case, sources)[1:]]
                    run = subprocess.run(command, capture_output=True, text=True, check=True)
                    assert not run.stderr, run.stderr
                    match = re.search(r"^FINAL .* max (\d+) at (\d+) (\d+) (\d+)", run.stdout, re.MULTILINE)
                    assert match and int(match[1]) == PHASE_CAP, run.stdout
                    assert tuple(map(int, match.groups()[1:])) == POINT, run.stdout
                    runs.append({"reverse": reverse, "stdout": run.stdout.splitlines()})
                result["phase_replays"] = runs
    print(json.dumps(result, indent=2, sort_keys=True))


if __name__ == "__main__":
    main()

#!/usr/bin/env python3
"""Audit the bounded factor-partition experiment and its surviving obstruction.

These are numerical proof-method obstructions, not adversarial polynomial
witnesses, impossibility results, or ProtocolClaims.
"""
from __future__ import annotations

import argparse
import json
from pathlib import Path
import re
import shutil
import subprocess
import tempfile

from astra_companion_joint_audit import arguments, cases, correlated, potential
from astra_companion_limit_audit import EXTRA_SOURCES, PHASE_CAP, POINT, strip_margin
from astra_companion_parameters import CAPACITY, W, N, locator_rank, scalar_row, tight_count
from astra_companion_shared_candidate import coefficients_fast


def mixed(p: tuple, q: tuple, f: tuple) -> int:
    z, v, r = p
    qz, qv, qr = q
    fz, fv, fr = f
    return ((qr*fr+qv*fr+qr*fv)*(z+v+r)+(qz*fr+qr*fz)*(v+r)
            +(qv*fv+qz*fv+qv*fz)*r)


def single_cost(r: int, v: int, z: int) -> int:
    """Independent Python transcription of the C2 branch, r>=3 and v>=2."""
    assert r >= 3 and v >= 2
    factor = (z, v, r)
    first = (2*z*(W+1), 1+2*v*(W+1), 2*(r-1)*(W+1))
    rational = ((W+3)*z, (W+3)*(v-1)+2, (W+3)*(r-2)+3)
    fiber = (z, v, r+1)
    cut = (rational[0], rational[1]+W+1, rational[2]+2*(W+1))
    return mixed(factor, first, rational)+(W+5)*mixed(factor, fiber, cut)


def point_audit(case: dict, point: tuple) -> dict:
    r, v, z = point
    ordinary = single_cost(r, v, z)
    rows = []
    for m, limit, slope in case["sources"]:
        shape = (m, limit, slope)
        if strip_margin(shape, point) > 0:
            y = (m*(N-80791)-1)//W
            coefficients = potential(80791, limit, y, slope)
            charge = sum(a*b for a, b in zip(coefficients, (r+v+z, r+v, r)))
            rows.append({"source": shape, "charge": charge})
    best = min([ordinary]+[row["charge"] for row in rows])
    total, root_y, root_r, wide_y, wide_r, limit_a = case["root"]
    remaining_total, remaining_y, remaining_r = total-r-v-z, wide_y-r-v, wide_r-r
    rr = min(remaining_total, remaining_y, remaining_r)
    rv = min(remaining_total-rr, remaining_y-rr)
    initial = potential(80791, limit_a, root_y, root_r, wide_y, wide_r)
    initial_cost = sum(a*b for a, b in zip(initial, (remaining_total, rr+rv, rr)))
    _, limit_b, t_y, t_r, _ = case["joint"]
    complement = initial_cost+correlated(80791, total, limit_b, t_y, t_r, r, v)
    tails = 34*tight_count(N-80791, 111*(N-80791), total)
    scalar = scalar_row(80791, 99, 136, 30)["list_budget"]
    count = best+complement+tails+scalar
    assert count > CAPACITY
    return {"point": point, "ordinary_single": ordinary, "routed_sources": rows,
            "best_single": best, "complement": complement, "fixed_tails": tails,
            "list_count": scalar, "combined_singleton_allowance": count,
            "excess": count-CAPACITY, "budget_passes": False}


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--check-partition", action="store_true")
    parser.add_argument("--check-dense-source", action="store_true")
    parser.add_argument("--sanitize", action="store_true")
    args = parser.parse_args()
    case = cases()[2]
    case["sources"] += EXTRA_SOURCES
    rows = [point_audit(case, p) for p in (POINT, (10, 37, 2310))]
    assert rows[0]["ordinary_single"] == rows[0]["best_single"] == 283403712362442072
    assert len(rows[0]["routed_sources"]) == 6
    assert min(r["charge"] for r in rows[0]["routed_sources"]) == 286642894046259837
    assert rows[0]["combined_singleton_allowance"] == 292206259561713467
    result = {"status": "BOUNDED_PARTITION_REFINEMENT_DOES_NOT_CLOSE_6804",
              "capacity": CAPACITY, "rectangle": [12, 48, 3000], "points": rows,
              "warning": "No existence claim for a polynomial at these abstract flags"}
    if args.check_partition or args.check_dense_source or args.sanitize:
        compiler = shutil.which("clang++") or shutil.which("g++")
        if not compiler:
            raise RuntimeError("a C++17 compiler supporting __int128 is required")
        flags = ["-O1", "-fsanitize=undefined", "-fno-sanitize-recover=all"] if args.sanitize else ["-O3"]
        with tempfile.TemporaryDirectory(prefix="astra-atoms-") as folder:
            if args.check_dense_source:
                search = str(Path(folder)/"search")
                subprocess.run([compiler, *flags, "-std=c++17", str(Path(__file__).with_name(
                    "astra_companion_source_limit.cpp")), "-o", search], check=True)
                run = subprocess.run([search, "10", "37", "2310", "--dense-local"],
                                     capture_output=True, text=True, check=True)
                assert not run.stderr, run.stderr
                dense = json.loads(run.stdout)
                assert dense["grid"] == "dense-local"
                assert (dense["min_multiplicity"], dense["max_multiplicity"]) == (8000, 11000)
                assert (dense["tested_shapes"], dense["passing_shapes"]) == (627767, 35452)
                assert dense["best_sources"][0] == {
                    "source": [9918, 553718, 3076], "point_charge": 349193997186658117,
                    "strip_margin": 10597174107, "kernel_nullity": 69199373378536160871}
                for witness in dense["best_sources"]:
                    m, limit, slope = shape = tuple(witness["source"])
                    point = (10, 37, 2310)
                    assert strip_margin(shape, point) == witness["strip_margin"] > 0
                    assert strip_margin((m, limit-1, slope), point) <= 0
                    d = m*(N-80791)
                    assert coefficients_fast(d, limit, slope)-N*locator_rank(m, limit, slope) == witness["kernel_nullity"]
                    charge = potential(80791, limit, (d-1)//W, slope)
                    assert sum(a*b for a, b in zip(charge, (2357, 47, 10))) == witness["point_charge"]
                assert dense["best_sources"][0]["point_charge"] > rows[1]["ordinary_single"]
                result["dense_source_run"] = {**dense, "sanitized": args.sanitize,
                                              "independently_checked_witnesses": 20}
            if not (args.check_partition or args.sanitize):
                print(json.dumps(result, indent=2, sort_keys=True))
                return
            binary = str(Path(folder)/"partition")
            subprocess.run([compiler, *flags, "-std=c++17", str(Path(__file__).with_name(
                "astra_companion_atom_partition.cpp")), "-o", binary], check=True)
            test = subprocess.run([binary, "self-test"], capture_output=True, text=True, check=True)
            assert test.stdout == "ATOM_CONVOLUTION_SELF_TEST 1000 exact_cases_passed\n"
            assert not test.stderr
            run = subprocess.run([binary, "candidate-closure", "--clipped-band", *arguments(case)[1:]],
                                 capture_output=True, text=True, check=True)
            assert not run.stderr, run.stderr
            match = re.search(r"^FINAL .* max (\d+) at (\d+) (\d+) (\d+)", run.stdout, re.MULTILINE)
            assert match and int(match[1]) == PHASE_CAP
            assert tuple(map(int, match.groups()[1:])) == POINT
            details = re.search(r"^ATOM_PARTITION rectangle 12 48 3000 convolutions (\d+) improved_cells (\d+) singleton (\d+) point_before (\d+) point_after (\d+)$", run.stdout, re.MULTILINE)
            assert details and tuple(map(int, details.groups())) == (
                48528, 125020, 283403712362442072, 283403712362442072, 283403712362442072)
            result["partition_run"] = {"phase_cap": PHASE_CAP, "maximizer": POINT,
                "interval_convolutions": 48528, "directly_improved_cells": 125020,
                "convolution_cross_checks": 1000, "sanitized": args.sanitize}
    print(json.dumps(result, indent=2, sort_keys=True))


if __name__ == "__main__":
    main()

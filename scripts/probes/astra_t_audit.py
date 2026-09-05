#!/usr/bin/env python3
"""T-interpolant quotient-cutoff audit at error80791; no protocol proof.

The optional phase replay uses an explicit --quotient-cutoff argument. Every
count uses the explicit supplied T.L; no total+3 identity is silently assumed.
The CLI checks consistency, while the dimension witness is verified here.
"""
from __future__ import annotations

import argparse
import hashlib
import json
from pathlib import Path
import re
import shutil
import subprocess
import tempfile

from astra_companion_joint_audit import chain_majorant, dense_sources, potential, source_rows
from astra_companion_limit_audit import EXTRA_SOURCES
from astra_companion_band_audit import channels, clipped
from astra_companion_atom_audit import single_cost
from astra_companion_parameters import CAPACITY, N, P, W, locator_rank, regular_count, tight_count
from astra_companion_shared_candidate import coefficients_fast

ERRORS, AGREEMENTS = 80791, 181353
UPSTREAM = "032154395c51fd6f77715a7f42d9a987ab9fb48a"
POINT = (10, 37, 2317)
ATOM = 283403712362442072
LIST = 5529601254
BASELINE = 292206259561713467
CASES = [
    ("old_T", 194, 6922, 60, 2),
    ("same_shape_cutoff4", 194, 6923, 60, 4),
    ("least_selected_cap", 197, 6922, 61, 4),
    ("least_old_point_charge", 166, 7159, 51, 1),
]


def kernel_row(m: int, limit: int, slope: int, cutoff: int) -> dict:
    d = m*AGREEMENTS
    y = (d-1)//W
    nullity = coefficients_fast(d, limit, slope)-N*locator_rank(m, limit, slope)
    quotient = coefficients_fast(d, cutoff, slope)
    assert 0 <= slope <= m <= 270 < P and slope <= 81
    assert m+slope <= limit <= 130000
    assert d+slope <= W*(y+1) and d <= 270*AGREEMENTS
    assert nullity > quotient and 0 <= cutoff < limit
    return {"m": m, "L": limit, "S": slope, "Y": y, "k": cutoff,
            "D": d, "selected_cap": limit-cutoff-1, "nullity": nullity,
            "quotient": quotient, "margin": nullity-quotient}


def point_ledger(row: dict, point: tuple = POINT) -> dict:
    """Uses actual T.L; there is deliberately no inferred total+3 identity."""
    r, v, z = point
    total, limit, y, slope = (row[key] for key in ("selected_cap", "L", "Y", "S"))
    residual_r = 33-r
    correlated = (chain_majorant(ERRORS, total, r, r+v)
        +chain_majorant(ERRORS, total, residual_r, 153-v)
        +regular_count(AGREEMENTS, (153, max(1, residual_r), 17568), (y, slope, limit))
        +chain_majorant(ERRORS, 17568, residual_r, 153)
        +2*tight_count(AGREEMENTS, 111*AGREEMENTS, 17568))
    initial = potential(ERRORS, 217071, 136, 30, 153, 33)
    remaining = total-r-v-z
    assert remaining >= 0
    nr = min(remaining, 153-r-v, residual_r)
    nv = min(remaining-nr, 153-r-v-nr)
    complement = sum(a*b for a, b in zip(initial, (remaining, nr+nv, nr)))
    tails = 34*tight_count(AGREEMENTS, 111*AGREEMENTS, total)
    combined = ATOM+correlated+complement+tails+LIST
    return {"point": point, "atom_allowance": ATOM, "correlated": correlated,
            "initial_complement": complement, "fixed_tails": tails,
            "list_count": LIST, "combined_at_old_point": combined,
            "change_from_old_point": combined-BASELINE,
            "excess_over_capacity": combined-CAPACITY}


def quotient_flags() -> list:
    """Necessary quotient dimensions, conditional on actual divisor R/Y caps.

    If R(F)>=r and YS(F)>=y, contact(F)>=w*y-R(F) needs an UPPER
    bound on R(F). Here r is the actual R degree, not merely a lower bound.
    The weighted quotient uses D-(w*y-r) and S-r.
    """
    rows = []
    for m, s in ((194, 60), (197, 61)):
        d = m*AGREEMENTS
        base = coefficients_fast(d, 100000, s)-N*locator_rank(m, 100000, s)
        lam = coefficients_fast(d, 100001, s)-N*locator_rank(m, 100001, s)-base
        for r, y in ((0, 0), (1, 1), (10, 47), (30, 136), (33, 153)):
            assert r <= s and W*y >= r
            candidates = []
            for k in range(100):
                q = coefficients_fast(max(0, d-(W*y-r)), k, s-r)
                limit = 100000+(q+1-base+lam-1)//lam
                nullity = coefficients_fast(d, limit, s)-N*locator_rank(m, limit, s)
                assert nullity > q
                candidates.append((limit-k-1, limit, k, q, nullity-q))
            selected, limit, k, q, margin = min(candidates)
            rows.append({"m": m, "S": s, "actual_divisor_R": r,
                         "actual_divisor_YS": y, "selected_cap": selected,
                         "L": limit, "k": k, "quotient": q, "margin": margin})
    return rows


def singleton_obstruction() -> dict:
    """Certify the fixed point's lower bound on this numerical envelope.

    This is a lower bound on an algorithmic allowance, not on actual bad seeds.
    Every routeable source at this point costs more than the singleton; every
    prefix defect is nonnegative, so no phase can lower the point below ATOM.
    """
    r, v, z = POINT
    assert single_cost(r, v, z) == ATOM > CAPACITY
    routed = []
    shapes = dense_sources()+EXTRA_SOURCES
    for m, limit, s in shapes:
        d, delta = m*AGREEMENTS, AGREEMENTS-W+1
        y = (d-1)//W
        nullity = coefficients_fast(d, limit, s)-N*locator_rank(m, limit, s)
        total, middle = r+v+z, r+v
        fuel = min(limit//total, y//middle, s//r)
        high, band, strip = max(0, d-(W*middle-r)), 0, 0
        for j in range(1, fuel+1):
            qt, qy, qs = limit-j*total, y-j*middle, s-j*r
            band += delta*channels(qt, qy, qs)
            strip += clipped(high, delta, qt, qy, qs)
            high = max(0, high-delta-(W*middle-r))
        assert 0 <= strip <= band
        if band < nullity or strip < nullity:
            coefficients = potential(ERRORS, limit, y, s)
            charge = sum(a*b for a,b in zip(coefficients, (total, middle, r)))
            assert charge > ATOM
            routed.append({"source": (m, limit, s), "charge": charge,
                           "strip_margin": nullity-strip})
    assert len(routed) == 6 and min(row["charge"] for row in routed) == 286642894046259837
    initial = potential(ERRORS, 217071, 136, 30, 153, 33)
    assert all(c > 0 for c in initial)
    # For every selected>=6917 the complement has saturated R/Y caps.
    assert 6917-sum(POINT) >= 153-POINT[0]-POINT[1] >= 33-POINT[0] >= 0
    return {"point": POINT, "ordinary_allowance": ATOM,
            "routeable_sources": routed,
            "minimum_routeable_charge": min(row["charge"] for row in routed),
            "initial_potential_coefficients_positive": True,
            "selected_cap_lower_bound": 6917,
            "scope": "Lower bound on the fixed 49-source numerical envelope, not on actual errors"}


def phase_replays(folder: Path, compiler: str, flags: list, rows: list,
                  reverse: bool) -> dict:
    source_path = Path(__file__).with_name("astra_companion_phases.cpp")
    original = source_path.read_bytes()
    binary = str(folder/"phases")
    subprocess.run([compiler, *flags, "-std=c++17", str(source_path), "-o", binary], check=True)
    shapes = dense_sources()+EXTRA_SOURCES
    assert len(shapes) == 49
    if reverse:
        shapes.reverse()
    result = {"shared_source_sha256": hashlib.sha256(original).hexdigest(),
              "shared_source_modified": False,
              "explicit_cutoff_argument": "--quotient-cutoff",
              "reverse_sources": reverse, "runs": []}
    for row in rows:
        total, limit, y, slope = (row[key] for key in ("selected_cap", "L", "Y", "S"))
        root = (total, 136, 30, 153, 33, 217071)
        source_rows(ERRORS, root, shapes, 0)
        args = ["candidate-closure", "--clipped-band", "--root", *root,
                "--errors", ERRORS, "--padding", 0,
                "--joint", 111, 17568, y, slope, limit,
                "--quotient-cutoff", row["k"],
                *[x for shape in shapes for x in shape]]
        run = subprocess.run([binary, *map(str, args)], capture_output=True,
                             text=True, check=True)
        assert not run.stderr, run.stderr
        match = re.search(r"^FINAL .* max (\d+) at (\d+) (\d+) (\d+)", run.stdout, re.M)
        assert match, run.stdout
        assert f'QUOTIENT cutoff {row["k"]} total_cap {total} limit {limit}\n' in run.stdout
        point = tuple(map(int, match.groups()[1:]))
        phase_cap = int(match[1])
        ledger = point_ledger(row, point)
        # This assertion also checks that the critical singleton survives.
        assert point == POINT and phase_cap+ledger["fixed_tails"]+LIST == ledger["combined_at_old_point"]
        assert f'correlated_at_max {ledger["correlated"]}\n' in run.stdout
        result["runs"].append({"name": row["name"], "phase_cap": phase_cap,
                               "maximizer": point, **ledger})
    return result


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--check-search", action="store_true")
    parser.add_argument("--check-phases", action="store_true")
    parser.add_argument("--reverse", action="store_true")
    parser.add_argument("--sanitize", action="store_true")
    parser.add_argument("--phase-case", choices=[case[0] for case in CASES],
                        help="replay only this case; arithmetic checks still cover every case")
    args = parser.parse_args()
    rows = [{"name": name, **kernel_row(m, limit, slope, cutoff)}
            for name, m, limit, slope, cutoff in CASES]
    for row in rows:
        row["ledger_at_old_point"] = point_ledger(row)
    assert [row["ledger_at_old_point"]["combined_at_old_point"] for row in rows] == [
        292206259561713467, 292206040206005516, 292222169121174681, 292119564672092577]
    result = {"status": "T_CAP_AND_LEDGER_PROBES_NO_PROTOCOL_PROOF",
              "upstream": UPSTREAM, "errors": ERRORS, "capacity": CAPACITY,
              "cases": rows, "conditional_quotient_flags": quotient_flags(),
              "singleton_envelope_obstruction": singleton_obstruction()}
    if args.check_search or args.check_phases or args.reverse or args.sanitize:
        compiler = shutil.which("clang++") or shutil.which("g++")
        if not compiler:
            raise RuntimeError("a C++17 compiler with __int128 is required")
        flags = ["-O1", "-fsanitize=undefined", "-fno-sanitize-recover=all"] if args.sanitize else ["-O3"]
        with tempfile.TemporaryDirectory(prefix="astra-t-") as temp:
            folder = Path(temp)
            if args.check_search or args.sanitize:
                binary = str(folder/"search")
                subprocess.run([compiler, *flags, "-std=c++17", str(Path(__file__).with_name(
                    "astra_t_cutoff.cpp")), "-o", binary], check=True)
                run = subprocess.run([binary, "--all"], capture_output=True, text=True, check=True)
                assert not run.stderr, run.stderr
                search = json.loads(run.stdout)
                assert search["shapes"] == 18900 and search["small_L_checks"] == 1145265
                assert search["eligible_rows"] == 5205
                best = search.pop("best_rows")
                for row in best:
                    assert row["selected_cap"] >= 6917 and row["S"] > 0
                    row["ledger_at_old_point"] = point_ledger(row)
                best.sort(key=lambda row: row["ledger_at_old_point"]["combined_at_old_point"])
                for row in best[:20]:
                    exact = kernel_row(row["m"], row["L"], row["S"], row["k"])
                    assert all(row[key] == value for key, value in exact.items())
                    previous = coefficients_fast(row["D"], row["L"]-1, row["S"])-N*locator_rank(
                        row["m"], row["L"]-1, row["S"])
                    assert previous <= row["quotient"]
                    assert row["lambda"]*row["L"]+row["beta"] == row["nullity"]
                    # Independently enumerate the entire ramp-transition range
                    # for each returned shape. Beyond it Q is affine with slope
                    # strictly greater than kernel-nullity slope, so no cutoff
                    # can improve the selected cap.
                    qs = [coefficients_fast(row["D"], k, row["S"])
                          for k in range(row["Y"]+row["S"]+4)]
                    differences = [b-a for a,b in zip(qs, qs[1:])]
                    assert differences == sorted(differences)
                    assert differences[-1] > row["lambda"]
                    best_selected = min((q+1-row["beta"]+row["lambda"]-1)//row["lambda"]-k-1
                                        for k,q in enumerate(qs))
                    assert best_selected >= 6917
                assert (best[0]["m"], best[0]["L"], best[0]["S"], best[0]["k"]) == (166,7159,51,1)
                search["least_point_charge_rows"] = best[:20]
                search["minimum_point_lower_bound_for_bounded_envelope"] = best[0]["ledger_at_old_point"]["combined_at_old_point"]
                search["point_lower_bound_requires_fixed_sources_and_monotone_ledger"] = True
                result["bounded_search"] = search
            if args.check_phases or args.reverse or args.sanitize:
                phase_rows = [row for row in rows if not args.phase_case or row["name"] == args.phase_case]
                result["phase_replays"] = phase_replays(folder, compiler, flags, phase_rows, args.reverse)
    print(json.dumps(result, indent=2, sort_keys=True))


if __name__ == "__main__":
    main()

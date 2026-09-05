#!/usr/bin/env python3
"""Exact contact-strip arithmetic and optional retuned phase experiments.

This is not a polynomial rank proof or a ProtocolClaim. The matching Std Lean
file proves the channel interval/indexing lemmas, not this whole computation.
"""
from __future__ import annotations

import argparse
import json
from pathlib import Path
import random
import re
import shutil
import subprocess
import tempfile

from astra_companion_parameters import CAPACITY, W
from astra_companion_joint_audit import arguments, cases


def channels(t: int, y: int, s: int) -> int:
    u = min(t, y)
    j = min(u, s)
    b, c = u+1, t+1
    return ((j+1)*(2*b*c-b*b+b)-(2*c+1)*j*(j+1)//2+j*(j+1)*(2*j+1)//6)//2


def ramp(base: int, last: int) -> int:
    first = max(0, 1-base)
    return (last-first+1)*(2*base+first+last)//2 if first <= last else 0


def clipped(high: int, delta: int, t: int, y: int, s: int) -> int:
    if not high or not delta:
        return 0
    top = min(t, y, (high+s-1)//W)
    full = min(t, y, (high-delta)//W) if high >= delta else -1
    result = delta*channels(t, full, s) if full >= 0 else 0
    for k in range(full+1, top+1):
        result += (t-k+1)*(ramp(high-W*k, min(k, s))-
                           ramp(high-W*k-delta, min(k, s)))
    return result


def naive_strip(high: int, delta: int, t: int, y: int, s: int) -> int:
    """Direct sum in the original separate Y and R coordinates."""
    return sum((t+1-a-r)*(max(0, high-W*a-(W-1)*r)-
                           max(0, max(0, high-delta)-W*a-(W-1)*r))
               for a in range(min(t, y)+1) for r in range(min(s, t-a, y-a)+1))


def nested_coefficients(high: int, t: int, y: int, s: int) -> int:
    """Count the whole nested box by summing R first, independently of strip rows."""
    result = 0
    for r in range(min(s, t, y)+1):
        a, b = high-(W-1)*r, t-r+1
        if a <= 0:
            break
        last = min(t-r, y-r, (a-1)//W)
        sum1, sum2 = last*(last+1)//2, last*(last+1)*(2*last+1)//6
        result += (last+1)*a*b-(a+b*W)*sum1+W*sum2
    return result


def checks() -> tuple[dict, list]:
    samples = []
    small = 0
    for t in range(9):
        for y in range(9):
            for s in range(9):
                for delta in (0, 1, 2, 50283, W, W+1):
                    for high in sorted({0, 1, max(0, delta-1), delta, delta+1,
                                        W-1, W, W+1, 2*W-1, 2*W, 2*W+1}):
                        value = clipped(high, delta, t, y, s)
                        assert value == naive_strip(high, delta, t, y, s)
                        small += 1
                        if small % 29 == 0:
                            samples.append((high, delta, t, y, s, value))
    rng = random.Random(6804)
    for _ in range(160):
        t, y, s = rng.randrange(20000000), rng.randrange(140000), rng.randrange(40000)
        high, delta = rng.randrange(20000000000), rng.randrange(200000)
        value = clipped(high, delta, t, y, s)
        assert value == nested_coefficients(high, t, y, s)-nested_coefficients(max(0, high-delta), t, y, s)
        thin = delta*channels(t, min(y, max(0, high+s-1)//W), s)
        assert value <= thin
        samples.append((high, delta, t, y, s, value))
    return {"direct_small_box_checks": small, "independent_large_box_difference_checks": 160}, samples


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--check-cpp", action="store_true")
    parser.add_argument("--check-phases", action="store_true")
    parser.add_argument("--sanitize", action="store_true")
    args = parser.parse_args()
    result, samples = checks()
    result["status"] = "EXACT_STRIP_ARITHMETIC_ONLY_POLYNOMIAL_RANK_BRIDGE_UNPROVED"
    result["lean_certificate"] = "scripts/probes/astra_companion_band_strip.lean"
    if args.check_cpp or args.check_phases or args.sanitize:
        compiler = shutil.which("clang++") or shutil.which("g++")
        if not compiler:
            raise RuntimeError("C++17 compiler supporting signed __int128 required")
        source = Path(__file__).with_name("astra_companion_phases.cpp").resolve()
        flags = ["-O1", "-fsanitize=undefined", "-fno-sanitize-recover=all"] if args.sanitize else ["-O3"]
        with tempfile.TemporaryDirectory(prefix="astra-strip-") as folder:
            driver = Path(folder)/"strip.cpp"
            driver.write_text('#define main phase_evaluator_main\n#include '+json.dumps(str(source))+
                '\n#undef main\nint main() { std::int64_t h; int d,t,y,s; '
                'while (std::cin>>h>>d>>t>>y>>s) std::cout<<decimal(clipped_band(h,d,t,y,s))<<"\\n"; }\n')
            binary = str(Path(folder)/"strip")
            subprocess.run([compiler, *flags, "-std=c++17", str(driver), "-o", binary], check=True)
            run = subprocess.run([binary], input="".join(" ".join(map(str, row[:5]))+"\n" for row in samples),
                                 capture_output=True, text=True, check=True)
            assert not run.stderr, run.stderr
            assert list(map(int, run.stdout.split())) == [row[5] for row in samples]
            result["cpp_cross_checks"] = len(samples)
            if args.check_phases or args.sanitize:
                phase = str(Path(folder)/"phases")
                subprocess.run([compiler, *flags, "-std=c++17", str(source), "-o", phase], check=True)
                runs = []
                for name, rule, case, expected, point in (
                    ("six_actual_contact", "--actual-contact", cases()[1], 295065697758669524, (12, 37, 4371)),
                    ("six_clipped_strip", "--clipped-band", cases()[1], 294944000934875098, (12, 37, 4368)),
                    ("thirty_clipped_strip", "--clipped-band", cases()[2], 293708302462235977, (10, 37, 2330))):
                    if name.startswith("thirty"):
                        case["sources"].append((6800, 374000, 2097))
                    command = [phase, *arguments(case)]
                    command.insert(2, rule)
                    run = subprocess.run(command, capture_output=True, text=True, check=True)
                    assert not run.stderr, run.stderr
                    match = re.search(r"^FINAL .* max (\d+) at (\d+) (\d+) (\d+)", run.stdout, re.MULTILINE)
                    assert match and int(match[1]) == expected, run.stdout
                    assert tuple(map(int, match.groups()[1:])) == point, run.stdout
                    count = expected+73789382345390+5529601254
                    assert count > CAPACITY
                    runs.append({"name": name, "conditional_phase_cap": expected,
                                 "maximizer": point, "combined_count": count,
                                 "excess": count-CAPACITY, "budget_passes": False})
                result["phase_runs"] = runs
    print(json.dumps(result, indent=2, sort_keys=True))


if __name__ == "__main__":
    main()

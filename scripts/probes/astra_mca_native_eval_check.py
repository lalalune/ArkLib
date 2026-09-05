#!/usr/bin/env python3
"""Bounded independent acceptance for the native compact MCA evaluator.

Compiles a small binary under the system temporary directory by default. Never
starts a production scan or allocates a production array. --benchmark measures
complete evaluations on at most 2^20 slots per run, not a full-domain count.
"""

import argparse
import hashlib
import json
from pathlib import Path
import random
import subprocess
import tempfile

from astra_mca_twogen_lift_eval import P, PRODUCTION_N, RecursiveMap


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--binary", type=Path)
    parser.add_argument("--benchmark", action="store_true")
    args = parser.parse_args()
    source = Path(__file__).with_suffix(".cpp")
    # The C++ evaluator and this checker intentionally have different basenames.
    source = source.with_name("astra_mca_native_eval.cpp")
    digest = hashlib.sha256(source.read_bytes()).hexdigest()
    binary = args.binary
    if binary is None:
        binary = Path(tempfile.gettempdir()) / ("astra-mca-native-" + digest[:16])
        subprocess.run(["clang++", "-std=c++17", "-O3", "-pthread", "-Wall", "-Wextra",
                        str(source), "-o", str(binary)], check=True)

    def run(*arguments, stdin=None, expected_success=True, timeout=None):
        result = subprocess.run([str(binary), *map(str, arguments)], input=stdin,
                                text=True, capture_output=True, timeout=timeout)
        if expected_success:
            assert result.returncode == 0, (arguments, result.stderr)
        return result

    # Verify the raw Montgomery kernel against Python unbounded integers.
    montgomery_inverse = pow(2**192, -1, P)
    random_rows = run("--field-vectors").stdout.splitlines()
    for row in random_rows:
        a, b, product, total, difference = map(int, row.split())
        assert product == a*b*montgomery_inverse % P
        assert total == (a+b) % P
        assert difference == (a-b) % P
    boundaries = {0, 1, 2, P-1, P-2, 2**192 % P, 2**384 % P}
    for bit in (30, 36, 38, 63, 64, 65, 94, 127, 128, 129, 157, 158):
        boundaries.update((2**bit+offset) % P for offset in (-1, 0, 1))
    pairs = [(a, b) for a in sorted(boundaries) for b in sorted(boundaries)]
    output = run("--field-input", stdin="".join(f"{a} {b}\n" for a,b in pairs)).stdout.splitlines()
    assert len(output) == len(pairs)
    for (a,b), line in zip(pairs, output):
        product, total, difference, inverse = line.split()
        assert int(product) == a*b*montgomery_inverse % P
        assert int(total) == (a+b) % P
        assert int(difference) == (a-b) % P
        assert inverse == (str(pow(a,-1,P)) if a else "zero")

    def gamma(direction):
        a,b = direction
        assert a or b
        denominator = (a+b) % P
        return str(-a*pow(denominator,-1,P) % P) if denominator else None

    def expected_slot(model, slot):
        if slot < 4:
            return gamma(model.private_directions()[slot][2])
        return gamma(model.ordinary_direction(slot-2))

    small_receipts = []
    for n in (16, 64, 256):
        model = RecursiveMap(n)
        rows = [json.loads(row) for row in run("--emit-slots", n, n+2, 6).stdout.splitlines()]
        assert len(rows) == n+2 and len({row["slot"] for row in rows}) == n+2
        for row in rows:
            assert row["gamma"] == expected_slot(model, row["slot"]), (n, row)
        assert len({row["gamma"] for row in rows}) == n+2
        small_receipts.append({"n": n, "all_slots_compared": n+2})

    # The production model exercises all fourteen summands, not the toy depth.
    model = RecursiveMap(PRODUCTION_N)
    sample = {0,1,2,3,PRODUCTION_N-2,PRODUCTION_N-1}
    for centre in (PRODUCTION_N//4, PRODUCTION_N//2, 3*PRODUCTION_N//4):
        sample.update((centre-1, centre, centre+1))
    for j in range(1, 15):
        sample.update((4**j-1, 4**j, 4**j+1))
    rng = random.Random(0xA57A20260904)
    sample.update(rng.randrange(PRODUCTION_N) for _ in range(64))
    arbitrary_slots = 0
    for exponent in sorted(sample):
        rows = [json.loads(row) for row in run("--emit", PRODUCTION_N, exponent, 1, 1).stdout.splitlines()]
        for row in rows:
            expected = (model.private_directions()[2*exponent+row["private_slot"]][2]
                        if exponent < 2 else model.ordinary_direction(exponent))
            assert row["gamma"] == gamma(expected), row
            arbitrary_slots += 1

    # Two batches and a block boundary, with every normalized output compared.
    block_count = 4098
    block_rows = [json.loads(row) for row in run("--emit-slots", PRODUCTION_N, block_count, 6).stdout.splitlines()]
    assert len(block_rows) == block_count and len({row["slot"] for row in block_rows}) == block_count
    for row in block_rows:
        assert row["gamma"] == expected_slot(model, row["slot"]), row
    mask = 2**64-1

    def mix(x):
        x ^= x >> 30
        x = x*0xbf58476d1ce4e5b9 & mask
        x ^= x >> 27
        x = x*0x94d049bb133111eb & mask
        return x ^ (x >> 31)

    checksum = 0
    for row in block_rows:
        value = row["gamma"]
        if value is None:
            key = 0
        else:
            a = int(value)
            key = mix((a & mask) ^ mix((a >> 64 & mask) ^ mix((a >> 128) ^ 0x9e3779b97f4a7c15)))
        checksum ^= mix(key ^ row["slot"])
    for workers in (1, 6):
        receipt = json.loads(run("--benchmark", PRODUCTION_N, block_count, workers).stdout)
        assert receipt["checksum"] == checksum

    # A zero array allowance must reject before any production-sized allocation.
    gate = run("--scan", PRODUCTION_N, 1, 0, expected_success=False)
    assert gate.returncode != 0 and "scan memory gate failed" in gate.stderr
    # Deliberately exercise poles, all-pole batches, and invalid zero rows.
    normalize_rows = [(0,1),(1,0),(1,P-1),(P-1,1),(P-1,P-1),(2,P-2),(P-2,3)]
    for test_rows in (normalize_rows, [(j,P-j) for j in range(1,18)]):
        output = run("--normalize-input", stdin="".join(f"{a} {b}\n" for a,b in test_rows)).stdout.splitlines()
        assert output == [gamma(row) if gamma(row) is not None else "pole" for row in test_rows]
    invalid = run("--normalize-input", stdin="0 0\n", expected_success=False)
    assert invalid.returncode != 0 and "zero residual" in invalid.stderr
    # Truncated fingerprints force the exact rescan instead of relying on lucky
    # absence of hash ties. These allocations contain only258 uint64 entries.
    forced = json.loads(run("--scan-test", 256, 4).stdout)
    assert forced["exact_resolution_used"] and forced["finite_event_count_lower_bound"] == 258
    for bits in (1,4,64):
        output = [json.loads(row) for row in run("--partition-test",256,bits,4096).stdout.splitlines()]
        result = output[-1]
        assert result["mode"] == "partition_scan_complete"
        assert result["exact_distinct_finite_values"] == 258
        assert not result["production_budget_exceeded"]
        if bits < 64:
            assert result["exact_resolution_passes"] == 2
    partition_checks = []
    for partition_bits in (1,3,4):
        for hash_bits in (4,64):
            output = [json.loads(row) for row in run("--partition-test",256,hash_bits,4096,partition_bits).stdout.splitlines()]
            result = output[-1]
            passes = [row for row in output if row["mode"] == "partition_pass"]
            assert result["mode"] == "partition_scan_complete"
            assert result["partition_count"] == 2**partition_bits
            assert result["partition_bits"] == partition_bits
            assert result["reserve_bytes"] == 64*2**20
            assert result["exact_distinct_finite_values"] == 258
            assert {row["partition"] for row in passes} == set(range(2**partition_bits))
            assert sum(row["stored_finite_slots"] for row in passes) == 258
            assert sum(row["exact_finite_values_in_partition"] for row in passes) == 258
            assert all(not row["complete_domain_certificate"] for row in passes)
            partition_checks.append({"partition_bits":partition_bits,"hash_bits":hash_bits,"exact_count":258})
    overflow = run("--partition-test",256,4,8,expected_success=False)
    assert overflow.returncode == 3 and "INCOMPLETE" in overflow.stderr and "capacity exceeded" in overflow.stderr
    assert "partition_scan_complete" not in overflow.stdout
    invalid_worker = run("--benchmark",PRODUCTION_N,10,2**32+1,expected_success=False)
    assert invalid_worker.returncode != 0 and "workers must" in invalid_worker.stderr
    invalid_partitions = run("--partition-scan",PRODUCTION_N,1,1,5,expected_success=False)
    assert invalid_partitions.returncode != 0 and "partition bits must" in invalid_partitions.stderr
    invalid_test_size = run("--partition-test",PRODUCTION_N,4,4096,4,expected_success=False)
    assert invalid_test_size.returncode != 0 and "bounded partition test" in invalid_test_size.stderr
    # Real multiworker parking with synthetic readings, fixed to 65,538 slots.
    # The resume mode compares every output and atomic per-slot visit count with
    # a separate unpaused stream. Subprocess deadlines detect lost notifications.
    pause_rows = [json.loads(row) for row in run("--pause-test","resume",timeout=10).stdout.splitlines()]
    resumed = pause_rows[-1]
    assert resumed["mode"] == "pause_test_complete"
    assert resumed["slots"] == 65538 and resumed["each_slot_visited_once"]
    assert resumed["every_value_compared"] and resumed["checksum"] == resumed["baseline_checksum"]
    assert resumed["pauses"] == 1 and resumed["waiters"] >= 3
    assert [row["phase"] for row in pause_rows[:-1]] == ["resource_pause","resource_resume"]
    assert all(row["synthetic_test"] for row in pause_rows[:-1])
    for scenario, reason in (("timeout","timed out"),("warning","not NORMAL")):
        failed = run("--pause-test",scenario,expected_success=False,timeout=10)
        assert failed.returncode == 3 and "INCOMPLETE" in failed.stderr and reason in failed.stderr
        assert "pause_test_complete" not in failed.stdout
        phases = [json.loads(row)["phase"] for row in failed.stdout.splitlines()]
        assert phases == ["resource_pause","resource_pause_incomplete"]
    receipt = {
        "status": "PASS_BOUNDED_NATIVE_ACCEPTANCE_NOT_PRODUCTION_SCAN",
        "source_sha256": digest,
        "binary": str(binary),
        "binary_sha256": hashlib.sha256(binary.read_bytes()).hexdigest(),
        "compiled_from_current_source_by_this_run": args.binary is None,
        "random_montgomery_products": len(random_rows),
        "boundary_field_pairs": len(pairs),
        "small_domain_checks": small_receipts,
        "production_arbitrary_exponents": len(sample),
        "production_arbitrary_slots": arbitrary_slots,
        "production_contiguous_slots_compared": block_count,
        "parallel_batch_checksums_match": True,
        "zero_allowance_production_gate_rejected": True,
        "mixed_and_all_pole_batch_checks": True,
        "zero_residual_rejected": True,
        "forced_hash_collision_exact_resolution": True,
        "two_partition_exact_counts_checked_at_bits": [1,4,64],
        "general_partition_checks": partition_checks,
        "explicit_test_reserve_bytes": 64*2**20,
        "production_size_rejected_by_test_mode": True,
        "partition_capacity_overflow_reports_incomplete": True,
        "cooperative_pause_resume_every_slot_compared": resumed["slots"],
        "cooperative_pause_resume_waiters": resumed["waiters"],
        "cooperative_pause_timeout_and_warning_fail_closed": True,
        "oversized_worker_number_rejected": True,
        "production_array_allocated": False,
    }
    print(json.dumps(receipt, sort_keys=True), flush=True)
    if args.benchmark:
        for workers in (1, 6, 12, 18):
            result = json.loads(run("--benchmark", PRODUCTION_N, 2**20, workers).stdout)
            result["extrapolation_scope"] = "bounded evaluation only; full scan and sorting unmeasured"
            print(json.dumps(result, sort_keys=True), flush=True)
        for workers in (12,18):
            result = json.loads(run("--benchmark-partition",PRODUCTION_N,2**20,workers).stdout)
            result["extrapolation_scope"] = "bounded sample; billion-entry sorting and sustained memory behavior unmeasured"
            print(json.dumps(result, sort_keys=True),flush=True)


if __name__ == "__main__":
    main()

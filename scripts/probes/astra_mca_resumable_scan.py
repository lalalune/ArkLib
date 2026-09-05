#!/usr/bin/env python3
"""Resumable deterministic fingerprint lower bounds; never an exact scalar census.

Default prints a plan. --run explicitly evaluates chunks. --test is restricted
to n<=65536 and uses the native small-test memory reserve. Production keeps the
native pressure gates and processes one partition at a time below 1GiB on disk.
Every CLI invocation requires --acceptance from a current compiling checker run.
"""
import argparse
import fcntl
import hashlib
import json
import os
from pathlib import Path
import shutil
import struct
import subprocess
import tempfile

MIB = 2**20
PROD = 2**30
P = 2**158 + 192*2**30 + 1
FINGERPRINT = "canonical-gamma-three-limb-mix64-v1"
FORMAT = "finite-fingerprint-le64-v1"
COUNT_MODE = "distinct-fingerprint-lower-bound"


class Incomplete(RuntimeError):
    pass


class Invalid(RuntimeError):
    pass


def require(condition, message):
    if not condition:
        raise Invalid(message)


def canonical(value):
    return json.dumps(value, sort_keys=True, separators=(",", ":")).encode()


def digest(path):
    require(path.is_file() and not path.is_symlink(), f"not a regular artifact: {path}")
    result = hashlib.sha256()
    with path.open("rb") as handle:
        while block := handle.read(MIB):
            result.update(block)
    return result.hexdigest()


def sync_dir(path):
    fd = os.open(path, os.O_RDONLY)
    try:
        os.fsync(fd)
    finally:
        os.close(fd)


def write_receipt(path, payload):
    require(not path.exists(), f"receipt already exists: {path}")
    envelope = {"payload": payload, "sha256": hashlib.sha256(canonical(payload)).hexdigest()}
    temporary = path.with_name(path.name + ".pending")
    with temporary.open("xb") as handle:
        handle.write(canonical(envelope) + b"\n")
        handle.flush()
        os.fsync(handle.fileno())
    os.rename(temporary, path)
    sync_dir(path.parent)


def read_receipt(path):
    require(path.is_file() and not path.is_symlink(), f"missing receipt: {path}")
    require(path.stat().st_size <= 32*MIB, "receipt exceeds bounded size")
    envelope = json.loads(path.read_text())
    require(set(envelope) == {"payload", "sha256"}, "invalid receipt envelope")
    require(hashlib.sha256(canonical(envelope["payload"])).hexdigest() == envelope["sha256"],
            f"receipt digest mismatch: {path}")
    return envelope["payload"]


def tree_bytes(path):
    total = 0
    for directory, dirs, files in os.walk(path):
        for name in dirs + files:
            candidate = Path(directory)/name
            require(not candidate.is_symlink(), f"symlink in checkpoint store: {candidate}")
            stat = candidate.stat()
            # Count at least payload bytes, including allocated directory/file
            # blocks when the filesystem reports them. Leave additional margin
            # below1GiB for metadata not attributed to individual artifacts.
            total += max(stat.st_size, stat.st_blocks*512)
    return total


def disk_gate(store, extra, config):
    if tree_bytes(store) + extra > config["store_cap_bytes"]:
        raise Incomplete("checkpoint working-store cap would be exceeded")
    reserve = (64 if config["bounded_test"] else 256)*MIB
    if shutil.disk_usage(store).free < extra + reserve:
        raise Incomplete("insufficient free disk for staged artifact plus reserve")


def expected_ranges(config):
    end = config["n"] + 2
    return [(begin, min(end, begin + config["chunk_slots"]))
            for begin in range(0, end, config["chunk_slots"])]


def chunk_name(index):
    return f"chunk-{index:06d}"


def validate_chunk(payload, config, config_hash, partition, index, raw=None):
    begin, end = expected_ranges(config)[index]
    native = payload["native"]
    require(payload["config_sha256"] == config_hash and payload["index"] == index,
            "chunk configuration or index mismatch")
    for key, value in {"mode": "fingerprint_chunk_complete", "format": FORMAT,
                       "n": config["n"], "slot_begin": begin, "slot_end": end,
                       "slots": end-begin, "partition_bits": config["partition_bits"],
                       "partition": partition, "hash_bits": config["hash_bits"],
                       "complete_domain_certificate": False}.items():
        require(native.get(key) == value, f"chunk {key} mismatch")
    stored, poles = native["stored_finite_keys"], native["chart_pole_slots"]
    require(type(stored) is int and type(poles) is int and 0 <= stored <= end-begin
            and 0 <= poles <= end-begin and stored+poles <= end-begin, "invalid chunk counts")
    require(native["key_bytes"] == stored*8 and 0 <= native["checksum"] < 2**64,
            "invalid chunk bytes/checksum")
    require(len(payload["keys_sha256"]) == 64, "invalid chunk digest")
    if raw is not None:
        require(raw.stat().st_size == stored*8 and digest(raw) == payload["keys_sha256"],
                f"corrupted fingerprint chunk: {raw}")


def verify_runtime(binary, config):
    require(digest(binary) == config["binary_sha256"]
            and digest(Path(__file__).with_name("astra_mca_native_eval.cpp")) == config["source_sha256"]
            and digest(Path(__file__)) == config["driver_sha256"], "source/binary/driver changed during run")
    provenance = config.get("acceptance_provenance", {})
    if provenance.get("kind") == "internal-bounded-checker-bootstrap-not-production-acceptance":
        require(config["bounded_test"] and config["n"] <= 65536, "unaccepted bootstrap cannot run production")
    else:
        record = provenance.get("record", {})
        checkpoint = record.get("resumable_checkpoint_checks", {})
        require(provenance.get("kind") == "validated-compiling-bounded-acceptance"
                and record.get("status") == "PASS_BOUNDED_NATIVE_ACCEPTANCE_NOT_PRODUCTION_SCAN"
                and record.get("compiled_from_current_source_by_this_run") is True
                and record.get("source_sha256") == config["source_sha256"]
                and record.get("binary_sha256") == config["binary_sha256"]
                and checkpoint.get("status") == "PASS_BOUNDED_CHECKPOINT_ACCEPTANCE"
                and checkpoint.get("driver_sha256") == config["driver_sha256"],
                "configuration lacks matching compiled-acceptance provenance")


def native_call(binary, arguments, mode, config):
    verify_runtime(binary, config)
    result = subprocess.run([str(binary), *map(str, arguments)], capture_output=True, text=True)
    verify_runtime(binary, config)
    if result.returncode == 3:
        raise Incomplete(result.stderr.strip())
    require(result.returncode == 0, f"native failure: {result.stderr.strip()}")
    rows = [json.loads(line) for line in result.stdout.splitlines()]
    receipts = [row for row in rows if row.get("mode") == mode]
    require(len(receipts) == 1 and rows[-1] == receipts[0], "missing native completion receipt")
    return receipts[0], {"arguments": list(map(str, arguments)), "stdout": result.stdout,
                         "stderr": result.stderr, "exit_code": result.returncode}


def discard_pending(part):
    for path in part.glob(".pending-*"):
        require(path.is_dir() and not path.is_symlink(), "invalid staging directory")
        tree_bytes(path)  # Reject links before removing only this driver's staging tree.
        shutil.rmtree(path)
    for path in part.glob("*.pending"):
        require(path.is_file() and not path.is_symlink(), "invalid pending receipt")
        path.unlink()


def validate_partition(payload, config, config_hash, partition, part):
    require(payload["config_sha256"] == config_hash and payload["partition"] == partition,
            "partition configuration mismatch")
    chunks = payload["chunks"]
    require(len(chunks) == len(expected_ranges(config)), "incomplete partition range cover")
    for index, chunk in enumerate(chunks):
        validate_chunk(chunk, config, config_hash, partition, index)
    native = payload["native"]
    stored = sum(chunk["native"]["stored_finite_keys"] for chunk in chunks)
    require(native["mode"] == "fingerprint_partition_reduced" and native["n"] == config["n"]
            and native["partition"] == partition and native["partition_bits"] == config["partition_bits"]
            and native["input_files"] == len(chunks) and native["stored_finite_keys"] == stored
            and native["count_mode"] == COUNT_MODE and not native["complete_domain_certificate"],
            "invalid partition reducer receipt")
    lower = native["distinct_fingerprint_lower_bound"]
    require(0 <= lower <= stored and native["ties_bytes"] == native["tied_keys"]*16,
            "invalid partition lower bound")
    ties = part/"ties.bin"
    require(ties.stat().st_size == native["ties_bytes"] and digest(ties) == payload["ties_sha256"],
            "tied-key receipt corrupted")
    last, loss, tied_slots, count = -1, 0, 0, 0
    with ties.open("rb") as handle:
        while row := handle.read(16):
            require(len(row) == 16, "short tied-key record")
            key, multiplicity = struct.unpack("<QQ", row)
            require(key > last and key >> (64-config["partition_bits"]) == partition and multiplicity >= 2,
                    "invalid tied-key order/prefix/count")
            last, count = key, count+1
            loss += multiplicity-1
            tied_slots += multiplicity
    require(count == native["tied_keys"] and tied_slots == native["tied_key_slots"]
            and lower == stored-loss, "tied-key accounting mismatch")
    return payload


def scan(binary, store, config, max_new_chunks=None):
    verify_runtime(binary, config)
    require(not store.is_symlink(), "checkpoint directory cannot be a symlink")
    store.mkdir(parents=True, exist_ok=True)
    sync_dir(store.parent)
    require("\n" not in str(store.resolve()), "newline in checkpoint directory")
    require(not (store/".lock").is_symlink(), "checkpoint lock cannot be a symlink")
    with (store/".lock").open("a") as lock:
        try:
            fcntl.flock(lock, fcntl.LOCK_EX | fcntl.LOCK_NB)
        except BlockingIOError:
            raise Incomplete("another writer owns this checkpoint store") from None
        if tree_bytes(store) > config["store_cap_bytes"]:
            raise Incomplete("existing checkpoint store exceeds its cap")
        allowed_root = {f"partition-{i:02d}" for i in range(2**config["partition_bits"])} | {
            ".lock", "config.json", "config.json.pending", "complete.json", "complete.json.pending"}
        require(all(path.name in allowed_root for path in store.iterdir()), "unexpected checkpoint root artifact")
        config_hash = hashlib.sha256(canonical(config)).hexdigest()
        if (store/"config.json").exists():
            require(read_receipt(store/"config.json") == config, "source/binary/model/configuration changed")
        else:
            require(set(p.name for p in store.iterdir()) <= {".lock", "config.json.pending"},
                    "nonempty store lacks a valid configuration")
            (store/"config.json.pending").unlink(missing_ok=True)
            write_receipt(store/"config.json", config)
        results, new_chunks = [], 0
        ranges = expected_ranges(config)
        for partition in range(2**config["partition_bits"]):
            part = store/f"partition-{partition:02d}"
            part.mkdir(exist_ok=True)
            sync_dir(store)
            discard_pending(part)
            allowed = {chunk_name(i) for i in range(len(ranges))} | {"result.json", "ties.bin"}
            require(all(p.name in allowed for p in part.iterdir()), "unexpected/duplicate chunk directory")
            if (part/"result.json").exists():
                payload = validate_partition(read_receipt(part/"result.json"), config, config_hash, partition, part)
            else:
                # A crash after ties.bin was committed but before result.json is
                # not a completed reduction. Raw chunks remain the authority.
                (part/"ties.bin").unlink(missing_ok=True)
                chunks, key_bytes = [], 0
                for index, (begin, end) in enumerate(ranges):
                    dest = part/chunk_name(index)
                    if dest.exists():
                        chunk = read_receipt(dest/"receipt.json")
                        validate_chunk(chunk, config, config_hash, partition, index, dest/"keys.bin")
                    else:
                        if max_new_chunks is not None and new_chunks >= max_new_chunks:
                            raise Incomplete("requested new-chunk limit reached; verified progress retained")
                        disk_gate(store, (end-begin)*8 + MIB, config)
                        stage = Path(tempfile.mkdtemp(prefix=".pending-", dir=part))
                        try:
                            arguments = ["--chunk-keys-test" if config["bounded_test"] else "--chunk-keys",
                                         config["n"], config["workers"], begin, end-begin,
                                         config["partition_bits"], partition, stage/"keys.bin"]
                            if config["bounded_test"]:
                                arguments.append(config["hash_bits"])
                            native, execution = native_call(binary, arguments, "fingerprint_chunk_complete", config)
                            chunk = {"config_sha256": config_hash, "index": index, "native": native,
                                     "keys_sha256": digest(stage/"keys.bin"), "execution": execution}
                            validate_chunk(chunk, config, config_hash, partition, index, stage/"keys.bin")
                            if key_bytes + native["key_bytes"] > config["partition_cap_bytes"]:
                                raise Incomplete("partition raw-key capacity exceeded; prior chunks retained")
                            write_receipt(stage/"receipt.json", chunk)
                            sync_dir(stage)
                            os.rename(stage, dest)
                            sync_dir(part)
                            new_chunks += 1
                        finally:
                            if stage.exists():
                                shutil.rmtree(stage)
                        print(json.dumps({"phase": "chunk_verified", "partition": partition, "index": index,
                                          "begin": begin, "end": end, "complete_domain_certificate": False}), flush=True)
                    key_bytes += chunk["native"]["key_bytes"]
                    chunks.append(chunk)
                require(key_bytes <= config["partition_cap_bytes"], "partition raw-key cap exceeded")
                disk_gate(store, 16*MIB + 8*MIB, config)
                stage = Path(tempfile.mkdtemp(prefix=".pending-", dir=part))
                try:
                    manifest = stage/"manifest.txt"
                    manifest.write_text("".join(str((part/chunk_name(i)/"keys.bin").resolve())+"\n"
                                                for i in range(len(ranges))))
                    native, execution = native_call(binary,
                        ["--reduce-keys-test" if config["bounded_test"] else "--reduce-keys", config["n"],
                         config["partition_bits"], partition, config["partition_cap_bytes"], manifest, stage/"ties.bin"],
                        "fingerprint_partition_reduced", config)
                    # Rehash after reduction to detect changed inputs. The store
                    # lock excludes other cooperating writers; these integrity
                    # digests are not signatures or a Lean certificate.
                    for i, chunk in enumerate(chunks):
                        validate_chunk(chunk, config, config_hash, partition, i, part/chunk_name(i)/"keys.bin")
                    payload = {"config_sha256": config_hash, "partition": partition, "chunks": chunks,
                               "native": native, "ties_sha256": digest(stage/"ties.bin"), "execution": execution}
                    os.rename(stage/"ties.bin", part/"ties.bin")
                    sync_dir(part)
                    validate_partition(payload, config, config_hash, partition, part)
                    write_receipt(part/"result.json", payload)
                finally:
                    shutil.rmtree(stage)
            # A durable complete partition receipt keeps all chunk digests,
            # ranges, counts and native outputs after raw-key cleanup.
            for i, chunk in enumerate(payload["chunks"]):
                dest = part/chunk_name(i)
                if dest.exists():
                    validate_chunk(read_receipt(dest/"receipt.json"), config, config_hash, partition, i, dest/"keys.bin")
                    require(read_receipt(dest/"receipt.json") == chunk, "remaining raw chunk differs from durable receipt")
                    pending = part/f".pending-cleanup-{i:06d}"
                    os.rename(dest, pending)
                    sync_dir(part)
                    shutil.rmtree(pending)
            sync_dir(part)
            if results:
                for old, new in zip(results[0]["chunks"], payload["chunks"]):
                    require((old["native"]["checksum"], old["native"]["chart_pole_slots"])
                            == (new["native"]["checksum"], new["native"]["chart_pole_slots"]),
                            "model stream differs across partitions")
            results.append(payload)
            print(json.dumps({"phase": "partition_checkpoint_verified", "partition": partition,
                              "distinct_fingerprint_lower_bound": payload["native"]["distinct_fingerprint_lower_bound"],
                              "complete_domain_certificate": False}), flush=True)
        poles = sum(c["native"]["chart_pole_slots"] for c in results[0]["chunks"])
        finite = sum(p["native"]["stored_finite_keys"] for p in results)
        require(finite == config["n"]+2-poles, "partition slot totals do not cover every finite slot")
        lower = sum(p["native"]["distinct_fingerprint_lower_bound"] for p in results)
        final = {"config_sha256": config_hash, "count_mode": COUNT_MODE, "n": config["n"],
                 "finite_slots": finite, "chart_pole_slots": poles, "distinct_fingerprint_lower_bound": lower,
                 "complete_domain_coverage": True, "length_plus_one_met": lower >= config["n"]+1,
                 "production_budget_exceeded": not config["bounded_test"] and config["n"] == PROD and lower >= PROD+1,
                 "status": "LOWER_BOUND_EXCEEDS_LENGTH" if lower >= config["n"]+1 else "INCONCLUSIVE_ABOUT_TRUE_DISTINCT_COUNT",
                 "scope": "native_fingerprint_lower_bound_not_exact_scalar_count_not_Lean_proof",
                 "partitions": [digest(store/f"partition-{i:02d}"/"result.json") for i in range(len(results))]}
        if (store/"complete.json").exists():
            require(read_receipt(store/"complete.json") == final, "completed receipt changed")
        else:
            (store/"complete.json.pending").unlink(missing_ok=True)
            write_receipt(store/"complete.json", final)
        print(json.dumps(final, sort_keys=True), flush=True)
        return final


def acceptance_binding(path, binary=None):
    require(path.is_file() and not path.is_symlink() and path.stat().st_size <= 8*MIB,
            "missing or oversized bounded-acceptance receipt")
    data = path.read_bytes()
    records = [json.loads(line) for line in data.splitlines() if line.strip()]
    passes = [row for row in records if row.get("status") == "PASS_BOUNDED_NATIVE_ACCEPTANCE_NOT_PRODUCTION_SCAN"]
    require(len(passes) == 1, "acceptance receipt must contain exactly one bounded PASS record")
    record = passes[0]
    require(record.get("compiled_from_current_source_by_this_run") is True,
            "acceptance receipt did not compile its binary from current source")
    source_sha = digest(Path(__file__).with_name("astra_mca_native_eval.cpp"))
    driver_sha = digest(Path(__file__))
    require(record.get("source_sha256") == source_sha, "acceptance source SHA does not match current CPP")
    checkpoint = record.get("resumable_checkpoint_checks", {})
    require(checkpoint.get("status") == "PASS_BOUNDED_CHECKPOINT_ACCEPTANCE"
            and checkpoint.get("driver_sha256") == driver_sha,
            "acceptance checkpoint driver SHA/status does not match current driver")
    selected = Path(record["binary"]) if binary is None else Path(binary)
    require(record.get("binary_sha256") == digest(selected), "acceptance binary SHA does not match selected binary")
    return selected, {"kind": "validated-compiling-bounded-acceptance",
                      "receipt_sha256": hashlib.sha256(data).hexdigest(), "record": record}


def configuration(binary, n=PROD, partition_bits=4, chunk_slots=2**22, workers=18,
                  bounded_test=False, hash_bits=64, acceptance=None, *, _checker_bootstrap=False):
    require(n >= 16 and n <= PROD and n & (n-1) == 0 and (n.bit_length()-1) % 2 == 0, "n must be 4^r in16..2^30")
    require(1 <= partition_bits <= 4 and 1 <= chunk_slots <= 2**24 and 1 <= workers <= 18,
            "invalid partition/chunk/worker bounds")
    require((not bounded_test and hash_bits == 64) or (bounded_test and n <= 65536 and 1 <= hash_bits <= 64),
            "truncated hashes and test reserve restricted to small domains")
    require(len(expected_ranges({"n": n, "chunk_slots": chunk_slots})) <= 10000, "too many chunks")
    if _checker_bootstrap:
        # The checker cannot already possess its own final acceptance receipt.
        # This internal bootstrap is never selectable through the CLI and can
        # only exercise a small domain; it is explicitly marked in every config.
        require(bounded_test and n <= 65536 and acceptance is None, "checker bootstrap restricted to bounded tests")
        provenance = {"kind": "internal-bounded-checker-bootstrap-not-production-acceptance"}
    else:
        require(acceptance is not None, "a compiling bounded-acceptance receipt is required")
        _, provenance = acceptance_binding(acceptance, binary)
    source = Path(__file__).with_name("astra_mca_native_eval.cpp")
    return {"version": 2, "P": str(P), "n": n, "chart": "gamma=-first/(first+second);g_to_g_plus_f",
            "fingerprint": FINGERPRINT, "format": FORMAT, "count_mode": COUNT_MODE,
            "acceptance_provenance": provenance,
            "source_sha256": digest(source), "binary_sha256": digest(binary),
            "driver_sha256": digest(Path(__file__)), "partition_bits": partition_bits,
            "chunk_slots": chunk_slots, "workers": workers, "hash_bits": hash_bits, "bounded_test": bounded_test,
            "partition_cap_bytes": MIB if bounded_test else 576*MIB, "store_cap_bytes": 896*MIB}


def checkpoint_checks(binary):
    """Strictly small acceptance, invoked by the independent native checker."""
    import contextlib
    import io
    from unittest.mock import patch

    def test_config(*args, **kwargs):
        return configuration(*args, **kwargs, _checker_bootstrap=True)

    def invoke(store, config, limit=None):
        with contextlib.redirect_stdout(io.StringIO()):
            return scan(binary, store, config, limit)

    def rejects(action, exception):
        try:
            action()
        except exception:
            return
        raise AssertionError("invalid/incomplete checkpoint unexpectedly accepted")

    with tempfile.TemporaryDirectory(prefix="astra-checkpoints-test-") as temporary:
        base = Path(temporary)
        config = test_config(binary, 256, 2, 67, 4, True)
        store = base/"resume"
        rejects(lambda: invoke(store, config, 2), Incomplete)
        part = store/"partition-00"
        first, second = part/chunk_name(0), part/chunk_name(1)
        second_digest, second_mtime = digest(second/"keys.bin"), (second/"keys.bin").stat().st_mtime_ns
        pending = part/".pending-interrupted-write"
        pending.mkdir()
        (pending/"keys.bin").write_bytes(b"partial")
        # A missing range is recomputed; a later verified range is reused intact.
        shutil.rmtree(first)
        rejects(lambda: invoke(store, config, 1), Incomplete)
        assert not pending.exists()
        assert digest(second/"keys.bin") == second_digest and (second/"keys.bin").stat().st_mtime_ns == second_mtime
        # Duplicate directories and a copied range with the wrong index fail.
        duplicate = part/"chunk-999999"
        shutil.copytree(second, duplicate)
        rejects(lambda: invoke(store, config, 0), Invalid)
        shutil.rmtree(duplicate)
        wrong_range = part/chunk_name(2)
        shutil.copytree(second, wrong_range)
        rejects(lambda: invoke(store, config, 0), Invalid)
        shutil.rmtree(wrong_range)
        raw = second/"keys.bin"
        saved = raw.read_bytes()
        raw.write_bytes(saved+b"corrupt")
        rejects(lambda: invoke(store, config, 0), Invalid)
        raw.write_bytes(saved)
        receipt = second/"receipt.json"
        saved_receipt = receipt.read_bytes()
        envelope = json.loads(saved_receipt)
        envelope["payload"]["native"]["checksum"] ^= 1
        receipt.write_bytes(canonical(envelope))
        rejects(lambda: invoke(store, config, 0), Invalid)
        receipt.write_bytes(saved_receipt)
        changed = dict(config, source_sha256="0"*64)
        rejects(lambda: invoke(store, changed, 0), Invalid)
        changed = dict(config, binary_sha256="0"*64)
        rejects(lambda: invoke(store, changed, 0), Invalid)
        changed = dict(config, chart="unreviewed-chart")
        rejects(lambda: invoke(store, changed, 0), Invalid)
        result = invoke(store, config)
        assert result["distinct_fingerprint_lower_bound"] == 258 and result["length_plus_one_met"]
        assert not result["production_budget_exceeded"] and not list(store.glob("partition-*/chunk-*"))
        assert invoke(store, config, 0) == result
        # Interruption during cleanup leaves only a disposable pending directory;
        # the complete receipt independently retains every expected range/digest.
        cleanup = part/".pending-cleanup-000000"
        cleanup.mkdir()
        (cleanup/"partially-deleted-file").write_bytes(b"unused")
        assert invoke(store, config, 0) == result and not cleanup.exists()
        payload = read_receipt(part/"result.json")
        assert [(c["native"]["slot_begin"],c["native"]["slot_end"]) for c in payload["chunks"]] == expected_ranges(config)
        # Even a recomputed JSON envelope cannot hide a wrong lower-bound count.
        result_path = part/"result.json"
        saved_result = result_path.read_bytes()
        payload["native"]["distinct_fingerprint_lower_bound"] += 1
        result_path.unlink()
        write_receipt(result_path, payload)
        rejects(lambda: invoke(store, config, 0), Invalid)
        result_path.write_bytes(saved_result)
        ties = part/"ties.bin"
        saved_ties = ties.read_bytes()
        ties.write_bytes(saved_ties+b"bad")
        rejects(lambda: invoke(store, config, 0), Invalid)
        ties.write_bytes(saved_ties)
        forced = test_config(binary, 256, 2, 89, 4, True, 4)
        forced_result = invoke(base/"forced-hashes", forced)
        assert forced_result["distinct_fingerprint_lower_bound"] == 16
        assert forced_result["status"] == "INCONCLUSIVE_ABOUT_TRUE_DISTINCT_COUNT"
        assert not forced_result["length_plus_one_met"]
        assert sum(read_receipt(path)["native"]["tied_keys"]
                   for path in (base/"forced-hashes").glob("partition-*/result.json")) == 16
        empty_config = test_config(binary, 16, 4, 18, 2, True, 1)
        empty_result = invoke(base/"empty-prefixes", empty_config)
        empty_prefixes = sum(read_receipt(path)["native"]["stored_finite_keys"] == 0
                             for path in (base/"empty-prefixes").glob("partition-*/result.json"))
        assert empty_result["distinct_fingerprint_lower_bound"] == 2 and empty_prefixes == 14
        # Compare arbitrary ranges with the original non-range stream, using
        # absolute slot IDs and independent Python fingerprint arithmetic.
        original = subprocess.run([str(binary), "--emit-slots", "16384", "9000", "4"],
                                  capture_output=True, text=True, check=True)
        values = {row["slot"]: row["gamma"] for row in map(json.loads, original.stdout.splitlines())}
        assert len(values) == 9000
        mask = 2**64-1

        def mix(value):
            value ^= value >> 30
            value = value*0xbf58476d1ce4e5b9 & mask
            value ^= value >> 27
            value = value*0x94d049bb133111eb & mask
            return value ^ (value >> 31)

        def fingerprint(gamma):
            if gamma is None:
                return 0
            value = int(gamma)
            return mix((value & mask) ^ mix((value >> 64 & mask) ^ mix((value >> 128) ^ 0x9e3779b97f4a7c15)))

        range_config = test_config(binary, 16384, 1, 4098, 4, True)
        for begin in (1, 3, 4095, 4096):
            count = 4098
            expected_checksum = 0
            for slot in range(begin, begin+count):
                expected_checksum ^= mix(fingerprint(values[slot]) ^ slot)
            for partition in (0, 1):
                output = base/f"range-{begin}-{partition}.bin"
                native, _ = native_call(binary,
                    ["--chunk-keys-test",16384,4,begin,count,1,partition,output,64],
                    "fingerprint_chunk_complete", range_config)
                expected = sorted(fingerprint(values[slot]) for slot in range(begin, begin+count)
                                  if values[slot] is not None and fingerprint(values[slot]) >> 63 == partition)
                actual = sorted(row[0] for row in struct.iter_unpack("<Q", output.read_bytes()))
                assert actual == expected and native["checksum"] == expected_checksum
        # The actual available-disk gate is tested with a read-only mock; no
        # allocation or host pressure manipulation is used.
        fake_usage = shutil.disk_usage(base)._replace(free=0)
        with patch.object(shutil, "disk_usage", return_value=fake_usage):
            rejects(lambda: invoke(base/"no-disk", config, 1), Incomplete)
        tiny_store = dict(config, store_cap_bytes=4096)
        rejects(lambda: invoke(base/"store-cap", tiny_store, 1), Incomplete)
        rejects(lambda: test_config(binary, PROD, 4, 2**22, 1, True), Invalid)
        rejects(lambda: test_config(binary, PROD, 4, 2**22, 1, False, 4), Invalid)
        rejects(lambda: test_config(binary, PROD, 4, 2**22, 1, False), Invalid)
        # Synthetic parser fixtures exist only inside this temporary test store;
        # the checker emits its real compiling acceptance after all tests finish.
        fixture = {"status": "PASS_BOUNDED_NATIVE_ACCEPTANCE_NOT_PRODUCTION_SCAN",
                   "compiled_from_current_source_by_this_run": True,
                   "source_sha256": digest(Path(__file__).with_name("astra_mca_native_eval.cpp")),
                   "binary": str(binary), "binary_sha256": digest(binary),
                   "resumable_checkpoint_checks": {"status": "PASS_BOUNDED_CHECKPOINT_ACCEPTANCE",
                                                     "driver_sha256": digest(Path(__file__))}}
        acceptance = base/"synthetic-acceptance-fixture.jsonl"
        acceptance.write_bytes(canonical(fixture)+b"\n")
        selected, binding = acceptance_binding(acceptance)
        assert selected == binary and binding["record"] == fixture
        copied = base/"identical-binary-copy"
        shutil.copyfile(binary, copied)
        assert acceptance_binding(acceptance, copied)[0] == copied
        accepted_config = configuration(binary, 256, 2, 67, 4, True, acceptance=acceptance)
        assert accepted_config["acceptance_provenance"]["receipt_sha256"] == digest(acceptance)
        rejects(lambda: configuration(binary, 256, 2, 67, 4, True), Invalid)
        provenance_cases = []
        for case in ("source", "binary", "driver", "uncompiled", "status", "checkpoint_status", "duplicate"):
            bad = json.loads(json.dumps(fixture))
            if case in ("source", "binary"):
                bad[case+"_sha256"] = "0"*64
            elif case == "driver":
                bad["resumable_checkpoint_checks"]["driver_sha256"] = "0"*64
            elif case == "uncompiled":
                bad["compiled_from_current_source_by_this_run"] = False
            elif case == "status":
                bad["status"] = "FAIL"
            elif case == "checkpoint_status":
                bad["resumable_checkpoint_checks"]["status"] = "FAIL"
            bad_path = base/f"bad-acceptance-{case}.jsonl"
            bad_path.write_bytes(canonical(bad)+b"\n"+(canonical(bad)+b"\n" if case == "duplicate" else b""))
            rejects(lambda: acceptance_binding(bad_path, binary), Invalid)
            # Plan-only must reject just as the execution path does, before
            # creating any checkpoint directory or starting the native binary.
            plan_store = base/f"rejected-plan-{case}"
            result = subprocess.run([__import__("sys").executable, str(Path(__file__)),
                                     "--acceptance", str(bad_path), "--binary", str(binary),
                                     "--store", str(plan_store)], capture_output=True, text=True, timeout=10)
            assert result.returncode != 0 and not plan_store.exists() and "plan_only" not in result.stdout
            provenance_cases.append(case)
        missing = subprocess.run([__import__("sys").executable, str(Path(__file__)),
                                  "--binary", str(binary), "--store", str(base/"missing-acceptance")],
                                 capture_output=True, text=True, timeout=10)
        assert missing.returncode != 0 and not (base/"missing-acceptance").exists()
        final_bytes = tree_bytes(store)
        assert final_bytes < MIB
        return {"status": "PASS_BOUNDED_CHECKPOINT_ACCEPTANCE", "n": 256,
                "driver_sha256": digest(Path(__file__)),
                "resume_gap_recomputed_without_rewriting_verified_chunk": True,
                "duplicate_and_wrong_range_rejected": True, "raw_and_receipt_corruption_rejected": True,
                "source_binary_chart_changes_rejected": True, "partial_write_and_cleanup_recovered": True,
                "summary_verified_after_raw_cleanup": True, "full_hash_lower_bound": 258,
                "forced_four_bit_lower_bound": 16, "forced_ties_report_inconclusive": True,
                "empty_prefixes_checked": empty_prefixes, "range_starts_compared": [1,3,4095,4096],
                "slots_per_range_compared": 4098,
                "acceptance_provenance_rejection_cases": provenance_cases,
                "plan_only_requires_matching_compiling_acceptance": True,
                "identical_binary_copy_accepted_by_hash": True,
                "working_store_and_free_disk_gates_checked": True, "final_store_bytes": final_bytes,
                "production_launched": False}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--acceptance", required=True, type=Path)
    parser.add_argument("--binary", type=Path, help="optional identical copy; otherwise use the receipt's binary path")
    parser.add_argument("--store", required=True, type=Path)
    parser.add_argument("--n", type=int, default=PROD)
    parser.add_argument("--partition-bits", type=int, default=4)
    parser.add_argument("--chunk-slots", type=int, default=2**22)
    parser.add_argument("--workers", type=int, default=18)
    parser.add_argument("--test", action="store_true")
    parser.add_argument("--hash-bits", type=int, default=64)
    parser.add_argument("--max-new-chunks", type=int)
    parser.add_argument("--run", action="store_true")
    args = parser.parse_args()
    try:
        binary, _ = acceptance_binding(args.acceptance, args.binary)
        config = configuration(binary, args.n, args.partition_bits, args.chunk_slots,
                               args.workers, args.test, args.hash_bits, args.acceptance)
        require(args.max_new_chunks is None or args.max_new_chunks >= 0, "invalid chunk limit")
        if not args.run:
            print(json.dumps({"mode": "plan_only", "config": config, "store": str(args.store),
                              "chunks_per_partition": len(expected_ranges(config)), "production_launched": False}, sort_keys=True))
        else:
            scan(binary, args.store, config, args.max_new_chunks)
    except Incomplete as error:
        print(f"INCOMPLETE: {error}", file=__import__("sys").stderr)
        return 3
    except (Invalid, OSError, ValueError, KeyError, TypeError) as error:
        print(f"INVALID: {error}", file=__import__("sys").stderr)
        return 1
    return 0


if __name__ == "__main__":
    raise SystemExit(main())

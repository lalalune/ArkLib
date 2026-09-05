# Resumable fingerprint lower bounds for the production construction

The [driver](../../scripts/probes/astra_mca_resumable_scan.py) preserves verified
chunks when a resource guard interrupts a scan. It complements the
[native evaluator](astra_mca_native_eval-2026-09-04.md); it does not report an
exact scalar census or prove the prize. No production result from this driver
is asserted here.

## Reproduction and provenance

First compile the current native source and run its independent bounded checks:

```sh
python3 scripts/probes/astra_mca_native_eval_check.py > /tmp/astra-native-acceptance.jsonl
```

Inspect a plan with the resulting receipt and a new checkpoint directory:

```sh
python3 scripts/probes/astra_mca_resumable_scan.py \
  --acceptance /tmp/astra-native-acceptance.jsonl \
  --store /tmp/astra-production-checkpoints
```

This validates the receipt without creating the store or starting a scan.
Add `--run` to evaluate. Repeating the identical command resumes verified
progress. `--max-new-chunks N` limits new chunks in one invocation; reaching
that limit returns `INCOMPLETE` while retaining completed chunks.

Both plan and run require a compiling PASS receipt whose source, binary, and
resumable-driver hashes match the actual current files. The binary normally
comes from that receipt; `--binary` permits a copy with the same hash. A stale
driver, unrelated binary, noncompiling receipt, or changed configuration is
rejected. These integrity checks preserve execution provenance; they are not
cryptographic proof of the mathematical result.

## Bounded storage and resumable coverage

Defaults use sixteen fingerprint partitions and chunks of 2^22 slots. A chunk
has at most a 32 MiB key buffer; the native 1 GiB preflight reserve and 512 MiB
runtime floor remain in force. The reducer caps one partition at 576 MiB.
The working store is capped at 896 MiB and also requires 256 MiB of actual
free-disk reserve. A capacity or resource failure returns `INCOMPLETE`.

Each committed chunk records its exact half-open slot range, field/domain and
chart configuration, source/binary/driver provenance, finite and pole counts,
absolute-slot checksum, raw native output, and key-file SHA-256. Staged output
is synced and renamed only after successful validation. A store lock prevents
two cooperating writers. Interrupted staging is discarded; verified chunks
are reused. Missing ranges are recomputed and mismatched ranges are rejected.

After every range of a partition is present, a native reducer sorts the keys
and records each tied fingerprint and its multiplicity. Only a durable,
validated partition receipt permits removal of its raw chunks. That receipt
retains all chunk ranges, counts, digests, and execution records. Resume checks
these records and tied-key accounting even after cleanup. The final receipt
requires all partitions and an exact finite-slot coverage total.

## What the number proves

Equal canonical finite scalars have equal full 64-bit fingerprints and enter
the same partition. Therefore the sum of distinct fingerprint counts is a
deterministic lower bound on distinct finite scalars. No random-hash assumption
is used. Reaching 1073741825 would satisfy the count needed for this production
construction, subject to its separately reviewed MCA conversion argument.

A smaller fingerprint count is explicitly `INCONCLUSIVE_ABOUT_TRUE_DISTINCT_COUNT`:
different scalars might share a fingerprint. The retained tied-key records
support later exact resolution; the driver does not perform that resolution.
Neither outcome is a universal predecessor-radius bound or a Lean proof.

The bounded acceptance checks cover gap recovery without rewriting later
verified chunks; duplicate/wrong ranges; corrupt keys, receipts, summaries and
ties; changed provenance; interrupted staging and cleanup; empty partitions;
arbitrary ranges across private slots and block boundaries; and resource caps.
At n=256, full hashes give lower bound 258, while forced four-bit hashes give
16 and correctly report an inconclusive result about the true scalar count.
The [bounded receipt](../../scripts/probes/astra_mca_resumable_acceptance.json)
pins the source, binary, and driver used for the reviewed checks, including
the root agent's independent current/stale-receipt CLI checks.

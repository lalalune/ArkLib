# Native evaluation and exact distinct-value counting

The native runner implements the reviewed
[compact two-generator evaluator](astra_mca_twogen_lift_eval-2026-09-04.md).
Its bounded acceptance checks pass. This note records the implementation and
verification scope. Three initial local production attempts stopped on resource
guards before completing a partition. A subsequent
[hosted production count](astra_mca_production_count-2026-09-05.md) completed
with a deterministic lower bound of n+1 finite scalars. It supports a written
threshold upper bound, but is not a Lean proof or prize closure.

The source is
[`astra_mca_native_eval.cpp`](../../scripts/probes/astra_mca_native_eval.cpp),
with an independent Python acceptance driver
[`astra_mca_native_eval_check.py`](../../scripts/probes/astra_mca_native_eval_check.py).
The default native command only checks n=16,64,256. The Python driver compiles
a small binary in the system temporary directory and never starts a production
scan. Its receipt binds both the source SHA256 and actual binary SHA256, and
states whether that run compiled the binary from the current source.

## Arithmetic and evaluation

The field modulus is `P=2^158+192*2^30+1`, with three 64-bit limbs
`[206158430209,0,1073741824]`. Multiplication uses Montgomery radix `2^192`,
128-bit intermediate products, and three reduction steps. The prime and
production generator are those already certified by `_PrizeShapePrimeP30.lean`.
The runner does not re-prove primality.

The rational formula is evaluated projectively using the equivalent identity

```text
R0(X)=(1/m)*sum_j 4^j*psi((omega*X)^(4^j)),
psi(z)=1/(2(z+1))-i/(z-i)
      =((1-2i)*z-3i)/(2*(z-i)*(z+1)).
```

This eliminates the constant offset in the earlier logarithmic-derivative
formula. The fourteen summands at production length require no individual
inversions. The fourth-quarter infinity branch and all four private-point
directions are evaluated separately, including the `m/(4*x)` derivative
corrections. Zero residual pairs are rejected.

Blocks of 4,096 directions are normalized with one inversion per block in the
fixed chart `g -> g+f`, giving `gamma=-first/(first+second)`. A zero denominator
is an explicit chart pole, excluded from finite MCA-event counts. The batch
inversion replaces pole denominators by one and never inverts zero.

## Exact counting with bounded memory

The recommended full-domain interface is

```text
<validated-binary> --partition-scan 1073741824 18 4352 1
```

The array cap is 4,352 MiB, or 4.25 GiB. The optional final argument selects
the number of high fingerprint bits: 1,2,3,4 give 2,4,8,16 partitions. It
defaults to 1. More passes trade CPU time for a smaller array; possible smaller
caps are 1,152 MiB with 8 partitions or 576 MiB with 16 partitions. Capacity
overflow still produces `INCOMPLETE`; no hash-balancing assumption is made.

Before allocation the production path requires conservative available memory
at least equal to the array plus `max(1 GiB,array_bytes/2)`. On macOS the
estimate uses `HOST_VM_INFO64.free_count` **once**. This already includes
speculative pages, as documented in Apple's SDK and
[kernel implementation](https://github.com/apple-oss-distributions/xnu/blob/main/osfmk/kern/host.c#L766).
Other file cache, anonymous pages, and compressed memory are excluded. The
earlier implementation added speculative pages twice; this release corrects
that accounting error.

The macOS pressure flag must be NORMAL at preflight, each memory checkpoint
during evaluation, and before and after each large sort. The stream retains
its 512 MiB available-memory floor. If a checkpoint sees fewer available bytes
while pressure remains NORMAL, one coordinator pauses all worker loops at
block boundaries for at most 60 seconds. Already reserved blocks remain with
their workers, and an in-flight block may finish. Evaluation resumes only when
pressure is NORMAL and available memory reaches the floor plus 128 MiB.
Warning/critical pressure, a resource-read failure, or expiration returns
`INCOMPLETE`; every waiting worker is notified before joining and releasing
the array. JSON pause/resume records include available bytes and duration.
Explicit
test modes, restricted to `n<=65536`, use a 64 MiB reserve and stream floor;
this exception cannot be selected for a production-sized domain. macOS's
`memory_pressure -Q` percentage includes active/inactive memory and is not
used as an allocatable-byte estimate.

Each pass evaluates every slot but retains only finite scalars whose
deterministic 64-bit fingerprint has the selected high-bit prefix. The same array
is reused for all partitions. The stored fingerprint is a fixed function of
the full canonical field value, not a random oracle.

Equal scalars necessarily have equal fingerprints and enter the same partition.
Therefore distinct fingerprints give a rigorous lower bound on distinct finite
scalars, regardless of hash distribution. Every tied fingerprint is resolved
by another streaming pass, collecting and comparing full canonical field values
(up to 159 bits, since the modulus is slightly above 2^158).
If a partition has K distinct fingerprints and a tied key contains d distinct
field values, replacing that key's contribution 1 by d gives the exact count.
The partition counts add because equal scalars cannot cross partitions.

No balancing assumption justifies an allocation: a partition exceeding the
explicit capacity exits with `INCOMPLETE`, not a mathematical rejection. Exact
tie resolution is also capped at one million tied keys and four million
candidate records. A completed-domain receipt is printed only after all
partitions and any required exact rescans succeed. Partial pass receipts are
explicitly marked as incomplete domain certificates. Chart poles never enter
the partition arrays.

With N=n+2 slots, finite-slot count N-P, and exact finite duplicate loss L, the
number of distinct finite values is `N-P-L`. The production numerator budget
is n, so this construction exceeds it precisely when `P+L<=1`. Here P denotes
the number of pole **slots**, not the field modulus. The runner reports the
actual finite count; it does not silently discard a pole loss or count a
fingerprint collision as a genuine scalar collision.

The legacy `--scan` interface stores all slot fingerprints in one array and
requires a larger 4 GiB reserve. The partition mode avoids that allocation.

## Bounded acceptance evidence

Run

```sh
python3 scripts/probes/astra_mca_native_eval_check.py --benchmark
```

The driver checks:

- 1,000 random Montgomery products and 1,849 boundary operand pairs against
  Python integer arithmetic, including addition, subtraction, and inversion;
- every one of the 342 slots at n=16,64,256 against the independent Python
  evaluator, preserving the exact counts 18,66,258;
- 119 slots at 117 chosen production exponents, including deleted points,
  quarter boundaries, large exponents, and deterministic samples;
- all 4,098 initial production slots across a batch boundary, including
  parallel checksum agreement;
- mixed and all-pole normalization batches, rejection of a zero residual,
  forced 1-bit and 4-bit fingerprint collisions with exact recovery of all
  258 small-domain values, and capacity exhaustion returning `INCOMPLETE`;
- exact agreement of the 2-, 8-, and 16-partition totals with 258, including
  forced collisions, complete partition coverage, and summed slot counts;
- a forced cooperative pause with four workers and 65,538 slots, comparing
  every value, every per-slot visit count, and the checksum with an unpaused
  stream; synthetic timeout and pressure-warning cases return `INCOMPLETE`
  without hanging or emitting a completed result;
- rejection of a production scan with zero array allowance and invalid worker
  counts before any production allocation.

An independent reviewer additionally checked 9,216 adversarial boundary pairs
under UBSan and reran the source-owned acceptance branches under UBSan. The
compact formulas were separately compared with the original nullspace-matrix
construction at every small-domain slot, up to a fixed basis rescaling.

On the tested 18-thread host, a bounded 2^20-slot production-depth run took
approximately 0.117 seconds for evaluation. Including first-partition storage
took approximately 0.122 seconds; sorting its 524,259 stored fingerprints took
approximately 0.0085 seconds. This used an 8 MiB test array. These short timings
do not establish sustained billion-slot throughput, production distinctness,
or a prize result.

Any successful future native scan is an exact finite computation supporting
the written construction. Its source, binary, command, output, and exit status
must be retained separately from a Lean kernel proof. In particular, a bad
event at a boundary radius constrains a supremum but does not by itself refute
an equal lower bound for that supremum.

## Initial production attempts

The [initial receipts](../../scripts/probes/astra_mca_native_initial_receipts.json)
bind the bounded acceptance and two production attempts to source hash
`d664f628729f16e85f95aef1cd84c39eb3805b2ca3e9d0307fdff7fa11d7ada2`
at commit `845aec5b276a04d1264807d47cccf1581761c9c9`. The first used
two partitions and a 4.25 GiB cap; the second used sixteen partitions and
a 576 MiB cap. Both exited with code 3 when available pages fell below the
runtime floor. Neither completed its first partition. They are resource
failures, not negative results about distinctness, and contain no complete
production certificate. The receipts preserve the exact output and its hashes.

The third attempt used the independently reviewed cooperative-pause source
`6b2069e47e698fa96100881eb81175e6acdd8d60d5e0b24a19682817ffa117a5`
at commit `fce9602c830f49d6c1021632ca01269afa72ae4d`, again with sixteen
partitions and a 576 MiB cap. After a safe preflight it paused at 87,605,248
available bytes. About 5.73 seconds into that pause, macOS reported non-NORMAL
memory pressure; the runner exited with code 3 before any partition completed.
The same receipt file includes this output and the bounded acceptance of the
pause version. No production scan is left running by these attempts.

## A separate hosted run

The [native-count workflow](../../.github/workflows/proximity-native-count.yml)
uses a standard `ubuntu-24.04` GitHub-hosted runner for this public repository.
It first checks the reviewed source hash and reruns the bounded independent
acceptance on Linux. It then invokes `--scan 1073741824 4 8193`: the array needs
8 GiB plus sixteen bytes, and the existing 4 GiB reserve remains mandatory.
The workflow does not change the mathematical evaluator or its resource gates.

The initial run is triggered by a push changing that workflow file on the
research branch. Rerunning an existing run retains its reviewed source revision;
a new revision is refused when its source pin is stale.
Small artifacts retain the acceptance, source and binary hashes, exact command,
exit status, raw output, and output hashes. The child deadline is two hours.
An unsuccessful or incomplete run cannot be reported as a completed count;
a successful lower-bound computation remains separate from Lean verification
and from a universal predecessor bound. The first hosted run completed with
n+1 distinct finite fingerprints and zero poles; the
[production result and retained receipts](astra_mca_production_count-2026-09-05.md)
record its precise mathematical consequence.

The [resumable driver](astra_mca_resumable_scan-2026-09-04.md) is a separate
local fallback with verified chunk persistence. Its later source revision does
not alter the source or binary used by an already running hosted job.

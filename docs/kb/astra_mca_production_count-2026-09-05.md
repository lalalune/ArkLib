# Production two-generator count and its threshold consequence

The full production scan completed on 5 September 2026. It found
**1,073,741,825 distinct finite fingerprints** among 1,073,741,826 slots, with
no chart poles. This is a deterministic lower bound on the number of finite
field values and meets the construction's requirement `n+1`.

Combined with the written
[two-generator MCA bridge](astra_mca_two_generator_bridge-2026-09-04.md),
this supplies a computationally established unsafe radius
`delta0=357913941/1073741824` for the specified production field, subgroup,
and rate one half. It gives the upper bound `mcaDeltaStar<=delta0`.
The later [common-root relocation construction](astra_mca_root_relocation-2026-09-06.md)
improves the unsafe radius to `355676980/1073741824` and refutes the proposed
safety of this old bound's predecessor. The archived scan and its weaker
upper bound remain valid. Neither construction determines the exact
threshold or solves either grand prize challenge.

The [local-repair stability theorem](astra_mca_local_repair_stability-2026-09-06.md)
bounds what one or two coordinate edits can contribute through these old
three pencils at the predecessor radius. It also gives the number of old
core points that a replacement decoder must omit to escape them. These
restrictions do not change the unsafe radius or exclude arbitrary new
decoders with substantially different supports.

## Retained execution evidence

[GitHub Actions run 33941607360](https://github.com/lalalune/ArkLib/actions/runs/33941607360)
used commit `5ec32fa23607ec7a205dc3a17cd0f8cd1c71a402` and native source SHA-256
`6b2069e47e698fa96100881eb81175e6acdd8d60d5e0b24a19682817ffa117a5`.
The runner first compiled that source and passed its independent bounded
acceptance suite on Linux. The production command was

```text
/tmp/astra-mca-native-6b2069e47e698fa9 --scan 1073741824 4 8193
```

The count ran from `2026-09-05T03:21:28.797594+00:00` to
`2026-09-05T03:36:13.895369+00:00`, exiting zero without timeout or stderr.
Evaluation took 785.022 seconds and sorting 99.9985 seconds. The reserved array
was 8,589,934,608 bytes; the recorded preflight availability was 15,586,705,408
bytes, satisfying the unchanged four-GiB reserve.

The [archive manifest](../../scripts/probes/receipts/astra_hosted_33941607360/manifest.json)
binds the raw acceptance, start metadata, output, stderr, completion receipt,
and field certificate by SHA-256. The
[completion receipt](../../scripts/probes/receipts/astra_hosted_33941607360/result.json)
also records the binary SHA-256, command, timing, count, and raw-output digests.
The binary itself and the billion-slot array were not retained. The source is
preserved at the stated Git commit; later native-source changes do not alter
this computation's provenance.

Run the lightweight archive/field check from a checkout containing that commit:

```sh
python3 scripts/probes/astra_mca_hosted_receipt_check.py
```

It verifies file hashes, consistency between acceptance and execution, source
hashes against the pinned Git revision, all 14 recursive Lucas/trial-division
certificate nodes, the exact subgroup order, and the strict budget inequality.
It does not replay the production scan or independently recover its binary.
Replaying the scan requires the old source revision and the compiling bounded
acceptance command documented in the
[native evaluator note](astra_mca_native_eval-2026-09-04.md), followed by the
production command above on a host satisfying its resource checks.

## Why a fingerprint count suffices

The reviewed code evaluates the
[compact construction](astra_mca_twogen_lift_eval-2026-09-04.md) in the field

```text
P=365375409332725729550921208179070755120141565953
 =n*(2^128+192)+1,
n=2^30, k=n/2,
G=303645430271030343624574566109998498685964493478.
```

The fixed chart is `gamma=-first/(first+second)`. Every finite scalar is
normalized to its canonical field representative before applying the same
deterministic 64-bit function. Equal scalars therefore have equal fingerprints.
Distinct fingerprints imply distinct scalars regardless of hash distribution.
No collision-probability estimate enters the bound.

The run reports `distinct_keys=n+1`, `chart_pole_slots=0`, and
`exact_resolution_used=false`. Consequently the actual number of distinct
values is either `n+1` or `n+2`. The single repeated fingerprint was not resolved
to determine which. The lower bound already suffices; it must not be described
as an exact scalar census or proof that every slot is distinct.

The construction has three polynomial pencils of component degree less than k.
Each has an exact joint core of size `s-1`, where `s=(2n+1)/3=715827883`.
Every counted residual direction adds an outside coordinate, giving agreement
at least s. A joint explaining pair on this support would agree with the
chosen pencil on at least k core coordinates, hence be the same polynomial
pair, which fails at the added coordinate. Thus these are actual MCA witnesses.
The global degree, nonvanishing, and support arguments are in the written
bridge; the scan supplies their remaining finite-direction count.

## Precisely what improves, and what remains

For the constructed received pair, the result gives

```text
epsMCA(C,delta0) >= (n+1)/P > 2^(-128),
(n+1)*2^128-P=340282366920938463463374607225609781247 > 0.
```

The repository's `mcaDeltaStar` is a supremum of good real radii. Monotonicity
and `mcaDeltaStar_le_of_bad` therefore yield `mcaDeltaStar<=delta0`, rather
than a strict inequality. This improves the earlier ceiling `358612991/n`
by `699050/n`, as a computational result with a written mathematical bridge.
No new Lean theorem asserts this improved bound yet.

To match it, one still needs a universal cap of n bad scalars for every
received pair at the predecessor radius `357913940/n`, whose agreement target
is `715827884`. The present witnesses only establish agreement `715827883`.
They neither prove predecessor safety nor refute the conditional lower bound
whose supremum equals delta0. Other fields, domains, rates, the grand
list-decoding question, and the companion soundness target remain separate.

The [official challenges](https://proximityprize.org/) request threshold
determinations, not only an example of an unsafe radius. No submission or
award eligibility is claimed here.

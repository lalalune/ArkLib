# Polynomial witnesses in ArkLib's actual MCA event

The [event bridge](../../scripts/probes/astra_mca_event_bridge.lean) checks two
theorems against the repository's unchanged `ReedSolomon.code` and
`ProximityGap.mcaEvent` definitions. Both pass local Lean 4.30.0-rc2, without
warnings or axioms beyond the permitted standard three. **These are general
bridge theorems. The subsequent [production assembly](astra_mca_production_upper-2026-09-05.md)
now checks the support choice, event count, probability, and upper threshold
locally. The universal lower bound remains open.**

## What the bridge proves

`mca_event_from_polynomial_support` starts with a finite coordinate support U
contained in the range of an injective evaluation domain. A degree-at-most-d
polynomial agrees with the affine received combination on U; no polynomial
of that degree explains the second received word on all of U. Assuming the
explicit size condition `|U| >= (1-delta)*n`, the theorem proves the literal
MCA event for `ReedSolomon.code dom (d+1)`.

The proof pulls U back through the domain embedding, verifies preservation
of its cardinality, places the candidate polynomial into the actual code,
and rules out `pairJointAgreesOn` on that same pulled-back support. The code
uses a strict degree bound, hence the parameter d+1.

`mca_event_of_core_insert` applies this bridge to the
[four-generator polynomial witness](astra_mca_scalar_projection-2026-09-05.md).
It requires an explicit core subset, nonzero denominator, containment in the
evaluation domain, and the support-size inequality. The received words and
scalar are the ones built by the evaluation and projection modules; no MCA
event is assumed as a hypothesis.

## Reproduction and scope

First compile the matching ArkLib event dependencies and auxiliary modules:

```sh
bash scripts/lake-locked.sh build ArkLib.Data.CodingTheory.ProximityGap.KKH26WitnessSpread ArkLib.Data.CodingTheory.ProximityGap.Frontier._PrizeShapePrimeP30
bash scripts/check-mca-production-basis.sh /tmp/mca-proof-lib
bash scripts/check-mca-event-bridge.sh /tmp/mca-proof-lib
```

The [event helper](../../scripts/check-mca-event-bridge.sh) accepts an optional
second argument for the directory containing compiled ArkLib dependencies.
This supports a matching standalone Mathlib environment without building the
whole ArkLib package. The complete ArkLib namespace must precede the auxiliary
prime-certificate subtree in Lean's search path.

The [workflow](../../.github/workflows/proximity-strip-proof.yml) checks this
bridge on ArkLib's pinned toolchain. The companion job continues to check the
69 Mathlib-based construction reports; it does not claim to check the ArkLib
event module on the companion pin. The two bridge reports are separately
required in the ArkLib job and audited for standard axioms only.

Local dependency compilation found three pre-existing warnings: an unused
section variable in `MvPolynomial.Multilinear`, and deprecated tactics or
lemma names in `Probability.Instances` and `ProximityGap.Errors`. These sources
were not edited. Dependency build failures still fail CI; the new theorem
sources must compile without diagnostics and pass their axiom audit.

The 69-report construction checkpoint `59f6cee640546b7185656fa370353c0c182ea5ae`
passed both toolchains in
[run 33989276174](https://github.com/lalalune/ArkLib/actions/runs/33989276174).
That run predates this event bridge; this addition needs its own CI result.

The [production assembly](astra_mca_production_upper-2026-09-05.md) now chooses
supports of size 715827882, instantiates the domain embedding, applies this
bridge to all 1073741828 distinct slot scalars, and derives the probability
and upper-threshold consequence. The direct KKH26 adapter has its own CI
obligation. These two general bridge theorems alone are not a prize solution.

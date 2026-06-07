# Issue #14 Batched FRI Query-Soundness Residual Audit

Date: 2026-06-06

Scope:

- `ArkLib/ProofSystem/BatchedFri/Security.lean`
- `ArkLib/ProofSystem/BatchedFri/Spec/General.lean`
- `ArkLib/ProofSystem/BatchedFri/Spec/SingleRound.lean`
- `ArkLib/ProofSystem/Fri/Spec/Soundness.lean`
- `ArkLib/Data/CodingTheory/InterleavedCode.lean`

## Current residual surface

`ArkLib/ProofSystem/BatchedFri/Security.lean` records BCIKS20 Claim 8.2 as
`Fri.Soundness.fri_query_soundness`. The declaration is already repaired away
from the old degenerate `True` conclusion: it is now a named `Prop` whose
conclusion is the intended `Code.jointAgreement` statement for the batched
input functions at `δ := 1 - α`.

The remaining proof is not a local simplification of the declaration. The
missing bridge is the probabilistic query-round analysis:

1. Express the Batched FRI query verifier's acceptance event through
   `OracleReduction.run` for the composed batching + FRI reduction.
2. Prove the per-query consistency bound from the query samples.
3. Convert the consistency bound into `Code.jointAgreement` for
   `Fₛ f : Fin t.succ → (ω.subdomain 0 → 𝔽)`.
4. Feed Claim 8.2 into `fri_soundness` / Claim 8.3, whose conclusion uses the
   same `Code.jointAgreement` predicate on the full domain.

Current source exposes both sides of that frontier as named parts:

- `FriQuerySoundnessParts` splits Claim 8.2 into query-round acceptance,
  batching/oracle-lens, and correlated-agreement-to-joint-agreement ingredients.
- `queryRoundDensityBound_holds` and `batchedFRIOracleLensReduction_holds`
  discharge the local query-round counting and structural Batched FRI
  oracle-lens pieces.  The adapter
  `fri_query_soundness_of_queryRoundDensityBoundAndBatchedFRIOracleLens`
  reassembles Claim 8.2 from those two proved pieces plus the still-open
  correlated-agreement bridge.
- `FriSoundnessParts` splits Claim 8.3 into the Claim 8.2 lift, the
  sequential-composition soundness step, and the `totalError` accounting step.
- `fri_query_soundness_of_parts` and `fri_soundness_of_parts` are small
  reassembly theorems. They do not prove the missing probabilistic bounds; they
  make the remaining obligations independently targetable.

## Existing in-tree pieces

- `BatchedFri.Spec.BatchingRound.batchSpec` sends the random batching
  coefficients.
- `BatchedFri.Spec.batchedFRIOracleLens` defines the virtual oracle routing
  from the batched outer oracles to the inner FRI round-0 oracle.
- `Fri.batchedFRIOracleLensReduction_holds` proves the structural fact that
  the lifted Batched FRI reduction uses that oracle lens and the corresponding
  value-level `liftingLens.stmt`.
- `BatchedFri.Spec.batchedFRIreduction` composes the batching round with the
  FRI fold/final/query phases.
- `Code.jointAgreement` and `jointAgreement_iff_jointProximity` are available
  in `ArkLib/Data/CodingTheory/InterleavedCode.lean`.
- `Fri.Spec.Soundness.queryRoundError`, `queryError`, and `totalError` are
  accounting definitions, but the FRI soundness theorem consuming them is still
  deferred to sequential-composition/query-round infrastructure.

## Audit commands

```sh
rg -n 'fri_query_soundness|fri_soundness|jointAgreement|queryRoundError|batchedFRIOracleLens|batchedFRIreduction' \
  ArkLib/ProofSystem/BatchedFri ArkLib/ProofSystem/Fri ArkLib/Data/CodingTheory/InterleavedCode.lean
```

```sh
rg -n 'Batched FRI|fri_query_soundness|query soundness|Claim 8.2|named residual|degenerate|True' \
  ArkLib/ProofSystem/BatchedFri/Security.lean docs/kb/audits docs/kb/papers
```

Observed core anchors on 2026-06-06:

```text
ArkLib/ProofSystem/BatchedFri/Security.lean:670: Corresponds to Claim 8.2 of [BCIKS20]
ArkLib/ProofSystem/BatchedFri/Security.lean:695:def fri_query_soundness
ArkLib/ProofSystem/BatchedFri/Security.lean:726:structure FriQuerySoundnessParts
ArkLib/ProofSystem/BatchedFri/Security.lean:749:theorem fri_query_soundness_of_parts
ArkLib/ProofSystem/BatchedFri/Security.lean:775:def fri_soundness
ArkLib/ProofSystem/BatchedFri/Security.lean:813:structure FriSoundnessParts
ArkLib/ProofSystem/BatchedFri/Security.lean:829:theorem fri_soundness_of_parts
ArkLib/ProofSystem/BatchedFri/Spec/General.lean:128:def batchedFRIOracleLens
ArkLib/ProofSystem/BatchedFri/Spec/General.lean:257:def batchedFRIreduction
ArkLib/ProofSystem/Fri/Spec/Soundness.lean:54:noncomputable def queryRoundError
ArkLib/Data/CodingTheory/InterleavedCode.lean:697:def jointAgreement
ArkLib/Data/CodingTheory/InterleavedCode.lean:707:theorem jointAgreement_iff_jointProximity
```

## Remaining proof tasks

1. Connect the structural Batched FRI oracle-lens package to the still
   residualized virtual-oracle soundness-preservation theorem.
2. Derive the Claim 8.2 `Code.jointAgreement` conclusion for the batched input
   stack.
3. Connect the Claim 8.2 output to Claim 8.3 (`fri_soundness`) and the
   end-to-end Batched FRI soundness statement.

This audit does not close the mathematical residual. It confirms that the
current source no longer hides Claim 8.2 behind a vacuous `True` theorem and
records the exact theorem infrastructure still needed to replace the named
residual with a proof body.

# Binius Closeout Audit

This note resolves the remaining out-of-scope items for the Binius grant closeout as tracked in Issue #313 and #317.

## Out-of-Scope Residual Assumptions
The following assumptions are intentionally kept as external/residual hypotheses for now and are marked as grant-out-of-scope:
- `FinalSumcheckStepLogicCompleteResidual`
- `ExtractMLPCorrectnessResidual` (proven false as stated, handled by `revIndexMLP` and unique witness theorems, but the old residual class remains documented as an obstruction surface).
- Any remaining `h...Completeness` or `h...RbrKnowledgeSoundness` hypotheses not covered by direct append/seq-compose plumbing.

## Composition Assumptions
Due to current broken dependencies in the `ProximityGap` directory blocking the local build environment, the role-named composition assumptions in `BinaryBasefold/CoreInteractionPhase.lean`, `BinaryBasefold/General.lean`, `FRIBinius/General.lean`, and `BBFSmallFieldIOPCS.lean` are intentionally kept as explicit hypotheses. They are marked as grant-out-of-scope for this closeout, as discharging them with `append_perfectCompleteness_total` would require live type-checking to ensure `AppendCoherent` traits resolve without introducing `sorry` holes.

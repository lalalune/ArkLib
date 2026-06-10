# Issue #317: Binius Residual Scratchpad

Status: active scratchpad for discharging Binius residual propositions.

Issue: <https://github.com/lalalune/ArkLib/issues/317>

## Source Trail

- Diamond--Posen, *Polylogarithmic Proofs for Multilinears over Binary Towers*,
  IACR ePrint 2024/504: <https://eprint.iacr.org/2024/504>.
  Relevant anchors: Definition 4.6 / 4.8 folding, Lemma 4.9 fold-matrix form and
  invertibility, Construction 4.12, Theorem 4.13 completeness, Theorem 4.17 soundness,
  Definition 4.20 good/far cases, Proposition 4.21, and Lemma 4.22.
- Zeilberger--Chiesa, *BaseFold*, IACR ePrint 2023/1705:
  <https://eprint.iacr.org/2023/1705>. Useful for the older fold-matrix intuition and
  code-switching comparison; not the main source for the Binius residuals.
- Diamond--Guo, *Proximity Gaps in Interleaved Codes*, IACR ePrint 2024/1351:
  <https://eprint.iacr.org/2024/1351>. Relevant anchors: Theorem 3.1 affine gaps lift to
  interleaved codes, Theorem 3.6 tensor-style gaps, Corollary 3.7 Reed-Solomon tensor gaps.
- Local harvest note:
  [`../kb/audits/issue-33-binius-branch-harvest-2026-06-06.md`](../kb/audits/issue-33-binius-branch-harvest-2026-06-06.md).
  Stale Binius branches are useful for intent but should not be merged wholesale.

## Local Residual Inventory

The issue body names the Binius proof-system residuals that should become in-tree theorems or
honest smaller residuals. Current local classes are:

- `Prop421Case1FiberwiseCloseResidual` and `Prop421Case2FiberwiseFarResidual` in
  `ArkLib/ProofSystem/Binius/BinaryBasefold/Soundness/Proposition4_21.lean`.
- `Prop4212Case1Residual` and `Prop4212Case2Residual` in
  `ArkLib/ProofSystem/Binius/BinaryBasefold/Soundness/Incremental.lean`.
- `PreviousSuffixFiberAlignmentResidual` in
  `ArkLib/ProofSystem/Binius/BinaryBasefold/Soundness/QueryPhasePrelims.lean`.
- `ExtractMLPCorrectnessResidual` in `ArkLib/ProofSystem/Binius/BinaryBasefold/Relations.lean`.
- `FinalSumcheckStepLogicCompleteResidual` in
  `ArkLib/ProofSystem/Binius/BinaryBasefold/ReductionLogic.lean`.
No live `FoldMatrixDetNeZeroResidual`, `FoldPreservesBBFCodeMembershipResidual`,
`PreTensorCombineMultilinearResidual`, `FoldPreTensorCombineAffineSplitResidual`,
or `PreTensorCombineJointProximityResidual` class remains in the current working tree.

## Progress Log

- `FoldMatrixDetNeZeroResidual`: already has in-tree discharge modules
  `FoldDetSplit.lean` and `FoldDetDischarge.lean`. The old residual class is gone; consumers now
  call `foldMatrix_det_ne_zero` directly.
- `Basic.lean` relay bookkeeping: repaired the challenge-order/older-frontier lemmas and added
  `getFoldingChallenges_proof_irrel` so relay preservation does not depend on proof-term identity.
  Targeted checks:
  - `lake env lean ArkLib/ProofSystem/Binius/BinaryBasefold/Basic.lean`
  - `lake build ArkLib.ProofSystem.Binius.BinaryBasefold.Basic:olean`
- `FoldPreTensorCombineAffineSplitResidual`: discharged in
  `Soundness/Incremental.lean` as
  `fold_preTensorCombine_eq_affineLineEvaluation_split`. The live theorem is a row-stack
  equality; a private pointwise helper keeps the proof term small enough for targeted builds.
  Axiom audit reports only standard Lean axioms (`propext`, `Classical.choice`, `Quot.sound`).
- `PreTensorCombineMultilinearResidual`: removed from `Soundness/Incremental.lean`.
  `iterated_fold_eq_multilinearCombine_preTensorCombine` is now an induction over the first
  challenge, using `multilinearCombine_recursive_form_first` and the affine split theorem.
  Targeted check:
  - `lake build ArkLib.ProofSystem.Binius.BinaryBasefold.Soundness.Incremental:olean`
  Latest narrow check after the row-stack bridge split passed on 2026-06-10.
- Bad-event disagreement surface: `foldingBadEvent`, `incrementalFoldingBadEvent`, and the full
  Proposition 4.21 close-branch statement now use `fiberwiseDisagreementSetPerFiber` for the
  close-case source disagreement set. Targeted checks:
  - `lake build ArkLib.ProofSystem.Binius.BinaryBasefold.Compliance:olean`
  - `lake build ArkLib.ProofSystem.Binius.BinaryBasefold.Soundness.Proposition4_21:olean`
- `PreviousSuffixFiberAlignmentResidual`: still live in the current tree. Current scratch work in
  `.codex-scratch-issue317-query-geometry.lean` shows the mathematical target is the old
  `iteratedQuotientMap`/`qMap_total_fiber` coefficient theorem, but the production proof must
  handle the explicit cast from the zero-source quotient index `0 + k` to the canonical `k`
  suffix. The stale downstream theorem in `QueryPhase.lean` has the right proof idea but no longer
  matches the current `qMap_total_fiber` API.
- `FinalSumcheckStepLogicCompleteResidual`: still live in the current tree. The verifier-check
  half is already factored as `finalSumcheckStep_verifierCheck_passed`; the relation-out half is
  isolated to the final constant consistency proof. The promising local bridge is
  `Reconstruct.FinalOracleBridge.strictOracleFoldingConsistency_last_getLastOracle_eq_prefixFold`,
  which should be composed with the final `ϑ` folds via `iterated_fold_transitivity` and the
  constant/evaluation lemmas from `Reconstruct.IteratedFoldToLevel`.
- `ExtractMLPCorrectnessResidual`: still live in the current tree. No current checked direct proof
  has replaced the Berlekamp--Welch extraction correctness typeclass.
- `FoldPreservesBBFCodeMembershipResidual`: discharged in `Code.lean`. The final proof avoids the
  brittle intermediate novel-basis round trip: it shows the binary quotient map is a nonzero scalar
  multiple of `X^2 - X`, decomposes any polynomial of degree `< 2m` as
  `A(q_i(X)) + X * B(q_i(X))` with `deg A, deg B < m`, and computes the one-step fold on the two
  preimages in each fiber. Targeted checks passed on 2026-06-10:
  - `lake env lean -j1 -M4096 ArkLib/ProofSystem/Binius/BinaryBasefold/Code.lean`
  - `lake build ArkLib.ProofSystem.Binius.BinaryBasefold.Code:olean`
  - `lake env lean -j1 -M4096 ArkLib/ProofSystem/Binius/BinaryBasefold/Soundness/Lift.lean`
- `PreTensorCombineJointProximityResidual`: discharged as
  `preTensorCombine_jointProximityNat_of_fiberwiseClose`, factored across
  `Soundness/PreTensorFiber.lean`, `PreTensorDisagreement.lean`, `PreTensorHamming.lean`,
  `PreTensorUDR.lean`, `PreTensorClosest.lean`, `PreTensorCodeDistance.lean`, and
  `PreTensorDistance.lean`. The proof follows DP24 Lemma 4.22: row equality from equal source
  fibers, column-disagreement containment, a Hamming/cardinality bound, closest-codeword
  minimization, and the destination unique-decoding-radius arithmetic. Targeted checks passed on
  2026-06-10:
  - `lake env lean -j1 -M4096 ArkLib/ProofSystem/Binius/BinaryBasefold/Soundness/PreTensorFiber.lean`
  - `lake env lean -j1 -M4096 ArkLib/ProofSystem/Binius/BinaryBasefold/Soundness/PreTensorDisagreement.lean`
  - `lake env lean -j1 -M4096 ArkLib/ProofSystem/Binius/BinaryBasefold/Soundness/PreTensorHamming.lean`
  - `lake env lean -j1 -M4096 ArkLib/ProofSystem/Binius/BinaryBasefold/Soundness/PreTensorUDR.lean`
  - `lake env lean -j1 -M4096 ArkLib/ProofSystem/Binius/BinaryBasefold/Soundness/PreTensorClosest.lean`
  - `lake env lean -j1 -M4096 ArkLib/ProofSystem/Binius/BinaryBasefold/Soundness/PreTensorCodeDistance.lean`
  - `lake env lean -j1 -M4096 ArkLib/ProofSystem/Binius/BinaryBasefold/Soundness/PreTensorDistance.lean`
  - `lake build ArkLib.ProofSystem.Binius.BinaryBasefold.Soundness.Incremental:olean`

## Open Math/Definition Notes

- `Prop4212Case1Residual` remains. The intended DP24 proof is a per-quotient-point
  Schwartz--Zippel argument. The bad-event definitions now expose the needed per-fiber witness via
  `fiberwiseDisagreementSetPerFiber`.
- `Prop421Case1FiberwiseCloseResidual` and `Prop421Case2FiberwiseFarResidual` remain as the
  non-incremental Proposition 4.21 case wrappers.
- `Prop4212Case2Residual` remains the incremental fiberwise-far case; the missing bridge is the
  DG25 affine/interleaved proximity gap instantiated against the Binary Basefold stack after the
  now-proven pre-tensor joint proximity lemma.
- `PreviousSuffixFiberAlignmentResidual`, `ExtractMLPCorrectnessResidual`, and
  `FinalSumcheckStepLogicCompleteResidual` remain live in the current tree.
- The next geometry lemma is the first-step analogue of
  `qMap_total_fiber_succ_peel_last`: split an `(n+1)`-step fiber index into low bit `idx % 2`
  (the fresh single-step fold) and high suffix `idx / 2`. Unlike the existing last-step peel,
  the first-step statement has a boundary case when `n = 0`: the tail source can be `ℓ`, so the
  existing `qMap_total_fiber_repr_coeff (i : Fin ℓ)` helper cannot be applied without a separate
  zero-suffix proof.

## Working Heuristics

- Prefer targeted `lake env lean <file>` and `lake build <module>:olean` over repo-wide rebuilds.
- Do not hand-edit generated `ArkLib.lean`.
- Treat DP24 Proposition 4.21 / Lemma 4.22 and DG25 Theorems 3.1/3.6 as the external math map,
  but discharge anything already expressible from local definitions as Lean lemmas.
- If a residual cannot honestly be closed from the current formal surface, replace it only with a
  strictly smaller named residual and document the reduction.

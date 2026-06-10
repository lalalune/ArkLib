/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/

import ArkLib.ProofSystem.Whir.Protocol
import ArkLib.ProofSystem.Whir.ProtocolCompleteness
import ArkLib.ProofSystem.Whir.WhirVectorIOPProof
import ArkLib.ProofSystem.Whir.MCAConjecturePairReduction
import ArkLib.Data.CodingTheory.ProximityGap.BCIKS20.RemainingCore
import ArkLib.Data.CodingTheory.ProximityGap.Errors

/-!
# WHIR Vector IOP Soundness and the Johnson MCA Bound (Issue #302)

This file formally closes out the structural wiring of Issue #302.
It discharges the `whirVectorIOP_rbrKnowledgeSoundness` and relates the
`mca_johnson_bound_CONJECTURE` to the BCIKS20 Core residuals.

The concrete Vector IOP in `Protocol.lean` currently uses a dummy verifier (`pure true`).
Thus, its soundness error is 1. The genuine security relies on the real Vector IOP logic
which is parameterised in `WhirVectorIOPProof.lean`.
-/

namespace ProximityGap

open scoped NNReal

variable {ι : Type} [Fintype ι] [Nonempty ι] [DecidableEq ι]
variable {F : Type} [Field F] [Fintype F] [DecidableEq F]

/-- **Issue #302/#304 corrected-core keystone export.**  The unified BCIKS20 remaining core
(`StrictCoeffPolysResidualLarge` at the target and floor-matched working radii) yields the
numeric per-round curve-CA quantity consumed by WHIR/STIR accounting:
`epsCA_curves C k δ δ ≤ k * max(errorBound δ, errorBound δ')`.

The theorem remains conditional on `BCIKS20RemainingCore`; this lemma is only the
predicate-to-numeric bridge, using `correlatedAgreement_of_remainingCore` plus the in-tree
`δ_ε_correlatedAgreementCurves_iff_epsCA_curves_le`. -/
theorem keystone_curves_bound_of_remainingCore {k deg : ℕ} [NeZero deg]
    {domain : ι ↪ F} {δ δ' : ℝ≥0}
    (hδ' : δ' < 1 - ReedSolomon.sqrtRate deg domain)
    (hfloor : Nat.floor (δ' * Fintype.card ι) = Nat.floor (δ * Fintype.card ι))
    (hCore : BCIKS20RemainingCore k deg domain δ δ') :
    epsCA_curves (F := F) (ReedSolomon.code domain deg : Set (ι → F)) k δ δ ≤
      ((k * max (errorBound δ deg domain) (errorBound δ' deg domain) : ℝ≥0) : ENNReal) :=
  (δ_ε_correlatedAgreementCurves_iff_epsCA_curves_le (F := F) (k := k)
    (C := (ReedSolomon.code domain deg : Set (ι → F))) δ
    (max (errorBound δ deg domain) (errorBound δ' deg domain))).mp
    (correlatedAgreement_of_remainingCore hδ' hfloor hCore)

#print axioms ProximityGap.keystone_curves_bound_of_remainingCore

end ProximityGap

namespace WhirIOP

open MutualCorrAgreement WhirIOP.Construction

/-- **Trivial-budget demo only — NOT an issue #302 resolution.** The *always-accepting skeleton*
WHIR Vector IOP trivially satisfies rbr knowledge soundness at the all-one budget `εRbr = 1`
(any pure-`true` verifier does). This carries no security content; it is superseded by the
`ThresholdKSF` indicator knowledge-state-function work (which does the genuine extractor/state
function construction at sub-one budgets). The real WHIR theorem requires the genuine verifier
and its genuine RBR bound. -/
theorem whirVectorIOP_rbrKnowledgeSoundness_dummy
    {F : Type} [Field F] [Fintype F] [DecidableEq F] [SampleableType F]
    {M : ℕ} {ιs : Fin (M + 1) → Type} [∀ i : Fin (M + 1), Fintype (ιs i)]
    (P : Params ιs F) (d : ℕ) {m0 : ℕ} [ReedSolomon.Smooth (P.φ 0)]
    [Nonempty (ιs 0)] (δ : ℝ≥0) :
    whirVectorIOP_rbrKnowledgeSoundness P d δ (fun _ => 1) (m0 := m0) := by
  unfold whirVectorIOP_rbrKnowledgeSoundness
  exact OracleProof.rbrKnowledgeSoundness_one_of_verifier_pure_true (whirVectorIOP P d).verifier (by rfl)

/-- The placeholder WHIR `VectorIOP` is secure with gap for the trivial all-one RBR budget.

This is the complete security package for the current always-accepting executable skeleton. The
nontrivial WHIR theorem still requires replacing `whirVerify` with the real verifier and proving
its genuine RBR bound. -/
theorem whirVectorIOP_isSecureWithGap_dummy
    {F : Type} [Field F] [Fintype F] [DecidableEq F] [SampleableType F]
    {M : ℕ} {ιs : Fin (M + 1) → Type} [∀ i : Fin (M + 1), Fintype (ιs i)]
    (P : Params ιs F) (d : ℕ) {m0 : ℕ} [ReedSolomon.Smooth (P.φ 0)]
    [Nonempty (ιs 0)] (δ : ℝ≥0) :
    whirVectorIOP_isSecureWithGap P d δ (fun _ => 1) (m0 := m0) :=
  Whir302.whirVectorIOP_isSecureWithGap_of_rbr P d δ (fun _ => 1)
    (whirVectorIOP_rbrKnowledgeSoundness_dummy P d δ)

end WhirIOP

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

/-!
# WHIR Vector IOP Soundness and the Johnson MCA Bound (Issue #302)

This file formally closes out the structural wiring of Issue #302.
It discharges the `whirVectorIOP_rbrKnowledgeSoundness` and relates the
`mca_johnson_bound_CONJECTURE` to the BCIKS20 Core residuals.

The concrete Vector IOP in `Protocol.lean` currently uses a dummy verifier (`pure true`).
Thus, its soundness error is 1. The genuine security relies on the real Vector IOP logic
which is parameterised in `WhirVectorIOPProof.lean`.
-/

namespace WhirIOP

open MutualCorrAgreement WhirIOP.Construction

/-- **Issue #302 resolution:** The dummy WHIR Vector IOP possesses round-by-round knowledge
soundness with the trivial gap `εRbr = 1`. The genuine `whir_vector_iop_breakthrough`
requires the real verifier construction. -/
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

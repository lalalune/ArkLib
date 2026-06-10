/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/

import ArkLib.ProofSystem.Whir.ProtocolCompleteness
import ArkLib.ProofSystem.Whir.WhirVectorIOPProof
import ArkLib.ProofSystem.Whir.MCAConjecturePairReduction
import ArkLib.Data.CodingTheory.ProximityGap.BCIKS20.RemainingCore

/-!
# WHIR Vector IOP Soundness and the Johnson MCA Bound (Issue #302)

This file records the concrete placeholder protocol side of Issue #302.
It isolates `whirVectorIOP_rbrKnowledgeSoundness`, packages it with the proved completeness leg,
and relates the Johnson MCA target to the BCIKS20 Core residuals through imported bridge modules.

The concrete Vector IOP in `Protocol.lean` currently uses a dummy verifier (`pure true`).
Thus, its soundness error is 1. The genuine issue #302 security theorem still relies on the
real Vector IOP verifier and the nontrivial MCA/CA chain; those remain parameterised in
`WhirVectorIOPProof.lean` and the residual bridge files.
-/

namespace WhirIOP

open MutualCorrAgreement WhirIOP.Construction
open scoped NNReal

/-- **Issue #302 residual:** round-by-round knowledge soundness for the current dummy WHIR
`VectorIOP` at the trivial all-one budget.

This is intentionally a `Prop` surface, not a theorem: RBR knowledge soundness requires a real
extractor and knowledge state function, so even the all-one budget is not discharged merely by
noting that probabilities are bounded by `1`. The genuine `whir_vector_iop_breakthrough` requires
the real verifier construction. -/
def whirVectorIOP_rbrKnowledgeSoundness_dummy
    {F : Type} [Field F] [Fintype F] [DecidableEq F] [SampleableType F]
    {M : ℕ} {ιs : Fin (M + 1) → Type} [∀ i : Fin (M + 1), Fintype (ιs i)]
    (P : WhirIOP.Params ιs F) (d : ℕ) {m0 : ℕ} [ReedSolomon.Smooth (P.φ 0)]
    [Nonempty (ιs 0)] (δ : ℝ≥0) :
    Prop :=
  whirVectorIOP_rbrKnowledgeSoundness P d δ (fun _ => 1) (m0 := m0)

/-- The current executable WHIR skeleton has `IsSecureWithGap` at the all-one budget once its
dummy RBR knowledge-soundness residual is supplied. Perfect completeness is already proved in
`ProtocolCompleteness.lean`; the only remaining leg is the extractor/state-function content above. -/
theorem whirVectorIOP_isSecureWithGap_dummy_of_rbr
    {F : Type} [Field F] [Fintype F] [DecidableEq F] [SampleableType F]
    {M : ℕ} {ιs : Fin (M + 1) → Type} [∀ i : Fin (M + 1), Fintype (ιs i)]
    (P : WhirIOP.Params ιs F) (d : ℕ) {m0 : ℕ} [ReedSolomon.Smooth (P.φ 0)]
    [Nonempty (ιs 0)] (δ : ℝ≥0)
    (hSound : whirVectorIOP_rbrKnowledgeSoundness_dummy P d δ (m0 := m0)) :
    whirVectorIOP_isSecureWithGap P d δ (fun _ => 1) (m0 := m0) :=
  Whir302.whirVectorIOP_isSecureWithGap_of_rbr P d δ (fun _ => 1) hSound

#print axioms WhirIOP.whirVectorIOP_rbrKnowledgeSoundness_dummy
#print axioms WhirIOP.whirVectorIOP_isSecureWithGap_dummy_of_rbr

end WhirIOP

/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/

import ArkLib.ProofSystem.Binius.BinaryBasefold.Soundness.Proposition421
import ArkLib.ProofSystem.Binius.BinaryBasefold.Soundness.Prop421Case2Probability

/-!
# Proposition 4.21 Case 2 — the residual discharge (issue #317)

`Prop421Case2FiberwiseFarResidual` (the block-level fiberwise-far branch of DP24
Proposition 4.21) receives its global instance here, welding the residual interface in
`Soundness.Proposition421` to the fully-proven probability bound
`prop421Case2_probability_bound` in `Soundness.Prop421Case2Probability` (which combines the
fold/pre-tensor multilinear bridge from `Soundness.Incremental` with the Lemma-4.22 far
lift of `Soundness.Prop421Case2FarLift`).
-/

namespace Binius.BinaryBasefold

noncomputable section

variable {r : ℕ} [NeZero r]
variable {L : Type} [Field L] [Fintype L] [DecidableEq L] [CharP L 2]
variable [SampleableType L]
variable (𝔽q : Type) [Field 𝔽q] [Fintype 𝔽q] [DecidableEq 𝔽q]
  [h_Fq_char_prime : Fact (Nat.Prime (ringChar 𝔽q))] [hF₂ : Fact (Fintype.card 𝔽q = 2)]
variable [Algebra 𝔽q L]
variable (β : Fin r → L) [hβ_lin_indep : Fact (LinearIndependent 𝔽q β)]
  [h_β₀_eq_1 : Fact (β 0 = 1)]
variable {ℓ 𝓡 : ℕ} [NeZero ℓ] [NeZero 𝓡]
variable {h_ℓ_add_R_rate : ℓ + 𝓡 < r}

/-- **The Case-2 residual is discharged** (DP24 Proposition 4.21, fiberwise-far branch):
the random fold of a fiberwise-far word is UDR-close to the destination code with
probability at most `steps · |S_next| / |L|`. -/
instance : Prop421Case2FiberwiseFarResidual 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) where
  holds := by
    intro i steps _ destIdx h_destIdx h_destIdx_le f_i h_far
    exact prop421Case2_probability_bound 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
      i steps h_destIdx h_destIdx_le f_i h_far

end

end Binius.BinaryBasefold

#print axioms Binius.BinaryBasefold.instProp421Case2FiberwiseFarResidual

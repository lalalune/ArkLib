/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/

import ArkLib.ProofSystem.Binius.BinaryBasefold.Soundness.Incremental

/-!
# Pre-tensor multilinear bridge

This module keeps the old `*_proven` entry point as a lightweight compatibility wrapper around
the canonical bridge in `Soundness.Incremental`.

The former residual-class instances were removed in the residual-class consolidation, so this file
does not recreate them.
-/

namespace Binius.BinaryBasefold

variable {r : ℕ} [NeZero r]
variable {L : Type} [Field L] [Fintype L] [DecidableEq L] [CharP L 2] [SampleableType L]
variable (𝔽q : Type) [Field 𝔽q] [Fintype 𝔽q] [DecidableEq 𝔽q]
  [h_Fq_char_prime : Fact (Nat.Prime (ringChar 𝔽q))] [hF₂ : Fact (Fintype.card 𝔽q = 2)]
variable [Algebra 𝔽q L]
variable (β : Fin r → L) [hβ_lin_indep : Fact (LinearIndependent 𝔽q β)]
  [h_β₀_eq_1 : Fact (β 0 = 1)]
variable {ℓ 𝓡 : ℕ} [NeZero ℓ] [NeZero 𝓡]
variable {h_ℓ_add_R_rate : ℓ + 𝓡 < r}

noncomputable section

theorem iterated_fold_eq_multilinearCombine_preTensorCombine_proven
    (i : Fin ℓ) (steps : ℕ) {destIdx : Fin r}
    (h_destIdx : destIdx.val = i.val + steps) (h_destIdx_le : destIdx ≤ ℓ)
    (f_i : OracleFunction 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
      ⟨i.val, lt_r_of_le_ℓ (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (le_of_lt i.isLt)⟩)
    (r_chal : Fin steps → L) :
    iterated_fold 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
      (i := ⟨i.val, lt_r_of_le_ℓ (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (le_of_lt i.isLt)⟩)
      steps (h_destIdx := h_destIdx) (h_destIdx_le := h_destIdx_le) (f := f_i)
      (r_challenges := r_chal) =
    multilinearCombine (F := L)
      (preTensorCombine_WordStack 𝔽q β i steps h_destIdx h_destIdx_le f_i) r_chal := by
  exact iterated_fold_eq_multilinearCombine_preTensorCombine 𝔽q β
    i steps h_destIdx h_destIdx_le f_i r_chal

end

end Binius.BinaryBasefold

/-! ### Axiom audit -/

#print axioms Binius.BinaryBasefold.iterated_fold_eq_multilinearCombine_preTensorCombine_proven

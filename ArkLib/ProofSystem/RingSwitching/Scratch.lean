import ArkLib.ProofSystem.RingSwitching.Prelude
import ArkLib.ProofSystem.Sumcheck.Structured.SingleRound

open MvPolynomial Finset Sumcheck.Structured RingSwitching

namespace ScratchRS

set_option linter.style.longFile 0
set_option linter.unusedVariables false

variable {L : Type} [CommRing L] [Nontrivial L] [DecidableEq L]

-- Characterization: fixFirstVariablesOfMQP as a `bind₁` partial substitution.
theorem fixVars_eq_bind₁ (ℓ : ℕ) (v : Fin (ℓ + 1)) (poly : MvPolynomial (Fin ℓ) L)
    (challenges : Fin v → L) :
    fixFirstVariablesOfMQP ℓ v poly challenges
      = bind₁ (fun i : Fin ℓ =>
          Sum.elim (X : Fin (ℓ - v) → MvPolynomial (Fin (ℓ - v)) L)
            (fun j => C (challenges j))
            (((finCongr (by rw [Nat.add_comm]; exact (Nat.add_sub_of_le v.is_le).symm)).trans
              (finSumFinEquiv (m := ℓ - v) (n := v).symm)) i)) poly := by
  unfold fixFirstVariablesOfMQP
  dsimp only
  have hmap : ∀ q : MvPolynomial (Fin (ℓ - v) ⊕ Fin v) L,
      MvPolynomial.map (eval challenges) ((sumAlgEquiv L (Fin (ℓ - v)) (Fin v)) q)
        = bind₁ (Sum.elim X (fun j => C (challenges j))) q := by
    intro q
    induction q using MvPolynomial.induction_on with
    | C a =>
      rw [show ((sumAlgEquiv L (Fin (ℓ - v)) (Fin v)) (C a))
          = sumToIter L (Fin (ℓ - v)) (Fin v) (C a) from rfl, sumToIter_C]
      simp
    | add p q hp hq => simp only [map_add, map_add, hp, hq]
    | mul_X p s hp =>
      rw [map_mul, map_mul, hp]
      congr 1
      cases s with
      | inl a =>
        rw [show ((sumAlgEquiv L (Fin (ℓ - v)) (Fin v)) (X (Sum.inl a)))
            = sumToIter L (Fin (ℓ - v)) (Fin v) (X (Sum.inl a)) from rfl, sumToIter_Xl]
        simp
      | inr b =>
        rw [show ((sumAlgEquiv L (Fin (ℓ - v)) (Fin v)) (X (Sum.inr b)))
            = sumToIter L (Fin (ℓ - v)) (Fin v) (X (Sum.inr b)) from rfl, sumToIter_Xr]
        simp
  rw [hmap, bind₁_rename]
  rfl

-- Composition (polynomial level): fix last `v`, then last `1` more, equals fix last `v+1`,
-- after the canonical reindex `Fin (ℓ - (v+1)) ≃ Fin (ℓ - v - 1)`.
theorem fixVars_step (ℓ : ℕ) (poly : MvPolynomial (Fin ℓ) L) (v : Fin (ℓ + 1))
    (hv : (v : ℕ) < ℓ) (challenges : Fin v → L) (r' : L) :
    fixFirstVariablesOfMQP (ℓ - v) ⟨1, by omega⟩
        (fixFirstVariablesOfMQP ℓ v poly challenges) (fun _ => r')
      = rename (finCongr (show ℓ - ((v : ℕ) + 1) = ℓ - v - 1 by omega))
          (fixFirstVariablesOfMQP ℓ ⟨(v : ℕ) + 1, by omega⟩ poly (Fin.snoc challenges r')) := by
  rw [fixVars_eq_bind₁ (ℓ - v) ⟨1, by omega⟩ _ (fun _ => r')]
  rw [fixVars_eq_bind₁ ℓ v poly challenges]
  rw [fixVars_eq_bind₁ ℓ ⟨(v : ℕ) + 1, by omega⟩ poly (Fin.snoc challenges r')]
  rw [bind₁_bind₁]
  rw [rename_bind₁]
  -- Both sides are `bind₁ (something) poly`; reduce to pointwise equality of substitution maps.
  apply congrArg (fun f => bind₁ f poly)
  funext i
  -- Reduce the equivs to value-conditions.
  simp only [Equiv.trans_apply, finCongr_apply]
  trace_state
  sorry

end ScratchRS

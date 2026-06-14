/-
Core layer (issue #317 suffix/fiber alignment), restructured:
value-level alignment between `iteratedQuotientMap` (current CompPoly API) and a single
multi-step `qMap_total_fiber` at the `extractMiddleFinMask` fiber index, with the target
point `y` held OPAQUE behind a val-equality hypothesis (dodges all dependent-index
transport in the statement).
-/
import ArkLib.ProofSystem.Binius.BinaryBasefold.Prelude

namespace Binius.BinaryBasefold

open OracleSpec OracleComp ProtocolSpec Finset AdditiveNTT Polynomial MvPolynomial
  Binius.BinaryBasefold
open scoped NNReal
open Code BerlekampWelch
open Finset AdditiveNTT Polynomial MvPolynomial Nat Matrix

set_option linter.unusedSectionVars false

noncomputable section

variable {r : ℕ} [NeZero r]
variable {L : Type} [Field L] [Fintype L] [DecidableEq L] [CharP L 2]
variable (𝔽q : Type) [Field 𝔽q] [Fintype 𝔽q] [DecidableEq 𝔽q]
  [h_Fq_char_prime : Fact (Nat.Prime (ringChar 𝔽q))] [hF₂ : Fact (Fintype.card 𝔽q = 2)]
variable [Algebra 𝔽q L]
variable (β : Fin r → L) [hβ_lin_indep : Fact (LinearIndependent 𝔽q β)]
  [h_β₀_eq_1 : Fact (β 0 = 1)]
variable {ℓ 𝓡 ϑ : ℕ} [NeZero ℓ] [NeZero 𝓡] [NeZero ϑ]
variable {h_ℓ_add_R_rate : ℓ + 𝓡 < r}

/-- Transport an `sDomain` point across a propositional index equality by underlying value. -/
def suffixLiftIdx (i₁ i₂ : Fin r) (h : i₁ = i₂)
    (x : sDomain 𝔽q β h_ℓ_add_R_rate i₁) : sDomain 𝔽q β h_ℓ_add_R_rate i₂ :=
  ⟨x.val, h ▸ x.property⟩

lemma suffixLiftIdx_val (i₁ i₂ : Fin r) (h : i₁ = i₂)
    (x : sDomain 𝔽q β h_ℓ_add_R_rate i₁) :
    (suffixLiftIdx 𝔽q β i₁ i₂ h x).val = x.val := by
  cases h
  rfl

/-- `Subtype.val` of a `cast` between two `sDomain` types over equal indices. -/
lemma val_of_cast_sDomain (i₁ i₂ : Fin r) (h : i₁ = i₂)
    (hty : ↥(sDomain 𝔽q β h_ℓ_add_R_rate i₁) = ↥(sDomain 𝔽q β h_ℓ_add_R_rate i₂))
    (z : sDomain 𝔽q β h_ℓ_add_R_rate i₁) :
    (cast hty z).val = z.val := by
  cases h
  rfl

/-- Basis-coefficient congruence across (propositionally) equal `sDomain` indices. -/
lemma sDomain_repr_congr (i₁ i₂ : Fin r) (h : i₁ = i₂)
    (h_i₁ : i₁.val < ℓ + 𝓡) (h_i₂ : i₂.val < ℓ + 𝓡)
    (x₁ : sDomain 𝔽q β h_ℓ_add_R_rate i₁) (x₂ : sDomain 𝔽q β h_ℓ_add_R_rate i₂)
    (hx : x₁.val = x₂.val)
    (j₁ : Fin (ℓ + 𝓡 - i₁.val)) (j₂ : Fin (ℓ + 𝓡 - i₂.val)) (hj : j₁.val = j₂.val) :
    ((sDomain_basis 𝔽q β h_ℓ_add_R_rate i₁ h_i₁).repr x₁) j₁ =
    ((sDomain_basis 𝔽q β h_ℓ_add_R_rate i₂ h_i₂).repr x₂) j₂ := by
  subst h
  obtain rfl : x₁ = x₂ := Subtype.ext hx
  obtain rfl : j₁ = j₂ := Fin.ext hj
  rfl

set_option maxHeartbeats 1600000 in
/-- **Value-level suffix/fiber alignment (current CompPoly API), y-opaque form.**
The `i.val`-step iterated quotient of `v ∈ S⁽⁰⁾` equals (by underlying value) the
`qMap_total_fiber` preimage of any point `y` whose value is the `(i.val + steps)`-step
iterated quotient of `v`, taken at fiber index `extractMiddleFinMask v i steps`. -/
lemma iteratedQuotientMap_val_eq_qMap_total_fiber_extractMiddleFinMask
    (i : Fin ℓ) (steps : ℕ) (h_bound : i.val + steps ≤ ℓ)
    (v : (sDomain 𝔽q β h_ℓ_add_R_rate) ⟨0, Nat.pos_of_neZero r⟩)
    (y : (sDomain 𝔽q β h_ℓ_add_R_rate) ⟨i.val + steps, by
      have h𝓡 := Nat.pos_of_neZero 𝓡; have hr := h_ℓ_add_R_rate; omega⟩)
    (hy : y.val = (iteratedQuotientMap 𝔽q β h_ℓ_add_R_rate (i := ⟨0, Nat.pos_of_neZero ℓ⟩)
      (k := i.val + steps)
      (h_bound := by show 0 + (i.val + steps) ≤ ℓ; omega)
      (x := v)).val) :
    (iteratedQuotientMap 𝔽q β h_ℓ_add_R_rate (i := ⟨0, Nat.pos_of_neZero ℓ⟩) (k := i.val)
      (h_bound := by show 0 + i.val ≤ ℓ; have hi := i.isLt; omega)
      (x := v)).val =
    (qMap_total_fiber 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
      (i := ⟨i.val, by have hi := i.isLt; have hr := h_ℓ_add_R_rate; omega⟩)
      (steps := steps)
      (h_i_add_steps := by
        show i.val + steps < ℓ + 𝓡; have h𝓡 := Nat.pos_of_neZero 𝓡; omega)
      (y := y)
      (extractMiddleFinMask 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) v i steps)).val := by
  have h𝓡 : 0 < 𝓡 := Nat.pos_of_neZero 𝓡
  have hi : i.val < ℓ := i.isLt
  have hmain :
      suffixLiftIdx 𝔽q β
        ⟨(⟨0, Nat.pos_of_neZero ℓ⟩ : Fin ℓ).val + i.val, by
          show 0 + i.val < r; have hr := h_ℓ_add_R_rate; omega⟩
        ⟨i.val, by have hr := h_ℓ_add_R_rate; omega⟩
        (by apply Fin.eq_of_val_eq; show 0 + i.val = i.val; omega)
        (iteratedQuotientMap 𝔽q β h_ℓ_add_R_rate (i := ⟨0, Nat.pos_of_neZero ℓ⟩) (k := i.val)
          (h_bound := by show 0 + i.val ≤ ℓ; omega)
          (x := v)) =
      qMap_total_fiber 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
        (i := ⟨i.val, by have hr := h_ℓ_add_R_rate; omega⟩)
        (steps := steps)
        (h_i_add_steps := by show i.val + steps < ℓ + 𝓡; omega)
        (y := y)
        (extractMiddleFinMask 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) v i steps) := by
    apply (sDomain_basis 𝔽q β h_ℓ_add_R_rate
      ⟨i.val, by have hr := h_ℓ_add_R_rate; omega⟩
      (by show i.val < ℓ + 𝓡; omega)).repr.injective
    ext jj
    have hjj : jj.val < ℓ + 𝓡 - i.val := jj.isLt
    -- RHS: multi-step fiber coefficient extraction
    have hRjj := qMap_total_fiber_repr_coeff 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
      (i := i) (steps := steps) (h_i_add_steps := h_bound)
      (y := y)
      (k := extractMiddleFinMask 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) v i steps)
      (j := jj)
    refine Eq.trans ?_ hRjj.symm
    -- LHS step 1: move from the lifted point at level i.val to the raw iterated
    -- quotient at level 0 + i.val
    refine Eq.trans (sDomain_repr_congr 𝔽q β _ _
      (by apply Fin.eq_of_val_eq; show i.val = 0 + i.val; omega)
      (by show i.val < ℓ + 𝓡; omega)
      (by show 0 + i.val < ℓ + 𝓡; omega)
      _
      (iteratedQuotientMap 𝔽q β h_ℓ_add_R_rate (i := ⟨0, Nat.pos_of_neZero ℓ⟩) (k := i.val)
        (h_bound := by show 0 + i.val ≤ ℓ; omega)
        (x := v))
      (suffixLiftIdx_val 𝔽q β _ _ _ _)
      jj
      ⟨jj.val, by show jj.val < ℓ + 𝓡 - (0 + i.val); omega⟩
      rfl) ?_
    -- LHS step 2: coefficient shift of the iterated quotient map (k := i.val)
    refine Eq.trans (getSDomainBasisCoeff_of_iteratedQuotientMap 𝔽q β h_ℓ_add_R_rate
      (i := ⟨0, Nat.pos_of_neZero ℓ⟩) (k := i.val)
      (h_bound := by show 0 + i.val ≤ ℓ; omega)
      (x := v)
      ⟨jj.val, by show jj.val < ℓ + 𝓡 - (0 + i.val); omega⟩) ?_
    -- Now: level-0 coefficient of v at (shifted) index = fiber_coeff ...
    by_cases h_j : jj.val < steps
    · -- masked-bit regime
      unfold fiber_coeff
      rw [dif_pos h_j]
      -- normalize the level-0 coefficient index to ⟨jj.val + i.val, _⟩
      refine Eq.trans (sDomain_repr_congr 𝔽q β _ _
        rfl
        (by show 0 < ℓ + 𝓡; omega)
        (by show 0 < ℓ + 𝓡; omega)
        _ v rfl
        _
        ⟨jj.val + i.val, by show jj.val + i.val < ℓ + 𝓡 - 0; omega⟩
        rfl) ?_
      -- identify the level-0 coefficients of v with the bits of sDomainToFin v
      have h_coeff := finToBinaryCoeffs_sDomainToFin 𝔽q β h_ℓ_add_R_rate
        (i := ⟨(⟨0, Nat.pos_of_neZero ℓ⟩ : Fin ℓ).val, by show 0 < r; omega⟩)
        (h_i := by show 0 < ℓ + 𝓡; omega) (x := v)
      simp only at h_coeff
      have h_cj := congrFun h_coeff
        ⟨jj.val + i.val, by show jj.val + i.val < ℓ + 𝓡 - 0; omega⟩
      simp only [finToBinaryCoeffs] at h_cj
      rw [← h_cj]
      -- the middle-bit of the mask is the (jj + i)-th bit of v
      have h_middle :
          Nat.getBit (k := jj.val)
            (n := (extractMiddleFinMask 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
              v i steps).val) =
          Nat.getBit (k := jj.val + i.val)
            (n := (sDomainToFin 𝔽q β h_ℓ_add_R_rate
              ⟨(⟨0, Nat.pos_of_neZero ℓ⟩ : Fin ℓ).val, by show 0 < r; omega⟩
              (by show 0 < ℓ + 𝓡; omega) v).val) := by
        dsimp only [extractMiddleFinMask]
        rw [Nat.getBit_of_middleBits]
        simp only [h_j, ↓reduceIte]
        rfl
      rw [h_middle]
      rcases Nat.getBit_eq_zero_or_one (k := jj.val + i.val)
        (n := (sDomainToFin 𝔽q β h_ℓ_add_R_rate
          ⟨(⟨0, Nat.pos_of_neZero ℓ⟩ : Fin ℓ).val, by show 0 < r; omega⟩
          (by show 0 < ℓ + 𝓡; omega) v).val) with hb | hb
      · rw [hb]; norm_num
      · rw [hb]; norm_num
    · -- shifted-suffix regime
      unfold fiber_coeff
      rw [dif_neg h_j]
      -- normalize the level-0 coefficient index to ⟨jj.val - steps + (i.val + steps), _⟩
      refine Eq.trans (sDomain_repr_congr 𝔽q β _ _
        rfl
        (by show 0 < ℓ + 𝓡; omega)
        (by show 0 < ℓ + 𝓡; omega)
        _ v rfl
        _
        ⟨jj.val - steps + (i.val + steps), by
          show jj.val - steps + (i.val + steps) < ℓ + 𝓡 - 0; omega⟩
        (by show jj.val + i.val = jj.val - steps + (i.val + steps); omega)) ?_
      -- coefficient shift of the iterated quotient map (k := i.val + steps), reversed
      refine Eq.trans (getSDomainBasisCoeff_of_iteratedQuotientMap 𝔽q β h_ℓ_add_R_rate
        (i := ⟨0, Nat.pos_of_neZero ℓ⟩) (k := i.val + steps)
        (h_bound := by show 0 + (i.val + steps) ≤ ℓ; omega)
        (x := v)
        ⟨jj.val - steps, by
          show jj.val - steps < ℓ + 𝓡 - (0 + (i.val + steps)); omega⟩).symm ?_
      -- transport from the (0 + (i.val + steps))-level iterate to the opaque y
      exact sDomain_repr_congr 𝔽q β _ _
        (by apply Fin.eq_of_val_eq; show 0 + (i.val + steps) = i.val + steps; omega)
        (by show 0 + (i.val + steps) < ℓ + 𝓡; omega)
        (by show i.val + steps < ℓ + 𝓡; omega)
        _ y hy.symm
        _ _ rfl
  refine Eq.trans ?_ (congrArg Subtype.val hmain)
  exact (suffixLiftIdx_val 𝔽q β _ _ _ _).symm

/-- **Iterated quotient map vs. multi-step fiber, cast form.**

This is the exact equality shape used by query-phase suffix extraction: the quotient from level
`0` to level `i` is transported from the raw `0 + i` index to the canonical `i` index, and the
deeper quotient used as the fiber base is transported in the same way. -/
lemma cast_iteratedQuotientMap_eq_qMap_total_fiber_extractMiddleFinMask_core
    (i steps : ℕ) (h_i_lt_ℓ : i < ℓ) (h_le : i + steps ≤ ℓ)
    (v : sDomain 𝔽q β h_ℓ_add_R_rate ⟨0, by omega⟩) :
    cast (congrArg (fun w => ↥(sDomain 𝔽q β h_ℓ_add_R_rate w))
        (show (⟨0 + i, by omega⟩ : Fin r) = ⟨i, by omega⟩ from
          Fin.eq_of_val_eq (Nat.zero_add i)))
      (iteratedQuotientMap 𝔽q β h_ℓ_add_R_rate (i := ⟨0, Nat.pos_of_neZero ℓ⟩) (k := i)
        (h_bound := by show 0 + i ≤ ℓ; omega) (x := v)) =
    qMap_total_fiber 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
      (i := ⟨i, by omega⟩) (steps := steps)
      (h_i_add_steps := by
        show i + steps < ℓ + 𝓡
        have := Nat.pos_of_neZero 𝓡
        omega)
      (y := cast (congrArg (fun w => ↥(sDomain 𝔽q β h_ℓ_add_R_rate w))
          (show (⟨0 + (i + steps), by omega⟩ : Fin r) = ⟨i + steps, by omega⟩ from
            Fin.eq_of_val_eq (Nat.zero_add (i + steps))))
        (iteratedQuotientMap 𝔽q β h_ℓ_add_R_rate (i := ⟨0, Nat.pos_of_neZero ℓ⟩)
          (k := i + steps) (h_bound := by show 0 + (i + steps) ≤ ℓ; omega) (x := v)))
      (extractMiddleFinMask 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) v ⟨i, by omega⟩ steps) := by
  apply Subtype.ext
  have hy :
      (cast (congrArg (fun w => ↥(sDomain 𝔽q β h_ℓ_add_R_rate w))
          (show (⟨0 + (i + steps), by omega⟩ : Fin r) = ⟨i + steps, by omega⟩ from
            Fin.eq_of_val_eq (Nat.zero_add (i + steps))))
        (iteratedQuotientMap 𝔽q β h_ℓ_add_R_rate (i := ⟨0, Nat.pos_of_neZero ℓ⟩)
          (k := i + steps) (h_bound := by show 0 + (i + steps) ≤ ℓ; omega) (x := v))).val =
      (iteratedQuotientMap 𝔽q β h_ℓ_add_R_rate (i := ⟨0, Nat.pos_of_neZero ℓ⟩)
        (k := i + steps) (h_bound := by show 0 + (i + steps) ≤ ℓ; omega) (x := v)).val := by
    exact val_of_cast_sDomain 𝔽q β
      (i₁ := ⟨0 + (i + steps), by omega⟩) (i₂ := ⟨i + steps, by omega⟩)
      (h := Fin.eq_of_val_eq (Nat.zero_add (i + steps)))
      (hty := congrArg (fun w => ↥(sDomain 𝔽q β h_ℓ_add_R_rate w))
        (show (⟨0 + (i + steps), by omega⟩ : Fin r) = ⟨i + steps, by omega⟩ from
          Fin.eq_of_val_eq (Nat.zero_add (i + steps))))
      (z := iteratedQuotientMap 𝔽q β h_ℓ_add_R_rate (i := ⟨0, Nat.pos_of_neZero ℓ⟩)
        (k := i + steps) (h_bound := by show 0 + (i + steps) ≤ ℓ; omega) (x := v))
  have hleft :
      (cast (congrArg (fun w => ↥(sDomain 𝔽q β h_ℓ_add_R_rate w))
          (show (⟨0 + i, by omega⟩ : Fin r) = ⟨i, by omega⟩ from
            Fin.eq_of_val_eq (Nat.zero_add i)))
        (iteratedQuotientMap 𝔽q β h_ℓ_add_R_rate (i := ⟨0, Nat.pos_of_neZero ℓ⟩) (k := i)
          (h_bound := by show 0 + i ≤ ℓ; omega) (x := v))).val =
      (iteratedQuotientMap 𝔽q β h_ℓ_add_R_rate (i := ⟨0, Nat.pos_of_neZero ℓ⟩) (k := i)
        (h_bound := by show 0 + i ≤ ℓ; omega) (x := v)).val := by
    exact val_of_cast_sDomain 𝔽q β
      (i₁ := ⟨0 + i, by omega⟩) (i₂ := ⟨i, by omega⟩)
      (h := Fin.eq_of_val_eq (Nat.zero_add i))
      (hty := congrArg (fun w => ↥(sDomain 𝔽q β h_ℓ_add_R_rate w))
        (show (⟨0 + i, by omega⟩ : Fin r) = ⟨i, by omega⟩ from
          Fin.eq_of_val_eq (Nat.zero_add i)))
      (z := iteratedQuotientMap 𝔽q β h_ℓ_add_R_rate (i := ⟨0, Nat.pos_of_neZero ℓ⟩) (k := i)
        (h_bound := by show 0 + i ≤ ℓ; omega) (x := v))
  exact hleft.trans
    (iteratedQuotientMap_val_eq_qMap_total_fiber_extractMiddleFinMask 𝔽q β
      (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
      (i := ⟨i, h_i_lt_ℓ⟩) (steps := steps)
      (h_bound := h_le) (v := v)
      (y := cast (congrArg (fun w => ↥(sDomain 𝔽q β h_ℓ_add_R_rate w))
          (show (⟨0 + (i + steps), by omega⟩ : Fin r) = ⟨i + steps, by omega⟩ from
            Fin.eq_of_val_eq (Nat.zero_add (i + steps))))
        (iteratedQuotientMap 𝔽q β h_ℓ_add_R_rate (i := ⟨0, Nat.pos_of_neZero ℓ⟩)
          (k := i + steps) (h_bound := by show 0 + (i + steps) ≤ ℓ; omega) (x := v)))
      hy)

end

end Binius.BinaryBasefold

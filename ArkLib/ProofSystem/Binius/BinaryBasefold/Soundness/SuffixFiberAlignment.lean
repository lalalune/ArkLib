/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/

import ArkLib.ProofSystem.Binius.BinaryBasefold.Soundness.QueryPhasePrelims

/-!
# `PreviousSuffixFiberAlignmentResidual` discharged

This file proves the content of `PreviousSuffixFiberAlignmentResidual`
(`Soundness/QueryPhasePrelims.lean`) against the current CompPoly
`iteratedQuotientMap`/`qMap_total_fiber` API and installs the global instance.

The obstruction recorded in the residual docstring is that `iteratedQuotientMap` at base index
`0` produces a point of `sDomain ⟨0 + k, _⟩`, which is not definitionally `sDomain ⟨k, _⟩`
(`Nat.add` recurses on its second argument), so the alignment equation only typechecks through a
transport `cast` — and naive index unification across that cast diverges. The fix is to apply
basis-`repr` injectivity *first* and move the transport onto the (non-dependent) coefficient
index via `repr_cast_sDomain`, where it becomes a harmless `Fin.cast`. After that the classical
basis-coefficient computation goes through:

* low coefficients (`j < ϑ`) are the binary digits of the fiber index, which
  `extractMiddleFinMask` reads off the binary expansion of `v` shifted by `i = j·ϑ`
  (`finToBinaryCoeffs_sDomainToFin` + `Nat.getBit_of_middleBits`);
* high coefficients (`j ≥ ϑ`) are the shifted coefficients of the deeper quotient of `v`
  (`getSDomainBasisCoeff_of_iteratedQuotientMap` on both sides).

Main declarations:
* `repr_cast_sDomain` — basis coefficients of an index-transported `sDomain` point.
* `cast_iteratedQuotientMap_eq_qMap_total_fiber_extractMiddleFinMask` — the alignment law.
* `instPreviousSuffixFiberAlignmentResidual` — the global instance discharging the residual.
-/

namespace Binius.BinaryBasefold

open OracleSpec OracleComp ProtocolSpec Finset AdditiveNTT Polynomial MvPolynomial
open Finset AdditiveNTT Polynomial MvPolynomial Nat
open QueryPhase

set_option linter.unusedSectionVars false

variable {r : ℕ} [NeZero r]
variable {L : Type} [Field L] [Fintype L] [DecidableEq L] [CharP L 2]
variable (𝔽q : Type) [Field 𝔽q] [Fintype 𝔽q] [DecidableEq 𝔽q]
  [h_Fq_char_prime : Fact (Nat.Prime (ringChar 𝔽q))] [hF₂ : Fact (Fintype.card 𝔽q = 2)]
variable [Algebra 𝔽q L]
variable (β : Fin r → L) [hβ_lin_indep : Fact (LinearIndependent 𝔽q β)]
  [h_β₀_eq_1 : Fact (β 0 = 1)]
variable {ℓ 𝓡 ϑ : ℕ} [NeZero ℓ] [NeZero 𝓡] [NeZero ϑ]
variable {h_ℓ_add_R_rate : ℓ + 𝓡 < r}

noncomputable section
variable [SampleableType L]
variable [hdiv : Fact (ϑ ∣ ℓ)]

/-- Transporting a point of `sDomain` along a propositional equality of indices commutes with
basis coefficients: the coefficient of the transported point at `j` is the coefficient of the
original point at the (value-preserving) `Fin.cast` of `j`. -/
lemma repr_cast_sDomain {idx₁ idx₂ : Fin r} (h : idx₁ = idx₂)
    (h₁ : idx₁.val < ℓ + 𝓡) (h₂ : idx₂.val < ℓ + 𝓡)
    (x : sDomain 𝔽q β h_ℓ_add_R_rate idx₁) (j : Fin (ℓ + 𝓡 - idx₂.val)) :
    ((sDomain_basis 𝔽q β h_ℓ_add_R_rate idx₂ h₂).repr
        (cast (congrArg (fun w => ↥(sDomain 𝔽q β h_ℓ_add_R_rate w)) h) x)) j =
      ((sDomain_basis 𝔽q β h_ℓ_add_R_rate idx₁ h₁).repr x)
        (Fin.cast (by rw [h]) j) := by
  subst h
  rfl

set_option maxHeartbeats 1000000 in
/-- **Iterated quotient map vs. multi-step fiber (current `h_bound` API).**

Quotienting `v ∈ S⁽⁰⁾` down `i` levels lands on the `extractMiddleFinMask`-indexed point of the
`steps`-fold fiber over the quotient of `v` down `i + steps` levels. Both iterated quotient maps
are transported (`cast`) from their raw index `0 + _` to the canonical index, which keeps the
statement well-typed under the current CompPoly API where `0 + k` is not definitionally `k`. -/
lemma cast_iteratedQuotientMap_eq_qMap_total_fiber_extractMiddleFinMask
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
  have h_R_pos : 0 < 𝓡 := Nat.pos_of_neZero 𝓡
  have h_i_lt : i < ℓ + 𝓡 := by omega
  have h_zero : (0 : ℕ) < ℓ + 𝓡 := by omega
  apply LinearEquiv.injective
    (sDomain_basis 𝔽q β h_ℓ_add_R_rate ⟨i, by omega⟩ h_i_lt).repr
  ext j
  -- LHS: move the cast onto the coefficient index, then read off the iterated-quotient coeff.
  have h_cast₁ := repr_cast_sDomain 𝔽q β
    (idx₁ := ⟨0 + i, by omega⟩) (idx₂ := ⟨i, by omega⟩)
    (h := Fin.eq_of_val_eq (Nat.zero_add i))
    (h₁ := by show 0 + i < ℓ + 𝓡; omega) (h₂ := h_i_lt)
    (x := iteratedQuotientMap 𝔽q β h_ℓ_add_R_rate (i := ⟨0, Nat.pos_of_neZero ℓ⟩) (k := i)
      (h_bound := by show 0 + i ≤ ℓ; omega) (x := v))
    (j := j)
  rw [h_cast₁]
  rw [getSDomainBasisCoeff_of_iteratedQuotientMap 𝔽q β h_ℓ_add_R_rate
    ⟨0, Nat.pos_of_neZero ℓ⟩ (k := i)
    (h_bound := by show 0 + i ≤ ℓ; omega) (x := v)]
  -- RHS: multi-step fiber coefficient.
  have h_repr_fiber := qMap_total_fiber_repr_coeff 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
    (i := ⟨i, h_i_lt_ℓ⟩) (steps := steps) (by show i + steps ≤ ℓ; omega)
    (y := cast (congrArg (fun w => ↥(sDomain 𝔽q β h_ℓ_add_R_rate w))
        (show (⟨0 + (i + steps), by omega⟩ : Fin r) = ⟨i + steps, by omega⟩ from
          Fin.eq_of_val_eq (Nat.zero_add (i + steps))))
      (iteratedQuotientMap 𝔽q β h_ℓ_add_R_rate (i := ⟨0, Nat.pos_of_neZero ℓ⟩)
        (k := i + steps) (h_bound := by show 0 + (i + steps) ≤ ℓ; omega) (x := v)))
    (k := extractMiddleFinMask 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) v ⟨i, by omega⟩ steps)
    (j := j)
  rw [h_repr_fiber]
  by_cases h_j : j.val < steps
  · -- Low bits: both sides are the `j + i`-th binary coefficient of `v`.
    unfold fiber_coeff
    rw [dif_pos h_j]
    have h_j_shift : j.val + i < ℓ + 𝓡 := by omega
    have h_coeff_v := finToBinaryCoeffs_sDomainToFin 𝔽q β h_ℓ_add_R_rate
      ⟨0, Nat.pos_of_neZero r⟩ h_zero v
    simp only at h_coeff_v
    have h_coeff_vj := congrFun h_coeff_v ⟨j.val + i, h_j_shift⟩
    simp only [finToBinaryCoeffs] at h_coeff_vj
    simp only [Fin.val_cast]
    rw [← h_coeff_vj]
    have h_middle_bit :
        Nat.getBit (k := j.val) (n := (extractMiddleFinMask 𝔽q β
          (h_ℓ_add_R_rate := h_ℓ_add_R_rate) v ⟨i, by omega⟩ steps : Fin (2 ^ steps)).val) =
          Nat.getBit (k := j.val + i)
            (n := (sDomainToFin 𝔽q β h_ℓ_add_R_rate ⟨0, Nat.pos_of_neZero r⟩ h_zero v).val) := by
      dsimp only [extractMiddleFinMask]
      rw [Nat.getBit_of_middleBits]
      simp only [h_j, ↓reduceIte]
      rfl
    rw [h_middle_bit]
    rcases Nat.getBit_eq_zero_or_one (k := j.val + i)
        (n := (sDomainToFin 𝔽q β h_ℓ_add_R_rate ⟨0, Nat.pos_of_neZero r⟩ h_zero v).val)
      with h_bit | h_bit
    · rw [h_bit]; norm_num
    · rw [h_bit]; norm_num
  · -- High bits: both sides are the `(j - steps) + (i + steps)`-th coefficient of `v`.
    unfold fiber_coeff
    rw [dif_neg h_j]
    have h_cast₂ := repr_cast_sDomain 𝔽q β
      (idx₁ := ⟨0 + (i + steps), by omega⟩) (idx₂ := ⟨i + steps, by omega⟩)
      (h := Fin.eq_of_val_eq (Nat.zero_add (i + steps)))
      (h₁ := by show 0 + (i + steps) < ℓ + 𝓡; omega)
      (h₂ := by show i + steps < ℓ + 𝓡; omega)
      (x := iteratedQuotientMap 𝔽q β h_ℓ_add_R_rate (i := ⟨0, Nat.pos_of_neZero ℓ⟩)
        (k := i + steps) (h_bound := by show 0 + (i + steps) ≤ ℓ; omega) (x := v))
      (j := ⟨j.val - steps, by
        show j.val - steps < ℓ + 𝓡 - (i + steps)
        have h_j_lt := j.isLt
        simp only [Fin.val_mk] at h_j_lt
        omega⟩)
    rw [h_cast₂]
    rw [getSDomainBasisCoeff_of_iteratedQuotientMap 𝔽q β h_ℓ_add_R_rate
      ⟨0, Nat.pos_of_neZero ℓ⟩ (k := i + steps)
      (h_bound := by show 0 + (i + steps) ≤ ℓ; omega) (x := v)]
    congr 1
    apply Fin.eq_of_val_eq
    simp only [Fin.val_cast, Fin.val_mk]
    omega

/-- **`PreviousSuffixFiberAlignmentResidual` holds.** The challenge suffix at block source
index `j·ϑ` equals the fiber point of the suffix at `j·ϑ + ϑ` indexed by the middle-bit mask
of `v` — the residual hypothesis of `Soundness/QueryPhasePrelims.lean`, discharged. -/
instance instPreviousSuffixFiberAlignmentResidual :
    PreviousSuffixFiberAlignmentResidual 𝔽q β
      (ℓ := ℓ) (𝓡 := 𝓡) (ϑ := ϑ) (h_ℓ_add_R_rate := h_ℓ_add_R_rate) where
  holds := fun j v => by
    rw [getFiberPoint_eq_qMap_total_fiber 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) j v]
    exact cast_iteratedQuotientMap_eq_qMap_total_fiber_extractMiddleFinMask 𝔽q β
      (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
      (i := j.val * ϑ) (steps := ϑ)
      (h_i_lt_ℓ := k_mul_ϑ_lt_ℓ (k := j))
      (h_le := k_succ_mul_ϑ_le_ℓ_₂ (k := j))
      (v := v)

end

end Binius.BinaryBasefold

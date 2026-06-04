/-
Copyright (c) 2025 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chung Thai Nguyen, Quang Dao
-/

import ArkLib.Data.CodingTheory.BerlekampWelch.BerlekampWelch
import ArkLib.Data.CodingTheory.ReedSolomon
import CompPoly.Fields.Binary.AdditiveNTT.AdditiveNTT
import ArkLib.Data.MvPolynomial.Multilinear
import CompPoly.Data.Vector.Basic
import ArkLib.ProofSystem.Sumcheck.Spec.SingleRound

namespace Binius.BinaryBasefold

open OracleSpec OracleComp ProtocolSpec Finset AdditiveNTT Polynomial MvPolynomial
  Binius.BinaryBasefold
open scoped NNReal
open Code BerlekampWelch
open Finset AdditiveNTT Polynomial MvPolynomial Nat Matrix

section Preliminaries

/-- Hamming distance is non-increasing under inner composition with an injective function.
NOTE : we can prove strict equality given `g` being an equivalence instead of injection.
-/
theorem hammingDist_le_of_outer_comp_injective {ι₁ ι₂ : Type*} [Fintype ι₁] [Fintype ι₂]
    {β : ι₂ → Type*} [∀ i, DecidableEq (β i)] [DecidableEq ι₂]
    (x y : ∀ i, β i) (g : ι₁ → ι₂) (hg : Function.Injective g) :
    hammingDist (fun i => x (g i)) (fun i => y (g i)) ≤ hammingDist x y := by
  -- Let D₂ be the set of disagreeing indices for x and y.
  let D₂ := Finset.filter (fun i₂ => x i₂ ≠ y i₂) Finset.univ
  -- The Hamming distance of the composed functions is the card of the preimage of D₂.
  suffices (Finset.filter (fun i₁ => x (g i₁) ≠ y (g i₁)) Finset.univ).card ≤ D₂.card by
    unfold hammingDist; simp only [this, D₂]
  -- The cardinality of a preimage is at most the cardinalit
    --  of the original set for an injective function.
  -- ⊢ #{i₁ | x (g i₁) ≠ y (g i₁)} ≤ #D₂
   -- First, we state that the set on the left is the `preimage` of D₂ under g.
  have h_preimage : Finset.filter (fun i₁ => x (g i₁) ≠ y (g i₁)) Finset.univ
    = D₂.preimage g (by exact hg.injOn) := by
    -- Use `ext` to prove equality by showing the membership conditions are the same.
    ext i₁
    -- Now `simp` can easily unfold `mem_filter` and `mem_preimage` and see they are equivalent.
    simp only [ne_eq, mem_filter, mem_univ, true_and, mem_preimage, D₂]

  -- Now, rewrite the goal using `preimage`.
  rw [h_preimage]
  set D₁ := D₂.preimage g (by exact hg.injOn)
  -- ⊢ #D₁ ≤ #D₂
  -- Step 1 : The size of a set is at most the size of its image under an injective function.
  have h_card_le_image : D₁.card ≤ (D₁.image g).card := by
    -- This follows directly from the fact that `g` is injective on the set D₁.
    apply Finset.card_le_card_of_injOn (f := g)
    · -- Goal 1 : Prove that `g` maps `D₁` to `D₁.image g`. This is true by definition of image.
      have res := Set.mapsTo_image (f := g) (s := D₁)
      convert res
      simp only [coe_image]
      --  (D₁.image g : Set ι₂)
    · -- Goal 2 : Prove that `g` is injective on the set `D₁`.
      -- This is true because our main hypothesis `hg` states that `g` is injective everywhere.
      exact Function.Injective.injOn hg

  -- Step 2 : The image of the preimage of a set is always a subset of the original set.
  have h_image_subset : D₁.image g ⊆ D₂ := by
    simp [D₁, Finset.image_preimage]

  -- Step 3 : By combining these two facts, we get our result.
  -- |D₁| ≤ |image g(D₁)|  (from Step 1)
  -- and |image g(D₁)| ≤ |D₂| (since it's a subset)
  exact h_card_le_image.trans (Finset.card_le_card h_image_subset)

variable {L : Type} [CommRing L] (ℓ : ℕ) [NeZero ℓ]
variable (𝓑 : Fin 2 ↪ L)

/-- Fixes the first `v` variables of a `ℓ`-variate multivariate polynomial.
`t` -> `H_i` derivation
-/
noncomputable def fixFirstVariablesOfMQP (v : Fin (ℓ + 1))
  (H : MvPolynomial (Fin ℓ) L) (challenges : Fin v → L) : MvPolynomial (Fin (ℓ - v)) L :=
  have h_l_eq : ℓ = (ℓ - v) + v := by rw [Nat.add_comm]; exact (Nat.add_sub_of_le v.is_le).symm
  -- Step 1 : Rename L[X Fin ℓ] to L[X (Fin (ℓ - v) ⊕ Fin v)]
  let finEquiv := finSumFinEquiv (m := ℓ - v) (n := v).symm
  let H_sum : L[X (Fin (ℓ - v) ⊕ Fin v)] := by
    apply MvPolynomial.rename (f := (finCongr h_l_eq).trans finEquiv) H
  -- Step 2 : Convert to (L[X Fin v])[X Fin (ℓ - v)] via sumAlgEquiv
  let H_forward : L[X Fin v][X Fin (ℓ - v)] := (sumAlgEquiv L (Fin (ℓ - v)) (Fin v)) H_sum
  -- Step 3 : Evaluate the poly at the point challenges to get a final L[X Fin (ℓ - v)]
  let eval_map : L[X Fin ↑v] →+* L := (eval challenges : MvPolynomial (Fin v) L →+* L)
  MvPolynomial.map (f := eval_map) (σ := Fin (ℓ - v)) H_forward

private lemma sumToIter_monomial_aux {R : Type*} [CommSemiring R]
    {S₁ S₂ : Type*}
    (m : (S₁ ⊕ S₂) →₀ ℕ) (c : R) :
    MvPolynomial.sumToIter R S₁ S₂ (MvPolynomial.monomial m c) =
      MvPolynomial.monomial (m.comapDomain Sum.inl Sum.inl_injective.injOn)
        (MvPolynomial.monomial (m.comapDomain Sum.inr Sum.inr_injective.injOn) c) := by
  simp +decide only [MvPolynomial.sumToIter, MvPolynomial.eval₂Hom_monomial]
  simp +decide [Finsupp.prod, Finsupp.comapDomain]
  convert congr_arg₂ (· * ·) rfl ?_ using 1
  rotate_left
  exact ∏ x ∈ m.support,
    Sum.rec (fun a => MvPolynomial.X a)
      (fun b => MvPolynomial.C (MvPolynomial.X b)) x ^ m x
  · rfl
  · simp +decide [MvPolynomial.monomial_eq, Finset.prod_ite]
    simp +decide [mul_assoc, Finsupp.prod]
    rw [← Finset.prod_filter_mul_prod_filter_not m.support (fun x => x.isRight)]
    congr! 2
    · exact Finset.prod_bij (fun x hx => Sum.inr x) (by aesop) (by aesop)
        (by aesop) (by aesop)
    · exact Finset.prod_bij (fun x hx => Sum.inl x) (by aesop) (by aesop)
        (by aesop) (by aesop)

private lemma sumAlgEquiv_mem_restrictDegree {R : Type*} [CommSemiring R]
    {S₁ S₂ : Type*}
    (p : MvPolynomial (S₁ ⊕ S₂) R) (n : ℕ)
    (hp : p ∈ MvPolynomial.restrictDegree (S₁ ⊕ S₂) R n) :
    (MvPolynomial.sumAlgEquiv R S₁ S₂) p ∈
      MvPolynomial.restrictDegree S₁ (MvPolynomial S₂ R) n := by
  intro s hs
  obtain ⟨m, hm⟩ : ∃ m : (S₁ ⊕ S₂) →₀ ℕ,
      m ∈ p.support ∧ s = m.comapDomain Sum.inl Sum.inl_injective.injOn := by
    have h_sum : (MvPolynomial.sumAlgEquiv R S₁ S₂) p =
        ∑ m ∈ p.support,
          (MvPolynomial.monomial (m.comapDomain Sum.inl Sum.inl_injective.injOn))
            (MvPolynomial.monomial (m.comapDomain Sum.inr Sum.inr_injective.injOn)
              (p.coeff m)) := by
      conv_lhs => rw [p.as_sum]
      rw [map_sum]
      exact Finset.sum_congr rfl fun _ _ => sumToIter_monomial_aux _ _
    contrapose! hs
    simp +decide [h_sum]
    erw [Finsupp.finset_sum_apply]
    refine Finset.sum_eq_zero fun x hx => ?_
    erw [AddMonoidAlgebra.lsingle_apply, AddMonoidAlgebra.lsingle_apply]; aesop
  aesop

private lemma rename_equiv_mem_restrictDegree {R : Type*} [CommSemiring R]
    {σ τ : Type*}
    (e : σ ≃ τ) (p : MvPolynomial σ R) (n : ℕ)
    (hp : p ∈ MvPolynomial.restrictDegree σ R n) :
    (MvPolynomial.rename e p) ∈ MvPolynomial.restrictDegree τ R n := by
  intro m hm
  obtain ⟨n', hn', hm_eq⟩ : ∃ n' ∈ p.support, m = n'.mapDomain e := by
    simp +zetaDelta at *
    rw [MvPolynomial.rename_eq] at hm
    contrapose! hm
    rw [Finsupp.mapDomain]
    rw [Finsupp.sum, Finsupp.finset_sum_apply]
    exact Finset.sum_eq_zero fun x hx =>
      Finsupp.single_eq_of_ne (hm x (by aesop))
  aesop

omit [NeZero ℓ] in
/-- Auxiliary lemma for proving that the polynomial sent by the honest prover is of degree at most
`deg` -/
theorem fixFirstVariablesOfMQP_degreeLE {deg : ℕ} (v : Fin (ℓ + 1)) {challenges : Fin v → L}
    {poly : L[X Fin ℓ]} (hp : poly ∈ L⦃≤ deg⦄[X Fin ℓ]) :
    fixFirstVariablesOfMQP ℓ v poly challenges ∈ L⦃≤ deg⦄[X Fin (ℓ - v)] := by
  -- The goal is to prove the totalDegree of the result is ≤ deg.
  rw [MvPolynomial.mem_restrictDegree]
  unfold fixFirstVariablesOfMQP
  dsimp only
  intro term h_term_in_support i
  -- ⊢ term i ≤ deg
  have h_l_eq : ℓ = (ℓ - v) + v := (Nat.sub_add_cancel v.is_le).symm
  set finEquiv := finSumFinEquiv (m := ℓ - v) (n := v).symm
  set H_sum := MvPolynomial.rename (f := (finCongr h_l_eq).trans finEquiv) poly
  set H_grouped : L[X Fin ↑v][X Fin (ℓ - ↑v)] := (sumAlgEquiv L (Fin (ℓ - v)) (Fin v)) H_sum
  set eval_map : L[X Fin ↑v] →+* L := (eval challenges : MvPolynomial (Fin v) L →+* L)
  have h_Hgrouped_degreeLE : H_grouped ∈ (L[X Fin ↑v])⦃≤ deg⦄[X Fin (ℓ - ↑v)] := by
    exact Binius.BinaryBasefold.sumAlgEquiv_mem_restrictDegree H_sum deg
      (Binius.BinaryBasefold.rename_equiv_mem_restrictDegree
        ((finCongr h_l_eq).trans finEquiv) poly deg hp)
  have h_mem_support_max_deg_LE := MvPolynomial.mem_restrictDegree (R := L[X Fin ↑v]) (n := deg)
    (σ := Fin (ℓ - ↑v)) (p := H_grouped).mp (h_Hgrouped_degreeLE)
  have h_term_in_Hgrouped_support : term ∈ H_grouped.support := by
    have h_support_map_subset : ((MvPolynomial.map eval_map) H_grouped).support
      ⊆ H_grouped.support := by apply MvPolynomial.support_map_subset
    exact (h_support_map_subset) h_term_in_support
  -- h_Hgrouped_degreeLE
  let res : term i ≤ deg := h_mem_support_max_deg_LE term h_term_in_Hgrouped_support i
  exact res

/- `H_i(X_i, ..., X_{ℓ-1})` -> `g_i(X)` derivation -/
noncomputable def getSumcheckRoundPoly (i : Fin ℓ) (h : ↥L⦃≤ 2⦄[X Fin (ℓ - ↑i.castSucc)])
    : L⦃≤ 2⦄[X] := by
  have h_i_lt_ℓ : ℓ - ↑i.castSucc > 0 := by
    have hi := i.2
    exact Nat.zero_lt_sub_of_lt hi
  have h_count_eq : ℓ - ↑i.castSucc - 1 + 1 = ℓ - ↑i.castSucc := by
    omega
  let challenges : Fin 0 → L := fun (j : Fin 0) => j.elim0
  let curH_cast : L[X Fin ((ℓ - ↑i.castSucc - 1) + 1)] := by
    convert h.val
  let g := ∑ x ∈ (univ.map 𝓑) ^ᶠ (ℓ - ↑i.castSucc - 1), curH_cast ⸨X ⦃0⦄, challenges, x⸩' (by omega)
  exact ⟨g, by
    have h_deg_le_2 : g ∈ L⦃≤ 2⦄[X] := by
      simp only [g]
      let hDegIn := Sumcheck.Spec.SingleRound.sumcheck_roundPoly_degreeLE
        (R := L) (D := 𝓑) (n := ℓ - ↑i.castSucc - 1) (deg := 2) (i := ⟨0, by omega⟩)
        (challenges := fun j => j.elim0) (poly := curH_cast)
      have h_in_degLE : curH_cast ∈ L⦃≤ 2⦄[X Fin (ℓ - ↑i.castSucc - 1 + 1)] := by
        rw! (castMode := .all) [h_count_eq]
        dsimp only [Fin.coe_castSucc, eq_mpr_eq_cast, curH_cast]
        rw [eqRec_eq_cast, cast_cast, cast_eq]
        exact h.property
      let res := hDegIn h_in_degLE
      exact res
    rw [mem_degreeLE] at h_deg_le_2 ⊢
    exact h_deg_le_2
  ⟩

end Preliminaries

noncomputable section       -- expands with 𝔽q in front
variable {r : ℕ} [NeZero r]
variable {L : Type} [Field L] [Fintype L] [DecidableEq L] [CharP L 2]
variable (𝔽q : Type) [Field 𝔽q] [Fintype 𝔽q] [DecidableEq 𝔽q]
  [h_Fq_char_prime : Fact (Nat.Prime (ringChar 𝔽q))] [hF₂ : Fact (Fintype.card 𝔽q = 2)]
variable [Algebra 𝔽q L]
variable (β : Fin r → L) [hβ_lin_indep : Fact (LinearIndependent 𝔽q β)]
  [h_β₀_eq_1 : Fact (β 0 = 1)]
variable {ℓ 𝓡 ϑ : ℕ} (γ_repetitions : ℕ) [NeZero ℓ] [NeZero 𝓡] [NeZero ϑ] -- Should we allow ℓ = 0?
variable {h_ℓ_add_R_rate : ℓ + 𝓡 < r} -- ℓ ∈ {1, ..., r-1}
variable {𝓑 : Fin 2 ↪ L}

section Essentials
-- In this section, we ue notation `ϑ` for the folding steps, along with `(hdiv : ϑ ∣ ℓ)`

/-- Oracle function type for round i.
f^(i) : S⁽ⁱ⁾ → L, where |S⁽ⁱ⁾| = 2^{ℓ + R - i} -/
abbrev OracleFunction (i : Fin (ℓ + 1)) : Type _ := sDomain 𝔽q β h_ℓ_add_R_rate ⟨i, by
  exact Nat.lt_of_le_of_lt (n := i) (k := r) (m := ℓ) (h₁ := by exact Fin.is_le i)
    (by exact lt_of_add_right_lt h_ℓ_add_R_rate)⟩ → L

omit [NeZero ℓ] in
lemma fin_ℓ_lt_ℓ_add_one (i : Fin ℓ) : i < ℓ + 1 :=
  Nat.lt_of_lt_of_le i.isLt (Nat.le_succ ℓ)

omit [NeZero ℓ] [NeZero r] [NeZero 𝓡] in
lemma fin_ℓ_lt_ℓ_add_R (i : Fin ℓ)
    : i.val < ℓ + 𝓡 := by omega

omit [NeZero ℓ] [NeZero r] [NeZero 𝓡] in
lemma fin_ℓ_lt_r {h_ℓ_add_R_rate : ℓ + 𝓡 < r} (i : Fin ℓ)
    : i.val < r := by omega

omit [NeZero ℓ] [NeZero r] [NeZero 𝓡] in
lemma fin_ℓ_add_one_lt_r {h_ℓ_add_R_rate : ℓ + 𝓡 < r} (i : Fin (ℓ + 1))
    : i.val < r := by omega

omit [NeZero ℓ] in
lemma fin_ℓ_steps_lt_ℓ_add_one (i : Fin ℓ) (steps : ℕ)
    (h : i.val + steps ≤ ℓ) : i.val + steps < ℓ + 1 :=
  Nat.lt_of_le_of_lt h (Nat.lt_succ_self ℓ)

omit [NeZero ℓ] in
lemma fin_ℓ_steps_lt_ℓ_add_R (i : Fin ℓ) (steps : ℕ) (h : i.val + steps ≤ ℓ)
    : i.val + steps < ℓ + 𝓡 := by
  apply Nat.lt_add_of_pos_right_of_le; omega

omit [NeZero ℓ] [NeZero r] [NeZero 𝓡] in
lemma fin_ℓ_steps_lt_r {h_ℓ_add_R_rate : ℓ + 𝓡 < r} (i : Fin ℓ) (steps : ℕ)
    (h : i.val + steps ≤ ℓ) : i.val + steps < r := by
  apply Nat.lt_of_le_of_lt (n := i + steps) (k := r) (m := ℓ) (h₁ := h)
    (by exact lt_of_add_right_lt h_ℓ_add_R_rate)

omit [NeZero ℓ] [NeZero r] [NeZero 𝓡] in
lemma ℓ_lt_r {h_ℓ_add_R_rate : ℓ + 𝓡 < r}
    : ℓ < r := by omega

omit [NeZero ℓ] [NeZero r] [NeZero 𝓡] in
lemma fin_r_succ_bound {h_ℓ_add_R_rate : ℓ + 𝓡 < r} (i : Fin r) (h_i : i + 1 < ℓ + 𝓡)
    : i + 1 < r := by omega

/-!
### The Fiber of the Quotient Map `qMap`

Utilities for constructing fibers and defining the fold operations used by Binary Basefold.
-/

def Fin2ToF2 (𝔽q : Type*) [Ring 𝔽q] (k : Fin 2) : 𝔽q :=
  if k = 0 then 0 else 1

/-! Standalone helper for the fiber coefficients used in `qMap_total_fiber`. -/
noncomputable def fiber_coeff
    (i : Fin r) (steps : ℕ)
    (j : Fin (ℓ + 𝓡 - i)) (elementIdx : Fin (2 ^ steps))
    (y_coeffs : Fin (ℓ + 𝓡 - (i + steps)) →₀ 𝔽q) : 𝔽q :=
  if hj : j.val < steps then
    if Nat.getBit (k := j) (n := elementIdx) = 0 then 0 else 1
  else y_coeffs ⟨j.val - steps, by -- ⊢ ↑j - steps < ℓ + 𝓡 - ↑⟨↑i + steps, ⋯⟩
    rw [←Nat.sub_sub]; -- ⊢ ↑j - steps < ℓ + 𝓡 - ↑i - steps
    apply Nat.sub_lt_sub_right;
    · exact Nat.le_of_not_lt hj
    · exact j.isLt⟩

/-- Get the full fiber list `(x₀, ..., x_{2 ^ steps-1})` which represents the
joined fiber `(q⁽ⁱ⁺steps⁻¹⁾ ∘ ⋯ ∘ q⁽ⁱ⁾)⁻¹({y}) ⊂ S⁽ⁱ⁾` over `y ∈ S^(i+steps)`,
in which the LSB repsents the FIRST qMap `q⁽ⁱ⁾`, and the MSB represents the LAST `q⁽ⁱ⁺steps⁻¹⁾`
-/
noncomputable def qMap_total_fiber
    -- S^i is source domain, S^{i + steps} is the target domain
      (i : Fin r) (steps : ℕ) (h_i_add_steps : i.val + steps < ℓ + 𝓡)
        (y : sDomain 𝔽q β h_ℓ_add_R_rate (i := ⟨i.val + steps, by omega⟩)) :
    Fin (2 ^ steps) → sDomain 𝔽q β h_ℓ_add_R_rate i :=
  if h_steps : steps = 0 then by
    -- Base case : 0 steps, the fiber is just the point y itself.
    subst h_steps
    simp only [add_zero, Fin.eta] at y
    exact fun _ => y
  else by
    -- fun (k : 𝔽q) =>
    let basis_y := sDomain_basis 𝔽q β h_ℓ_add_R_rate (i := ⟨i+steps,by omega⟩) (by omega)
    let y_coeffs : Fin (ℓ + 𝓡 - (↑i + steps)) →₀ 𝔽q := basis_y.repr y

    let basis_x := sDomain_basis 𝔽q β h_ℓ_add_R_rate ⟨i, by omega⟩ (by simp only; omega)
    exact fun elementIdx => by
      let x_coeffs : Fin (ℓ + 𝓡 - i) → 𝔽q := fun j =>
        if hj_lt_steps : j.val < steps then
          if Nat.getBit (k := j) (n := elementIdx) = 0 then (0 : 𝔽q)
          else (1 : 𝔽q)
        else
          y_coeffs ⟨j.val - steps, by
            rw [←Nat.sub_sub]; apply Nat.sub_lt_sub_right;
            · exact Nat.le_of_not_lt hj_lt_steps
            · exact j.isLt
          ⟩  -- Shift indices to match y's basis
      exact basis_x.repr.symm ((Finsupp.equivFunOnFinite).symm x_coeffs)

/- Note: state that the fiber of y is the set of all 2 ^ steps points in the
larger domain S⁽ⁱ⁾ that get mapped to y by the series of quotient maps q⁽ⁱ⁾, ..., q⁽ⁱ⁺steps⁻¹⁾. -/

omit [CharP L 2] [DecidableEq 𝔽q] hF₂ h_β₀_eq_1 [NeZero ℓ] in
/-- **qMap_fiber coefficient extraction**.
The coefficients of `x = qMap_total_fiber(y, k)` with respect to `basis_x` are exactly
the function that puts binary coeffs corresponding to bits of `k` in
the first `steps` positions, and shifts `y`'s coefficients.
This is the multi-step counterpart of `qMap_fiber_repr_coeff`.
-/
lemma qMap_total_fiber_repr_coeff (i : Fin ℓ) (steps : ℕ) (h_i_add_steps : i.val + steps ≤ ℓ)
    (y : sDomain 𝔽q β h_ℓ_add_R_rate (i := ⟨i.val + steps, by omega⟩))
    (k : Fin (2 ^ steps)) :
    let x := qMap_total_fiber 𝔽q β (i := ⟨i, by omega⟩)
      (steps := steps)
      (h_i_add_steps := by simp only; exact fin_ℓ_steps_lt_ℓ_add_R i steps h_i_add_steps) (y := y) k
    let basis_y := sDomain_basis 𝔽q β h_ℓ_add_R_rate (i := ⟨i.val + steps, by omega⟩)
      (h_i := by simp only; exact fin_ℓ_steps_lt_ℓ_add_R i steps h_i_add_steps)
    let y_coeffs := basis_y.repr y
    ∀ j, -- j refers to bit index of the fiber point x
      ((sDomain_basis 𝔽q β h_ℓ_add_R_rate (i := ⟨i, by omega⟩) (by simp only; omega)).repr x) j
      = fiber_coeff (i := i) (steps := steps) (j := j) (elementIdx := k)
        (y_coeffs := y_coeffs) := by
  unfold fiber_coeff
  simp only
  intro j
  -- have h_steps_ne_0 : steps ≠ 0 := by exact?
  by_cases h_steps_eq_0 : steps = 0
  · subst h_steps_eq_0
    simp only [qMap_total_fiber, ↓reduceDIte, Nat.add_zero, eq_mp_eq_cast, cast_eq, not_lt_zero',
      tsub_zero, Fin.eta]
  · simp only [qMap_total_fiber, h_steps_eq_0, ↓reduceDIte, Module.Basis.repr_symm_apply,
    Module.Basis.repr_linearCombination, Finsupp.equivFunOnFinite_symm_apply_apply]

/-- `b` and `2 ^ n * c` have disjoint bit supports when `b < 2 ^ n`: low `n` bits live in
`b`, bits `≥ n` live in `2 ^ n * c`. -/
lemma and_lt_two_pow_mul_eq_zero {n c b : ℕ} (hb : b < 2 ^ n) :
    b &&& (2 ^ n * c) = 0 := by
  apply Nat.and_eq_zero_iff_and_each_getBit_eq_zero.mpr
  intro k
  rw [Nat.getBit_of_multiple_of_power_of_two]
  by_cases hk : k < n
  · simp only [hk, ↓reduceIte, Nat.and_zero]
  · -- `k ≥ n` ⇒ bit `k` of `b` is `0` since `b < 2 ^ n`.
    have h_b_bit : Nat.getBit k b = 0 := by
      simp only [Nat.getBit, Nat.shiftRight_eq_div_pow, Nat.and_one_is_mod]
      rw [Nat.div_eq_of_lt (Nat.lt_of_lt_of_le hb (Nat.pow_le_pow_right (by omega)
        (Nat.le_of_not_lt hk)))]
    simp only [hk, ↓reduceIte, h_b_bit, Nat.zero_and]

/-- Low-bit decomposition: for `b < 2 ^ n`, `c < 2`, the low `n` bits of `c * 2 ^ n + b`
are exactly the bits of `b`. -/
lemma getBit_low_of_add_mul_two_pow {n c b j : ℕ} (hb : b < 2 ^ n) (hj : j < n) :
    Nat.getBit j (c * 2 ^ n + b) = Nat.getBit j b := by
  -- `b` and `c * 2 ^ n` have disjoint bit supports below `n`, so bits agree there.
  have h_and : (2 ^ n * c) &&& b = 0 := by
    rw [Nat.and_comm]; exact and_lt_two_pow_mul_eq_zero hb
  rw [Nat.mul_comm c (2 ^ n)]
  rw [Nat.getBit_of_add_distrib (h_n_AND_m := h_and)]
  rw [Nat.getBit_of_multiple_of_power_of_two]
  simp only [hj, ↓reduceIte, Nat.zero_add]

/-- High-bit decomposition: for `b < 2 ^ n`, `c < 2`, bit `n` of `c * 2 ^ n + b` is `c`. -/
lemma getBit_high_of_add_mul_two_pow {n c b : ℕ} (hb : b < 2 ^ n) (hc : c < 2) :
    Nat.getBit n (c * 2 ^ n + b) = c := by
  have h_and : (2 ^ n * c) &&& b = 0 := by
    rw [Nat.and_comm]; exact and_lt_two_pow_mul_eq_zero hb
  rw [Nat.mul_comm c (2 ^ n)]
  rw [Nat.getBit_of_add_distrib (h_n_AND_m := h_and)]
  rw [Nat.getBit_of_multiple_of_power_of_two]
  simp only [lt_irrefl, ↓reduceIte, Nat.sub_self]
  -- bit `n` of `b` is `0` since `b < 2 ^ n`; bit `0` of `c` is `c` since `c < 2`.
  have h_b_bit : Nat.getBit n b = 0 := by
    simp only [Nat.getBit, Nat.shiftRight_eq_div_pow, Nat.and_one_is_mod]
    rw [Nat.div_eq_of_lt hb]
  rw [h_b_bit, add_zero]
  simp only [Nat.getBit, Nat.shiftRight_zero, Nat.and_one_is_mod]
  omega

omit [CharP L 2] hF₂ h_β₀_eq_1 [NeZero ℓ] in
/-- **Fiber composition (last level peeled).**
The `(n+1)`-step fiber of `y' ∈ S^(i+(n+1))` at index `idx`, with `idx` split into the
high bit `c := idx / 2^n` (selecting the last quotient `q^(i+n)`) and the low `n` bits
`b := idx % 2^n`, equals the `n`-step fiber of the single-step preimage
`z_c := qMap_total_fiber(i+n, 1, y')(c)` at index `b`. This is the geometric fact pinning
the recursive `foldMatrixNat` construction. -/
lemma qMap_total_fiber_succ_peel_last (i : Fin ℓ) (n : ℕ) (h_i_add_steps : i.val + (n + 1) ≤ ℓ)
    (y' : sDomain 𝔽q β h_ℓ_add_R_rate (i := ⟨i.val + (n + 1), by omega⟩))
    (idx : Fin (2 ^ (n + 1))) :
    qMap_total_fiber 𝔽q β (i := ⟨i, by omega⟩) (steps := n + 1)
      (h_i_add_steps := by simp only; exact fin_ℓ_steps_lt_ℓ_add_R i (n + 1) h_i_add_steps)
      (y := y') idx =
    qMap_total_fiber 𝔽q β (i := ⟨i, by omega⟩) (steps := n)
      (h_i_add_steps := by simp only; exact fin_ℓ_steps_lt_ℓ_add_R i n (by omega))
      (y := qMap_total_fiber 𝔽q β (i := ⟨i.val + n, by omega⟩) (steps := 1)
        (h_i_add_steps := by
          simp only
          exact Nat.lt_of_le_of_lt (by omega)
            (Nat.lt_add_of_pos_right (Nat.pos_of_ne_zero (NeZero.ne 𝓡))))
        (y := ⟨y'.val, by have := y'.property; simpa only [Nat.add_assoc] using this⟩)
        ⟨idx.val / 2 ^ n, by
          have hb : idx.val < 2 ^ n * 2 := Nat.lt_of_lt_of_eq idx.isLt (by rw [pow_succ])
          exact Nat.div_lt_of_lt_mul hb⟩)
      ⟨idx.val % 2 ^ n, Nat.mod_lt _ (Nat.two_pow_pos n)⟩ := by
  -- Both points live in `S^i`; compare their `basis_x` coefficients via `repr` injectivity.
  set c : Fin 2 := ⟨idx.val / 2 ^ n, by
    have hb : idx.val < 2 ^ n * 2 := Nat.lt_of_lt_of_eq idx.isLt (by rw [pow_succ])
    exact Nat.div_lt_of_lt_mul hb⟩ with hc_def
  set b : Fin (2 ^ n) := ⟨idx.val % 2 ^ n, Nat.mod_lt _ (Nat.two_pow_pos n)⟩ with hb_def
  have h𝓡 : 0 < 𝓡 := Nat.pos_of_ne_zero (NeZero.ne 𝓡)
  have h_z_bound : (⟨i.val + n, by omega⟩ : Fin r).val + 1 < ℓ + 𝓡 := by simp only; omega
  let y'_lift : sDomain 𝔽q β h_ℓ_add_R_rate (i := ⟨(⟨i.val + n, by omega⟩ : Fin r).val + 1, by
    omega⟩) := ⟨y'.val, by have := y'.property; simpa only [Nat.add_assoc] using this⟩
  -- `idx = c * 2^n + b` as naturals.
  have h_idx_split : idx.val = c.val * 2 ^ n + b.val := by
    simp only [hc_def, hb_def]
    exact (Nat.div_add_mod' idx.val (2 ^ n)).symm
  apply (sDomain_basis 𝔽q β h_ℓ_add_R_rate (i := ⟨i, by omega⟩)
    (by simp only; omega)).repr.injective
  ext j
  -- LHS coefficient via the `(n+1)`-step extraction lemma.
  have hL := qMap_total_fiber_repr_coeff 𝔽q β i (steps := n + 1) (by omega) y' idx (j := j)
  -- RHS coefficient via the `n`-step extraction lemma over `z_c`.
  set zc := qMap_total_fiber 𝔽q β (i := ⟨i.val + n, by omega⟩) (steps := 1)
    (h_i_add_steps := h_z_bound)
    (y := y'_lift) c with hzc_def
  have hR := qMap_total_fiber_repr_coeff 𝔽q β i (steps := n) (by omega) zc b (j := j)
  simp only at hL hR ⊢
  rw [hL, hR]
  -- Now compare the two `fiber_coeff` values bit-by-bit, using the bit decomposition of `idx`.
  unfold fiber_coeff
  by_cases hj_lt_n : j.val < n
  · -- Low region: both pick up bit `j` of `idx`, which equals bit `j` of `b`.
    have hjn1 : j.val < n + 1 := by omega
    simp only [hj_lt_n, hjn1, ↓reduceDIte]
    rw [h_idx_split, getBit_low_of_add_mul_two_pow b.isLt hj_lt_n]
  · by_cases hj_eq_n : j.val = n
    · -- Boundary: LHS picks up bit `n` of `idx` (= `c`); RHS reads the `0`-th coeff of `z_c`,
      -- which is bit `0` of `c`.
      have hjn1 : j.val < n + 1 := by omega
      have hjn_not : ¬ j.val < n := by omega
      simp only [hjn1, hjn_not, ↓reduceDIte]
      rw [h_idx_split]
      have h_getbit : Nat.getBit j.val (c.val * 2 ^ n + b.val) = c.val := by
        simpa [hj_eq_n] using getBit_high_of_add_mul_two_pow b.isLt c.isLt
      rw [h_getbit]
      -- RHS: `(j - n)`-th coeff of `z_c`'s `basis_y` repr; with `j = n` this is its `0`-th coeff.
      have hRc := qMap_total_fiber_repr_coeff 𝔽q β (⟨i.val + n, by omega⟩ : Fin ℓ) (steps := 1)
        (by simp only; omega)
        (⟨y'.val, by have := y'.property; simpa only [Nat.add_assoc] using this⟩) c
        (j := ⟨j.val - n, by
          have hj_ge_n : n ≤ j.val := Nat.le_of_not_lt hjn_not
          have hsub : j.val - n < (ℓ + 𝓡 - i.val) - n :=
            Nat.sub_lt_sub_right hj_ge_n j.isLt
          simp only
          omega⟩)
      rw [← hzc_def] at hRc
      have hj_sub : j.val - n = 0 := by omega
      have h_c_bit : Nat.getBit 0 c.val = c.val := by
        simp only [Nat.getBit, Nat.shiftRight_zero, Nat.and_one_is_mod]
        omega
      simp only [fiber_coeff, hj_sub, zero_lt_one, ↓reduceDIte, h_c_bit] at hRc
      simpa [hj_sub] using hRc.symm
    · -- High region (`j > n`): both read `y'`'s shifted coefficients; indices agree.
      have hjn1_not : ¬ j.val < n + 1 := by omega
      have hjn_not : ¬ j.val < n := by omega
      simp only [hjn1_not, hjn_not, ↓reduceDIte]
      have hRc := qMap_total_fiber_repr_coeff 𝔽q β (⟨i.val + n, by omega⟩ : Fin ℓ) (steps := 1)
        (by simp only; omega)
        (⟨y'.val, by have := y'.property; simpa only [Nat.add_assoc] using this⟩) c
        (j := ⟨j.val - n, by
          have hj_ge_n : n ≤ j.val := Nat.le_of_not_lt hjn_not
          have hsub : j.val - n < (ℓ + 𝓡 - i.val) - n :=
            Nat.sub_lt_sub_right hj_ge_n j.isLt
          simp only
          omega⟩)
      rw [← hzc_def] at hRc
      have hj_sub_not : ¬ j.val - n < 1 := by omega
      simp only [fiber_coeff, hj_sub_not, ↓reduceDIte] at hRc
      convert hRc.symm using 1 <;> omega

def pointToIterateQuotientIndex (i : Fin (ℓ + 1)) (steps : ℕ) (h_i_add_steps : i.val + steps ≤ ℓ)
    (x : sDomain 𝔽q β h_ℓ_add_R_rate (i := ⟨i, by omega⟩)) : Fin (2 ^ steps) := by
  let basis_x := sDomain_basis 𝔽q β h_ℓ_add_R_rate ⟨i, by omega⟩
    (by apply Nat.lt_add_of_pos_right_of_le; simp only; omega)
  let x_coeffs := basis_x.repr x
  let k_bits : Fin steps → Nat := fun j =>
    if x_coeffs ⟨j, by simp only; omega⟩ = 0 then 0 else 1
  let k := Nat.binaryFinMapToNat (n := steps) (m := k_bits) (h_binary := by
    intro j; simp only [k_bits]; split_ifs
    · norm_num
    · norm_num
  )
  exact k

omit [CharP L 2] [DecidableEq 𝔽q] hF₂ h_β₀_eq_1 [NeZero ℓ] in
/-- When ϑ = 1, qMap_total_fiber maps k = 0 to an element with first coefficient 0
and k = 1 to an element with first coefficient 1. -/
lemma qMap_total_fiber_one_level_eq (i : Fin ℓ) (h_i_add_1 : i.val + 1 ≤ ℓ)
    (y : sDomain 𝔽q β h_ℓ_add_R_rate (i := ⟨i + 1, by omega⟩)) (k : Fin 2) :
    let basis_x := sDomain_basis 𝔽q β h_ℓ_add_R_rate ⟨i, by omega⟩ (by simp only; omega)
    let x : sDomain 𝔽q β h_ℓ_add_R_rate ⟨i, by omega⟩ := qMap_total_fiber 𝔽q β (i := ⟨i, by omega⟩)
      (steps := 1) (h_i_add_steps := by apply Nat.lt_add_of_pos_right_of_le; omega) (y := y) k
    let y_lifted : sDomain 𝔽q β h_ℓ_add_R_rate ⟨i, by omega⟩ := sDomain.lift 𝔽q β h_ℓ_add_R_rate
      (i := ⟨i, by omega⟩) (j := ⟨i.val + 1, by omega⟩)
      (h_j := by apply Nat.lt_add_of_pos_right_of_le; omega)
      (h_le := by apply Fin.mk_le_mk.mpr (by omega)) y
    let free_coeff_term : sDomain 𝔽q β h_ℓ_add_R_rate ⟨i, by omega⟩ :=
      (Fin2ToF2 𝔽q k) • (basis_x ⟨0, by simp only; omega⟩)
    x = free_coeff_term + y_lifted
    := by
  let basis_x := sDomain_basis 𝔽q β h_ℓ_add_R_rate ⟨i, by omega⟩ (by simp only; omega)
  apply basis_x.repr.injective
  simp only [map_add, map_smul]
  simp only [Module.Basis.repr_self, Finsupp.smul_single, smul_eq_mul, mul_one, basis_x]
  ext j
  have h_repr_x := qMap_total_fiber_repr_coeff 𝔽q β i (steps := 1) (by omega)
    (y := y) (k := k) (j := j)
  simp only [h_repr_x, Finsupp.coe_add, Pi.add_apply]
  simp only [fiber_coeff, lt_one_iff, reducePow, Fin2ToF2, Fin.isValue]

  by_cases hj : j = ⟨0, by omega⟩
  · simp only [hj, ↓reduceDIte, Fin.isValue, Finsupp.single_eq_same]
    by_cases hk : k = 0
    · simp only [getBit, hk, Fin.isValue, Fin.coe_ofNat_eq_mod, zero_mod, shiftRight_zero,
      and_one_is_mod, ↓reduceIte, zero_add]
      -- => Now use basis_repr_of_sDomain_lift
      simp only [basis_repr_of_sDomain_lift, add_tsub_cancel_left, zero_lt_one, ↓reduceDIte]
    · have h_k_eq_1 : k = 1 := by omega
      simp only [getBit, h_k_eq_1, Fin.isValue, Fin.coe_ofNat_eq_mod, mod_succ, shiftRight_zero,
        Nat.and_self, one_ne_zero, ↓reduceIte, left_eq_add]
      simp only [basis_repr_of_sDomain_lift, add_tsub_cancel_left, zero_lt_one, ↓reduceDIte]
  · have hj_ne_zero : j ≠ ⟨0, by omega⟩ := by omega
    have hj_val_ne_zero : j.val ≠ 0 := by
      change j.val ≠ ((⟨0, by omega⟩ :  Fin (ℓ + 𝓡 - ↑i)).val)
      apply Fin.val_ne_of_ne
      exact hj_ne_zero
    simp only [hj_val_ne_zero, ↓reduceDIte, Finsupp.single, Fin.isValue, ite_eq_left_iff,
      one_ne_zero, imp_false, Decidable.not_not, Pi.single, Finsupp.coe_mk, Function.update,
      hj_ne_zero, Pi.zero_apply, zero_add]
    simp only [basis_repr_of_sDomain_lift, add_tsub_cancel_left, lt_one_iff, right_eq_dite_iff]
    intro hj_eq_zero
    exact False.elim (hj_val_ne_zero hj_eq_zero)

omit [CharP L 2] [DecidableEq 𝔽q] hF₂ [NeZero ℓ] in
/-- `x` is in the fiber of `y` under `qMap_total_fiber` iff `y` is the iterated
quotient of `x`. That is, for binary field, the fiber of `y` is exactly the set of
all `x` that map to `y` under the iterated quotient map. -/
theorem generates_quotient_point_if_is_fiber_of_y
    (i : Fin ℓ) (steps : ℕ) (h_i_add_steps : i.val + steps ≤ ℓ)
    (x : sDomain 𝔽q β h_ℓ_add_R_rate (i := ⟨i, by omega⟩))
    (y : sDomain 𝔽q β h_ℓ_add_R_rate (i := ⟨i.val + steps, by omega⟩))
    (hx_is_fiber : ∃ (k : Fin (2 ^ steps)), x = qMap_total_fiber 𝔽q β (i := ⟨i, by omega⟩)
      (steps := steps) (h_i_add_steps := by
        simp only; exact fin_ℓ_steps_lt_ℓ_add_R i steps h_i_add_steps) (y := y) k) :
    y = iteratedQuotientMap 𝔽q β h_ℓ_add_R_rate i (k := steps) (h_bound := h_i_add_steps) x := by
 -- Get the fiber index `k` and the equality from the hypothesis.
  rcases hx_is_fiber with ⟨k, hx_eq⟩
  let basis_y := sDomain_basis 𝔽q β h_ℓ_add_R_rate
    (i := ⟨i.val + steps, by omega⟩) (h_i := by apply Nat.lt_add_of_pos_right_of_le; omega)
  apply basis_y.repr.injective
  ext j
  conv_rhs =>
    rw [getSDomainBasisCoeff_of_iteratedQuotientMap]
  have h_repr_x := qMap_total_fiber_repr_coeff 𝔽q β i (steps := steps)
    (h_i_add_steps := by omega) (y := y) (k := k) (j := ⟨j + steps, by simp only; omega⟩)
  simp only at h_repr_x
  rw [←hx_eq] at h_repr_x
  simp only [fiber_coeff, add_lt_iff_neg_right, not_lt_zero', ↓reduceDIte, add_tsub_cancel_right,
    Fin.eta] at h_repr_x
  exact h_repr_x.symm

omit [CharP L 2] [NeZero ℓ] in
/-- State the corrrespondence between the forward qMap and the backward qMap_total_fiber -/
theorem is_fiber_iff_generates_quotient_point (i : Fin ℓ) (steps : ℕ)
    (h_i_add_steps : i.val + steps ≤ ℓ)
    (x : sDomain 𝔽q β h_ℓ_add_R_rate (i := ⟨i, by omega⟩))
    (y : sDomain 𝔽q β h_ℓ_add_R_rate (i := ⟨i.val + steps, by omega⟩)) :
    let qMapFiber := qMap_total_fiber 𝔽q β (i := ⟨i, by omega⟩) (steps := steps)
      (h_i_add_steps := by simp only; exact fin_ℓ_steps_lt_ℓ_add_R i steps h_i_add_steps) (y := y)
    let k := pointToIterateQuotientIndex (i := ⟨i, by omega⟩) (steps := steps)
      (h_i_add_steps := h_i_add_steps) (x := x)
    y = iteratedQuotientMap 𝔽q β h_ℓ_add_R_rate i (k := steps) (h_bound := h_i_add_steps) x ↔
    qMapFiber k = x := by
  let basis_x := sDomain_basis 𝔽q β h_ℓ_add_R_rate ⟨i, by omega⟩
    (by simp only; omega)
  let basis_y := sDomain_basis 𝔽q β h_ℓ_add_R_rate ⟨i.val + steps, by omega⟩
    (h_i := by apply Nat.lt_add_of_pos_right_of_le; omega)
  simp only
  set k := pointToIterateQuotientIndex (i := ⟨i, by omega⟩) (steps := steps)
    (h_i_add_steps := h_i_add_steps) (x := x)
  constructor
  · intro h_x_generates_y
    -- ⊢ qMap_total_fiber ...` ⟨↑i, ⋯⟩ steps ⋯ y k = x
    -- We prove that `qMap_total_fiber` with this `k` reconstructs `x` via basis repr
    apply basis_x.repr.injective
    ext j
    let reConstructedX := basis_x.repr (qMap_total_fiber 𝔽q β (i := ⟨i, by omega⟩)
      (steps := steps) (h_i_add_steps := by apply Nat.lt_add_of_pos_right_of_le; omega) (y := y) k)
    have h_repr_of_reConstructedX := qMap_total_fiber_repr_coeff 𝔽q β i (steps := steps)
      (h_i_add_steps := by omega) (y := y) (k := k) (j := j)
    simp only at h_repr_of_reConstructedX
    -- ⊢ repr of reConstructedX at j = repr of x at j
    rw [h_repr_of_reConstructedX]; dsimp [k, pointToIterateQuotientIndex, fiber_coeff];
    rw [getBit_of_binaryFinMapToNat]; simp only [Fin.eta, dite_eq_right_iff, ite_eq_left_iff,
      one_ne_zero, imp_false, Decidable.not_not]
    -- Now we only need to do case analysis
    by_cases h_j : j.val < steps
    · -- Case 1 : The first `steps` coefficients, determined by `k`.
      simp only [h_j, ↓reduceDIte, forall_const]
      by_cases h_coeff_j_of_x : basis_x.repr x j = 0
      · simp only [basis_x, h_coeff_j_of_x, ↓reduceIte];
      · simp only [basis_x, h_coeff_j_of_x, ↓reduceIte];
        have h_coeff := 𝔽q_element_eq_zero_or_eq_one 𝔽q (c := basis_x.repr x j)
        simp only [h_coeff_j_of_x, false_or] at h_coeff
        exact id (Eq.symm h_coeff)
    · -- Case 2 : The remaining coefficients, determined by `y`.
      simp only [h_j, ↓reduceDIte]
      simp only [basis_x]
      -- ⊢ Here we compare coeffs, not the basis elements
      simp only [h_x_generates_y]
      have h_res := getSDomainBasisCoeff_of_iteratedQuotientMap 𝔽q β h_ℓ_add_R_rate i (k := steps)
        (h_bound := by omega) x (j := ⟨j - steps, by -- Note: make this index bound proof cleaner
          simp only; rw [←Nat.sub_sub]; -- ⊢ ↑j - steps < ℓ + 𝓡 - ↑i - steps
          apply Nat.sub_lt_sub_right;
          · exact Nat.le_of_not_lt h_j
          · exact j.isLt
        ⟩) -- ⊢ ↑j - steps < ℓ + 𝓡 - (↑i + steps)
      have h_j_sub_add_steps : j - steps + steps = j := by omega
      simp only at h_res
      simp only [h_j_sub_add_steps, Fin.eta] at h_res
      exact h_res
  · intro h_x_is_fiber_of_y
    -- y is the quotient point of x over steps steps
    apply generates_quotient_point_if_is_fiber_of_y (h_i_add_steps := h_i_add_steps)
      (x := x) (y := y) (hx_is_fiber := by use k; exact h_x_is_fiber_of_y.symm)

omit [CharP L 2] hF₂ h_β₀_eq_1 [NeZero ℓ] in
/-- the pointToIterateQuotientIndex of qMap_total_fiber -/
lemma pointToIterateQuotientIndex_qMap_total_fiber_eq_self (i : Fin ℓ) (steps : ℕ)
    (h_i_add_steps : i.val + steps ≤ ℓ)
    (y : (sDomain 𝔽q β h_ℓ_add_R_rate) (i := ⟨i + steps, by omega⟩)) (k : Fin (2 ^ steps)) :
    pointToIterateQuotientIndex (i := ⟨i, by omega⟩) (steps := steps) (h_i_add_steps := by omega)
      (x := ((qMap_total_fiber 𝔽q β (i := ⟨i, by omega⟩) (steps := steps)
        (h_i_add_steps := by apply Nat.lt_add_of_pos_right_of_le; omega) (y := y) k):
          sDomain 𝔽q β h_ℓ_add_R_rate (i := ⟨i, by omega⟩))) = k := by
  apply Fin.eq_mk_iff_val_eq.mpr
  apply eq_iff_eq_all_getBits.mpr
  intro j -- bit index j
  simp only [pointToIterateQuotientIndex, qMap_total_fiber]
  rw [Nat.getBit_of_binaryFinMapToNat]
  simp only [Nat.add_zero, Nat.pow_zero, eq_mp_eq_cast, cast_eq, Module.Basis.repr_symm_apply]
  by_cases h_j : j < steps
  · simp only [h_j, ↓reduceDIte];
    by_cases hsteps : steps = 0
    · simp only [hsteps, ↓reduceDIte, eqRec_eq_cast, Nat.add_zero, Nat.pow_zero]
      omega
    · simp only [hsteps, ↓reduceDIte, Module.Basis.repr_linearCombination,
      Finsupp.equivFunOnFinite_symm_apply_apply, h_j, ite_eq_left_iff, one_ne_zero,
      imp_false, Decidable.not_not]
      -- ⊢ (if j.getBit ↑k = 0 then 0 else 1) = j.getBit ↑k
      have h := Nat.getBit_eq_zero_or_one (k := j) (n := k)
      by_cases h_j_getBit_k_eq_0 : j.getBit ↑k = 0
      · simp only [h_j_getBit_k_eq_0, ↓reduceIte]
      · simp only [h_j_getBit_k_eq_0, false_or, ↓reduceIte] at h ⊢
        exact id (Eq.symm h)
  · rw [Nat.getBit_of_lt_two_pow];
    simp only [h_j, ↓reduceDIte, ↓reduceIte];

omit [CharP L 2] [DecidableEq 𝔽q] hF₂ h_β₀_eq_1 [NeZero ℓ] in
/-- **qMap_fiber coefficient extraction** -/
lemma qMap_total_fiber_basis_sum_repr (i : Fin ℓ) (steps : ℕ) (h_i_add_steps : i.val + steps ≤ ℓ)
    (y : (sDomain 𝔽q β h_ℓ_add_R_rate) (i := ⟨i + steps, by omega⟩))
    (k : Fin (2 ^ steps)) :
    let x : sDomain 𝔽q β h_ℓ_add_R_rate (i := ⟨i, by omega⟩) := qMap_total_fiber 𝔽q β
      (i := ⟨i, by omega⟩) (steps := steps) (h_i_add_steps := by
        apply Nat.lt_add_of_pos_right_of_le; omega) (y := y) (k)
    let basis_x := sDomain_basis 𝔽q β h_ℓ_add_R_rate ⟨i, by omega⟩
      (by simp only; apply Nat.lt_add_of_pos_right_of_le; omega)
    let basis_y := sDomain_basis 𝔽q β h_ℓ_add_R_rate ⟨i + steps, by omega⟩
      (h_i := by apply Nat.lt_add_of_pos_right_of_le; omega)
    let y_coeffs := basis_y.repr y
    x = ∑ j : Fin (ℓ + 𝓡 - i), (
      fiber_coeff (i := i) (steps := steps) (j := j) (elementIdx := k) (y_coeffs := y_coeffs)
    ) • (basis_x j)
     := by
    set basis_x := sDomain_basis 𝔽q β h_ℓ_add_R_rate ⟨i, by omega⟩ (by
      simp only; apply Nat.lt_add_of_pos_right_of_le; omega)
    set basis_y := sDomain_basis 𝔽q β h_ℓ_add_R_rate ⟨i + steps, by omega⟩
      (h_i := by apply Nat.lt_add_of_pos_right_of_le; omega)
    set y_coeffs := basis_y.repr y
    -- Let `x` be the element from the fiber for brevity.
    set x := qMap_total_fiber 𝔽q β (i := ⟨i, by omega⟩) (steps := steps)
      (h_i_add_steps := by apply Nat.lt_add_of_pos_right_of_le; omega) (y := y) (k)
    simp only;
    -- Express `(x:L)` using its basis representation, which is built from `x_coeffs_fn`.
    set x_coeffs_fn := fun j : Fin (ℓ + 𝓡 - i) =>
      fiber_coeff (i := i) (steps := steps) (j := j) (elementIdx := k) (y_coeffs := y_coeffs)
    have hx_val_sum : (x : L) = ∑ j, (x_coeffs_fn j) • (basis_x j) := by
      rw [←basis_x.sum_repr x]
      rw [Submodule.coe_sum, Submodule.coe_sum]
      congr; funext j;
      simp_rw [Submodule.coe_smul]
      congr; unfold x_coeffs_fn
      have h := qMap_total_fiber_repr_coeff 𝔽q β (i := ⟨i, by omega⟩) (steps := steps)
        (h_i_add_steps := by omega) (y := y) (k := k) (j := j)
      rw [h]
    apply Subtype.ext -- convert to equality in Subtype embedding
    rw [hx_val_sum]

omit [CharP L 2] [DecidableEq 𝔽q] hF₂ h_β₀_eq_1 [NeZero ℓ] in
theorem card_qMap_total_fiber (i : Fin ℓ) (steps : ℕ) (h_i_add_steps : i.val + steps ≤ ℓ)
    (y : sDomain 𝔽q β h_ℓ_add_R_rate (i := ⟨i.val + steps, by omega⟩)) :
    Fintype.card (Set.image (qMap_total_fiber 𝔽q β (i := ⟨i, by omega⟩) (steps := steps)
      (h_i_add_steps := by simp only; exact fin_ℓ_steps_lt_ℓ_add_R i steps h_i_add_steps)
      (y := y)) Set.univ) = 2 ^ steps := by
  -- The cardinality of the image of a function equals the cardinality of its domain
  -- if it is injective.
  rw [Set.card_image_of_injective Set.univ]
  -- The domain is `Fin (2 ^ steps)`, which has cardinality `2 ^ steps`.
  · -- ⊢ Fintype.card ↑Set.univ = 2 ^ steps
    simp only [Fintype.card_setUniv, Fintype.card_fin]
  · -- prove that `qMap_total_fiber` is an injective function.
    intro k₁ k₂ h_eq
    -- Assume two indices `k₁` and `k₂` produce the same point `x`.
    let basis_x := sDomain_basis 𝔽q β h_ℓ_add_R_rate ⟨i, by omega⟩ (by simp only; omega)
    -- If the points are equal, their basis representations must be equal.
    set fiberMap := qMap_total_fiber 𝔽q β (i := ⟨i, by omega⟩) (steps := steps)
      (h_i_add_steps := by apply Nat.lt_add_of_pos_right_of_le; omega) (y := y)
    have h_coeffs_eq : basis_x.repr (fiberMap k₁) = basis_x.repr (fiberMap k₂) := by
      rw [h_eq]
    -- The first `steps` coefficients are determined by the bits of `k₁` and `k₂`.
    -- If the coefficients are equal, the bits must be equal.
    have h_bits_eq : ∀ j : Fin steps,
        Nat.getBit (k := j) (n := k₁.val) = Nat.getBit (k := j) (n := k₂.val) := by
      intro j
      have h_coeff_j_eq : basis_x.repr (fiberMap k₁) ⟨j, by simp only; omega⟩
        = basis_x.repr (fiberMap k₂) ⟨j, by simp only; omega⟩ := by rw [h_coeffs_eq]
      rw [qMap_total_fiber_repr_coeff 𝔽q β (i := ⟨i, by omega⟩) (steps := steps)
        (h_i_add_steps := h_i_add_steps) (y := y) (j := ⟨j, by simp only; omega⟩)]
        at h_coeff_j_eq
      rw [qMap_total_fiber_repr_coeff 𝔽q β (i := ⟨i, by omega⟩) (steps := steps)
        (h_i_add_steps := h_i_add_steps) (y := y) (k := k₂) (j := ⟨j, by simp only; omega⟩)]
        at h_coeff_j_eq
      simp only [fiber_coeff, Fin.is_lt, ↓reduceDIte] at h_coeff_j_eq
      by_cases hbitj_k₁ : Nat.getBit (k := j) (n := k₁.val) = 0
      · simp only [hbitj_k₁, ↓reduceIte, left_eq_ite_iff, zero_ne_one, imp_false,
        Decidable.not_not] at ⊢ h_coeff_j_eq
        simp only [h_coeff_j_eq]
      · simp only [hbitj_k₁, ↓reduceIte, right_eq_ite_iff, one_ne_zero,
        imp_false] at ⊢ h_coeff_j_eq
        have b1 : Nat.getBit (k := j) (n := k₁.val) = 1 := by
          have h := Nat.getBit_eq_zero_or_one (k := j) (n := k₁.val)
          simp only [hbitj_k₁, false_or] at h
          exact h
        have b2 : Nat.getBit (k := j) (n := k₂.val) = 1 := by
          have h := Nat.getBit_eq_zero_or_one (k := j) (n := k₂.val)
          simp only [h_coeff_j_eq, false_or] at h
          exact h
        simp only [b1, b2]
      -- Extract the j-th coefficient from h_coeffs_eq and show it implies the bits are equal.
    -- If all the bits of two numbers are equal, the numbers themselves are equal.
    apply Fin.eq_of_val_eq
    -- ⊢ ∀ {n : ℕ} {i j : Fin n}, ↑i = ↑j → i = j
    apply eq_iff_eq_all_getBits.mpr
    intro k
    by_cases h_k : k < steps
    · simp only [h_bits_eq ⟨k, by omega⟩]
    · -- The bits at positions ≥ steps must be deterministic
      conv_lhs => rw [Nat.getBit_of_lt_two_pow]
      conv_rhs => rw [Nat.getBit_of_lt_two_pow]
      simp only [h_k, ↓reduceIte]
omit [CharP L 2] [NeZero ℓ] in
/-- The images of `qMap_total_fiber` over distinct quotient points `y₁ ≠ y₂` are
disjoint -/
theorem qMap_total_fiber_disjoint
  (i : Fin ℓ) (steps : ℕ) (h_i_add_steps : i + steps ≤ ℓ)
  {y₁ y₂ : sDomain 𝔽q β h_ℓ_add_R_rate ⟨i.val + steps, by omega⟩}
  (hy_ne : y₁ ≠ y₂) :
  Disjoint
    ((qMap_total_fiber 𝔽q β (i := ⟨i, by omega⟩) (steps := steps)
      (h_i_add_steps := fin_ℓ_steps_lt_ℓ_add_R i steps h_i_add_steps) y₁ '' Set.univ).toFinset)
    ((qMap_total_fiber 𝔽q β (i := ⟨i, by omega⟩) (steps := steps)
      (h_i_add_steps := fin_ℓ_steps_lt_ℓ_add_R i steps h_i_add_steps) y₂ '' Set.univ).toFinset)
    := by
 -- Proof by contradiction. Assume the intersection is non-empty.
  rw [Finset.disjoint_iff_inter_eq_empty]
  by_contra h_nonempty
  -- Let `x` be an element in the intersection of the two fiber sets.
  obtain ⟨x, h_x_mem_inter⟩ := Finset.nonempty_of_ne_empty h_nonempty
  have hx₁ := Finset.mem_of_mem_inter_left h_x_mem_inter
  have hx₂ := Finset.mem_of_mem_inter_right h_x_mem_inter
  -- A helper lemma : applying the forward map to a point in a generated fiber returns
  -- the original quotient point.
  have iteratedQuotientMap_of_qMap_total_fiber_eq_self
    (y : sDomain 𝔽q β h_ℓ_add_R_rate ⟨i.val + steps, by omega⟩)
    (k : Fin (2 ^ steps)) :
    iteratedQuotientMap 𝔽q β h_ℓ_add_R_rate (i := ⟨i, by omega⟩) (k := steps)
      (h_bound := by omega)
      (qMap_total_fiber 𝔽q β (i := ⟨i, by omega⟩) (steps := steps)
        (h_i_add_steps := by apply Nat.lt_add_of_pos_right_of_le; omega) (y := y) k) = y := by
      have h := generates_quotient_point_if_is_fiber_of_y
        (h_i_add_steps := h_i_add_steps) (x:=
        ((qMap_total_fiber 𝔽q β (i := ⟨i, by omega⟩) (steps := steps)
          (h_i_add_steps := by apply Nat.lt_add_of_pos_right_of_le; omega) (y := y) k) :
          sDomain 𝔽q β h_ℓ_add_R_rate (i := ⟨i, by omega⟩))
      ) (y := y) (hx_is_fiber := by use k)
      exact h.symm
  have h_exists_k₁ : ∃ k, x = qMap_total_fiber 𝔽q β (i := ⟨i, by omega⟩) (steps := steps)
      (h_i_add_steps := by apply Nat.lt_add_of_pos_right_of_le; omega) y₁ k := by
    -- convert (x ∈ Finset of the image of the fiber) to statement
    -- about membership in the Set.
    rw [Set.mem_toFinset] at hx₁
    rw [Set.mem_image] at hx₁ -- Set.mem_image gives us t an index that maps to x
    -- ⊢ `∃ (k : Fin (2 ^ steps)), k ∈ Set.univ ∧ qMap_total_fiber ... y₁ k = x`.
    rcases hx₁ with ⟨k, _, h_eq⟩
    use k; exact h_eq.symm

  have h_exists_k₂ : ∃ k, x = qMap_total_fiber 𝔽q β (i := ⟨i, by omega⟩) (steps := steps)
      (h_i_add_steps := by apply Nat.lt_add_of_pos_right_of_le; omega) y₂ k := by
    rw [Set.mem_toFinset] at hx₂
    rw [Set.mem_image] at hx₂ -- Set.mem_image gives us t an index that maps to x
    rcases hx₂ with ⟨k, _, h_eq⟩
    use k; exact h_eq.symm

  have h_y₁_eq_quotient_x : y₁ =
      iteratedQuotientMap 𝔽q β h_ℓ_add_R_rate i steps h_i_add_steps x := by
    apply generates_quotient_point_if_is_fiber_of_y (hx_is_fiber := by exact h_exists_k₁)

  have h_y₂_eq_quotient_x : y₂ =
      iteratedQuotientMap 𝔽q β h_ℓ_add_R_rate i steps h_i_add_steps x := by
    apply generates_quotient_point_if_is_fiber_of_y (hx_is_fiber := by exact h_exists_k₂)

  let kQuotientIndex := pointToIterateQuotientIndex (i := ⟨i, by omega⟩) (steps := steps)
    (h_i_add_steps := by omega) (x := x)

  -- Since `x` is in the fiber of `y₁`, applying the forward map to `x` yields `y₁`.
  have h_map_x_eq_y₁ : iteratedQuotientMap 𝔽q β h_ℓ_add_R_rate (i := ⟨i, by omega⟩)
      (k := steps) (h_bound := by omega) x = y₁ := by
    have h := iteratedQuotientMap_of_qMap_total_fiber_eq_self (y := y₁) (k := kQuotientIndex)
    have hx₁ : x = qMap_total_fiber 𝔽q β (i := ⟨i, by omega⟩) (steps := steps)
        (h_i_add_steps := by apply Nat.lt_add_of_pos_right_of_le; omega) y₁ kQuotientIndex := by
      have h_res := is_fiber_iff_generates_quotient_point 𝔽q β i steps (by omega)
        (x := x) (y := y₁).mp (h_y₁_eq_quotient_x)
      exact h_res.symm
    rw [hx₁]
    exact iteratedQuotientMap_of_qMap_total_fiber_eq_self y₁ kQuotientIndex

  -- Similarly, since `x` is in the fiber of `y₂`, applying the forward map yields `y₂`.
  have h_map_x_eq_y₂ : iteratedQuotientMap 𝔽q β h_ℓ_add_R_rate (i := ⟨i, by omega⟩)
      (k := steps) (h_bound := by omega) x = y₂ := by
    -- have h := iteratedQuotientMap_of_qMap_total_fiber_eq_self (y := y₂) (k := kQuotientIndex)
    have hx₂ : x = qMap_total_fiber 𝔽q β (i := ⟨i, by omega⟩) (steps := steps)
        (h_i_add_steps := by apply Nat.lt_add_of_pos_right_of_le; omega) y₂ kQuotientIndex := by
      have h_res := is_fiber_iff_generates_quotient_point 𝔽q β i steps (by omega)
        (x := x) (y := y₂).mp (h_y₂_eq_quotient_x)
      exact h_res.symm
    rw [hx₂]
    exact iteratedQuotientMap_of_qMap_total_fiber_eq_self y₂ kQuotientIndex

  exact hy_ne (h_map_x_eq_y₁.symm.trans h_map_x_eq_y₂)

/-- Single-step fold : Given `f : S⁽ⁱ⁾ → L` and challenge `r`, produce `S⁽ⁱ⁺¹⁾ → L`, where
`f⁽ⁱ⁺¹⁾ = fold(f⁽ⁱ⁾, r) : y ↦ [1-r, r] · [[x₁, -x₀], [-1, 1]] · [f⁽ⁱ⁾(x₀), f⁽ⁱ⁾(x₁)]`
-/
def fold (i : Fin r) (h_i : i + 1 < ℓ + 𝓡) (f : (sDomain 𝔽q β
    h_ℓ_add_R_rate) i → L) (r_chal : L) :
    (sDomain 𝔽q β h_ℓ_add_R_rate) (⟨i + 1, by omega⟩) → L :=
  fun y => by
    let fiberMap := qMap_total_fiber 𝔽q β (i := i) (steps := 1)
      (h_i_add_steps := h_i) (y := y)
    let x₀ := fiberMap 0
    let x₁ := fiberMap 1
    let f_x₀ := f x₀
    let f_x₁ := f x₁
    exact f_x₀ * ((1 - r_chal) * x₁.val - r_chal) + f_x₁ * (r_chal - (1 - r_chal) * x₀.val)

def baseFoldMatrix (i : Fin r) (h_i : i + 1 < ℓ + 𝓡)
    (y : ↥(sDomain 𝔽q β h_ℓ_add_R_rate ⟨↑i + 1, by omega⟩)) : Matrix (Fin 2) (Fin 2) L :=
  let fiberMap := qMap_total_fiber 𝔽q β (i := i) (steps := 1)
      (h_i_add_steps := h_i) (y := y)
  let x₀ := fiberMap 0
  let x₁ := fiberMap 1
  fun i j => match i, j with
  | 0, 0 => x₁
  | 0, 1 => -x₀
  | 1, 0 => -1
  | 1, 1 => 1

/-- The fold matrix as a `Nat`-indexed structural recursion on `steps`.

This is the explicit recursive construction pinned by `iterated_fold_eq_matrix_form`
(Lemma 4.9). Peeling the **last** fold (`Fin.dfoldl_succ_last`) at level `i + steps`,
`iterated_fold (steps + 1)` is one extra single-step `fold` applied to `iterated_fold steps`.
Translating that one step into matrix form yields the block/composition law:
`M_{steps+1}(y)[a][b] = baseFoldMatrix(i+steps, y)[a % 2][b / 2^steps]`
`  * M_{steps}(z_{b / 2^steps})[a / 2][b % 2^steps]`,
where `z_c = qMap_total_fiber(i+steps, 1, y)(c)` are the two single-step preimages of `y`,
the new (last) challenge occupies the **low** bit of the row index `a` (matching
`challengeTensorProduct`'s recursion), and the last quotient level occupies the **high**
bits of the column/fiber index `b` (matching `qMap_total_fiber`'s MSB convention).
The base case `steps = 0` is the `1 × 1` identity scalar `1`. -/
noncomputable def foldMatrixNat (i : Fin r) :
    (steps : ℕ) → (h_i_add_steps : i.val + steps < ℓ + 𝓡) →
    (y : (sDomain 𝔽q β h_ℓ_add_R_rate) ⟨↑i + steps, by omega⟩) →
    Matrix (Fin (2 ^ steps)) (Fin (2 ^ steps)) L
  | 0, _, _ => fun _ _ => 1
  | (n + 1), h, y =>
      let baseM : Matrix (Fin 2) (Fin 2) L :=
        baseFoldMatrix 𝔽q β ⟨i.val + n, by omega⟩ (h_i := by simp only; omega)
          (y := ⟨y.val, by have := y.property; simpa only [Nat.add_assoc] using this⟩)
      let zMap : Fin 2 → (sDomain 𝔽q β h_ℓ_add_R_rate) ⟨i.val + n, by omega⟩ :=
        qMap_total_fiber 𝔽q β (i := ⟨i.val + n, by omega⟩) (steps := 1)
          (h_i_add_steps := by simp only; omega)
          (y := ⟨y.val, by have := y.property; simpa only [Nat.add_assoc] using this⟩)
      fun a b =>
        let cBit : Fin 2 := ⟨b.val / 2 ^ n, by
          have hb : b.val < 2 ^ n * 2 :=
            Nat.lt_of_lt_of_eq b.isLt (by rw [pow_succ])
          exact Nat.div_lt_of_lt_mul hb⟩
        let bLow : Fin (2 ^ n) := ⟨b.val % 2 ^ n, Nat.mod_lt _ (Nat.two_pow_pos n)⟩
        let aBit : Fin 2 := ⟨a.val % 2, Nat.mod_lt _ (by omega)⟩
        let aHigh : Fin (2 ^ n) := ⟨a.val / 2, by
          have ha : a.val < 2 * 2 ^ n :=
            Nat.lt_of_lt_of_eq a.isLt (by rw [pow_succ, Nat.mul_comm])
          exact Nat.div_lt_of_lt_mul ha⟩
        baseM aBit cBit * foldMatrixNat i n (by omega) (zMap cBit) aHigh bLow

/-- `M_y` matrix which depends only on `y ∈ S^(i+ϑ)` -/
def foldMatrix (i : Fin r) (steps : Fin (ℓ + 1)) (h_i_add_steps : i.val + steps < ℓ + 𝓡)
    (y : (sDomain 𝔽q β h_ℓ_add_R_rate)
      ⟨↑i + steps, by apply Nat.lt_trans (m := ℓ + 𝓡) (h_i_add_steps) h_ℓ_add_R_rate⟩)
    : Matrix (Fin (2 ^ steps.val)) (Fin (2 ^ steps.val)) L :=
  foldMatrixNat 𝔽q β i steps.val h_i_add_steps y

/-- Agreement of the single-step `foldMatrixNat` with `baseFoldMatrix`: the recursion's
`steps = 1` value is exactly the base matrix (its old special-case branch). -/
lemma foldMatrixNat_one (i : Fin r) (h_i_add_steps : i.val + 1 < ℓ + 𝓡)
    (y : (sDomain 𝔽q β h_ℓ_add_R_rate) ⟨↑i + 1, by omega⟩)
    (a b : Fin (2 ^ 1)) :
    foldMatrixNat 𝔽q β i 1 h_i_add_steps y a b =
      baseFoldMatrix 𝔽q β i (h_i := by simpa using h_i_add_steps) y
        (Fin.cast (by norm_num) a) (Fin.cast (by norm_num) b) := by
  -- Unfold one recursion step; the `steps = 0` tail collapses to the scalar `1`.
  simp only [foldMatrixNat, pow_zero, Nat.div_one, Nat.mod_one, mul_one]
  -- Both sides are `baseFoldMatrix` of the same data; reconcile `i + 0 = i`, the `y`
  -- subtype lift, and the `Fin 2` indices (`a % 2 = a`, `b / 1 = b` for `a, b < 2`).
  congr 1
  all_goals apply Fin.ext
  all_goals simp only [Fin.coe_cast]
  all_goals omega

/-- Iterated fold over `steps` steps starting at domain index `i`. -/
def iterated_fold (i : Fin r) (steps : Fin (ℓ + 1)) (h_i_add_steps : i.val + steps < ℓ + 𝓡)
  (f : sDomain 𝔽q β h_ℓ_add_R_rate (i := i) → L) (r_challenges : Fin steps → L) :
    sDomain 𝔽q β h_ℓ_add_R_rate
      (⟨i + steps.val, Nat.lt_trans (m := ℓ + 𝓡) (h_i_add_steps) h_ℓ_add_R_rate⟩) → L := by
  let domain_type := sDomain 𝔽q β h_ℓ_add_R_rate
  let fold_func := fold 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
  let α (j : Fin (steps + 1)) := domain_type (⟨i + j.val, by omega⟩) → L
  let fold_step (j : Fin steps) (f_acc : α ⟨j, by omega⟩) : α j.succ := by
    unfold α domain_type at *
    intro x
    have fold_func := fold_func (i := ⟨i + j.val, by omega⟩) (h_i := by
      simp only
      omega
    ) (f_acc) (r_challenges j)
    exact fold_func x
  exact Fin.dfoldl (n := steps) (α := α) (f := fun i (accF : α ⟨i, by omega⟩) =>
    have fSucc : α ⟨i.succ, by omega⟩ := fold_step i accF
    fSucc) (init := f)

set_option maxHeartbeats 1000000 in
seal sDomain qMap_total_fiber normalizedW intermediateEvaluationPoly in
/-- **Peel the last fold step from `iterated_fold`.** Folding `n + 1` steps starting at
level `i` equals one single-step `fold` (at level `i + n`, with the last challenge
`r_challenges (last n)`) applied to the `n`-step iterated fold over the truncated
challenges. This is the structural `Fin.dfoldl` peel (`Fin.dfoldl_succ_last`) that drives
the inductive proof of Lemma 4.9. -/
theorem iterated_fold_succ_last (i : Fin ℓ) (n : ℕ)
    (h_i_add_steps : i.val + (n + 1) ≤ ℓ)
    (f : sDomain 𝔽q β h_ℓ_add_R_rate (i := ⟨i, by omega⟩) → L)
    (r_challenges : Fin (n + 1) → L)
    (y : sDomain 𝔽q β h_ℓ_add_R_rate (i := ⟨i.val + (n + 1), by omega⟩)) :
    iterated_fold 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (i := ⟨i, by omega⟩)
      (steps := ⟨n + 1, by omega⟩)
      (by simp only; exact fin_ℓ_steps_lt_ℓ_add_R i (n + 1) h_i_add_steps) f r_challenges y =
    fold 𝔽q β (i := ⟨i.val + n, by omega⟩)
      (h_i := by simp only; have h𝓡 : 0 < 𝓡 := Nat.pos_of_ne_zero (NeZero.ne 𝓡); omega)
      (f := iterated_fold 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (i := ⟨i, by omega⟩)
        (steps := ⟨n, by omega⟩)
        (by simp only; exact fin_ℓ_steps_lt_ℓ_add_R i n (by omega)) f
        (fun j => r_challenges j.castSucc))
      (r_chal := r_challenges (Fin.last n))
      ⟨y.val, by have hy := y.property; simpa only [Nat.add_assoc] using hy⟩ := by
  unfold iterated_fold
  rw [Fin.dfoldl_succ_last]
  rfl

/--
Transitivity of iterated_fold : folding for `steps₁` and then for `steps₂`
equals folding for `steps₁ + steps₂` with concatenated challenges.
-/
lemma iterated_fold_transitivity
    (i : Fin r) (steps₁ steps₂ : Fin (ℓ + 1))
    (h_bounds : i.val + steps₁ + steps₂ ≤ ℓ) -- A single, sufficient bounds check
    (f : sDomain 𝔽q β h_ℓ_add_R_rate (i := i) → L)
    (r_challenges₁ : Fin steps₁ → L) (r_challenges₂ : Fin steps₂ → L) :
    -- LHS : The nested fold (folding twice)
    have hi1 : i.val + steps₁ ≤ ℓ := by exact le_of_add_right_le h_bounds
    have hi2 : i.val + steps₂ ≤ ℓ := by
      rw [Nat.add_assoc, Nat.add_comm steps₁ steps₂, ←Nat.add_assoc] at h_bounds
      exact le_of_add_right_le h_bounds
    have hi12 : steps₁ + steps₂ < ℓ + 1 := by
      apply Nat.lt_succ_of_le; rw [Nat.add_assoc] at h_bounds;
      exact Nat.le_of_add_left_le h_bounds
    let lhs := iterated_fold 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
      (i := ⟨i.val + steps₁, by -- ⊢ ↑i + ↑steps₁ < r
        apply Nat.lt_of_le_of_lt (m := ℓ) (hi1) (ℓ_lt_r (h_ℓ_add_R_rate := h_ℓ_add_R_rate))⟩)
      (steps := steps₂)
      (h_i_add_steps := by simp only; apply Nat.lt_add_of_pos_right_of_le; exact h_bounds)
      (f := by
        exact iterated_fold 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (i := i) (steps := steps₁)
          (h_i_add_steps := by apply Nat.lt_add_of_pos_right_of_le; exact hi1) (f := f)
          (r_challenges := r_challenges₁)
      ) r_challenges₂
    let rhs := iterated_fold 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (i := i)
      (steps := ⟨steps₁ + steps₂, hi12⟩)
      (h_i_add_steps := by
        simp only; rw [←Nat.add_assoc]; apply Nat.lt_add_of_pos_right_of_le; exact h_bounds)
      (f := f) (r_challenges := Fin.append r_challenges₁ r_challenges₂)
    lhs = by
      simp only [←Nat.add_assoc] at ⊢ rhs
      exact rhs := by
  -- PROOF APPROACH (documented; not yet closed). After `simp only`, the goal is the
  -- `Fin.dfoldl` append/split law:
  --   `iterated_fold (i+s₁) s₂ (iterated_fold i s₁ f r₁) r₂`
  --     = cast (iterated_fold i (s₁+s₂) f (Fin.append r₁ r₂)).
  -- Induct on `s₂ := steps₂.val` (via `obtain ⟨s2, hs2⟩ := steps₂`). The base case needs
  -- `Fin.dfoldl_zero` (LHS) + `Fin.append` of an empty tail + the `⟨s₁+0,_⟩ ≃ steps₁` cast.
  -- The succ case peels the last step on BOTH sides and consumes the IH on the truncated
  -- `Fin.append r₁ (r₂ ∘ castSucc)`; the heavy part is the dependent-cast/`Fin.append`
  -- index bookkeeping under the `Fin (ℓ+1)` packaging. NOTE: unlike Lemma 4.9, the start
  -- index here is a general `i : Fin r` (not `Fin ℓ`), so `iterated_fold_succ_last` (which
  -- requires `Fin ℓ`) does NOT directly apply — a generic `Fin.dfoldl`-level peel is needed.
  sorry

/-- Tensor product of challenge vectors : for a local fold length `steps`,
⨂_{j=0}^{steps-1}(1-r_j, r_j). -/
def challengeTensorProduct (steps : ℕ) (r_challenges : Fin steps → L) : Vector L (2 ^ steps) :=
  if h_steps_zero : steps = 0 then
    -- Base case : steps = 0, return single element vector [1]
    by
      rw [h_steps_zero, pow_zero]
      exact ⟨#[1], rfl⟩
  else
    -- Recursive case : compute tensor product iteratively
    Nat.rec
      (motive := fun k => k ≤ steps → Vector L (2^k))
      (fun _ => ⟨#[1], rfl⟩)  -- Base : empty tensor product = [1]
      (fun k ih h_k_le =>
        -- Inductive step : extend tensor product by one more challenge
        let prev_vec := ih (Nat.le_trans (Nat.le_succ k) h_k_le)
        let r_k := r_challenges ⟨k, by omega⟩
        -- Each element of prev_vec gets multiplied by both (1-r_k) and r_k
        Vector.ofFn (fun idx : Fin (2^k.succ) =>
          let prev_idx : Fin (2^k) := ⟨idx.val / 2, by
            have h_succ : 2^k.succ = 2 * 2^k := by rw [pow_succ, mul_comm]
            rw [h_succ] at idx
            have : idx.val < 2 * 2^k := idx.isLt
            apply Nat.div_lt_of_lt_mul;
            omega⟩
          let bit := idx.val % 2
          let prev_val := prev_vec.get prev_idx
          if bit = 0 then (1 - r_k) * prev_val else r_k * prev_val))
      steps (le_refl steps)

/-- The inner `Nat.rec` accumulator of `challengeTensorProduct` (for nonzero outer `steps`),
exposed as a structural recursion so we can reason about it compositionally. -/
def ctpAux (m : ℕ) (r_challenges : Fin m → L) : (k : ℕ) → k ≤ m → Vector L (2 ^ k)
  | 0, _ => ⟨#[1], rfl⟩
  | (k + 1), hk =>
      Vector.ofFn (fun idx : Fin (2 ^ (k + 1)) =>
        let prev_idx : Fin (2 ^ k) := ⟨idx.val / 2, by
          exact Nat.div_lt_of_lt_mul (Nat.lt_of_lt_of_eq idx.isLt (by rw [pow_succ, Nat.mul_comm]))⟩
        if idx.val % 2 = 0
          then (1 - r_challenges ⟨k, by omega⟩) * (ctpAux m r_challenges k (by omega)).get prev_idx
          else r_challenges ⟨k, by omega⟩ * (ctpAux m r_challenges k (by omega)).get prev_idx)

/-- The raw inner `Nat.rec` accumulator equals the named `ctpAux`, at every level `k ≤ m`. -/
theorem natRec_ctp_eq_ctpAux (m : ℕ) (r_challenges : Fin m → L) :
    ∀ (k : ℕ) (hk : k ≤ m),
      (Nat.rec (motive := fun k => k ≤ m → Vector L (2 ^ k)) (fun _ => ⟨#[1], rfl⟩)
        (fun k ih h_k_le =>
          let prev_vec := ih (Nat.le_trans (Nat.le_succ k) h_k_le)
          let r_k := r_challenges ⟨k, by omega⟩
          Vector.ofFn (fun idx : Fin (2 ^ k.succ) =>
            let prev_idx : Fin (2 ^ k) := ⟨idx.val / 2, by
              have h_succ : 2 ^ k.succ = 2 * 2 ^ k := by rw [pow_succ, mul_comm]
              rw [h_succ] at idx
              have : idx.val < 2 * 2 ^ k := idx.isLt
              apply Nat.div_lt_of_lt_mul
              omega⟩
            let bit := idx.val % 2
            let prev_val := prev_vec.get prev_idx
            if bit = 0 then (1 - r_k) * prev_val else r_k * prev_val))
        k hk)
      = ctpAux (ℓ := ℓ) (𝓡 := 𝓡) (r := r) m r_challenges k hk := by
  intro k
  induction k with
  | zero => intro hk; rfl
  | succ k ih =>
    intro hk
    show (Vector.ofFn _ : Vector L (2 ^ (k + 1))) = _
    simp only [ctpAux]
    congr 1
    funext idx
    rw [ih (by omega)]

/-- `challengeTensorProduct` (nonzero `steps`) is exactly its named inner recursion. -/
theorem challengeTensorProduct_eq_ctpAux (m : ℕ) (hm : m ≠ 0) (r_challenges : Fin m → L) :
    challengeTensorProduct (L := L) (ℓ := ℓ) (𝓡 := 𝓡) (r := r) m r_challenges
      = ctpAux (ℓ := ℓ) (𝓡 := 𝓡) (r := r) m r_challenges m (le_refl m) := by
  rw [challengeTensorProduct]
  simp only [hm, ↓reduceDIte]
  exact natRec_ctp_eq_ctpAux m r_challenges m (le_refl m)

/-- `ctpAux` get only depends on the challenges at indices `< k`. -/
theorem ctpAux_congr (m m' : ℕ) (r' : Fin m → L) (r'' : Fin m' → L) :
    ∀ (k : ℕ), (∀ (j : ℕ) (hm : j < m) (hm' : j < m'), j < k → r' ⟨j, hm⟩ = r'' ⟨j, hm'⟩) →
      ∀ (hk : k ≤ m) (hk' : k ≤ m') (idx : Fin (2 ^ k)),
        (ctpAux (ℓ := ℓ) (𝓡 := 𝓡) (r := r) m r' k hk).get idx
          = (ctpAux (ℓ := ℓ) (𝓡 := 𝓡) (r := r) m' r'' k hk').get idx := by
  intro k
  induction k with
  | zero => intro _ _ _ idx; fin_cases idx; rfl
  | succ k ih =>
    intro hagree hk hk' idx
    simp only [ctpAux, Vector.get_ofFn]
    have hrk : r' ⟨k, by omega⟩ = r'' ⟨k, by omega⟩ := hagree k (by omega) (by omega) (by omega)
    have hprev : (ctpAux (ℓ := ℓ) (𝓡 := 𝓡) (r := r) m r' k (by omega)).get ⟨idx.val / 2, by
        exact Nat.div_lt_of_lt_mul (Nat.lt_of_lt_of_eq idx.isLt (by rw [pow_succ, Nat.mul_comm]))⟩
      = (ctpAux (ℓ := ℓ) (𝓡 := 𝓡) (r := r) m' r'' k (by omega)).get ⟨idx.val / 2, by
        exact Nat.div_lt_of_lt_mul (Nat.lt_of_lt_of_eq idx.isLt (by rw [pow_succ, Nat.mul_comm]))⟩ :=
      ih (fun j hmj hm'j hjk => hagree j hmj hm'j (by omega)) (by omega) (by omega) _
    rw [hrk, hprev]

set_option maxHeartbeats 2000000 in
/-- Tensor product recursion (entry form): low bit selects last challenge, high bits index the
`n`-step tensor over truncated challenges. -/
theorem challengeTensorProduct_succ_get (n : ℕ) (r_challenges : Fin (n + 1) → L)
    (idx : Fin (2 ^ (n + 1))) :
    (challengeTensorProduct (L := L) (ℓ := ℓ) (𝓡 := 𝓡) (r := r) (n + 1) r_challenges).get idx =
      (if idx.val % 2 = 0 then (1 - r_challenges (Fin.last n)) else r_challenges (Fin.last n)) *
        (challengeTensorProduct (L := L) (ℓ := ℓ) (𝓡 := 𝓡) (r := r) n
          (fun j => r_challenges j.castSucc)).get
          ⟨idx.val / 2, by
            exact Nat.div_lt_of_lt_mul (Nat.lt_of_lt_of_eq idx.isLt (by rw [pow_succ, Nat.mul_comm]))⟩ := by
  rw [challengeTensorProduct_eq_ctpAux (n + 1) (by omega) r_challenges]
  simp only [ctpAux, Vector.get_ofFn]
  have hlast : r_challenges ⟨n, by omega⟩ = r_challenges (Fin.last n) := rfl
  rw [hlast]
  by_cases hn : n = 0
  · subst hn
    fin_cases idx <;> split <;> rfl
  · rw [challengeTensorProduct_eq_ctpAux n hn (fun j => r_challenges j.castSucc)]
    have hidxlt : idx.val / 2 < 2 ^ n :=
      Nat.div_lt_of_lt_mul (Nat.lt_of_lt_of_eq idx.isLt (by rw [pow_succ, Nat.mul_comm]))
    have hbridge :
        (ctpAux (ℓ := ℓ) (𝓡 := 𝓡) (r := r) (n + 1) r_challenges n (by omega)).get ⟨idx.val / 2, hidxlt⟩
        = (ctpAux (ℓ := ℓ) (𝓡 := 𝓡) (r := r) n (fun j => r_challenges j.castSucc) n (by omega)).get
            ⟨idx.val / 2, hidxlt⟩ := by
      apply ctpAux_congr
      intro j hmj hm'j hjk
      rfl
    rw [hbridge]
    split <;> rfl

/-- Evaluation vector [f^(i)(x_0) ... f^(i)(x_{2 ^ steps-1})]^T -/
def fiberEvaluationMapping (i : Fin r) (steps : ℕ) (h_i_add_steps : i.val + steps < ℓ + 𝓡)
    (f : (sDomain 𝔽q β h_ℓ_add_R_rate) i → L)
    (y : (sDomain 𝔽q β h_ℓ_add_R_rate)
      ⟨↑i + steps, by apply Nat.lt_trans (m := ℓ + 𝓡) (h_i_add_steps) h_ℓ_add_R_rate⟩)
    : Fin (2 ^ steps) → L :=
  -- Get the fiber points
  let fiberMap := qMap_total_fiber 𝔽q β (i := i) (steps := steps)
    (h_i_add_steps := h_i_add_steps) (y := y)

  -- Evaluate f at each fiber point
  fun idx => f (fiberMap idx)

/-- Matrix-vector multiplication form of iterated fold : For a local `steps > 0`,
`∀ i ∈ {0, ..., l-steps}`,
`y ∈ S^(i+steps)`,
`fold(f^(i), r_0, ..., r_{steps-1})(y) = [⨂_{j=0}^{steps-1}(1-r_j, r_j)] • M_y`
`• [f^(i)(x_0) ... f^(i)(x_{2 ^ steps-1})]^T`,
where the right-hand vector's values `(x_0, ..., x_{2 ^ steps-1})` represent the fiber
`(q^(i+steps-1) ∘ ... ∘ q^(i))⁻¹({y}) ⊂ S^(i)`.
-/
def localized_fold_matrix_form (i : Fin ℓ) (steps : ℕ) (h_i_add_steps : i.val + steps ≤ ℓ)
  (r_challenges : Fin steps → L)
  (y : (sDomain 𝔽q β h_ℓ_add_R_rate) ⟨↑i + steps, by omega⟩)
  (fiber_eval_mapping : Fin (2 ^ steps) → L) :
  L := by
    let challenge_vec : Vector L (2 ^ steps) := challengeTensorProduct (L := L)
      (ℓ := ℓ) (𝓡 := 𝓡) (r := r) steps r_challenges
    let fold_mat := foldMatrix 𝔽q β (i := ⟨i, by omega⟩) ⟨steps, by omega⟩
      (h_i_add_steps := by apply Nat.lt_add_of_pos_right_of_le; omega) y
    -- Matrix-vector multiplication : challenge_vec^T • (fold_mat • fiber_eval_mapping)
    let intermediate_fn := Matrix.mulVec fold_mat fiber_eval_mapping
    let intermediate_vec := Vector.ofFn intermediate_fn
    simp only at intermediate_vec
    exact Vector.dotProduct challenge_vec intermediate_vec

/-- Wrapper of `localized_fold_matrix_form` with `fiber_eval_mapping` being specified
explicitly. -/
def localized_fold_eval (i : Fin ℓ) (steps : ℕ) (h_i_add_steps : i + steps ≤ ℓ)
    (f : (sDomain 𝔽q β h_ℓ_add_R_rate)
      ⟨i, by exact Nat.lt_of_le_of_lt (n := i) (k := r) (m := ℓ) (h₁ := by
        exact Fin.is_le') (by exact lt_of_add_right_lt h_ℓ_add_R_rate)⟩ → L)
    (r_challenges : Fin steps → L)
    (y : (sDomain 𝔽q β h_ℓ_add_R_rate) ⟨↑i + steps, by omega⟩) : L := by
    let fiber_eval_mapping := fiberEvaluationMapping 𝔽q β (steps := steps)
      (i := ⟨i, by omega⟩)
      (h_i_add_steps := by apply Nat.lt_add_of_pos_right_of_le; omega) f y
    exact localized_fold_matrix_form 𝔽q β (i := i) steps h_i_add_steps r_challenges y
      fiber_eval_mapping

/-- Split a sum over `Fin (2^(n+1))` into the high bit `c ∈ Fin 2` and the low `n` bits
`b ∈ Fin (2^n)`, where `idx = c * 2^n + b`. -/
theorem sum_fin_pow_succ_split {M : Type*} [AddCommMonoid M] (n : ℕ)
    (g : Fin (2 ^ (n + 1)) → M) :
    ∑ idx : Fin (2 ^ (n + 1)), g idx =
      ∑ c : Fin 2, ∑ b : Fin (2 ^ n),
        g ⟨c.val * 2 ^ n + b.val, by
          have h2 : 2 ^ (n + 1) = 2 ^ n * 2 := by rw [pow_succ]
          have hc : c.val < 2 := c.isLt
          have hb : b.val < 2 ^ n := b.isLt
          rw [h2]; nlinarith [Nat.mul_le_mul_right (2 ^ n) (Nat.le_pred_of_lt hc)]⟩ := by
  have h2 : 2 ^ (n + 1) = 2 ^ n * 2 := by rw [pow_succ]
  rw [← Finset.sum_product']
  refine Finset.sum_nbij'
    (i := fun idx => (⟨idx.val / 2 ^ n, by
        have : idx.val < 2 ^ n * 2 := by rw [← h2]; exact idx.isLt
        exact Nat.div_lt_of_lt_mul (by omega)⟩,
      ⟨idx.val % 2 ^ n, Nat.mod_lt _ (Nat.two_pow_pos n)⟩))
    (j := fun p => ⟨p.1.val * 2 ^ n + p.2.val, by
        have hc : p.1.val < 2 := p.1.isLt
        have hb : p.2.val < 2 ^ n := p.2.isLt
        rw [h2]; nlinarith [Nat.mul_le_mul_right (2 ^ n) (Nat.le_pred_of_lt hc)]⟩)
    ?_ ?_ ?_ ?_ ?_
  · intro idx _; exact Finset.mem_univ _
  · intro p _; exact Finset.mem_univ _
  · intro idx _
    apply Fin.ext; simp only
    have hdm := Nat.div_add_mod idx.val (2 ^ n)
    have hc : idx.val / 2 ^ n * 2 ^ n = 2 ^ n * (idx.val / 2 ^ n) := Nat.mul_comm _ _
    omega
  · intro p _
    apply Prod.ext
    · apply Fin.ext; simp only
      rw [Nat.add_comm, Nat.add_mul_div_right _ _ (Nat.two_pow_pos n),
        Nat.div_eq_of_lt p.2.isLt, Nat.zero_add]
    · apply Fin.ext; simp only
      rw [Nat.add_comm, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt p.2.isLt]
  · intro idx _
    congr 1
    apply Fin.ext; simp only
    have hdm := Nat.div_add_mod idx.val (2 ^ n)
    have hc : idx.val / 2 ^ n * 2 ^ n = 2 ^ n * (idx.val / 2 ^ n) := Nat.mul_comm _ _
    omega

set_option maxHeartbeats 2000000 in
seal sDomain qMap_total_fiber normalizedW intermediateEvaluationPoly in
/-- `localized_fold_eval` as an explicit double sum over the challenge tensor and fold matrix. -/
theorem localized_fold_eval_eq_sum (i : Fin ℓ) (steps : ℕ) (h_i_add_steps : i.val + steps ≤ ℓ)
    (f : (sDomain 𝔽q β h_ℓ_add_R_rate) ⟨i, by omega⟩ → L)
    (r_challenges : Fin steps → L)
    (y : (sDomain 𝔽q β h_ℓ_add_R_rate) ⟨↑i + steps, by omega⟩) :
    localized_fold_eval 𝔽q β i (steps := steps) (h_i_add_steps := h_i_add_steps) f r_challenges y =
      ∑ a : Fin (2 ^ steps),
        (challengeTensorProduct (L := L) (ℓ := ℓ) (𝓡 := 𝓡) (r := r) steps r_challenges).get a *
          ∑ b : Fin (2 ^ steps),
            foldMatrixNat 𝔽q β ⟨i, by omega⟩ steps
              (by simp only; exact fin_ℓ_steps_lt_ℓ_add_R i steps h_i_add_steps) y a b *
              f (qMap_total_fiber 𝔽q β (i := ⟨i, by omega⟩) (steps := steps)
                (h_i_add_steps := by simp only; exact fin_ℓ_steps_lt_ℓ_add_R i steps h_i_add_steps)
                (y := y) b) := by
  unfold localized_fold_eval localized_fold_matrix_form fiberEvaluationMapping foldMatrix
  simp only
  rw [Vector.dotProduct_eq_root_dotProduct]
  unfold _root_.dotProduct
  simp only [Vector.get_ofFn]
  rfl

/-- Split a sum over `Fin (2^(n+1))` into the low bit `lo ∈ Fin 2` and the high `n` bits
`hi ∈ Fin (2^n)`, where `idx = lo + 2 * hi`. -/
theorem sum_fin_pow_succ_split_low {M : Type*} [AddCommMonoid M] (n : ℕ)
    (g : Fin (2 ^ (n + 1)) → M) :
    ∑ idx : Fin (2 ^ (n + 1)), g idx =
      ∑ lo : Fin 2, ∑ hi : Fin (2 ^ n),
        g ⟨lo.val + 2 * hi.val, by
          have h2 : 2 ^ (n + 1) = 2 * 2 ^ n := by rw [pow_succ, Nat.mul_comm]
          have hlo : lo.val < 2 := lo.isLt
          have hhi : hi.val < 2 ^ n := hi.isLt
          rw [h2]; omega⟩ := by
  have h2 : 2 ^ (n + 1) = 2 * 2 ^ n := by rw [pow_succ, Nat.mul_comm]
  rw [← Finset.sum_product']
  refine Finset.sum_nbij'
    (i := fun idx => (⟨idx.val % 2, Nat.mod_lt _ (by omega)⟩, ⟨idx.val / 2, by
        have : idx.val < 2 * 2 ^ n := by rw [← h2]; exact idx.isLt
        exact Nat.div_lt_of_lt_mul (by omega)⟩))
    (j := fun p => ⟨p.1.val + 2 * p.2.val, by
        have hlo : p.1.val < 2 := p.1.isLt
        have hhi : p.2.val < 2 ^ n := p.2.isLt
        rw [h2]; omega⟩)
    ?_ ?_ ?_ ?_ ?_
  · intro idx _; exact Finset.mem_univ _
  · intro p _; exact Finset.mem_univ _
  · intro idx _
    apply Fin.ext; simp only
    omega
  · intro p _
    apply Prod.ext
    · apply Fin.ext; simp only
      rw [Nat.add_mul_mod_self_left]
      exact Nat.mod_eq_of_lt p.1.isLt
    · apply Fin.ext; simp only
      rw [Nat.add_mul_div_left _ _ (by omega : 0 < 2), Nat.div_eq_of_lt p.1.isLt, Nat.zero_add]
  · intro idx _
    congr 1
    apply Fin.ext; simp only
    omega

set_option maxHeartbeats 2000000 in
seal sDomain qMap_total_fiber normalizedW intermediateEvaluationPoly in
/-- One-step recursion of `foldMatrixNat` at an entry. -/
theorem foldMatrixNat_succ_apply (i : Fin r) (n : ℕ) (h : i.val + (n + 1) < ℓ + 𝓡)
    (y : (sDomain 𝔽q β h_ℓ_add_R_rate) ⟨↑i + (n + 1), by omega⟩)
    (a b : Fin (2 ^ (n + 1))) :
    foldMatrixNat 𝔽q β i (n + 1) h y a b =
      baseFoldMatrix 𝔽q β ⟨i.val + n, by omega⟩ (h_i := by simp only; omega)
        (y := ⟨y.val, by have := y.property; simpa only [Nat.add_assoc] using this⟩)
        ⟨a.val % 2, Nat.mod_lt _ (by omega)⟩
        ⟨b.val / 2 ^ n, Nat.div_lt_of_lt_mul (by have e : 2 ^ (n + 1) = 2 * 2 ^ n := (by rw [pow_succ, Nat.mul_comm]); have := b.isLt; omega)⟩ *
      foldMatrixNat 𝔽q β i n (show i.val + n < ℓ + 𝓡 by omega)
        (qMap_total_fiber 𝔽q β (i := ⟨i.val + n, by omega⟩) (steps := 1)
          (h_i_add_steps := by simp only; omega)
          (y := ⟨y.val, by have := y.property; simpa only [Nat.add_assoc] using this⟩)
          ⟨b.val / 2 ^ n, Nat.div_lt_of_lt_mul (by have e : 2 ^ (n + 1) = 2 * 2 ^ n := (by rw [pow_succ, Nat.mul_comm]); have := b.isLt; omega)⟩)
        ⟨a.val / 2, Nat.div_lt_of_lt_mul (by have e : 2 ^ (n + 1) = 2 * 2 ^ n := (by rw [pow_succ, Nat.mul_comm]); have := a.isLt; omega)⟩
        ⟨b.val % 2 ^ n, Nat.mod_lt _ (Nat.two_pow_pos n)⟩ := by
  rfl

set_option maxHeartbeats 4000000 in
seal sDomain qMap_total_fiber normalizedW intermediateEvaluationPoly in
/-- RHS recursion of `localized_fold_eval`: the `(n+1)`-step localized fold evaluation at `y`
equals one single-step `fold` (at level `i + n`, last challenge `r_challenges (last n)`) applied
to the `n`-step localized fold evaluation over the truncated challenges. -/
theorem localized_fold_eval_succ (i : Fin ℓ) (n : ℕ) (h_i_add_steps : i.val + (n + 1) ≤ ℓ)
    (f : (sDomain 𝔽q β h_ℓ_add_R_rate)
      ⟨i, by exact Nat.lt_of_le_of_lt (n := i) (k := r) (m := ℓ) (h₁ := by
        exact Fin.is_le') (by exact lt_of_add_right_lt h_ℓ_add_R_rate)⟩ → L)
    (r_challenges : Fin (n + 1) → L)
    (y : (sDomain 𝔽q β h_ℓ_add_R_rate) ⟨↑i + (n + 1), by omega⟩) :
    localized_fold_eval 𝔽q β i (steps := n + 1) (h_i_add_steps := h_i_add_steps) f
        r_challenges y =
      fold 𝔽q β (i := ⟨i.val + n, by omega⟩)
        (h_i := by simp only; have h𝓡 : 0 < 𝓡 := Nat.pos_of_ne_zero (NeZero.ne 𝓡); omega)
        (f := localized_fold_eval 𝔽q β i (steps := n) (h_i_add_steps := by omega) f
              (fun j => r_challenges j.castSucc))
        (r_chal := r_challenges (Fin.last n))
        ⟨y.val, by have hy := y.property; simpa only [Nat.add_assoc] using hy⟩ := by
  rw [localized_fold_eval_eq_sum]
  conv_rhs => unfold fold
  simp only
  rw [localized_fold_eval_eq_sum, localized_fold_eval_eq_sum]
  rw [sum_fin_pow_succ_split_low (r := r) (ℓ := ℓ) (𝓡 := 𝓡) n]
  conv_lhs =>
    enter [2, lo, 2, hi]
    rw [challengeTensorProduct_succ_get, sum_fin_pow_succ_split (n := n)]
    enter [2, 2, c, 2, bL]
    rw [foldMatrixNat_succ_apply,
      qMap_total_fiber_succ_peel_last 𝔽q β (i := i) (n := n) (h_i_add_steps := h_i_add_steps)]
  have e1 : ∀ x : Fin (2^n), (2 * (x:ℕ)) / 2 = (x:ℕ) := fun x => by omega
  have e2 : ∀ x : Fin (2^n), (1 + 2 * (x:ℕ)) / 2 = (x:ℕ) := fun x => by omega
  have e3 : ∀ x : Fin (2^n), (2^n + (x:ℕ)) / 2^n = 1 := fun x => by
    rw [Nat.add_comm, Nat.add_div_right _ (Nat.two_pow_pos n), Nat.div_eq_of_lt x.isLt]
  have e4 : ∀ x : Fin (2^n), (2^n + (x:ℕ)) % 2^n = (x:ℕ) := fun x => by
    rw [Nat.add_mod_left]; exact Nat.mod_eq_of_lt x.isLt
  simp only [Fin.sum_univ_two, Fin.val_zero, Fin.val_one,
    Nat.zero_mul, Nat.one_mul, Nat.zero_add,
    Nat.add_mul_mod_self_left,
    Nat.mul_mod_right, e1, e2, e3, e4,
    Nat.div_eq_of_lt (Fin.is_lt _), Nat.mod_eq_of_lt (Fin.is_lt _),
    if_true, Nat.one_ne_zero, if_false]
  simp only [baseFoldMatrix, Fin.eta, neg_mul, one_mul]
  rw [Finset.sum_mul, Finset.sum_mul]
  simp only [Finset.mul_sum, Finset.sum_mul, neg_mul, mul_neg, ← Finset.sum_add_distrib,
    ← Finset.sum_neg_distrib]
  apply Finset.sum_congr rfl
  intro x _
  apply Finset.sum_congr rfl
  intro x_1 _
  simp only [Fin.mk_zero, Fin.mk_one]
  ring

set_option maxHeartbeats 2000000 in
seal sDomain normalizedW intermediateEvaluationPoly in
/-- Base case of the localized fold evaluation: zero steps is just `f` at `y`. -/
theorem localized_fold_eval_zero (i : Fin ℓ) (h_i_add_steps : i.val + 0 ≤ ℓ)
    (f : (sDomain 𝔽q β h_ℓ_add_R_rate)
      ⟨i, by exact Nat.lt_of_le_of_lt (n := i) (k := r) (m := ℓ) (h₁ := by
        exact Fin.is_le') (by exact lt_of_add_right_lt h_ℓ_add_R_rate)⟩ → L)
    (r_challenges : Fin 0 → L)
    (y : (sDomain 𝔽q β h_ℓ_add_R_rate) ⟨↑i + 0, by omega⟩) :
    localized_fold_eval 𝔽q β i (steps := 0) (h_i_add_steps := h_i_add_steps) f r_challenges y
      = f ⟨y.val, by have := y.property; simpa only [Nat.add_zero] using this⟩ := by
  have hsub : Subsingleton (Fin (2 ^ 0)) := by rw [pow_zero]; infer_instance
  rw [localized_fold_eval_eq_sum]
  rw [Fintype.sum_subsingleton _ (0 : Fin (2^0))]
  rw [Fintype.sum_subsingleton _ (0 : Fin (2^0))]
  have hctp : (challengeTensorProduct (L := L) (ℓ := ℓ) (𝓡 := 𝓡) (r := r) 0 r_challenges).get
      (0 : Fin (2 ^ 0)) = 1 := rfl
  have hfm : foldMatrixNat 𝔽q β ⟨↑i, by omega⟩ 0
      (by simp only; exact fin_ℓ_steps_lt_ℓ_add_R i 0 h_i_add_steps) y (0 : Fin (2^0)) (0 : Fin (2^0)) = 1 := rfl
  have hfib : qMap_total_fiber 𝔽q β (i := ⟨↑i, by omega⟩) (steps := 0)
      (h_i_add_steps := by simp only; exact fin_ℓ_steps_lt_ℓ_add_R i 0 h_i_add_steps)
      (y := y) (0 : Fin (2^0)) = ⟨y.val, by have := y.property; simpa only [Nat.add_zero] using this⟩ := by
    simp only [qMap_total_fiber, ↓reduceDIte]
    apply Subtype.ext
    simp
  rw [hctp, hfm, hfib, one_mul, one_mul]

set_option maxHeartbeats 4000000 in
seal sDomain qMap_total_fiber normalizedW intermediateEvaluationPoly in
/-- **Lemma 4.9.** The iterated fold equals the localized fold evaluation via matmul form -/
theorem iterated_fold_eq_matrix_form (i : Fin ℓ) (steps : ℕ) (h_i_add_steps : i + steps ≤ ℓ)
    (f : (sDomain 𝔽q β h_ℓ_add_R_rate) ⟨i, by omega⟩ → L)
    (r_challenges : Fin steps → L)
    (y : (sDomain 𝔽q β h_ℓ_add_R_rate) ⟨↑i + steps, by omega⟩) :
    (iterated_fold 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
      (steps := ⟨steps, by apply Nat.lt_succ_of_le; exact Nat.le_of_add_left_le h_i_add_steps⟩)
      (i := ⟨i, by omega⟩)
      (h_i_add_steps := by simp only; exact fin_ℓ_steps_lt_ℓ_add_R i steps h_i_add_steps) f
      r_challenges ⟨y, by exact Submodule.coe_mem y⟩) =
    localized_fold_eval 𝔽q β i (steps := steps) (h_i_add_steps := h_i_add_steps) f
      r_challenges (y := ⟨y, by exact Submodule.coe_mem y⟩) := by
  induction steps with
  | zero =>
    rw [localized_fold_eval_zero]
    unfold iterated_fold
    rw [Fin.dfoldl_zero]
  | succ n ih =>
    rw [iterated_fold_succ_last 𝔽q β i n h_i_add_steps,
      localized_fold_eval_succ 𝔽q β i n h_i_add_steps]
    congr 1
    funext y'
    exact ih (by omega) f (fun j => r_challenges j.castSucc) y'


omit [CharP L 2] [NeZero ℓ] in
/-- Lemma 4.13 : if f⁽ⁱ⁾ is evaluation of P⁽ⁱ⁾(X) over S⁽ⁱ⁾, then fold(f⁽ⁱ⁾, r_chal)
  is evaluation of P⁽ⁱ⁺¹⁾(X) over S⁽ⁱ⁺¹⁾. At level `i = ℓ`, we have P⁽ˡ⁾ =
-/
theorem fold_advances_evaluation_poly
  (i : Fin (ℓ)) (h_i_succ_lt : i + 1 < ℓ + 𝓡)
  (coeffs : Fin (2 ^ (ℓ - ↑i)) → L) (r_chal : L) :
  let P_i : L[X] := intermediateEvaluationPoly 𝔽q β h_ℓ_add_R_rate (i := ⟨i, by
    exact Nat.lt_trans (n := i) (k := ℓ+1) (m := ℓ) (h₁ := i.isLt) (by exact Nat.lt_add_one ℓ)
  ⟩) coeffs
  let f_i := fun (x : (sDomain 𝔽q β h_ℓ_add_R_rate)
      ⟨i, by exact Nat.lt_trans (n := i) (k := r) (m := ℓ) (h₁ := by omega) (by omega)⟩) =>
    P_i.eval (x.val : L)
  let f_i_plus_1 := fold (i := ⟨i, by omega⟩) (h_i := by omega) (f := f_i) (r_chal := r_chal)
  let new_coeffs := fun j : Fin (2^(ℓ - (i + 1))) =>
    (1 - r_chal) * (coeffs ⟨j.val * 2, by
      rw [←Nat.add_zero (j.val * 2)]
      apply mul_two_add_bit_lt_two_pow (c := ℓ - i) (a := j) (b := ℓ - (↑i + 1))
        (i := 0) (by omega) (by omega)
    ⟩) +
    r_chal * (coeffs ⟨j.val * 2 + 1, by
      apply mul_two_add_bit_lt_two_pow (c := ℓ - i) (a := j) (b := ℓ - (↑i + 1))
        (i := 1) (by omega) (by omega)
    ⟩)
  let P_i_plus_1 :=
    intermediateEvaluationPoly 𝔽q β h_ℓ_add_R_rate (i := ⟨i+1, by omega⟩) new_coeffs
  ∀ (y : (sDomain 𝔽q β h_ℓ_add_R_rate)
    ⟨i+1, by omega⟩), f_i_plus_1 y = P_i_plus_1.eval y.val := by
  simp only
  intro y
  set fiberMap := qMap_total_fiber 𝔽q β (i := ⟨i, by omega⟩) (steps := 1)
    (h_i_add_steps := by simp only; omega) (y := y)
  set x₀ := fiberMap 0
  set x₁ := fiberMap 1
  set P_i := intermediateEvaluationPoly 𝔽q β h_ℓ_add_R_rate (i := ⟨i, by omega⟩) coeffs
  set new_coeffs := fun j : Fin (2^(ℓ - (i + 1))) =>
    (1 - r_chal) * (coeffs ⟨j.val * 2, by
      have h : j.val * 2 < 2^(ℓ - (i + 1)) * 2 := by omega
      have h2 : 2^(ℓ - i) = 2^(ℓ - (i + 1)) * 2 := by
        conv_rhs => enter[2]; rw [←Nat.pow_one 2]
        rw [←pow_add]; congr
        rw [Nat.sub_add_eq_sub_sub_rev (h1 := by omega) (h2 := by omega)]
        -- ⊢ ℓ - ↑i = ℓ - (↑i + 1 - 1)
        rw [Nat.add_sub_cancel (n := i) (m := 1)]
      omega
    ⟩) +
    r_chal * (coeffs ⟨j.val * 2 + 1, by
      apply mul_two_add_bit_lt_two_pow (c := ℓ - i) (a := j) (b := ℓ - (↑i + 1)) (i := 1)
      · omega
      · omega
    ⟩)
  have h_eval_qMap_x₀ : (AdditiveNTT.qMap 𝔽q β ⟨i, by omega⟩).eval x₀.val = y := by
    have h := iteratedQuotientMap_k_eq_1_is_qMap 𝔽q β h_ℓ_add_R_rate i (by omega) x₀
    simp only [Subtype.eq_iff] at h
    rw [h.symm]
    have h_res := is_fiber_iff_generates_quotient_point 𝔽q β i (steps := 1) (by omega)
      (x := x₀) (y := y).mpr (by rw [pointToIterateQuotientIndex_qMap_total_fiber_eq_self])
    rw [h_res]
    -- exact qMap_eval_fiber_eq_self ⟦L⟧ ⟨i + 1, by omega⟩ (by simp only; omega) h_i_succ_lt y 0
  have h_eval_qMap_x₁ : (AdditiveNTT.qMap 𝔽q β ⟨i, by omega⟩).eval x₁.val = y := by
    have h := iteratedQuotientMap_k_eq_1_is_qMap 𝔽q β h_ℓ_add_R_rate i (by omega) x₁
    simp only [Subtype.eq_iff] at h
    rw [h.symm]
    have h_res := is_fiber_iff_generates_quotient_point 𝔽q β i (steps := 1) (by omega)
      (x := x₁) (y := y).mpr (by rw [pointToIterateQuotientIndex_qMap_total_fiber_eq_self])
    rw [h_res]
  have hx₀ := qMap_total_fiber_basis_sum_repr 𝔽q β i (steps := 1)
    (h_i_add_steps := by omega) y 0
  have hx₁ := qMap_total_fiber_basis_sum_repr 𝔽q β i (steps := 1)
    (h_i_add_steps := by omega) y 1
  simp only [Fin.isValue] at hx₀ hx₁

  have h_fiber_diff : x₁.val - x₀.val = 1 := by
    simp only [Fin.isValue, x₁, x₀, fiberMap]
    rw [hx₁, hx₀]
    simp only [Fin.isValue, AddSubmonoidClass.coe_finset_sum, SetLike.val_smul]
    have h_index : ℓ + 𝓡 - i = (ℓ + 𝓡 - (i.val + 1)) + 1 := by omega
    rw! (castMode := .all) [h_index]
    rw [Fin.sum_univ_succ, Fin.sum_univ_succ] -- (free_term + y_repr) - (free_term + y_repr) = 1
    -- First, simplify the free terms
    simp only [fiber_coeff, eqRec_eq_cast, lt_one_iff, reducePow, Fin.isValue,
      Fin.coe_ofNat_eq_mod, mod_succ, dite_smul, ite_smul, zero_smul, one_smul, zero_mod]
    have h_cast_0 :
        (cast (Eq.symm h_index ▸ rfl : Fin (ℓ + 𝓡 - (↑i + 1) + 1) = Fin (ℓ + 𝓡 - ↑i)) 0).val =
        0 := by
      rw [←Fin.cast_eq_cast (h := by omega)]
      rw [Fin.cast_val_eq_val (h_eq := by omega)]
      simp only [Fin.coe_ofNat_eq_mod, mod_succ_eq_iff_lt, succ_eq_add_one, lt_add_iff_pos_left]
      omega
    have h_cast_1 :
        (cast (Eq.symm h_index ▸ rfl : Fin (ℓ + 𝓡 - (↑i + 1) + 1) = Fin (ℓ + 𝓡 - ↑i)) 1).val =
        1 := by
      rw [←Fin.cast_eq_cast (h := by omega)]
      rw [Fin.cast_val_eq_val (h_eq := by omega)]
      simp only [Fin.coe_ofNat_eq_mod, mod_succ_eq_iff_lt, succ_eq_add_one,
        lt_add_iff_pos_left, tsub_pos_iff_lt]
      omega
    simp only [h_cast_0, ↓reduceDIte]
    have h_getBit_0_of_0 : Nat.getBit (k := 0) (n := 0) = 0 := by
      simp only [getBit, shiftRight_zero, and_one_is_mod, zero_mod]
    have h_getBit_0_of_1 : Nat.getBit (k := 0) (n := 1) = 1 := by
      simp only [getBit, shiftRight_zero, Nat.and_self]
    simp only [h_getBit_0_of_1, one_ne_zero, ↓reduceIte, h_getBit_0_of_0, zero_add]
    rw! (castMode := .all) [←h_index]
    rw [cast_eq]
    simp only [get_sDomain_basis, Fin.coe_ofNat_eq_mod, zero_mod, add_zero, cast_eq]
    rw [normalizedWᵢ_eval_βᵢ_eq_1 𝔽q β]
    ring_nf
    conv_rhs => rw [←add_zero (a := 1)]
    rw [add_sub_assoc]
    congr 1
    rw [sub_eq_zero]
    apply Finset.sum_congr (h := by rfl)
    simp only [mem_univ, congr_eqRec, Fin.val_succ, Nat.add_eq_zero, one_ne_zero, and_false,
      ↓reduceDIte, add_tsub_cancel_right, Fin.eta, imp_self, implies_true]
  set P_i_plus_1 :=
    intermediateEvaluationPoly 𝔽q β h_ℓ_add_R_rate (i := ⟨i+1, by omega⟩) new_coeffs
  -- Set up the even and odd refinement polynomials
  set P₀_coeffs := fun j : Fin (2^(ℓ - (i + 1))) => coeffs ⟨j.val * 2, by
    have h1 : ℓ - (i + 1) + 1 = ℓ - i := by omega
    have h2 : 2^(ℓ - (i + 1) + 1) = 2^(ℓ - i) := by rw [h1]
    have h3 : 2^(ℓ - (i + 1)) * 2 = 2^(ℓ - (i + 1) + 1) := by rw [pow_succ]
    rw [← h2, ← h3]; omega⟩
  set P₁_coeffs := fun j : Fin (2^(ℓ - (i + 1))) => coeffs ⟨j.val * 2 + 1, by
    have h1 : ℓ - (i + 1) + 1 = ℓ - i := by omega
    have h2 : 2^(ℓ - (i + 1) + 1) = 2^(ℓ - i) := by rw [h1]
    have h3 : 2^(ℓ - (i + 1)) * 2 = 2^(ℓ - (i + 1) + 1) := by rw [pow_succ]
    rw [← h2, ← h3]; omega⟩
  set P₀ := evenRefinement 𝔽q β h_ℓ_add_R_rate i coeffs
  set P₁ := oddRefinement 𝔽q β h_ℓ_add_R_rate i coeffs
  have h_P_i_eval := evaluation_poly_split_identity 𝔽q β h_ℓ_add_R_rate ⟨i, by omega⟩ coeffs
  -- Equation 39 : P^(i)(X) = P₀^(i+1)(q^(i)(X)) + X · P₁^(i+1)(q^(i)(X))
  have h_equation_39_x₀ : P_i.eval x₀.val = P₀.eval y.val + x₀.val * P₁.eval y.val := by
    simp only [h_P_i_eval, Fin.eta, Polynomial.eval_add, eval_comp,
      h_eval_qMap_x₀, Polynomial.eval_mul, Polynomial.eval_X, P_i, P₀, P₁]
  have h_equation_39_x₁ : P_i.eval x₁.val = P₀.eval y.val + x₁.val * P₁.eval y.val := by
    simp only [h_P_i_eval, Fin.eta, Polynomial.eval_add, eval_comp,
      h_eval_qMap_x₁, Polynomial.eval_mul, Polynomial.eval_X, P_i, P₀, P₁]
  set f_i := fun (x : (sDomain 𝔽q β h_ℓ_add_R_rate) ⟨i, by omega⟩) => P_i.eval (x.val : L)
  set f_i_plus_1 := fold (i := ⟨i, by omega⟩) (h_i := by omega) (f := f_i) (r_chal := r_chal)
  -- Unfold the definition of f_i_plus_1 using the fold function
  have h_fold_def : f_i_plus_1 y =
      f_i x₀ * ((1 - r_chal) * x₁.val - r_chal) +
      f_i x₁ * (r_chal - (1 - r_chal) * x₀.val) := rfl
  -- Main calculation following the outline
  calc f_i_plus_1 y
    = f_i x₀ * ((1 - r_chal) * x₁.val - r_chal) +
        f_i x₁ * (r_chal - (1 - r_chal) * x₀.val) := h_fold_def
    _ = P_i.eval x₀.val * ((1 - r_chal) * x₁.val - r_chal) +
        P_i.eval x₁.val * (r_chal - (1 - r_chal) * x₀.val) := by simp only [f_i]
    _ = (P₀.eval y.val + x₀.val * P₁.eval y.val) * ((1 - r_chal) * x₁.val - r_chal) +
        (P₀.eval y.val + x₁.val * P₁.eval y.val) * (r_chal - (1 - r_chal) * x₀.val) := by
      rw [h_equation_39_x₀, h_equation_39_x₁]
    _ = P₀.eval y.val * ((1 - r_chal) * x₁.val - r_chal + r_chal - (1 - r_chal) * x₀.val) +
        P₁.eval y.val * (x₀.val * ((1 - r_chal) * x₁.val - r_chal) +
          x₁.val * (r_chal - (1 - r_chal) * x₀.val)) := by ring
    _ = P₀.eval y.val * ((1 - r_chal) * (x₁.val - x₀.val)) +
        P₁.eval y.val * ((x₁.val - x₀.val) * r_chal) := by ring
    _ = P₀.eval y.val * (1 - r_chal) + P₁.eval y.val * r_chal := by rw [h_fiber_diff]; ring
    _ = P_i_plus_1.eval y.val := by
      simp only [P_i_plus_1, P₀, P₁, new_coeffs, evenRefinement, oddRefinement,
        intermediateEvaluationPoly]
      conv_lhs => enter [1]; rw [mul_comm, ←Polynomial.eval_C_mul]
      conv_lhs => enter [2]; rw [mul_comm, ←Polynomial.eval_C_mul]
      -- ⊢ eval y (C (1-r) * ∑...) + eval y (C r * ∑...) = eval y (∑...)
      rw [←Polynomial.eval_add]
      -- ⊢ poly_left.eval y = poly_right.eval y
      congr
      simp_rw [mul_sum, ←Finset.sum_add_distrib]
      -- We now prove that the terms inside the sums are equal for each index.
      apply Finset.sum_congr rfl
      intro j hj
      have h_j_lt : j.val < 2 ^ (ℓ - (↑i + 1)) := by
        rw [Nat.sub_add_eq]
        omega
      conv_lhs => enter [1]; rw [mul_comm (a := Polynomial.C (coeffs ⟨j.val * 2, by
        rw [←Nat.add_zero (j.val * 2)]
        apply mul_two_add_bit_lt_two_pow (c := ℓ - i) (a := j) (b := ℓ - (↑i + 1))
          (i := 0) (by omega) (by omega)⟩)), ←mul_assoc,
        mul_comm (a := Polynomial.C (1 - r_chal))]; rw [mul_assoc]
      conv_lhs => enter [2]; rw [mul_comm (a := Polynomial.C (coeffs ⟨j.val * 2 + 1, by
        apply mul_two_add_bit_lt_two_pow (c := ℓ - i) (a := j) (b := ℓ - (↑i + 1))
          (i := 1) (by omega) (by omega)⟩)), ←mul_assoc,
        mul_comm (a := Polynomial.C r_chal)]; rw [mul_assoc]
      conv_rhs => rw [mul_comm]
      rw [←mul_add]
      congr
      simp only [←Polynomial.C_mul, ←Polynomial.C_add]

/-- Given a point `v ∈ S^(0)`, extract the middle `steps` bits `{v_i, ..., v_{i+steps-1}}`
as a `Fin (2 ^ steps)`. -/
def extractMiddleFinMask (v : (sDomain 𝔽q β h_ℓ_add_R_rate) ⟨0, by exact pos_of_neZero r⟩)
    (i : Fin ℓ) (steps : ℕ) : Fin (2 ^ steps) := by
  let vToFin := AdditiveNTT.sDomainToFin 𝔽q β h_ℓ_add_R_rate ⟨0, by
    exact pos_of_neZero r⟩ (by simp only [add_pos_iff]; left; exact pos_of_neZero ℓ) v
  simp only [tsub_zero] at vToFin
  let middleBits := Nat.getMiddleBits (offset := i.val) (len := steps) (n := vToFin.val)
  exact ⟨middleBits, Nat.getMiddleBits_lt_two_pow⟩

/-- The equality polynomial eq̃(r, r') that evaluates to 1 when r = r' and 0 otherwise.
This is used in the final sumcheck identity : s_ℓ = c · eq̃(r, r') -/
def eqTilde {L : Type} [CommRing L] {ℓ : ℕ} (r r' : Fin ℓ → L) : L :=
  MvPolynomial.eval r' (MvPolynomial.eqPolynomial r)

end Essentials

section SoundnessTools
-- In this section, we use the generic notation `steps` instead of `ϑ` to avoid conflicts

/-!
### Binary Basefold Specific Code Definitions

Definitions specific to the Binary Basefold protocol based on the fundamentals document.
-/

/-- The Reed-Solomon code C^(i) for round i in Binary Basefold.
For each i ∈ {0, steps, ..., ℓ}, C(i) is the Reed-Solomon code
RS_{L, S⁽ⁱ⁾}[2^{ℓ+R-i}, 2^{ℓ-i}]. -/
def BBF_Code (i : Fin (ℓ + 1)) : Submodule L ((sDomain 𝔽q β h_ℓ_add_R_rate)
    ⟨i, by
      exact Nat.lt_of_le_of_lt (n := i) (k := r) (m := ℓ) (h₁ := by exact Fin.is_le i)
        (by exact lt_of_add_right_lt h_ℓ_add_R_rate)⟩ → L) :=
  let domain : (sDomain 𝔽q β h_ℓ_add_R_rate) ⟨i, by omega⟩ ↪ L :=
    ⟨fun x => x.val, fun x y h => by exact Subtype.ext h⟩
  ReedSolomon.code (domain := domain) (deg := 2^(ℓ - i.val))

/-- The (minimum) distance d_i of the code C^(i) : `dᵢ := 2^(ℓ + R - i) - 2^(ℓ - i) + 1` -/
def BBF_CodeDistance (ℓ 𝓡 : ℕ) (i : Fin (ℓ + 1)) : ℕ :=
  2^(ℓ + 𝓡 - i.val) - 2^(ℓ - i.val) + 1

/-- Disagreement set Δ : The set of points where two functions disagree.
For functions f^(i+ϑ) and g^(i+ϑ), this is {y ∈ S^(i+ϑ) | f^(i+ϑ)(y) ≠ g^(i+ϑ)(y)}. -/
def disagreementSet (i : Fin ℓ) (steps : ℕ) [NeZero steps] (h_i_add_steps : i.val + steps ≤ ℓ)
  (f g : OracleFunction 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) ⟨i.val + steps, by
    exact Nat.lt_add_of_pos_right_of_le (↑i + steps) ℓ 1 h_i_add_steps⟩) :
  Set ((sDomain 𝔽q β h_ℓ_add_R_rate) ⟨i.val + steps, by omega⟩) :=
  {y | f y ≠ g y}

/-- Fiber-wise disagreement set Δ^(i) : The set of points y ∈ S^(i+ϑ) for which
functions f^(i) and g^(i) are not identical when restricted to the entire fiber
of points in S⁽ⁱ⁾ that maps to y. -/
def fiberwiseDisagreementSet (i : Fin ℓ) (steps : ℕ) [NeZero steps]
    (h_i_add_steps : i.val + steps ≤ ℓ) (f g : OracleFunction 𝔽q β (h_ℓ_add_R_rate :=
      h_ℓ_add_R_rate) ⟨i, by omega⟩) :
  Set ((sDomain 𝔽q β h_ℓ_add_R_rate) ⟨i.val + steps, by omega⟩) :=
  -- The set of points `y ∈ S^{i+steps}` that there exists a
    -- point `x` in its fiber where `f x ≠ g x`
  {y | ∃ x, iteratedQuotientMap 𝔽q β h_ℓ_add_R_rate (i := i)
    (k := steps) (h_bound := by omega) x = y ∧ f x ≠ g x}

/-- Fiber-wise distance d^(i) : The minimum size of the fiber-wise disagreement set
between f^(i) and any codeword in C^(i). -/
def fiberwiseDistance (i : Fin ℓ) (steps : ℕ) [NeZero steps] (h_i_add_steps : i.val + steps ≤ ℓ)
  (f : OracleFunction 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) ⟨i.val, by omega⟩) : ℕ :=
  -- The minimum size of the fiber-wise disagreement set between f^(i) and any codeword in C^(i)
  -- d^(i)(f^(i), C^(i)) := min_{g^(i) ∈ C^(i)} |Δ^(i)(f^(i), g^(i))|
  let C_i := BBF_Code 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) ⟨i.val, by omega⟩
  let disagreement_sizes := (fun (g : C_i) =>
    (fiberwiseDisagreementSet 𝔽q β i steps h_i_add_steps f g).ncard) '' Set.univ
  sInf disagreement_sizes

/-- Fiberwise closeness : f^(i) is fiberwise close to C^(i) if
2 * d^(i)(f^(i), C^(i)) < d_{i+steps} -/
def fiberwiseClose (i : Fin ℓ) (steps : ℕ) [NeZero steps] (h_i_add_steps : i.val + steps ≤ ℓ)
    (f : OracleFunction 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
      ⟨i, by omega⟩) : Prop :=
  2 * fiberwiseDistance 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (i := i) steps
    (h_i_add_steps := h_i_add_steps) (f := f) < (BBF_CodeDistance ℓ 𝓡 ⟨i + steps, by omega⟩ : ℕ∞)

/-- Hamming closeness : f is close to C in Hamming distance if
2 * d(f, C) < d_i -/
def hammingClose (i : Fin (ℓ + 1)) (f : OracleFunction 𝔽q β
    (h_ℓ_add_R_rate := h_ℓ_add_R_rate) i) : Prop :=
  2 * Code.distFromCode (u := f)
    (C := BBF_Code 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) i) <
    (BBF_CodeDistance ℓ 𝓡 i : ℕ∞)

#check hammingClose 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
-- i (f := fun x => 0)
/-- Unique closest codeword : If a function f^(i) is within the unique decoding radius
of the code C^(i), then this gives the unique closest codeword using Berlekamp-Welch decoder. -/
def uniqueClosestCodeword
  (i : Fin (ℓ + 1)) (h_i : i < ℓ + 𝓡)
  (f : OracleFunction 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) ⟨i, i.isLt⟩)
  (h_within_radius : hammingClose 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) i f) :
  OracleFunction 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) ⟨i, i.isLt⟩
   := by
  -- Set up Berlekamp-Welch parameters
  set domain_size := Fintype.card (sDomain 𝔽q β h_ℓ_add_R_rate ⟨i, by omega⟩)
  set d := Code.distFromCode (u := f)
    (C := BBF_Code 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) ⟨i, by omega⟩)
  let e : ℕ := d.toNat
  have h_dist_ne_top : d ≠ ⊤ := by
    intro h_dist_eq_top
    unfold hammingClose at h_within_radius
    unfold d at h_dist_eq_top
    simp only [h_dist_eq_top, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, ENat.mul_top]
      at h_within_radius
    exact not_top_lt h_within_radius
  let k : ℕ := 2^(ℓ - i.val)  -- degree bound from BBF_Code definition
  -- Convert domain to Fin format for Berlekamp-Welch
  let domain_to_fin : (sDomain 𝔽q β h_ℓ_add_R_rate)
    ⟨i, by omega⟩ ≃ Fin domain_size := by
    simp only [domain_size]
    rw [sDomain_card 𝔽q β h_ℓ_add_R_rate
      (i := ⟨i, by omega⟩) (h_i := h_i)]
    have h_equiv := sDomainFinEquiv 𝔽q β
      h_ℓ_add_R_rate (i := ⟨i, by omega⟩) (h_i := h_i)
    convert h_equiv
    exact hF₂.out
  -- ωs is the mapping from the point index to the actually point in the domain S^{i}
  let ωs : Fin domain_size → L := fun j => (domain_to_fin.symm j).val
  let f_vals : Fin domain_size → L := fun j => f (domain_to_fin.symm j)
  -- Run Berlekamp-Welch decoder to get P(X) in monomial basis
  have domain_neZero : NeZero domain_size := by
    simp only [domain_size];
    rw [sDomain_card 𝔽q β h_ℓ_add_R_rate
      (i := ⟨i, by omega⟩) (h_i := h_i)]
    exact {
      out := by
        rw [hF₂.out]
        simp only [ne_eq, Nat.pow_eq_zero, OfNat.ofNat_ne_zero, false_and, not_false_eq_true]
    }
  let berlekamp_welch_result : Option L[X] := BerlekampWelch.decoder (F := L) e k ωs f_vals
  have h_ne_none : berlekamp_welch_result ≠ none := by
    -- 1) Choose a codeword achieving minimal Hamming distance (closest codeword).
    let C_i := BBF_Code 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) ⟨i, by omega⟩
    let S := (fun (g : C_i) => Δ₀(f, g)) '' Set.univ
    let SENat := (fun (g : C_i) => (Δ₀(f, g) : ENat)) '' Set.univ
      -- let S_nat := (fun (g : C_i) => hammingDist f g) '' Set.univ
    have hS_nonempty : S.Nonempty := Set.image_nonempty.mpr Set.univ_nonempty
    have h_coe_sinfS_eq_sinfSENat : ↑(sInf S) = sInf SENat := by
      rw [ENat.coe_sInf (hs := hS_nonempty)]
      simp only [SENat, Set.image_univ, sInf_range]
      simp only [S, Set.image_univ, iInf_range]
    rcases Nat.sInf_mem hS_nonempty with ⟨g_subtype, hg_subtype, hg_min⟩
    rcases g_subtype with ⟨g_closest, hg_mem⟩
    have h_dist_f : hammingDist f g_closest ≤ e := by
      rw [show e = d.toNat from rfl]
      -- The distance `d` is exactly the Hamming distance of `f` to `g_closest` (lifted to `ℕ∞`).
      have h_dist_eq_hamming : d = (hammingDist f g_closest) := by
        -- We found `g_closest` by taking the `sInf` of all distances, and `hg_min`
        -- shows that the distance to `g_closest` achieves this `sInf`.
        have h_distFromCode_eq_sInf : d = sInf SENat := by
          apply le_antisymm
          · -- Part 1 : `d ≤ sInf ...`
            simp only [d, distFromCode]
            apply sInf_le_sInf
            intro a ha
            -- `a` is in `SENat`, so `a = ↑Δ₀(f, g)` for some codeword `g`.
            rcases (Set.mem_image _ _ _).mp ha with ⟨g, _, rfl⟩
            -- We must show `a` is in the set for `d`, which is `{d' | ∃ v, ↑Δ₀(f, v) ≤ d'}`.
            -- We can use `g` itself as the witness `v`, since `↑Δ₀(f, g) ≤ ↑Δ₀(f, g)`.
            use g; simp only [Fin.eta, Subtype.coe_prop, le_refl, and_self]
          · -- Part 2 : `sInf ... ≤ d`
            simp only [d, distFromCode]
            apply le_sInf
            -- Let `d'` be any element in the set that `d` is the infimum of.
            intro d' h_d'
            -- Unpack `h_d'` : there exists some `v` in the code such that
            -- `↑(hammingDist f v) ≤ d'`.
            rcases h_d' with ⟨v, hv_mem, h_dist_v_le_d'⟩
            -- By definition, `sInf SENat` is a lower bound for all elements in `SENat`.
            -- The element `↑(hammingDist f v)` is in `SENat`.
            have h_sInf_le_dist_v : sInf SENat ≤ ↑(hammingDist f v) := by
              apply sInf_le -- ⊢ ↑Δ₀(f, v) ∈ SENat
              rw [Set.mem_image]
              -- ⊢ ∃ x ∈ Set.univ, ↑Δ₀(f, ↑x) = ↑Δ₀(f, v)
              simp only [Fin.eta, Set.mem_univ, Nat.cast_inj, true_and, Subtype.exists, exists_prop]
              -- ⊢ ∃ a ∈ C_i, Δ₀(f, a) = Δ₀(f, v)
              use v
              exact And.symm ⟨rfl, hv_mem⟩
            -- Now, chain the inequalities : `sInf SENat ≤ ↑(dist_to_any_v) ≤ d'`.
            exact h_sInf_le_dist_v.trans h_dist_v_le_d'
        rw [h_distFromCode_eq_sInf, ←h_coe_sinfS_eq_sinfSENat, ←hg_min]
      rw [h_dist_eq_hamming]
      rw [ENat.toNat_coe]
    -- Get the closest polynomial
    obtain ⟨p, hp_deg_lt, hp_eval⟩ : ∃ p, p ∈ Polynomial.degreeLT L k ∧
      (fun (x : sDomain 𝔽q β h_ℓ_add_R_rate (i := ⟨i, by omega⟩)) ↦ p.eval (↑x)) = g_closest := by
      simp only [Fin.eta, BBF_Code, ReedSolomon.code, ReedSolomon.evalOnPoints, Function.Embedding.coeFn_mk,
        Submodule.mem_map, LinearMap.coe_mk, AddHom.coe_mk, C_i] at hg_mem
      rcases hg_mem with ⟨p_witness, hp_prop, hp_eq⟩
      use p_witness
    have natDeg_p_lt_k : p.natDegree < k := by
      simp only [mem_degreeLT] at hp_deg_lt
      by_cases hi : i = ℓ
      · simp only [hi, tsub_self, pow_zero, cast_one, lt_one_iff, k] at ⊢ hp_deg_lt
        by_cases hp_p_eq_0 : p = 0
        · rw [hp_p_eq_0, Polynomial.natDegree_zero];
        · rw [Polynomial.natDegree_eq_of_degree_eq_some]
          have h_deg_p : p.degree = 0 := by
            have h_le_zero : p.degree ≤ 0 := by
              exact WithBot.lt_one_iff_le_zero.mp hp_deg_lt
            have h_deg_ne_bot : p.degree ≠ ⊥ := by
              rw [Polynomial.degree_ne_bot]; omega
            apply le_antisymm h_le_zero (zero_le_degree_iff.mpr hp_p_eq_0)
          simp only [h_deg_p, CharP.cast_eq_zero]
      · by_cases hp_p_eq_0 : p = 0
        · rw [hp_p_eq_0, Polynomial.natDegree_zero];
          have h_i_lt_ℓ : i < ℓ := by omega
          simp only [ofNat_pos, pow_pos, k]
        · rw [Polynomial.natDegree_lt_iff_degree_lt (by omega)]
          exact hp_deg_lt
    have h_decoder_succeeds : BerlekampWelch.decoder e k ωs f_vals = some p := by
      apply BerlekampWelch.decoder_eq_some
      · -- ⊢ `2 * e < d_i = n - k + 1`
        simp only [domain_size, k]; rw [sDomain_card 𝔽q β (h_i := by omega),]
        · -- ⊢ 2 * e < 2 ^ (ℓ + 𝓡 - ↑i) - 2 ^ (ℓ - ↑i) + 1
          simp only [hammingClose, BBF_CodeDistance, cast_add, ENat.coe_sub, cast_pow, cast_ofNat,
            cast_one] at h_within_radius;
          have h_lt_eq : ↑(2 * Δ₀(f, ↑(BBF_Code 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) i)).toNat) =
  2 * Δ₀(f, ↑(BBF_Code 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) i)) := by
            simp only [cast_mul, cast_ofNat]
            rw [ENat.coe_toNat]
            exact h_dist_ne_top
          apply ENat.coe_lt_coe.mp
          rw [h_lt_eq, hF₂.out]
          exact h_within_radius
      · -- ⊢ `k ≤ domain_size`. This holds by the problem setup.
        simp only [k, domain_size]
        rw [sDomain_card 𝔽q β (h_i := by omega), hF₂.out]
        apply Nat.pow_le_pow_right (by omega) -- ⊢ ℓ - ↑i ≤ ℓ + 𝓡 - ↑⟨↑i, ⋯⟩
        simp only [tsub_le_iff_right]
        omega
      · -- ⊢ Function.Injective ωs
        simp only [ωs]
        -- The composition of two injective functions (`Equiv.symm` and `Subtype.val`) is injective.
        exact Function.Injective.comp Subtype.val_injective (Equiv.injective _)
      · -- ⊢ `p.natDegree < k`. This is true from `hp_deg`.
        exact natDeg_p_lt_k
      · -- ⊢ `Δ₀(f_vals, (fun a ↦ Polynomial.eval a p) ∘ ωs) ≤ e`
        change hammingDist f_vals ((fun a ↦ Polynomial.eval a p) ∘ ωs) ≤ e
        simp only [ωs]
        have h_functions_eq : (fun a ↦ Polynomial.eval a p) ∘ ωs
          = g_closest ∘ domain_to_fin.symm := by
          ext j; simp only [Function.comp_apply, Fin.eta, ωs]
          rw [←hp_eval]
        rw [h_functions_eq]
        -- ⊢ Δ₀(f_vals, g_closest ∘ ⇑domain_to_fin.symm) ≤ e
        simp only [Fin.eta, ge_iff_le, f_vals]
        -- ⊢ Δ₀(fun j ↦ f (domain_to_fin.symm j), g_closest ∘ ⇑domain_to_fin.symm) ≤ e
        calc
          _ ≤ hammingDist f g_closest := by
            apply hammingDist_le_of_outer_comp_injective f g_closest domain_to_fin.symm
              (hg := by exact Equiv.injective domain_to_fin.symm)
          _ ≤ e := by exact h_dist_f
    simp only [ne_eq, berlekamp_welch_result]
    simp only [h_decoder_succeeds, reduceCtorEq, not_false_eq_true]
  let p : L[X] := berlekamp_welch_result.get (Option.ne_none_iff_isSome.mp h_ne_none)
  exact fun x => p.eval x.val

omit [CharP L 2] [NeZero ℓ] in
/-- if `d⁽ⁱ⁾(f⁽ⁱ⁾, C⁽ⁱ⁾) < d_{ᵢ₊steps} / 2` (fiberwise distance),
then `d(f⁽ⁱ⁾, C⁽ⁱ⁾) < dᵢ/2` (regular code distance) -/
theorem fiberwise_dist_lt_imp_dist_lt_unique_decoding_radius (i : Fin ℓ) (steps : ℕ)
    [NeZero steps] (h_i_add_steps : i.val + steps ≤ ℓ)
    (f : OracleFunction 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) ⟨i, by omega⟩)
  (h_fw_dist_lt : fiberwiseClose 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
    (i := i) (steps := steps) (h_i_add_steps := h_i_add_steps) (f := f)) :
  hammingClose 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) ⟨i, by omega⟩ f := by
  unfold fiberwiseClose at h_fw_dist_lt
  unfold hammingClose
  -- 2 * Δ₀(f, ↑(BBF_Code 𝔽q β ⟨↑i, ⋯⟩)) < ↑(BBF_CodeDistance ℓ 𝓡 ⟨↑i, ⋯⟩)
  let d_fw := fiberwiseDistance 𝔽q β (i := i) steps h_i_add_steps f
  let C_i := (BBF_Code 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) ⟨i, by omega⟩)
  let d_H := Code.distFromCode f C_i
  let d_i := BBF_CodeDistance ℓ 𝓡 (⟨i, by omega⟩)
  let d_i_plus_steps := BBF_CodeDistance ℓ 𝓡 ⟨i.val + steps, by omega⟩

  have h_d_i_gt_0 : d_i > 0 := by
    dsimp [d_i, BBF_CodeDistance] -- ⊢ 2 ^ (ℓ + 𝓡 - ↑i) - 2 ^ (ℓ - ↑i) + 1 > 0
    have h_exp_lt : ℓ - i.val < ℓ + 𝓡 - i.val := by
      exact Nat.sub_lt_sub_right (a := ℓ) (b := ℓ + 𝓡) (c := i.val) (by omega) (by
        apply Nat.lt_add_of_pos_right; exact pos_of_neZero 𝓡)
    have h_pow_lt : 2 ^ (ℓ - i.val) < 2 ^ (ℓ + 𝓡 - i.val) := by
      exact Nat.pow_lt_pow_right (by norm_num) h_exp_lt
    omega

  have h_C_i_nonempty : Nonempty C_i := by
    simp only [nonempty_subtype, C_i]
    exact Submodule.nonempty (BBF_Code 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) ⟨i.val, by omega⟩)

  -- 1. Relate Hamming distance `d_H` to fiber-wise distance `d_fw`.
  obtain ⟨g', h_g'_mem, h_g'_min_card⟩ : ∃ g' ∈ C_i, d_fw
    = (fiberwiseDisagreementSet 𝔽q β i steps h_i_add_steps f g').ncard := by
    -- Let `S` be the set of all possible fiber-wise disagreement sizes.
    let S := (fun (g : C_i) => (fiberwiseDisagreementSet 𝔽q β i steps h_i_add_steps
      f g).ncard) '' Set.univ
    -- The code `C_i` (a submodule) is non-empty, so `S` is also non-empty.
    have hS_nonempty : S.Nonempty := by
      refine Set.image_nonempty.mpr ?_

      exact Set.univ_nonempty
    -- For a non-empty set of natural numbers, `sInf` is an element of the set.
    have h_sInf_mem : sInf S ∈ S := Nat.sInf_mem hS_nonempty
    -- By definition, `d_fw = sInf S`.
    unfold d_fw at h_sInf_mem
    -- Since `sInf S` is in the image set `S`, there must be an element `g_subtype` in the domain
    -- (`C_i`) that maps to it. This `g_subtype` is the codeword we're looking for.
    rw [Set.mem_image] at h_sInf_mem
    rcases h_sInf_mem with ⟨g_subtype, _, h_eq⟩
    -- Extract the codeword and its membership proof.
    exact ⟨g_subtype.val, g_subtype.property, by exact id (Eq.symm h_eq)⟩

  -- The Hamming distance to any codeword `g'` is bounded by `d_fw * 2 ^ steps`.
  have h_dist_le_fw_dist_times_fiber_size : (hammingDist f g' : ℕ∞) ≤ d_fw * 2 ^ steps := by
    -- This proves `dist f g' ≤ (fiberwiseDisagreementSet ... f g').ncard * 2 ^ steps`
    -- and lifts to ℕ∞. We prove the `Nat` version `hammingDist f g' ≤ ...`,
    -- which is equivalent.
    change (Δ₀(f, g') : ℕ∞) ≤ ↑d_fw * ((2 ^ steps : ℕ) : ℕ∞)
    rw [←ENat.coe_mul, ENat.coe_le_coe, h_g'_min_card]
    -- Let ΔH be the finset of actually bad x points where f and g' disagree.
    set ΔH := Finset.filter (fun x => f x ≠ g' x) Finset.univ
    have h_dist_eq_card : hammingDist f g' = ΔH.card := by
      simp only [hammingDist, ne_eq, ΔH]
    rw [h_dist_eq_card]
    -- Y_bad is the set of quotient points y that THERE EXISTS a bad fiber point x
    set Y_bad := fiberwiseDisagreementSet 𝔽q β i steps h_i_add_steps f g'
    simp only at * -- simplify domain indices everywhere

    -- ⊢ #ΔH ≤ Y_bad.ncard * 2 ^ steps

    have hFinType_Y_bad : Fintype Y_bad := by exact Fintype.ofFinite ↑Y_bad
    -- Every point of disagreement `x` must belong to a fiber over some `y` in `Y_bad`,
    -- BY DEFINITION of `Y_bad`. Therefore, `ΔH` is a subset of the union of the fibers
    -- of `Y_bad`
    have h_ΔH_subset_bad_fiber_points : ΔH ⊆ Finset.biUnion Y_bad.toFinset
        (t := fun y => ((qMap_total_fiber 𝔽q β (i := ⟨i, by omega⟩) (steps := steps)
          (h_i_add_steps := by apply Nat.lt_add_of_pos_right_of_le; omega) (y := y)) ''
          (Finset.univ : Finset (Fin ((2:ℕ)^steps)))).toFinset) := by
      -- ⊢ If any x ∈ ΔH, then x ∈ Union(qMap_total_fiber(y), ∀ y ∈ Y_bad)
      intro x hx_in_ΔH; -- ⊢ x ∈ Union(qMap_total_fiber(y), ∀ y ∈ Y_bad)
      simp only [ΔH, Finset.mem_filter] at hx_in_ΔH
      -- Now we actually apply iterated qMap into x to get y_of_x,
      -- then x ∈ qMap_total_fiber(y_of_x) by definition
      let y_of_x := iteratedQuotientMap 𝔽q β h_ℓ_add_R_rate i steps h_i_add_steps x
      apply Finset.mem_biUnion.mpr; use y_of_x
      -- ⊢ y_of_x ∈ Y_bad.toFinset ∧ x ∈ qMap_total_fiber(y_of_x)
      have h_elemenet_Y_bad :  y_of_x ∈ Y_bad.toFinset := by
        -- ⊢ y ∈ Y_bad.toFinset
        simp only [fiberwiseDisagreementSet, iteratedQuotientMap, ne_eq, Subtype.exists,
          Set.toFinset_setOf, mem_filter, mem_univ, true_and, Y_bad]
        -- one bad fiber point of y_of_x is x itself
        let X := x.val
        have h_X_in_source : X ∈ sDomain 𝔽q β h_ℓ_add_R_rate (i := ⟨i, by omega⟩) := by
          exact Submodule.coe_mem x
        use X
        use h_X_in_source
        -- ⊢ Ŵ_steps⁽ⁱ⁾(X) = y (iterated quotient map) ∧ ¬f ⟨X, ⋯⟩ = g' ⟨X, ⋯⟩
        have h_forward_iterated_qmap : Polynomial.eval X
            (intermediateNormVpoly 𝔽q β h_ℓ_add_R_rate ⟨↑i, by omega⟩
              ⟨steps, by simp only; omega⟩) = y_of_x := by
          simp only [iteratedQuotientMap, X, y_of_x];
        have h_eval_diff : f ⟨X, by omega⟩ ≠ g' ⟨X, by omega⟩ := by
          unfold X
          simp only [Subtype.coe_eta, ne_eq, hx_in_ΔH, not_false_eq_true]
        simp only [h_forward_iterated_qmap, Subtype.coe_eta, h_eval_diff,
          not_false_eq_true, and_self]
      simp only [h_elemenet_Y_bad, true_and]

      set qMapFiber := qMap_total_fiber 𝔽q β (i := ⟨i, by omega⟩) (steps := steps)
        (h_i_add_steps := by apply Nat.lt_add_of_pos_right_of_le; omega) (y := y_of_x)
      simp only [coe_univ, Set.image_univ, Set.toFinset_range, mem_image, mem_univ, true_and]
      use (pointToIterateQuotientIndex (i := ⟨i, by omega⟩) (steps := steps)
        (h_i_add_steps := by omega) (x := x))
      have h_res := is_fiber_iff_generates_quotient_point 𝔽q β i steps (by omega)
        (x := x) (y := y_of_x).mp (by rfl)
      exact h_res
    -- ⊢ #ΔH ≤ Y_bad.ncard * 2 ^ steps
    -- The cardinality of a subset is at most the cardinality of the superset.
    apply (Finset.card_le_card h_ΔH_subset_bad_fiber_points).trans
    -- The cardinality of a disjoint union is the sum of cardinalities.
    rw [Finset.card_biUnion]
    · -- The size of the sum is the number of bad fibers (`Y_bad.ncard`) times
      -- the size of each fiber (`2 ^ steps`).
      simp only [Set.toFinset_card]
      have h_card_fiber_per_quotient_point := card_qMap_total_fiber 𝔽q β
        (h_ℓ_add_R_rate := h_ℓ_add_R_rate) i steps h_i_add_steps
      simp only [Set.image_univ, Fintype.card_ofFinset,
        Subtype.forall] at h_card_fiber_per_quotient_point
      have h_card_fiber_of_each_y : ∀ y ∈ Y_bad.toFinset,
          Fintype.card ((qMap_total_fiber 𝔽q β (i := ⟨↑i, by omega⟩) (steps := steps)
            (h_i_add_steps := by apply Nat.lt_add_of_pos_right_of_le; omega) (y := y)) ''
            ↑(Finset.univ : Finset (Fin ((2:ℕ)^steps)))) = 2 ^ steps := by
        intro y hy_in_Y_bad
        have hy_card_fiber_of_y := h_card_fiber_per_quotient_point (a := y) (b := by
          exact Submodule.coe_mem y)
        simp only [coe_univ, Set.image_univ, Fintype.card_ofFinset, hy_card_fiber_of_y]
      rw [Finset.sum_congr rfl h_card_fiber_of_each_y]
      -- ⊢ ∑ x ∈ Y_bad.toFinset, 2 ^ steps ≤ Y_bad.encard.toNat * 2 ^ steps
      simp only [sum_const, Set.toFinset_card, smul_eq_mul, ofNat_pos, pow_pos,
        _root_.mul_le_mul_right, ge_iff_le]
      conv_rhs => rw [←_root_.Nat.card_coe_set_eq] -- convert .ncard back to .card
      -- ⊢ Fintype.card ↑Y_bad ≤ Nat.card ↑Y_bad
      simp only [card_eq_fintype_card, le_refl]
    · -- Prove that the fibers for distinct quotient points y₁, y₂ are disjoint.
      intro y₁ hy₁ y₂ hy₂ hy_ne
      have h_disjoint := qMap_total_fiber_disjoint (i := ⟨↑i, by omega⟩) (steps := steps)
        (h_i_add_steps := by omega) (y₁ := y₁) (y₂ := y₂) (hy_ne := hy_ne)
      simp only [Function.onFun, coe_univ]
      exact h_disjoint

  -- The minimum distance `d_H` is bounded by the distance to this specific `g'`.
  have h_dist_bridge : d_H ≤ d_fw * 2 ^ steps := by
    -- exact h_dist_le_fw_dist_times_fiber_size
    apply le_trans (a := d_H) (c := d_fw * 2 ^ steps) (b := hammingDist f g')
    · -- ⊢ d_H ≤ ↑Δ₀(f, g')
      simp only [distFromCode, SetLike.mem_coe, hammingDist, ne_eq, d_H];
      -- ⊢ Δ₀(f, C_i) ≤ ↑Δ₀(f, g')
      -- ⊢ sInf {d | ∃ v ∈ C_i, ↑(#{i | f i ≠ v i}) ≤ d} ≤ ↑(#{i | f i ≠ g' i})
      apply sInf_le
      use g'
    · exact h_dist_le_fw_dist_times_fiber_size

  -- 2. Use the premise : `2 * d_fw < d_{i+steps}`.
  -- As a `Nat` inequality, this is equivalent to `2 * d_fw ≤ d_{i+steps} - 1`.
  have h_fw_bound : 2 * d_fw ≤ d_i_plus_steps - 1 := by
    -- Convert the ENat inequality to a Nat inequality using `a < b ↔ a + 1 ≤ b`.
    exact Nat.le_of_lt_succ (WithTop.coe_lt_coe.1 h_fw_dist_lt)

  -- 3. The Algebraic Identity.
  -- The core of the proof is the identity : `(d_{i+steps} - 1) * 2 ^ steps = d_i - 1`.
  have h_algebraic_identity : (d_i_plus_steps - 1) * 2 ^ steps = d_i - 1 := by
    dsimp [d_i, d_i_plus_steps, BBF_CodeDistance]
    rw [Nat.sub_mul, ←Nat.pow_add, ←Nat.pow_add];
    have h1 : ℓ + 𝓡 - (↑i + steps) + steps = ℓ + 𝓡 - i := by
      rw [Nat.sub_add_eq_sub_sub_rev (h1 := by omega) (h2 := by omega),
        Nat.add_sub_cancel (n := i) (m := steps)]
    have h2 : (ℓ - (↑i + steps) + steps) = ℓ - i := by
      rw [Nat.sub_add_eq_sub_sub_rev (h1 := by omega) (h2 := by omega),
        Nat.add_sub_cancel (n := i) (m := steps)]
    rw [h1, h2]

  -- 4. Conclusion : Chain the inequalities to prove `2 * d_H < d_i`.
  -- We know `d_H` is finite, since `C_i` is nonempty.
  have h_dH_ne_top : d_H ≠ ⊤ := by
    simp only [ne_eq, d_H]
    rw [Code.distFromCode_eq_top_iff_empty f C_i]
    exact Set.nonempty_iff_ne_empty'.mp h_C_i_nonempty

  -- We can now work with the `Nat` value of `d_H`.
  let d_H_nat := ENat.toNat d_H
  have h_dH_eq : d_H = d_H_nat := (ENat.coe_toNat h_dH_ne_top).symm

  -- The calculation is now done entirely in `Nat`.
  have h_final_inequality : 2 * d_H_nat ≤ d_i - 1 := by
    have h_bridge_nat : d_H_nat ≤ d_fw * 2 ^ steps := by
        rw [←ENat.coe_le_coe]
        exact le_of_eq_of_le (id (Eq.symm h_dH_eq)) h_dist_bridge
    calc 2 * d_H_nat
      _ ≤ 2 * (d_fw * 2 ^ steps) := by gcongr
      _ = (2 * d_fw) * 2 ^ steps := by rw [mul_assoc]
      _ ≤ (d_i_plus_steps - 1) * 2 ^ steps := by gcongr;
      _ = d_i - 1 := h_algebraic_identity

  simp only [d_H, d_H_nat] at h_dH_eq
  -- This final line is equivalent to the goal statement.
  rw [h_dH_eq]
  -- ⊢ 2 * ↑Δ₀(f, C_i).toNat < ↑(BBF_CodeDistance ℓ 𝓡 ⟨↑i, ⋯⟩)
  change ((2 : ℕ) : ℕ∞) * ↑Δ₀(f, C_i).toNat < ↑(BBF_CodeDistance ℓ 𝓡 ⟨↑i, by omega⟩)
  rw [←ENat.coe_mul, ENat.coe_lt_coe]
  apply Nat.lt_of_le_pred (n := 2 * Δ₀(f, C_i).toNat) (m := d_i) (h := h_d_i_gt_0)
    (h_final_inequality)

/--
Compliance condition (Definition 4.17) : For an index `i` that is a multiple of `steps`,
the oracle `f_i` is compliant if it's close to the code fiber-wise, the next oracle
`f_i_plus_steps` is close to its code, and their unique closest codewords are consistent
with folding.
-/
def isCompliant (i : Fin (ℓ)) (steps : ℕ) [NeZero steps]
  (h_i_add_steps : i + steps ≤ ℓ)
  (f_i : OracleFunction 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) ⟨i, by omega⟩)
  (f_i_plus_steps : OracleFunction 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
      ⟨i + steps, by omega⟩)
  (challenges : Fin steps → L) : Prop :=
  ∃ (h_fw_dist_lt : 2 * fiberwiseDistance 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (i := i)
      (steps := steps) h_i_add_steps f_i < (BBF_CodeDistance ℓ 𝓡 ⟨i + steps, by omega⟩ : ℕ∞))
    (h_dist_next_lt : 2 * distFromCode f_i_plus_steps
      (BBF_Code 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) ⟨i + steps, by omega⟩)
      < (BBF_CodeDistance ℓ 𝓡 ⟨i + steps, by omega⟩ : ℕ∞)), -- note that two lts are equal
    -- Third constraint : the DECODED codewords are consistent via the iterated_fold
    let h_dist_curr_lt := fiberwise_dist_lt_imp_dist_lt_unique_decoding_radius 𝔽q β
      (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (i := i) steps h_i_add_steps f_i
      (h_fw_dist_lt := h_fw_dist_lt)
    let f_bar_i := uniqueClosestCodeword 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
      (i := ⟨i, by omega⟩) (h_i := fin_ℓ_lt_ℓ_add_R i) f_i h_dist_curr_lt
    let f_bar_i_plus_steps := uniqueClosestCodeword 𝔽q β
      (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (i := ⟨i + steps, by omega⟩)
      (h_i := fin_ℓ_steps_lt_ℓ_add_R i steps h_i_add_steps)
      f_i_plus_steps h_dist_next_lt
    iterated_fold 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
      (steps := ⟨steps, by apply Nat.lt_succ_of_le; exact Nat.le_of_add_left_le h_i_add_steps⟩)
      (i := ⟨i, by omega⟩)
      (h_i_add_steps := by simp only; exact fin_ℓ_steps_lt_ℓ_add_R i steps h_i_add_steps)
      f_bar_i challenges = f_bar_i_plus_steps

omit [CharP L 2] [NeZero ℓ] in
/--
Farness implies non-compliance. If `f_i` is far from its code `C_i`, it cannot be
compliant. This follows directly from the contrapositive of
`fiberwise_dist_lt_imp_dist_lt`.
-/
lemma farness_implies_non_compliance (i : Fin ℓ) (steps : ℕ) [NeZero steps]
  (h_i_add_steps : i + steps ≤ ℓ)
  (f_i : OracleFunction 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) ⟨i, by omega⟩)
  (f_i_plus_steps : OracleFunction 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
    ⟨i + steps, by omega⟩)
  (challenges : Fin steps → L)
  (h_far : 2 * Code.distFromCode f_i
      (BBF_Code 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) ⟨i, by omega⟩)
    ≥ (BBF_CodeDistance ℓ 𝓡 ⟨i, by omega⟩ : ℕ∞)) :
  ¬ isCompliant 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (i := i) (steps := steps)
    h_i_add_steps f_i f_i_plus_steps challenges :=
by -- We use our key theorem that "fiber-wise close" implies "Hamming close".
  intro h_compliant
  rcases h_compliant with ⟨h_fw_dist_lt, _, _⟩
  have h_close := fiberwise_dist_lt_imp_dist_lt_unique_decoding_radius 𝔽q β
    (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (i := i) (steps := steps) h_i_add_steps f_i
    h_fw_dist_lt
  have h_not_far := LT.lt.not_ge h_close
  exact h_not_far h_far

/--
Bad event for folding (Definition 4.19) : This event captures two scenarios where the
random folding challenges undermine the protocol's soundness checks.
For `i ∈ {0, ..., ℓ - steps}`,
- In case `d⁽ⁱ⁾(f⁽ⁱ⁾, C⁽ⁱ⁾) < dᵢ₊steps / 2` :
  `Δ⁽ⁱ⁾(f⁽ⁱ⁾, f̄⁽ⁱ⁾) ⊄ Δ(fold(f⁽ⁱ⁾, rᵢ', ..., rᵢ₊steps₋₁'), fold(f̄⁽ⁱ⁾, rᵢ', ..., rᵢ₊steps₋₁'))`
- In case `d⁽ⁱ⁾(f⁽ⁱ⁾, C⁽ⁱ⁾) ≥ dᵢ₊steps / 2` :
  `d(fold(f⁽ⁱ⁾, rᵢ', ..., rᵢ₊steps₋₁'), C⁽ⁱ⁺steps⁾) < dᵢ₊steps / 2`
-/
def foldingBadEvent (i : Fin ℓ) (steps : ℕ) [NeZero steps] (h_i_add_steps : i + steps ≤ ℓ)
  (f_i : OracleFunction 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) ⟨i, by omega⟩)
  (challenges : Fin steps → L) : Prop :=
  let d_i_plus_steps := BBF_CodeDistance ℓ 𝓡 ⟨i + steps, by omega⟩
  if h_is_close : 2 * fiberwiseDistance 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (i := i)
      steps h_i_add_steps f_i < (d_i_plus_steps : ℕ∞) then
    -- Case 1 : The oracle `f_i` is fiber-wise "close" to the code.
    -- The bad event is when folding causes disagreements to vanish, violating Lemma 4.18.
    -- This happens if the random challenges are unlucky.
    let h_dist_curr_lt := fiberwise_dist_lt_imp_dist_lt_unique_decoding_radius 𝔽q β
      (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (i := i) (steps := steps) h_i_add_steps f_i h_is_close

    let f_bar_i := uniqueClosestCodeword 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
      (i := ⟨i, by omega⟩) (h_i := by apply Nat.lt_add_of_pos_right_of_le; omega) f_i
      h_dist_curr_lt
    let folded_f_i := iterated_fold 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
      (steps := ⟨steps, by omega⟩) (i := ⟨i, by omega⟩)
      (h_i_add_steps := by apply Nat.lt_add_of_pos_right_of_le; omega) f_i challenges
    let folded_f_bar_i := iterated_fold 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
      (steps := ⟨steps, by omega⟩) (i := ⟨i, by omega⟩)
      (h_i_add_steps := by apply Nat.lt_add_of_pos_right_of_le; omega) f_bar_i challenges

    let fiberwise_disagreements := fiberwiseDisagreementSet 𝔽q β i steps h_i_add_steps
      f_i f_bar_i
    let folded_disagreements := disagreementSet 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) i steps
      h_i_add_steps folded_f_i folded_f_bar_i
    -- The bad event is that the subset relation does NOT hold.
    ¬ (fiberwise_disagreements ⊆ folded_disagreements)
  else
    -- Case 2 : The oracle `f_i` is fiber-wise "far" from the code.
    -- Folding a "far" function should result in another "far" function.
    -- The bad event is when folding makes this far function appear "close" to the code.
    let folded_f_i := iterated_fold 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
      (steps := ⟨steps, by omega⟩) (i := ⟨i, by omega⟩)
      (h_i_add_steps := by simp only; apply Nat.lt_add_of_pos_right_of_le; omega) f_i challenges
    let dist_to_code := distFromCode folded_f_i
      (BBF_Code 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) ⟨i + steps, by omega⟩)
    2 * dist_to_code < (d_i_plus_steps : ℕ∞)

end SoundnessTools
end
end Binius.BinaryBasefold

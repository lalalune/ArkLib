/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.W2WindowHalfCount

/-!
# The window packing law: bad scalars form a partial Steiner system (#371)

The w-general form of the `w = 2` secant-disjointness law.  For a genuinely
rational coprime stack at any below-UDR slack `w` with kernel freedom
`j := 3w + k − 1 − n ≥ 0`:

* every bad scalar's missing set `T_γ = D ∖ Agr_γ` has size in `[w − j, w]`;
* two DISTINCT bad scalars' missing sets share at most `j` points — if they shared
  `j + 1`, the agreement sets would share `≥ n − 2w + j + 1 = w + k` points, forcing
  the secant bracket `(γ−γ')·R₁ − (P_γ−P_{γ'})·ℓ₁` (degree ≤ `w + k − 1`) to vanish,
  i.e. `ℓ₁ ∣ R₁` — contradicting genuineness;
* hence no `(j+1)`-subset of the domain lies in two missing sets, and double
  counting gives

  **`#bad · C(w−j, j+1) ≤ C(n, j+1)`.**

At `j = 0` this is `#bad ≤ n/w` — attained exactly by the `μ_w`-coset family
(`ℓ = X^w − e`, DISPROOF_LOG 2026-06-12), so the law is SHARP at the first
beyond-ladder slice for every `w ∣ n`.  At `w = 2` it recovers `2·#bad ≤ n`
(`W2WindowHalfCount`).  For production-rate windows the right side stays far below
the field budget, carrying `WindowRationalLinear` on the low-`j` window strata.
-/

open Finset Polynomial
open scoped NNReal ENNReal

namespace ProximityGap.WBPencil

open ProximityGap.SpikeFloor

variable {F : Type} [Field F] [Fintype F] [DecidableEq F]
variable {n : ℕ} [NeZero n]

/-- General degree bound for the agreement residual. -/
theorem w2Residual_natDegree_le_general {ℓ₀ ℓ₁ R₀ R₁ P : F[X]} {γ : F} {k w : ℕ}
    (hk : 1 ≤ k)
    (hℓ₀d : ℓ₀.natDegree ≤ w) (hℓ₁d : ℓ₁.natDegree ≤ w)
    (hR₀d : R₀.natDegree ≤ w + k - 1) (hR₁d : R₁.natDegree ≤ w + k - 1)
    (hPd : P.natDegree ≤ k - 1) :
    (w2Residual ℓ₀ ℓ₁ R₀ R₁ P γ).natDegree ≤ 2 * w + k - 1 := by
  rw [w2Residual]
  refine le_trans (natDegree_sub_le _ _) (max_le (le_trans (natDegree_add_le _ _)
    (max_le ?_ ?_)) ?_)
  · calc (ℓ₁ * R₀).natDegree ≤ ℓ₁.natDegree + R₀.natDegree := natDegree_mul_le
      _ ≤ w + (w + k - 1) := Nat.add_le_add hℓ₁d hR₀d
      _ ≤ 2 * w + k - 1 := by omega
  · calc (C γ * (ℓ₀ * R₁)).natDegree
        ≤ (C γ).natDegree + (ℓ₀ * R₁).natDegree := natDegree_mul_le
      _ ≤ 0 + (ℓ₀.natDegree + R₁.natDegree) :=
          Nat.add_le_add (le_of_eq (natDegree_C _)) natDegree_mul_le
      _ ≤ 0 + (w + (w + k - 1)) :=
          Nat.add_le_add_left (Nat.add_le_add hℓ₀d hR₁d) 0
      _ ≤ 2 * w + k - 1 := by omega
  · calc (P * (ℓ₀ * ℓ₁)).natDegree
        ≤ P.natDegree + (ℓ₀ * ℓ₁).natDegree := natDegree_mul_le
      _ ≤ (k - 1) + (ℓ₀.natDegree + ℓ₁.natDegree) :=
          Nat.add_le_add hPd natDegree_mul_le
      _ ≤ (k - 1) + (w + w) := by omega
      _ ≤ 2 * w + k - 1 := by omega

section Packing

variable (dom : Fin n ↪ F) {k w : ℕ}
variable {ℓ₀ ℓ₁ R₀ R₁ : F[X]}

open Classical in
/-- **The general secant forcing**: two scalars with degree-`< k` explainers whose
agreement sets share `≥ w + k` points are equal (genuine `u₁`). -/
theorem shared_forces_eq_general (hk : 1 ≤ k)
    (hℓ₁d : ℓ₁.natDegree ≤ w) (hR₁d : R₁.natDegree ≤ w + k - 1)
    (hℓ₀v : ∀ i : Fin n, ℓ₀.eval (dom i) ≠ 0)
    (hgen₁ : ¬ ℓ₁ ∣ R₁)
    {γ γ' : F} {P P' : F[X]}
    (hPd : P.natDegree ≤ k - 1) (hP'd : P'.natDegree ≤ k - 1)
    {I : Finset (Fin n)} (hIcard : w + k ≤ I.card)
    (hI : ∀ i ∈ I, (w2Residual ℓ₀ ℓ₁ R₀ R₁ P γ).eval (dom i) = 0 ∧
      (w2Residual ℓ₀ ℓ₁ R₀ R₁ P' γ').eval (dom i) = 0) :
    γ = γ' := by
  by_contra hne
  set B : F[X] := C (γ - γ') * R₁ - (P - P') * ℓ₁ with hB
  have hBvan : ∀ i ∈ I, B.eval (dom i) = 0 := by
    intro i hi
    obtain ⟨h1, h2⟩ := hI i hi
    have hdiff : (w2Residual ℓ₀ ℓ₁ R₀ R₁ P γ
        - w2Residual ℓ₀ ℓ₁ R₀ R₁ P' γ').eval (dom i) = 0 := by
      rw [eval_sub, h1, h2, sub_zero]
    have hfact : w2Residual ℓ₀ ℓ₁ R₀ R₁ P γ - w2Residual ℓ₀ ℓ₁ R₀ R₁ P' γ'
        = ℓ₀ * B := by
      rw [hB, w2Residual, w2Residual, C_sub]
      ring
    rw [hfact, eval_mul] at hdiff
    exact (mul_eq_zero.mp hdiff).resolve_left (hℓ₀v i)
  have hBdeg : B.natDegree ≤ w + k - 1 := by
    rw [hB]
    refine le_trans (natDegree_sub_le _ _) (max_le ?_ ?_)
    · calc (C (γ - γ') * R₁).natDegree
          ≤ (C (γ - γ')).natDegree + R₁.natDegree := natDegree_mul_le
        _ ≤ 0 + (w + k - 1) := Nat.add_le_add (le_of_eq (natDegree_C _)) hR₁d
        _ = w + k - 1 := by omega
    · calc ((P - P') * ℓ₁).natDegree
          ≤ (P - P').natDegree + ℓ₁.natDegree := natDegree_mul_le
        _ ≤ (k - 1) + w :=
            Nat.add_le_add (le_trans (natDegree_sub_le _ _)
              (max_le hPd hP'd)) hℓ₁d
        _ ≤ w + k - 1 := by omega
  have hB0 : B = 0 := by
    refine eq_zero_of_vanishing_card_gt dom hBvan ?_
    omega
  have hdvd : ℓ₁ ∣ C (γ - γ') * R₁ := by
    refine ⟨P - P', ?_⟩
    have := sub_eq_zero.mp hB0
    linear_combination this
  have h2 : ℓ₁ ∣ C (γ - γ')⁻¹ * (C (γ - γ') * R₁) := Dvd.dvd.mul_left hdvd _
  have h3 : C (γ - γ')⁻¹ * (C (γ - γ') * R₁) = R₁ := by
    rw [← mul_assoc, ← C_mul, inv_mul_cancel₀ (sub_ne_zero.mpr hne), C_1, one_mul]
  exact hgen₁ (h3 ▸ h2)

open Classical in
/-- **The window explainer, general slack**: every bad scalar has an explainer whose
full agreement set has size in `[n − w, 2w + k − 1]`. -/
theorem window_explainer (hk : 1 ≤ k)
    (hℓ₀d : ℓ₀.natDegree ≤ w) (hℓ₁d : ℓ₁.natDegree ≤ w)
    (hR₀d : R₀.natDegree ≤ w + k - 1) (hR₁d : R₁.natDegree ≤ w + k - 1)
    (hℓ₀v : ∀ i : Fin n, ℓ₀.eval (dom i) ≠ 0)
    (hℓ₁v : ∀ i : Fin n, ℓ₁.eval (dom i) ≠ 0)
    (hcop : IsCoprime ℓ₀ ℓ₁) (hgen₀ : ¬ ℓ₀ ∣ R₀)
    {δ : ℝ≥0} (hδn : δ * (Fintype.card (Fin n) : ℝ≥0) ≤ w) {γ : F}
    (hbad : mcaEvent (F := F)
      ((rsCode dom k : Submodule F (Fin n → F)) : Set (Fin n → F)) δ
      (fun i => R₀.eval (dom i) / ℓ₀.eval (dom i))
      (fun i => R₁.eval (dom i) / ℓ₁.eval (dom i)) γ) :
    ∃ P : F[X], P.natDegree ≤ k - 1 ∧
      n - w ≤ (w2Agr dom ℓ₀ ℓ₁ R₀ R₁ P γ).card ∧
      (w2Agr dom ℓ₀ ℓ₁ R₀ R₁ P γ).card ≤ 2 * w + k - 1 := by
  obtain ⟨S, hsz, ⟨c, hc, hag⟩, -⟩ := hbad
  obtain ⟨P, hPdeg, rfl⟩ := hc
  have hPd : P.natDegree ≤ k - 1 := by
    by_cases hP0 : P = 0
    · subst hP0; simp
    · have := (Polynomial.natDegree_lt_iff_degree_lt hP0).mpr hPdeg
      omega
  refine ⟨P, hPd, ?_, ?_⟩
  · -- witness size: n − w ≤ S.card ≤ Agr.card
    have hsize : n ≤ S.card + w := by
      have h1 : ((n - w : ℕ) : ℝ≥0) ≤ (S.card : ℝ≥0) := by
        have hnw : ((n - w : ℕ) : ℝ≥0) = (n : ℝ≥0) - (w : ℝ≥0) := by
          rw [Nat.cast_tsub]
        have hcardn : (Fintype.card (Fin n) : ℝ≥0) = (n : ℝ≥0) := by
          rw [Fintype.card_fin]
        calc ((n - w : ℕ) : ℝ≥0) = (n : ℝ≥0) - (w : ℝ≥0) := hnw
          _ ≤ (n : ℝ≥0) - δ * (Fintype.card (Fin n) : ℝ≥0) := by
              exact tsub_le_tsub_left (by rw [hcardn] at hδn ⊢; exact hδn) _
          _ = (1 - δ) * (Fintype.card (Fin n) : ℝ≥0) := by
              rw [tsub_mul, one_mul, hcardn]
          _ ≤ (S.card : ℝ≥0) := hsz
      have : (n - w : ℕ) ≤ S.card := by exact_mod_cast h1
      omega
    have hsub : S ⊆ w2Agr dom ℓ₀ ℓ₁ R₀ R₁ P γ := by
      intro i hi
      rw [w2Agr, Finset.mem_filter]
      refine ⟨Finset.mem_univ _, ?_⟩
      rw [w2Residual_eval_zero_iff (hℓ₀v i) (hℓ₁v i)]
      have := hag i hi
      simpa [smul_eq_mul] using this
    have := Finset.card_le_card hsub
    omega
  · by_contra hbig
    push_neg at hbig
    have hM0 : w2Residual ℓ₀ ℓ₁ R₀ R₁ P γ = 0 := by
      refine eq_zero_of_vanishing_card_gt dom
        (S := w2Agr dom ℓ₀ ℓ₁ R₀ R₁ P γ) (fun i hi => ?_) ?_
      · rw [w2Agr, Finset.mem_filter] at hi
        exact hi.2
      · have := w2Residual_natDegree_le_general (γ := γ) (w := w)
          hk hℓ₀d hℓ₁d hR₀d hR₁d hPd
        omega
    exact w2Residual_ne_zero hcop hgen₀ hM0

open Classical in
/-- **THE WINDOW PACKING LAW**: for a genuinely rational coprime stack at slack `w`
in the window stratum `n + j = 3w + k - 1` with `j ≤ w`, the missing sets of distinct
bad scalars intersect in ≤ `j` points, hence

`#bad · C(w − j, j + 1) ≤ C(n, j + 1)`.

Sharp at `j = 0` (`#bad ≤ n/w`, attained by the `μ_w`-coset family); at `w = 2` it
is the `2·#bad ≤ n` law. -/
theorem window_packing_law (hk : 1 ≤ k) {j : ℕ} (hj : n + j = 3 * w + k - 1)
    (hjw : j ≤ w) (hwn : w ≤ n)
    (hℓ₀d : ℓ₀.natDegree ≤ w) (hℓ₁d : ℓ₁.natDegree ≤ w)
    (hR₀d : R₀.natDegree ≤ w + k - 1) (hR₁d : R₁.natDegree ≤ w + k - 1)
    (hℓ₀v : ∀ i : Fin n, ℓ₀.eval (dom i) ≠ 0)
    (hℓ₁v : ∀ i : Fin n, ℓ₁.eval (dom i) ≠ 0)
    (hcop : IsCoprime ℓ₀ ℓ₁) (hgen₀ : ¬ ℓ₀ ∣ R₀) (hgen₁ : ¬ ℓ₁ ∣ R₁)
    {δ : ℝ≥0} (hδn : δ * (Fintype.card (Fin n) : ℝ≥0) ≤ w) :
    (Finset.univ.filter (fun γ : F => mcaEvent (F := F)
      ((rsCode dom k : Submodule F (Fin n → F)) : Set (Fin n → F)) δ
      (fun i => R₀.eval (dom i) / ℓ₀.eval (dom i))
      (fun i => R₁.eval (dom i) / ℓ₁.eval (dom i)) γ)).card
      * (w - j).choose (j + 1) ≤ n.choose (j + 1) := by
  set Γ : Finset F := Finset.univ.filter (fun γ : F => mcaEvent (F := F)
      ((rsCode dom k : Submodule F (Fin n → F)) : Set (Fin n → F)) δ
      (fun i => R₀.eval (dom i) / ℓ₀.eval (dom i))
      (fun i => R₁.eval (dom i) / ℓ₁.eval (dom i)) γ) with hΓ
  have key : ∀ γ ∈ Γ, ∃ P : F[X], P.natDegree ≤ k - 1 ∧
      n - w ≤ (w2Agr dom ℓ₀ ℓ₁ R₀ R₁ P γ).card ∧
      (w2Agr dom ℓ₀ ℓ₁ R₀ R₁ P γ).card ≤ 2 * w + k - 1 := by
    intro γ hγ
    rw [hΓ, Finset.mem_filter] at hγ
    exact window_explainer dom hk hℓ₀d hℓ₁d hR₀d hR₁d hℓ₀v hℓ₁v hcop hgen₀
      hδn hγ.2
  choose! Pf hPfdeg hPfge hPfle using key
  set T : F → Finset (Fin n) := fun γ =>
    Finset.univ \ w2Agr dom ℓ₀ ℓ₁ R₀ R₁ (Pf γ) γ with hT
  -- size bounds for the missing sets
  have hTge : ∀ γ ∈ Γ, w - j ≤ (T γ).card := by
    intro γ hγ
    rw [hT]
    rw [Finset.card_sdiff, Finset.card_univ, Finset.inter_univ, Fintype.card_fin]
    have := hPfle γ hγ
    omega
  have hTle : ∀ γ ∈ Γ, (T γ).card ≤ w := by
    intro γ hγ
    rw [hT]
    rw [Finset.card_sdiff, Finset.card_univ, Finset.inter_univ, Fintype.card_fin]
    have := hPfge γ hγ
    omega
  -- distinct bad scalars share at most j missing points
  have hshare : ∀ γ ∈ Γ, ∀ γ' ∈ Γ, γ ≠ γ' → ((T γ) ∩ (T γ')).card ≤ j := by
    intro γ hγ γ' hγ' hne
    by_contra hbig
    push_neg at hbig
    set A := w2Agr dom ℓ₀ ℓ₁ R₀ R₁ (Pf γ) γ with hA
    set A' := w2Agr dom ℓ₀ ℓ₁ R₀ R₁ (Pf γ') γ' with hA'
    -- |A ∩ A'| = n − |T ∪ T'| ≥ n − (|T| + |T'| − (j+1)) ≥ w + k
    have hcompl : A ∩ A' = Finset.univ \ ((T γ) ∪ (T γ')) := by
      rw [hT, hA, hA']
      ext i
      simp only [Finset.mem_inter, Finset.mem_sdiff, Finset.mem_union,
        Finset.mem_univ, true_and]
      tauto
    have hunion : ((T γ) ∪ (T γ')).card + (j + 1) ≤ (T γ).card + (T γ').card := by
      have := Finset.card_inter_add_card_union (T γ) (T γ')
      omega
    have hIcard : w + k ≤ (A ∩ A').card := by
      rw [hcompl, Finset.card_sdiff, Finset.card_univ, Finset.inter_univ,
        Fintype.card_fin]
      have h1 := hTle γ hγ
      have h2 := hTle γ' hγ'
      have h3 : ((T γ) ∪ (T γ')).card ≤ n := by
        have := Finset.card_le_card (Finset.subset_univ ((T γ) ∪ (T γ')))
        rw [Finset.card_univ, Fintype.card_fin] at this
        exact this
      omega
    exact hne (shared_forces_eq_general dom hk hℓ₁d hR₁d hℓ₀v hgen₁
      (hPfdeg γ hγ) (hPfdeg γ' hγ') hIcard (fun i hi => by
        have hiA := Finset.mem_of_mem_inter_left hi
        have hiA' := Finset.mem_of_mem_inter_right hi
        rw [hA, w2Agr, Finset.mem_filter] at hiA
        rw [hA', w2Agr, Finset.mem_filter] at hiA'
        exact ⟨hiA.2, hiA'.2⟩))
  -- the Steiner double count over (j+1)-subsets
  set Jset : F → Finset (Finset (Fin n)) := fun γ =>
    Finset.powersetCard (j + 1) (T γ) with hJ
  have hJdisj : ∀ γ ∈ Γ, ∀ γ' ∈ Γ, γ ≠ γ' → Disjoint (Jset γ) (Jset γ') := by
    intro γ hγ γ' hγ' hne
    rw [Finset.disjoint_left]
    intro A hA hA'
    rw [hJ, Finset.mem_powersetCard] at hA hA'
    have hsub : A ⊆ (T γ) ∩ (T γ') :=
      Finset.subset_inter hA.1 hA'.1
    have := Finset.card_le_card hsub
    have := hshare γ hγ γ' hγ' hne
    omega
  have hJcard : ∀ γ ∈ Γ, (w - j).choose (j + 1) ≤ (Jset γ).card := by
    intro γ hγ
    rw [hJ, Finset.card_powersetCard]
    exact Nat.choose_le_choose _ (hTge γ hγ)
  have hbiU : (Γ.biUnion Jset).card = ∑ γ ∈ Γ, (Jset γ).card :=
    Finset.card_biUnion hJdisj
  have hcap : (Γ.biUnion Jset).card ≤ n.choose (j + 1) := by
    have hsub : Γ.biUnion Jset ⊆ Finset.powersetCard (j + 1) Finset.univ := by
      intro A hA
      rw [Finset.mem_biUnion] at hA
      obtain ⟨γ, -, hAγ⟩ := hA
      rw [hJ, Finset.mem_powersetCard] at hAγ
      rw [Finset.mem_powersetCard]
      exact ⟨Finset.subset_univ _, hAγ.2⟩
    have := Finset.card_le_card hsub
    rw [Finset.card_powersetCard, Finset.card_univ, Fintype.card_fin] at this
    exact this
  calc Γ.card * (w - j).choose (j + 1)
      = ∑ _γ ∈ Γ, (w - j).choose (j + 1) := by
        rw [Finset.sum_const, smul_eq_mul, mul_comm]
    _ ≤ ∑ γ ∈ Γ, (Jset γ).card := Finset.sum_le_sum hJcard
    _ = (Γ.biUnion Jset).card := hbiU.symm
    _ ≤ n.choose (j + 1) := hcap

open Classical in
/-- **The solved stratum** (`j = 0`, the first beyond-ladder slice `n = 3w+k−1`):
`#bad · w ≤ n`.  The `μ_w`-coset family attains `n/w`
(`probe_coset_family_jzero.py`: 3 = 3, 4 = 4, 4 = 4), so the bounds MEET. -/
theorem window_jzero_solved (hk : 1 ≤ k) (hj : n = 3 * w + k - 1) (hwn : w ≤ n)
    (hℓ₀d : ℓ₀.natDegree ≤ w) (hℓ₁d : ℓ₁.natDegree ≤ w)
    (hR₀d : R₀.natDegree ≤ w + k - 1) (hR₁d : R₁.natDegree ≤ w + k - 1)
    (hℓ₀v : ∀ i : Fin n, ℓ₀.eval (dom i) ≠ 0)
    (hℓ₁v : ∀ i : Fin n, ℓ₁.eval (dom i) ≠ 0)
    (hcop : IsCoprime ℓ₀ ℓ₁) (hgen₀ : ¬ ℓ₀ ∣ R₀) (hgen₁ : ¬ ℓ₁ ∣ R₁)
    {δ : ℝ≥0} (hδn : δ * (Fintype.card (Fin n) : ℝ≥0) ≤ w) :
    (Finset.univ.filter (fun γ : F => mcaEvent (F := F)
      ((rsCode dom k : Submodule F (Fin n → F)) : Set (Fin n → F)) δ
      (fun i => R₀.eval (dom i) / ℓ₀.eval (dom i))
      (fun i => R₁.eval (dom i) / ℓ₁.eval (dom i)) γ)).card * w ≤ n := by
  have h := window_packing_law dom hk (j := 0) (by omega) (by omega) hwn
    hℓ₀d hℓ₁d hR₀d hR₁d hℓ₀v hℓ₁v hcop hgen₀ hgen₁ hδn
  simpa using h

open Classical in
/-- Division form of `window_jzero_solved`: if `w > 0`, then the
per-stack bad-scalar count at the first beyond-ladder slice is at most `⌊n / w⌋`. -/
theorem window_jzero_solved_card_le (hk : 1 ≤ k)
    (hj : n = 3 * w + k - 1) (hwn : w ≤ n) (hwpos : 0 < w)
    (hℓ₀d : ℓ₀.natDegree ≤ w) (hℓ₁d : ℓ₁.natDegree ≤ w)
    (hR₀d : R₀.natDegree ≤ w + k - 1) (hR₁d : R₁.natDegree ≤ w + k - 1)
    (hℓ₀v : ∀ i : Fin n, ℓ₀.eval (dom i) ≠ 0)
    (hℓ₁v : ∀ i : Fin n, ℓ₁.eval (dom i) ≠ 0)
    (hcop : IsCoprime ℓ₀ ℓ₁) (hgen₀ : ¬ ℓ₀ ∣ R₀) (hgen₁ : ¬ ℓ₁ ∣ R₁)
    {δ : ℝ≥0} (hδn : δ * (Fintype.card (Fin n) : ℝ≥0) ≤ w) :
    (Finset.univ.filter (fun γ : F => mcaEvent (F := F)
      ((rsCode dom k : Submodule F (Fin n → F)) : Set (Fin n → F)) δ
      (fun i => R₀.eval (dom i) / ℓ₀.eval (dom i))
      (fun i => R₁.eval (dom i) / ℓ₁.eval (dom i)) γ)).card ≤ n / w := by
  exact Nat.le_div_iff_mul_le hwpos |>.mpr
    (window_jzero_solved (dom := dom) (k := k) (w := w) hk hj hwn
      hℓ₀d hℓ₁d hR₀d hR₁d hℓ₀v hℓ₁v hcop hgen₀ hgen₁ hδn)

end Packing

end ProximityGap.WBPencil

-- Axiom audit (expected: propext, Classical.choice, Quot.sound only)
#print axioms ProximityGap.WBPencil.shared_forces_eq_general
#print axioms ProximityGap.WBPencil.window_explainer
#print axioms ProximityGap.WBPencil.window_packing_law
#print axioms ProximityGap.WBPencil.window_jzero_solved
#print axioms ProximityGap.WBPencil.window_jzero_solved_card_le

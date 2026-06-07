/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/

import ArkLib.Data.CodingTheory.Connections.GKL24FirstMoment

set_option autoImplicit false

/-!
# Existence of the maximal correlated-agreement domain (GKL24 building block)

The GKL24 first-moment argument (`GKL24MaxCorrWitnessCoverResidual`) requires, per codeword, a
*maximal* correlated-agreement domain `D` (`maxCorrAgreeDomain`).  This file proves the underlying
existence fact: whenever *some* correlated-agreement domain exists, a maximal one exists — a finite
poset has a maximal element.  This is the first verified component of the GKL24
maximal-correlated-agreement-domain residual; the remaining geometric properties (strict containment
in the bad line-agreement sets, the `(1−p)·n` pairwise intersection) are the genuine GKL24
Lemma 1 / Cor 1 content.
-/

set_option linter.unusedFintypeInType false
set_option linter.unusedDecidableInType false
set_option linter.unusedSectionVars false

namespace ProximityGap

open scoped NNReal

variable {ι : Type} [Fintype ι] [Nonempty ι] [DecidableEq ι]
  {F : Type} [Field F] [Fintype F] [DecidableEq F]

/-- **Maximal correlated-agreement domain exists (when any domain does).**  If some `D₀` is a
correlated-agreement domain, then a *maximal* one exists.  Proof: the correlated-agreement domains
form a nonempty finite family of `Finset ι`s; a maximal-cardinality member is maximal under
inclusion (any larger domain containing it has equal cardinality, hence equals it). -/
theorem exists_maxCorrAgreeDomain_of_nonempty
    (MC : Submodule F (ι → F)) (p : ℝ≥0) (u₀ u₁ : ι → F)
    (h : ∃ D₀ : Finset ι, corrAgreeDomain MC p u₀ u₁ D₀) :
    ∃ D : Finset ι, maxCorrAgreeDomain MC p u₀ u₁ D := by
  classical
  obtain ⟨D₀, hD₀⟩ := h
  set 𝒮 : Finset (Finset ι) :=
    (Finset.univ : Finset ι).powerset.filter (fun D => corrAgreeDomain MC p u₀ u₁ D) with h𝒮
  have hD₀mem : D₀ ∈ 𝒮 :=
    Finset.mem_filter.mpr ⟨Finset.mem_powerset.mpr (Finset.subset_univ _), hD₀⟩
  obtain ⟨D, hDmem, hDmax⟩ := Finset.exists_max_image 𝒮 Finset.card ⟨D₀, hD₀mem⟩
  refine ⟨D, (Finset.mem_filter.mp hDmem).2, ?_⟩
  intro E hDE hE
  have hEmem : E ∈ 𝒮 :=
    Finset.mem_filter.mpr ⟨Finset.mem_powerset.mpr (Finset.subset_univ _), hE⟩
  exact (Finset.eq_of_subset_of_card_le hDE (hDmax E hEmem)).ge

/-- **Pairwise intersection of two line-agreement sets (distinct combiners).**  For `γ ≠ γ'`, the
coordinates where `w` agrees with both `u₀ + γ·u₁` and `u₀ + γ'·u₁` are exactly those where `u₁`
vanishes and `w = u₀`: on the overlap, `(γ − γ')·u₁ᵢ = 0` forces `u₁ᵢ = 0`, hence `wᵢ = u₀ᵢ`.  This
is the structural core of the GKL24 residual's `(1−p)·n` pairwise-intersection requirement — once a
maximal domain `D ⊆ lineAgreeSet γ` is in hand, `D` lands inside this common set, so `(1−p)·n ≤ |D|`
transfers to the intersection. -/
theorem lineAgreeSet_inter_eq (u₀ u₁ w : ι → F) {γ γ' : F} (hγ : γ ≠ γ') :
    lineAgreeSet u₀ u₁ w γ ∩ lineAgreeSet u₀ u₁ w γ'
      = Finset.univ.filter (fun i => u₁ i = 0 ∧ w i = u₀ i) := by
  ext i
  simp only [Finset.mem_inter, mem_lineAgreeSet_iff, Finset.mem_filter, Finset.mem_univ, true_and]
  constructor
  · rintro ⟨h1, h2⟩
    have heq : γ • u₁ i = γ' • u₁ i :=
      add_left_cancel (a := u₀ i) (by rw [← h1, ← h2])
    have hu1 : u₁ i = 0 := by
      by_contra hne
      rw [smul_eq_mul, smul_eq_mul] at heq
      exact hγ (mul_right_cancel₀ hne heq)
    exact ⟨hu1, by rw [h1, hu1, smul_zero, add_zero]⟩
  · rintro ⟨hu1, hw⟩
    refine ⟨?_, ?_⟩ <;> rw [hw, hu1, smul_zero, add_zero]

/-- **Reduction of the residual's pairwise-intersection bound to domain containment.**  If `D` is a
correlated-agreement domain (so `(1−p)·n ≤ |D|`) contained in both `lineAgreeSet γ` and
`lineAgreeSet γ'`, then `(1−p)·n ≤ |lineAgreeSet γ ∩ lineAgreeSet γ'|`.  Combined with
`exists_maxCorrAgreeDomain_of_nonempty`, this discharges the `(1−p)·n` pairwise-intersection clause
of `GKL24MaxCorrWitnessCoverResidual` from the single remaining GKL24 kernel property: that the
maximal domain is contained in each bad witness's line-agreement set (`D ⊆ lineAgreeSet γ`). -/
theorem corrAgreeDomain_subset_inter_card
    {MC : Submodule F (ι → F)} {p : ℝ≥0} {u₀ u₁ w : ι → F} {γ γ' : F} {D : Finset ι}
    (hD : corrAgreeDomain MC p u₀ u₁ D)
    (hγ : D ⊆ lineAgreeSet u₀ u₁ w γ) (hγ' : D ⊆ lineAgreeSet u₀ u₁ w γ') :
    ((1 - p) * Fintype.card ι : ℝ≥0)
      ≤ ((lineAgreeSet u₀ u₁ w γ ∩ lineAgreeSet u₀ u₁ w γ').card : ℝ≥0) :=
  le_trans hD.1 (by exact_mod_cast Finset.card_le_card (Finset.subset_inter hγ hγ'))

end ProximityGap

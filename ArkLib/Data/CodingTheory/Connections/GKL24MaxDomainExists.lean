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

/-- **Line-agreement petals are pairwise disjoint above a domain absorbing their intersection.**
If `D` contains `lineAgreeSet γ ∩ lineAgreeSet γ'`, the petals `lineAgreeSet γ \ D` and
`lineAgreeSet γ' \ D` are disjoint: their overlap lies in the intersection, which `D` removes.
This is the GKL24 / GCXK25 sunflower-petal disjointness step. -/
theorem linePetal_disjoint_of_inter_subset (D : Finset ι) (u₀ u₁ w : ι → F) {γ γ' : F}
    (h : lineAgreeSet u₀ u₁ w γ ∩ lineAgreeSet u₀ u₁ w γ' ⊆ D) :
    Disjoint (linePetal D u₀ u₁ w γ) (linePetal D u₀ u₁ w γ') := by
  rw [Finset.disjoint_left]
  intro i hi hi'
  rw [linePetal, Finset.mem_sdiff] at hi
  rw [linePetal, Finset.mem_sdiff] at hi'
  exact hi.2 (h (Finset.mem_inter.mpr ⟨hi.1, hi'.1⟩))

/-- **Sunflower petals for distinct bad combiners are disjoint above a domain containing the common
zero-agreement set.**  Specialising `linePetal_disjoint_of_inter_subset` via `lineAgreeSet_inter_eq`:
for `γ ≠ γ'`, if `D ⊇ {i : u₁ᵢ = 0 ∧ wᵢ = u₀ᵢ}` then the two petals are disjoint.  Together with
`corrAgreeDomain_subset_inter_card` and `exists_maxCorrAgreeDomain_of_nonempty`, this assembles the
sunflower structure of the GKL24 residual around a maximal domain. -/
theorem linePetal_disjoint_of_common_subset (D : Finset ι) (u₀ u₁ w : ι → F) {γ γ' : F}
    (hγ : γ ≠ γ')
    (h : Finset.univ.filter (fun i => u₁ i = 0 ∧ w i = u₀ i) ⊆ D) :
    Disjoint (linePetal D u₀ u₁ w γ) (linePetal D u₀ u₁ w γ') :=
  linePetal_disjoint_of_inter_subset D u₀ u₁ w (by rw [lineAgreeSet_inter_eq u₀ u₁ w hγ]; exact h)

/-- **Petal-counting: pairwise-disjoint large petals bound the number of combiners.**  If the petals
`P γ` (`γ ∈ B`) are pairwise disjoint, each contained in `U`, and each of size `≥ L`, then
`|B|·L ≤ |U|`.  Proof: the disjoint petals tile a subset of `U`, so `∑|P γ| = |⋃ P γ| ≤ |U|`, while
`∑|P γ| ≥ |B|·L`.  This is the cardinality consumer for the GKL24 sunflower step. -/
theorem card_mul_le_of_disjoint_petals {B : Finset F} {P : F → Finset ι} {U : Finset ι} {L : ℕ}
    (hdisj : ∀ γ ∈ B, ∀ γ' ∈ B, γ ≠ γ' → Disjoint (P γ) (P γ'))
    (hsub : ∀ γ ∈ B, P γ ⊆ U) (hL : ∀ γ ∈ B, L ≤ (P γ).card) :
    B.card * L ≤ U.card :=
  calc B.card * L = ∑ _γ ∈ B, L := by rw [Finset.sum_const, smul_eq_mul, mul_comm]
    _ ≤ ∑ γ ∈ B, (P γ).card := Finset.sum_le_sum hL
    _ = (B.biUnion P).card := (Finset.card_biUnion hdisj).symm
    _ ≤ U.card := Finset.card_le_card (Finset.biUnion_subset.mpr hsub)

/-- **Petal lower bound under domain containment.**  When the maximal domain `D` is contained in a
bad witness's line-agreement set, the petal `lineAgreeSet γ \ D` has size `≥ |lineAgreeSet γ| − |D|`,
hence `≥ (large agreement) − |D|`.  Combined with `card_mul_le_of_disjoint_petals` and the petal
disjointness, this delivers the GKL24 first-moment count `|B| · (agreement − |D|) ≤ n − |D|`. -/
theorem card_linePetal_ge (D : Finset ι) (u₀ u₁ w : ι → F) (γ : F) :
    (lineAgreeSet u₀ u₁ w γ).card - D.card ≤ (linePetal D u₀ u₁ w γ).card := by
  rw [linePetal]
  have h := Finset.card_sdiff_add_card_inter (lineAgreeSet u₀ u₁ w γ) D
  have hi : (lineAgreeSet u₀ u₁ w γ ∩ D).card ≤ D.card :=
    Finset.card_le_card Finset.inter_subset_right
  omega

/-- **GKL24 first-moment count (sunflower assembly).**  Let `D` absorb the common zero-agreement set
`{i : u₁ᵢ = 0 ∧ wᵢ = u₀ᵢ}`, and let every combiner `γ ∈ B` have line-agreement of size `≥ A`.  Then
`|B| · (A − |D|) ≤ n − |D|`.  This assembles the whole sunflower argument — petal disjointness
(`linePetal_disjoint_of_common_subset`), the petal lower bound (`card_linePetal_ge`), and the
counting consumer (`card_mul_le_of_disjoint_petals`) — into the GKL24 first-moment bound on the
number of bad combiners.  Instantiated with `A = (1−δ)·n` (the bad-witness agreement) this is GKL24's
`|Bad¹|`-style count; the sole remaining input is that `D` absorbs the common set. -/
theorem badCombiner_count {D : Finset ι} {u₀ u₁ w : ι → F} {B : Finset F} {A : ℕ}
    (hcommon : Finset.univ.filter (fun i => u₁ i = 0 ∧ w i = u₀ i) ⊆ D)
    (hA : ∀ γ ∈ B, A ≤ (lineAgreeSet u₀ u₁ w γ).card) :
    B.card * (A - D.card) ≤ Fintype.card ι - D.card := by
  have hU : (Finset.univ \ D).card = Fintype.card ι - D.card := by
    have h := Finset.card_sdiff_add_card_inter (Finset.univ : Finset ι) D
    rw [Finset.univ_inter, Finset.card_univ] at h
    omega
  rw [← hU]
  refine card_mul_le_of_disjoint_petals (fun γ _ γ' _ hne =>
    linePetal_disjoint_of_common_subset D u₀ u₁ w hne hcommon) (fun γ _ => ?_) (fun γ hγ => ?_)
  · rw [linePetal]
    exact Finset.sdiff_subset_sdiff (Finset.subset_univ _) (Finset.Subset.refl D)
  · exact le_trans (Nat.sub_le_sub_right (hA γ hγ) D.card) (card_linePetal_ge D u₀ u₁ w γ)

/-- **Bad-witness combiners have large line-agreement.**  Every `γ ∈ mcaBadWitness C δ u₀ u₁ w` has
`|lineAgreeSet γ| ≥ (1−δ)·n`: the witnessing set `S` (size `≥ (1−δ)n` on which `w` agrees with the
line) is contained in `lineAgreeSet γ`.  This supplies the agreement input `A = (1−δ)n` of
`badCombiner_count`, connecting the sunflower count to the actual residual. -/
theorem card_lineAgreeSet_ge_of_mem_mcaBadWitness
    {MC : Submodule F (ι → F)} {δ : ℝ≥0} {u₀ u₁ w : ι → F} {γ : F}
    (hγ : γ ∈ mcaBadWitness (MC : Set (ι → F)) δ u₀ u₁ w) :
    ((1 - δ) * Fintype.card ι : ℝ≥0) ≤ ((lineAgreeSet u₀ u₁ w γ).card : ℝ≥0) := by
  classical
  simp only [mcaBadWitness, Finset.mem_filter, Finset.mem_univ, true_and] at hγ
  obtain ⟨S, hScard, hSagree, -⟩ := hγ
  have hSsub : S ⊆ lineAgreeSet u₀ u₁ w γ := fun i hi => by
    rw [mem_lineAgreeSet_iff]; exact hSagree i hi
  exact le_trans hScard (by exact_mod_cast Finset.card_le_card hSsub)

/-- **The common zero-agreement set jointly agrees (via `(w, 0)`).**  On `{i : u₁ᵢ = 0 ∧ wᵢ = u₀ᵢ}`
the codeword pair `(w, 0)` witnesses joint agreement: `w = u₀` there and `0 = u₁` there.  Hence,
once this set is large enough, it is a correlated-agreement domain. -/
theorem pairJointAgreesOn_common {MC : Submodule F (ι → F)} {u₀ u₁ w : ι → F} (hw : w ∈ MC) :
    pairJointAgreesOn (MC : Set (ι → F))
      (Finset.univ.filter (fun i => u₁ i = 0 ∧ w i = u₀ i)) u₀ u₁ := by
  refine ⟨w, hw, 0, MC.zero_mem, fun i hi => ?_⟩
  rw [Finset.mem_filter] at hi
  exact ⟨hi.2.2, by rw [Pi.zero_apply]; exact hi.2.1.symm⟩

/-- **A maximal correlated-agreement domain containing a given one exists.**  Strengthening
`exists_maxCorrAgreeDomain_of_nonempty`: from a correlated-agreement domain `D₀`, a *maximal* domain
`D ⊇ D₀` exists.  Combined with `pairJointAgreesOn_common`, taking `D₀ = {i : u₁ᵢ=0 ∧ wᵢ=u₀ᵢ}` (when
large) yields a maximal domain that **absorbs the common zero-agreement set** — the precise input
`hcommon` that `badCombiner_count` and the petal disjointness require. -/
theorem exists_maxCorrAgreeDomain_containing
    (MC : Submodule F (ι → F)) (p : ℝ≥0) (u₀ u₁ : ι → F) (D₀ : Finset ι)
    (hD₀ : corrAgreeDomain MC p u₀ u₁ D₀) :
    ∃ D : Finset ι, D₀ ⊆ D ∧ maxCorrAgreeDomain MC p u₀ u₁ D := by
  classical
  set 𝒮 : Finset (Finset ι) :=
    (Finset.univ : Finset ι).powerset.filter
      (fun D => corrAgreeDomain MC p u₀ u₁ D ∧ D₀ ⊆ D) with h𝒮
  have hD₀mem : D₀ ∈ 𝒮 :=
    Finset.mem_filter.mpr ⟨Finset.mem_powerset.mpr (Finset.subset_univ _), hD₀, Finset.Subset.refl _⟩
  obtain ⟨D, hDmem, hDmax⟩ := Finset.exists_max_image 𝒮 Finset.card ⟨D₀, hD₀mem⟩
  obtain ⟨hDcorr, hD₀D⟩ := (Finset.mem_filter.mp hDmem).2
  refine ⟨D, hD₀D, hDcorr, fun E hDE hE => ?_⟩
  have hEmem : E ∈ 𝒮 :=
    Finset.mem_filter.mpr
      ⟨Finset.mem_powerset.mpr (Finset.subset_univ _), hE, le_trans hD₀D hDE⟩
  exact (Finset.eq_of_subset_of_card_le hDE (hDmax E hEmem)).ge

end ProximityGap

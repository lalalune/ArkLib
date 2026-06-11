/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.MCALowerBound

/-!
# The witness-spread structure of MCA lower bounds (Proximity Prize, ABF26 #232)

The Grand MCA Challenge needs a **lower** bound `ε_mca(C, δ) > ε*` for `δ` above the
threshold `δ*`. The state-of-the-art near-capacity lower bound is `ε_mca ≥ n^{Ω(1)}/|F|`
([BCHKS25],[KK25],[CGHLL26]); the file `MCAGeneralLowerBound.lean` proves the unconditional
`ε_mca ≥ 1/|F|` up to capacity for every proper linear code. To beat `1/|F|`, one must make
`mcaEvent` fire for **many** scalars `γ` on a single line.

This file isolates *exactly* what such a construction must look like, and proves a sharp
structural obstruction:

* `pairJointAgreesOn_iff_split` — **rowwise split.** The MCA joint-pair predicate is exactly
  the conjunction of independent row explanations on the same witness set. This makes row-level
  non-explainability a reusable route to `¬ pairJointAgreesOn`.

* `epsMCA_ge_card_div_of_mcaEvent_set` — **multi-`γ` lower bound.** If a fixed stack `u`
  admits a whole finite set `G ⊆ F` of bad scalars (`mcaEvent` fires at each), then
  `ε_mca(C, δ) ≥ |G|/|F|`. This is the lower-bound engine the prize needs: producing
  `|G| = n^{Ω(1)}` bad scalars yields the near-capacity bound. (Generalizes the single-scalar
  `epsMCA_ge_inv_card_of_mcaEvent`, which is the `|G| = 1` case.)

* `unique_bad_gamma_common_witness` — **the obstruction.** For *any* linear code `C`, if two
  bad scalars `γ₁, γ₂` are witnessed by the **same** coordinate set `S` (the same `S` carries
  the line-closeness for both *and* the joint-disagreement), then `γ₁ = γ₂`. Reason: from
  `w₁ = u₀ + γ₁·u₁` and `w₂ = u₀ + γ₂·u₁` on `S`, the linear combinations
  `v₁ := (γ₁-γ₂)⁻¹(w₁-w₂)` and `v₀ := w₁ - γ₁·v₁` are codewords agreeing with `(u₀,u₁)` on
  `S` — exactly the `pairJointAgreesOn` that `mcaEvent` forbids.

* `common_witness_badGamma_card_le_one` / `epsMCA_common_witness_le_inv_card` — **consequence.**
  A single common witness set yields at most `1/|F|`. Hence **the prize's lower bound
  provably requires the witness sets `S_γ` to vary with `γ`** — i.e. the list-decoding
  geometry (different codewords, hence different agreement sets, near the line). This is the
  precise reason the near-capacity lower bound is genuinely hard, and it delineates the open
  core honestly: the open content is *not* positivity (`1/|F|`, done) but producing a line
  whose `δ`-close points are witnessed by a *spread* of distinct coordinate sets.

* `badScalar_card_le_one_of_forced_univ` / `epsMCA_le_inv_card_of_forced_univ` — **forced
  universal witness barrier.** If the radius is so small that every legal `mcaEvent` witness set
  must be all coordinates, then every bad scalar shares the same witness set `univ`; the common
  witness obstruction collapses the bad set to size at most one. This turns the exact F5
  `δ*` pin and the zero-code endpoint into instances of the same structural phenomenon.

All results are `sorry`-free and axiom-clean (`[propext, Classical.choice, Quot.sound]`).

## References
- [ABF26] Arnon, Boneh, Fenzi. *Open Problems in List Decoding and Correlated Agreement*. 2026.
  Tracking issue #232 / #141.
-/

set_option linter.unusedSectionVars false
set_option linter.unusedFintypeInType false
set_option linter.unusedDecidableInType false

open scoped NNReal ENNReal ProbabilityTheory BigOperators
open ProximityGap Code

namespace ProximityGap.MCAWitnessSpread

variable {ι : Type} [Fintype ι] [Nonempty ι] [DecidableEq ι]
variable {F : Type} [Field F] [Fintype F] [DecidableEq F]
variable {A : Type} [Fintype A] [DecidableEq A] [AddCommGroup A] [Module F A]

/-- **The joint-pair clause splits rowwise.** `pairJointAgreesOn C S u₀ u₁` packages two
independent row explanations over the same coordinate set `S`: one codeword agrees with `u₀`
on `S`, and one codeword agrees with `u₁` on `S`. This is often the cleanest way to refute
joint agreement, since failure of either row explanation is enough. -/
theorem pairJointAgreesOn_iff_split (C : Set (ι → A)) (S : Finset ι) (u₀ u₁ : ι → A) :
    pairJointAgreesOn C S u₀ u₁ ↔
      (∃ v₀ ∈ C, ∀ i ∈ S, v₀ i = u₀ i) ∧ (∃ v₁ ∈ C, ∀ i ∈ S, v₁ i = u₁ i) := by
  constructor
  · rintro ⟨v₀, h₀, v₁, h₁, h⟩
    exact ⟨⟨v₀, h₀, fun i hi => (h i hi).1⟩, ⟨v₁, h₁, fun i hi => (h i hi).2⟩⟩
  · rintro ⟨⟨v₀, h₀, e₀⟩, ⟨v₁, h₁, e₁⟩⟩
    exact ⟨v₀, h₀, v₁, h₁, fun i hi => ⟨e₀ i hi, e₁ i hi⟩⟩

open Classical in
/-- **Multi-scalar MCA lower bound.** If a fixed stack `u` admits a whole finite set `G ⊆ F`
of bad scalars — `mcaEvent C δ (u 0) (u 1) γ` fires for every `γ ∈ G` — then
`ε_mca(C, δ) ≥ |G|/|F|`.

This is the lower-bound engine for the Grand MCA Challenge: the near-capacity bound
`ε_mca ≥ n^{Ω(1)}/|F|` is exactly this lemma instantiated with a line carrying
`|G| = n^{Ω(1)}` bad scalars. Generalizes `epsMCA_ge_inv_card_of_mcaEvent` (`|G| = 1`). -/
theorem epsMCA_ge_card_div_of_mcaEvent_set
    (C : Set (ι → A)) (δ : ℝ≥0) (u : WordStack A (Fin 2) ι) (G : Finset F)
    (hG : ∀ γ ∈ G, mcaEvent C δ (u 0) (u 1) γ) :
    (G.card : ℝ≥0∞) / (Fintype.card F : ℝ≥0∞) ≤ epsMCA (F := F) (A := A) C δ := by
  refine le_trans ?_ (mcaEvent_prob_le_epsMCA (F := F) (A := A) C δ u)
  rw [prob_uniform_eq_card_filter_div_card]
  have hsub : G ⊆ Finset.filter (fun γ => mcaEvent C δ (u 0) (u 1) γ) Finset.univ := by
    intro γ hγ
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    exact hG γ hγ
  have hcard : G.card
      ≤ (Finset.filter (fun γ => mcaEvent C δ (u 0) (u 1) γ) Finset.univ).card :=
    Finset.card_le_card hsub
  simp only [ENNReal.coe_natCast]
  gcongr

/-- **At most one bad scalar per witness set (linear codes).** For any linear code `C` and any
coordinate set `S` on which `(u₀, u₁)` has *no* joint codeword pair, at most one scalar `γ` can
have the line `u₀ + γ·u₁` agree with a codeword on all of `S`.

Proof: if `w₁ = u₀ + γ₁·u₁` and `w₂ = u₀ + γ₂·u₁` on `S` with `γ₁ ≠ γ₂`, then
`v₁ := (γ₁-γ₂)⁻¹(w₁-w₂)` and `v₀ := w₁ - γ₁·v₁` are codewords (linearity) with `v₀ = u₀`,
`v₁ = u₁` on `S` — a `pairJointAgreesOn` witness, contradicting the hypothesis. -/
theorem unique_bad_gamma_common_witness
    (C : Submodule F (ι → A)) (S : Finset ι) (u₀ u₁ : ι → A) {γ₁ γ₂ : F}
    (hno : ¬ pairJointAgreesOn (C : Set (ι → A)) S u₀ u₁)
    (h₁ : ∃ w ∈ C, ∀ i ∈ S, w i = u₀ i + γ₁ • u₁ i)
    (h₂ : ∃ w ∈ C, ∀ i ∈ S, w i = u₀ i + γ₂ • u₁ i) :
    γ₁ = γ₂ := by
  by_contra hne
  obtain ⟨w₁, hw₁C, hw₁⟩ := h₁
  obtain ⟨w₂, hw₂C, hw₂⟩ := h₂
  have hd : (γ₁ - γ₂) ≠ 0 := sub_ne_zero.mpr hne
  set v₁ : ι → A := (γ₁ - γ₂)⁻¹ • (w₁ - w₂) with hv₁def
  set v₀ : ι → A := w₁ - γ₁ • v₁ with hv₀def
  have hv₁mem : v₁ ∈ C := C.smul_mem _ (C.sub_mem hw₁C hw₂C)
  have hv₀mem : v₀ ∈ C := C.sub_mem hw₁C (C.smul_mem _ hv₁mem)
  apply hno
  refine ⟨v₀, hv₀mem, v₁, hv₁mem, ?_⟩
  intro i hi
  have hv₁i : v₁ i = u₁ i := by
    simp only [hv₁def, Pi.smul_apply, Pi.sub_apply, hw₁ i hi, hw₂ i hi]
    rw [show (u₀ i + γ₁ • u₁ i) - (u₀ i + γ₂ • u₁ i) = (γ₁ - γ₂) • u₁ i from by
      rw [sub_smul]; abel]
    rw [inv_smul_smul₀ hd]
  have hv₀i : v₀ i = u₀ i := by
    simp only [hv₀def, Pi.sub_apply, Pi.smul_apply, hw₁ i hi, hv₁i]
    abel
  exact ⟨hv₀i, hv₁i⟩

open Classical in
/-- **The common-witness bad-scalar set is a subsingleton (linear codes).** Restating
`unique_bad_gamma_common_witness`: with a single coordinate set `S` on which `(u₀, u₁)` has no
joint codeword pair, the set of scalars whose line agrees with a codeword on all of `S` has at
most one element. -/
theorem common_witness_badGamma_card_le_one
    (C : Submodule F (ι → A)) (S : Finset ι) (u₀ u₁ : ι → A)
    (hno : ¬ pairJointAgreesOn (C : Set (ι → A)) S u₀ u₁) :
    (Finset.univ.filter
      (fun γ : F => ∃ w ∈ C, ∀ i ∈ S, w i = u₀ i + γ • u₁ i)).card ≤ 1 := by
  rw [Finset.card_le_one]
  intro γ₁ h₁ γ₂ h₂
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at h₁ h₂
  exact unique_bad_gamma_common_witness C S u₀ u₁ hno h₁ h₂

open Classical in
/-- **A single common witness set yields at most `1/|F|`.** If *every* bad scalar in a finite
set `G` is witnessed by the **same** coordinate set `S` (same `S` carries both the
line-closeness and the joint-disagreement, as in `mcaEvent`), then `|G| ≤ 1`. Consequently the
common-witness route never beats the unconditional `ε_mca ≥ 1/|F|`.

Hence the prize's near-capacity lower bound `ε_mca ≥ n^{Ω(1)}/|F|` provably **requires the
witness sets to vary with `γ`** — the list-decoding spread of distinct agreement sets around
the line. This pins down precisely what is open on the lower-bound side. -/
theorem common_witness_badGamma_set_card_le_one
    (C : Submodule F (ι → A)) (S : Finset ι) (u₀ u₁ : ι → A) (G : Finset F)
    (hno : ¬ pairJointAgreesOn (C : Set (ι → A)) S u₀ u₁)
    (hG : ∀ γ ∈ G, ∃ w ∈ C, ∀ i ∈ S, w i = u₀ i + γ • u₁ i) :
    G.card ≤ 1 := by
  rw [Finset.card_le_one]
  intro γ₁ hmem₁ γ₂ hmem₂
  exact unique_bad_gamma_common_witness C S u₀ u₁ hno (hG γ₁ hmem₁) (hG γ₂ hmem₂)

open Classical in
/-- **Forced-universal-witness barrier.** If the radius/cardinality side condition forces every
legal `mcaEvent` witness set to be `Finset.univ`, then every stack has at most one bad scalar.

Mathematically, this is the endpoint version of the witness-spread obstruction: when geometry
leaves no room for the witness sets to vary, all bad scalars share the common witness `univ`, so
`unique_bad_gamma_common_witness` collapses them. -/
theorem badScalar_card_le_one_of_forced_univ
    (C : Submodule F (ι → A)) (δ : ℝ≥0)
    (hforce : ∀ T : Finset ι,
      ((1 : ℝ≥0) - δ) * (Fintype.card ι : ℝ≥0) ≤ (T.card : ℝ≥0) → T = Finset.univ)
    (u : WordStack A (Fin 2) ι) :
    (Finset.filter
      (fun γ : F => mcaEvent (F := F) (C : Set (ι → A)) δ (u 0) (u 1) γ)
      Finset.univ).card ≤ 1 := by
  rw [Finset.card_le_one]
  intro γ hγ γ' hγ'
  rw [Finset.mem_filter] at hγ hγ'
  obtain ⟨S, hS, hclose, hno⟩ := hγ.2
  obtain ⟨S', hS', hclose', _⟩ := hγ'.2
  rw [hforce S hS] at hclose hno
  rw [hforce S' hS'] at hclose'
  exact unique_bad_gamma_common_witness C Finset.univ (u 0) (u 1) hno hclose hclose'

open Classical in
/-- **Probability form of the forced-universal-witness barrier.** If every legal `mcaEvent`
witness set is forced to be all coordinates, then the MCA error is at most the unconditional
floor `1/|F|` for any linear code. The only way to exceed this floor is therefore a genuine
spread of distinct witness sets. -/
theorem epsMCA_le_inv_card_of_forced_univ
    (C : Submodule F (ι → A)) (δ : ℝ≥0)
    (hforce : ∀ T : Finset ι,
      ((1 : ℝ≥0) - δ) * (Fintype.card ι : ℝ≥0) ≤ (T.card : ℝ≥0) → T = Finset.univ) :
    epsMCA (F := F) (A := A) (C : Set (ι → A)) δ ≤ 1 / (Fintype.card F : ℝ≥0∞) := by
  unfold epsMCA
  refine iSup_le fun u => ?_
  rw [prob_uniform_eq_card_filter_div_card]
  simp only [ENNReal.coe_natCast]
  gcongr
  exact_mod_cast badScalar_card_le_one_of_forced_univ C δ hforce u

#print axioms pairJointAgreesOn_iff_split
#print axioms epsMCA_ge_card_div_of_mcaEvent_set
#print axioms unique_bad_gamma_common_witness
#print axioms common_witness_badGamma_card_le_one
#print axioms common_witness_badGamma_set_card_le_one
#print axioms badScalar_card_le_one_of_forced_univ
#print axioms epsMCA_le_inv_card_of_forced_univ

end ProximityGap.MCAWitnessSpread

/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/

import scripts.probes.astra_mca_event_bridge
import ArkLib.Data.CodingTheory.ProximityGap.MCAWitnessSpread
import Mathlib.Data.Finset.Prod

set_option autoImplicit false

noncomputable section
namespace AstraMcaRootRelocation
open Polynomial
open scoped NNReal

section FreshDirections
variable {F I : Type} [Field F] [Fintype F] [DecidableEq F] [Fintype I]

/-- At one coordinate, finitely many collinear local values admit fresh,
nonzero, pairwise distinct finite cancellation directions. The inequality
is an explicit unconditional field-size condition, not a genericity assumption. -/
theorem exists_fresh_directions (x : F) (z : I → F)
    (hz : Function.Injective z) (S : Finset F)
    (hfirst : Fintype.card I < Fintype.card F)
    (hsize : Fintype.card I * (S.card + 1) + 1 < Fintype.card F) :
    ∃ c t : F,
      (∀ i, c ≠ z i) ∧
      (∀ i, x * z i - t ≠ 0) ∧
      (∀ i, (c - z i) / (x * z i - t) ≠ 0) ∧
      Function.Injective (fun i => (c - z i) / (x * z i - t)) ∧
      (∀ i, (c - z i) / (x * z i - t) ∉ S) ∧
      (∀ i, z i + ((c - z i) / (x * z i - t)) * (x * z i) =
        c + ((c - z i) / (x * z i - t)) * t) := by
  classical
  have hcsize : (Finset.univ.image z).card < (Finset.univ : Finset F).card := by
    rw [Finset.card_univ]
    exact (Finset.card_image_le.trans (by simp)).trans_lt hfirst
  obtain ⟨c, _, hc⟩ := Finset.exists_mem_notMem_of_card_lt_card hcsize
  have hcz : ∀ i, c ≠ z i := by
    intro i hi
    apply hc
    exact Finset.mem_image.mpr ⟨i, Finset.mem_univ _, hi.symm⟩
  let poles : Finset F := Finset.univ.image (fun i => x * z i)
  let old : Finset F := (Finset.univ ×ˢ S).image
    (fun p : I × F => x * z p.1 - (c - z p.1) / p.2)
  let bad : Finset F := insert (x * c) (poles ∪ old)
  have hpoles : poles.card ≤ Fintype.card I := by
    exact Finset.card_image_le.trans (by simp)
  have hold : old.card ≤ Fintype.card I * S.card := by
    exact Finset.card_image_le.trans (by simp)
  have hbad : bad.card < (Finset.univ : Finset F).card := by
    have hb := Finset.card_insert_le (x * c) (poles ∪ old)
    have hu := Finset.card_union_le poles old
    rw [Finset.card_univ]
    dsimp only [bad] at *
    nlinarith
  obtain ⟨t, _, ht⟩ := Finset.exists_mem_notMem_of_card_lt_card hbad
  have hcarrier : t ≠ x * c := by
    intro he
    apply ht
    simp [bad, he]
  have hden : ∀ i, x * z i - t ≠ 0 := by
    intro i he
    apply ht
    apply Finset.mem_insert_of_mem
    apply Finset.mem_union_left
    exact Finset.mem_image.mpr ⟨i, Finset.mem_univ _, (sub_eq_zero.mp he)⟩
  have hn : ∀ i, (c - z i) / (x * z i - t) ≠ 0 := by
    intro i
    exact div_ne_zero (sub_ne_zero.mpr (hcz i)) (hden i)
  refine ⟨c, t, hcz, hden, hn, ?_, ?_, ?_⟩
  · intro i j he
    have he' := (div_eq_div_iff (hden i) (hden j)).mp he
    have hm : (z i - z j) * (t - x * c) = 0 := by
      linear_combination he'
    apply hz
    exact sub_eq_zero.mp ((mul_eq_zero.mp hm).resolve_right (sub_ne_zero.mpr hcarrier))
  · intro i hi
    let γ := (c - z i) / (x * z i - t)
    have hγ : γ ≠ 0 := hn i
    have he : γ * (x * z i - t) = c - z i := by
      exact (eq_div_iff (hden i)).mp rfl
    have hrecover : t = x * z i - (c - z i) / γ := by
      field_simp [hγ]
      linear_combination -he
    apply ht
    apply Finset.mem_insert_of_mem
    apply Finset.mem_union_right
    exact Finset.mem_image.mpr ⟨(i, γ), Finset.mem_product.mpr ⟨Finset.mem_univ _, hi⟩,
      hrecover.symm⟩
  · intro i
    have he : ((c - z i) / (x * z i - t)) * (x * z i - t) = c - z i := by
      exact (eq_div_iff (hden i)).mp rfl
    linear_combination he

end FreshDirections

section SimultaneousDirections
variable {F I : Type} [Field F] [Fintype F] [DecidableEq F] [Fintype I]

/-- The finite scalar determined by a received pair and a local pencil value. -/
def direction (x : F) (z : I → F) (v : F × F) (i : I) : F :=
  (v.1 - z i) / (x * z i - v.2)

/-- Local nonzero residuals and their exact scalar cancellation identities. -/
def GoodLocal (x : F) (z : I → F) (v : F × F) : Prop :=
  ∀ i, v.1 ≠ z i ∧ x * z i - v.2 ≠ 0 ∧ direction x z v i ≠ 0 ∧
    z i + direction x z v i * (x * z i) = v.1 + direction x z v i * v.2

/-- Finite greedy selection for every coordinate at once. All directions,
including those at different coordinates, are distinct and avoid S. -/
theorem exists_simultaneous_directions (U : Finset F) (z : F → I → F)
    (S : Finset F) (hz : ∀ x ∈ U, Function.Injective (z x))
    (hfirst : Fintype.card I < Fintype.card F)
    (hsize : Fintype.card I * (S.card + U.card * Fintype.card I + 1) + 1 <
      Fintype.card F) :
    ∃ v : F → F × F,
      (∀ x ∈ U, GoodLocal x (z x) (v x)) ∧
      (∀ x ∈ U, ∀ i, direction x (z x) (v x) i ∉ S) ∧
      (∀ x ∈ U, ∀ y ∈ U, ∀ i j,
        direction x (z x) (v x) i = direction y (z y) (v y) j → x = y ∧ i = j) := by
  classical
  induction U using Finset.induction_on with
  | empty =>
    refine ⟨fun _ => (0, 0), ?_, ?_, ?_⟩ <;> simp
  | @insert a U ha ih =>
    have hsizeU : Fintype.card I * (S.card + U.card * Fintype.card I + 1) + 1 <
        Fintype.card F := by
      rw [Finset.card_insert_of_notMem ha] at hsize
      nlinarith
    obtain ⟨v, hgood, havoid, hinj⟩ := ih
      (fun x hx => hz x (Finset.mem_insert_of_mem hx)) hsizeU
    let used : Finset F := (U ×ˢ (Finset.univ : Finset I)).image
      (fun p : F × I => direction p.1 (z p.1) (v p.1) p.2)
    have hused : used.card ≤ U.card * Fintype.card I := by
      exact Finset.card_image_le.trans (by simp)
    have hSused : (S ∪ used).card ≤ S.card + U.card * Fintype.card I :=
      (Finset.card_union_le S used).trans (Nat.add_le_add_left hused _)
    have hnewsize : Fintype.card I * ((S ∪ used).card + 1) + 1 <
        Fintype.card F := by
      nlinarith
    obtain ⟨c, t, hcz, hden, hn, hnewinj, hnewavoid, hcancel⟩ :=
      exists_fresh_directions a (z a) (hz a (Finset.mem_insert_self _ _))
        (S ∪ used) hfirst hnewsize
    let w : F → F × F := fun x => if x = a then (c, t) else v x
    have hwa : w a = (c, t) := by simp [w]
    have hwU : ∀ x ∈ U, w x = v x := by
      intro x hx
      have hxa : x ≠ a := by rintro rfl; exact ha hx
      simp [w, hxa]
    have hnewold : ∀ x ∈ U, ∀ i j,
        direction a (z a) (c, t) i ≠ direction x (z x) (v x) j := by
      intro x hx i j he
      apply hnewavoid i
      apply Finset.mem_union_right
      exact Finset.mem_image.mpr ⟨(x, j),
        Finset.mem_product.mpr ⟨hx, Finset.mem_univ _⟩, he.symm⟩
    refine ⟨w, ?_, ?_, ?_⟩
    · intro x hx
      rcases Finset.mem_insert.mp hx with rfl | hx
      · rw [hwa]
        intro i
        exact ⟨hcz i, hden i, hn i, hcancel i⟩
      · rw [hwU x hx]
        exact hgood x hx
    · intro x hx i
      rcases Finset.mem_insert.mp hx with rfl | hx
      · rw [hwa]
        intro hi
        exact hnewavoid i (Finset.mem_union_left _ hi)
      · rw [hwU x hx]
        exact havoid x hx i
    · intro x hx y hy i j he
      rcases Finset.mem_insert.mp hx with hxa | hxU <;>
        rcases Finset.mem_insert.mp hy with hya | hyU
      · subst x
        subst y
        rw [hwa] at he
        exact ⟨rfl, hnewinj he⟩
      · subst x
        rw [hwa, hwU y hyU] at he
        exact False.elim (hnewold y hyU i j he)
      · subst y
        rw [hwa, hwU x hxU] at he
        exact False.elim (hnewold x hxU j i he.symm)
      · rw [hwU x hxU, hwU y hyU] at he
        exact hinj x hxU y hyU i j he

end SimultaneousDirections

section CountedDirections
variable {F I : Type} [Field F] [Fintype F] [DecidableEq F] [Fintype I]

/-- The simultaneous greedy choices give exactly |U|*|I| fresh scalars,
with explicit local origins and no overlap with the prescribed old set. -/
theorem exists_counted_fresh_directions (U : Finset F) (z : F → I → F)
    (S : Finset F) (hz : ∀ x ∈ U, Function.Injective (z x))
    (hfirst : Fintype.card I < Fintype.card F)
    (hsize : Fintype.card I * (S.card + U.card * Fintype.card I + 1) + 1 <
      Fintype.card F) :
    ∃ v : F → F × F, ∃ fresh : Finset F,
      fresh.card = U.card * Fintype.card I ∧ Disjoint fresh S ∧
      (∀ x ∈ U, GoodLocal x (z x) (v x)) ∧
      (∀ γ ∈ fresh, ∃ x ∈ U, ∃ i, γ = direction x (z x) (v x) i) := by
  classical
  obtain ⟨v, hgood, havoid, hinj⟩ :=
    exists_simultaneous_directions U z S hz hfirst hsize
  let pairs := U ×ˢ (Finset.univ : Finset I)
  let f : F × I → F := fun p => direction p.1 (z p.1) (v p.1) p.2
  refine ⟨v, pairs.image f, ?_, ?_, hgood, ?_⟩
  · rw [Finset.card_image_of_injOn]
    · simp [pairs]
    · intro p hp q hq he
      obtain ⟨hx, hi⟩ := hinj p.1 (Finset.mem_product.mp hp).1
        q.1 (Finset.mem_product.mp hq).1 p.2 q.2 he
      exact Prod.ext hx hi
  · apply Finset.disjoint_left.mpr
    intro γ hγ
    obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp hγ
    exact havoid p.1 (Finset.mem_product.mp hp).1 p.2
  · intro γ hγ
    obtain ⟨p, hp, he⟩ := Finset.mem_image.mp hγ
    exact ⟨p.1, (Finset.mem_product.mp hp).1, p.2, he.symm⟩

/-- The coarse six-direction production field-size budget, by kernel arithmetic. -/
theorem production_greedy_arithmetic :
    (6 : ℕ) < 365375409332725729550921208179070755120141565953 ∧
    6 * ((2 ^ 30) + (2 ^ 30) * 6 + 1) + 1 <
      365375409332725729550921208179070755120141565953 := by
  norm_num

end CountedDirections

section EventBridge
variable {F ι : Type} [Field F] [DecidableEq F] [Fintype ι]

/-- A degree-bounded joint core and one nonzero second-coordinate residual
produce ArkLib's original MCA event on precisely the core-plus-point support. -/
theorem mca_event_of_joint_core_extra (dom : ι ↪ F) (d : ℕ) (δ : ℝ≥0)
    (u₀ u₁ : F → F) (p q : F[X]) (γ x : F) (U : Finset F)
    (hp : p.natDegree ≤ d) (hq : q.natDegree ≤ d)
    (hcore : ∀ y ∈ U, p.eval y = u₀ y ∧ q.eval y = u₁ y)
    (hlarge : d < U.card)
    (hextra : p.eval x + γ * q.eval x = u₀ x + γ * u₁ x)
    (hnonzero : q.eval x ≠ u₁ x)
    (hrange : ∀ y ∈ insert x U, y ∈ Set.range dom)
    (hsize : ((U.card + 1 : ℕ) : ℝ≥0) ≥ (1 - δ) * Fintype.card ι) :
    ProximityGap.mcaEvent (F := F) (ReedSolomon.code dom (d + 1) : Set (ι → F))
      δ (fun i => u₀ (dom i)) (fun i => u₁ (dom i)) γ := by
  have hx : x ∉ U := by
    intro hx
    exact hnonzero (hcore x hx).2
  apply AstraMcaEventBridge.mca_event_from_polynomial_support dom d δ u₀ u₁ γ
    (insert x U) hrange
    (by simpa only [Finset.card_insert_of_notMem hx] using hsize)
    (p + C γ * q)
  · exact (natDegree_add_le _ _).trans (max_le hp
      (natDegree_mul_le.trans (by simpa using hq)))
  · intro y hy
    simp only [eval_add, eval_mul, eval_C]
    rcases Finset.mem_insert.mp hy with rfl | hy
    · exact hextra
    · rw [(hcore y hy).1, (hcore y hy).2]
  · rintro ⟨r, hr, heval⟩
    have heq : r = q := by
      apply eq_of_natDegree_lt_card_of_eval_eq' r q U
      · intro y hy
        exact (heval y (Finset.mem_insert_of_mem hy)).trans (hcore y hy).2.symm
      · exact (max_le hr hq).trans_lt hlarge
    exact hnonzero (heq ▸ heval x (Finset.mem_insert_self _ _))

/-- The ordinary assigned coordinates of a root-relocation construction
give their reciprocal scalars as actual same-support MCA events. -/
theorem mca_event_of_reciprocal_extra (dom : ι ↪ F) (d : ℕ) (δ : ℝ≥0)
    (u₀ u₁ : F → F) (p q : F[X]) (x : F) (U : Finset F)
    (hp : p.natDegree ≤ d) (hq : q.natDegree ≤ d)
    (hcore : ∀ y ∈ U, p.eval y = u₀ y ∧ q.eval y = u₁ y)
    (hlarge : d < U.card) (hx : x ≠ 0)
    (hcode : q.eval x = x * p.eval x) (hword : u₁ x = x * u₀ x)
    (hnonzero : p.eval x ≠ u₀ x)
    (hrange : ∀ y ∈ insert x U, y ∈ Set.range dom)
    (hsize : ((U.card + 1 : ℕ) : ℝ≥0) ≥ (1 - δ) * Fintype.card ι) :
    ProximityGap.mcaEvent (F := F) (ReedSolomon.code dom (d + 1) : Set (ι → F))
      δ (fun i => u₀ (dom i)) (fun i => u₁ (dom i)) (-1 / x) := by
  apply mca_event_of_joint_core_extra dom d δ u₀ u₁ p q (-1 / x) x U hp hq
    hcore hlarge ?_ ?_ hrange hsize
  · have hm : (-1 / x) * x = -1 := div_mul_cancel₀ _ hx
    have hz : ∀ y : F, y + (-1 / x) * (x * y) = 0 := by
      intro y
      calc
        y + (-1 / x) * (x * y) = y + ((-1 / x) * x) * y := by ring
        _ = 0 := by rw [hm]; ring
    rw [hcode, hword, hz, hz]
  · rw [hcode, hword]
    exact fun he => hnonzero (mul_left_cancel₀ hx he)

/-- Every local origin produced by the fresh-direction theorem maps to the
original MCA event, once its polynomial core and domain membership are supplied. -/
theorem mca_event_of_good_local {I : Type} (dom : ι ↪ F) (d : ℕ) (δ : ℝ≥0)
    (u₀ u₁ : F → F) (p q : F[X]) (x : F) (U : Finset F)
    (z : I → F) (v : F × F) (i : I) (hgood : GoodLocal x z v)
    (hp : p.natDegree ≤ d) (hq : q.natDegree ≤ d)
    (hcore : ∀ y ∈ U, p.eval y = u₀ y ∧ q.eval y = u₁ y)
    (hlarge : d < U.card)
    (hpval : p.eval x = z i) (hqval : q.eval x = x * z i)
    (hu₀ : u₀ x = v.1) (hu₁ : u₁ x = v.2)
    (hrange : ∀ y ∈ insert x U, y ∈ Set.range dom)
    (hsize : ((U.card + 1 : ℕ) : ℝ≥0) ≥ (1 - δ) * Fintype.card ι) :
    ProximityGap.mcaEvent (F := F) (ReedSolomon.code dom (d + 1) : Set (ι → F))
      δ (fun j => u₀ (dom j)) (fun j => u₁ (dom j)) (direction x z v i) := by
  apply mca_event_of_joint_core_extra dom d δ u₀ u₁ p q (direction x z v i) x U hp hq
    hcore hlarge ?_ ?_ hrange hsize
  · simpa only [hpval, hqval, hu₀, hu₁] using (hgood i).2.2.2
  · rw [hqval, hu₁]
    exact sub_ne_zero.mp (hgood i).2.1

end EventBridge

section EventCounting
variable {F ι : Type} [Field F] [DecidableEq F] [Fintype F] [Fintype ι]
open scoped ENNReal ProbabilityTheory

/-- Disjoint ordinary and fresh contributions form one actual MCA-event set
whose cardinality is the sum of the two contributions. -/
theorem disjoint_event_union (code : Set (ι → F)) (δ : ℝ≥0) (u₀ u₁ : ι → F)
    (ordinary fresh : Finset F) (hdisj : Disjoint ordinary fresh)
    (hordinary : ∀ γ ∈ ordinary, ProximityGap.mcaEvent code δ u₀ u₁ γ)
    (hfresh : ∀ γ ∈ fresh, ProximityGap.mcaEvent code δ u₀ u₁ γ) :
    ∃ bad : Finset F, bad.card = ordinary.card + fresh.card ∧
      ∀ γ ∈ bad, ProximityGap.mcaEvent code δ u₀ u₁ γ := by
  refine ⟨ordinary ∪ fresh, Finset.card_union_of_disjoint hdisj, ?_⟩
  intro γ hγ
  exact (Finset.mem_union.mp hγ).elim (hordinary γ) (hfresh γ)

/-- The ordinary-plus-fresh count is a lower bound on the complete bad-scalar
set for the same fixed received word, allowing additional unknown decoders. -/
theorem disjoint_event_card_le_bad_card (code : Set (ι → F)) (δ : ℝ≥0)
    (u₀ u₁ : ι → F) (ordinary fresh : Finset F)
    (hdisj : Disjoint ordinary fresh)
    (hordinary : ∀ γ ∈ ordinary, ProximityGap.mcaEvent code δ u₀ u₁ γ)
    (hfresh : ∀ γ ∈ fresh, ProximityGap.mcaEvent code δ u₀ u₁ γ) :
    ordinary.card + fresh.card ≤
      (Finset.univ.filter fun γ => ProximityGap.mcaEvent code δ u₀ u₁ γ).card := by
  classical
  obtain ⟨bad, hcard, hbad⟩ := disjoint_event_union code δ u₀ u₁ ordinary fresh
    hdisj hordinary hfresh
  rw [← hcard]
  apply Finset.card_le_card
  intro γ hγ
  exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hbad γ hγ⟩

/-- Exact counting of disjoint contributions gives a probability lower bound
for the single received pair used throughout the construction. -/
theorem disjoint_event_probability_lower (code : Set (ι → F)) (δ : ℝ≥0)
    (u₀ u₁ : ι → F) (ordinary fresh : Finset F)
    (hdisj : Disjoint ordinary fresh)
    (hordinary : ∀ γ ∈ ordinary, ProximityGap.mcaEvent code δ u₀ u₁ γ)
    (hfresh : ∀ γ ∈ fresh, ProximityGap.mcaEvent code δ u₀ u₁ γ) :
    ((ordinary.card + fresh.card : ℕ) : ℝ≥0∞) / Fintype.card F ≤
      Pr_{let γ ← $ᵖ F}[ProximityGap.mcaEvent code δ u₀ u₁ γ] := by
  classical
  rw [prob_uniform_eq_card_filter_div_card]
  have hc := disjoint_event_card_le_bad_card code δ u₀ u₁ ordinary fresh
    hdisj hordinary hfresh
  exact ENNReal.div_le_div_right (by exact_mod_cast hc) _

/-- The same concrete disjoint event sets lower-bound the original worst-case
MCA error; no full bad-scalar census is required. -/
theorem disjoint_event_epsMCA_lower [Nonempty ι] (code : Set (ι → F)) (δ : ℝ≥0)
    (u₀ u₁ : ι → F) (ordinary fresh : Finset F)
    (hdisj : Disjoint ordinary fresh)
    (hordinary : ∀ γ ∈ ordinary, ProximityGap.mcaEvent code δ u₀ u₁ γ)
    (hfresh : ∀ γ ∈ fresh, ProximityGap.mcaEvent code δ u₀ u₁ γ) :
    ((ordinary.card + fresh.card : ℕ) : ℝ≥0∞) / Fintype.card F ≤
      ProximityGap.epsMCA (F := F) code δ := by
  classical
  obtain ⟨bad, hcard, hbad⟩ := disjoint_event_union code δ u₀ u₁ ordinary fresh
    hdisj hordinary hfresh
  let u : Code.WordStack F (Fin 2) ι := fun j => if j = 0 then u₀ else u₁
  have h := ProximityGap.MCAWitnessSpread.epsMCA_ge_card_div_of_mcaEvent_set
    code δ u bad (fun γ hγ => by simpa [u] using hbad γ hγ)
  simpa only [hcard] using h

end EventCounting
end AstraMcaRootRelocation
#print axioms AstraMcaRootRelocation.exists_fresh_directions
#print axioms AstraMcaRootRelocation.exists_simultaneous_directions
#print axioms AstraMcaRootRelocation.exists_counted_fresh_directions
#print axioms AstraMcaRootRelocation.production_greedy_arithmetic
#print axioms AstraMcaRootRelocation.mca_event_of_joint_core_extra
#print axioms AstraMcaRootRelocation.mca_event_of_reciprocal_extra
#print axioms AstraMcaRootRelocation.mca_event_of_good_local
#print axioms AstraMcaRootRelocation.disjoint_event_union
#print axioms AstraMcaRootRelocation.disjoint_event_card_le_bad_card
#print axioms AstraMcaRootRelocation.disjoint_event_probability_lower
#print axioms AstraMcaRootRelocation.disjoint_event_epsMCA_lower

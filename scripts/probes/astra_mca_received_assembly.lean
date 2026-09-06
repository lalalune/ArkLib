/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/

import scripts.probes.astra_mca_root_relocation

/-!
# Constructing one received word with ordinary and fresh MCA witnesses

The inputs are polynomial cores, coordinate sets, and local evaluation facts.
The received word, fresh scalars, original MCA events, and exact union count
are constructed in the proof. Production seed/fiber instantiation is separate.
-/

set_option autoImplicit false

noncomputable section

namespace AstraMcaReceivedAssembly

open Polynomial AstraMcaRootRelocation
open scoped NNReal

variable {F ι K J : Type} [Field F] [DecidableEq F] [Fintype F]
  [Fintype ι] [Fintype J]

/-- Patch finite fresh-direction choices into a prescribed received word while
preserving every polynomial core. The ordinary and fresh origins together
witness an exact-sized subset of the original MCA event set. -/
theorem exists_received_word_and_events
    (dom : ι ↪ F) (d : ℕ) (δ : ℝ≥0)
    (p q : K → F[X]) (core : K → Finset F) (base : F → F × F)
    (covered uncovered : Finset F) (source : F → J → K)
    (hp : ∀ i, (p i).natDegree ≤ d) (hq : ∀ i, (q i).natDegree ≤ d)
    (hcore : ∀ i, ∀ x ∈ core i,
      (p i).eval x = (base x).1 ∧ (q i).eval x = (base x).2)
    (hlarge : ∀ i, d < (core i).card)
    (hsize : ∀ i, (((core i).card + 1 : ℕ) : ℝ≥0) ≥
      (1 - δ) * Fintype.card ι)
    (hcore_range : ∀ i, ∀ x ∈ core i, x ∈ Set.range dom)
    (hcore_outside : ∀ i, ∀ x ∈ core i, x ∉ uncovered)
    (hcovered_range : ∀ x ∈ covered, x ∈ Set.range dom)
    (huncovered_range : ∀ x ∈ uncovered, x ∈ Set.range dom)
    (hdisjoint : Disjoint covered uncovered)
    (hcovered_nonzero : ∀ x ∈ covered, x ≠ 0)
    (hcarrier : ∀ i, ∀ x ∈ covered ∪ uncovered,
      (q i).eval x = x * (p i).eval x)
    (hbase_carrier : ∀ x ∈ covered, (base x).2 = x * (base x).1)
    (hnonowner : ∀ x ∈ covered, ∃ i, (p i).eval x ≠ (base x).1)
    (hinjective : ∀ x ∈ uncovered,
      Function.Injective (fun j => (p (source x j)).eval x))
    (hfirst : Fintype.card J < Fintype.card F)
    (hbudget : Fintype.card J *
      (covered.card + uncovered.card * Fintype.card J + 1) + 1 < Fintype.card F) :
    ∃ u₀ u₁ : ι → F, ∃ bad : Finset F,
      bad.card = covered.card + uncovered.card * Fintype.card J ∧
      ∀ γ ∈ bad,
        ProximityGap.mcaEvent (F := F)
          (ReedSolomon.code dom (d + 1) : Set (ι → F)) δ u₀ u₁ γ := by
  classical
  let ordinary : Finset F := covered.image (fun x => -1 / x)
  have hordinary_card : ordinary.card = covered.card := by
    dsimp only [ordinary]
    apply Finset.card_image_of_injOn
    intro x hx y hy hxy
    have h := congrArg (fun t : F => (-t)⁻¹) hxy
    simpa only [neg_div, one_div, neg_neg, inv_inv] using h
  let z : F → J → F := fun x j => (p (source x j)).eval x
  have hz : ∀ x ∈ uncovered, Function.Injective (z x) := hinjective
  have hbudget' : Fintype.card J *
      (ordinary.card + uncovered.card * Fintype.card J + 1) + 1 < Fintype.card F := by
    simpa only [hordinary_card] using hbudget
  obtain ⟨v, fresh, hfresh_card, hfresh_disjoint, hgood, horigin⟩ :=
    exists_counted_fresh_directions uncovered z ordinary hz hfirst hbudget'
  let received : F → F × F := fun x => if x ∈ uncovered then v x else base x
  have hpatch : ∀ x ∈ uncovered, received x = v x := by
    intro x hx
    simp only [received, if_pos hx]
  have hpreserve : ∀ x ∉ uncovered, received x = base x := by
    intro x hx
    simp only [received, if_neg hx]
  have hreceived_core : ∀ i, ∀ x ∈ core i,
      (p i).eval x = (received x).1 ∧ (q i).eval x = (received x).2 := by
    intro i x hx
    rw [hpreserve x (hcore_outside i x hx)]
    exact hcore i x hx
  have hordinary_event : ∀ γ ∈ ordinary,
      ProximityGap.mcaEvent (F := F)
        (ReedSolomon.code dom (d + 1) : Set (ι → F)) δ
        (fun i => (received (dom i)).1) (fun i => (received (dom i)).2) γ := by
    intro γ hγ
    obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hγ
    obtain ⟨i, hi⟩ := hnonowner x hx
    have hx_outside : x ∉ uncovered := by
      intro hu
      exact Finset.disjoint_left.mp hdisjoint hx hu
    apply mca_event_of_reciprocal_extra dom d δ
      (fun y => (received y).1) (fun y => (received y).2)
      (p i) (q i) x (core i) (hp i) (hq i) (hreceived_core i) (hlarge i)
      (hcovered_nonzero x hx)
      (hcarrier i x (Finset.mem_union_left _ hx))
    · rw [hpreserve x hx_outside]
      exact hbase_carrier x hx
    · simpa only [hpreserve x hx_outside] using hi
    · intro y hy
      rcases Finset.mem_insert.mp hy with rfl | hy
      · exact hcovered_range x hx
      · exact hcore_range i y hy
    · exact hsize i
  have hfresh_event : ∀ γ ∈ fresh,
      ProximityGap.mcaEvent (F := F)
        (ReedSolomon.code dom (d + 1) : Set (ι → F)) δ
        (fun i => (received (dom i)).1) (fun i => (received (dom i)).2) γ := by
    intro γ hγ
    obtain ⟨x, hx, j, rfl⟩ := horigin γ hγ
    apply mca_event_of_good_local dom d δ
      (fun y => (received y).1) (fun y => (received y).2)
      (p (source x j)) (q (source x j)) x (core (source x j))
      (z x) (v x) j (hgood x hx)
      (hp (source x j)) (hq (source x j))
      (hreceived_core (source x j)) (hlarge (source x j))
    · rfl
    · exact hcarrier (source x j) x (Finset.mem_union_right _ hx)
    · rw [hpatch x hx]
    · rw [hpatch x hx]
    · intro y hy
      rcases Finset.mem_insert.mp hy with rfl | hy
      · exact huncovered_range x hx
      · exact hcore_range (source x j) y hy
    · exact hsize (source x j)
  obtain ⟨bad, hbad_card, hbad⟩ := disjoint_event_union
    (ReedSolomon.code dom (d + 1) : Set (ι → F)) δ
    (fun i => (received (dom i)).1) (fun i => (received (dom i)).2)
    ordinary fresh hfresh_disjoint.symm hordinary_event hfresh_event
  refine ⟨(fun i => (received (dom i)).1), (fun i => (received (dom i)).2),
    bad, ?_, hbad⟩
  simpa only [hordinary_card, hfresh_card] using hbad_card

end AstraMcaReceivedAssembly

#print axioms AstraMcaReceivedAssembly.exists_received_word_and_events

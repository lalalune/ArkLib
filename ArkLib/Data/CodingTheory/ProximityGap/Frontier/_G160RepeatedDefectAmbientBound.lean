/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._G159InjectiveDepthFiberExact
import Mathlib.Data.Fintype.CardEmbedding

/-!
# G160: exact ambient count and upper bound for the repeated-coordinate defect

G159 isolates the complement of the internally-injective full-depth sector.  This file counts
non-injective words exactly by identifying injective `t`-words on `G` with embeddings
`Fin t ↪ G`.  A union bound over the endpoint on which a repetition occurs then gives an
unconditional ambient ceiling for the G159 defect.

Issue #466.
-/

set_option autoImplicit false

namespace ArkLib.ProximityGap.Frontier.G160RepeatedDefectAmbientBound

open ArkLib.ProximityGap.Frontier.G83MMaximalCommonCancellation
open ArkLib.ProximityGap.Frontier.G87CorrectedPaddingDecoder
open ArkLib.ProximityGap.Frontier.G95CardinalityDeepCapNoGo
open ArkLib.ProximityGap.Frontier.G114DepthThreePopulationNormalForm
open ArkLib.ProximityGap.Frontier.G145LowerDepthMultiplicityEnvelope
open ArkLib.ProximityGap.Frontier.G159InjectiveDepthFiberExact

variable {F : Type*} [AddCommGroup F] [Fintype F] [DecidableEq F]

def ambientWords (G : Finset F) (t : ℕ) : Finset (Fin t → F) :=
  Fintype.piFinset fun _ : Fin t => G

def injectiveWords (G : Finset F) (t : ℕ) : Finset (Fin t → F) :=
  (ambientWords G t).filter Function.Injective

def repeatedWords (G : Finset F) (t : ℕ) : Finset (Fin t → F) :=
  (ambientWords G t).filter fun v => ¬Function.Injective v

/-- Internally-injective words on `G` are the same finite objects as embeddings into `G`. -/
noncomputable def injectiveWordEquivEmbedding (G : Finset F) (t : ℕ) :
    ↥(injectiveWords G t) ≃ (Fin t ↪ ↥G) where
  toFun v :=
    { toFun := fun i => ⟨v.1 i, by
        have hv := (Finset.mem_filter.mp v.2).1
        rw [ambientWords, Fintype.mem_piFinset] at hv
        exact hv i⟩
      inj' := by
        intro i j hij
        apply (Finset.mem_filter.mp v.2).2
        exact congrArg Subtype.val hij }
  invFun e := ⟨fun i => (e i).1, by
    rw [injectiveWords, Finset.mem_filter]
    refine ⟨?_, ?_⟩
    · rw [ambientWords, Fintype.mem_piFinset]
      exact fun i => (e i).2
    · intro i j hij
      apply e.injective
      exact Subtype.ext hij⟩
  left_inv v := by
    apply Subtype.ext
    funext i
    rfl
  right_inv e := by
    apply DFunLike.ext _ _
    intro i
    rfl

theorem ambientWords_card (G : Finset F) (t : ℕ) :
    (ambientWords G t).card = G.card ^ t := by
  exact Fintype.card_piFinset_const G t

theorem injectiveWords_card (G : Finset F) (t : ℕ) :
    (injectiveWords G t).card = G.card.descFactorial t := by
  rw [← Fintype.card_coe, Fintype.card_congr (injectiveWordEquivEmbedding G t),
    Fintype.card_embedding_eq, Fintype.card_coe, Fintype.card_fin]

/-- Exact birthday-defect count for one endpoint word. -/
theorem repeatedWords_card (G : Finset F) (t : ℕ) :
    (repeatedWords G t).card = G.card ^ t - G.card.descFactorial t := by
  have hpart := Finset.card_filter_add_card_filter_not
    (s := ambientWords G t) (p := Function.Injective)
  rw [← injectiveWords, ← repeatedWords, injectiveWords_card, ambientWords_card] at hpart
  omega

/-- At positive depth a full-cancellation pair cannot be diagonal. -/
theorem ne_of_mem_fullDepth_of_pos {G : Finset F} {t : ℕ}
    {q : (Fin t → F) × (Fin t → F)} (ht : 0 < t)
    (hq : q ∈ (energySet G t).filter fun z => cancelDepth z = t) : q.1 ≠ q.2 := by
  intro heq
  rw [Finset.mem_filter] at hq
  have hd := (cancelDepth_eq_length_iff_disjoint q.1 q.2).mp hq.2
  rw [heq] at hd
  have hempty : valueBag q.2 = 0 := disjoint_self.mp hd
  have hcard : (valueBag q.2).card = t := by simp [valueBag]
  rw [hempty] at hcard
  simp at hcard
  omega

/-- Every positive-depth repeated defect has a non-injective left or right endpoint. -/
theorem repeatedDepthDefect_subset_endpointRepeated {G : Finset F} {t : ℕ} (ht : 0 < t) :
    repeatedDepthDefect G t ⊆
      (repeatedWords G t ×ˢ ambientWords G t) ∪
        (ambientWords G t ×ˢ repeatedWords G t) := by
  intro q hq
  rw [repeatedDepthDefect, Finset.mem_filter] at hq
  obtain ⟨hdepth, hbad⟩ := hq
  have henergy := (Finset.mem_filter.mp hdepth).1
  rw [energySet, Finset.mem_filter] at henergy
  have hprod := henergy.1
  obtain ⟨hL, hR⟩ := Finset.mem_product.mp hprod
  have hne := ne_of_mem_fullDepth_of_pos ht hdepth
  simp only [not_and_or] at hbad
  rcases hbad with hbadL | hbadR
  · rw [Finset.mem_union]
    left
    exact Finset.mem_product.mpr
      ⟨Finset.mem_filter.mpr ⟨hL, hbadL⟩, hR⟩
  · have hbadR' : ¬Function.Injective q.2 := by
      simpa [hne] using hbadR
    rw [Finset.mem_union]
    right
    exact Finset.mem_product.mpr
      ⟨hL, Finset.mem_filter.mpr ⟨hR, hbadR'⟩⟩

/-- **G160 defect capstone.** The repeated-coordinate sector pays the exact one-word birthday
defect on either endpoint and otherwise has a free ambient endpoint. -/
theorem repeatedDepthDefect_card_le (G : Finset F) {t : ℕ} (ht : 0 < t) :
    (repeatedDepthDefect G t).card ≤
      2 * (G.card ^ t - G.card.descFactorial t) * G.card ^ t := by
  calc
    (repeatedDepthDefect G t).card ≤
        ((repeatedWords G t ×ˢ ambientWords G t) ∪
          (ambientWords G t ×ˢ repeatedWords G t)).card :=
      Finset.card_le_card (repeatedDepthDefect_subset_endpointRepeated ht)
    _ ≤ (repeatedWords G t ×ˢ ambientWords G t).card +
        (ambientWords G t ×ˢ repeatedWords G t).card := Finset.card_union_le _ _
    _ = 2 * (G.card ^ t - G.card.descFactorial t) * G.card ^ t := by
      rw [Finset.card_product, Finset.card_product, repeatedWords_card, ambientWords_card]
      ring

/-- The G159 exact split plus the unconditional birthday ceiling. -/
theorem depthFiber_le_core_mul_factorial_sq_add_birthday (G : Finset F) {t : ℕ} (ht : 0 < t) :
    depthFiber G t t ≤ (subsetCorePairs G t).card * (t.factorial ^ 2) +
      2 * (G.card ^ t - G.card.descFactorial t) * G.card ^ t :=
  (depthFiber_le_core_mul_factorial_sq_add_iff G t _).mpr
    (repeatedDepthDefect_card_le G ht)

#print axioms injectiveWords_card
#print axioms repeatedWords_card
#print axioms repeatedDepthDefect_subset_endpointRepeated
#print axioms repeatedDepthDefect_card_le
#print axioms depthFiber_le_core_mul_factorial_sq_add_birthday

end ArkLib.ProximityGap.Frontier.G160RepeatedDefectAmbientBound

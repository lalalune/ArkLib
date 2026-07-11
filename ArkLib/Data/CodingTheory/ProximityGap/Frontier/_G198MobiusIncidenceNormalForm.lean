/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._G197F5MobiusSignRefuted

/-!
# G198: depth-three Möbius covariance as an incidence discrepancy

The signed term from G195 has an exact counting normal form.  Parameterize the canonical pair
collision by `(x,z) ∈ G²`, with target `2x+z`, and the triple collision by `a ∈ G`, with
target `3a`.  If

`N = ∑_t #{(x,z) ∈ G² : 2x+z=t} #{a ∈ G : 3a=t}`,

then

`⟨B,C⟩_c = |F| N - |G|³`.

Thus the false universal sign condition is exactly the false assertion that this incidence count
always exceeds its uniform baseline `|G|³/|F|`.  The viable target is a magnitude/discrepancy
bound for `|F|N-|G|³`.

Issue #466.
-/

set_option autoImplicit false

namespace ArkLib.ProximityGap.Frontier.G198MobiusIncidenceNormalForm

open scoped BigOperators
open ArkLib.ProximityGap.Frontier.G175CenteredDeletionMonotonicityNoGo
open ArkLib.ProximityGap.Frontier.G176RepetitionDefectCovariance
open ArkLib.ProximityGap.Frontier.G179RepetitionPenaltyTransfer
open ArkLib.ProximityGap.Frontier.G182AllDepthDefectCarrier
open ArkLib.ProximityGap.Frontier.G183PairCollisionEnergyReduction
open ArkLib.ProximityGap.Frontier.G192DepthThreeSymmetricPatterns
open ArkLib.ProximityGap.Frontier.G194DepthThreeMobiusTransform
open ArkLib.ProximityGap.Frontier.G195DepthThreeCenteredMobius

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

noncomputable def pairParamFiber (G : Finset F) (t : F) : Finset (F × F) :=
  (G ×ˢ G).filter fun xz => xz.1 + xz.1 + xz.2 = t

noncomputable def tripleParamFiber (G : Finset F) (t : F) : Finset F :=
  G.filter fun a => a + a + a = t

theorem pairCollisionFiber_three_card_eq_pairParamFiber (G : Finset F) (t : F) :
    (pairCollisionFiber G 3 t ((0 : Fin 3), (1 : Fin 3))).card =
      (pairParamFiber G t).card := by
  classical
  apply Finset.card_bij (fun v _ => (v 0, v 2))
  · intro v hv
    rw [pairCollisionFiber, Finset.mem_filter, tupleSumFiber,
      Finset.mem_filter, Fintype.mem_piFinset] at hv
    rw [pairParamFiber, Finset.mem_filter, Finset.mem_product]
    refine ⟨⟨hv.1.1 0, hv.1.1 2⟩, ?_⟩
    simpa [Fin.sum_univ_succ, hv.2, add_assoc] using hv.1.2
  · intro v hv w hw heq
    rw [pairCollisionFiber, Finset.mem_filter] at hv hw
    funext i
    have h0 : v 0 = w 0 := congrArg Prod.fst heq
    have h2 : v 2 = w 2 := congrArg Prod.snd heq
    fin_cases i
    · exact h0
    · exact hv.2.symm.trans (h0.trans hw.2)
    · exact h2
  · intro xz hxz
    let v : Fin 3 → F := ![xz.1, xz.1, xz.2]
    refine ⟨v, ?_, ?_⟩
    · rw [pairParamFiber, Finset.mem_filter, Finset.mem_product] at hxz
      rw [pairCollisionFiber, Finset.mem_filter, tupleSumFiber,
        Finset.mem_filter, Fintype.mem_piFinset]
      refine ⟨⟨?_, ?_⟩, by simp [v]⟩
      · intro i
        fin_cases i <;> simp [v, hxz.1]
      · simpa [v, Fin.sum_univ_succ, add_assoc] using hxz.2
    · simp [v]

theorem allThreeEqualFiber_card_eq_tripleParamFiber (G : Finset F) (t : F) :
    (allThreeEqualFiber G t).card = (tripleParamFiber G t).card := by
  classical
  apply Finset.card_bij (fun v _ => v 0)
  · intro v hv
    rw [allThreeEqualFiber, Finset.mem_filter, repeatedTupleSumFiber,
      Finset.mem_filter, tupleSumFiber, Finset.mem_filter, Fintype.mem_piFinset] at hv
    rw [tripleParamFiber, Finset.mem_filter]
    refine ⟨hv.1.1.1 0, ?_⟩
    simpa [Fin.sum_univ_succ, hv.2.1, hv.2.2, add_assoc] using hv.1.1.2
  · intro v hv w hw heq
    rw [allThreeEqualFiber, Finset.mem_filter] at hv hw
    funext i
    have h0 : v 0 = w 0 := heq
    fin_cases i
    · exact h0
    · exact hv.2.1.symm.trans (h0.trans hw.2.1)
    · exact hv.2.2.symm.trans
        (hv.2.1.symm.trans (h0.trans (hw.2.1.trans hw.2.2)))
  · intro a ha
    let v : Fin 3 → F := ![a, a, a]
    refine ⟨v, ?_, by simp [v]⟩
    rw [tripleParamFiber, Finset.mem_filter] at ha
    rw [allThreeEqualFiber, Finset.mem_filter, repeatedTupleSumFiber,
      Finset.mem_filter, tupleSumFiber, Finset.mem_filter, Fintype.mem_piFinset]
    refine ⟨⟨⟨?_, ?_⟩, ?_⟩, by simp [allThreeEqual, v]⟩
    · intro i
      fin_cases i <;> simp [v, ha.1]
    · simpa [v, Fin.sum_univ_succ, add_assoc] using ha.2
    · intro hinj
      exact Fin.zero_ne_one (hinj (by simp [v]))

theorem sum_pairParamFiber_card (G : Finset F) :
    ∑ t : F, (pairParamFiber G t).card = G.card ^ 2 := by
  classical
  let P := G ×ˢ G
  have hmaps : ∀ xz ∈ P, xz.1 + xz.1 + xz.2 ∈ (Finset.univ : Finset F) := by simp
  have h := Finset.card_eq_sum_card_fiberwise hmaps
  simpa [P, pairParamFiber, Finset.card_product, pow_two] using h.symm

theorem sum_tripleParamFiber_card (G : Finset F) :
    ∑ t : F, (tripleParamFiber G t).card = G.card := by
  classical
  have hmaps : ∀ a ∈ G, a + a + a ∈ (Finset.univ : Finset F) := by simp
  have h := Finset.card_eq_sum_card_fiberwise hmaps
  simpa [tripleParamFiber] using h.symm

theorem sum_pair01Profile (G : Finset F) :
    ∑ t : F, pair01Profile G t = (G.card : ℝ) ^ 2 := by
  unfold pair01Profile
  simp_rw [pairCollisionFiber_three_card_eq_pairParamFiber]
  rw [← Nat.cast_sum, sum_pairParamFiber_card]
  norm_num

theorem sum_allThreeEqualProfile (G : Finset F) :
    ∑ t : F, allThreeEqualProfile G t = G.card := by
  unfold allThreeEqualProfile
  simp_rw [allThreeEqualFiber_card_eq_tripleParamFiber]
  rw [← Nat.cast_sum, sum_tripleParamFiber_card]

noncomputable def pairTripleIncidenceCount (G : Finset F) : ℕ :=
  ∑ t : F, (pairParamFiber G t).card * (tripleParamFiber G t).card

theorem sum_pair01_mul_allThree_eq_incidence (G : Finset F) :
    ∑ t : F, pair01Profile G t * allThreeEqualProfile G t =
      pairTripleIncidenceCount G := by
  unfold pair01Profile allThreeEqualProfile pairTripleIncidenceCount
  simp_rw [pairCollisionFiber_three_card_eq_pairParamFiber,
    allThreeEqualFiber_card_eq_tripleParamFiber]
  push_cast
  rfl

/-- **Exact depth-three covariance/incidence normal form.** -/
theorem pair_triple_centeredInner_eq_incidence_discrepancy (G : Finset F) :
    centeredInner (pair01Profile G) (allThreeEqualProfile G) =
      (Fintype.card F : ℝ) * pairTripleIncidenceCount G - (G.card : ℝ) ^ 3 := by
  unfold centeredInner
  rw [sum_pair01_mul_allThree_eq_incidence, sum_pair01Profile,
    sum_allThreeEqualProfile]
  ring

theorem pair_triple_centeredInner_nonneg_iff_incidence_ge_uniform (G : Finset F) :
    0 ≤ centeredInner (pair01Profile G) (allThreeEqualProfile G) ↔
      (G.card : ℝ) ^ 3 ≤
        (Fintype.card F : ℝ) * pairTripleIncidenceCount G := by
  rw [pair_triple_centeredInner_eq_incidence_discrepancy]
  exact sub_nonneg

theorem abs_pair_triple_centeredInner_eq_incidence_discrepancy (G : Finset F) :
    |centeredInner (pair01Profile G) (allThreeEqualProfile G)| =
      |(Fintype.card F : ℝ) * pairTripleIncidenceCount G - (G.card : ℝ) ^ 3| := by
  rw [pair_triple_centeredInner_eq_incidence_discrepancy]

/-- The complete depth-three defect energy in incidence coordinates. -/
theorem factorialRepetitionDefect_three_centeredMass_eq_incidence (G : Finset F) :
    centeredSqMass (factorialRepetitionDefect G 3) =
      9 * centeredSqMass (pair01Profile G) +
        4 * centeredSqMass (allThreeEqualProfile G) -
          12 * ((Fintype.card F : ℝ) * pairTripleIncidenceCount G -
            (G.card : ℝ) ^ 3) := by
  rw [factorialRepetitionDefect_three_centeredMass_eq_mobius,
    pair_triple_centeredInner_eq_incidence_discrepancy]

#print axioms pairCollisionFiber_three_card_eq_pairParamFiber
#print axioms allThreeEqualFiber_card_eq_tripleParamFiber
#print axioms sum_pairParamFiber_card
#print axioms sum_tripleParamFiber_card
#print axioms sum_pair01Profile
#print axioms sum_allThreeEqualProfile
#print axioms pair_triple_centeredInner_eq_incidence_discrepancy
#print axioms pair_triple_centeredInner_nonneg_iff_incidence_ge_uniform
#print axioms abs_pair_triple_centeredInner_eq_incidence_discrepancy
#print axioms factorialRepetitionDefect_three_centeredMass_eq_incidence

end ArkLib.ProximityGap.Frontier.G198MobiusIncidenceNormalForm

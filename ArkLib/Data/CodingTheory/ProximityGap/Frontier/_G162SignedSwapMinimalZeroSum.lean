/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._G161NegationStabilizerRigidity

/-!
# G162: signed-swap primitive packets reduce to minimal zero-sum supports

G161 eliminates endpointwise-negation-fixed primitive packets above depth two.  The other fixed
class for the swap/negation Klein-four action has the form `(S, -S)`.  In a group with no
two-torsion, balance forces `sum S = 0`.  Primitivity then forces `S` to be minimal zero-sum:
every nonempty proper subset has nonzero sum, since a zero-sum subset `A` would create the proper
balanced signed subcore `(A, -A)`.

The finite signed-swap primitive census therefore injects into the finite census of minimal
zero-sum `t`-subsets.  This identifies the last symmetry stabilizer as a classical zero-sum
sequence problem rather than an unrestricted additive-energy problem.

Issue #466.
-/

set_option autoImplicit false

namespace ArkLib.ProximityGap.Frontier.G162SignedSwapMinimalZeroSum

open scoped BigOperators
open ArkLib.ProximityGap.Frontier.G147ConnectedBalancedCoreRecursion
open ArkLib.ProximityGap.Frontier.G145LowerDepthMultiplicityEnvelope
open ArkLib.ProximityGap.Frontier.G152DepthFourCompositeCensus

variable {F : Type*} [AddCommGroup F] [Fintype F] [DecidableEq F]

def negFinset (S : Finset F) : Finset F := S.image Neg.neg

def signedCore (S : Finset F) : Finset F × Finset F := (S, negFinset S)

def IsMinimalZeroSum (S : Finset F) : Prop :=
  S.Nonempty ∧ (∑ x ∈ S, x) = 0 ∧
    ∀ A : Finset F, A.Nonempty → A ⊆ S → A ≠ S → (∑ x ∈ A, x) ≠ 0

theorem negFinset_card (S : Finset F) : (negFinset S).card = S.card := by
  exact Finset.card_image_of_injective S neg_injective

theorem sum_negFinset (S : Finset F) :
    ∑ x ∈ negFinset S, x = -(∑ x ∈ S, x) := by
  rw [negFinset, Finset.sum_image]
  · exact Finset.sum_neg_distrib (fun x : F => x)
  · intro a ha b hb hab
    exact neg_injective hab

theorem negFinset_mono {A S : Finset F} (hAS : A ⊆ S) : negFinset A ⊆ negFinset S := by
  intro x hx
  obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hx
  exact Finset.mem_image.mpr ⟨a, hAS ha, rfl⟩

/-- A signed core which is balanced has zero left sum when doubling has trivial kernel. -/
theorem sum_eq_zero_of_signedCore_balanced
    (htwo : ∀ z : F, z + z = 0 → z = 0) {S : Finset F}
    (hbal : IsBalancedCore (signedCore S)) : (∑ x ∈ S, x) = 0 := by
  have heq : (∑ x ∈ S, x) = -(∑ x ∈ S, x) := by
    simpa [signedCore, sum_negFinset] using hbal.2.2.2
  apply htwo
  calc
    (∑ x ∈ S, x) + ∑ x ∈ S, x =
        (∑ x ∈ S, x) + -(∑ x ∈ S, x) := congrArg ((∑ x ∈ S, x) + ·) heq
    _ = 0 := add_neg_cancel _

/-- Any zero-sum sub-support of a signed core gives a balanced signed subcore. -/
theorem signedSubcore_balanced {S A : Finset F}
    (hSbal : IsBalancedCore (signedCore S))
    (hAne : A.Nonempty) (hAS : A ⊆ S) (hAsum : (∑ x ∈ A, x) = 0) :
    IsBalancedCore (signedCore A) := by
  refine ⟨hAne, ?_, ?_, ?_⟩
  · exact (negFinset_card A).symm
  · exact hSbal.2.2.1.mono hAS (negFinset_mono hAS)
  · rw [signedCore, sum_negFinset, hAsum, neg_zero]

/-- A proper zero-sum subset creates a proper balanced subcore of the signed packet. -/
theorem signedSubcore_proper {S A : Finset F}
    (hSbal : IsBalancedCore (signedCore S))
    (hAne : A.Nonempty) (hAS : A ⊆ S) (hAproper : A ≠ S)
    (hAsum : (∑ x ∈ A, x) = 0) :
    IsProperBalancedSubcore (signedCore A) (signedCore S) :=
  ⟨signedSubcore_balanced hSbal hAne hAS hAsum, hAS, negFinset_mono hAS, hAproper⟩

/-- **Pointwise G162 capstone.** Signed-swap primitivity forces a minimal zero-sum support. -/
theorem minimalZeroSum_of_signedCore_primitive
    (htwo : ∀ z : F, z + z = 0 → z = 0) {S : Finset F}
    (hprim : IsPrimitiveBalancedCore (signedCore S)) : IsMinimalZeroSum S := by
  refine ⟨hprim.1.1, sum_eq_zero_of_signedCore_balanced htwo hprim.1, ?_⟩
  intro A hAne hAS hAproper hAsum
  exact hprim.2 ⟨signedCore A,
    signedSubcore_proper hprim.1 hAne hAS hAproper hAsum⟩

noncomputable def signedSwapPrimitiveCorePairs (G : Finset F) (t : ℕ) :
    Finset (Finset F × Finset F) :=
  (primitiveCorePairs G t).filter fun c => c.2 = negFinset c.1

noncomputable def minimalZeroSumSupports (G : Finset F) (t : ℕ) : Finset (Finset F) :=
  by
    classical
    exact (G.powersetCard t).filter IsMinimalZeroSum

/-- Every signed-swap primitive core maps to its minimal zero-sum left support. -/
theorem left_mem_minimalZeroSumSupports
    (htwo : ∀ z : F, z + z = 0 → z = 0) {G : Finset F} {t : ℕ}
    {c : Finset F × Finset F} (hc : c ∈ signedSwapPrimitiveCorePairs G t) :
    c.1 ∈ minimalZeroSumSupports G t := by
  classical
  rw [signedSwapPrimitiveCorePairs, Finset.mem_filter] at hc
  obtain ⟨hcPrimMem, hsigned⟩ := hc
  rw [primitiveCorePairs, Finset.mem_filter] at hcPrimMem
  obtain ⟨hcCore, hcPrim⟩ := hcPrimMem
  rw [minimalZeroSumSupports, Finset.mem_filter]
  refine ⟨(mem_subsetCorePairs_iff.mp hcCore).1, ?_⟩
  have hcoreEq : c = signedCore c.1 := by
    apply Prod.ext
    · rfl
    · exact hsigned
  rw [hcoreEq] at hcPrim
  exact minimalZeroSum_of_signedCore_primitive htwo hcPrim

/-- **Finite G162 capstone.** The remaining signed-swap fixed primitive sector injects into the
minimal zero-sum support census. -/
theorem signedSwapPrimitiveCorePairs_card_le_minimalZeroSumSupports
    (htwo : ∀ z : F, z + z = 0 → z = 0) (G : Finset F) (t : ℕ) :
    (signedSwapPrimitiveCorePairs G t).card ≤ (minimalZeroSumSupports G t).card := by
  classical
  exact Finset.card_le_card_of_injOn Prod.fst
    (fun _ hc => left_mem_minimalZeroSumSupports htwo hc)
    (fun c hc d hd h => by
      apply Prod.ext
      · exact h
      · rw [(Finset.mem_filter.mp hc).2, (Finset.mem_filter.mp hd).2, h])

#print axioms sum_eq_zero_of_signedCore_balanced
#print axioms signedSubcore_proper
#print axioms minimalZeroSum_of_signedCore_primitive
#print axioms left_mem_minimalZeroSumSupports
#print axioms signedSwapPrimitiveCorePairs_card_le_minimalZeroSumSupports

end ArkLib.ProximityGap.Frontier.G162SignedSwapMinimalZeroSum

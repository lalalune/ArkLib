/-
Copyright (c) 2024-2025 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Katerina Hristova
-/

import ArkLib.Data.CodingTheory.ProximityGap.ProximityGenerators
import Mathlib.Data.Rat.Star
import Mathlib.Order.CompletePartialOrder
import Mathlib.Probability.Distributions.Uniform
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.LinearAlgebra.TensorProduct.Defs
import Mathlib.Data.Matrix.Mul
import Mathlib.Data.Matrix.Diagonal
import Mathlib

/-!
# Proximity Generators fundamental definitions

Define the fundamental concepts for different types of generators functions used in coding theory.

## Main Results



## References

* [Guruswami, V., Rudra, A., Sudan M., *Essential Coding Theory*, online copy][GRS25]
* [Bordage, S., Chiesa, A., Guan, Z., Manzur, I., *All Polynomial Generators Preserve Distance
with Mutual Correlated Agreement*][BSGM25]. Full paper : https://eprint.iacr.org/2025/2051}
-/

section

namespace LinearTransformations

open NNReal ENNReal unitInterval LinearCode CoreDefinitions
open scoped ProbabilityTheory

variable {ι : Type} [Fintype ι]
         {F : Type} [Field F] [Fintype F]
         {ℓ ℓ' : Type} [Fintype ℓ] [Fintype ℓ']
         {S : Type}

def hasPseudoLeftInverse [DecidableEq ℓ'] (A : Matrix ℓ ℓ' F) : Prop :=
 ∃ B : Matrix ℓ' ℓ F, B * A = 1

noncomputable def pseudoInverse [DecidableEq ℓ'] (A : Matrix ℓ ℓ' F) (hA : hasPseudoLeftInverse A) :
  Matrix ℓ' ℓ F := Classical.choose hA

def isPseudoLeftInverse [DecidableEq ℓ'] (A : Matrix ℓ ℓ' F) (B : Matrix ℓ' ℓ F) : Prop :=
    B * A = 1

lemma pseudoLeftInverse [DecidableEq ℓ'] (A : Matrix ℓ ℓ' F)
  (hA : Matrix.colRank A = Fintype.card ℓ') :
  let B :=  (A.transpose * A)⁻¹ * (A.transpose)
  (isPseudoLeftInverse A B) := by
  sorry

/-- Generator `G'` inside Lemma 4.1 [BSGM25] -/
def pseudoInvNewGen [DecidableEq ℓ']
{S : Type} [Nonempty S] [Fintype S] (G : Generator S ℓ F)
(A : Matrix ℓ ℓ' F) : Generator S ℓ' F := fun x ↦ (Matrix.vecMul (G x) A)

/-- Lemma 4.1 [BSGM25] -/
lemma pseudoinverseGen [DecidableEq ℓ']
{S : Type} [Nonempty S] [Fintype S] (G : Generator S ℓ F) (ε_mca : I → I) (LC : LinearCode ι F)
(hG : IsMCAGenerator G ε_mca LC) (A : Matrix ℓ ℓ' F) (hA : hasPseudoLeftInverse A) :
IsMCAGenerator (pseudoInvNewGen G A) ε_mca LC := by sorry

/-- Generator `G'` inside Corollary 4.2 [BSGM25] -/
def neSubsetGen
{S : Type} [Nonempty S] [Fintype S] (G : Generator S ℓ F) (κ : Set ℓ)
: Generator S κ F := fun x ↦ Set.restrict κ (G x)

/-- Corollary 4.2 [BSGM25]-/
lemma generatorSubset [DecidableEq ℓ']
{S : Type} [Nonempty S] [Fintype S] (G : Generator S ℓ F) (ε_mca : I → I) (LC : LinearCode ι F)
(hG : IsMCAGenerator G ε_mca LC) (κ : Set ℓ) (hκ : Nonempty κ) :
  IsMCAGenerator (neSubsetGen G κ) ε_mca LC := by sorry


end LinearTransformations

end

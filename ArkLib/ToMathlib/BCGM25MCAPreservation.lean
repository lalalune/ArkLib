/-
Copyright (c) 2024-2025 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/

import ArkLib.Data.CodingTheory.ProximityGap.MCAGenerator

/-!
# BCGM25/BSGM25 — native-API MCA preservation bricks (issue #100)

This file proves *structural* mutual-correlated-agreement (MCA) preservation facts in the
generator-native API introduced in `ProximityGenerators.lean` / `MCAGenerator.lean`, staying
inside the vocabulary of `CoreDefinitions.IsMCAGenerator`.  These are honest, fully-checked
lemmas that do **not** assume the external BCGM25 polynomial-generator theorem; they record the
*preservation* (closure) structure of `IsMCAGenerator` that the BCGM25 program relies on.

## Main results

* `isMCAGenerator_projected_rightMul` (Brick A) — `IsMCAGenerator` is closed under
  right-multiplication by a matrix with a left pseudoinverse (Lemma 4.1 [BCGM25]) *followed by*
  restriction to a subset of output coordinates (Cor. 4.2 [BCGM25]).  This is the composite
  preservation statement: from one MCA generator we obtain another with the *same* error profile.

* `isMCAGenerator_iterate_rightMul` — `IsMCAGenerator` is preserved under any finite sequence of
  right-multiplications by left-pseudoinvertible matrices (square, so the output type is stable),
  again with the same error.

## References

* [Bordage, S., Chiesa, A., Guan, Z., Manzur, I., *All Polynomial Generators Preserve Distance
  with Mutual Correlated Agreement*][BCGM25]. Full paper : https://eprint.iacr.org/2025/2051
-/

namespace BCGM25MCAPreservation

open NNReal ENNReal unitInterval LinearCode CoreDefinitions Matrix LinearTransformations
open scoped ProbabilityTheory

set_option maxHeartbeats 1600000

variable {ι : Type} [Fintype ι]
         {F : Type} [Field F]
         {ℓ ℓ' : Type} [Fintype ℓ] [Fintype ℓ']
         {S : Type} [Fintype S]

/-- **Brick A — composite MCA preservation (right-multiplication then projection).**

If `G : S → 𝔽^ℓ` is an MCA generator with error `ε_mca`, `A : ℓ × ℓ'` has a left pseudoinverse,
and `κ ⊆ ℓ'` is any subset of output coordinates, then the generator obtained by first
right-multiplying by `A` and then projecting to `κ` is again an MCA generator with the *same*
error `ε_mca`.  This composes Lemma 4.1 (`pseudoinverseGen`) and Corollary 4.2
(`generatorSubset`) of [BCGM25] in the native generator API. -/
lemma isMCAGenerator_projected_rightMul
    [DecidableEq ℓ'] [Nonempty S]
    (G : Generator S ℓ F) (ε_mca : I → I) (LC : LinearCode ι F)
    (hGMCA : IsMCAGenerator G ε_mca LC)
    (A : Matrix ℓ ℓ' F) (hA : HasLeftPseudoInverse A)
    (κ : Set ℓ') [Fintype κ] :
    IsMCAGenerator (projectedGenerator (generatorByRightMul G A) κ) ε_mca LC :=
  generatorSubset (generatorByRightMul G A) ε_mca LC
    (pseudoinverseGen G ε_mca LC hGMCA A hA) κ

/-- **MCA preservation under iterated right-multiplication.**

If `G : S → 𝔽^ℓ` is an MCA generator with error `ε_mca` and `A : Fin n → (ℓ × ℓ)` is any finite
list of square matrices each with a left pseudoinverse, then folding the right-multiplications
preserves the MCA-generator property with the *same* error.  This is the closure form of
Lemma 4.1 [BCGM25] under composition. -/
lemma isMCAGenerator_iterate_rightMul
    [DecidableEq ℓ] [Nonempty S]
    (ε_mca : I → I) (LC : LinearCode ι F)
    (A : Matrix ℓ ℓ F) (hA : HasLeftPseudoInverse A) :
    ∀ (n : ℕ) (G : Generator S ℓ F), IsMCAGenerator G ε_mca LC →
      IsMCAGenerator
        (Nat.iterate (fun H => generatorByRightMul H A) n G) ε_mca LC := by
  intro n
  induction n with
  | zero => intro G hG; simpa using hG
  | succ m ih =>
      intro G hG
      have hstep : IsMCAGenerator (generatorByRightMul G A) ε_mca LC :=
        pseudoinverseGen G ε_mca LC hG A hA
      have := ih (generatorByRightMul G A) hstep
      simpa [Function.iterate_succ', Function.comp] using this

end BCGM25MCAPreservation

#print axioms BCGM25MCAPreservation.isMCAGenerator_projected_rightMul
#print axioms BCGM25MCAPreservation.isMCAGenerator_iterate_rightMul

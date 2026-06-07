/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import Mathlib.Algebra.Polynomial.BigOperators
import Mathlib.Algebra.Polynomial.Degree.Lemmas
import Mathlib.Tactic

/-!
# STIR Combine-operator degree bound (issue #24)

The polynomial-level degree bound underlying STIR's `Combine` operator (ACFY24 / STIR §4.5,
Def. 4.11 / Lemma 4.12): the combined polynomial
`∑ᵢ C(rᵉⁱ)·gᵢ·(∑_{l ≤ dstar - degs i} (X·C r)^l)` has `natDegree ≤ dstar` whenever each `gᵢ`
has degree `≤ degs i ≤ dstar`. Stated and proved with mathlib `Polynomial` operations only.
-/

open Polynomial

namespace Polynomial

/-- The STIR geometric factor `∑_{l ≤ d} (X·C r)^l` has `natDegree ≤ d`. -/
theorem geomFactor_natDegree_le {F : Type*} [Field F] (r : F) (d : ℕ) :
    (∑ l ∈ Finset.range (d + 1), (X * C r) ^ l).natDegree ≤ d := by
  apply Polynomial.natDegree_sum_le_of_forall_le
  intro l hl
  rw [Finset.mem_range] at hl
  calc ((X * C r) ^ l).natDegree
      ≤ l * (X * C r).natDegree := natDegree_pow_le
    _ ≤ l * 1 := by
        gcongr
        calc (X * C r).natDegree ≤ X.natDegree + (C r).natDegree := natDegree_mul_le
          _ = 1 := by simp [natDegree_X, natDegree_C]
    _ = l := mul_one l
    _ ≤ d := by omega

/-- **STIR Combine-operator degree bound.** The combined polynomial
`∑ᵢ C(rᵉⁱ)·gᵢ·(∑_{l ≤ dstar - degs i} (X·C r)^l)` has `natDegree ≤ dstar`, given
`(g i).natDegree ≤ degs i ≤ dstar` for each `i`. -/
theorem combinePoly_natDegree_le {F : Type*} [Field F] {m : ℕ} (dstar : ℕ) (r : F)
    (e : Fin m → ℕ) (g : Fin m → Polynomial F) (degs : Fin m → ℕ)
    (hg : ∀ i, (g i).natDegree ≤ degs i) (hle : ∀ i, degs i ≤ dstar) :
    (∑ i, C (r ^ e i) * g i
      * (∑ l ∈ Finset.range (dstar - degs i + 1), (X * C r) ^ l)).natDegree ≤ dstar := by
  apply Polynomial.natDegree_sum_le_of_forall_le
  intro i _
  have hd := hle i
  calc (C (r ^ e i) * g i
        * (∑ l ∈ Finset.range (dstar - degs i + 1), (X * C r) ^ l)).natDegree
      ≤ (C (r ^ e i) * g i).natDegree
          + (∑ l ∈ Finset.range (dstar - degs i + 1), (X * C r) ^ l).natDegree := natDegree_mul_le
    _ ≤ ((C (r ^ e i)).natDegree + (g i).natDegree) + (dstar - degs i) := by
        gcongr
        · exact natDegree_mul_le
        · exact geomFactor_natDegree_le r (dstar - degs i)
    _ ≤ (0 + degs i) + (dstar - degs i) := by
        gcongr
        · simp [natDegree_C]
        · exact hg i
    _ = dstar := by omega

end Polynomial

#print axioms Polynomial.geomFactor_natDegree_le
#print axioms Polynomial.combinePoly_natDegree_le

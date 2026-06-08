import ArkLib.Data.CodingTheory.GuruswamiSudan.DictionaryBridge
import ArkLib.ToMathlib.BivariateDegreeToolkit

/-! The `(1,k)`-weighted degree of `toPoly c` is `< D`: every monomial of `toPoly` has bidegree
in `monoIdx k D`, i.e. weighted degree `< D`. This makes the dictionary interpolant
`exists_bivariate_vanishing` a genuine **bounded-degree** Guruswami–Sudan witness. -/

open Polynomial

namespace GSMultInterp

variable {F : Type} [Field F] [DecidableEq F]

/-- Off the index set `monoIdx`, the bidegree coefficient of `toPoly c` vanishes. -/
theorem toPoly_coeff_zero_of_not_mem (k D : ℕ) (c : CoeffSpace (F := F) k D) (s j : ℕ)
    (h : (s, j) ∉ monoIdx k D) :
    ((toPoly k D c).coeff j).coeff s = 0 := by
  classical
  rw [toPoly, Polynomial.finset_sum_coeff, Polynomial.finset_sum_coeff]
  refine Finset.sum_eq_zero (fun st _ => ?_)
  rcases eq_or_ne st.1.2 j with h2 | h2
  · rcases eq_or_ne st.1.1 s with h1 | h1
    · refine absurd ?_ h
      have hst1 : st.1 = (s, j) := Prod.ext h1 h2
      rw [← hst1]; exact st.2
    · simp [Polynomial.coeff_monomial, h2, h1]
  · simp [Polynomial.coeff_monomial, h2]

/-- **Bounded weighted degree.** `natWeightedDegree (toPoly c) 1 k < D` (for `0 < D`). -/
theorem toPoly_natWeightedDegree_lt (k D : ℕ) (hD : 0 < D) (c : CoeffSpace (F := F) k D) :
    Polynomial.Bivariate.natWeightedDegree (toPoly k D c) 1 k < D := by
  rw [Polynomial.Bivariate.natWeightedDegree, Finset.sup_lt_iff hD]
  intro j hj
  simp only [one_mul]
  by_contra hcon
  push_neg at hcon
  have hne : (toPoly k D c).coeff j ≠ 0 := Polynomial.mem_support_iff.mp hj
  have hcoeff : ((toPoly k D c).coeff j).coeff ((toPoly k D c).coeff j).natDegree ≠ 0 :=
    Polynomial.leadingCoeff_ne_zero.mpr hne
  have hnotmem : (((toPoly k D c).coeff j).natDegree, j) ∉ monoIdx k D := by
    rw [mem_monoIdx]; push_neg; intro _ _; omega
  exact hcoeff (toPoly_coeff_zero_of_not_mem k D c _ j hnotmem)

#print axioms GSMultInterp.toPoly_coeff_zero_of_not_mem
#print axioms GSMultInterp.toPoly_natWeightedDegree_lt

end GSMultInterp

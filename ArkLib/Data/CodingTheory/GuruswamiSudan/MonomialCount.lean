import Mathlib
import ArkLib.Data.CodingTheory.GuruswamiSudan.MultiplicityInterpolation

/-! The exact count of the Guruswami–Sudan monomial index set `monoIdx k D` — the open
feasibility input `(monoIdx k D).card` of `exists_ne_zero_vanishesToOrder` (the companion to the
proven `card_multIdx = m(m+1)/2`). -/

open Finset

namespace GSMultInterp

/-- **The number of available monomials is `∑_{b<D} (D − k·b)`.** Partition `monoIdx k D` by the
`Y`-exponent `b`: for each `b`, the admissible `X`-exponents are `a < D − k·b`. -/
theorem card_monoIdx (k D : ℕ) :
    (monoIdx k D).card = ∑ b ∈ Finset.range D, (D - k * b) := by
  classical
  rw [monoIdx, Finset.card_filter, Finset.sum_product, Finset.sum_comm]
  refine Finset.sum_congr rfl (fun b _ => ?_)
  rw [← Finset.card_filter]
  have hset : (Finset.range D).filter (fun a => a + k * b < D) = Finset.range (D - k * b) := by
    ext a
    simp only [Finset.mem_filter, Finset.mem_range]
    omega
  rw [hset, Finset.card_range]

/-- **Clean lower bound for feasibility:** keeping only `Y`-exponents `b` with `k·b ≤ D/2`, each
contributes more than `D/2` monomials, so `(monoIdx k D).card` is at least `⌈D/(2k)⌉·⌈D/2⌉`-ish.
Concretely, every term with `b < D` and `k·b < D` is `≥ 1`, and the first `b = 0` term alone is
`D`; we record the simple consequence that the count is positive and `≥ D` whenever `0 < D`. -/
theorem card_monoIdx_ge (k D : ℕ) (hD : 0 < D) : D ≤ (monoIdx k D).card := by
  rw [card_monoIdx]
  calc D = D - k * 0 := by rw [Nat.mul_zero, Nat.sub_zero]
    _ ≤ ∑ b ∈ Finset.range D, (D - k * b) :=
        Finset.single_le_sum (f := fun b => D - k * b) (fun _ _ => Nat.zero_le _)
          (Finset.mem_range.mpr hD)

/-- **Parametric (floor-free) lower bound for feasibility.** Keeping only the first `t ≤ D`
`Y`-exponents gives `∑_{b<t}(D − k·b) ≤ (monoIdx k D).card`; choosing `t ≈ D/(2k)` recovers the
`≈ D²/(2k)` triangle bound the GS regime uses to satisfy `n·m(m+1)/2 < #monomials`. -/
theorem card_monoIdx_ge_partial (k D t : ℕ) (ht : t ≤ D) :
    ∑ b ∈ Finset.range t, (D - k * b) ≤ (monoIdx k D).card := by
  rw [card_monoIdx]
  exact Finset.sum_le_sum_of_subset_of_nonneg
    (Finset.range_mono ht) (fun _ _ _ => Nat.zero_le _)

/-- **Closed form of the partial monomial sum.** When the first `t` `Y`-exponents stay within the
degree budget (`k·(t−1) ≤ D`, so no truncation), `∑_{b<t}(D − k·b) = t·D − k·t(t−1)/2` — the
exact area of the GS staircase up to row `t`. -/
theorem sum_range_sub_kb (k D t : ℕ) (ht : k * (t - 1) ≤ D) :
    ∑ b ∈ Finset.range t, (D - k * b) = t * D - k * (t * (t - 1) / 2) := by
  cases t with
  | zero => simp
  | succ s =>
    have hb : ∀ b ∈ Finset.range (s + 1), k * b ≤ D := by
      intro b hbmem
      rw [Finset.mem_range] at hbmem
      calc k * b ≤ k * s := Nat.mul_le_mul_left k (by omega)
        _ ≤ D := by simpa using ht
    have hadd : ∑ b ∈ Finset.range (s + 1), (D - k * b)
        + ∑ b ∈ Finset.range (s + 1), (k * b) = ∑ _b ∈ Finset.range (s + 1), D := by
      rw [← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl (fun b hbmem => Nat.sub_add_cancel (hb b hbmem))
    rw [Finset.sum_const, Finset.card_range, smul_eq_mul] at hadd
    have hgauss : ∑ b ∈ Finset.range (s + 1), b = (s + 1) * s / 2 := by
      have h2 := Finset.sum_range_id_mul_two (s + 1)
      simp only [Nat.add_sub_cancel] at h2
      omega
    have hkb : ∑ b ∈ Finset.range (s + 1), (k * b) = k * ((s + 1) * s / 2) := by
      rw [← Finset.mul_sum, hgauss]
    rw [hkb] at hadd
    simp only [Nat.succ_sub_one]
    omega

/-- **Explicit triangle lower bound.** Combining the partial bound with its closed form: under
`k·(t−1) ≤ D` and `t ≤ D`, `t·D − k·t(t−1)/2 ≤ (monoIdx k D).card`. Choosing `t ≈ D/k` gives the
classical `≈ D²/(2k)` monomial count the GS regime checks against `n·m(m+1)/2`. -/
theorem card_monoIdx_ge_triangle (k D t : ℕ) (htk : k * (t - 1) ≤ D) (ht : t ≤ D) :
    t * D - k * (t * (t - 1) / 2) ≤ (monoIdx k D).card := by
  rw [← sum_range_sub_kb k D t htk]
  exact card_monoIdx_ge_partial k D t ht

variable {F : Type*} [Field F]

/-- **Directly-checkable GS interpolation feasibility.** If for some `t ≤ D` the partial monomial
sum `∑_{b<t}(D − k·b)` already exceeds the constraint count `n·m(m+1)/2`, then a nonzero
interpolant exists. This turns the abstract `(monoIdx k D).card` hypothesis of
`exists_ne_zero_vanishesToOrder` into a concrete arithmetic side condition the GS regime can
discharge by choosing `t ≈ D/(2k)`. -/
theorem exists_ne_zero_vanishesToOrder_of_partial_sum
    (k D m n t : ℕ) (xs ys : Fin n → F) (ht : t ≤ D)
    (hfeas : n * (m * (m + 1) / 2) < ∑ b ∈ Finset.range t, (D - k * b)) :
    ∃ c : CoeffSpace (F := F) k D, c ≠ 0 ∧
      ∀ i : Fin n, vanishesToOrder k D m c (xs i) (ys i) :=
  exists_ne_zero_vanishesToOrder k D m n xs ys
    (lt_of_lt_of_le hfeas (card_monoIdx_ge_partial k D t ht))

#print axioms GSMultInterp.card_monoIdx
#print axioms GSMultInterp.card_monoIdx_ge_partial
#print axioms GSMultInterp.card_monoIdx_ge
#print axioms GSMultInterp.sum_range_sub_kb
#print axioms GSMultInterp.card_monoIdx_ge_triangle
#print axioms GSMultInterp.exists_ne_zero_vanishesToOrder_of_partial_sum

end GSMultInterp

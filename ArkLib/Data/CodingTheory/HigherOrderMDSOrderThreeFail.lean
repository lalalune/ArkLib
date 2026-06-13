/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import Mathlib
import ArkLib.Data.CodingTheory.HigherOrderMDSReedSolomon


/-!
# Order-2 higher MDS is sharp: an explicit MDS frame failing order 3 (#389)

Companion to `HigherOrderMDSOrderTwo.lean` (`isHigherMDS_two_of_isMDSFrame`, which shows order 2 is
automatic for every MDS frame).  Here is an *explicit Reed–Solomon (hence MDS) frame that is not
higher-order MDS of order 3*, proving the order-2 ceiling is sharp and that the genuine GM-MDS
difficulty really does begin at order 3.

The construction exposes the mechanism by which explicit/structured domains fail: take three
disjoint pairs of evaluation points sharing a common **sum** — here `{0,10}, {1,9}, {2,8}`, all
summing to `10`.  In dimension `k = 3` the span of a pair `{a,b}` is the plane orthogonal to the
interpolation normal `(X−a)(X−b) = X² − (a+b)X + ab`, i.e. to the point `(ab, −(a+b), 1)`.  Equal
sums make the three normals lie in a common plane (their `(sum, product)` points are collinear), so
they are linearly dependent and the three pair-spans share the unexpected common vector
`w = (0,1,10)` — even though generic position would force their intersection to be `{0}`.
Axiom-clean.
-/
open Finset Module ArkLib.HigherOrderMDS

namespace ArkLib.HigherOrderMDS

/-- The 6 explicit evaluation points: three pairs `{0,10},{1,9},{2,8}` all summing to `10`. -/
def Dfail : Fin 6 → ℚ := ![0, 10, 1, 9, 2, 8]

/-- The common vector `(0,1,10)` lying in all three pair-spans (generic intersection is `{0}`). -/
def wfail : Fin 3 → ℚ := ![0, 1, 10]

/-- The three disjoint pairs (by index). -/
def Jfail : Fin 3 → Finset (Fin 6) := ![{0, 1}, {2, 3}, {4, 5}]

theorem Dfail_injective : Function.Injective Dfail := by
  intro i j h
  fin_cases i <;> fin_cases j <;> simp_all [Dfail]

theorem wfail_ne : wfail ≠ 0 := by
  intro h
  have := congrFun h 1
  simp [wfail] at this

/-- Order-3 higher MDS is **not** automatic: this explicit Reed–Solomon (hence MDS) frame fails it,
because the three pair-spans share the common vector `(0,1,10)` while generic intersection is `{0}`.
The mechanism: the pairs `{0,10},{1,9},{2,8}` share the sum `10`, so their interpolation normals
`(X−a)(X−b)` are linearly dependent (collinear `(sum,product)` points), forcing an unexpected
common vector.  Together with `isHigherMDS_two_of_isMDSFrame`, this pins the boundary: order 2
always holds, order 3 can fail. -/
theorem reedSolomonFrame_not_isHigherMDS_three :
    ¬ IsHigherMDS ℚ 3 (reedSolomonFrame Dfail 3) := by
  set v := reedSolomonFrame Dfail 3 with hv
  have hmds : IsMDSFrame ℚ v := reedSolomonFrame_isMDS Dfail_injective (by norm_num)
  -- membership helper
  have mem_pair : ∀ (J' : Finset (Fin 6)) (i₀ i₁ : Fin 6) (a b : ℚ),
      i₀ ∈ J' → i₁ ∈ J' → wfail = a • v i₀ + b • v i₁ → wfail ∈ frameSpan ℚ v J' := by
    intro J' i₀ i₁ a b h0 h1 hw
    rw [frameSpan, hw]
    exact Submodule.add_mem _
      (Submodule.smul_mem _ a (Submodule.subset_span ⟨i₀, Finset.mem_coe.mpr h0, rfl⟩))
      (Submodule.smul_mem _ b (Submodule.subset_span ⟨i₁, Finset.mem_coe.mpr h1, rfl⟩))
  have hw0 : wfail ∈ frameSpan ℚ v (Jfail 0) :=
    mem_pair _ 0 1 (-1/10) (1/10) (by decide) (by decide) (by
      ext j; fin_cases j <;> simp [wfail, hv, reedSolomonFrame, Dfail] <;> norm_num)
  have hw1 : wfail ∈ frameSpan ℚ v (Jfail 1) :=
    mem_pair _ 2 3 (-1/8) (1/8) (by decide) (by decide) (by
      ext j; fin_cases j <;> simp [wfail, hv, reedSolomonFrame, Dfail] <;> norm_num)
  have hw2 : wfail ∈ frameSpan ℚ v (Jfail 2) :=
    mem_pair _ 4 5 (-1/6) (1/6) (by decide) (by decide) (by
      ext j; fin_cases j <;> simp [wfail, hv, reedSolomonFrame, Dfail] <;> norm_num)
  apply not_higherMDS_of_not_generic (J := Jfail)
  · intro i; fin_cases i <;> simp [Jfail]
  · intro i j hij; fin_cases i <;> fin_cases j <;> simp_all [Jfail]
  · -- ¬ IsGenericInter: the intersection contains wfail ≠ 0, but generic codim would be 3
    intro hgen
    have hwmem : wfail ∈ ⨅ i, frameSpan ℚ v (Jfail i) := by
      rw [Submodule.mem_iInf]
      intro i; fin_cases i
      · exact hw0
      · exact hw1
      · exact hw2
    have hbot : (⨅ i, frameSpan ℚ v (Jfail i)) ≠ ⊥ := fun h => by
      rw [h, Submodule.mem_bot] at hwmem; exact wfail_ne hwmem
    have hpos : 1 ≤ finrank ℚ ↥(⨅ i, frameSpan ℚ v (Jfail i)) :=
      Submodule.one_le_finrank_iff.mpr hbot
    have hV : finrank ℚ (Fin 3 → ℚ) = 3 := by simp
    have hc : ∀ i, (Jfail i).card ≤ finrank ℚ (Fin 3 → ℚ) := by
      intro i; rw [hV]; fin_cases i <;> simp [Jfail]
    rw [IsGenericInter, Fin.sum_univ_three, codim_frameSpan hmds (hc 0),
      codim_frameSpan hmds (hc 1), codim_frameSpan hmds (hc 2), codim, hV] at hgen
    have hcard : ∀ i, (Jfail i).card = 2 := by intro i; fin_cases i <;> simp [Jfail]
    rw [hcard 0, hcard 1, hcard 2] at hgen
    omega

end ArkLib.HigherOrderMDS

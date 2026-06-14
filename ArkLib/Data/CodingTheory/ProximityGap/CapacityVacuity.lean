/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ReedSolomon
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.InformationTheory.Hamming
import Mathlib.LinearAlgebra.Lagrange
import Mathlib.Tactic

/-!
# Capacity-vacuity of the correlated-agreement premise (Issue #232)

The cleanest formal account of *why the Reed-Solomon proximity-gap problem is open up to capacity*:
**at the capacity error budget the "there is a nearby codeword" premise is satisfied by every word**,
so it carries no information and rigidity cannot be concluded from it alone.

This is the evaluation-domain form of the syndrome-space *capacity-vacuity* observation
(Okamoto, *The Syndrome-Space Lens*, eprint 2025/1712, Lemma 3.1 ⟹ Theorem 5.1: for an MDS/RS
code, any `m = n − deg` columns of the parity-check span the whole syndrome space, so at error
budget `k = m` every syndrome is realizable and the CA premise is information-theoretically vacuous).
Reed-Solomon codes are MDS, so we obtain it directly from Lagrange interpolation without any
parity-check machinery:

* `exists_codeword_hammingDist_le_redundancy` — **MDS covering radius ≤ redundancy.** Every word
  `w : ι → F` lies within Hamming distance `|ι| − deg` of `code domain deg`. Proof: interpolate `w`
  on any `deg`-element subset `S` of the domain; the interpolant has degree `< deg`, hence is a
  codeword, and it agrees with `w` on all of `S`, so it disagrees on at most `|ι| − deg` coordinates.

* `forall_exists_codeword_hammingDist_le_of_capacity` — **capacity-vacuity.** Consequently, at any
  error budget `t ≥ |ι| − deg` (relative `δ ≥ 1 − ρ`, i.e. at or beyond the capacity bound), *every*
  word — including an adversarially chosen one — has a codeword within budget. The correlated-
  agreement premise therefore imposes no constraint there: it is exactly the obstruction behind the
  open prize (#232), and it confirms (consistently with CS25/BCHKS25) that correlated agreement
  *cannot* hold unconditionally up to capacity.

* `okamoto_rank_condition_below_johnson` — **Okamoto's unconditional rank condition is
  sub-Johnson.** The paper's unconditional `r ≥ 2` branch needs `(r+1)δ < 1−ρ`, hence
  `δ < (1−ρ)/3`, and this cutoff is strictly below the Johnson radius `1−√ρ` for every
  `ρ ∈ (0,1)`. This arithmetic pin is the reason the syndrome-space lens does not close the
  prize window.

All closed results in this file are `sorry`-free and axiom-clean.

## References
- [Oka25] R. Okamoto. *The Syndrome-Space Lens*. eprint 2025/1712. (Theorem 5.1, capacity vacuity.)
- [ABF26] Arnon, Boneh, Fenzi. *Open Problems in List Decoding and Correlated Agreement*. 2026.
  Tracking issue #232.
-/

open Polynomial Finset

namespace ArkLib.ProximityGap.CapacityVacuity

open ReedSolomon

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {F : Type*} [Field F] [DecidableEq F]

/-- **MDS covering radius ≤ redundancy.** Every word `w : ι → F` lies within Hamming distance
`|ι| − deg` of the Reed-Solomon code `code domain deg`: interpolating `w` on any `deg`-element
subset of the domain yields a codeword agreeing there, hence disagreeing on at most `|ι| − deg`
coordinates. (Reed-Solomon codes are MDS, and an `[n, deg]` MDS code has covering radius `n − deg`.) -/
theorem exists_codeword_hammingDist_le_redundancy
    (domain : ι ↪ F) (deg : ℕ) (hdeg : deg ≤ Fintype.card ι) (w : ι → F) :
    ∃ c ∈ code domain deg, hammingDist w c ≤ Fintype.card ι - deg := by
  classical
  obtain ⟨S, hS_sub, hS_card⟩ := Finset.exists_subset_card_eq
    (s := (Finset.univ : Finset ι)) (n := deg) (by rw [Finset.card_univ]; exact hdeg)
  set p : F[X] := Lagrange.interpolate S domain.toFun w with hp
  have hinj : Set.InjOn domain.toFun (S : Set ι) := domain.injective.injOn
  have hdeglt : p.degree < (deg : WithBot ℕ) := by
    have := Lagrange.degree_interpolate_lt (s := S) (v := domain.toFun) (r := w) hinj
    rwa [hS_card] at this
  have hp_mem : p ∈ degreeLT F deg := (Polynomial.mem_degreeLT).mpr hdeglt
  set c : ι → F := evalOnPoints domain p with hc
  have hc_mem : c ∈ code domain deg := Submodule.mem_map.mpr ⟨p, hp_mem, rfl⟩
  have hagree : ∀ i ∈ S, c i = w i := by
    intro i hi
    have : p.eval (domain.toFun i) = w i :=
      Lagrange.eval_interpolate_at_node (s := S) (v := domain.toFun) (r := w) hinj hi
    simpa [hc, evalOnPoints] using this
  refine ⟨c, hc_mem, ?_⟩
  have hsub : Finset.filter (fun i => w i ≠ c i) Finset.univ ⊆ Finset.univ \ S := by
    intro i hi
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi
    rw [Finset.mem_sdiff]
    refine ⟨Finset.mem_univ i, fun hiS => hi ?_⟩
    exact (hagree i hiS).symm
  have hcard : hammingDist w c ≤ (Finset.univ \ S).card := by
    have hh : hammingDist w c = (Finset.filter (fun i => w i ≠ c i) Finset.univ).card := rfl
    rw [hh]; exact Finset.card_le_card hsub
  rwa [Finset.card_sdiff_of_subset hS_sub, Finset.card_univ, hS_card] at hcard

/-- **Capacity-vacuity of the correlated-agreement premise.** At any error budget `t ≥ |ι| − deg`
(relative distance `δ ≥ 1 − ρ`, i.e. at or beyond capacity), *every* word — including an
adversarially chosen one — has a codeword within budget. Hence the CA premise "there is a codeword
within the budget" carries no information at capacity: it cannot, on its own, force any rigidity.
This is the precise obstruction behind the open proximity prize (#232) and the evaluation-domain
form of the syndrome-space capacity-vacuity theorem. -/
theorem forall_exists_codeword_hammingDist_le_of_capacity
    (domain : ι ↪ F) (deg : ℕ) (hdeg : deg ≤ Fintype.card ι)
    (t : ℕ) (ht : Fintype.card ι - deg ≤ t) (w : ι → F) :
    ∃ c ∈ code domain deg, hammingDist w c ≤ t := by
  obtain ⟨c, hc, hdist⟩ := exists_codeword_hammingDist_le_redundancy domain deg hdeg w
  exact ⟨c, hc, le_trans hdist ht⟩

/-- **Okamoto's best unconditional radius cutoff is below Johnson.** For every rate
`ρ ∈ (0,1)`, `(1−ρ)/3 < 1−√ρ`. Thus any theorem whose largest unconditional reach is
`δ < (1−ρ)/3` is strictly sub-Johnson and cannot touch the prize window. -/
theorem okamoto_unconditional_cutoff_below_johnson {ρ : ℝ} (hρ0 : 0 < ρ) (hρ1 : ρ < 1) :
    (1 - ρ) / 3 < 1 - Real.sqrt ρ := by
  have hsq : Real.sqrt ρ ^ 2 = ρ := Real.sq_sqrt hρ0.le
  have hslt1 : Real.sqrt ρ < 1 := by
    rw [show (1 : ℝ) = Real.sqrt 1 by rw [Real.sqrt_one]]
    exact Real.sqrt_lt_sqrt hρ0.le hρ1
  have hsnonneg : 0 ≤ Real.sqrt ρ := Real.sqrt_nonneg ρ
  nlinarith [hsq, hslt1, hsnonneg]

/-- **The Okamoto rank condition forces the one-third cutoff.** If `r ≥ 2`, `δ ≥ 0`, and
`(r+1)δ < 1−ρ`, then necessarily `δ < (1−ρ)/3`. This is the exact arithmetic translation of
the paper's `(r+1)k < m+1` hypothesis after normalizing by block length. -/
theorem okamoto_rank_condition_radius_lt_third {ρ δ : ℝ} {r : ℕ}
    (hδ0 : 0 ≤ δ) (hr : 2 ≤ r)
    (hcond : ((r + 1 : ℕ) : ℝ) * δ < 1 - ρ) :
    δ < (1 - ρ) / 3 := by
  have h3 : (3 : ℝ) ≤ ((r + 1 : ℕ) : ℝ) := by
    exact_mod_cast Nat.succ_le_succ hr
  have h3δ : 3 * δ ≤ ((r + 1 : ℕ) : ℝ) * δ :=
    mul_le_mul_of_nonneg_right h3 hδ0
  have h3δ_lt : 3 * δ < 1 - ρ := lt_of_le_of_lt h3δ hcond
  nlinarith

/-- **Okamoto's unconditional rank condition is strictly below Johnson.** Combining the previous two
arithmetic facts: in rate `ρ ∈ (0,1)`, any nonnegative radius satisfying the unconditional
syndrome-space rank hypothesis with `r ≥ 2` lies below `1−√ρ`, hence outside the Johnson-to-capacity
prize window. -/
theorem okamoto_rank_condition_below_johnson {ρ δ : ℝ} {r : ℕ}
    (hρ0 : 0 < ρ) (hρ1 : ρ < 1) (hδ0 : 0 ≤ δ) (hr : 2 ≤ r)
    (hcond : ((r + 1 : ℕ) : ℝ) * δ < 1 - ρ) :
    δ < 1 - Real.sqrt ρ :=
  lt_trans (okamoto_rank_condition_radius_lt_third hδ0 hr hcond)
    (okamoto_unconditional_cutoff_below_johnson hρ0 hρ1)

end ArkLib.ProximityGap.CapacityVacuity

#print axioms ArkLib.ProximityGap.CapacityVacuity.exists_codeword_hammingDist_le_redundancy
#print axioms ArkLib.ProximityGap.CapacityVacuity.forall_exists_codeword_hammingDist_le_of_capacity
#print axioms ArkLib.ProximityGap.CapacityVacuity.okamoto_unconditional_cutoff_below_johnson
#print axioms ArkLib.ProximityGap.CapacityVacuity.okamoto_rank_condition_radius_lt_third
#print axioms ArkLib.ProximityGap.CapacityVacuity.okamoto_rank_condition_below_johnson

/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import Mathlib.InformationTheory.Hamming
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.Chebyshev

/-!
# The Johnson per-word list bound (second-moment form) — the object #232 reduces to

`CollisionLemma.lean` reduces the proximity-gap prize to a **single per-word list bound** for the code.
This file proves that bound's classical second-moment core, self-contained and `sorry`-free.

Let `L` be a set of codewords each within Hamming distance `e` of a received word `f`, pairwise at
distance `≥ d`, over `ι` with `|ι| = n`. Writing `A = Σ_{c∈L}(n - d(c,f))` for the total agreement and
`a_i = #{c∈L : c i = f i}` for the per-coordinate agreement count:

* `johnson_second_moment` — `A² ≤ n·(A + |L|·(|L|-1)·(n-d))`, via Cauchy–Schwarz `(Σa_i)² ≤ n·Σa_i²`
  and the pairwise overlap bound `|agree(c,f) ∩ agree(c',f)| ≤ n-d` for `c ≠ d` apart.

Since `A ≥ |L|·(n-e)`, this yields the Johnson list bound: when the Johnson condition `(n-e)² > n(n-d)`
holds (radius below the Johnson radius), `|L|` is bounded by a polynomial in `n,d`. This is the proven
below-Johnson half of the per-word object; the past-Johnson case is the open core.
-/

namespace ArkLib.CodingTheory.JohnsonPerWord

open Finset

variable {ι : Type*} [Fintype ι] [DecidableEq ι]
variable {F : Type*} [DecidableEq F]

/-- Agreement count of `c` with `f` equals `n - d(c,f)`. -/
theorem agree_card (c f : ι → F) :
    (Finset.univ.filter (fun i => c i = f i)).card = Fintype.card ι - hammingDist c f := by
  have hcompl : (Finset.univ.filter (fun i => c i = f i)).card
      + (Finset.univ.filter (fun i => c i ≠ f i)).card = Fintype.card ι := by
    rw [Finset.filter_card_add_filter_neg_card_eq_card (p := fun i => c i = f i), Finset.card_univ]
  have : hammingDist c f = (Finset.univ.filter (fun i => c i ≠ f i)).card := rfl
  omega

/-- **Pairwise overlap bound.** Two codewords at distance `≥ d` agree with `f` simultaneously on at
most `n - d` coordinates (their mutual-agreement set is contained in `{i : c i = c' i}`). -/
theorem overlap_le (c c' f : ι → F) (d : ℕ) (hd : d ≤ hammingDist c c') :
    (Finset.univ.filter (fun i => c i = f i ∧ c' i = f i)).card ≤ Fintype.card ι - d := by
  have hsub : (Finset.univ.filter (fun i => c i = f i ∧ c' i = f i))
      ⊆ Finset.univ.filter (fun i => c i = c' i) := by
    intro i hi
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi ⊢
    rw [hi.1, hi.2]
  have hcard : (Finset.univ.filter (fun i => c i = c' i)).card = Fintype.card ι - hammingDist c c' :=
    agree_card c c'
  calc (Finset.univ.filter (fun i => c i = f i ∧ c' i = f i)).card
      ≤ (Finset.univ.filter (fun i => c i = c' i)).card := Finset.card_le_card hsub
    _ = Fintype.card ι - hammingDist c c' := hcard
    _ ≤ Fintype.card ι - d := by omega

/-- The per-coordinate agreement count `a_i = #{c∈L : c i = f i}`. -/
def aCount (L : Finset (ι → F)) (f : ι → F) (i : ι) : ℕ :=
  (L.filter (fun c => c i = f i)).card

/-- `Σ_i a_i = Σ_{c∈L} (n - d(c,f))` (total agreement, summed two ways). -/
theorem sum_aCount (L : Finset (ι → F)) (f : ι → F) :
    (∑ i, aCount L f i) = ∑ c ∈ L, (Fintype.card ι - hammingDist c f) := by
  simp only [aCount, Finset.card_filter]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl (fun c _ => ?_)
  rw [← Finset.card_filter, agree_card]

/-- `Σ_i a_i² = Σ_{c,c'∈L} |agree(c,f) ∩ agree(c',f)|` (expand the square, swap sums). -/
theorem sum_aCount_sq (L : Finset (ι → F)) (f : ι → F) :
    (∑ i, aCount L f i ^ 2)
      = ∑ c ∈ L, ∑ c' ∈ L,
          (Finset.univ.filter (fun i => c i = f i ∧ c' i = f i)).card := by
  have hsq : ∀ i, aCount L f i ^ 2
      = ∑ c ∈ L, ∑ c' ∈ L, (if c i = f i ∧ c' i = f i then (1 : ℕ) else 0) := by
    intro i
    rw [aCount, Finset.card_filter, pow_two, Finset.sum_mul_sum]
    refine Finset.sum_congr rfl (fun c _ => Finset.sum_congr rfl (fun c' _ => ?_))
    by_cases h1 : c i = f i <;> by_cases h2 : c' i = f i <;> simp [h1, h2]
  simp only [hsq]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl (fun c _ => ?_)
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl (fun c' _ => ?_)
  rw [← Finset.card_filter]

/-- **Johnson second-moment inequality.** For a list `L` of codewords each within `e` of `f`, pairwise
at distance `≥ d`, with `A = Σ_{c∈L}(n - d(c,f))`:
`A² ≤ n·(A + |L|·(|L|-1)·(n-d))`. Combined with `A ≥ |L|·(n-e)` and the Johnson condition
`(n-e)² > n(n-d)`, this bounds `|L|` polynomially. -/
theorem johnson_second_moment (L : Finset (ι → F)) (f : ι → F) (d : ℕ)
    (hpair : ∀ c ∈ L, ∀ c' ∈ L, c ≠ c' → d ≤ hammingDist c c') :
    (∑ c ∈ L, (Fintype.card ι - hammingDist c f)) ^ 2
      ≤ Fintype.card ι * ((∑ c ∈ L, (Fintype.card ι - hammingDist c f))
          + L.card * (L.card - 1) * (Fintype.card ι - d)) := by
  classical
  set n := Fintype.card ι with hn
  -- Cauchy–Schwarz over coordinates
  have hcs : (∑ i, aCount L f i) ^ 2 ≤ n * ∑ i, aCount L f i ^ 2 := by
    have := sq_sum_le_card_mul_sum_sq (s := (Finset.univ : Finset ι)) (f := aCount L f)
    rwa [Finset.card_univ] at this
  -- bound Σ a_i² by diagonal + off-diagonal
  have hdiag : (∑ c ∈ L, ∑ c' ∈ L,
      (Finset.univ.filter (fun i => c i = f i ∧ c' i = f i)).card)
      ≤ (∑ c ∈ L, (n - hammingDist c f)) + L.card * (L.card - 1) * (n - d) := by
    -- split each inner sum into c'=c (diagonal) and c'≠c (off-diagonal)
    have hbound : ∀ c ∈ L,
        (∑ c' ∈ L, (Finset.univ.filter (fun i => c i = f i ∧ c' i = f i)).card)
          ≤ (n - hammingDist c f) + (L.card - 1) * (n - d) := by
      intro c hc
      have hsplit : (∑ c' ∈ L, (Finset.univ.filter (fun i => c i = f i ∧ c' i = f i)).card)
          = (Finset.univ.filter (fun i => c i = f i ∧ c i = f i)).card
            + ∑ c' ∈ L.erase c, (Finset.univ.filter (fun i => c i = f i ∧ c' i = f i)).card := by
        rw [← Finset.sum_erase_add L _ hc, add_comm]
      rw [hsplit]
      have hdiagc : (Finset.univ.filter (fun i => c i = f i ∧ c i = f i)).card
          = n - hammingDist c f := by
        simp only [and_self]; rw [agree_card]
      have hoff : (∑ c' ∈ L.erase c, (Finset.univ.filter (fun i => c i = f i ∧ c' i = f i)).card)
          ≤ (L.card - 1) * (n - d) := by
        calc (∑ c' ∈ L.erase c, (Finset.univ.filter (fun i => c i = f i ∧ c' i = f i)).card)
            ≤ ∑ _c' ∈ L.erase c, (n - d) := by
              refine Finset.sum_le_sum (fun c' hc' => ?_)
              rw [Finset.mem_erase] at hc'
              exact overlap_le c c' f d (hpair c hc c' hc'.2 (Ne.symm hc'.1))
          _ = (L.erase c).card * (n - d) := by rw [Finset.sum_const, smul_eq_mul]
          _ ≤ (L.card - 1) * (n - d) := by
              rw [Finset.card_erase_of_mem hc]
      rw [hdiagc]
      exact Nat.add_le_add_left hoff _
    calc (∑ c ∈ L, ∑ c' ∈ L,
          (Finset.univ.filter (fun i => c i = f i ∧ c' i = f i)).card)
        ≤ ∑ c ∈ L, ((n - hammingDist c f) + (L.card - 1) * (n - d)) :=
          Finset.sum_le_sum hbound
      _ = (∑ c ∈ L, (n - hammingDist c f)) + L.card * ((L.card - 1) * (n - d)) := by
          rw [Finset.sum_add_distrib, Finset.sum_const, smul_eq_mul]
      _ = (∑ c ∈ L, (n - hammingDist c f)) + L.card * (L.card - 1) * (n - d) := by ring
  -- assemble
  rw [sum_aCount L f] at hcs
  rw [sum_aCount_sq L f] at hcs
  calc (∑ c ∈ L, (n - hammingDist c f)) ^ 2
      ≤ n * ∑ c ∈ L, ∑ c' ∈ L, (Finset.univ.filter (fun i => c i = f i ∧ c' i = f i)).card := hcs
    _ ≤ n * ((∑ c ∈ L, (n - hammingDist c f)) + L.card * (L.card - 1) * (n - d)) := by
        exact Nat.mul_le_mul_left _ hdiag

#print axioms johnson_second_moment

end ArkLib.CodingTheory.JohnsonPerWord

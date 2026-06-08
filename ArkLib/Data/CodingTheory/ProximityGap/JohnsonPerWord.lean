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

`CollisionLemma.lean` reduces the proximity-gap prize to a **single per-word list bound**
for the code. This file proves that bound's classical second-moment core, self-contained
and `sorry`-free.

Let `L` be a set of codewords each within Hamming distance `e` of a received word `f`,
pairwise at distance `≥ d`, over `ι` with `|ι| = n`. Writing
`A = Σ_{c∈L}(n - d(c,f))` for the total agreement and `a_i = #{c∈L : c i = f i}`
for the per-coordinate agreement count:

* `johnson_second_moment` — `A² ≤ n·(A + |L|·(|L|-1)·(n-d))`, via
  Cauchy–Schwarz `(Σa_i)² ≤ n·Σa_i²` and the pairwise overlap bound
  `|agree(c,f) ∩ agree(c',f)| ≤ n-d` for `c ≠ d` apart.

Since `A ≥ |L|·(n-e)`, this yields the Johnson list bound: when the Johnson condition
`(n-e)² > n(n-d)` holds (radius below the Johnson radius), `|L|` is bounded by a
polynomial in `n,d`. This is the proven below-Johnson half of the per-word object;
the past-Johnson case is the open core.
-/

namespace ArkLib.CodingTheory.JohnsonPerWord

open Finset

variable {ι : Type*} [Fintype ι]
variable {F : Type*} [DecidableEq F]

open Classical in
/-- Agreement count of `c` with `f` equals `n - d(c,f)`. -/
theorem agree_card (c f : ι → F) :
    (Finset.univ.filter (fun i => c i = f i)).card = Fintype.card ι - hammingDist c f := by
  have hcompl : (Finset.univ.filter (fun i => c i = f i)).card
      + (Finset.univ.filter (fun i => c i ≠ f i)).card = Fintype.card ι := by
    rw [Finset.card_filter_add_card_filter_not, Finset.card_univ]
  have : hammingDist c f = (Finset.univ.filter (fun i => c i ≠ f i)).card := rfl
  omega

open Classical in
/-- **Pairwise overlap bound.** Two codewords at distance `≥ d` agree with `f`
simultaneously on at most `n - d` coordinates (their mutual-agreement set is contained
in `{i : c i = c' i}`). -/
theorem overlap_le (c c' f : ι → F) (d : ℕ) (hd : d ≤ hammingDist c c') :
    (Finset.univ.filter (fun i => c i = f i ∧ c' i = f i)).card ≤ Fintype.card ι - d := by
  have hsub : (Finset.univ.filter (fun i => c i = f i ∧ c' i = f i))
      ⊆ Finset.univ.filter (fun i => c i = c' i) := by
    intro i hi
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi ⊢
    rw [hi.1, hi.2]
  have hcard : (Finset.univ.filter (fun i => c i = c' i)).card =
      Fintype.card ι - hammingDist c c' :=
    agree_card c c'
  calc (Finset.univ.filter (fun i => c i = f i ∧ c' i = f i)).card
      ≤ (Finset.univ.filter (fun i => c i = c' i)).card := Finset.card_le_card hsub
    _ = Fintype.card ι - hammingDist c c' := hcard
    _ ≤ Fintype.card ι - d := by omega

/-- The per-coordinate agreement count `a_i = #{c∈L : c i = f i}`. -/
def aCount (L : Finset (ι → F)) (f : ι → F) (i : ι) : ℕ :=
  (L.filter (fun c => c i = f i)).card

open Classical in
/-- `Σ_i a_i = Σ_{c∈L} (n - d(c,f))` (total agreement, summed two ways). -/
theorem sum_aCount (L : Finset (ι → F)) (f : ι → F) :
    (∑ i, aCount L f i) = ∑ c ∈ L, (Fintype.card ι - hammingDist c f) := by
  simp only [aCount, Finset.card_filter]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl (fun c _ => ?_)
  rw [← Finset.card_filter, agree_card]

open Classical in
/-- `Σ_i a_i² = Σ_{c,c'∈L} |agree(c,f) ∩ agree(c',f)|` (expand the square,
swap sums). -/
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

open Classical in
/-- **Johnson second-moment inequality.** For a list `L` of codewords each within `e` of
`f`, pairwise at distance `≥ d`, with `A = Σ_{c∈L}(n - d(c,f))`:
`A² ≤ n·(A + |L|·(|L|-1)·(n-d))`. Combined with `A ≥ |L|·(n-e)` and the Johnson condition
`(n-e)² > n(n-d)`, this bounds `|L|` polynomially. -/
theorem johnson_second_moment (L : Finset (ι → F)) (f : ι → F) (d : ℕ)
    (hpair : ∀ c ∈ L, ∀ c' ∈ L, c ≠ c' → d ≤ hammingDist c c') :
    (∑ c ∈ L, (Fintype.card ι - hammingDist c f)) ^ 2
      ≤ Fintype.card ι * ((∑ c ∈ L, (Fintype.card ι - hammingDist c f))
          + L.card * (L.card - 1) * (Fintype.card ι - d)) := by
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
      have hsplit :
          (∑ c' ∈ L, (Finset.univ.filter (fun i => c i = f i ∧ c' i = f i)).card)
            = (Finset.univ.filter (fun i => c i = f i ∧ c i = f i)).card
              + ∑ c' ∈ L.erase c,
                (Finset.univ.filter (fun i => c i = f i ∧ c' i = f i)).card := by
        rw [← Finset.sum_erase_add L _ hc, add_comm]
      rw [hsplit]
      have hdiagc : (Finset.univ.filter (fun i => c i = f i ∧ c i = f i)).card
          = n - hammingDist c f := by
        simp only [and_self]; rw [agree_card]
      have hoff :
          (∑ c' ∈ L.erase c,
              (Finset.univ.filter (fun i => c i = f i ∧ c' i = f i)).card)
            ≤ (L.card - 1) * (n - d) := by
        calc (∑ c' ∈ L.erase c,
              (Finset.univ.filter (fun i => c i = f i ∧ c' i = f i)).card)
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
      ≤ n * ∑ c ∈ L, ∑ c' ∈ L,
          (Finset.univ.filter (fun i => c i = f i ∧ c' i = f i)).card := hcs
    _ ≤ n * ((∑ c ∈ L, (n - hammingDist c f)) + L.card * (L.card - 1) * (n - d)) := by
        exact Nat.mul_le_mul_left _ hdiag


/-- **Explicit Johnson list bound.** For a list `L` of codewords each within `e` of `f`, pairwise at
distance `≥ d` (with `d, e ≤ n`):  `|L|·((n-e)² - n·(n-d)) ≤ n·d`.  When the Johnson condition
`(n-e)² > n(n-d)` holds, this bounds `|L| ≤ n·d / ((n-e)² - n(n-d))` — polynomial. This is the closed
form of the per-word object that `CollisionLemma` reduces #232 to; it is the proven below-Johnson
half. -/
theorem johnson_list_bound (L : Finset (ι → F)) (f : ι → F) (e d : ℕ)
    (hd : d ≤ Fintype.card ι) (he : e ≤ Fintype.card ι)
    (hclose : ∀ c ∈ L, hammingDist c f ≤ e)
    (hpair : ∀ c ∈ L, ∀ c' ∈ L, c ≠ c' → d ≤ hammingDist c c') :
    (L.card : ℤ) * (((Fintype.card ι : ℤ) - e) ^ 2
        - (Fintype.card ι : ℤ) * ((Fintype.card ι : ℤ) - d))
      ≤ (Fintype.card ι : ℤ) * d := by
  classical
  rcases Nat.eq_zero_or_pos L.card with hL0 | hLpos
  · rw [hL0]; simp only [Nat.cast_zero, zero_mul]; positivity
  · have hsm := johnson_second_moment L f d hpair
    set n := Fintype.card ι with hn
    set A := ∑ c ∈ L, (n - hammingDist c f) with hA
    have hc1 : (1 : ℕ) ≤ L.card := hLpos
    have hlo : L.card * (n - e) ≤ A := by
      rw [hA]
      have h : ∑ _c ∈ L, (n - e) ≤ ∑ c ∈ L, (n - hammingDist c f) :=
        Finset.sum_le_sum (fun c hc => by have := hclose c hc; omega)
      rwa [Finset.sum_const, smul_eq_mul] at h
    have hhi : A ≤ L.card * n := by
      rw [hA]
      have h : ∑ c ∈ L, (n - hammingDist c f) ≤ ∑ _c ∈ L, n :=
        Finset.sum_le_sum (fun c _ => by omega)
      rwa [Finset.sum_const, smul_eq_mul] at h
    have hsmZ : (A : ℤ) ^ 2
        ≤ (n : ℤ) * ((A : ℤ) + (L.card : ℤ) * ((L.card : ℤ) - 1) * ((n : ℤ) - (d : ℤ))) := by
      calc (A : ℤ) ^ 2 = ((A ^ 2 : ℕ) : ℤ) := by push_cast; ring
        _ ≤ ((n * (A + L.card * (L.card - 1) * (n - d)) : ℕ) : ℤ) := by exact_mod_cast hsm
        _ = (n : ℤ) * ((A : ℤ) + (L.card : ℤ) * ((L.card : ℤ) - 1) * ((n : ℤ) - (d : ℤ))) := by
            push_cast [Nat.cast_sub hd, Nat.cast_sub hc1]; ring
    have hloZ : (L.card : ℤ) * ((n : ℤ) - (e : ℤ)) ≤ (A : ℤ) := by
      calc (L.card : ℤ) * ((n : ℤ) - (e : ℤ)) = ((L.card * (n - e) : ℕ) : ℤ) := by
            push_cast [Nat.cast_sub he]; ring
        _ ≤ (A : ℤ) := by exact_mod_cast hlo
    have hhiZ : (A : ℤ) ≤ (L.card : ℤ) * (n : ℤ) := by exact_mod_cast hhi
    have hLnn : (0 : ℤ) ≤ (L.card : ℤ) := Int.natCast_nonneg _
    have hnenn : (0 : ℤ) ≤ (n : ℤ) - (e : ℤ) := by simp only [sub_nonneg]; exact_mod_cast he
    nlinarith [hsmZ, hloZ, hhiZ, hLnn, hnenn,
      mul_nonneg hLnn hnenn, sq_nonneg ((A : ℤ) - (L.card : ℤ) * ((n : ℤ) - (e : ℤ)))]

#print axioms johnson_second_moment

end ArkLib.CodingTheory.JohnsonPerWord
#print axioms ArkLib.CodingTheory.JohnsonPerWord.johnson_list_bound

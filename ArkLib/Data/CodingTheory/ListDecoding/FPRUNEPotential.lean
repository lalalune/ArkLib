/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# The FPRUNE potential induction (Chen–Zhang 2025 / arXiv 2512.08017, Lemma 3.5 from 3.4)

The polynomial list-decoding bound for subspace-design codes is proven via the `FPRUNE`
algorithm, which recursively samples a coordinate set `T` while strictly reducing the dimension
`r := dim ℋ` of an ambient linear space. Each candidate codeword `c` is scored by the weighted
agreement indicator with expectation `E r := E_T[X_{c,T}·(1-η')^{|T|}]` for a dimension-`r`
space.

**Lemma 3.5** lower-bounds this expectation by a potential `pot r := η/(r+η)`. Its proof is a
strong induction on the dimension `r`:

* **base** (`r = 0`, `ℋ = {0}`): the recursion returns `T = ∅`, so `E 0 = pot 0`;
* **step** (`r > 0`, the content of **Lemma 3.4**): unfolding one FPRUNE recursion `T = {i} ∪ T'`,
  the expectation factors as a nonnegative combination `∑_i c_i · E(d_i)` of the sub-space
  expectations (`c_i = p_i·(1-η') ≥ 0`, `d_i = dim ℋ_i < r`), and the subspace-design budget
  (Definition 6) yields the matching potential inequality `pot r ≤ ∑_i c_i · pot(d_i)`.

This file formalizes that induction **abstractly**: given the base value and the one-step
potential/expectation recursion (Lemma 3.4) as hypotheses, the dimension-wise lower bound
`pot r ≤ E r` follows for all `r`. Composed with the in-tree subspace-design inequality
(`sum_card_vanishing_le_design`, the source of the one-step `pot`-inequality) and the
`FirstMomentListBound` union-bound shell (the outer `|L| ≤ M/β`), this assembles the full
list-decoding bound. The induction here is the genuine structural core of Lemma 3.5; the
remaining content is exactly the per-step Lemma 3.4 inequality supplied as `hpot`.

Pure `Finset`/order arithmetic, reusable for any recursively-defined potential lower bound on a
nonnegatively-branching, dimension-decreasing process.
-/

namespace CodingTheory.ListDecoding

open Finset

variable {ι : Type*}

/-- **FPRUNE potential lower bound (Lemma 3.5 from the one-step Lemma 3.4).** Let `E, pot : ℕ → ℝ`
with `pot 0 ≤ E 0` (base case). Suppose that for every `r > 0` there is a finite branching — a
`Finset J` of branches with nonnegative coefficients `c j ≥ 0` and strictly smaller dimensions
`d j < r` — such that

* `∑_{j∈J} c j · E (d j) ≤ E r`  (the expectation factors through one recursion step), and
* `pot r ≤ ∑_{j∈J} c j · pot (d j)`  (the one-step potential inequality, Lemma 3.4 / Def 6).

Then `pot r ≤ E r` for every dimension `r`. Proof: strong induction on `r`; the inductive
hypothesis `pot (d j) ≤ E (d j)` (valid since `d j < r`) transports through the nonnegative
combination. -/
theorem fprune_potential_bound
    (E pot : ℕ → ℝ) (base : pot 0 ≤ E 0)
    (step : ∀ r, 0 < r → ∃ (J : Finset ι) (c : ι → ℝ) (d : ι → ℕ),
        (∀ j ∈ J, 0 ≤ c j) ∧ (∀ j ∈ J, d j < r) ∧
        (∑ j ∈ J, c j * E (d j) ≤ E r) ∧
        (pot r ≤ ∑ j ∈ J, c j * pot (d j))) :
    ∀ r, pot r ≤ E r := by
  intro r
  induction r using Nat.strong_induction_on with
  | _ r ih =>
    rcases Nat.eq_zero_or_pos r with h0 | hpos
    · subst h0; exact base
    · obtain ⟨J, c, d, hc, hd, hE, hpot⟩ := step r hpos
      calc pot r
          ≤ ∑ j ∈ J, c j * pot (d j) := hpot
        _ ≤ ∑ j ∈ J, c j * E (d j) :=
            Finset.sum_le_sum fun j hj =>
              mul_le_mul_of_nonneg_left (ih (d j) (hd j hj)) (hc j hj)
        _ ≤ E r := hE

/-- **The Lemma-3.5 endpoint.** Specialising the potential to `pot r = η/(r+η)` (`η > 0`): the
expectation `E r` is at least `η/(r+η)`, the bound used by the first-moment list-size shell with
`β := η/(r+η)`. -/
theorem fprune_expectation_lower
    (E : ℕ → ℝ) (η : ℝ) (hη : 0 < η)
    (base : η / ((0 : ℕ) + η) ≤ E 0)
    (step : ∀ r, 0 < r → ∃ (J : Finset ι) (c : ι → ℝ) (d : ι → ℕ),
        (∀ j ∈ J, 0 ≤ c j) ∧ (∀ j ∈ J, d j < r) ∧
        (∑ j ∈ J, c j * E (d j) ≤ E r) ∧
        (η / ((r : ℕ) + η) ≤ ∑ j ∈ J, c j * (η / ((d j : ℕ) + η)))) :
    ∀ r, η / ((r : ℕ) + η) ≤ E r :=
  fprune_potential_bound E (fun r => η / ((r : ℕ) + η)) base step

/-! ## Lemma 3.4 — the one-step potential inequality (design-weighted FPRUNE sampling) -/

variable [DecidableEq ι]

/-- **Lemma 3.4 (one-step potential inequality), the design-weighted FPRUNE sampling.** With
`pot x = η/(x+η)`, sampling each good coordinate `j ∈ J` with probability proportional to
`wt_η(ℋ_j) = d_j + η` and crediting one recursion step the factor `(1-η')`, the resulting
nonnegative combination `c_j := (d_j+η)·(1-η') / W` (where `W := ∑_{k∈J}(d_k+η)`) satisfies the
potential step `pot r ≤ ∑_{j∈J} c_j · pot(d_j)`.

The proof is the exact arithmetic: each summand `[(d_j+η)(1-η')/W]·[η/(d_j+η)]` cancels to
`(1-η')η/W`, so the sum is `|J|·(1-η')·η/W`, and `η/(r+η) ≤ |J|(1-η')η/W` reduces to
`W ≤ |J|·(1-η')(r+η)`, which holds termwise because every good coordinate has
`d_j + η ≤ (1-η')(r+η)` (the FPRUNE "good" predicate). -/
theorem fprune_one_step
    (η η' : ℝ) (hη : 0 < η) (hη' : 0 ≤ 1 - η')
    (r : ℕ) (J : Finset ι) (d : ι → ℕ) (hJ : J.Nonempty)
    (hgood : ∀ j ∈ J, (d j : ℝ) + η ≤ (1 - η') * ((r : ℝ) + η)) :
    η / ((r : ℕ) + η) ≤
      ∑ j ∈ J, ((((d j : ℝ) + η) * (1 - η')) / (∑ k ∈ J, ((d k : ℝ) + η)))
                  * (η / ((d j : ℕ) + η)) := by
  have hposTerm : ∀ j, (0 : ℝ) < (d j : ℝ) + η := fun j =>
    add_pos_of_nonneg_of_pos (Nat.cast_nonneg _) hη
  set W : ℝ := ∑ k ∈ J, ((d k : ℝ) + η) with hW
  have hWpos : 0 < W := by
    rw [hW]; exact Finset.sum_pos (fun j _ => hposTerm j) hJ
  have hWne : W ≠ 0 := ne_of_gt hWpos
  have hrη : (0 : ℝ) < (r : ℝ) + η := add_pos_of_nonneg_of_pos (Nat.cast_nonneg _) hη
  -- Each summand collapses to `(1-η')·η / W`.
  have hterm : ∀ j ∈ J,
      ((((d j : ℝ) + η) * (1 - η')) / W) * (η / ((d j : ℕ) + η))
        = (1 - η') * η / W := by
    intro j _
    have hdj : (d j : ℝ) + η ≠ 0 := ne_of_gt (hposTerm j)
    field_simp
  rw [Finset.sum_congr rfl hterm, Finset.sum_const, nsmul_eq_mul]
  -- `W ≤ |J|·(1-η')(r+η)` termwise from the good predicate.
  have hWle : W ≤ (J.card : ℝ) * ((1 - η') * ((r : ℝ) + η)) := by
    rw [hW]
    calc ∑ k ∈ J, ((d k : ℝ) + η)
        ≤ ∑ _k ∈ J, ((1 - η') * ((r : ℝ) + η)) := Finset.sum_le_sum hgood
      _ = (J.card : ℝ) * ((1 - η') * ((r : ℝ) + η)) := by
          rw [Finset.sum_const, nsmul_eq_mul]
  -- Conclude `η/(r+η) ≤ |J|·(1-η')η / W`.
  have key : η / ((r : ℝ) + η) ≤ ((J.card : ℝ) * (1 - η') * η) / W := by
    rw [le_div_iff₀ hWpos, div_mul_eq_mul_div, div_le_iff₀ hrη]
    -- `η · W ≤ (|J|·(1-η')·η) · (r+η)`, i.e. `η · hWle`.
    nlinarith [mul_le_mul_of_nonneg_left hWle (le_of_lt hη), hη, hWpos, hrη]
  calc η / ((r : ℕ) + η)
      = η / ((r : ℝ) + η) := by push_cast; ring_nf
    _ ≤ ((J.card : ℝ) * (1 - η') * η) / W := key
    _ = (J.card : ℝ) * ((1 - η') * η / W) := by ring

end CodingTheory.ListDecoding

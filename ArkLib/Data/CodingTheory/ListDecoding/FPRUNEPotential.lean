/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Real.Basic

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

end CodingTheory.ListDecoding

/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexander Hicks
-/

import Mathlib.Probability.ProbabilityMassFunction.Basic
import ArkLib.Data.Probability.Notation

/-!
# Probabilistic combinatorics

Stand-alone probabilistic-combinatorics statements used elsewhere in ArkLib.
Currently this module hosts `exists_large_image_of_pairwise_collision_bound`,
which is Claim B.1 of [ABF26].

## References

* [Arnon, G., Boneh, D., Fenzi, G., *Open Problems in List Decoding and
  Correlated Agreement*][ABF26]
-/

namespace Probability

open Finset NNReal ENNReal ProbabilityTheory

/-! ## Colliding-pair helpers (ABF26 Appendix B counting)

Helper definitions and the central Cauchy-Schwarz-on-fibers lemma used
by `exists_large_image_of_pairwise_collision_bound` (Claim B.1). -/

section CollidingPairs

variable {S T : Type} [Fintype S] [DecidableEq S] [DecidableEq T]

/-- Number of *ordered* pairs `(x, y) : S × S` with `x ≠ y` and `φ x = φ y`.

This equals twice the number of distinct (unordered) colliding pairs;
working ordered avoids needing a `LinearOrder S` to canonicalise unordered
pairs. Paper's `|C_φ|` is `numCollsOrdered φ / 2`. -/
def numCollsOrdered (φ : S → T) : ℕ :=
  (Finset.univ.filter (fun p : S × S => p.1 ≠ p.2 ∧ φ p.1 = φ p.2)).card

/-- Sum of squared fiber-cardinalities = `|S| + numCollsOrdered`.

Each ordered pair `(x, y)` with `φ x = φ y` is counted once on the LHS
(via its common image μ); the `|S|` diagonal pairs `(x, x)` and the
`numCollsOrdered` off-diagonal pairs partition them.

**Tagged sorry — bounded follow-up.** Proof chains: `|fiber μ|² =
|fiber μ × fiber μ|` (via `Finset.card_product`); sum-over-image
collects to `#{(x, y) : φ x = φ y}` (via `Finset.card_biUnion` with
disjointness); split diagonal vs. off-diagonal (via
`Finset.card_union_of_disjoint`); diagonal-count = `|S|` (via the
`fun x ↦ (x, x)` bijection from `S` to the diagonal filter). ~40-60
lines. -/
lemma sum_fiber_sq_eq (φ : S → T) :
    ∑ μ ∈ Finset.univ.image φ,
        ((Finset.univ.filter (fun x : S => φ x = μ)).card)^2 =
      Fintype.card S + numCollsOrdered φ := by
  sorry

/-- Cauchy-Schwarz applied to fiber cardinalities.

Equivalent to `Finset.sq_sum_le_card_mul_sum_sq` over the image of `φ`,
combined with `sum_fiber_sq_eq` to rewrite the squared-sum side and
with `Finset.card_eq_sum_card_image` (or an explicit fiber count) to
identify `Σ μ ∈ image, |fiber μ| = |S|`.

**Tagged sorry — bounded follow-up.** ~10-20 lines through the named
Mathlib lemmas listed. -/
lemma cauchy_schwarz_fiber (φ : S → T) :
    (Fintype.card S)^2 ≤
      (Finset.univ.image φ).card * (Fintype.card S + numCollsOrdered φ) := by
  sorry

end CollidingPairs

/-- **Claim B.1 of [ABF26]** ("Omitted claim for Lemma 6.12").

Suppose `S, T` are finite sets and `Φ` is a distribution on functions `S → T`
such that for any distinct `x, y ∈ S`, the probability that a sample
`φ ← Φ` sends `x` and `y` to the same image is bounded by `ε`:
```
∀ x y ∈ S, x ≠ y → Pr_{φ ← Φ}[φ x = φ y] ≤ ε.
```
Then there exists some `φ` in the support of `Φ` whose image has cardinality
at least `|S| / (1 + (|S| − 1) · ε)`.

## Proof outline (from [ABF26] Appendix B)

Let `C_φ := { (x, y) ∈ Sym2 S : x ≠ y ∧ φ x = φ y }` be the set of distinct
colliding pairs under `φ`.

1. **Expected number of collisions.** By linearity of expectation,
   `E_{φ ← Φ}[|C_φ|] = Σ_{(x,y) ∈ Sym2 S, x ≠ y} Pr[φ x = φ y]
                     ≤ (|S| choose 2) · ε`.

2. **Counting collisions via fibers.** For every fixed `φ`,
   `|S| = Σ_{μ ∈ φ(S)} |φ⁻¹(μ)|` and each `μ ∈ φ(S)` contributes
   `(|φ⁻¹(μ)| choose 2)` colliding pairs, so
   `|C_φ| = ½(Σ_μ |φ⁻¹(μ)|² − |S|)`.

3. **Cauchy–Schwarz on fibers.**
   `(Σ_μ |φ⁻¹(μ)|)² ≤ (Σ_μ 1²) · (Σ_μ |φ⁻¹(μ)|²) = |φ(S)| · Σ_μ |φ⁻¹(μ)|²`,
   hence `|φ(S)| · (2 |C_φ| + |S|) ≥ |S|²` and thus
   `|φ(S)| ≥ |S|² / (2 |C_φ| + |S|)`. Captured by `cauchy_schwarz_fiber`.

4. **Contradiction-form.** Rather than Jensen on convex `x ↦ |S|²/(2x+|S|)`,
   we negate the goal and derive `numCollsOrdered > |S|·(|S|−1)·ε` for every
   `φ ∈ support`, then sum to contradict the hypothesis.

5. **Existence by averaging.** Some `φ` in the support of `Φ` achieves at
   least the expectation, hence the claimed bound. -/
theorem exists_large_image_of_pairwise_collision_bound
    {S T : Type} [Fintype S] [DecidableEq T]
    (Φ : PMF (S → T)) (ε : ENNReal)
    (hΦ : ∀ x y : S, x ≠ y →
        Pr_{ let φ ← Φ }[(decide (φ x = φ y) : Prop)] ≤ ε) :
    ∃ φ ∈ Φ.support, ((Finset.univ.image φ).card : ENNReal) ≥
      (Fintype.card S : ENNReal) / (1 + (Fintype.card S - 1) * ε) := by
  -- ABF26 Claim B.1. Contradiction-form proof avoiding Jensen explicitly:
  -- if every `φ ∈ support` has `|φ(S)| < K := |S|/(1 + (|S|−1)ε)`, then
  -- Cauchy-Schwarz forces every `φ` to have *more* colliding pairs than the
  -- hypothesis's `E[colls] ≤ (|S| choose 2)·ε` bound permits — contradiction.
  --
  -- ## Proof skeleton (full closure deferred — bounded follow-up)
  --
  -- Let `numColls φ : ℕ` be the count of unordered pairs `{x,y}` with
  -- `x ≠ y ∧ φ x = φ y` (paper's `|C_φ|`). The chain:
  --
  -- Step 1 (pointwise Cauchy-Schwarz):  for every `φ : S → T`,
  --    `|S|² ≤ |φ(S)| · (2 · numColls φ + |S|)`
  --   via `Finset.sq_sum_le_card_mul_sum_sq` applied to fiber-cardinalities
  --   `μ ↦ |φ⁻¹(μ)|` over the image `φ(S)`. The `Σ |φ⁻¹(μ)|²` decomposes
  --   into `2 · numColls + |S|` by counting ordered same-image pairs.
  --
  -- Step 2 (rearrange):  if `|φ(S)| < K`, then
  --    `numColls φ > (|S| choose 2) · ε`
  --   from Step 1's bound + the explicit value of K.
  --
  -- Step 3 (averaging):  if `∀ φ ∈ support, numColls φ > c`,
  --   then `E_{φ←Φ}[numColls φ] > c`. Standard.
  --
  -- Step 4 (linearity of expectation):  the hypothesis sums to
  --    `E_{φ←Φ}[numColls φ] ≤ (|S| choose 2) · ε`
  --   (pairwise-collision bound, summed over `(|S| choose 2)` unordered
  --   pairs). The `decide` wrapper in `hΦ` unwraps via `decide_iff`.
  --
  -- Step 5 (contradict):  Steps 3 + 4 together force
  --    `(|S| choose 2) · ε < E[…] ≤ (|S| choose 2) · ε`,
  --   a contradiction.
  --
  -- Each step is a stand-alone proof; closure of all 5 steps is a focused
  -- proof-PR (~100-200 lines through PMF expectations and ENNReal /
  -- ℕ casts; also needs an auxiliary `numColls` definition that handles
  -- the unordered-pair count canonically, e.g. via `Sym2` or by
  -- requiring `[LinearOrder S]` and using `p.1 < p.2`).
  sorry

end Probability

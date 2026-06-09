/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Finset.Powerset
import Mathlib.Algebra.Field.ZMod
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.LinearCombination

/-!
# Round 8 (Issue #232, ABF26) — `⟨ω⟩`-symmetric subsets concentrate BOTH `∑x` and `∑x²` at `0`:
# the order-4 root-of-unity construction that resolves Round 7's open `p₂`-spread residual.

Round 7 (`SubsetSumNegSymmConcentration.lean`, `negSymm_card_ge_choose`) cracked the concentration
"open door" on the **first** coordinate: a *negation*-symmetric subset `S = P ∪ (−P)` (closure under
the order-`2` element `−1`) forces `∑_{x∈S} x = 0` at a single target, `q`-independently, with a
super-polynomial count `C(n/2, t)`. Round 7's honest residual: the **second** coordinate
`∑_{x∈S} x² = 2∑_{g∈P} g²` *spreads* — "whether the pair-squares `{g²}` concentrate is open".

## What this round contributes — close the door on BOTH coordinates at once

The Round-7 residual dissolves at one level up the root-of-unity tower. The pair-squares `{g² : g∈G}`
are exactly the order-`n/2` subgroup `G²`, *also* negation-closed — so the *same* trick applies to the
squares. Packaged multiplicatively, this is just **closure under the order-4 element** `ω` (`ω² = −1`,
so `ω⁴ = 1`, `⟨ω⟩ = {1, ω, −1, −ω}`). The clean engine:

* `omega_closed_psum_eq_zero` — **the engine.** If `S` is closed under `x ↦ ω·x`
  (`S.image (ω·) = S`), `ω ≠ 0`, and `ω^j ≠ 1`, then `∑_{x∈S} x^j = 0`. Proof: reindex
  `∑_S x^j = ∑_S (ω x)^j = ω^j ∑_S x^j`, so `(1 − ω^j)∑ = 0`, and `ω^j ≠ 1` kills the sum. This is a
  *single* uniform statement that vanishes **every** power sum `p_j` with `ω^j ≠ 1`.

* For an order-4 `ω` (`ω² = −1`): `ω¹ = ω ≠ 1` and `ω² = −1 ≠ 1` (char `≠ 2`), so the engine gives
  `∑_{x∈S} x = 0` **and** `∑_{x∈S} x² = 0` for *every* `⟨ω⟩`-closed `S`
  (`omega4Closure_sum_eq_zero`, `omega4Closure_sumsq_eq_zero`). Hence `e₁(S) = 0` and
  `e₂(S) = (e₁² − p₂)/2 = 0`: **both** symmetric functions are pinned to the single target `(0,0)` —
  exactly the `N2(·; 0, 0)` fiber Round 7 could only pin on its first coordinate.

* `omega4Closure` (`P ∪ ωP ∪ ω²P ∪ ω³P`) is the `⟨ω⟩`-orbit closure of `P`; `omega4Closure_image_eq`
  proves it is `ω`-closed, feeding the engine.

* `omega4_card_eq` / `omega4Closure_injOn` / `card_ge_choose_two_zero` — under a **free-action**
  hypothesis on a transversal `T` of the `⟨ω⟩`-orbits (the four translates `ω^i·T` are independent),
  the `s`-subsets `U ⊆ T` inject (via `U ↦ omega4Closure ω U`) into the size-`4s` subsets with
  `∑x = ∑x² = 0`. Hence `C(|T|, s) ≤ #{ S : |S| = 4s, ∑x = 0 ∧ ∑x² = 0 }`. With `|T| = n/4` this is a
  **`q`-independent, super-polynomial** lower bound on the *single* `(0,0)` fiber of the
  `(sum, sum-of-squares)` count — Round 7's residual coordinate, now concentrated.

## Honest scope — what this does and does NOT do (the depth-collapse wall)

* It **IS** a `sorry`-free, axiom-clean, `q`-independent super-polynomial lower bound on the *single*
  `(∑x, ∑x²) = (0,0)` fiber — closing the Round-7 residual on BOTH coordinates simultaneously, for the
  `t = 2` joint count `N2`.
* It generalizes (the engine is stated for all `j`): closure under a primitive `2^r`-th root of unity
  `ω_r` vanishes every power sum `p_j` with `2^r ∤ j`, hence `p_1, …, p_{2^r−1} = 0`, hence
  `e_1, …, e_{2^r−1} = 0`. So killing the first `t` symmetric functions needs `r = ⌈log₂(t+1)⌉`.
* It is **NOT** a prize counterexample, and this file is honest about *why* (the genuine wall): the
  `⟨ω_r⟩`-orbits have size `2^r`, so a transversal has only `n/2^r` elements and the concentrated
  count is `C(n/2^r, s)`. Reaching the **deep interior** (agreement `≈ √(kn)`, near the Johnson radius)
  forces `2^r ≈ t ≈ √(kn) − k`, i.e. `r ≈ m`, which **collapses** the transversal to `n/2^r = O(1)`
  elements and the count to a *constant*. The root-of-unity depth needed to pin `t` symmetric
  functions eats the subgroup geometrically. This is the precise, structural reason the construction
  concentrates near *capacity* (constant `t`) but cannot pin `δ*` in the deep interior — and it
  matches ABF26's "no known technique past Johnson for explicit RS".

All headline results are `sorry`-free and axiom-clean (`[propext, Classical.choice, Quot.sound]`).

## References
- [ABF26] Arnon, Boneh, Fenzi. *Open Problems in List Decoding and Correlated Agreement*. 2026.
  Tracking issue #232. Builds on Round 7 `SubsetSumNegSymmConcentration.lean`.
-/

open Finset BigOperators

namespace ArkLib.CodingTheory.Round8OmegaConcentration

variable {F : Type*} [Field F] [DecidableEq F]

/-! ## 1. The engine: a `⟨ω⟩`-closed set vanishes every power sum `p_j` with `ω^j ≠ 1`. -/

/-- **The engine.** If `S` is closed under multiplication by `ω` (`S.image (ω·) = S`), `ω ≠ 0`, and
`ω^j ≠ 1`, then the `j`-th power sum vanishes: `∑_{x∈S} x^j = 0`.

Proof: multiplication by `ω` is a bijection of `S` (injective since `ω ≠ 0`, onto `S` by `hS`), so
reindexing the sum gives `∑_{x∈S} x^j = ∑_{x∈S} (ω x)^j = ω^j ∑_{x∈S} x^j`. Hence
`(1 − ω^j)·∑ = 0`, and `1 − ω^j ≠ 0` (as `ω^j ≠ 1`) forces `∑ = 0`.

This single statement kills **every** power sum whose exponent is not annihilated by `ω`. For `ω` a
primitive `N`-th root of unity it vanishes `p_j` for all `j` with `N ∤ j`. -/
theorem omega_closed_psum_eq_zero {ω : F} {S : Finset F} {j : ℕ}
    (hω0 : ω ≠ 0) (hωj : ω ^ j ≠ 1) (hS : S.image (fun x => ω * x) = S) :
    ∑ x ∈ S, x ^ j = 0 := by
  classical
  have key : ∑ x ∈ S, x ^ j = ω ^ j * ∑ x ∈ S, x ^ j := by
    conv_lhs => rw [← hS]
    rw [Finset.sum_image (fun a _ b _ h => mul_left_cancel₀ hω0 h), Finset.mul_sum]
    exact Finset.sum_congr rfl (fun x _ => by rw [mul_pow])
  have hz : (1 - ω ^ j) * (∑ x ∈ S, x ^ j) = 0 := by linear_combination key
  rcases mul_eq_zero.mp hz with h | h
  · exact absurd (sub_eq_zero.mp h).symm hωj
  · exact h

/-! ## 2. The order-4 root of unity and its basic arithmetic (`ω² = −1`). -/

variable {ω : F}

/-- From `ω² = −1` and char `≠ 2`: `ω ≠ 0`. -/
theorem omega_ne_zero (h2 : (2 : F) ≠ 0) (hω2 : ω ^ 2 = -1) : ω ≠ 0 := by
  rintro rfl
  apply h2
  rw [zero_pow (by norm_num : (2 : ℕ) ≠ 0)] at hω2
  linear_combination 2 * hω2

/-- From `ω² = −1` and char `≠ 2`: `ω⁴ = 1`. -/
theorem omega_pow_four (hω2 : ω ^ 2 = -1) : ω ^ 4 = 1 := by
  have : ω ^ 4 = (ω ^ 2) ^ 2 := by ring
  rw [this, hω2]; ring

/-- From `ω² = −1` and char `≠ 2`: `ω ≠ 1` (else `1 = ω² = −1`, so `2 = 0`). -/
theorem omega_ne_one (h2 : (2 : F) ≠ 0) (hω2 : ω ^ 2 = -1) : ω ≠ 1 := by
  rintro rfl
  apply h2
  rw [one_pow] at hω2
  linear_combination hω2

/-- From `ω² = −1` and char `≠ 2`: `ω² ≠ 1` (else `−1 = 1`, so `2 = 0`). -/
theorem omega_sq_ne_one (h2 : (2 : F) ≠ 0) (hω2 : ω ^ 2 = -1) : ω ^ 2 ≠ 1 := by
  rw [hω2]; intro h; apply h2; linear_combination -h

/-! ## 3. The `⟨ω⟩`-orbit closure and its `ω`-closedness. -/

/-- The **`⟨ω⟩`-orbit closure** of `P`: `P ∪ ωP ∪ ω²P ∪ ω³P`, the union of the four `⟨ω⟩`-translates.
For `P` inside a transversal `T` of the `⟨ω⟩`-orbits of a smooth subgroup `G`, this is the
`⟨ω⟩`-symmetric subset of `G` the construction uses. -/
noncomputable def omega4Closure (ω : F) (P : Finset F) : Finset F :=
  P ∪ P.image (fun x => ω * x) ∪ P.image (fun x => ω ^ 2 * x) ∪ P.image (fun x => ω ^ 3 * x)

/-- `omega4Closure ω P` is closed under multiplication by `ω` (using `ω⁴ = 1`): multiplying each
translate by `ω` cyclically permutes `{P, ωP, ω²P, ω³P}` (the `ω³P` translate wraps to `ω⁴P = P`). -/
theorem omega4Closure_image_eq (hω4 : ω ^ 4 = 1) (P : Finset F) :
    (omega4Closure ω P).image (fun x => ω * x) = omega4Closure ω P := by
  classical
  unfold omega4Closure
  simp only [Finset.image_union, Finset.image_image, Function.comp_def]
  have c1 : (fun x : F => ω * (ω * x)) = fun x => ω ^ 2 * x := by funext x; ring
  have c2 : (fun x : F => ω * (ω ^ 2 * x)) = fun x => ω ^ 3 * x := by funext x; ring
  have c3 : (fun x : F => ω * (ω ^ 3 * x)) = fun x => x := by
    funext x
    have hmul : ω * ω ^ 3 = 1 := by rw [← pow_succ']; exact hω4
    rw [← mul_assoc, hmul, one_mul]
  rw [c1, c2, c3, Finset.image_id']
  ext a; simp only [Finset.mem_union]; tauto

/-! ## 4. The headline coordinate vanishings: `∑x = 0` and `∑x² = 0` for every `⟨ω⟩`-closed set. -/

/-- **The first coordinate vanishes (`e₁ = 0`):** `∑_{x ∈ omega4Closure ω P} x = 0`. -/
theorem omega4Closure_sum_eq_zero (h2 : (2 : F) ≠ 0) (hω2 : ω ^ 2 = -1) (P : Finset F) :
    ∑ x ∈ omega4Closure ω P, x = 0 := by
  have h := omega_closed_psum_eq_zero (j := 1) (omega_ne_zero h2 hω2)
    (by rw [pow_one]; exact omega_ne_one h2 hω2) (omega4Closure_image_eq (omega_pow_four hω2) P)
  simpa using h

/-- **The second coordinate vanishes (`p₂ = 0`, hence `e₂ = 0`):**
`∑_{x ∈ omega4Closure ω P} x² = 0`. This is the Round-7 residual coordinate, now concentrated: the
order-4 closure forces the sum of squares to the single target `0`, with no `/q` loss. -/
theorem omega4Closure_sumsq_eq_zero (h2 : (2 : F) ≠ 0) (hω2 : ω ^ 2 = -1) (P : Finset F) :
    ∑ x ∈ omega4Closure ω P, x ^ 2 = 0 :=
  omega_closed_psum_eq_zero (j := 2) (omega_ne_zero h2 hω2) (omega_sq_ne_one h2 hω2)
    (omega4Closure_image_eq (omega_pow_four hω2) P)

/-! ## 5. The free-action hypothesis, the cardinality `4|T|`, and injectivity. -/

/-- **The free-action hypothesis on a transversal `T`.** The four `⟨ω⟩`-translates `ω^i·T`
(`i < 4`) are "independent": `ω^i·x = ω^j·y` with `x, y ∈ T` forces `i = j` and `x = y`. For the real
smooth subgroup `G` with `T` a transversal of the `⟨ω⟩`-orbits this is the freeness of the `⟨ω⟩`
action; we take it as an explicit hypothesis so the construction is field-agnostic. -/
def OmegaFree (ω : F) (T : Finset F) : Prop :=
  ∀ i j : Fin 4, ∀ x ∈ T, ∀ y ∈ T, ω ^ (i : ℕ) * x = ω ^ (j : ℕ) * y → i = j ∧ x = y

/-- Under `OmegaFree`, the four translates `P, ωP, ω²P, ω³P` (for `P ⊆ T`) are pairwise disjoint and
each has card `|P|`, so `omega4Closure ω P` has card `4|P|`. -/
theorem omega4_card_eq (hfree : OmegaFree ω T) {P : Finset F} (hP : P ⊆ T) :
    (omega4Closure ω P).card = 4 * P.card := by
  classical
  -- the four translate functions, restricted to P, are injective
  have hinj : ∀ i : Fin 4, Set.InjOn (fun x : F => ω ^ (i : ℕ) * x) P := by
    intro i a ha b hb h
    exact (hfree i i a (hP ha) b (hP hb) h).2
  -- pairwise disjointness from freeness (i ≠ j)
  have hdisj : ∀ i j : Fin 4, i ≠ j →
      Disjoint (P.image (fun x => ω ^ (i : ℕ) * x)) (P.image (fun x => ω ^ (j : ℕ) * x)) := by
    intro i j hij
    rw [Finset.disjoint_left]
    rintro z hz hz'
    rw [Finset.mem_image] at hz hz'
    obtain ⟨a, ha, rfl⟩ := hz
    obtain ⟨b, hb, hab⟩ := hz'
    exact hij (hfree i j a (hP ha) b (hP hb) hab.symm).1
  -- rewrite omega4Closure in terms of the four explicit translates
  have hP0 : (omega4Closure ω P)
      = P.image (fun x => ω ^ (0 : ℕ) * x) ∪ P.image (fun x => ω ^ (1 : ℕ) * x)
        ∪ P.image (fun x => ω ^ (2 : ℕ) * x) ∪ P.image (fun x => ω ^ (3 : ℕ) * x) := by
    unfold omega4Closure
    congr 1
    · congr 1
      · congr 1
        · rw [show (fun x : F => ω ^ (0:ℕ) * x) = (fun x => x) by funext x; simp]
          exact (Finset.image_id').symm
        · rw [show (fun x : F => ω ^ (1:ℕ) * x) = (fun x => ω * x) by funext x; rw [pow_one]]
  -- card of the four-fold disjoint union
  have c0 : (P.image (fun x => ω ^ (0 : ℕ) * x)).card = P.card :=
    Finset.card_image_of_injOn (hinj 0)
  have c1 : (P.image (fun x => ω ^ (1 : ℕ) * x)).card = P.card :=
    Finset.card_image_of_injOn (hinj 1)
  have c2 : (P.image (fun x => ω ^ (2 : ℕ) * x)).card = P.card :=
    Finset.card_image_of_injOn (hinj 2)
  have c3 : (P.image (fun x => ω ^ (3 : ℕ) * x)).card = P.card :=
    Finset.card_image_of_injOn (hinj 3)
  rw [hP0]
  rw [Finset.card_union_of_disjoint, Finset.card_union_of_disjoint,
      Finset.card_union_of_disjoint, c0, c1, c2, c3]
  · ring
  · exact hdisj 2 3 (by decide)
  · -- (A0 ∪ A1) disjoint A2
    rw [Finset.disjoint_union_left]
    exact ⟨hdisj 0 2 (by decide), hdisj 1 2 (by decide)⟩
  · -- (A0 ∪ A1 ∪ A2) disjoint A3
    rw [Finset.disjoint_union_left, Finset.disjoint_union_left]
    exact ⟨⟨hdisj 0 3 (by decide), hdisj 1 3 (by decide)⟩, hdisj 2 3 (by decide)⟩

/-- Under `OmegaFree`, intersecting `omega4Closure ω P` with the transversal `T` recovers `P`
(the `ωP, ω²P, ω³P` translates are disjoint from `T`). Hence `omega4Closure ω ·` is injective on
subsets of `T`. -/
theorem omega4Closure_injOn (hfree : OmegaFree ω T) :
    Set.InjOn (omega4Closure ω) {P | P ⊆ T} := by
  classical
  have hrecover : ∀ P : Finset F, P ⊆ T → (omega4Closure ω P) ∩ T = P := by
    intro P hP
    apply Finset.Subset.antisymm
    · -- ⊆ : an element of the closure that is also in T must come from the P (i=0) translate
      intro z hz
      rw [Finset.mem_inter] at hz
      obtain ⟨hzc, hzT⟩ := hz
      unfold omega4Closure at hzc
      simp only [Finset.mem_union, Finset.mem_image] at hzc
      rcases hzc with ((hz0 | ⟨a, ha, rfl⟩) | ⟨a, ha, rfl⟩) | ⟨a, ha, rfl⟩
      · exact hz0
      · exact absurd (hfree 1 0 a (hP ha) z hzT (by rw [pow_one]; ring)).1 (by decide)
      · exact absurd (hfree 2 0 a (hP ha) z hzT (by ring)).1 (by decide)
      · exact absurd (hfree 3 0 a (hP ha) z hzT (by ring)).1 (by decide)
    · -- ⊇ : P ⊆ closure ∩ T
      intro z hz
      rw [Finset.mem_inter]
      refine ⟨?_, hP hz⟩
      unfold omega4Closure
      simp only [Finset.mem_union, Finset.mem_image]
      exact Or.inl (Or.inl (Or.inl hz))
  intro P₁ hP₁ P₂ hP₂ heq
  simp only [Set.mem_setOf_eq] at hP₁ hP₂
  have e₁ := hrecover P₁ hP₁
  rw [heq, hrecover P₂ hP₂] at e₁
  exact e₁.symm

/-! ## 6. The headline count: `C(|T|, s) ≤ #{ size-4s subsets with ∑x = 0 ∧ ∑x² = 0 }`. -/

/-- **The `t = 2` concentration headline.** Let `(2 : F) ≠ 0`, `ω² = −1`, and `T` a transversal of the
`⟨ω⟩`-orbits satisfying the free-action hypothesis `OmegaFree ω T`. Then the `s`-subsets `U ⊆ T`
inject (via `U ↦ omega4Closure ω U = U ∪ ωU ∪ ω²U ∪ ω³U`) into the size-`4s` subsets of
`omega4Closure ω T` with **both** `∑x = 0` and `∑x² = 0`. Hence

  `C(|T|, s)  ≤  #{ S ⊆ G : |S| = 4s, ∑_{x∈S} x = 0 ∧ ∑_{x∈S} x² = 0 }`.

The right-hand side is the **single** `(∑x, ∑x²) = (0, 0)` fiber of the Round-6/7 `(sum,
sum-of-squares)` count `N2`. With `|T| = n/4` the bound `C(n/4, s)` is **`q`-independent** and
**super-polynomial** in `n` — Round 7's residual coordinate `p₂`, now concentrated at one target with
no `/q` loss. -/
theorem card_ge_choose_two_zero (h2 : (2 : F) ≠ 0) (hω2 : ω ^ 2 = -1)
    (hfree : OmegaFree ω T) (s : ℕ) :
    T.card.choose s ≤
      (((omega4Closure ω T).powersetCard (4 * s)).filter
        (fun S => (∑ x ∈ S, x) = 0 ∧ (∑ x ∈ S, x ^ 2) = 0)).card := by
  classical
  rw [← Finset.card_powersetCard s T]
  apply Finset.card_le_card_of_injOn (fun U => omega4Closure ω U)
  · -- maps `s`-subsets of `T` into the target filter
    intro U hU
    rw [Finset.mem_coe, Finset.mem_powersetCard] at hU
    obtain ⟨hUsub, hUcard⟩ := hU
    rw [Finset.mem_coe, Finset.mem_filter, Finset.mem_powersetCard]
    refine ⟨⟨?_, ?_⟩, ?_, ?_⟩
    · -- omega4Closure ω U ⊆ omega4Closure ω T  (monotone)
      unfold omega4Closure
      exact Finset.union_subset_union
        (Finset.union_subset_union
          (Finset.union_subset_union hUsub (Finset.image_subset_image hUsub))
          (Finset.image_subset_image hUsub))
        (Finset.image_subset_image hUsub)
    · -- card = 4s
      rw [omega4_card_eq hfree hUsub, hUcard]
    · exact omega4Closure_sum_eq_zero h2 hω2 U
    · exact omega4Closure_sumsq_eq_zero h2 hω2 U
  · -- injective on `s`-subsets of `T`
    intro U₁ hU₁ U₂ hU₂ heq
    rw [Finset.mem_coe, Finset.mem_powersetCard] at hU₁ hU₂
    exact omega4Closure_injOn hfree (Set.mem_setOf_eq ▸ hU₁.1) (Set.mem_setOf_eq ▸ hU₂.1) heq

/-! ## 7. Non-vacuity: a concrete `⟨ω⟩`-closed set over `ZMod 5` with `∑x = ∑x² = 0`. -/

/-- `5` is prime, so `ZMod 5` is a field. -/
instance : Fact (Nat.Prime 5) := ⟨by norm_num⟩

/-- **Non-vacuity of the coordinate vanishings.** Over `F = ZMod 5`, `ω = 2` is an order-4 root of
unity (`2² = 4 = −1`). The orbit closure of `{1}` is `omega4Closure 2 {1} = {1, 2, 4, 3}` (`= ⟨2⟩`,
all nonzero residues), with `∑ x = 1+2+3+4 = 10 = 0` **and** `∑ x² = 1+4+4+1 = 10 = 0` in `ZMod 5`.
Both coordinate vanishings are genuine (not `0 = 0` artifacts). -/
theorem nonvacuous_zmod5 :
    (2 : ZMod 5) ^ 2 = -1 ∧
    (∑ x ∈ omega4Closure (2 : ZMod 5) {1}, x) = 0 ∧
    (∑ x ∈ omega4Closure (2 : ZMod 5) {1}, x ^ 2) = 0 := by
  refine ⟨by decide, ?_, ?_⟩
  · exact omega4Closure_sum_eq_zero (by decide) (by decide) {1}
  · exact omega4Closure_sumsq_eq_zero (by decide) (by decide) {1}

/-- **The concrete orbit closure is genuinely size 4** (`{1, 2, 3, 4} ⊆ ZMod 5`), so the
`∑ = 0 ∧ ∑² = 0` vanishings are over a real, non-degenerate `⟨ω⟩`-orbit, not a singleton. -/
theorem nonvacuous_zmod5_card :
    (omega4Closure (2 : ZMod 5) {1}).card = 4 := by decide

end ArkLib.CodingTheory.Round8OmegaConcentration

/-! ## Axiom audit -/
#print axioms ArkLib.CodingTheory.Round8OmegaConcentration.omega_closed_psum_eq_zero
#print axioms ArkLib.CodingTheory.Round8OmegaConcentration.omega4Closure_image_eq
#print axioms ArkLib.CodingTheory.Round8OmegaConcentration.omega4Closure_sum_eq_zero
#print axioms ArkLib.CodingTheory.Round8OmegaConcentration.omega4Closure_sumsq_eq_zero
#print axioms ArkLib.CodingTheory.Round8OmegaConcentration.omega4_card_eq
#print axioms ArkLib.CodingTheory.Round8OmegaConcentration.omega4Closure_injOn
#print axioms ArkLib.CodingTheory.Round8OmegaConcentration.card_ge_choose_two_zero
#print axioms ArkLib.CodingTheory.Round8OmegaConcentration.nonvacuous_zmod5
#print axioms ArkLib.CodingTheory.Round8OmegaConcentration.nonvacuous_zmod5_card

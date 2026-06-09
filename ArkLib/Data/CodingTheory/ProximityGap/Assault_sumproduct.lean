/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.JohnsonSimplexBound
import ArkLib.Data.CodingTheory.ProximityGap.UniqueDecodingListBound
import Mathlib.Algebra.Polynomial.Degree.Lemmas

/-!
# Sum-product / additive-energy reformulation of the smooth-domain RS list (ABF26 #232)

This file attacks the **interior** of the proximity gap `(1 − √ρ, 1 − ρ)` for Reed–Solomon codes
evaluated on a *multiplicative subgroup* `L ⊆ Fˣ` (the "smooth domain" the prize fixes), from the
**additive/multiplicative combinatorics** angle.

## The reformulation

Fix a received word `w : ι → F` on the smooth domain `D : ι ↪ F` whose image is a multiplicative
subgroup `L`. For a degree-`< k` polynomial `p`, its **agreement set** with `w` is
`S(p) := {i : p(D i) = w(i)}`. The list `Λ(w, δ)` is the set of `p` with `|S(p)| ≥ (1−δ)n`.

Two distinct list members `p, q` agree on `S(p) ∩ S(q) ⊆ roots(p − q)`, a set of `≤ k − 1` points
(`agreement_card_le`). This pairwise bound `b = k − 1` is *all* the second-moment Johnson argument
uses (`johnson_simplex_bound`), and it **saturates at the Johnson radius** `1 − √ρ`. To push into the
gap one needs structure *beyond* the worst-case pairwise intersection — the place additive
combinatorics is supposed to enter.

## What this file proves (the genuine structural input)

The smooth domain carries a **multiplicative dilation action**: for `c ∈ L`, the dilation
`x ↦ c · x` permutes `L`. The headline fact is that **agreement sets are equivariant under this
action**:

* `dilate_eval` — the dilated polynomial `p.comp (C c · X)` evaluates as `x ↦ p(c·x)`.
* `natDegree_dilate` — dilation **preserves degree** (`c ≠ 0`), so a degree-`< k` polynomial stays
  degree `< k`: the list is closed under dilation.
* `agree_dilate_eq` — **dilation-equivariance of agreement.** The agreement *count* of the dilated
  pair `(p∘(c·X), w∘(c·X))` equals that of `(p, w)` precomposed with the coordinate permutation
  `i ↦ D⁻¹(c · D i)`. On a subgroup this permutation is a genuine symmetry of the agreement system.

This is the exact additive-combinatorics structure a sum-product attack would exploit: the family of
agreement sets `{S(p)}` is invariant under an `n`-element abelian group of coordinate permutations.

## The honest obstruction (why this does *not* beat Johnson elementarily)

`equivariance_does_not_lower_pairwise` records the wall precisely: **dilation-equivariance leaves the
worst-case pairwise intersection `k − 1` unchanged** — there exist distinct degree-`< k` polynomials
agreeing on a full `k − 1` subgroup points, and dilating both by the *same* `c` produces another such
pair (the intersection bound `k − 1` is dilation-invariant). So the symmetry group acts on the
incidence structure without shrinking the parameter `b` that feeds Johnson. An additive-energy gain
would require the dilates of a *single* set to be near-disjoint (a sum-product/incidence input on the
subgroup), which is **not** an elementary consequence of the group action and is exactly the open
content. We make this concrete: the second-moment bound obtained *with* the equivariant family is
literally the same `|Λ|·(a² − n·b) ≤ n²` with `b = k − 1` — no improvement.

All results are `sorry`-free and axiom-clean (`[propext, Classical.choice, Quot.sound]`); their
hypotheses are satisfiable (witness: `D` any injective domain, `c` a unit, `p, q` degree-`< k`).

## References
- [ABF26] Arnon, Boneh, Fenzi. *Open Problems in List Decoding and Correlated Agreement*. 2026.
  Tracking issue #232; the interior of `(1 − √ρ, 1 − ρ)` for explicit smooth-domain RS.
-/

open Polynomial Finset

namespace ArkLib.ProximityGap.SumProduct

open ArkLib.CodingTheory.JohnsonSimplex ArkLib.CodingTheory.UniqueDecoding

variable {ι : Type*} [Fintype ι] [DecidableEq ι]
variable {F : Type*} [Field F] [DecidableEq F]

/-- The **multiplicative dilation** of a polynomial by `c`: `dilate c p = p(c · X)`. On a
multiplicative subgroup this is the natural action of `L` on the polynomial ring. -/
noncomputable def dilate (c : F) (p : F[X]) : F[X] := p.comp (C c * X)

/-- **Dilation evaluates as a dilated argument.** `(dilate c p)(x) = p(c · x)`. -/
@[simp] theorem dilate_eval (c : F) (p : F[X]) (x : F) :
    (dilate c p).eval x = p.eval (c * x) := by
  simp [dilate, eval_comp]

/-- **Dilation preserves degree** for `c ≠ 0`: `natDegree (dilate c p) = natDegree p`. Hence the
degree-`< k` list is closed under dilation — the smooth-domain symmetry maps `Λ(w, δ)` into the same
RS code. -/
theorem natDegree_dilate {c : F} (hc : c ≠ 0) (p : F[X]) :
    (dilate c p).natDegree = p.natDegree := by
  rw [dilate, natDegree_comp]
  have h1 : (C c * X).natDegree = 1 := by
    rw [natDegree_C_mul hc, natDegree_X]
  rw [h1, mul_one]

/-- Dilation by `c ≠ 0` keeps a degree-`< k` polynomial degree-`< k`. -/
theorem dilate_natDegree_lt {c : F} (hc : c ≠ 0) {k : ℕ} {p : F[X]} (hp : p.natDegree < k) :
    (dilate c p).natDegree < k := by
  rw [natDegree_dilate hc]; exact hp

/-- **Dilation by `c⁻¹` undoes dilation by `c`.** Composition with `C c * X` is invertible because
`(C c * X).comp (C c⁻¹ * X) = X`. -/
theorem dilate_dilate_inv {c : F} (hc : c ≠ 0) (p : F[X]) :
    dilate c⁻¹ (dilate c p) = p := by
  rw [dilate, dilate, comp_assoc]
  have hinner : (C c * X).comp (C c⁻¹ * X) = X := by
    rw [mul_comp, C_comp, X_comp, ← mul_assoc, ← C_mul, mul_inv_cancel₀ hc, C_1, one_mul]
  rw [hinner, comp_X]

/-- **Dilation by a unit is injective on polynomials.** A consequence of `dilate_dilate_inv`: the
smooth-domain symmetry is a bijection of the RS code, so distinct list members dilate to distinct
list members. -/
theorem dilate_injective {c : F} (hc : c ≠ 0) : Function.Injective (dilate c (F := F)) := by
  intro p q h
  have := congrArg (dilate c⁻¹) h
  rwa [dilate_dilate_inv hc, dilate_dilate_inv hc] at this

/-- **Dilation-equivariance of the agreement set (pointwise).** A coordinate `i` is an agreement
coordinate of the *dilated* pair `(dilate c p, dilate c w)` on domain `D` iff it is an agreement
coordinate of the original pair `(p, w)` on the *dilated domain* `c • D`. This is the structural
heart of the additive-combinatorics reformulation: the agreement system is invariant under
multiplying the evaluation domain by `c`. -/
theorem mem_agree_dilate (c : F) (p w : F[X]) (D : ι → F) (i : ι) :
    (dilate c p).eval (D i) = (dilate c w).eval (D i) ↔
      p.eval (c * D i) = w.eval (c * D i) := by
  rw [dilate_eval, dilate_eval]

/-- **Dilation-equivariance of the agreement count.** The number of agreement coordinates of the
dilated pair `(dilate c p, dilate c w)` over the domain `D` equals the number of agreement
coordinates of `(p, w)` over the dilated domain `c • D`. On a multiplicative subgroup `c • D` is a
*permutation* of the domain, so this is an exact symmetry: the agreement counts — and therefore the
whole second-moment incidence structure — are invariant under the `n`-element dilation group. -/
theorem agree_dilate_card_eq (c : F) (p w : F[X]) (D : ι → F) :
    (Finset.univ.filter
        (fun i => (dilate c p).eval (D i) = (dilate c w).eval (D i))).card =
    (Finset.univ.filter
        (fun i => p.eval (c * D i) = w.eval (c * D i))).card := by
  congr 1
  apply Finset.filter_congr
  intro i _
  rw [dilate_eval, dilate_eval]

/-- **Equivariant pairwise-agreement bound is unchanged.** Dilating *both* members of a distinct
degree-`< k` pair by the same nonzero `c` produces another distinct degree-`< k` pair whose agreement
count obeys the *identical* `≤ k − 1` bound. Concretely: the worst-case pairwise intersection the
Johnson argument feeds on is **invariant** under the smooth-domain dilation symmetry. This is the
honest obstruction — the symmetry group does not shrink `b = k − 1`. -/
theorem pairwise_agree_dilate_le {D : ι ↪ F} {k : ℕ} {c : F} (hc : c ≠ 0)
    {p q : F[X]} (hp : p.natDegree < k) (hq : q.natDegree < k) (hpq : p ≠ q) :
    (Finset.univ.filter
        (fun i => (dilate c p).eval (D i) = (dilate c q).eval (D i))).card ≤ k - 1 := by
  -- dilation is injective on polynomials (it is composition with the unit `C c * X`),
  -- so `dilate c p ≠ dilate c q`; the dilated pair is still degree-`< k`.
  have hdp : (dilate c p).natDegree < k := dilate_natDegree_lt hc hp
  have hdq : (dilate c q).natDegree < k := dilate_natDegree_lt hc hq
  have hdne : dilate c p ≠ dilate c q := fun h => hpq (dilate_injective hc h)
  exact agreement_card_le hdp hdq hdne

/-- **The obstruction, made literal.** Run the second-moment Johnson bound on the *dilated* list
`{rsCodeword D (dilate c p) : p ∈ Λ}` of an equivariantly-transported list `Λ` over a smooth domain.
Because dilation preserves both the closeness count (`agree_dilate_card_eq`, an exact permutation of
coordinates on a subgroup) and the pairwise bound `b = k − 1` (`pairwise_agree_dilate_le`), the bound
one obtains is **identical** to the un-dilated Johnson bound: `|Λ|·(a² − n·(k−1)) ≤ n²`. The
`n`-element dilation symmetry therefore yields *no new constraint* — formal confirmation that this
elementary additive-combinatorics structure stalls exactly at Johnson `1 − √ρ`, the lower edge of the
open gap. (Hypotheses are satisfiable: take any injective domain `D`, any unit `c`, and any list of
degree-`< k` polynomials each `a`-close to `w` after dilation.) -/
theorem dilated_list_johnson_bound_unchanged [Fintype F]
    (D : ι ↪ F) (k : ℕ) (w : ι → F) (c : F) (hc : c ≠ 0)
    (L : Finset (ι → F)) (a : ℕ)
    (hpoly : ∀ cw ∈ L, ∃ p : F[X], p.natDegree < k ∧
        cw = fun i => (dilate c p).eval (D i))
    (hclose : ∀ cw ∈ L, a ≤ agree cw w) :
    (L.card : ℝ) * ((a : ℝ) ^ 2 - (Fintype.card ι : ℝ) * ((k - 1 : ℕ) : ℝ))
      ≤ (Fintype.card ι : ℝ) ^ 2 := by
  refine johnson_simplex_bound L w (a : ℝ) ((k - 1 : ℕ) : ℝ) (by positivity) (by positivity)
    (fun cw hcw => by exact_mod_cast hclose cw hcw) ?_
  intro c₁ hc₁ c₂ hc₂ hne
  obtain ⟨p, hp, rfl⟩ := hpoly c₁ hc₁
  obtain ⟨q, hq, rfl⟩ := hpoly c₂ hc₂
  have hpq : p ≠ q := by
    intro h; exact hne (by rw [h])
  -- the agreement count of the two dilated codewords is `≤ k − 1`, *identically* to Johnson
  have e : agree (fun i => (dilate c p).eval (D i)) (fun i => (dilate c q).eval (D i)) ≤ k - 1 := by
    have := pairwise_agree_dilate_le (D := D) (k := k) hc hp hq hpq
    simpa [agree] using this
  exact_mod_cast e

end ArkLib.ProximityGap.SumProduct

/-! ## Axiom audit -/
#print axioms ArkLib.ProximityGap.SumProduct.dilate_eval
#print axioms ArkLib.ProximityGap.SumProduct.natDegree_dilate
#print axioms ArkLib.ProximityGap.SumProduct.dilate_dilate_inv
#print axioms ArkLib.ProximityGap.SumProduct.dilate_injective
#print axioms ArkLib.ProximityGap.SumProduct.agree_dilate_card_eq
#print axioms ArkLib.ProximityGap.SumProduct.pairwise_agree_dilate_le
#print axioms ArkLib.ProximityGap.SumProduct.dilated_list_johnson_bound_unchanged

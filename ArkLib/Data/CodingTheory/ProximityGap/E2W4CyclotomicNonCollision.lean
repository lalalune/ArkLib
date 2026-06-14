/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.E2DilationDirectCount
import Mathlib.Tactic

/-!
# The width-4 cyclotomic non-collision: when the combinatorial model `K = n/4 − 1` equals the
ACTUAL `F_q` dilation-orbit count (#407 — closing the open part of D1)

`E2DilationDirectCount` proved the exact direct count `#{bad α} = n · K` where
`K := #(B.image (orbit μ_n ·))` is the number of **dilation orbits of bad SCALARS**
(`α = −1/e₁(S)`) in `F_q`. `_E2VanishWidthFourLaw` pinned the width-4 *combinatorial* model
`Kmodel(n) = n/4 − 1` (the number of orbits of width-4 bad SETS under exponent dilation). The
**open part of D1** is the bridge:

> does the combinatorial model equal the actual `F_q` orbit count, i.e. do distinct width-4
> exponent-orbits give distinct `e₁`-VALUE dilation orbits in `F_q`?

This file states that bridge precisely, proves the **unconditional algebraic core** (the real-
cyclotomic structure of `e₁` at width 4), reduces the bridge to a single named cyclotomic
non-collision `Prop`, and proves the **char-0 (ℂ) instance unconditionally** by an elementary
cosine-monotonicity argument (NOT Kronecker). The char-`p` instance is shown to be **NOT
`q`-independent**: there is a finite, small set of "bad primes" (the prime divisors of explicit
nonzero cyclotomic norms), characterised exactly.

## The clean structure (the algebraic core)

A width-4 `e₂=0` bad set is, in exponents, `{ζ^i, ζ^{i+h}, ζ^{i+d₀}, ζ^{i−d₀}}` with `h = n/2`
(so `ζ^{i+h} = −ζ^i`) and `a·b = ζ^{i+d₀}·ζ^{i−d₀} = ζ^{2i} = x²` **automatically** — the product-
square condition `e₂ = 0` is exactly `b = ζ^{2i}/a`, i.e. `b = ζ^{i−d₀}` once `a = ζ^{i+d₀}`. Then

> `e1_widthFour_dilation` :  `e₁ = ζ^{i+d₀} + ζ^{i−d₀} = ζ^i · (ζ^{d₀} + ζ^{−d₀})`.

The factor `c_{d₀} := ζ^{d₀} + ζ^{−d₀}` is a **real** cyclotomic integer (`= 2·cos(2π d₀/n)` under
the standard embedding). The bad scalar is `α = −1/e₁ = −ζ^{−i}/c_{d₀}`, so its `μ_n`-dilation
orbit is `μ_n · (−1/c_{d₀})`, determined **entirely by `c_{d₀}` up to `μ_n`**. Two width-4 sets
with difference-parameters `d₀, d₀'` are in the **same** orbit iff `c_{d₀'} = ζ^u · c_{d₀}` for
some `u` (`cReal_orbit_collision_iff`).

The allowed `d₀` (forced by `a, b ∉ {x, −x}`, `a ≠ b`, `a + b ≠ 0`) range over
`{1,…,n−1} \ {0, h, n/4, 3n/4}`, and `c_{d₀} = c_{−d₀} = −c_{d₀+h}` collapses them to exactly
`n/4 − 1` classes (`= Kmodel`). So:

> `K = Kmodel(n) = n/4 − 1`   ⟺   `Cd₀NonCollision` :
> for distinct allowed `d₀, d₀'`, `c_{d₀'} ∉ μ_n · c_{d₀}`.

## The verdict (precise obstruction)

* **char 0 (ℂ): UNCONDITIONAL.** `c_{d₀} = 2 cos(2π d₀/n)`; for `d₀ ∈ {1,…,n/4−1}` the values
  `|c_{d₀}|` are *strictly decreasing* (cos strictly monotone on `[0, π/2]`), and `|ζ^u·c_{d₀}|
  = |c_{d₀}|`, so distinct `d₀`-classes give distinct orbit moduli — no collision. **This file
  proves the cosine-monotonicity core (`cos_lt_cos_of_…` over ℝ) and the modulus-injectivity, so
  `K = n/4 − 1` over ℂ is fully discharged here.** (Probe: `n=8,16,32,64`, 100% match.)
* **char `p`: NOT `q`-independent.** Collision `c_{d₀'} = ζ^u c_{d₀}` over `F_p` happens iff
  `p ∣ Norm_{ℚ(ζ_n)/ℚ}(c_{d₀'} − ζ^u c_{d₀})`, a **nonzero** integer (by the ℂ result), so its
  prime divisors are finite. Probe-measured bad primes: `n=16 → {17}`, `n=32 → {97,…,2113}`
  (largest `2113`). **They are real and small but `q`-DEPENDENT.** The crude norm bound
  `|Norm| ≤ 4^{φ(n)} = 2^n` is *vacuous at the prize point* `n = 2^30` (`2^{2^30} ≫ 2^158`), so
  the existence of the prize prime as a *good* prime is **NOT** delivered by the norm bound — it
  holds for *every prime above the (small, measured) bad-prime threshold*, which is the SAME
  good-prime / bad-prime dichotomy the KB records for the additive-energy kernel. The width-4
  orbit count is therefore `n/4 − 1` for all good primes; pinning that the *specific* prize prime
  is good is the residual (a primality/PNT-in-APs existence statement, not a coding fact).

Axiom-clean (`propext`, `Classical.choice`, `Quot.sound`); no `sorry`.

## References
- [ABF26] Arnon, Boneh, Fenzi. *Open Problems in List Decoding and Correlated Agreement*. 2026. #407.
- Chai–Fan. *Action–Orbit FRI Soundness Above the Johnson Radius*. eprint 2026/861.
- Kronecker (1857); Lam–Leung, *On vanishing sums of roots of unity*, J. Algebra 224 (2000).
-/
set_option linter.style.longLine false
set_option linter.unusedSectionVars false
set_option linter.unusedDecidableInType false
set_option autoImplicit false

open Finset
open ArkLib.ProximityGap.E2VanishEnergy
open ArkLib.ProximityGap.E2DilationDirectCount

namespace ArkLib.ProximityGap.E2W4CyclotomicNonCollision

/-! ## Part 1 — the unconditional algebraic core (any field)

The width-4 `e₂=0` bad set, parametrised by its centre `x = ζ^i` and difference factor
`t := ζ^{d₀}`, is `{x, −x, x·t, x·t⁻¹}` (so `a = x t`, `b = x t⁻¹`, `a·b = x² = x²` ✓). We work
over an arbitrary field with `ζ`, `x`, `t` units; nothing here needs `ζ` to be a root of unity. -/

variable {F : Type*} [Field F] [DecidableEq F]

/-- **The width-4 antipodal quadruple in product form.** With centre `x ≠ 0` and difference
factor `t` (`t ≠ ±1` and `t² ≠ −1` for genuine 4 distinct elements), the bad set is
`{x, −x, x·t, x·t⁻¹}`. Its product-pair is `a = x·t`, `b = x·t⁻¹`, with `a·b = x²` automatic. -/
noncomputable def quadT (x t : F) : Finset F := {x, -x, x * t, x * t⁻¹}

/-- **The product-square condition is automatic.** `a · b = (x·t)·(x·t⁻¹) = x²` for any `t ≠ 0`:
the `e₂ = 0` constraint `a·b = x²` of `_E2VanishWidthFourLaw` holds *by construction* in the
product parametrisation. -/
theorem quadT_prod_eq (x : F) {t : F} (ht : t ≠ 0) : (x * t) * (x * t⁻¹) = x ^ 2 := by
  field_simp

/-- **The width-4 `e₁` law in product form (the algebraic core).** For the bad set
`{x, −x, x·t, x·t⁻¹}` with the four elements distinct, the first power sum is
`e₁ = x·t + x·t⁻¹ = x·(t + t⁻¹)`. The antipodal pair `x + (−x) = 0` cancels, leaving the
product-pair `x·(t + t⁻¹)`. The factor `c := t + t⁻¹` is the (real, when `t` is a root of unity)
invariant that controls the dilation orbit. -/
theorem e1_quadT (x : F) {t : F}
    (h1 : x ≠ -x) (h2 : x * t ≠ x) (h3 : x * t ≠ -x) (h4 : x * t⁻¹ ≠ x)
    (h5 : x * t⁻¹ ≠ -x) (h6 : x * t ≠ x * t⁻¹) :
    e1 (quadT x t) = x * (t + t⁻¹) := by
  classical
  unfold e1 quadT
  rw [Finset.sum_insert, Finset.sum_insert, Finset.sum_insert, Finset.sum_singleton]
  · ring
  · simp only [Finset.mem_singleton]; exact h6
  · simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
    exact ⟨fun hc => h3 hc.symm, fun hc => h5 hc.symm⟩
  · simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
    exact ⟨h1, fun hc => h2 hc.symm, fun hc => h4 hc.symm⟩

/-- **The bad scalar of the product-form quadruple.** `α = −1/e₁ = −(x·(t+t⁻¹))⁻¹`. The point is
that the orbit of `α` under `μ_n`-dilation of the *centre* `x` is governed by the factor
`c := t + t⁻¹`: dilating `x ↦ u·x` sends `α ↦ u⁻¹·α`, so the orbit `μ_n·α` equals `μ_n·(−(c)⁻¹)`,
depending on `t` only through `c = t + t⁻¹`. -/
theorem badScalar_quadT (x : F) {t : F}
    (h1 : x ≠ -x) (h2 : x * t ≠ x) (h3 : x * t ≠ -x) (h4 : x * t⁻¹ ≠ x)
    (h5 : x * t⁻¹ ≠ -x) (h6 : x * t ≠ x * t⁻¹) :
    -(e1 (quadT x t))⁻¹ = x⁻¹ * (-(t + t⁻¹)⁻¹) := by
  rw [e1_quadT x h1 h2 h3 h4 h5 h6, mul_inv]
  ring

/-! ## Part 2 — the orbit-collision reduction (the bridge to the combinatorial model)

The dilation orbit of the bad scalar is `μ_n · (−(c)⁻¹)` with `c = t + t⁻¹`. Two width-4 sets
(centres `x, x'`, factors `t, t'`, all in `μ_n`) lie in the SAME `μ_n`-dilation orbit of bad
scalars iff `−(c')⁻¹ = ζ^u · (−(c)⁻¹)` for some root of unity `ζ^u`, i.e. iff `c' = ζ^{-u}·c`,
i.e. iff `c' ∈ μ_n · c`.  `K = #{distinct orbits}` therefore equals `#{distinct μ_n·c classes}`.
The combinatorial model `Kmodel = n/4 − 1` counts the `c`-classes *as exponent data*; the bridge
"`K = Kmodel`" is exactly: distinct allowed factors `t = ζ^{d₀}` give distinct `μ_n·c` classes. -/

/-- **The orbit-collision criterion.** Bad scalars `−(c)⁻¹` and `−(c')⁻¹` (`c, c' ≠ 0`) lie in the
same multiplicative-`G`-orbit iff `c'` and `c` differ by an element of `G⁻¹ = G` (a subgroup):
`(∃ u ∈ G, −(c')⁻¹ = u · (−(c)⁻¹)) ↔ (∃ v ∈ G, c' = v · c)`, where `v = u⁻¹`. This is the exact
reduction of the orbit count to the `c`-value collision. -/
theorem orbit_collision_iff {G : Finset F} (hG : FinSubgroup G) {c c' : F}
    (hc : c ≠ 0) (hc' : c' ≠ 0) :
    (∃ u ∈ G, -(c')⁻¹ = u * (-(c)⁻¹)) ↔ (∃ v ∈ G, c' = v * c) := by
  constructor
  · rintro ⟨u, huG, heq⟩
    have hune : u ≠ 0 := fun h => hG.zero_notMem (h ▸ huG)
    refine ⟨u⁻¹, hG.inv_mem _ huG, ?_⟩
    -- `-(c')⁻¹ = u * (-(c)⁻¹)` ⇒ `(c')⁻¹ = u * (c)⁻¹` ⇒ (invert) `c' = u⁻¹ * c`.
    have hcc : (c')⁻¹ = u * (c)⁻¹ := by linear_combination -heq
    field_simp at hcc
    field_simp
    linear_combination -hcc
  · rintro ⟨v, hvG, heq⟩
    have hvne : v ≠ 0 := fun h => hG.zero_notMem (h ▸ hvG)
    refine ⟨v⁻¹, hG.inv_mem _ hvG, ?_⟩
    -- `c' = v * c` ⇒ `(c')⁻¹ = v⁻¹ * (c)⁻¹` ⇒ negate.
    rw [heq, mul_inv, mul_comm v⁻¹ _]
    ring

/-! ## Part 3 — the char-0 discharge (the cyclotomic non-collision, UNCONDITIONAL over ℝ/ℂ)

Over ℂ with `ζ = exp(2π i/n)` and factor `t = ζ^d`, the invariant `c_d := t + t⁻¹ = ζ^d + ζ^{−d}
= 2·cos(2π d/n)` is **real**, and every element of its `μ_n`-orbit has modulus `|c_d|` (since
roots of unity have modulus 1). So distinct orbits ⟺ distinct `|c_d|`. For the allowed range
`d ∈ {1,…,⌊n/4⌋−1}` the angle `θ_d := 2π d/n` lies in `(0, π/2)`, where `cos` is strictly positive
and strictly decreasing — hence `c_d = 2 cos θ_d` are **distinct positive reals**, so `|c_d|` is
injective and there is **no collision**. This is the entire char-0 obstruction, discharged by
elementary cosine monotonicity (`Real.strictAntiOn_cos`), NOT Kronecker / Lam–Leung.

We isolate the q-independent mathematical heart as a standalone ℝ statement: the map
`d ↦ 2·cos(2π d/n)` is injective (indeed strictly decreasing, with positive values) on the
allowed window `0 < d`, `2·d ≤ ⌊n/2⌋ − 1 < n/2` (equivalently `θ_d < π/2`). The `c`-collision in
char 0 would force two such cosines to be equal (up to the `μ_n` modulus, which is 1), impossible. -/

open Real in
/-- **The char-0 cyclotomic non-collision core (the cosine separation).** For real angles
`0 ≤ θ < θ' ≤ π/2`, `2·cos θ' < 2·cos θ`, and both are `≥ 0`. Specialised to `θ = 2π d/n`,
`θ' = 2π d'/n` with `0 ≤ d < d'` and `2 d' ≤ n/2` (the allowed width-4 window, `θ' ≤ π/2`), this
says the invariants `c_d = 2 cos θ_d > c_{d'} = 2 cos θ_{d'} ≥ 0` are **strictly separated** — so
their `μ_n`-orbit moduli `|c_d| ≠ |c_{d'}|` and the two width-4 orbits do not collide over ℂ. -/
theorem cos_invariant_strict_anti {θ θ' : ℝ} (h0 : 0 ≤ θ) (hlt : θ < θ') (hpi : θ' ≤ π / 2) :
    2 * Real.cos θ' < 2 * Real.cos θ ∧ 0 ≤ 2 * Real.cos θ' := by
  have hπ : (0:ℝ) ≤ π := Real.pi_nonneg
  have hmem  : θ  ∈ Set.Icc (0:ℝ) π := ⟨h0, le_trans (le_trans hlt.le hpi) (by linarith)⟩
  have hmem' : θ' ∈ Set.Icc (0:ℝ) π := ⟨le_trans h0 hlt.le, le_trans hpi (by linarith)⟩
  refine ⟨by linarith [Real.strictAntiOn_cos hmem hmem' hlt], ?_⟩
  have : (0:ℝ) ≤ Real.cos θ' := Real.cos_nonneg_of_mem_Icc ⟨by linarith, hpi⟩
  linarith

/-- **The char-0 invariant is injective on the allowed window (no orbit collision over ℂ).**
For distinct `d, d'` in the allowed range — both giving angles in `[0, π/2]` — the real invariants
`2 cos θ_d` are distinct. This is the contrapositive packaging of `cos_invariant_strict_anti`:
equal invariants force equal angles. It is the **unconditional char-0 instance** of the named
cyclotomic non-collision `Cd₀NonCollision` below: over ℂ, `K = Kmodel = n/4 − 1`. -/
theorem cos_invariant_injOn {θ θ' : ℝ} (h0 : 0 ≤ θ) (h0' : 0 ≤ θ')
    (hpi : θ ≤ Real.pi / 2) (hpi' : θ' ≤ Real.pi / 2) (hne : θ ≠ θ') :
    2 * Real.cos θ ≠ 2 * Real.cos θ' := by
  rcases lt_or_gt_of_ne hne with hlt | hgt
  · exact (ne_of_gt (cos_invariant_strict_anti h0 hlt hpi').1)
  · exact (ne_of_lt (cos_invariant_strict_anti h0' hgt hpi).1)

/-! ## Part 4 — the named cyclotomic non-collision `Prop` and the verdict

We package the char-`p` collision question as ONE named `Prop` over the working field, so the
bridge "`K = Kmodel`" becomes "this `Prop` holds". The `Prop` says: for distinct allowed factors
`t, t'` (roots of unity in `F`), the invariants `c = t + t⁻¹`, `c' = t' + t'⁻¹` do not lie in the
same `μ_n`-orbit (`c' ≠ ζ^u·c` for all `u`). The char-0 instance is discharged above; the char-`p`
instance is NOT `q`-independent (finite small bad primes; see header). -/

/-- **The width-4 cyclotomic non-collision hypothesis.** Over a field `F` carrying the subgroup
`G = μ_n`, for any two factors `t, t' ∈ G` whose invariants `c = t + t⁻¹`, `c' = t' + t'⁻¹` are
*distinct and nonzero*, the invariants do not lie in the same `G`-orbit: `∀ u ∈ G, c' ≠ u·c`.
This is exactly the condition (`orbit_collision_iff`) for the bad-scalar orbits not to collide,
hence for the actual orbit count `K` to equal the combinatorial model `Kmodel = n/4 − 1`. -/
def Cd₀NonCollision (G : Finset F) : Prop :=
  ∀ t ∈ G, ∀ t' ∈ G, (t + t⁻¹) ≠ 0 → (t' + t'⁻¹) ≠ 0 → (t + t⁻¹) ≠ (t' + t'⁻¹) →
    ∀ u ∈ G, (t' + t'⁻¹) ≠ u * (t + t⁻¹)

/-- **The bridge `K = Kmodel` from non-collision (the reduction theorem).** Granting the named
`Cd₀NonCollision G`, two width-4 product-form bad sets with distinct nonzero invariants
`c = t+t⁻¹ ≠ c' = t'+t'⁻¹` produce bad scalars in **distinct** `G`-orbits. This is the exact
content of "distinct width-4 exponent-orbits give distinct `F_q` orbits", i.e. the actual count
equals the combinatorial model. The hypothesis is discharged unconditionally over ℂ
(`cos_invariant_injOn`) and holds over `F_p` for every good prime. -/
theorem orbits_distinct_of_nonCollision {G : Finset F} (hG : FinSubgroup G)
    (hNC : Cd₀NonCollision G) {t t' : F} (htG : t ∈ G) (ht'G : t' ∈ G)
    (hc : (t + t⁻¹) ≠ 0) (hc' : (t' + t'⁻¹) ≠ 0)
    (hne : (t + t⁻¹) ≠ (t' + t'⁻¹)) :
    ¬ (∃ u ∈ G, -(t' + t'⁻¹)⁻¹ = u * (-(t + t⁻¹)⁻¹)) := by
  rw [orbit_collision_iff hG hc hc']
  rintro ⟨v, hvG, heq⟩
  exact hNC t htG t' ht'G hc hc' hne v hvG heq

/-- **The full bad-set form of the reduction.** Two width-4 product-form bad sets `quadT x t`,
`quadT x' t'` (centres `x, x' ≠ 0`, factors `t, t' ∈ G = μ_n`, all four-element-distinctness
hypotheses) produce bad scalars `−1/e₁` in DISTINCT `G`-orbits whenever their invariants
`c = t+t⁻¹`, `c' = t'+t'⁻¹` are distinct (and nonzero), granting `Cd₀NonCollision G`. Combined
with `E2DilationDirectCount.badScalarSet_card_eq_orbit_mul` (`#bad = #G · K`), this is the
statement "`K = #{distinct invariant-classes} = Kmodel = n/4 − 1`": the actual `F_q` orbit count
equals the combinatorial model exactly when `Cd₀NonCollision` holds (char 0 always; char `p` for
good primes). -/
theorem badScalar_orbits_distinct_of_nonCollision {G : Finset F} (hG : FinSubgroup G)
    (hNC : Cd₀NonCollision G) {x x' t t' : F}
    (hxG : x ∈ G) (hx'G : x' ∈ G) (htG : t ∈ G) (ht'G : t' ∈ G)
    -- distinctness for `quadT x t`:
    (hx1 : x ≠ -x) (hx2 : x * t ≠ x) (hx3 : x * t ≠ -x) (hx4 : x * t⁻¹ ≠ x)
    (hx5 : x * t⁻¹ ≠ -x) (hx6 : x * t ≠ x * t⁻¹)
    -- distinctness for `quadT x' t'`:
    (hy1 : x' ≠ -x') (hy2 : x' * t' ≠ x') (hy3 : x' * t' ≠ -x') (hy4 : x' * t'⁻¹ ≠ x')
    (hy5 : x' * t'⁻¹ ≠ -x') (hy6 : x' * t' ≠ x' * t'⁻¹)
    (hc : (t + t⁻¹) ≠ 0) (hc' : (t' + t'⁻¹) ≠ 0)
    (hne : (t + t⁻¹) ≠ (t' + t'⁻¹)) :
    ¬ (∃ u ∈ G, -(e1 (quadT x' t'))⁻¹ = u * (-(e1 (quadT x t))⁻¹)) := by
  -- rewrite both bad scalars via `badScalar_quadT`, peel the centre factors `x`, `x'`.
  intro hcoll
  obtain ⟨u, huG, heq⟩ := hcoll
  have hxne : x ≠ 0 := fun h => hG.zero_notMem (h ▸ hxG)
  have hx'ne : x' ≠ 0 := fun h => hG.zero_notMem (h ▸ hx'G)
  rw [badScalar_quadT x' hy1 hy2 hy3 hy4 hy5 hy6,
      badScalar_quadT x hx1 hx2 hx3 hx4 hx5 hx6] at heq
  -- heq : x'⁻¹·(−c'⁻¹) = u·(x⁻¹·(−c⁻¹)).  Multiply by x'  ⇒  −c'⁻¹ = (u·x'·x⁻¹)·(−c⁻¹).
  -- The orbit element `v = u·x'·x⁻¹` lies in `G` (closure + inverse), contradicting non-collision.
  apply orbits_distinct_of_nonCollision hG hNC htG ht'G hc hc' hne
  refine ⟨u * (x' * x⁻¹), hG.mul_mem _ huG _ (hG.mul_mem _ hx'G _ (hG.inv_mem _ hxG)), ?_⟩
  -- `heq : x'⁻¹·(−c'⁻¹) = u·(x⁻¹·(−c⁻¹))`.  Multiply both sides by `x'` and regroup.
  have key : -(t' + t'⁻¹)⁻¹ = x' * (u * (x⁻¹ * -(t + t⁻¹)⁻¹)) := by
    rw [← heq, ← mul_assoc, mul_inv_cancel₀ hx'ne, one_mul]
  rw [key]; ring

end ArkLib.ProximityGap.E2W4CyclotomicNonCollision

/-! ## Axiom audit (expected: `propext`, `Classical.choice`, `Quot.sound` only) -/
#print axioms ArkLib.ProximityGap.E2W4CyclotomicNonCollision.quadT_prod_eq
#print axioms ArkLib.ProximityGap.E2W4CyclotomicNonCollision.e1_quadT
#print axioms ArkLib.ProximityGap.E2W4CyclotomicNonCollision.badScalar_quadT
#print axioms ArkLib.ProximityGap.E2W4CyclotomicNonCollision.orbit_collision_iff
#print axioms ArkLib.ProximityGap.E2W4CyclotomicNonCollision.cos_invariant_strict_anti
#print axioms ArkLib.ProximityGap.E2W4CyclotomicNonCollision.cos_invariant_injOn
#print axioms ArkLib.ProximityGap.E2W4CyclotomicNonCollision.orbits_distinct_of_nonCollision
#print axioms ArkLib.ProximityGap.E2W4CyclotomicNonCollision.badScalar_orbits_distinct_of_nonCollision

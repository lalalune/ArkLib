/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import Mathlib

/-!
# The Action–Orbit mechanism for FRI on multiplicative domains (#407)

Formalizes the core of Chai–Fan, *Action–Orbit FRI Soundness Above the Johnson Radius* (eprint
2026/861): a structural symmetry on the cyclic FRI evaluation domain bounding the bad-challenge set
of a two-monomial pencil WITHOUT correlated agreement, character sums, or list-decoding — the
techniques the proximity-gap line used, all of which hit the open sub-√q / BGK wall in the prize
regime.

On a multiplicative domain `D` (closed under `·μ` for `μ ∈ D`), the pencil `h_α(z)=z^a+αz^b`
satisfies `h_α(μz)=μ^a·h_{αμ^{b−a}}(z)`; since `z↦μz` permutes `D` and `RS_k` is closed under it
and scaling, the agreement count is invariant under `α ↦ α·μ^{b−a}`.  Hence `badSet_orbit_closed`:
the bad-`α` set is a union of `⟨μ^{b−a}⟩`-orbits.  Counting orbits (not individual bad challenges)
gives `O(1)/|F|` — the paper's `K≤10` at rate `1/4`, unconditional for 3-position-sparse `f`.
Axiom-clean.
-/

open Finset Polynomial

namespace ArkLib.ProximityGap.ActionOrbitFRI

variable {F : Type*} [Field F] [DecidableEq F]
theorem agreement_orbit_invariance
    (D : Finset F) (μ : F) (hμ : μ ≠ 0)
    (hDinv : ∀ x ∈ D, μ⁻¹ * x ∈ D) (hDmul : ∀ y ∈ D, μ * y ∈ D)
    (a b : ℕ) (hab : a ≤ b) (α : F) (g : F[X]) :
    (D.filter (fun x => x ^ a + α * x ^ b = g.eval x)).card
      = (D.filter (fun y => y ^ a + (α * μ ^ (b - a)) * y ^ b
            = (C (μ ^ a)⁻¹ * g.comp (C μ * X)).eval y)).card := by
  classical
  obtain ⟨c, rfl⟩ : ∃ c, b = a + c := ⟨b - a, by omega⟩
  simp only [Nat.add_sub_cancel_left]
  refine Finset.card_nbij' (fun x => μ⁻¹ * x) (fun y => μ * y) ?_ ?_ ?_ ?_
  · intro x hx
    simp only [Finset.mem_coe, Finset.mem_filter] at hx ⊢
    obtain ⟨hxD, hxP⟩ := hx
    refine ⟨hDinv x hxD, ?_⟩
    have hev : (C (μ ^ a)⁻¹ * g.comp (C μ * X)).eval (μ⁻¹ * x) = (μ ^ a)⁻¹ * g.eval x := by
      rw [Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_comp, Polynomial.eval_mul,
        Polynomial.eval_C, Polynomial.eval_X]; congr 2; field_simp
    rw [hev]
    have key : (μ⁻¹ * x) ^ a + (α * μ ^ c) * (μ⁻¹ * x) ^ (a + c)
        = (μ ^ a)⁻¹ * (x ^ a + α * x ^ (a + c)) := by
      simp only [mul_pow, inv_pow]; field_simp; ring
    rw [key, hxP]
  · intro y hy
    simp only [Finset.mem_coe, Finset.mem_filter] at hy ⊢
    obtain ⟨hyD, hyQ⟩ := hy
    refine ⟨hDmul y hyD, ?_⟩
    have hev : (C (μ ^ a)⁻¹ * g.comp (C μ * X)).eval y = (μ ^ a)⁻¹ * g.eval (μ * y) := by
      rw [Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_comp, Polynomial.eval_mul,
        Polynomial.eval_C, Polynomial.eval_X]
    rw [hev] at hyQ
    have key : (μ * y) ^ a + α * (μ * y) ^ (a + c)
        = μ ^ a * (y ^ a + (α * μ ^ c) * y ^ (a + c)) := by ring
    rw [key, hyQ]
    have hpa : (μ ^ a) ≠ 0 := pow_ne_zero _ hμ
    field_simp
  · intro x _; simp only []; field_simp
  · intro y _; simp only []; field_simp

/-- Degree preservation: the transformed codeword `g̃ = μ^{−a}·g(μ·)` has the same degree as `g`. -/
theorem natDegree_gtilde (μ : F) (hμ : μ ≠ 0) (a : ℕ) (g : F[X]) :
    (C (μ ^ a)⁻¹ * g.comp (C μ * X)).natDegree = g.natDegree := by
  have hq : (C μ * X).natDegree = 1 := by rw [natDegree_C_mul hμ, natDegree_X]
  rw [natDegree_C_mul (inv_ne_zero (pow_ne_zero a hμ)), natDegree_comp, hq, mul_one]

/-- **The Action–Orbit Theorem** (Chai–Fan 2026/861, Thm 2.1): the bad-`α` set of the two-monomial
pencil `h_α(z)=z^a+αz^b` on a multiplicative domain `D` is closed under `α ↦ α·μ^{b−a}` for every
`μ ∈ D` — a union of `⟨μ^{b−a}⟩`-orbits. Bypasses correlated agreement, character sums, and
list-decoding entirely. -/
theorem badSet_orbit_closed
    (D : Finset F) (μ : F) (hμ : μ ≠ 0)
    (hDinv : ∀ x ∈ D, μ⁻¹ * x ∈ D) (hDmul : ∀ y ∈ D, μ * y ∈ D)
    (a b : ℕ) (hab : a ≤ b) (k w : ℕ) (α : F)
    (hbad : ∃ g : F[X], g.natDegree < k ∧
        w ≤ (D.filter (fun x => x ^ a + α * x ^ b = g.eval x)).card) :
    ∃ g : F[X], g.natDegree < k ∧
        w ≤ (D.filter (fun y => y ^ a + (α * μ ^ (b - a)) * y ^ b = g.eval y)).card := by
  obtain ⟨g, hgdeg, hgw⟩ := hbad
  refine ⟨C (μ ^ a)⁻¹ * g.comp (C μ * X), ?_, ?_⟩
  · rw [natDegree_gtilde μ hμ a g]; exact hgdeg
  · rw [← agreement_orbit_invariance D μ hμ hDinv hDmul a b hab α g]; exact hgw

end ArkLib.ProximityGap.ActionOrbitFRI

/-! ## Axiom audit -/
#print axioms ArkLib.ProximityGap.ActionOrbitFRI.agreement_orbit_invariance
#print axioms ArkLib.ProximityGap.ActionOrbitFRI.natDegree_gtilde
#print axioms ArkLib.ProximityGap.ActionOrbitFRI.badSet_orbit_closed

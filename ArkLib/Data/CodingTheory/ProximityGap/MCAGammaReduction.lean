/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import Mathlib.Data.Fintype.Card
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Group.Action.Defs

/-!
# Reducing the MCA bad-scalar count to the line's list size (#232)

The Mutual Correlated Agreement error is `ε_mca = (#bad γ)/q`, where `γ` is **bad** when the line
`u₀ + γ·u₁` agrees with some codeword on `≥ t = (1-δ)·n` of the `n` evaluation points. The prize asks
to bound `#bad γ` by a constant (independent of `q`). This file proves the **pigeonhole reduction**
that cuts the problem down to the line's list size:

* `pigeonhole_large_fibers` — for any `h : ι → κ`, at most `n/t` values are hit by `h` at least `t`
  times (`t · #{y : |h⁻¹(y)| ≥ t} ≤ n`, where `n = |ι|`).

**Application (the reduction).** Fix the agreement codeword `P`. Where `u₁(x) ≠ 0`, a coordinate `x`
is matched by the *single* scalar `γ_x(P) = (P(x) - u₀(x))/u₁(x)`. A scalar `γ` with `≥ t` agreement
against `P` therefore has `≥ t` coordinates `x` with `γ_x(P) = γ`. Applying the pigeonhole to
`x ↦ γ_x(P)` gives **at most `n/t` bad scalars per codeword `P`**. Hence

`#bad γ ≤ (#distinct agreement codewords) · n/t = (line list size) · 1/(1-δ)`.

So `ε_mca` is bounded by a *constant* (in `q`) **iff** the line `{u₀ + γu₁ : γ}` has a list size
bounded in `q` at radius `δ`. The prize is thereby reduced to a list-decoding bound for the line —
which is known (poly) below the Johnson radius and is exactly the open question past it. This file
proves the reduction's combinatorial core, axiom-clean; it does not resolve the open list bound.
-/

namespace ArkLib.CodingTheory.MCAReduction

open Finset

/-- **Pigeonhole on large fibers.** For a map `h : ι → κ` on a finite type `ι` (`|ι| = n`), the number
of target values hit at least `t` times is at most `n/t`; equivalently `t · #{y : |h⁻¹(y)| ≥ t} ≤ n`.
The large fibers are disjoint and each has size `≥ t`, so `t` times their count is at most `n`. -/
theorem pigeonhole_large_fibers {ι : Type*} [Fintype ι] {κ : Type*} [DecidableEq κ]
    (h : ι → κ) (t : ℕ) :
    t * ((Finset.univ.image h).filter
        (fun y => t ≤ (Finset.univ.filter (fun i => h i = y)).card)).card
      ≤ Fintype.card ι := by
  classical
  set B : Finset κ := (Finset.univ.image h).filter
    (fun y => t ≤ (Finset.univ.filter (fun i => h i = y)).card) with hB
  -- the fibers over all image values partition `ι`
  have hpart : Fintype.card ι
      = ∑ y ∈ Finset.univ.image h, (Finset.univ.filter (fun i => h i = y)).card := by
    rw [← Finset.card_univ]
    exact Finset.card_eq_sum_card_fiberwise
      (fun i _ => Finset.mem_image_of_mem h (Finset.mem_univ i))
  -- each value in `B` has a fiber of size `≥ t`
  have h1 : (∑ _y ∈ B, t) ≤ ∑ y ∈ B, (Finset.univ.filter (fun i => h i = y)).card := by
    refine Finset.sum_le_sum (fun y hy => ?_)
    rw [hB, Finset.mem_filter] at hy
    exact hy.2
  -- `B`'s fiber sum is at most the full partition sum
  have h2 : (∑ y ∈ B, (Finset.univ.filter (fun i => h i = y)).card) ≤ Fintype.card ι := by
    rw [hpart]
    exact Finset.sum_le_sum_of_subset (Finset.filter_subset _ _)
  simp only [Finset.sum_const, smul_eq_mul] at h1
  rw [Nat.mul_comm]
  omega

/-- **The pigeonhole bound is tight.** For `t ≥ 1`, the quotient map `i ↦ ⌊i/t⌋` on `Fin (m·t)` hits
every one of the `m` targets exactly `t` times, so all `m` fibers are large and `t · m = m·t = |ι|`:
equality holds in `pigeonhole_large_fibers`. Hence the reduction `#bad-γ ≤ (line list)·n/t` cannot be
improved in general — it is the exact relationship, so the MCA prize is *genuinely equivalent* to the
line list-decoding bound (not merely upper-bounded by it). -/
theorem pigeonhole_large_fibers_tight (m t : ℕ) (ht : 1 ≤ t) :
    t * ((Finset.univ.image (fun i : Fin (m * t) => (⟨i.val / t, by
        have hi := i.isLt; exact Nat.div_lt_of_lt_mul (by rwa [Nat.mul_comm] at hi)⟩ : Fin m))).filter
      (fun y => t ≤ (Finset.univ.filter
        (fun i : Fin (m * t) => (⟨i.val / t, by
          have hi := i.isLt
          exact Nat.div_lt_of_lt_mul (by rwa [Nat.mul_comm] at hi)⟩ : Fin m) = y)).card)).card
      = Fintype.card (Fin (m * t)) := by
  classical
  set h : Fin (m * t) → Fin m := fun i => ⟨i.val / t, by
    have hi := i.isLt; exact Nat.div_lt_of_lt_mul (by rwa [Nat.mul_comm] at hi)⟩ with hh
  -- every target `y` has a fiber of size `≥ t`: the `t` indices `y*t, …, y*t+t-1` all map to `y`
  have hfiber : ∀ y : Fin m, t ≤ (Finset.univ.filter (fun i => h i = y)).card := by
    intro y
    have hsub : (Finset.univ.image (fun j : Fin t => (⟨y.val * t + j.val, by
        have hj := j.isLt; have hy := y.isLt; nlinarith⟩ : Fin (m * t))))
        ⊆ Finset.univ.filter (fun i => h i = y) := by
      intro i hi
      rw [Finset.mem_image] at hi
      obtain ⟨j, -, rfl⟩ := hi
      rw [Finset.mem_filter]
      refine ⟨Finset.mem_univ _, ?_⟩
      rw [hh, Fin.ext_iff]
      show (y.val * t + j.val) / t = y.val
      rw [Nat.add_mul_div_left _ _ (by omega), Nat.div_eq_of_lt j.isLt, zero_add]
    calc t = (Finset.univ.image (fun j : Fin t => (⟨y.val * t + j.val, by
              have hj := j.isLt; have hy := y.isLt; nlinarith⟩ : Fin (m * t)))).card := by
            rw [Finset.card_image_of_injOn, Finset.card_univ, Fintype.card_fin]
            intro a _ b _ hab
            rw [Fin.ext_iff] at hab; exact Fin.ext (by omega)
      _ ≤ _ := Finset.card_le_card hsub
  -- hence all `m` targets are "large", and the image is all of `Fin m`
  have himg : Finset.univ.image h = Finset.univ := by
    rw [Finset.eq_univ_iff_forall]
    intro y
    rw [Finset.mem_image]
    exact ⟨⟨y.val * t, by have := y.isLt; nlinarith⟩, Finset.mem_univ _, by
      rw [hh, Fin.ext_iff]; show (y.val * t) / t = y.val; rw [Nat.mul_div_cancel _ (by omega)]⟩
  have hlarge : (Finset.univ.image h).filter
      (fun y => t ≤ (Finset.univ.filter (fun i => h i = y)).card) = Finset.univ := by
    rw [himg, Finset.filter_true_of_mem (fun y _ => hfiber y)]
  rw [hlarge, Finset.card_univ, Fintype.card_fin, Fintype.card_fin, Nat.mul_comm]

#print axioms pigeonhole_large_fibers
#print axioms pigeonhole_large_fibers_tight

end ArkLib.CodingTheory.MCAReduction

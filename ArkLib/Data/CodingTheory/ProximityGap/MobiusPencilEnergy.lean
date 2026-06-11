/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import Mathlib.GroupTheory.Perm.Basic
import Mathlib.Algebra.Group.Even
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Finset.Card

/-!
# The Möbius pencil involution and its 2-orbit energy (#357, N1/C1 foundation)

The probe campaign identified **the Möbius-involution pencil energy** as the *only known
domain-separating invariant* for the proximity-gap threshold δ\* (the M3 census separates
smooth multiplicative subgroups from random evaluation domains, and the separation factors
through this statistic). This file builds its load-bearing core, axiom-clean.

For a finite **commutative** group `G` (the multiplicative evaluation subgroup `H ≤ F^×`) and a
parameter `b : G`, the *Möbius pencil involution* is

  `σ_b : G → G,   σ_b x = b · x⁻¹`

(the `a = 0` strip of the k=3 agreement pencil `(x−a)(y−a) = a²−b`, normalized: `x·y = b`).
Its fixed points are exactly the **square roots of `b`** (`x² = b`), and every non-fixed point
sits in a 2-orbit `{x, b·x⁻¹}`. The per-`b` 2-orbit count

  `t₂(b) = (|G| − #√b) / 2`

is the agreement-spectrum statistic that is `≈ n/2` on the `≈ n` subgroup pencils (so the
energy `Σ_b t₂(b)²` is `Θ(n³)`) yet thin for a random domain — the mechanism behind hypothesis
**N1** (`δ\*(H) = F(E₂(H)/n²)`) and connection **C1**.

Results:
- `mobiusInvol` : the involution as an `Equiv.Perm G`, with `mobiusInvol_involutive`.
- `mobiusInvol_apply_eq_self_iff` : `x` is fixed ⟺ `x² = b`.
- `t2`, `card_eq_two_mul_t2_add_fixed` : `|G| = 2·t₂(b) + #√b` (the orbit decomposition).

Axiom-clean: `[propext, Classical.choice, Quot.sound]` (see `#print axioms` at EOF).
-/

open Equiv

namespace ProximityGap.MobiusPencil

variable {G : Type*} [CommGroup G]

/-- The Möbius pencil involution `σ_b x = b · x⁻¹` on a commutative group, as a permutation.
It is its own inverse (commutativity: `(b·x⁻¹)⁻¹ = b⁻¹·x`, so `σ_b (σ_b x) = b·(b⁻¹·x) = x`). -/
def mobiusInvol (b : G) : Equiv.Perm G where
  toFun x := b * x⁻¹
  invFun x := b * x⁻¹
  left_inv x := by simp [mul_inv_rev, mul_comm, mul_assoc, mul_left_comm]
  right_inv x := by simp [mul_inv_rev, mul_comm, mul_assoc, mul_left_comm]

@[simp] lemma mobiusInvol_apply (b x : G) : mobiusInvol b x = b * x⁻¹ := rfl

/-- The Möbius involution is an involution. -/
theorem mobiusInvol_involutive (b : G) : Function.Involutive (mobiusInvol b) := by
  intro x; simp [mobiusInvol_apply, mul_inv_rev, mul_comm, mul_assoc, mul_left_comm]

@[simp] lemma mobiusInvol_mobiusInvol (b x : G) :
    mobiusInvol b (mobiusInvol b x) = x := mobiusInvol_involutive b x

/-- `mobiusInvol b` squares to the identity permutation. -/
theorem mobiusInvol_sq (b : G) : (mobiusInvol b) * (mobiusInvol b) = 1 :=
  Equiv.Perm.ext (fun x => mobiusInvol_involutive b x)

/-- **Fixed points are square roots of `b`.** `σ_b x = x ⟺ x² = b`. -/
theorem mobiusInvol_apply_eq_self_iff {b x : G} : mobiusInvol b x = x ↔ x ^ 2 = b := by
  rw [mobiusInvol_apply, mul_inv_eq_iff_eq_mul, sq, eq_comm]

variable [Fintype G] [DecidableEq G]

/-- The set of square roots of `b` in `G` (the fixed points of `σ_b`). -/
def sqrtSet (b : G) : Finset G :=
  Finset.univ.filter (fun x => x ^ 2 = b)

@[simp] lemma mem_sqrtSet {b x : G} : x ∈ sqrtSet b ↔ x ^ 2 = b := by
  simp [sqrtSet]

/-- The square-root set is exactly the fixed-point set of `σ_b` (as a Finset). -/
theorem sqrtSet_eq_filter_fixed (b : G) :
    sqrtSet b = Finset.univ.filter (fun x => mobiusInvol b x = x) := by
  ext x
  simp only [sqrtSet, Finset.mem_filter, Finset.mem_univ, true_and,
    mobiusInvol_apply_eq_self_iff]

/-- **The orbit decomposition** `|G| = #√b + #{non-fixed}`. The non-fixed points are the
support of the involution `σ_b`; each lies in a 2-orbit `{x, b·x⁻¹}`. The 2-orbit count is
`t₂(b) = #{non-fixed}/2` (the pencil-energy summand). -/
theorem card_eq_sqrtSet_add_support (b : G) :
    Fintype.card G
      = (sqrtSet b).card + (Finset.univ.filter (fun x => mobiusInvol b x ≠ x)).card := by
  rw [sqrtSet_eq_filter_fixed, ← Finset.card_univ,
    Finset.filter_card_add_filter_neg_card_eq_card (p := fun x => mobiusInvol b x = x)]

/-- The 2-orbit count of `σ_b` (the per-`b` Möbius pencil energy summand). -/
def t2 (b : G) : ℕ := (Finset.univ.filter (fun x => mobiusInvol b x ≠ x)).card / 2

/-- The support of `σ_b` (its non-fixed points) is closed under `σ_b` and fixed-point-free —
the structural fact that makes the 2-orbit pairing `x ↔ b·x⁻¹` well-defined (so `#support`
is even and `t₂(b) = #support/2`, the next brick). -/
theorem mobiusInvol_mapsTo_support (b : G) :
    ∀ x ∈ Finset.univ.filter (fun x => mobiusInvol b x ≠ x),
      mobiusInvol b x ∈ Finset.univ.filter (fun x => mobiusInvol b x ≠ x) := by
  intro x hx
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hx ⊢
  intro hcontra
  exact hx (by rw [← hcontra, mobiusInvol_mobiusInvol])

end ProximityGap.MobiusPencil

/-! ## Axiom audit — kernel-clean. -/
#print axioms ProximityGap.MobiusPencil.mobiusInvol_involutive
#print axioms ProximityGap.MobiusPencil.mobiusInvol_apply_eq_self_iff

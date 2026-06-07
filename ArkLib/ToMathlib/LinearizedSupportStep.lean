/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import Mathlib

/-!
# Frobenius support scaling (inductive engine for q-linearized support)

Over an extension `K` of a finite field `F` with `q = |F|`, the support of `f^q` is the
`q`-scaling of the support of `f`:

* `support_expand_eq` — char-free: `(expand K q f).support = q · (support f)`.
* `support_pow_card` — `(f^q).support = q · (support f)`, via the finite-field freshman's dream
  `f^q = map (iterateFrobenius) (expand q f)` (`map_iterateFrobenius_expand`).

This is the inductive step for the q-linearized support theorem: if `support f ⊆ {q^i}` then
`support (f^q) = q · support f ⊆ {q^{i+1}}`, so the linearized-binomial recursion
`f ↦ f^q - C b · f` preserves support on the `q`-powers (the BKR06 list-size residual).
-/

open Polynomial BigOperators

namespace ArkLib.LinearizedKernel

variable {K : Type*} [Field K]

/-- Support of `expand` scales by `q`: `(expand K q f).support = (· * q) '' support f`. -/
theorem support_expand_eq {q : ℕ} (hq : 0 < q) (f : K[X]) :
    (expand K q f).support = f.support.image (· * q) := by
  classical
  ext m
  simp only [mem_support_iff, Finset.mem_image]
  rw [coeff_expand hq]
  constructor
  · intro hm
    by_cases hdvd : q ∣ m
    · rw [if_pos hdvd] at hm
      exact ⟨m / q, hm, Nat.div_mul_cancel hdvd⟩
    · rw [if_neg hdvd] at hm; exact absurd rfl hm
  · rintro ⟨k, hk, rfl⟩
    rw [if_pos (dvd_mul_left q k), Nat.mul_div_cancel _ hq]
    exact hk

variable {F : Type*} [Field F] [Fintype F] [Algebra F K]

/-- **Frobenius support scaling.** Over an extension `K` of a finite field `F` (`q = |F|`),
`(f^q).support = q · support f`.  Uses `f^q = map (iterateFrobenius) (expand q f)` (the
finite-field freshman's dream), that `map` by the injective iterated Frobenius preserves support,
and `support_expand_eq`. -/
theorem support_pow_card (f : K[X]) :
    (f ^ Fintype.card F).support = f.support.image (· * Fintype.card F) := by
  haveI : CharP F (ringChar F) := ringChar.charP F
  obtain ⟨n, hp, hcard⟩ := FiniteField.card F (ringChar F)
  haveI : Fact (ringChar F).Prime := ⟨hp⟩
  haveI : CharP K (ringChar F) :=
    charP_of_injective_algebraMap (algebraMap F K).injective (ringChar F)
  haveI : ExpChar K (ringChar F) := ExpChar.prime hp
  have hpos : 0 < (ringChar F) ^ (n : ℕ) := pow_pos hp.pos _
  rw [hcard, ← map_iterateFrobenius_expand (ringChar F) f (n : ℕ),
    support_map_of_injective _ (iterateFrobenius K (ringChar F) (n : ℕ)).injective,
    support_expand_eq hpos f]

end ArkLib.LinearizedKernel

-- Axiom audit.
#print axioms ArkLib.LinearizedKernel.support_expand_eq
#print axioms ArkLib.LinearizedKernel.support_pow_card

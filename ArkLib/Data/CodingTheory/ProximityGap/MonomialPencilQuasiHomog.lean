/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import Mathlib.Algebra.Ring.Basic
import Mathlib.Tactic

/-!
# Monomial-pencil μ_d-quasi-homogeneity (#407 — coset-saturation piece (2) structural core)

The Kambiré δ* optimality reduces (piece (2), "coset-saturation") to: for a MONOMIAL pencil
`U = X^a + γ·X^b` on `μ_n`, beyond Johnson, every large agreement set is a union of `μ_d`-cosets,
`d = gcd(a−b, n)`.  This file proves the elementary STRUCTURAL CORE:

> **`monomialPencil_quasi_homogeneous`** — if `ω^(a−b) = 1` (e.g. `ω ∈ μ_d`, `d ∣ a−b`) then for all
> `x, γ`:  `(ω·x)^a + γ·(ω·x)^b = ω^a · (x^a + γ·x^b)`  (so `U(ωx) = ω^a U(x)`).

Consequence (composing with the proven `FactorizationRigidity`): `U − c_a` (`c_a` = the degree-`≡a (mod
d)` part of the codeword) is `d`-sparse, so its `μ_n`-roots are `μ_d`-coset-closed.  This reduces piece
(2) to a Johnson bound on the OFF-residue codeword part — replacing the analytic char-`p`/Gauss-sum wall
with combinatorics.  Verified `scripts/probes/probe_coset_sat_structure.py` (12/12, n=16,32,64). Axiom-clean.
-/

namespace ArkLib.ProximityGap.MonomialPencilQuasiHomog

/-- **Monomial-pencil μ_d-quasi-homogeneity.** If `ω^(a−b) = 1` (so `ω^a = ω^b`, e.g. `ω` a `d`-th root
of unity with `d ∣ a−b`), the monomial pencil `x ↦ x^a + γ·x^b` satisfies `U(ω·x) = ω^a · U(x)`. -/
theorem monomialPencil_quasi_homogeneous {R : Type*} [CommRing R] (a b : ℕ) (hab : b ≤ a)
    (ω x γ : R) (hω : ω ^ (a - b) = 1) :
    (ω * x) ^ a + γ * (ω * x) ^ b = ω ^ a * (x ^ a + γ * x ^ b) := by
  have hωab : ω ^ a = ω ^ b := by
    have h : ω ^ a = ω ^ (a - b) * ω ^ b := by
      rw [← pow_add]; congr 1; omega
    rw [h, hω, one_mul]
  rw [mul_pow, mul_pow, hωab]; ring

/-- The agreement condition `U = c` transports along the `μ_d`-orbit: `U(ωx) = ω^a · c(x)`, so
coset-closure of the agreement set is exactly `c(ωx) = ω^a c(x)` (the off-residue part of `c`). -/
theorem agreement_orbit_condition {R : Type*} [CommRing R] (a b : ℕ) (hab : b ≤ a)
    (ω x γ : R) (hω : ω ^ (a - b) = 1) (c : R) (hagree : x ^ a + γ * x ^ b = c) :
    (ω * x) ^ a + γ * (ω * x) ^ b = ω ^ a * c := by
  rw [monomialPencil_quasi_homogeneous a b hab ω x γ hω, hagree]

end ArkLib.ProximityGap.MonomialPencilQuasiHomog

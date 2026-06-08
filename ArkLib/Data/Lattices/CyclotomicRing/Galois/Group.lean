/-
Copyright (c) 2024-2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tobias Rothmann
-/
import ArkLib.Data.Lattices.CyclotomicRing.Galois.Automorphism

/-!
# The Galois Group and the Subgroup `H = ⟨σ_{-1}, σ_{4k+1}⟩`

The Galois automorphisms `σ_i` of `R_q = Z_q[X] / (X^{2^α} + 1)` form a group isomorphic to
`(Z / 2^{α+1})ˣ` via `σ_i ∘ σ_j = σ_{ij}` and `σ_1 = id`. Hachi [NOZ26, §3] works with the
subgroup `H := ⟨σ_{-1}, σ_{4k+1}⟩`, whose fixed subring is the subfield `≅ F_{q^k}`.

This file pins the two generators (`σ_{-1}` with exponent `2^{α+1}-1 ≡ -1`, and `σ_{4k+1}`),
records their oddness (so they are genuine automorphisms), and provides the explicit exponent
set `Hexp` enumerating `H` for use by the trace map. The composition law `σ_i ∘ σ_j = σ_{ij}`
(for odd `i, j`) and `σ_1 = id` are proven via the soundness bridge; the order computation
`|⟨4k+1⟩| = d/(2k)` (Hachi [NOZ26, §3, Claim 1] / [LS18, Lem 2.4]) remains sorried (number
theory).

## Main definitions

* `conjExp α` / `genExp k` — the exponents `2^{α+1}-1` (`σ_{-1}`) and `4k+1` (`σ_{4k+1}`).
* `conjAut α` / `genAut α k` — the two generating automorphisms as `RingHom`s.
* `Hexp α k` — the exponent set enumerating `H = ⟨σ_{-1}, σ_{4k+1}⟩`.

## References

* [Lyubashevsky, V., and Seiler, G., *Short, Invertible Elements …*][LS18]
* [Nguyen, N. K., O'Rourke, G., and Zhang, J., *Hachi …*][NOZ26]
-/

open Polynomial CompPoly Finset

namespace ArkLib.Lattices.CyclotomicModulus

variable {R : Type*} [Field R] [BEq R] [LawfulBEq R] [DecidableEq R]

/-! ## Generators of `H` and their exponents -/

/-- The exponent of the conjugation automorphism `σ_{-1}`: `2^{α+1} - 1 ≡ -1 (mod 2^{α+1})`. -/
def conjExp (α : ℕ) : ℕ := 2 ^ (α + 1) - 1

/-- The exponent of the second generator `σ_{4k+1}`. -/
def genExp (k : ℕ) : ℕ := 4 * k + 1

theorem genExp_odd (k : ℕ) : Odd (genExp k) := ⟨2 * k, by unfold genExp; ring⟩

theorem conjExp_odd (α : ℕ) : Odd (conjExp α) := by
  have h : 1 ≤ 2 ^ α := Nat.one_le_two_pow
  refine ⟨2 ^ α - 1, ?_⟩
  unfold conjExp
  rw [pow_succ]; omega

/-- The conjugation automorphism `σ_{-1} : X ↦ X^{-1}`, as a `RingHom`. -/
noncomputable def conjAut (α : ℕ) :
    Rq (powTwoCyclotomic (R := R) α) →+* Rq (powTwoCyclotomic (R := R) α) :=
  galoisRingHom α (conjExp α) (conjExp_odd α)

/-- The second generator `σ_{4k+1}`, as a `RingHom`. -/
noncomputable def genAut (α k : ℕ) :
    Rq (powTwoCyclotomic (R := R) α) →+* Rq (powTwoCyclotomic (R := R) α) :=
  galoisRingHom α (genExp k) (genExp_odd k)

/-! ## Group laws (number-theoretic core sorried) -/

/-- `σ_1 = id`: substituting `X ↦ X^1` is the identity. Proven via the soundness bridge, since
`aeval X` is the identity on `Polynomial R`. -/
theorem galoisAut_one_eq (α : ℕ) (a : Rq (powTwoCyclotomic (R := R) α)) :
    galoisAut (powTwoCyclotomic α) 1 a = a := by
  apply Rq.toQuotient_injective (powTwoCyclotomic α)
  rw [galoisAut_toQuotient α 1 odd_one, galoisAutₛ_toQuotient α 1 odd_one, pow_one,
    Polynomial.aeval_X_left_apply, Rq.toQuotient, quotientHom_apply]

/-- Composition law `σ_i ∘ σ_j = σ_{ij}` (for `i, j` odd, so the maps are genuine
automorphisms). Proven on the semantic `aeval` side via the soundness bridge
`galoisAut_toQuotient` and `aeval_X_pow_aeval_X_pow`. -/
theorem galoisAut_comp (α i j : ℕ) (hi : Odd i) (hj : Odd j)
    (a : Rq (powTwoCyclotomic (R := R) α)) :
    galoisAut (powTwoCyclotomic α) i (galoisAut (powTwoCyclotomic α) j a)
      = galoisAut (powTwoCyclotomic α) (i * j) a := by
  apply Rq.toQuotient_injective (powTwoCyclotomic α)
  rw [galoisAut_toQuotient α i hi, galoisAut_toQuotient α j hj,
    galoisAut_toQuotient α (i * j) (hi.mul hj), galoisAutₛ_toQuotient α j hj, galoisAutₛ_mk,
    galoisAutₛ_toQuotient α (i * j) (hi.mul hj), aeval_X_pow_aeval_X_pow]

/-! ## 2-adic order kernel for `4k+1`

These two lemmas are the number-theoretic heart of the `Hexp` / `traceH_mem_fixed` story:
`4k+1 = 1 + 2^{κ+2}` has 2-adic order dividing `2^α/(2k)` in `(ℤ/2^{α+1})ˣ`, so its `±`-orbit
`Hexp` is closed under multiplication by `4k+1`. Proven by an elementary `(A-1)(A+1)` induction
(no lifting-the-exponent needed for the divisibility direction). -/

/-- **2-adic divisibility.** For `m ≥ 1`, `2^{m+j} ∣ (1 + 2^m)^{2^j} - 1`. -/
theorem two_pow_dvd_one_add_two_pow_pow (m j : ℕ) (hm : 1 ≤ m) :
    (2 ^ (m + j) : ℤ) ∣ (1 + 2 ^ m) ^ (2 ^ j) - 1 := by
  induction j with
  | zero => simp only [pow_zero, pow_one, add_zero, add_sub_cancel_left]; exact dvd_rfl
  | succ j ih =>
    have hodd : Odd ((1 + 2 ^ m : ℤ) ^ (2 ^ j)) := by
      apply Odd.pow
      have : Even ((2 : ℤ) ^ m) := by rw [Int.even_pow]; exact ⟨even_two, by omega⟩
      simpa [add_comm] using this.add_one
    have h2 : (2 : ℤ) ∣ (1 + 2 ^ m) ^ (2 ^ j) + 1 := by
      obtain ⟨t, ht⟩ := hodd; exact ⟨t + 1, by rw [ht]; ring⟩
    have key : (1 + 2 ^ m : ℤ) ^ (2 ^ (j + 1)) - 1
        = ((1 + 2 ^ m) ^ (2 ^ j) - 1) * ((1 + 2 ^ m) ^ (2 ^ j) + 1) := by
      rw [pow_succ, pow_mul]; ring
    rw [key, show m + (j + 1) = (m + j) + 1 from by ring, pow_succ]
    exact mul_dvd_mul ih h2

/-- **Order divides.** For `k = 2^κ` with `2k ∣ 2^α`, the 2-adic order of `4k+1` divides
`2^α/(2k)`: `2^{α+1} ∣ (4k+1)^{2^α/(2k)} - 1`. This is exactly the wrap-around fact that makes
`Hexp` closed under multiplication by `4k+1` mod `2^{α+1}`. -/
theorem two_pow_succ_dvd_four_mul_add_one_pow (α k κ : ℕ)
    (hk : k = 2 ^ κ) (hκ : κ + 1 ≤ α) :
    (2 ^ (α + 1) : ℤ) ∣ (4 * k + 1) ^ (2 ^ α / (2 * k)) - 1 := by
  subst hk
  have hexp : 2 ^ α / (2 * 2 ^ κ) = 2 ^ (α - (κ + 1)) := by
    rw [show 2 * 2 ^ κ = 2 ^ (κ + 1) from by rw [pow_succ]; ring,
      Nat.pow_div (by omega) (by norm_num)]
  rw [hexp]
  push_cast
  rw [show (4 * (2 : ℤ) ^ κ + 1) = 1 + 2 ^ (κ + 2) from by rw [pow_add]; ring]
  have h := two_pow_dvd_one_add_two_pow_pow (κ + 2) (α - (κ + 1)) (by omega)
  rwa [show (κ + 2) + (α - (κ + 1)) = α + 1 from by omega] at h

/-! ## The subgroup `H` as an exponent set -/

/-- The exponent set enumerating `H = ⟨σ_{-1}, σ_{4k+1}⟩` inside `(Z / 2^{α+1})ˣ`:
`{ ±(4k+1)^a mod 2^{α+1} : 0 ≤ a < d/(2k) }`. The trace map sums the automorphisms over this
set. -/
def Hexp (α k : ℕ) : Finset ℕ :=
  (Finset.range (2 ^ α / (2 * k))).biUnion fun a =>
    {(4 * k + 1) ^ a % 2 ^ (α + 1),
      (2 ^ (α + 1) - (4 * k + 1) ^ a % 2 ^ (α + 1)) % 2 ^ (α + 1)}

/-- `|H| = d/k = 2^α / k` (Hachi [NOZ26, §3], from `|⟨4k+1⟩| = d/(2k)` and the `±` factor).

The hypotheses match Hachi [NOZ26, §3, Claim 1] / [LS18, Lem 2.4]: `k` is a power of two
(`hk2pow`) and divides `d/2`, i.e. `2k ∣ d = 2^α` (`hk`). Both are needed for `4k+1` to have
order exactly `d/(2k)` in `(Z/2^{α+1})ˣ`; the weaker `k ∣ 2^α` (= `k ∣ d`) does not suffice
(e.g. `k = 2^α` gives `2k ∤ d`, so `2^α/(2k)` is not the true order).

DEFERRED (rated 8): order of `4k+1` in `(Z/2^{α+1})ˣ` plus injectivity of the enumeration. -/
theorem Hexp_card (α k : ℕ) (hk2pow : ∃ κ, k = 2 ^ κ) (hk : 2 * k ∣ 2 ^ α) :
    (Hexp α k).card = 2 ^ α / k := by
  sorry

end ArkLib.Lattices.CyclotomicModulus

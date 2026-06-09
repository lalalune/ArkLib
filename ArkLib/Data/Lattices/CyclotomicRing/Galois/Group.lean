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

/-! ## Periodicity of the Galois action in the exponent (mod `2^{α+1}`) -/

/-- In the cyclotomic quotient, `X^i = X^{i mod 2^{α+1}}`, since `X^{2^{α+1}} = 1`
(`(X^{2^α})² = (−1)² = 1`). -/
theorem mkX_pow_periodic (α i : ℕ) :
    (Ideal.Quotient.mk (powTwoCyclotomic (R := R) α).modIdeal) (Polynomial.X ^ i)
      = Ideal.Quotient.mk _ (Polynomial.X ^ (i % 2 ^ (α + 1))) := by
  set i' := i % 2 ^ (α + 1) with hi'
  rw [Ideal.Quotient.eq]
  have hsplit : i = 2 ^ (α + 1) * (i / 2 ^ (α + 1)) + i' := by
    rw [hi']; exact (Nat.div_add_mod i (2 ^ (α + 1))).symm
  rw [hsplit, pow_add, pow_mul, ← sub_one_mul]
  simp only [modIdeal, powTwoCyclotomic_toPoly, Ideal.mem_span_singleton]
  refine Dvd.dvd.mul_right ?_ _
  have h1 : (Polynomial.X ^ 2 ^ α + 1 : Polynomial R) ∣ Polynomial.X ^ 2 ^ (α + 1) - 1 := by
    have he : (Polynomial.X ^ 2 ^ (α + 1) - 1 : Polynomial R)
        = (Polynomial.X ^ 2 ^ α - 1) * (Polynomial.X ^ 2 ^ α + 1) := by
      rw [show 2 ^ (α + 1) = 2 ^ α * 2 from by rw [pow_succ], pow_mul]; ring
    rw [he]; exact Dvd.intro_left _ rfl
  have h2 : (Polynomial.X ^ 2 ^ (α + 1) - 1 : Polynomial R)
      ∣ (Polynomial.X ^ 2 ^ (α + 1)) ^ (i / 2 ^ (α + 1)) - 1 := by
    simpa using sub_dvd_pow_sub_pow (Polynomial.X ^ 2 ^ (α + 1) : Polynomial R) 1 (i / 2 ^ (α + 1))
  exact h1.trans h2

/-- **The Galois automorphism `σ_i` depends only on `i mod 2^{α+1}`.** Since `X` has order
`2^{α+1}` in the cyclotomic quotient, `σ_i = σ_{i mod 2^{α+1}}`. -/
theorem galoisAut_periodic (α i : ℕ) (hi : Odd i) (a : Rq (powTwoCyclotomic (R := R) α)) :
    galoisAut (powTwoCyclotomic α) i a
      = galoisAut (powTwoCyclotomic α) (i % 2 ^ (α + 1)) a := by
  have hi' : Odd (i % 2 ^ (α + 1)) := by
    rw [Nat.odd_iff, Nat.mod_mod_of_dvd i (dvd_pow_self 2 (Nat.succ_ne_zero α))]
    exact Nat.odd_iff.mp hi
  apply Rq.toQuotient_injective
  rw [galoisAut_toQuotient α i hi, galoisAut_toQuotient α (i % 2 ^ (α + 1)) hi',
    galoisAutₛ_toQuotient α i hi, galoisAutₛ_toQuotient α (i % 2 ^ (α + 1)) hi',
    Polynomial.aeval_def, Polynomial.aeval_def, Polynomial.algebraMap_eq,
    Polynomial.hom_eval₂, Polynomial.hom_eval₂, mkX_pow_periodic]

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

/-- **Exact 2-adic valuation.** `(1+2^m)^{2^j} ≡ 1 + 2^{m+j} (mod 2^{m+j+1})` for `m ≥ 2`:
the term `2^{m+j}` is exactly the next bit, giving both `2^{m+j} ∣ ((1+2^m)^{2^j}-1)` and its
sharpness (`2^{m+j+1} ∤`). Proven by an explicit-witness `(A-1)(A+1)` induction. -/
theorem one_add_two_pow_pow_exact (m j : ℕ) (hm : 2 ≤ m) :
    ∃ c, (1 + 2 ^ m) ^ (2 ^ j) = 1 + 2 ^ (m + j) + 2 ^ (m + j + 1) * c := by
  induction j with
  | zero => exact ⟨0, by ring⟩
  | succ j ih =>
    obtain ⟨c, hc⟩ := ih
    obtain ⟨d, hd⟩ : ∃ d, m + j = d + 2 := ⟨m + j - 2, by omega⟩
    refine ⟨c + 2 ^ d * (1 + 2 * c) ^ 2, ?_⟩
    have e : (1 + 2 ^ m) ^ 2 ^ (j + 1) = ((1 + 2 ^ m) ^ 2 ^ j) ^ 2 := by rw [pow_succ, pow_mul]
    rw [e, hc, hd, show m + (j + 1) = d + 3 from by omega, show d + 2 + 1 = d + 3 from by ring]
    simp only [pow_add]; ring

/-- **Order does not divide a half-step.** For `k = 2^κ` with `2k ∣ 2^α`, the 2-adic order of
`4k+1` does NOT divide `2^α/(4k)`: `(4k+1)^{2^α/(4k)} ≢ 1 (mod 2^{α+1})`. With the order-divides
fact, this pins the order to exactly `2^α/(2k)`. -/
theorem four_mul_add_one_pow_half_ord_mod (α k κ : ℕ) (hk : k = 2 ^ κ) (hκ : κ + 2 ≤ α) :
    (4 * k + 1) ^ (2 ^ (α - κ - 2)) % 2 ^ (α + 1) ≠ 1 := by
  subst hk
  obtain ⟨c, hc⟩ := one_add_two_pow_pow_exact (κ + 2) (α - κ - 2) (by omega)
  have hbase : (4 * 2 ^ κ + 1 : ℕ) = 1 + 2 ^ (κ + 2) := by rw [pow_add]; ring
  rw [hbase, hc]
  have hE1 : (2 : ℕ) ^ (α + 1) = 2 ^ ((κ + 2) + (α - κ - 2) + 1) := by congr 1; omega
  have hEpos : 1 < (2 : ℕ) ^ ((κ + 2) + (α - κ - 2)) := Nat.one_lt_pow (by omega) (by norm_num)
  rw [hE1, Nat.add_mul_mod_self_left,
    Nat.mod_eq_of_lt (by rw [pow_succ]; omega)]
  omega

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

/-- The natural-number form: `(4k+1)^{2^α/(2k)} ≡ 1 (mod 2^{α+1})`. The orbit-wrap-around fact
that closes `Hexp` under multiplication by `4k+1`. -/
theorem four_mul_add_one_pow_ord_mod (α k κ : ℕ) (hk : k = 2 ^ κ) (hκ : κ + 1 ≤ α) :
    (4 * k + 1) ^ (2 ^ α / (2 * k)) % 2 ^ (α + 1) = 1 := by
  have hZ := two_pow_succ_dvd_four_mul_add_one_pow α k κ hk hκ
  have hmod : ((4 * k + 1) ^ (2 ^ α / (2 * k)) : ℕ) ≡ 1 [MOD 2 ^ (α + 1)] := by
    rw [Nat.modEq_iff_dvd]
    have hd : ((2 ^ (α + 1) : ℕ) : ℤ) ∣
        ((1 : ℕ) : ℤ) - ((4 * k + 1) ^ (2 ^ α / (2 * k)) : ℕ) := by
      push_cast; simpa using (dvd_neg.mpr hZ)
    exact_mod_cast hd
  have hlt : 1 < 2 ^ (α + 1) := Nat.one_lt_pow (by omega) (by norm_num)
  rw [Nat.ModEq, Nat.one_mod_eq_one.mpr (by omega)] at hmod
  exact hmod

/-- **Injectivity of the `+`-orbit enumeration.** The map `a ↦ (4·2^κ+1)^a mod 2^{α+1}` is
injective on `[0, 2^α/(2·2^κ)) = [0, 2^{α-κ-1})`: the multiplicative order of `4·2^κ+1` in
`(ℤ/2^{α+1})ˣ` is *exactly* `2^{α-κ-1}` (order-divides via `four_mul_add_one_pow_ord_mod`,
half-order non-vanishing via `four_mul_add_one_pow_half_ord_mod`, pinned by
`orderOf_eq_prime_pow`), so distinct exponents in that range give distinct residues. -/
theorem four_mul_add_one_pow_inj (α κ a a' : ℕ) (hκα : κ + 1 ≤ α)
    (ha : a < 2 ^ (α - κ - 1)) (ha' : a' < 2 ^ (α - κ - 1))
    (h : (4 * 2 ^ κ + 1) ^ a % 2 ^ (α + 1) = (4 * 2 ^ κ + 1) ^ a' % 2 ^ (α + 1)) :
    a = a' := by
  rcases Nat.lt_or_ge (α - κ - 1) 1 with h0 | h1
  · -- `α - κ - 1 = 0`, so the range is `[0,1)` and `a = a' = 0`
    have hz : α - κ - 1 = 0 := by omega
    rw [hz, pow_zero] at ha ha'; omega
  · -- `α ≥ κ + 2`: run the exact-order argument
    have hκα2 : κ + 2 ≤ α := by omega
    have hM1 : (1 : ℕ) < 2 ^ (α + 1) := Nat.one_lt_pow (by omega) (by norm_num)
    haveI : NeZero (2 ^ (α + 1)) := ⟨by positivity⟩
    haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    have hg_odd : Odd (4 * 2 ^ κ + 1) := ⟨2 * 2 ^ κ, by ring⟩
    have hcop : Nat.Coprime (4 * 2 ^ κ + 1) (2 ^ (α + 1)) :=
      (Nat.coprime_pow_right_iff (by omega) _ _).mpr
        (Nat.coprime_comm.mp ((Nat.prime_two.coprime_iff_not_dvd).mpr
          (Nat.two_dvd_ne_zero.mpr (Nat.odd_iff.mp hg_odd))))
    -- the unit `u = 4·2^κ+1` in `(ℤ/2^{α+1})ˣ`
    set u : (ZMod (2 ^ (α + 1)))ˣ := ZMod.unitOfCoprime (4 * 2 ^ κ + 1) hcop with hu
    have hu_coe : (u : ZMod (2 ^ (α + 1))) = ((4 * 2 ^ κ + 1 : ℕ) : ZMod (2 ^ (α + 1))) :=
      ZMod.coe_unitOfCoprime _ _
    have hpow_iff : ∀ n : ℕ, u ^ n = 1 ↔ (4 * 2 ^ κ + 1) ^ n % 2 ^ (α + 1) = 1 := by
      intro n
      rw [← Units.val_eq_one, Units.val_pow_eq_pow_val, hu_coe, ← Nat.cast_pow,
        ← Nat.cast_one (R := ZMod (2 ^ (α + 1))), ZMod.natCast_eq_natCast_iff, Nat.ModEq,
        Nat.one_mod_eq_one.mpr (by omega)]
    -- `2^α/(2·2^κ) = 2^{α-κ-1}`
    have he : 2 ^ α / (2 * 2 ^ κ) = 2 ^ (α - κ - 1) := by
      rw [show (2 : ℕ) * 2 ^ κ = 2 ^ (κ + 1) from by rw [pow_succ]; ring,
        Nat.pow_div (by omega) (by norm_num), show α - (κ + 1) = α - κ - 1 from by omega]
    have hdiv : u ^ (2 ^ (α - κ - 1)) = 1 := by
      rw [hpow_iff, ← he]; exact four_mul_add_one_pow_ord_mod α (2 ^ κ) κ rfl hκα
    have hhalf : u ^ (2 ^ (α - κ - 2)) ≠ 1 := by
      rw [ne_eq, hpow_iff]; exact four_mul_add_one_pow_half_ord_mod α (2 ^ κ) κ rfl hκα2
    have horderOf : orderOf u = 2 ^ (α - κ - 1) := by
      have key := orderOf_eq_prime_pow (p := 2) (n := α - κ - 2) hhalf
        (by rwa [show α - κ - 2 + 1 = α - κ - 1 from by omega])
      rwa [show α - κ - 2 + 1 = α - κ - 1 from by omega] at key
    -- transport the residue equality `h` to `u^a = u^a'`, then use injectivity below order
    have huu : u ^ a = u ^ a' := by
      apply Units.ext
      rw [Units.val_pow_eq_pow_val, Units.val_pow_eq_pow_val, hu_coe, ← Nat.cast_pow,
        ← Nat.cast_pow, ZMod.natCast_eq_natCast_iff]
      exact h
    have hmod : a ≡ a' [MOD orderOf u] := pow_eq_pow_iff_modEq.mp huu
    rw [horderOf, Nat.ModEq, Nat.mod_eq_of_lt ha, Nat.mod_eq_of_lt ha'] at hmod
    exact hmod

/-- Modular periodicity of powers: if `p^ord ≡ 1 (mod M)` then `p^n ≡ p^{n mod ord} (mod M)`. -/
theorem pow_mod_period (p ord M n : ℕ) (h1 : p ^ ord % M = 1) (hM : 1 < M) :
    p ^ n % M = p ^ (n % ord) % M := by
  conv_lhs => rw [← Nat.div_add_mod n ord]
  rw [pow_add, pow_mul, Nat.mul_mod, Nat.pow_mod, h1, one_pow,
    Nat.one_mod_eq_one.mpr (by omega), one_mul, Nat.mod_mod]

/-- Multiplication by an odd `j` is injective mod `2^{α+1}` on residues. -/
theorem mul_mod_inj (α j x y : ℕ) (hj : Odd j) (hx : x < 2 ^ (α + 1)) (hy : y < 2 ^ (α + 1))
    (h : j * x % 2 ^ (α + 1) = j * y % 2 ^ (α + 1)) : x = y := by
  have hcop2 : Nat.Coprime j 2 :=
    Nat.coprime_comm.mp ((Nat.prime_two.coprime_iff_not_dvd).mpr
      (Nat.two_dvd_ne_zero.mpr (Nat.odd_iff.mp hj)))
  have hcop : Nat.Coprime j (2 ^ (α + 1)) := (Nat.coprime_pow_right_iff (by omega) j 2).mpr hcop2
  have hgcd : Nat.gcd (2 ^ (α + 1)) j = 1 := by rw [Nat.gcd_comm]; exact hcop
  have hmod : x ≡ y [MOD 2 ^ (α + 1)] := Nat.ModEq.cancel_left_of_coprime hgcd h
  rwa [Nat.ModEq, Nat.mod_eq_of_lt hx, Nat.mod_eq_of_lt hy] at hmod

/-- Multiplication distributes over modular negation: `j·(M−z) ≡ −(j·z) (mod M)`. -/
theorem mul_sub_mod (j z M : ℕ) (hM : 0 < M) (hz : z ≤ M) :
    j * (M - z) % M = (M - j * z % M) % M := by
  have hcast : ((j * (M - z) : ℕ) : ZMod M) = ((M - j * z % M : ℕ) : ZMod M) := by
    rw [Nat.cast_mul, Nat.cast_sub hz, Nat.cast_sub (Nat.mod_lt _ hM).le]
    push_cast [ZMod.natCast_self, ZMod.natCast_mod]; ring
  exact (ZMod.natCast_eq_natCast_iff _ _ _).mp hcast

/-! ## The subgroup `H` as an exponent set -/

/-- The exponent set enumerating `H = ⟨σ_{-1}, σ_{4k+1}⟩` inside `(Z / 2^{α+1})ˣ`:
`{ ±(4k+1)^a mod 2^{α+1} : 0 ≤ a < d/(2k) }`. The trace map sums the automorphisms over this
set. -/
def Hexp (α k : ℕ) : Finset ℕ :=
  (Finset.range (2 ^ α / (2 * k))).biUnion fun a =>
    {(4 * k + 1) ^ a % 2 ^ (α + 1),
      (2 ^ (α + 1) - (4 * k + 1) ^ a % 2 ^ (α + 1)) % 2 ^ (α + 1)}

/-- Every exponent in `Hexp` is odd (`±` an odd power of the odd `4k+1`). -/
theorem Hexp_odd (α k i : ℕ) (hi : i ∈ Hexp α k) : Odd i := by
  simp only [Hexp, Finset.mem_biUnion, Finset.mem_insert, Finset.mem_singleton] at hi
  obtain ⟨a, -, ha⟩ := hi
  have hp : Odd ((4 * k + 1) ^ a) := Odd.pow ⟨2 * k, by ring⟩
  have hM : (2 : ℕ) ∣ 2 ^ (α + 1) := dvd_pow_self 2 (by omega)
  have hx : (4 * k + 1) ^ a % 2 ^ (α + 1) % 2 = 1 := by
    rw [Nat.mod_mod_of_dvd _ hM]; exact Nat.odd_iff.mp hp
  rcases ha with rfl | rfl
  · exact Nat.odd_iff.mpr hx
  · rw [Nat.odd_iff]
    have hpos : 0 < (4 * k + 1) ^ a % 2 ^ (α + 1) := by
      rcases Nat.eq_zero_or_pos ((4 * k + 1) ^ a % 2 ^ (α + 1)) with h | h
      · rw [h] at hx; simp at hx
      · exact h
    rw [Nat.mod_eq_of_lt (by omega : 2 ^ (α + 1) - (4 * k + 1) ^ a % 2 ^ (α + 1) < 2 ^ (α + 1))]
    omega

/-- Every exponent in `Hexp` is a residue `< 2^{α+1}`. -/
theorem Hexp_lt (α k i : ℕ) (hi : i ∈ Hexp α k) : i < 2 ^ (α + 1) := by
  simp only [Hexp, Finset.mem_biUnion, Finset.mem_insert, Finset.mem_singleton] at hi
  obtain ⟨a, -, ha⟩ := hi
  rcases ha with rfl | rfl <;> exact Nat.mod_lt _ (by positivity)

/-- **`Hexp` is closed under multiplication by `4k+1` mod `2^{α+1}`.** `σ_{4k+1}` cyclically
shifts each `±`-orbit by one (`a ↦ (a+1) mod ord`), wrapping via
`four_mul_add_one_pow_ord_mod`. -/
theorem Hexp_image_gen (α k κ : ℕ) (hk : k = 2 ^ κ) (hκ : κ + 1 ≤ α) :
    (Hexp α k).image (fun i => (4 * k + 1) * i % 2 ^ (α + 1)) = Hexp α k := by
  have hord1 : (4 * k + 1) ^ (2 ^ α / (2 * k)) % 2 ^ (α + 1) = 1 :=
    four_mul_add_one_pow_ord_mod α k κ hk hκ
  have hMlt : 1 < 2 ^ (α + 1) := Nat.one_lt_pow (by omega) (by norm_num)
  have hMpos : 0 < 2 ^ (α + 1) := by positivity
  have hordpos : 0 < 2 ^ α / (2 * k) := by
    subst hk
    rw [show 2 * 2 ^ κ = 2 ^ (κ + 1) from by rw [pow_succ]; ring, Nat.pow_div (by omega) (by norm_num)]
    positivity
  refine Finset.eq_of_subset_of_card_le ?_ ?_
  · intro y hy
    simp only [Finset.mem_image] at hy
    obtain ⟨i, hi, rfl⟩ := hy
    simp only [Hexp, Finset.mem_biUnion, Finset.mem_insert, Finset.mem_singleton,
      Finset.mem_range] at hi ⊢
    obtain ⟨a, ha, hia⟩ := hi
    have hpos : (4 * k + 1) * ((4 * k + 1) ^ a % 2 ^ (α + 1)) % 2 ^ (α + 1)
        = (4 * k + 1) ^ ((a + 1) % (2 ^ α / (2 * k))) % 2 ^ (α + 1) := by
      have h := (Nat.mod_modEq ((4 * k + 1) ^ a) (2 ^ (α + 1))).mul_left (4 * k + 1)
      rw [Nat.ModEq] at h
      rw [h, ← pow_succ', pow_mod_period _ _ _ (a + 1) hord1 hMlt]
    refine ⟨(a + 1) % (2 ^ α / (2 * k)), Nat.mod_lt _ hordpos, ?_⟩
    rcases hia with rfl | rfl
    · left; exact hpos
    · right
      have hz : (4 * k + 1) ^ a % 2 ^ (α + 1) ≤ 2 ^ (α + 1) := (Nat.mod_lt _ hMpos).le
      have e1 : (4 * k + 1) * ((2 ^ (α + 1) - (4 * k + 1) ^ a % 2 ^ (α + 1)) % 2 ^ (α + 1))
            % 2 ^ (α + 1)
          = (4 * k + 1) * (2 ^ (α + 1) - (4 * k + 1) ^ a % 2 ^ (α + 1)) % 2 ^ (α + 1) := by
        have h := (Nat.mod_modEq (2 ^ (α + 1) - (4 * k + 1) ^ a % 2 ^ (α + 1)) (2 ^ (α + 1))).mul_left
          (4 * k + 1)
        rwa [Nat.ModEq] at h
      rw [e1, mul_sub_mod _ _ _ hMpos hz, hpos]
  · rw [Finset.card_image_of_injOn]
    intro x hx y hy hxy
    exact mul_mod_inj α (4 * k + 1) x y ⟨2 * k, by ring⟩
      (Hexp_lt α k x (Finset.mem_coe.mp hx)) (Hexp_lt α k y (Finset.mem_coe.mp hy)) hxy

/-- **`Hexp` is closed under multiplication by `2^{α+1}−1 ≡ −1` mod `2^{α+1}`.** `σ_{−1}` swaps
the two `±` halves of each orbit cell, fixing the cell index. -/
theorem Hexp_image_conj (α k : ℕ) :
    (Hexp α k).image (fun i => (2 ^ (α + 1) - 1) * i % 2 ^ (α + 1)) = Hexp α k := by
  have hMpos : 0 < 2 ^ (α + 1) := by positivity
  refine Finset.eq_of_subset_of_card_le ?_ ?_
  · intro y hy
    simp only [Finset.mem_image] at hy
    obtain ⟨i, hi, rfl⟩ := hy
    simp only [Hexp, Finset.mem_biUnion, Finset.mem_insert, Finset.mem_singleton,
      Finset.mem_range] at hi ⊢
    obtain ⟨a, ha, hia⟩ := hi
    have hpapos : 0 < (4 * k + 1) ^ a % 2 ^ (α + 1) := by
      have hp : Odd ((4 * k + 1) ^ a) := Odd.pow ⟨2 * k, by ring⟩
      rcases Nat.eq_zero_or_pos ((4 * k + 1) ^ a % 2 ^ (α + 1)) with h | h
      · have hd : (2 : ℕ) ∣ 2 ^ (α + 1) := dvd_pow_self 2 (by omega)
        rw [Nat.odd_iff, ← Nat.mod_mod_of_dvd _ hd, h] at hp; simp at hp
      · exact h
    have hlt : (4 * k + 1) ^ a % 2 ^ (α + 1) < 2 ^ (α + 1) := Nat.mod_lt _ hMpos
    refine ⟨a, ha, ?_⟩
    rcases hia with rfl | rfl
    · right
      rw [mul_comm, mul_sub_mod _ _ _ hMpos (by omega), mul_one, Nat.mod_mod]
    · left
      rw [Nat.mod_eq_of_lt (by omega : 2 ^ (α + 1) - (4 * k + 1) ^ a % 2 ^ (α + 1) < 2 ^ (α + 1)),
        mul_comm, mul_sub_mod _ _ _ hMpos (by omega), mul_one,
        Nat.mod_eq_of_lt (by omega : 2 ^ (α + 1) - (4 * k + 1) ^ a % 2 ^ (α + 1) < 2 ^ (α + 1)),
        Nat.sub_sub_self (le_of_lt hlt), Nat.mod_eq_of_lt hlt]
  · rw [Finset.card_image_of_injOn]
    intro x hx y hy hxy
    have hodd : Odd (2 ^ (α + 1) - 1) := by
      have : 1 ≤ 2 ^ (α + 1) := Nat.one_le_two_pow
      refine ⟨2 ^ α - 1, ?_⟩; rw [pow_succ]; omega
    exact mul_mod_inj α (2 ^ (α + 1) - 1) x y hodd
      (Hexp_lt α k x (Finset.mem_coe.mp hx)) (Hexp_lt α k y (Finset.mem_coe.mp hy)) hxy

/-- `|H| = d/k = 2^α / k` (Hachi [NOZ26, §3], from `|⟨4k+1⟩| = d/(2k)` and the `±` factor).

The hypotheses match Hachi [NOZ26, §3, Claim 1] / [LS18, Lem 2.4]: `k` is a power of two
(`hk2pow`) and divides `d/2`, i.e. `2k ∣ d = 2^α` (`hk`). Both are needed for `4k+1` to have
order exactly `d/(2k)` in `(Z/2^{α+1})ˣ`; the weaker `k ∣ 2^α` (= `k ∣ d`) does not suffice
(e.g. `k = 2^α` gives `2k ∤ d`, so `2^α/(2k)` is not the true order).

DEFERRED (rated 8): order of `4k+1` in `(Z/2^{α+1})ˣ` plus injectivity of the enumeration. -/
theorem Hexp_card (α k : ℕ) (hk2pow : ∃ κ, k = 2 ^ κ) (hk : 2 * k ∣ 2 ^ α) :
    (Hexp α k).card = 2 ^ α / k := by
  obtain ⟨κ, rfl⟩ := hk2pow
  have h2k : (2 : ℕ) * 2 ^ κ = 2 ^ (κ + 1) := by rw [pow_succ]; ring
  have hκα : κ + 1 ≤ α := by
    have hdvd : (2 : ℕ) ^ (κ + 1) ∣ 2 ^ α := by rw [← h2k]; exact hk
    exact (Nat.pow_dvd_pow_iff_le_right (by norm_num : (1 : ℕ) < 2)).mp hdvd
  -- basic facts about the modulus `M = 2^{α+1}` and base `g = 4·2^κ+1`
  have hMpos : (0 : ℕ) < 2 ^ (α + 1) := by positivity
  have h4M : (4 : ℕ) ∣ 2 ^ (α + 1) := by
    rw [show (4 : ℕ) = 2 ^ 2 from rfl]; exact pow_dvd_pow 2 (by omega)
  have hg_odd : Odd (4 * 2 ^ κ + 1) := ⟨2 * 2 ^ κ, by ring⟩
  -- the `+`-residue `p(a) = g^a % M` is a nonzero residue `≡ 1 (mod 4)`
  have hp_pos : ∀ a, 0 < (4 * 2 ^ κ + 1) ^ a % 2 ^ (α + 1) := by
    intro a
    have hd : (2 : ℕ) ∣ 2 ^ (α + 1) := dvd_pow_self 2 (by omega)
    have : Odd ((4 * 2 ^ κ + 1) ^ a % 2 ^ (α + 1)) := by
      rw [Nat.odd_iff, Nat.mod_mod_of_dvd _ hd, ← Nat.odd_iff]; exact hg_odd.pow
    exact this.pos
  have hp_lt : ∀ a, (4 * 2 ^ κ + 1) ^ a % 2 ^ (α + 1) < 2 ^ (α + 1) := fun a => Nat.mod_lt _ hMpos
  have hg4 : (4 * 2 ^ κ + 1) % 4 = 1 := by
    rw [show 4 * 2 ^ κ + 1 = 1 + 2 ^ κ * 4 from by ring, Nat.add_mul_mod_self_right]
  have hp4 : ∀ a, (4 * 2 ^ κ + 1) ^ a % 2 ^ (α + 1) % 4 = 1 := by
    intro a; rw [Nat.mod_mod_of_dvd _ h4M, Nat.pow_mod, hg4, one_pow]; omega
  -- the `−`-residue `n(a) = (M - p(a)) % M = M - p(a)`, with `n(a) ≡ 3 (mod 4)`
  have hn_val : ∀ a, (2 ^ (α + 1) - (4 * 2 ^ κ + 1) ^ a % 2 ^ (α + 1)) % 2 ^ (α + 1)
      = 2 ^ (α + 1) - (4 * 2 ^ κ + 1) ^ a % 2 ^ (α + 1) := by
    intro a; exact Nat.mod_eq_of_lt (by have := hp_pos a; have := hp_lt a; omega)
  have hn4 : ∀ a, (2 ^ (α + 1) - (4 * 2 ^ κ + 1) ^ a % 2 ^ (α + 1)) % 2 ^ (α + 1) % 4 = 3 := by
    intro a; rw [hn_val a]; have := hp4 a; have := hp_lt a; have := hp_pos a; omega
  -- each `±`-cell `{p(a), n(a)}` has exactly two elements
  have hcell : ∀ a, ({(4 * 2 ^ κ + 1) ^ a % 2 ^ (α + 1),
      (2 ^ (α + 1) - (4 * 2 ^ κ + 1) ^ a % 2 ^ (α + 1)) % 2 ^ (α + 1)} : Finset ℕ).card = 2 := by
    intro a; apply Finset.card_pair
    have h1 := hp4 a; have h2 := hn4 a; intro heq; rw [heq] at h1; omega
  -- distinct cells are disjoint
  have hdisj : ∀ a ∈ Finset.range (2 ^ α / (2 * 2 ^ κ)),
      ∀ a' ∈ Finset.range (2 ^ α / (2 * 2 ^ κ)), a ≠ a' →
      Disjoint ({(4 * 2 ^ κ + 1) ^ a % 2 ^ (α + 1),
          (2 ^ (α + 1) - (4 * 2 ^ κ + 1) ^ a % 2 ^ (α + 1)) % 2 ^ (α + 1)} : Finset ℕ)
        ({(4 * 2 ^ κ + 1) ^ a' % 2 ^ (α + 1),
          (2 ^ (α + 1) - (4 * 2 ^ κ + 1) ^ a' % 2 ^ (α + 1)) % 2 ^ (α + 1)} : Finset ℕ) := by
    intro a ha a' ha' hne
    rw [Finset.mem_range] at ha ha'
    have he : 2 ^ α / (2 * 2 ^ κ) = 2 ^ (α - κ - 1) := by
      rw [h2k, Nat.pow_div (by omega) (by norm_num), show α - (κ + 1) = α - κ - 1 from by omega]
    rw [he] at ha ha'
    -- `p(a) ≠ p(a')` by injectivity of the `+`-orbit enumeration (exact order)
    have hpp : (4 * 2 ^ κ + 1) ^ a % 2 ^ (α + 1) ≠ (4 * 2 ^ κ + 1) ^ a' % 2 ^ (α + 1) :=
      fun heq => hne (four_mul_add_one_pow_inj α κ a a' hκα ha ha' heq)
    rw [Finset.disjoint_left]
    intro x hx hx'
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx hx'
    obtain hx | hx := hx <;> obtain hx' | hx' := hx' <;> rw [hx] at hx'
    · exact hpp hx'
    · have h1 := hp4 a; have h2 := hn4 a'; rw [hx'] at h1; omega
    · have h1 := hn4 a; have h2 := hp4 a'; rw [hx'] at h1; omega
    · rw [hn_val a, hn_val a'] at hx'
      have := hp_lt a; have := hp_lt a'; have := hp_pos a; have := hp_pos a'
      exact hpp (by omega)
  -- assemble: `|Hexp| = ∑_{a < ord} 2 = 2·ord = 2^α / 2^κ`
  have hRHS : 2 ^ α / 2 ^ κ = 2 * (2 ^ α / (2 * 2 ^ κ)) := by
    have e1 : 2 ^ α / 2 ^ κ = 2 ^ (α - κ) := Nat.pow_div (by omega) (by norm_num)
    have e2 : 2 ^ α / (2 * 2 ^ κ) = 2 ^ (α - κ - 1) := by
      rw [h2k, Nat.pow_div (by omega) (by norm_num), show α - (κ + 1) = α - κ - 1 from by omega]
    rw [e1, e2]
    conv_lhs => rw [show α - κ = (α - κ - 1) + 1 from by omega, pow_succ]
    ring
  rw [hRHS, Hexp, Finset.card_biUnion hdisj]
  rw [Finset.sum_congr rfl (fun a _ => hcell a), Finset.sum_const, Finset.card_range,
    smul_eq_mul, Nat.mul_comm]

end ArkLib.Lattices.CyclotomicModulus

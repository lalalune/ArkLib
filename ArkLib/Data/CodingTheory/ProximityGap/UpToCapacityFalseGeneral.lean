/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.EntropyVolumeListSize
import ArkLib.Data.CodingTheory.ProximityGap.ListDecodingCapacityOverflow

/-!
# General capacity-exponent overflow ⇒ list-decoding bound is false (#232, negative side)

Master form of `rs_uptoCapacity_false_rate12_n256`: the negative side of the prize, abstracted to
**every** rate and radius via a single overflow hypothesis.

  `rs_lambda_gt_of_capExp_overflow` — for `RS[F, α, k]` at relative radius `δ`, if the
  capacity exponent `E = n·H_q(⌊δn⌋/n) − (n − k)` overflows the prize budget, namely

      `log_q((n+1)·(ε*·|F|))  <  E`,

  then `Λ(RS[k], δ) > ε*·|F|` — the `(δ, ε*)` list-decoding bound fails.

Chains the axiom-clean entropy-volume lower bound `rs_lambda_ge_capacity_exponent`
(`|Λ| ≥ q^E/(n+1)`) with the `rpow`/`logb` overflow bridge `threshold_lt_pow_div`. Since
`H_q(δ) > δ` for `δ ∈ (0, (q−1)/q]` (`qEntropy_gt_self`), the exponent `E` is positive at the
capacity radius `δ = 1 − ρ` for every rate, so the overflow holds once `n` is large enough relative
to the prize budget `ε* = 2^{-128}`. The rate-`1/2`, `n = 256` instance
(`rs_uptoCapacity_false_rate12_n256`) is exactly this theorem with the numerics discharged.

So the negative side — the list-decoding bound is unattainable at capacity — holds uniformly across
the prize-rate family, in one statement. Axiom-clean (`[propext, Classical.choice, Quot.sound]`).

## References
- [ABF26] Arnon, Boneh, Fenzi. *Open Problems in List Decoding and Correlated Agreement*. 2026.
  #232.
- [CS25] Crites, Stewart. *On Reed–Solomon Proximity Gaps Conjectures*. ePrint 2025/2046.
-/

namespace CodingTheory

open Real ListDecodable
open scoped ENNReal

/-- Closed form for the q-ary entropy at radius `1/2`. -/
theorem qEntropy_half_eq (q : ℕ) :
    qEntropy q (1 / 2) =
      (1 / 2) * Real.logb (q : ℝ) ((q : ℝ) - 1) + Real.logb (q : ℝ) 2 := by
  unfold qEntropy
  have hhalf : (1 : ℝ) - 1 / 2 = 1 / 2 := by norm_num
  have hloghalf : Real.logb (q : ℝ) (1 / 2) = -Real.logb (q : ℝ) 2 := by
    rw [show (1 / 2 : ℝ) = (2 : ℝ)⁻¹ by norm_num, Real.logb_inv]
  rw [hhalf, hloghalf]
  ring

/-- **Capacity-exponent overflow refutes the list-decoding bound.** For `RS[F, α, k]` at radius
`δ`, if `log_q((n+1)·ε*·|F|) < n·H_q(⌊δn⌋/n) − (n − k)` (the capacity exponent
overflows the budget), then `Λ(RS[k], δ) > ε*·|F|`. Generalizes
`rs_uptoCapacity_false_rate12_n256` to every rate and radius. -/
theorem rs_lambda_gt_of_capExp_overflow
    {F ι : Type} [Field F] [Fintype F] [DecidableEq F]
    [Fintype ι] [Nonempty ι] [DecidableEq ι]
    (α : ι ↪ F) (k : ℕ) (δ : ℝ) (hδpos : 0 < δ) (hδlt : δ < 1)
    (hq : 2 ≤ Fintype.card F) (hkcard : k ≤ Fintype.card ι)
    (hk0 : 0 < ⌊δ * (Fintype.card ι : ℝ)⌋₊)
    (hkn : ⌊δ * (Fintype.card ι : ℝ)⌋₊ < Fintype.card ι)
    {ε_star : ℝ} (hεpos : 0 < ε_star)
    (hover : Real.logb (Fintype.card F)
        (((Fintype.card ι : ℝ) + 1) * (ε_star * (Fintype.card F : ℝ)))
      < (Fintype.card ι : ℝ) * qEntropy (Fintype.card F)
          ((⌊δ * (Fintype.card ι : ℝ)⌋₊ : ℝ) / (Fintype.card ι : ℝ))
        - ((Fintype.card ι : ℝ) - (k : ℝ))) :
    ENNReal.ofReal (ε_star * (Fintype.card F : ℝ))
      < (Lambda ((ReedSolomon.code α k : Set (ι → F))) δ : ENNReal) := by
  have hLB := rs_lambda_ge_capacity_exponent α k δ hδpos hδlt hq hkcard hk0 hkn
  have hq1 : (1 : ℝ) < (Fintype.card F : ℝ) := by
    have : 1 < Fintype.card F := by omega
    exact_mod_cast this
  have hqpos : (0 : ℝ) < (Fintype.card F : ℝ) := by
    have : 0 < Fintype.card F := by omega
    exact_mod_cast this
  have hεq : 0 < ε_star * (Fintype.card F : ℝ) := mul_pos hεpos hqpos
  have hreal := threshold_lt_pow_div (Fintype.card F) hq1 ((Fintype.card ι : ℝ) + 1)
    (by positivity) (ε_star * (Fintype.card F : ℝ)) hεq _ hover
  exact lt_of_lt_of_le ((ENNReal.ofReal_lt_ofReal_iff (by positivity)).mpr hreal) hLB

#print axioms rs_lambda_gt_of_capExp_overflow

/-- **Concrete rate-`1/2`, length-`256` capacity-side failure.** For `RS[F, α, 128]` on
`Fin 256`, if `2^128 ≤ |F| ≤ 2^256`, then at the Singleton/capacity radius `δ = 1/2`
the list size is already larger than the prize budget `2^{-128}·|F|`. -/
theorem rs_uptoCapacity_false_rate12_n256
    {F : Type} [Field F] [Fintype F] (α : Fin 256 ↪ F)
    (hq1 : (2 : ℝ) ^ 128 ≤ (Fintype.card F : ℝ))
    (hq2 : (Fintype.card F : ℝ) ≤ (2 : ℝ) ^ 256) :
    ENNReal.ofReal ((1 / 2 ^ 128) * (Fintype.card F : ℝ))
      < (Lambda ((ReedSolomon.code α 128 : Set (Fin 256 → F))) (1 / 2) : ENNReal) := by
  classical
  have hqNat : 2 ≤ Fintype.card F := by
    have h2pow : (2 : ℝ) ≤ (2 : ℝ) ^ 128 := by norm_num
    have hqR : (2 : ℝ) ≤ (Fintype.card F : ℝ) := le_trans h2pow hq1
    exact_mod_cast hqR
  have hover : Real.logb (Fintype.card F)
        (((Fintype.card (Fin 256) : ℝ) + 1) *
          ((1 / 2 ^ 128) * (Fintype.card F : ℝ)))
      < (Fintype.card (Fin 256) : ℝ) * qEntropy (Fintype.card F)
          ((⌊(1 / 2 : ℝ) * (Fintype.card (Fin 256) : ℝ)⌋₊ : ℝ) /
            (Fintype.card (Fin 256) : ℝ))
        - ((Fintype.card (Fin 256) : ℝ) - (128 : ℝ)) := by
    set q : ℝ := (Fintype.card F : ℝ) with hqdef
    have hq1' : (2 : ℝ) ^ 128 ≤ q := by simpa [hqdef] using hq1
    have hq2' : q ≤ (2 : ℝ) ^ 256 := by simpa [hqdef] using hq2
    have hqpos : 0 < q := by
      have h2pow : (0 : ℝ) < (2 : ℝ) ^ 128 := by positivity
      exact lt_of_lt_of_le h2pow hq1'
    have hqgt1 : 1 < q := by
      have h2pow : (1 : ℝ) < (2 : ℝ) ^ 128 := by norm_num
      exact lt_of_lt_of_le h2pow hq1'
    have hqm1pos : 0 < q - 1 := by linarith
    have h2q3 : (2 : ℝ) * q ≤ 3 * (q - 1) := by
      have hq3 : 3 ≤ q := by
        have h3pow : (3 : ℝ) ≤ (2 : ℝ) ^ 128 := by norm_num
        exact le_trans h3pow hq1'
      nlinarith
    have hpow23 : (2 : ℝ) ^ 128 * q ^ 128 ≤ 3 ^ 128 * (q - 1) ^ 128 := by
      have hpow := pow_le_pow_left₀ (by positivity : (0 : ℝ) ≤ (2 : ℝ) * q) h2q3 128
      simpa [mul_pow] using hpow
    have hnum : (257 : ℝ) * 3 ^ 128 < 2 ^ 256 := by norm_num
    have harglt :
        (257 : ℝ) * ((1 / 2 ^ 128) * q) <
          ((2 : ℝ) ^ 256 * (q - 1) ^ 128) / q ^ 128 := by
      have hqpowpos : 0 < q ^ 128 := by positivity
      have h2powpos : 0 < (2 : ℝ) ^ 128 := by positivity
      apply (lt_div_iff₀ hqpowpos).mpr
      refine lt_of_mul_lt_mul_left ?_ (le_of_lt h2powpos)
      calc
        (2 : ℝ) ^ 128 *
            ((257 : ℝ) * ((1 / 2 ^ 128) * q) * q ^ 128)
            = (257 : ℝ) * q * q ^ 128 := by
              field_simp [pow_ne_zero 128 (by norm_num : (2 : ℝ) ≠ 0)]
        _ ≤ (257 : ℝ) * (2 : ℝ) ^ 256 * q ^ 128 := by
              exact mul_le_mul_of_nonneg_right
                (mul_le_mul_of_nonneg_left hq2' (by positivity : (0 : ℝ) ≤ 257))
                (by positivity : (0 : ℝ) ≤ q ^ 128)
        _ ≤ (257 : ℝ) * (2 : ℝ) ^ 128 * 3 ^ 128 * (q - 1) ^ 128 := by
              have hmul := mul_le_mul_of_nonneg_left hpow23
                (by positivity : (0 : ℝ) ≤ (257 : ℝ) * 2 ^ 128)
              nlinarith
        _ < (2 : ℝ) ^ 128 * ((2 : ℝ) ^ 256 * (q - 1) ^ 128) := by
              have hmul := mul_lt_mul_of_pos_right hnum
                (by positivity : (0 : ℝ) < (2 : ℝ) ^ 128 * (q - 1) ^ 128)
              nlinarith
    have hE :
        (Fintype.card (Fin 256) : ℝ) * qEntropy (Fintype.card F)
            ((⌊(1 / 2 : ℝ) * (Fintype.card (Fin 256) : ℝ)⌋₊ : ℝ) /
              (Fintype.card (Fin 256) : ℝ))
          - ((Fintype.card (Fin 256) : ℝ) - (128 : ℝ))
        = Real.logb (Fintype.card F)
            (((2 : ℝ) ^ 256 * (q - 1) ^ 128) / q ^ 128) := by
      have hqcard : (Fintype.card F : ℝ) = q := by rw [hqdef]
      have hfloor : ((⌊(1 / 2 : ℝ) * (256 : ℝ)⌋₊ : ℝ) / (256 : ℝ)) = 1 / 2 := by
        norm_num
      have hsub : ((256 : ℝ) - (128 : ℝ)) = 128 := by norm_num
      rw [Fintype.card_fin]
      change (256 : ℝ) * qEntropy (Fintype.card F)
          ((⌊(1 / 2 : ℝ) * (256 : ℝ)⌋₊ : ℝ) / (256 : ℝ))
        - ((256 : ℝ) - (128 : ℝ))
        = Real.logb (Fintype.card F)
            (((2 : ℝ) ^ 256 * (q - 1) ^ 128) / q ^ 128)
      rw [hfloor, hsub]
      rw [qEntropy_half_eq, hqcard]
      have hqne : q ≠ 0 := ne_of_gt hqpos
      have hqm1ne : q - 1 ≠ 0 := ne_of_gt hqm1pos
      have h2ne : (2 : ℝ) ^ 256 ≠ 0 := pow_ne_zero _ (by norm_num)
      have hqm1powne : (q - 1) ^ 128 ≠ 0 := pow_ne_zero _ hqm1ne
      have hqpowne : q ^ 128 ≠ 0 := pow_ne_zero _ hqne
      have hlogq : Real.logb q q = 1 := Real.logb_self_eq_one hqgt1
      rw [Real.logb_div (mul_ne_zero h2ne hqm1powne) hqpowne,
        Real.logb_mul h2ne hqm1powne,
        Real.logb_pow, Real.logb_pow, Real.logb_pow, hlogq]
      ring
    have hargpos : 0 < (257 : ℝ) * ((1 / 2 ^ 128) * q) := by positivity
    have hloglt := Real.logb_lt_logb (b := q) hqgt1 hargpos harglt
    have hargleft :
        ((Fintype.card (Fin 256) : ℝ) + 1) *
            ((1 / 2 ^ 128) * (Fintype.card F : ℝ))
          = (257 : ℝ) * ((1 / 2 ^ 128) * q) := by
      rw [Fintype.card_fin, hqdef]
      norm_num
    rw [hE]
    rw [hargleft]
    simpa [hqdef, mul_assoc] using hloglt
  exact rs_lambda_gt_of_capExp_overflow (F := F) (ι := Fin 256) α 128 (1 / 2)
    (by norm_num) (by norm_num) hqNat
    (by rw [Fintype.card_fin]; norm_num)
    (by rw [Fintype.card_fin]; norm_num)
    (by rw [Fintype.card_fin]; norm_num)
    (ε_star := 1 / 2 ^ 128) (by positivity) hover

#print axioms rs_uptoCapacity_false_rate12_n256

end CodingTheory

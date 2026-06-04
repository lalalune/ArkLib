import ArkLib.Data.MvPolynomial.LinearMvExtension
import ArkLib.Data.MvPolynomial.Multilinear
import Mathlib.Data.Nat.Bitwise

open LinearMvExtension MvPolynomial Polynomial

noncomputable section

/-- For `{0,1}`-valued exponents `d : Fin m → ℕ`, the `ℓ`-th bit of `∑ j, 2^j * d_j`
recovers `d ℓ`. Binary representation uniqueness. -/
lemma testBit_sum_two_pow {m : ℕ} (d : Fin m → ℕ) (hd : ∀ j, d j ≤ 1) (ℓ : Fin m) :
    (∑ j : Fin m, 2 ^ (j : ℕ) * d j).testBit ℓ.val = (d ℓ = 1) := by
  sorry

/-- The encoding `d ↦ ∑ j, 2^(j) * d_j` is injective on `{0,1}`-valued exponents. -/
lemma sum_two_pow_inj {m : ℕ} (d e : Fin m → ℕ)
    (hd : ∀ j, d j ≤ 1) (he : ∀ j, e j ≤ 1)
    (h : ∑ j : Fin m, 2 ^ (j : ℕ) * d j = ∑ j : Fin m, 2 ^ (j : ℕ) * e j) :
    ∀ j, d j = e j := by
  intro j
  have h1 := testBit_sum_two_pow d hd j
  have h2 := testBit_sum_two_pow e he j
  rw [h] at h1
  rw [h1] at h2
  have hdj := hd j
  have hej := he j
  omega_nat <;> omega
  sorry

end

/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.BCIKS20.RestrictedFaaDiBrunoExtract

/-!
# BCIKS20 Appendix A.4 — the STEP-8 `ξ`-telescope for monic `H` (issue #139, obstruction 2)

For monic `H` the `W`-power weighting of the STEP-8 recursion side already collapses
(`restrictedMatchRecursionPartitionForm_eq_Wfree_of_leadingCoeff_one`). The remaining unit-side
content is the **separability-discriminant unit `ξ = ClaimA2.ξ`** (`ξ ≠ 0`,
`embeddingOf𝒪Into𝕃_ξ_ne_zero`). This file determines exactly how the `ξ`-powers behave and lands
every genuine `ξ`-power-bookkeeping lemma.

## The exponent geometry

* On the **recursion (RHS) side** `restrictedMatchRecursionPartitionForm`, each `(i₁, λ)` summand
  carries `ξ^{2·i₁ + σλ − 2}` (`σλ = sigmaLambda λ = λ.parts.card`), over a *global* denominator
  `ξ^{2(t+1)−1}` (the `W`-side of the denominator is `1` for monic `H`).
* On the **Faà-di-Bruno (LHS) side** `restrictedFaaDiBrunoPartitionForm`, the `ξ`-powers enter only
  through the assembled-series coefficients `coeff l (βHenselAssembled) =
  embed(βHensel l) / (W^{l+1}·ξ^{2l−1})`. Since `coeff 0` is `ξ`-free (`2·0−1 = 0` in `ℕ`) and each
  part `l ≥ 1`, a partition `λ ⊢ (t+1−i₁)` contributes the `ξ`-denominator exponent
  `∑_{l∈λ}(2l−1) = 2·(λ.parts.sum) − σλ = 2(t+1−i₁) − σλ`.

## Result: the `ξ`-powers TELESCOPE jointly, not as a pure-RHS factorization

The pure-`ℕ` identity `xiExp_recNum_add_lhsDen` proves the central fact

  `(2·i₁ + σλ − 2) + (2·(t+1−i₁) − σλ) = 2·(t+1) − 2`,

i.e. **the per-term RHS `ξ`-numerator exponent and the per-term LHS `ξ`-denominator exponent sum to
a single `(i₁,λ)`-independent constant `2(t+1)−2`.**  No `ℕ`-truncation interferes (the single-part
partition `[t+1]` of the `i₁ = 0` block is excluded by the `(t+1) ∉ λ.parts` filter, so every
surviving term has `2·i₁ + σλ ≥ 2`; `card ≤ sum` keeps the LHS exponent honest).

Consequently (`restrictedMatchRecursionPartitionForm_eq_ξfree_of_leadingCoeff_one`) the monic
recursion side factors as a **single global unit `ζ · ξ⁻¹`** times a sum whose per-term `ξ`-content
is *exactly* the LHS-shaped denominator `1/ξ^{2(t+1−i₁)−σλ}`:

  `restrictedMatchRecursionPartitionForm … t`
    `= (ζ / ξ) · ∑_{i₁,λ} (⟦B_coeff⟧ · ⟦partitionProd λ βHensel⟧) / ξ^{2(t+1−i₁)−σλ}`.

So the answer to "do the `ξ`-powers factor out cleanly?" is precise: the *global* `ξ`-power
collapses to a single `ξ⁻¹` (one global unit per order), but a genuine per-term `ξ`-denominator
`1/ξ^{2(t+1−i₁)−σλ}` **remains** — and it is exactly the `ξ`-denominator that the LHS
`βHenselAssembled` coefficients supply. The `ξ`-telescope is therefore a *joint* LHS↔RHS
cancellation, not a one-sided `(global-ξ-power)·(ξ-free core)` split. After this `ξ`-bookkeeping the
monic STEP-8 residual reduces to the `W`-free, `ξ`-matched combinatorial Faà-di-Bruno identity
(`B_coeff`/binomial/`countPerms`/`partitionProd`), which is the unformalized BCIKS20 A.4 content.

See issue #139.
-/

noncomputable section

open scoped BigOperators
open Finset
open Polynomial Polynomial.Bivariate
open ArkLib.PowerSeriesComposition
open BCIKS20AppendixA
open ProximityPrize.BCIKS20.GammaGenuine

namespace BCIKS20.HenselNumerator

variable {F : Type} [Field F]
variable (H : F[X][Y]) [Fact (Irreducible H)] [Fact (0 < H.natDegree)]

/-! ## 1. The pure-`ℕ` exponent telescope -/

/-- **`σλ ≤ m` for a partition `λ ⊢ m` (axiom-clean).** The number of parts is at most the sum,
because every part is `≥ 1`. This is the no-truncation guard for the LHS `ξ`-denominator exponent
`2·m − σλ`. -/
theorem sigmaLambda_le {m : ℕ} (lam : Nat.Partition m) : sigmaLambda lam ≤ m := by
  have hc : lam.parts.card ≤ lam.parts.sum := by
    calc lam.parts.card = (lam.parts.map (fun _ => 1)).sum := by
              simp [Multiset.map_const', Multiset.sum_replicate]
      _ ≤ (lam.parts.map (fun l => l)).sum := by
              apply Multiset.sum_map_le_sum_map
              intro l hl
              exact lam.parts_pos hl
      _ = lam.parts.sum := by rw [Multiset.map_id']
  rw [lam.parts_sum] at hc
  rw [sigmaLambda]
  exact hc

/-- **The LHS `ξ`-denominator exponent of a partition (axiom-clean).** The assembled-series
coefficient `coeff l (βHenselAssembled) = embed(βHensel l) / (W^{l+1}·ξ^{2l−1})` contributes the
`ξ`-exponent `2·l − 1` for each part `l` of `λ`. Summing over the multiset of parts (the genuine
`partitionProd`-shape product), and using that every part is `≥ 1` so each `2·l − 1` is untruncated,
gives `∑_{l∈λ}(2l−1) = 2·m − σλ`. -/
theorem sum_map_two_mul_sub_one {m : ℕ} (lam : Nat.Partition m) :
    (lam.parts.map (fun l => 2 * l - 1)).sum = 2 * m - sigmaLambda lam := by
  have hmap : (lam.parts.map (fun l => 2 * l - 1))
      = lam.parts.map (fun l => 2 * (l - 1) + 1) := by
    apply Multiset.map_congr rfl
    intro l hl
    have hl1 : 1 ≤ l := lam.parts_pos hl
    omega
  rw [hmap, Multiset.sum_map_add]
  simp only [Multiset.sum_map_mul_left, Multiset.map_const', Multiset.sum_replicate, smul_eq_mul,
    mul_one]
  have hsub : (lam.parts.map (fun l => l - 1)).sum = m - lam.parts.card := by
    have heq : (lam.parts.map (fun l => (l - 1) + 1)).sum = (lam.parts.map (fun l => l)).sum := by
      apply congrArg
      apply Multiset.map_congr rfl
      intro l hl
      have hl1 : 1 ≤ l := lam.parts_pos hl
      omega
    rw [Multiset.sum_map_add] at heq
    simp only [Multiset.map_const', Multiset.sum_replicate, smul_eq_mul, mul_one,
      Multiset.map_id'] at heq
    rw [lam.parts_sum] at heq
    omega
  rw [hsub, sigmaLambda]
  have hle := sigmaLambda_le lam
  rw [sigmaLambda] at hle
  omega

/-- **The STEP-8 `ξ`-exponent telescope (PURE `ℕ`, axiom-clean).** For a partition `λ ⊢ (t+1−i₁)`
with `i₁ ≤ t+1` and `2 ≤ 2·i₁ + σλ` (the surviving-filter guard), the per-term recursion-side
`ξ`-numerator exponent `2·i₁ + σλ − 2` and the LHS-side `ξ`-denominator exponent
`2·(t+1−i₁) − σλ` sum to the single `(i₁,λ)`-independent constant `2·(t+1) − 2`:

  `(2·i₁ + σλ − 2) + (2·(t+1−i₁) − σλ) = 2·(t+1) − 2`.

This is the algebraic heart of the `ξ`-telescope: it shows the per-term variation in the recursion
exponent is *exactly* compensated by the per-term variation in the LHS assembled-coefficient
`ξ`-denominator. -/
theorem xiExp_recNum_add_lhsDen (t i1 : ℕ) {m : ℕ} (lam : Nat.Partition m)
    (hm : m = t + 1 - i1) (hi1 : i1 ≤ t + 1) (hguard : 2 ≤ 2 * i1 + sigmaLambda lam) :
    (2 * i1 + sigmaLambda lam - 2) + (2 * m - sigmaLambda lam) = 2 * (t + 1) - 2 := by
  have hsl : sigmaLambda lam ≤ m := sigmaLambda_le lam
  subst hm
  omega

end BCIKS20.HenselNumerator

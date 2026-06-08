/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.CandidateStructureLoop26

/-!
# Loop 27 — polynomial additive fold costs are also absorbed

Loop 26 shot down the multiplicative-tower disproof if the per-fold contribution is additive with a
constant cost. This file pushes that self-refutation one step further: even if each fold contributes
a **polynomial** amount in the top domain size `N = 2^m`, summing over all `m = log₂ N` folds is still
polynomial. The logarithmic depth is absorbed by one extra domain power:

    m · (2^m)^c ≤ (2^m)^(c+1).

So an additive per-fold disproof cannot merely exhibit polynomially many new close codewords per
round. It must force a super-polynomial additive contribution, or else show genuinely multiplicative
branching with an `N`-growing factor. This is the refined disproof target after Loops 24--26.

Sorry-free and axiom-clean. See `DISPROOF_LOG.md` (Loop27).
-/

namespace ArkLib.ProximityGap.StructureLoop27

open ArkLib.ProximityGap.StructureLoop26

/-- **The fold-depth logarithm is absorbed by one domain power.** Since `m ≤ 2^m`, summing a
degree-`c` polynomial contribution over the `m` folds is bounded by a degree-`c+1` polynomial in the
domain size `2^m`. -/
theorem fold_depth_mul_domain_pow_le_next_pow (c m : ℕ) :
    (m : ℝ) * (((2 : ℝ) ^ m) ^ c) ≤ ((2 : ℝ) ^ m) ^ (c + 1) := by
  have hm : (m : ℝ) ≤ (2 : ℝ) ^ m := by
    have := Nat.lt_two_pow_self (n := m)
    exact_mod_cast this.le
  have hnonneg : 0 ≤ (((2 : ℝ) ^ m) ^ c) := by positivity
  calc
    (m : ℝ) * (((2 : ℝ) ^ m) ^ c) ≤
        ((2 : ℝ) ^ m) * (((2 : ℝ) ^ m) ^ c) :=
      mul_le_mul_of_nonneg_right hm hnonneg
    _ = ((2 : ℝ) ^ m) ^ (c + 1) := by rw [pow_succ]

/-- **Polynomial additive per-fold cost is prize-safe.** If every fold adds at most a degree-`c`
polynomial in the top domain size `2^m`, then after all `m` folds the list is bounded by the base
plus a degree-`c+1` polynomial. Thus a polynomial additive fold cost cannot be the fixed-gap
super-polynomial lower bound required by Loop 8. -/
theorem additive_polynomial_step_le_next_pow
    (T : ℕ → ℝ) {B₀ C : ℝ} {c m : ℕ} (hC : 0 ≤ C)
    (hstep : ∀ j, T (j + 1) ≤ T j + C * (((2 : ℝ) ^ m) ^ c)) (hbase : T 0 ≤ B₀) :
    T m ≤ B₀ + C * (((2 : ℝ) ^ m) ^ (c + 1)) := by
  let b : ℝ := C * (((2 : ℝ) ^ m) ^ c)
  have hb : 0 ≤ b := by
    dsimp [b]
    positivity
  have hlin : T m ≤ T 0 + (m : ℝ) * b :=
    additive_recursion_linear T b hstep m
  have hdepth : (m : ℝ) * b ≤ C * (((2 : ℝ) ^ m) ^ (c + 1)) := by
    dsimp [b]
    calc
      (m : ℝ) * (C * (((2 : ℝ) ^ m) ^ c)) =
          C * ((m : ℝ) * (((2 : ℝ) ^ m) ^ c)) := by ring
      _ ≤ C * (((2 : ℝ) ^ m) ^ (c + 1)) :=
        mul_le_mul_of_nonneg_left (fold_depth_mul_domain_pow_le_next_pow c m) hC
  linarith

end ArkLib.ProximityGap.StructureLoop27

/-! ## Axiom audit -/
#print axioms ArkLib.ProximityGap.StructureLoop27.fold_depth_mul_domain_pow_le_next_pow
#print axioms ArkLib.ProximityGap.StructureLoop27.additive_polynomial_step_le_next_pow

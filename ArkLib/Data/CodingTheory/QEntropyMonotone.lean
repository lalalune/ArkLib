/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/

import ArkLib.Data.CodingTheory.ProximityPrizeLeaves2

/-!
# Monotonicity of the q-ary entropy `qEntropy` below capacity

ArkLib's base-`q` entropy `CodingTheory.qEntropy` (ABF26 Def 2.2) has nonnegativity / boundary /
capacity lemmas, but lacked monotonicity. This file adds it, derived from Mathlib's
`Real.qaryEntropy_strictMonoOn` through the existing base-change bridge
`qEntropy_mul_log_eq_qaryEntropy` (`qEntropy q x · log q = Real.qaryEntropy q x`): dividing by the
positive constant `log q` (for `q ≥ 2`) preserves strict monotonicity.

`qEntropy q` is strictly increasing on `[0, 1 − 1/q]` (up to the capacity point `1 − 1/q`,
`qEntropy_capacity_eq_one`). Useful for relating `H_q(δ')` and `H_q(δ)` when `δ' ≤ δ` in the
sub-capacity regime, e.g. floor-vs-real radius comparisons in the entropy-volume / list-size
bounds. `sorry`/`axiom`-free, axiom-clean.
-/

namespace CodingTheory

open Real

variable {q : ℕ}

/-- **`qEntropy q` is strictly monotone on `[0, 1 − 1/q]`.** Derived from Mathlib's
`Real.qaryEntropy_strictMonoOn` via the base-change bridge `qEntropy q x · log q = qaryEntropy q x`
(division by `log q > 0` preserves strict monotonicity). -/
theorem qEntropy_strictMonoOn (hq : 2 ≤ q) :
    StrictMonoOn (qEntropy q) (Set.Icc 0 (1 - 1 / (q : ℝ))) := by
  intro x hx y hy hxy
  have hlog : 0 < Real.log q :=
    Real.log_pos (by exact_mod_cast (show 1 < q by omega))
  have h := Real.qaryEntropy_strictMonoOn hq hx hy hxy
  rw [← qEntropy_mul_log_eq_qaryEntropy hq x, ← qEntropy_mul_log_eq_qaryEntropy hq y] at h
  exact lt_of_mul_lt_mul_right h hlog.le

/-- **`qEntropy q` is monotone on `[0, 1 − 1/q]`** (non-strict corollary). -/
theorem qEntropy_monotoneOn (hq : 2 ≤ q) :
    MonotoneOn (qEntropy q) (Set.Icc 0 (1 - 1 / (q : ℝ))) :=
  (qEntropy_strictMonoOn hq).monotoneOn

/-- **`qEntropy` comparison below capacity.** For `0 ≤ x ≤ y ≤ 1 − 1/q`, `H_q(x) ≤ H_q(y)`. -/
theorem qEntropy_le_qEntropy_of_le (hq : 2 ≤ q) {x y : ℝ}
    (hx0 : 0 ≤ x) (hxy : x ≤ y) (hy : y ≤ 1 - 1 / (q : ℝ)) :
    qEntropy q x ≤ qEntropy q y :=
  qEntropy_monotoneOn hq ⟨hx0, le_trans hxy hy⟩ ⟨le_trans hx0 hxy, hy⟩ hxy

end CodingTheory

-- Axiom audit: depends on exactly `[propext, Classical.choice, Quot.sound]`.
#print axioms CodingTheory.qEntropy_strictMonoOn
#print axioms CodingTheory.qEntropy_monotoneOn
#print axioms CodingTheory.qEntropy_le_qEntropy_of_le

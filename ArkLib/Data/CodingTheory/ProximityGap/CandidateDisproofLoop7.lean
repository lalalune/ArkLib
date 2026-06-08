/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import Mathlib.Algebra.Order.Field.Basic

/-!
# Loop 7 — why near-capacity Frobenius orbits do not yet disprove the prize

Loop 6 isolated a real obstruction: if a Frobenius-stable bad-scalar set is bounded by a
field-independent constant `C`, then every bad scalar has bounded Frobenius degree. A high-degree
bad scalar would therefore be a promising disproof mechanism.

Loop 7 records the first disproof of that disproof. The toy Frobenius constructions found so far
sit extremely close to capacity: the available gap behaves like `η ≲ A / d`, where `d` is the
Frobenius-orbit degree. In that regime a linear orbit lower bound `#bad = O(d)` is only
`O(1 / η)`, and the prize RHS is explicitly allowed to contain an `η^{-c₃}` factor. Thus such a
family cannot refute the field-universal prize by itself; to beat the conjecture one needs either
a high-degree orbit at fixed gap, or bad-count growth faster than every permitted polynomial in
`1/η` and the interleaving width.

The lemmas below are intentionally just the reusable arithmetic guardrail.
-/

namespace ArkLib.ProximityGap.DisproofLoop7

/-- If a degree parameter `d` only appears when the prize gap is at most `A / d`, then the degree
is bounded by the inverse gap: `d ≤ A / η`.

This is the core self-refutation for the near-capacity Frobenius-orbit attack: a growing orbit
whose growth is paid for by a shrinking gap is polynomial in `1/η`, exactly the kind of growth the
prize bound allows. -/
theorem degree_le_const_div_gap_of_gap_le_const_div_degree
    {d : ℕ} {η A : ℝ}
    (hd : 0 < (d : ℝ)) (hη : 0 < η)
    (hgap : η ≤ A / (d : ℝ)) :
    (d : ℝ) ≤ A / η := by
  have hmul : η * (d : ℝ) ≤ A := by
    calc
      η * (d : ℝ) ≤ (A / (d : ℝ)) * (d : ℝ) :=
        mul_le_mul_of_nonneg_right hgap (le_of_lt hd)
      _ = A := by field_simp [ne_of_gt hd]
  rw [le_div_iff₀ hη]
  simpa [mul_comm] using hmul

/-- Linear bad-count growth in such a near-capacity family is absorbed by one inverse-gap factor.

If `#bad ≤ B d` and the construction only works with `η ≤ A/d`, then `#bad ≤ (B A)/η`. So a
merely linear Frobenius-orbit family cannot beat a prize RHS with even a first power of `1/η`.
-/
theorem linear_badcount_le_const_div_gap_of_gap_le_const_div_degree
    {bad d : ℕ} {η A B : ℝ}
    (hd : 0 < (d : ℝ)) (hη : 0 < η) (hB : 0 ≤ B)
    (hbad : (bad : ℝ) ≤ B * (d : ℝ))
    (hgap : η ≤ A / (d : ℝ)) :
    (bad : ℝ) ≤ (B * A) / η := by
  have hdle : (d : ℝ) ≤ A / η :=
    degree_le_const_div_gap_of_gap_le_const_div_degree hd hη hgap
  calc
    (bad : ℝ) ≤ B * (d : ℝ) := hbad
    _ ≤ B * (A / η) := mul_le_mul_of_nonneg_left hdle hB
    _ = (B * A) / η := by ring

end ArkLib.ProximityGap.DisproofLoop7

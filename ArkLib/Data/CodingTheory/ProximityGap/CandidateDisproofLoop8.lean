/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Data.Real.Archimedean
import Mathlib.Tactic

/-!
# Loop 8 (O6') — the disproof reduces to a `q`-growing list size below capacity

The genuine open prize is `epsMCAgsPrizeUniversalConjecture` / `UniversalGSListMassBound`.
At the mass-bound layer, the proved plumbing gives a GS-row error bound of the form

  `epsMCAgs <= listSize / q`,

and the prize target has the form

  `listSize / q <= (1 / q) * B`,

where `B = (2^m)^c1 / (rho^c2 * eta^c3)` is independent of the field size `q` once the
universal constants, rate, gap, and interleaving parameter are fixed.

This file records the exact arithmetic: because `q > 0`, the `1/q` factors cancel. Thus the prize
mass clause is equivalent, at this layer, to a field-size-independent list budget `listSize <= B`.
A disproof therefore needs a fixed-gap family whose necessary faithful/pivot GS list size grows
past every such constant as `q` grows. Merely making probabilities scale like `poly / q` is not
enough.

These lemmas do not disprove the prize; they isolate the remaining disproof target.
-/

namespace ArkLib.ProximityGap.DisproofLoop8

/-- **The `1/q` cancellation.** If `listSize / q <= (1/q) * B` and `q > 0`, then
`listSize <= B`. This is the arithmetic core of Loop 8: the prize mass clause is a
field-size-independent list-size bound after cancelling the common `1/q`. -/
theorem listsize_le_numerator_of_mass
    {q listSize : ℕ} {B : ℝ}
    (hq : 0 < (q : ℝ))
    (hmass : (listSize : ℝ) / (q : ℝ) ≤ (1 / (q : ℝ)) * B) :
    (listSize : ℝ) ≤ B := by
  have hmul := mul_le_mul_of_nonneg_right hmass (le_of_lt hq)
  have hleft : ((listSize : ℝ) / (q : ℝ)) * (q : ℝ) = (listSize : ℝ) := by
    field_simp [ne_of_gt hq]
  have hright : ((1 / (q : ℝ)) * B) * (q : ℝ) = B := by
    field_simp [ne_of_gt hq]
  linarith

/-- **Oversized list refutes the mass clause.** If the required list size exceeds the numerator
budget `B`, then no inequality of the form `listSize/q <= (1/q)*B` can hold. -/
theorem listsize_gt_numerator_refutes_mass
    {q listSize : ℕ} {B : ℝ}
    (hq : 0 < (q : ℝ))
    (hgt : B < (listSize : ℝ)) :
    ¬ (listSize : ℝ) / (q : ℝ) ≤ (1 / (q : ℝ)) * B := by
  intro hmass
  exact not_lt_of_ge (listsize_le_numerator_of_mass hq hmass) hgt

/-- **Any fixed numerator can be exceeded by a natural list-size.** This supplies the purely
arithmetic half of the fixed-gap disproof target: for any proposed numerator budget `B`, some
natural list size is larger. The missing mathematical content is realizing such a list size as a
necessary faithful/pivot GS list at fixed gap. -/
theorem listsize_can_exceed_any_numerator (B : ℝ) :
    ∃ listSize : ℕ, B < (listSize : ℝ) :=
  exists_nat_gt B

/-- **Single-instance refutation package.** A single positive field size and necessary list size
above the numerator budget is enough to refute the corresponding mass inequality. -/
theorem single_instance_over_numerator_refutes
    {q listSize : ℕ} {B : ℝ}
    (hq : 0 < (q : ℝ))
    (hgt : B < (listSize : ℝ)) :
    ((listSize : ℝ) / (q : ℝ) ≤ (1 / (q : ℝ)) * B) → False := by
  exact fun hmass => listsize_gt_numerator_refutes_mass hq hgt hmass

end ArkLib.ProximityGap.DisproofLoop8

/-! ## Axiom audit -/
#print axioms ArkLib.ProximityGap.DisproofLoop8.listsize_le_numerator_of_mass
#print axioms ArkLib.ProximityGap.DisproofLoop8.listsize_gt_numerator_refutes_mass
#print axioms ArkLib.ProximityGap.DisproofLoop8.listsize_can_exceed_any_numerator
#print axioms ArkLib.ProximityGap.DisproofLoop8.single_instance_over_numerator_refutes

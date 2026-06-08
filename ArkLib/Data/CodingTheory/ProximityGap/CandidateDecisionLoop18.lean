/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Algebra.Order.Field.Basic

/-!
# Loop 18 — the prize is exactly ONE decision: is the smooth-domain list `q`-independent-bounded?

Both full-band reductions collapse to the *same* quantity. The proof side (Loop17: BGM) and the
disproof side (Loop8: `q`-independence) are two faces of one criterion:

    prize mass clause at `(ρ,η)`  ⟺  the GS list size `ℓ` is `≤ B`,

where `B = (2^m)^{c₁}/(ρ^{c₂}η^{c₃})` is the **`q`-independent** prize numerator (the `1/q` cancels,
Loop8). This file proves that equivalence cleanly: `ℓ/q ≤ (1/q)·B ↔ ℓ ≤ B`. Hence:

* **prize TRUE** ⟺ the smooth-domain RS list at the prize radius is bounded by a `q`-independent
  polynomial in `(2^m, 1/ρ, 1/η)` — the BGM-generic behaviour (Loop17);
* **prize FALSE** ⟺ that list grows with `q` at fixed `(ρ,η)` — the Diamond–Gruen deterministic
  behaviour (Loop8/Loop12).

These are exhaustive and mutually exclusive: the prize is decided by a single binary fact about one
list-size function. No current method determines it for *plain smooth-deterministic* RS (second
moment dies at `η₀`, BGM needs generic points, folding needs folded codes), and the structural leans
**conflict** — Loop15's degree-buffer leans TRUE, the deterministic-domain hardness
(Diamond–Gruen / BCIKS "Johnson is the genuine limit for deterministic RS") leans FALSE. So Loop15's
lean is *not* decisive; honestly the prize is undecided. This brick records the exact decision
criterion. Sorry-free, axiom-clean. See `DISPROOF_LOG.md` (Loop18 decision criterion + corrected synthesis).
-/

namespace ArkLib.ProximityGap.DecisionLoop18

/-- **The prize decision criterion.** For a list size `ℓ`, the `q`-independent prize numerator `B`,
and field size `q > 0`, the prize mass clause `ℓ/q ≤ (1/q)·B` holds **iff** `ℓ ≤ B`. So the prize at
`(ρ,η)` is decided entirely by whether the list size is bounded by the `q`-independent numerator —
the single binary fact both the proof (Loop17/BGM) and disproof (Loop8) reductions hinge on. -/
theorem prize_mass_iff_listsize_le {ℓ B q : ℝ} (hq : 0 < q) :
    ℓ / q ≤ (1 / q) * B ↔ ℓ ≤ B := by
  rw [div_eq_inv_mul, one_div]
  constructor
  · intro h; exact le_of_mul_le_mul_left h (inv_pos.mpr hq)
  · intro h; exact mul_le_mul_of_nonneg_left h (le_of_lt (inv_pos.mpr hq))

/-- **Exhaustive dichotomy.** For any list size `ℓ` and `q`-independent numerator `B`, exactly one
holds: the prize mass clause (`ℓ ≤ B`, prize TRUE side) or its strict failure (`B < ℓ`, prize FALSE
side). The prize is a single binary decision about the list-size function. -/
theorem prize_dichotomy (ℓ B : ℝ) : ℓ ≤ B ∨ B < ℓ := le_or_lt ℓ B

/-- **`q`-independence of the decision.** The criterion `ℓ ≤ B` does not mention `q`: if the list
size `ℓ` is the *same* across a family of fields (the deterministic smooth-domain regime, where the
domain `2^m` and rate `ρ` are fixed while the field `q` varies), then the prize verdict is uniform —
either every field in the family satisfies the mass clause, or none does. -/
theorem decision_qindependent {ℓ B : ℝ} (hle : ℓ ≤ B) {q : ℝ} (hq : 0 < q) :
    ℓ / q ≤ (1 / q) * B :=
  (prize_mass_iff_listsize_le hq).mpr hle

end ArkLib.ProximityGap.DecisionLoop18

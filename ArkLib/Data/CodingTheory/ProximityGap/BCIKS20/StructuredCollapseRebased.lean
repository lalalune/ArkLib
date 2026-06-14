/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import Mathlib.Tactic

/-!
# The re-baselined structured collapse (Johnson V1, step 1)

DISPROOF_LOG O154 findings 1–2: the in-tree structured weight invariant is unsatisfiable
at `t = 0` in the consumers' regime `D > d_H` (the order-0 representative is `Y`, of weight
`D + 1 − d_H`), so the base constant `1` must be re-baselined to `D + 1 − d_H`. This file
transcribes the verified hand proof that the re-baselined invariant still collapses into
the loose target `(2t+1)·d_R·D` consumed by `βHensel_weight_bound` — with slack `(t+1)·D`:

  `(D+1−d_H) + (t+1)·degW + (2t−1)·(d_R−1)·(D−d_H+1) ≤ (2t+1)·d_R·D`

under `1 ≤ d_H ≤ d_R`, `2 ≤ d_R`, `degW + d_H ≤ D`. The chain: the ξ-term cedes
`(D−d_H+1) ≤ D`; the budget identity leaves `D·(2d_R + 2t − 1) ≥ D·(2t+3)`; the remaining
terms need only `(t+2)·D`. ℕ-truncation edges (`t = 0` kills the ξ-term) verified.

This is step (1) of the V1 order; step (2) is the re-baselined invariant itself through
the (A.1) recursion (base case exact by the finding-1 rep computation), step (3) the
corrected per-term lemma, step (4) the wiring to `JohnsonDischargeStatement` and the
exact δ* pin.

## References
* DISPROOF_LOG O154 (findings 1–2); `HenselNumerator.lean` (`structured_weight_collapse`,
  `βHensel_weight_bound_of_structured_weight` — the `1`-based originals).
-/

namespace BCIKS20.HenselNumerator

/-- **The re-baselined structured collapse** (pure ℕ-arithmetic, slack `(t+1)·D`): the
corrected structured invariant implies the loose per-order weight target. -/
theorem structured_weight_collapse_rebased
    {dH dR degW D t : ℕ} (h1 : 1 ≤ dH) (hHR : dH ≤ dR) (h2 : 2 ≤ dR)
    (hW : degW + dH ≤ D) :
    (D + 1 - dH) + (t + 1) * degW + (2 * t - 1) * (dR - 1) * (D - dH + 1)
      ≤ (2 * t + 1) * dR * D := by
  -- normalize the truncated subtractions
  obtain ⟨a, rfl⟩ : ∃ a, D = a + dH := ⟨D - dH, by omega⟩
  have hdega : degW ≤ a := by omega
  have hD1 : a + dH + 1 - dH = a + 1 := by omega
  have hD2 : a + dH - dH + 1 = a + 1 := by omega
  rw [hD1, hD2]
  -- bound the LHS by `(a+1)·(t+2 + (2t−1)(dR−1))`
  have hLHS : (a + 1) + (t + 1) * degW + (2 * t - 1) * (dR - 1) * (a + 1)
      ≤ (a + 1) * ((t + 2) + (2 * t - 1) * (dR - 1)) := by
    have h1' : (t + 1) * degW ≤ (t + 1) * (a + 1) :=
      Nat.mul_le_mul_left _ (by omega)
    nlinarith [h1']
  refine le_trans hLHS ?_
  -- coefficient comparison: `t+2 + (2t−1)(dR−1) ≤ (2t+1)·dR`, then scale by `a+1 ≤ D`
  have hcoeff : (t + 2) + (2 * t - 1) * (dR - 1) ≤ (2 * t + 1) * dR := by
    rcases Nat.eq_zero_or_pos t with rfl | ht
    · simpa using h2
    · -- `t ≥ 1`: expand `(2t−1)(dR−1) = (2t−1)dR − (2t−1)`; reduces to `3 − t ≤ 2dR`.
      have h2t : 1 ≤ 2 * t := by omega
      obtain ⟨s, hs⟩ : ∃ s, 2 * t = s + 1 := ⟨2 * t - 1, by omega⟩
      obtain ⟨r, hr⟩ : ∃ r, dR = r + 1 := ⟨dR - 1, by omega⟩
      subst hr
      rw [hs]
      have hsub1 : s + 1 - 1 = s := by omega
      have hsub2 : r + 1 - 1 = r := by omega
      rw [hsub1, hsub2]
      -- goal: `t + 2 + s * r ≤ (s + 1 + 1) * (r + 1)` with `s = 2t − 1`, `r ≥ 1`
      have hr1 : 1 ≤ r := by omega
      have hst : t ≤ s := by omega
      nlinarith [hr1, hst]
  calc (a + 1) * ((t + 2) + (2 * t - 1) * (dR - 1))
      ≤ (a + 1) * ((2 * t + 1) * dR) := Nat.mul_le_mul_left _ hcoeff
    _ ≤ (a + dH) * ((2 * t + 1) * dR) := Nat.mul_le_mul_right _ (by omega)
    _ = (2 * t + 1) * dR * (a + dH) := by ring

/-! ## Source audit -/

#print axioms structured_weight_collapse_rebased

end BCIKS20.HenselNumerator

/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.SV11GeneratorFamily
import ArkLib.Data.CodingTheory.ProximityGap.WronskianGeneral

/-!
# The SV11 Wronskian's common `(X−c)`-power factor (#389) — the degree-reduction first step

`sv11_combination_natDegree_le` shows the imposed-combination auxiliary keeps degree `≈ tB`, which
makes the Stepanov bound trivial. The sharp `O(t^{2/3})` route instead uses the **Wronskian** of the
generators as the auxiliary and *divides out* the `t`-power common factors, dropping the effective
degree. This file proves the first, common-factor, step of that reduction.

For SV11 generators `g_j = X^{a_j}(X−c)^{t·b_j}` all with `b_j ≥ 1`, every `g_j` is divisible by
`(X−c)^t`, so by the in-tree `pow_dvd_wronskianDet` (with `l ≤ t+1`) the Wronskian is divisible by
`(X−c)^{l·t − C(l,2)}` — a factor of degree `≈ lt` that divides out, beginning the cancellation of the
`t`-power degree. The remaining (refined, per-`b_j`) cancellation down to effective degree `~lD` is the
research-level step that completes the sharp bound; this is its proven foundation.

Axiom-clean `[propext, Classical.choice, Quot.sound]`.
-/

open Polynomial Finset

namespace ProximityGap.BinomialDet

variable {F : Type*} [Field F]

/-- **The SV11 Wronskian's `(X−c)`-power factor.** For SV11 generators `g_j = X^{a_j}(X−c)^{t·b_j}` all
with `b_j ≥ 1` and `l ≤ t+1`, the Wronskian is divisible by `(X−c)^{l·t − C(l,2)}`. -/
theorem sv11_wronskian_pow_dvd {l : ℕ} (c : F) (t : ℕ) (idx : Fin l → ℕ × ℕ)
    (hl : l ≤ t + 1) (hb : ∀ j, 1 ≤ (idx j).2) :
    (X - C c) ^ (l * t - l.choose 2) ∣
      ArkLib.ProximityGap.Wronskian.wronskianDet (fun j => sv11Gen c t (idx j)) := by
  apply ArkLib.ProximityGap.Wronskian.pow_dvd_wronskianDet hl
  intro j
  unfold sv11Gen
  refine dvd_trans (pow_dvd_pow (X - C c) ?_) (dvd_mul_left _ _)
  calc t = t * 1 := (mul_one t).symm
    _ ≤ t * (idx j).2 := Nat.mul_le_mul_left t (hb j)

end ProximityGap.BinomialDet

-- Axiom audit (expected: propext, Classical.choice, Quot.sound only)
#print axioms ProximityGap.BinomialDet.sv11_wronskian_pow_dvd

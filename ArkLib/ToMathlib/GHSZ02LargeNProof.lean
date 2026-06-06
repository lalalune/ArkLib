/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/

import Mathlib
import ArkLib.ToMathlib.GHSZ02Cor20
import ArkLib.Data.CodingTheory.ListDecoding.GHSZ02Foundations

/-!
# GHSZ02 Corollary 20: the `GHSZ02LargeN` asymptotic residual, proven

This file discharges `CodingTheory.GHSZ02LargeN` — the single named asymptotic residual of
the GHSZ02 Cor-20 chain (`ArkLib/ToMathlib/GHSZ02Cor20.lean`) — at the front-door parameters
`δ = 1 − ((1−β)/α)·p^{α−1}`, for all `p` past explicit numeric thresholds.

## The ledger

With `A := (1−β)/α`, `P := (p:ℝ)`, `L := log p`, `r := ⌊δ·P⌋₊`, `a := p − r`, `k := ⌊P^α⌋₊`
(so `A·P^α ≤ a < A·P^α + 1`), the chain is:

* `C(p,r) = C(p,a)` (symmetry) `≥ (p+1−a)^a/a! ≥ (P/2)^a/a^a` (`Nat.pow_le_choose` via the
  in-tree `choose_real_ge_pow_div`, `Nat.factorial_le_pow`, and `a ≤ P/2`);
* `(P−1)^r = P^r·(1−1/P)^r ≥ P^r·(1−1/P)^p ≥ P^r·(e^{−1}/2)`
  (`GHSZ02Core.one_sub_inv_pow_ge_inv_e`);
* taking logs and cancelling `P^p = P^a·P^r`, the inequality reduces to the **ledger**
  `(P^α·β/2)·L + a·log 2 + a·log a + (1 + log 2) ≤ k·L`;
* `a·(log 2 + log a) = a·log(2a) ≤ (A·P^α+1)·(log(4A) + α·L)`, and since `α·A = 1−β` the
  head term `(1−β)·P^α·L` cancels against `k·L ≥ (P^α−1)·L`, leaving `(β/2)·P^α·L` of
  room, of which the threshold hypotheses `hT1`/`hT2` each consume `(β/4)·P^α·L`.

All declarations compile `sorry`/`axiom`-free and are axiom-clean
(`[propext, Classical.choice, Quot.sound]`).
-/

set_option linter.unusedSectionVars false
set_option maxHeartbeats 1600000

noncomputable section

open CodingTheory ListDecodable

namespace GHSZ02LargeNProof

/-- **Brick A: the ledger reduction.**  `GHSZ02LargeN α β p δ` at the front-door radius
`δ = 1 − ((1−β)/α)·p^{α−1}`, from explicit numeric threshold hypotheses (each of which
holds for all `p` large enough). -/
theorem ghsz02LargeN_of_thresholds
    (α β : ℝ) (p : ℕ) (hp2 : 2 ≤ p)
    (hα0 : 0 < α) (hβ1 : β < 1)
    (hA1 : 1 ≤ (1 - β) / α * (p : ℝ) ^ α)
    (hhalf : (1 - β) / α * (p : ℝ) ^ α + 1 ≤ (p : ℝ) / 2)
    (hT1 : Real.log (4 * ((1 - β) / α)) * ((1 - β) / α * (p : ℝ) ^ α + 1)
        ≤ β / 4 * ((p : ℝ) ^ α * Real.log p))
    (hT2 : (1 + Real.log 2) + (1 + α) * Real.log p
        ≤ β / 4 * ((p : ℝ) ^ α * Real.log p)) :
    GHSZ02LargeN α β p (1 - (1 - β) / α * (p : ℝ) ^ (α - 1)) := by
  classical
  unfold GHSZ02LargeN
  -- ## Setup
  have hP0 : (0 : ℝ) < (p : ℝ) := by exact_mod_cast Nat.lt_of_lt_of_le Nat.zero_lt_two hp2
  have hP1 : (1 : ℝ) < (p : ℝ) := by exact_mod_cast Nat.lt_of_lt_of_le Nat.one_lt_two hp2
  have hP2 : (2 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hp2
  have hL0 : (0 : ℝ) < Real.log p := Real.log_pos hP1
  set A : ℝ := (1 - β) / α with hAdef
  set P : ℝ := (p : ℝ) with hPdef
  set L : ℝ := Real.log p with hLdef
  have hA0 : 0 < A := by
    rw [hAdef]; exact div_pos (by linarith) hα0
  have hPα0 : (0 : ℝ) < P ^ α := Real.rpow_pos_of_pos hP0 α
  -- ## The floor-argument rewrite `δ·P = P − A·P^α`
  have hδP : (1 - A * P ^ (α - 1)) * P = P - A * P ^ α := by
    have hsplit : P ^ (α - 1) = P ^ α / P := by
      rw [Real.rpow_sub hP0, Real.rpow_one]
    rw [hsplit]
    field_simp
  rw [hδP]
  set r : ℕ := ⌊P - A * P ^ α⌋₊ with hrdef
  set k : ℕ := ⌊P ^ α⌋₊ with hkdef
  -- ## Floor bookkeeping
  have hPA_nonneg : (0 : ℝ) ≤ P - A * P ^ α := by nlinarith
  have hr_le : (r : ℝ) ≤ P - A * P ^ α := Nat.floor_le hPA_nonneg
  have hr_gt : P - A * P ^ α < (r : ℝ) + 1 := Nat.lt_floor_add_one _
  have hr_le_p : r ≤ p := by
    have : (r : ℝ) ≤ P := le_trans hr_le (by nlinarith [mul_pos hA0 hPα0])
    exact_mod_cast this
  set a : ℕ := p - r with hadef
  have ha_cast : (a : ℝ) = P - (r : ℝ) := by
    rw [hadef]
    push_cast [Nat.cast_sub hr_le_p]
    ring
  have ha_lb : A * P ^ α ≤ (a : ℝ) := by rw [ha_cast]; linarith
  have ha_ub : (a : ℝ) < A * P ^ α + 1 := by rw [ha_cast]; linarith
  have ha1R : (1 : ℝ) ≤ (a : ℝ) := le_trans hA1 ha_lb
  have ha1 : 1 ≤ a := by exact_mod_cast ha1R
  have ha0R : (0 : ℝ) < (a : ℝ) := by linarith
  have har : a + r = p := by rw [hadef]; omega
  have ha_half : (a : ℝ) ≤ P / 2 := by linarith
  -- ## Binomial lower bound: `(P/2)^a / a^a ≤ C(p,r)`
  have hchoose_symm : Nat.choose p a = Nat.choose p r := by
    rw [hadef]
    exact Nat.choose_symm hr_le_p
  have hfac_le : (Nat.factorial a : ℝ) ≤ (a : ℝ) ^ a := by
    exact_mod_cast Nat.factorial_le_pow a
  have hfac_pos : (0 : ℝ) < (Nat.factorial a : ℝ) := by
    exact_mod_cast Nat.factorial_pos a
  have hcast_sub : ((p + 1 - a : ℕ) : ℝ) = P + 1 - (a : ℝ) := by
    rw [Nat.cast_sub (by omega : a ≤ p + 1)]
    push_cast
    ring
  have hbase_ge : P / 2 ≤ ((p + 1 - a : ℕ) : ℝ) := by
    rw [hcast_sub]; linarith
  have hapow_pos : (0 : ℝ) < (a : ℝ) ^ a := pow_pos ha0R a
  have hchoose_ge : (P / 2) ^ a / (a : ℝ) ^ a ≤ (Nat.choose p r : ℝ) := by
    rw [← hchoose_symm]
    have h1 := GHSZ02Cor20.choose_real_ge_pow_div a p
    have h2 : (P / 2) ^ a / (a : ℝ) ^ a ≤ ((p + 1 - a : ℕ) : ℝ) ^ a / (a : ℝ) ^ a := by
      gcongr
      · linarith
      · exact hbase_ge
    have h3 : ((p + 1 - a : ℕ) : ℝ) ^ a / (a : ℝ) ^ a
        ≤ ((p + 1 - a : ℕ) : ℝ) ^ a / (Nat.factorial a : ℝ) :=
      div_le_div_of_nonneg_left (by positivity) hfac_pos hfac_le
    exact le_trans h2 (le_trans h3 h1)
  -- ## The `(P−1)^r` bound
  have hinvP : (1 : ℝ) / P ≤ 1 / 2 := by
    apply one_div_le_one_div_of_le (by norm_num) hP2
  have h1P : (0 : ℝ) ≤ 1 - 1 / P := by linarith
  have h1P' : 1 - 1 / P ≤ 1 := by
    have : (0 : ℝ) < 1 / P := by positivity
    linarith
  have hhalfP : (1 : ℝ) / 2 ≤ 1 - 1 / P := by linarith
  have hexpbrick : Real.exp (-1) ≤ (1 - 1 / P) ^ (p - 1) :=
    GHSZ02Core.one_sub_inv_pow_ge_inv_e hp2
  have hp_pow : (1 - 1 / P) ^ p = (1 - 1 / P) ^ (p - 1) * (1 - 1 / P) := by
    conv_lhs => rw [show p = (p - 1) + 1 by omega]
    rw [pow_succ]
  have hppow_ge : Real.exp (-1) / 2 ≤ (1 - 1 / P) ^ p := by
    rw [hp_pow]
    calc Real.exp (-1) / 2 = Real.exp (-1) * (1 / 2) := by ring
      _ ≤ (1 - 1 / P) ^ (p - 1) * (1 - 1 / P) :=
          mul_le_mul hexpbrick hhalfP (by norm_num)
            (le_trans (Real.exp_pos _).le hexpbrick)
  have hrp_pow : (1 - 1 / P) ^ p ≤ (1 - 1 / P) ^ r :=
    pow_le_pow_of_le_one h1P h1P' hr_le_p
  have hPm1_eq : P - 1 = P * (1 - 1 / P) := by field_simp
  have hPm1_ge : P ^ r * (Real.exp (-1) / 2) ≤ (P - 1) ^ r := by
    rw [hPm1_eq, mul_pow]
    exact mul_le_mul_of_nonneg_left (le_trans hppow_ge hrp_pow) (by positivity)
  -- ## RHS assembly
  have hRHS : P ^ k * ((P / 2) ^ a / (a : ℝ) ^ a * (P ^ r * (Real.exp (-1) / 2)))
      ≤ P ^ k * ((Nat.choose p r : ℝ) * (P - 1) ^ r) := by
    apply mul_le_mul_of_nonneg_left _ (by positivity)
    exact mul_le_mul hchoose_ge hPm1_ge (by positivity) (by positivity)
  refine le_trans ?_ hRHS
  -- ## The main multiplicative bound, via logs
  have hLHS_pos : (0 : ℝ) < P ^ p * P ^ (P ^ α * β / 2) := by positivity
  have hQ_pos : (0 : ℝ) < (P / 2) ^ a / (a : ℝ) ^ a := by positivity
  have hR_pos : (0 : ℝ) < P ^ r * (Real.exp (-1) / 2) := by positivity
  have hRHS_pos : (0 : ℝ)
      < P ^ k * ((P / 2) ^ a / (a : ℝ) ^ a * (P ^ r * (Real.exp (-1) / 2))) := by
    positivity
  rw [← Real.log_le_log_iff hLHS_pos hRHS_pos]
  -- expand both logs into linear form
  rw [Real.log_mul (by positivity) (by positivity),
    Real.log_mul (by positivity) (by positivity),
    Real.log_mul (by positivity) (by positivity),
    Real.log_mul (by positivity) (by positivity),
    Real.log_div (by positivity) (by positivity),
    Real.log_div (by positivity) (by positivity),
    Real.log_div (ne_of_gt (Real.exp_pos _)) (by norm_num),
    Real.log_pow, Real.log_pow, Real.log_pow, Real.log_pow,
    Real.log_rpow hP0, Real.log_exp]
  -- ## The ledger
  -- `p = a + r` as a real coefficient identity
  have hParL : P * L = (a : ℝ) * L + (r : ℝ) * L := by
    have hpar : P = (a : ℝ) + (r : ℝ) := by
      rw [hPdef]
      exact_mod_cast har.symm
    rw [hpar]; ring
  -- `k·L ≥ (P^α − 1)·L`
  have hk_gt : P ^ α - 1 < (k : ℝ) := by
    have := Nat.lt_floor_add_one (P ^ α)
    rw [← hkdef] at this
    linarith
  have hkL : (P ^ α - 1) * L ≤ (k : ℝ) * L :=
    mul_le_mul_of_nonneg_right hk_gt.le hL0.le
  -- `a·log(2a) ≤ (A·P^α + 1)·(log(4A) + α·L)`
  have h2a_ub : 2 * (a : ℝ) ≤ 4 * A * P ^ α := by nlinarith
  have hlog2a_le : Real.log (2 * (a : ℝ)) ≤ Real.log (4 * A) + α * L := by
    have hstep : Real.log (2 * (a : ℝ)) ≤ Real.log (4 * A * P ^ α) :=
      Real.log_le_log (by positivity) h2a_ub
    have hsplit : Real.log (4 * A * P ^ α) = Real.log (4 * A) + α * L := by
      rw [Real.log_mul (by positivity) (ne_of_gt hPα0), Real.log_rpow hP0]
    linarith
  have hlog2a_nonneg : 0 ≤ Real.log (2 * (a : ℝ)) := by
    apply Real.log_nonneg
    linarith
  have haln : (a : ℝ) * Real.log (2 * (a : ℝ))
      ≤ (A * P ^ α + 1) * (Real.log (4 * A) + α * L) := by
    have hmul1 : (a : ℝ) * Real.log (2 * (a : ℝ))
        ≤ (a : ℝ) * (Real.log (4 * A) + α * L) :=
      mul_le_mul_of_nonneg_left hlog2a_le ha0R.le
    have hpos : 0 ≤ Real.log (4 * A) + α * L := le_trans hlog2a_nonneg hlog2a_le
    have hmul2 : (a : ℝ) * (Real.log (4 * A) + α * L)
        ≤ (A * P ^ α + 1) * (Real.log (4 * A) + α * L) :=
      mul_le_mul_of_nonneg_right ha_ub.le hpos
    linarith
  -- split `log(2a)` and expand the product
  have hsplit2a : (a : ℝ) * Real.log (2 * (a : ℝ))
      = (a : ℝ) * Real.log 2 + (a : ℝ) * Real.log (a : ℝ) := by
    rw [Real.log_mul (by norm_num) (ne_of_gt ha0R)]
    ring
  have hexpand : (A * P ^ α + 1) * (Real.log (4 * A) + α * L)
      = Real.log (4 * A) * (A * P ^ α + 1) + (α * A) * (P ^ α * L) + α * L := by
    ring
  have hαA : α * A = 1 - β := by
    rw [hAdef]
    field_simp
  have hαAsub : (α * A) * (P ^ α * L) = (1 - β) * (P ^ α * L) := by rw [hαA]
  -- close the ledger
  nlinarith [hkL, haln, hsplit2a, hexpand, hαAsub, hParL, hT1, hT2, hL0,
    mul_pos hPα0 hL0]

end GHSZ02LargeNProof

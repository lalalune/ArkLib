/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.ListThresholdWellDefined
import ArkLib.Data.CodingTheory.ProximityGap.ScaleJohnsonInstance
import ArkLib.Data.CodingTheory.ProximityGap.ListInteriorUnconditionalT1

/-!
# Issue #232 — THE PRIZE THRESHOLD OBJECT, BRACKETED, for in-tree Reed–Solomon at prize scale

The capstone composition.  `ListThresholdWellDefined` made the prize's `δ*` a first-class object
(`aStar`, with the crossing API); `PrizeScaleJohnsonInstance` bounds lists at prize scale; Round-5's
`exists_interior_list_ge_unconditional` violates budgets near capacity.  This file composes all
three **for the genuine in-tree `ReedSolomon.code`** at the prize's own configuration
(`n = 2²⁰`, `ρ = 1/2`, `|F| ≤ 2²⁵⁶`):

* `maxList_rs_le_91` — the worst-case list of the RS code at agreement `750000` is `≤ 91`
  (each listed codeword pulls back to its unique degree-`< 2¹⁹` polynomial; the prize-scale GS
  instance caps the polynomial list).
* `ninetyone_lt_maxList_rs` — at agreement `2¹⁹ + 1` (just inside capacity) the worst-case list
  **exceeds 91**: the Round-5 averaging word has `≥ C(2²⁰, 2¹⁹+1)/q` close codewords, and the
  central-binomial chain gives `C(2²⁰, 2¹⁹+1) > 2²⁶³ > 91·q` for every `q ≤ 2²⁵⁶`.
* `prize_threshold_bracket` (HEADLINE) — therefore the **threshold object itself** satisfies

  `2¹⁹ + 1  <  aStar(RS, 91)  ≤  750000`,

  i.e. the prize's `δ*` (at budget 91, in agreement form) is machine-checked to lie in the window
  `δ* ∈ [1 − 750000/2²⁰, 1 − (2¹⁹+1)/2²⁰) ≈ [0.2848, 0.5)` — confined between 1.2% inside the
  Johnson radius and the capacity edge, for the actual in-tree Reed–Solomon code at full prize
  scale.  Sharpening this window (in particular its position relative to Johnson `≈ 0.2929`) is
  exactly the open content of the prize.

All results are `sorry`-free and axiom-clean (`[propext, Classical.choice, Quot.sound]`).
-/

open Finset Polynomial

namespace ArkLib.CodingTheory.PrizeScaleThresholdBracket

open ArkLib.CodingTheory.ListThresholdWellDefined
open ArkLib.CodingTheory.Round5Unconditional
open ArkLib.CodingTheory.Round4InteriorList

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

/-- The in-tree Reed–Solomon code at prize scale (`n = 2²⁰`, degree `< 2¹⁹`), as a `Finset` of
words (the carrier for the `maxList`/`aStar` machinery). -/
noncomputable def rsCodeF (D : Fin (2 ^ 20) ↪ F) : Finset (Fin (2 ^ 20) → F) :=
  by
    classical
    exact Finset.univ.filter (· ∈ ReedSolomon.code D (2 ^ 19))

/-- The two agreement counts in play (`ListThresholdWellDefined.agree` and the Round-4/5
`agreeCount`) are the same number — the underlying filters differ only in their `Decidable`
instances. -/
theorem agree_eq_agreeCount (c w : Fin (2 ^ 20) → F) :
    agree c w = agreeCount c w := by
  unfold agree agreeCount
  congr 1

/-- **Upper side: the RS worst-case list at agreement `750000` is `≤ 91`.**  Every listed codeword
is the evaluation of a unique degree-`< 2¹⁹` polynomial; the polynomial pullback of the list is
admissible for `prize_scale_johnson_list_bound`, which caps it at `91`. -/
theorem maxList_rs_le_91 (D : Fin (2 ^ 20) ↪ F) :
    maxList (rsCodeF D) 750000 ≤ 91 := by
  classical
  apply Finset.sup_le
  intro w _
  set S := (rsCodeF D).filter (fun c => 750000 ≤ agree c w) with hS
  -- choose, for each listed word, its polynomial
  have hpoly : ∀ v ∈ S, ∃ p : F[X], p.degree < (2 ^ 19 : ℕ) ∧ v = ReedSolomon.evalOnPoints D p := by
    intro v hv
    rw [hS, Finset.mem_filter] at hv
    have hcode : v ∈ ReedSolomon.code D (2 ^ 19) := by
      have := hv.1
      rw [rsCodeF, Finset.mem_filter] at this
      exact this.2
    exact ReedSolomon.mem_code_iff_exists_polynomial.mp hcode
  set L : Finset F[X] := S.attach.image
    (fun v => Classical.choose (hpoly v.1 v.2)) with hL
  -- the pullback has the same cardinality (evaluation determines the word)
  have hcardL : S.card = L.card := by
    rw [hL]
    rw [Finset.card_image_of_injOn, Finset.card_attach]
    intro v₁ _ v₂ _ heq
    have h₁ := (Classical.choose_spec (hpoly v₁.1 v₁.2)).2
    have h₂ := (Classical.choose_spec (hpoly v₂.1 v₂.2)).2
    apply Subtype.ext
    rw [h₁, h₂, heq]
  -- the pullback is admissible for the prize-scale GS bound
  have hbound : L.card ≤ 91 := by
    apply ArkLib.CodingTheory.PrizeScaleJohnson.prize_scale_johnson_list_bound
      (⇑D) w D.injective L
    · -- degrees
      intro f hf
      rw [hL, Finset.mem_image] at hf
      obtain ⟨v, _, rfl⟩ := hf
      have hdeg := (Classical.choose_spec (hpoly v.1 v.2)).1
      rcases eq_or_ne (Classical.choose (hpoly v.1 v.2)) 0 with h0 | h0
      · rw [h0]
        simp
      · have := (Polynomial.degree_lt_iff_natDegree_lt h0).mp (by exact_mod_cast hdeg)
        omega
    · -- agreements
      intro f hf
      rw [hL, Finset.mem_image] at hf
      obtain ⟨v, _, rfl⟩ := hf
      have heval := (Classical.choose_spec (hpoly v.1 v.2)).2
      have hagree : 750000 ≤ agree v.1 w := by
        have := v.2
        rw [hS, Finset.mem_filter] at this
        exact this.2
      calc 750000 ≤ agree v.1 w := hagree
        _ = (Finset.univ.filter fun s : Fin (2 ^ 20) =>
              (Classical.choose (hpoly v.1 v.2)).eval (D s) = w s).card := by
            unfold agree
            congr 1
            apply Finset.filter_congr
            intro i _
            have : v.1 i = (Classical.choose (hpoly v.1 v.2)).eval (D i) := by
              rw [heval]; rfl
            rw [this]
  omega

/-- **The central-binomial chain:** `91·q < C(2²⁰, 2¹⁹+1)` for every `q ≤ 2²⁵⁶` — symbolic
(`4^(2¹⁹) = 2^(2²⁰)` dwarfs everything), no astronomical computation. -/
theorem ninetyone_mul_q_lt_choose (q : ℕ) (hq : q ≤ 2 ^ 256) :
    91 * q < (2 ^ 20).choose (2 ^ 19 + 1) := by
  -- 2·C(k+1) ≥ C(k):  C(k+1)·(k+1) = C(k)·(n−k) = C(k)·2¹⁹  and  2·(2¹⁹+1) ≥ 2²⁰ ≥ 2¹⁹.
  have hratio : (2 ^ 20).choose (2 ^ 19) ≤ 2 * (2 ^ 20).choose (2 ^ 19 + 1) := by
    have h := Nat.choose_succ_right_eq (2 ^ 20) (2 ^ 19)
    -- h : C(2^20, 2^19+1) * (2^19+1) = C(2^20, 2^19) * (2^20 − 2^19)
    have hsub : (2 ^ 20 : ℕ) - 2 ^ 19 = 2 ^ 19 := by norm_num
    rw [hsub] at h
    -- multiply out: C(k)·(2¹⁹+1) ≤ C(k)·2²⁰ = 2·C(k)·2¹⁹ = 2·C(k+1)·(2¹⁹+1)
    have hineq : (2 ^ 20).choose (2 ^ 19) * (2 ^ 19 + 1)
        ≤ (2 * (2 ^ 20).choose (2 ^ 19 + 1)) * (2 ^ 19 + 1) := by
      calc (2 ^ 20).choose (2 ^ 19) * (2 ^ 19 + 1)
          ≤ (2 ^ 20).choose (2 ^ 19) * (2 ^ 20) := by
            apply Nat.mul_le_mul_left
            norm_num
        _ = 2 * ((2 ^ 20).choose (2 ^ 19) * 2 ^ 19) := by ring
        _ = 2 * ((2 ^ 20).choose (2 ^ 19 + 1) * (2 ^ 19 + 1)) := by rw [h]
        _ = (2 * (2 ^ 20).choose (2 ^ 19 + 1)) * (2 ^ 19 + 1) := by ring
    exact Nat.le_of_mul_le_mul_right hineq (by norm_num)
  -- 4^(2¹⁹) ≤ 2²⁰ · C(2²⁰, 2¹⁹)  (central binomial)
  have hcb : 4 ^ (2 ^ 19) ≤ 2 ^ 20 * (2 ^ 20).choose (2 ^ 19) := by
    have h := Nat.four_pow_le_two_mul_self_mul_centralBinom (2 ^ 19) (by norm_num)
    -- h : 4 ^ (2^19) ≤ 2 * 2^19 * centralBinom (2^19)
    have hcb_eq : Nat.centralBinom (2 ^ 19) = (2 ^ 20).choose (2 ^ 19) := by
      rw [Nat.centralBinom]
      norm_num
    rw [hcb_eq] at h
    calc 4 ^ (2 ^ 19) ≤ 2 * 2 ^ 19 * (2 ^ 20).choose (2 ^ 19) := h
      _ = 2 ^ 20 * (2 ^ 20).choose (2 ^ 19) := by ring
  -- 4^(2¹⁹) = 2^(2²⁰)
  have hfour : (4 : ℕ) ^ (2 ^ 19) = 2 ^ (2 ^ 20) := by
    rw [show (4 : ℕ) = 2 ^ 2 by norm_num, ← pow_mul]
    norm_num
  -- chain: 2²⁸⁴ < 2^(2²⁰) ≤ 2²⁰·C(k) ≤ 2²¹·C(k+1)  ⟹  2²⁶³ < C(k+1)
  have hbig : (2 : ℕ) ^ 284 < 2 ^ 21 * (2 ^ 20).choose (2 ^ 19 + 1) := by
    calc (2 : ℕ) ^ 284 < 2 ^ (2 ^ 20) := by
          apply Nat.pow_lt_pow_right (by norm_num)
          norm_num
      _ = 4 ^ (2 ^ 19) := hfour.symm
      _ ≤ 2 ^ 20 * (2 ^ 20).choose (2 ^ 19) := hcb
      _ ≤ 2 ^ 20 * (2 * (2 ^ 20).choose (2 ^ 19 + 1)) := Nat.mul_le_mul_left _ hratio
      _ = 2 ^ 21 * (2 ^ 20).choose (2 ^ 19 + 1) := by ring
  have hC : (2 : ℕ) ^ 263 < (2 ^ 20).choose (2 ^ 19 + 1) := by
    have h284 : (2 : ℕ) ^ 284 = 2 ^ 21 * 2 ^ 263 := by
      rw [← pow_add]
    rw [h284] at hbig
    exact Nat.lt_of_mul_lt_mul_left hbig
  calc 91 * q ≤ 91 * 2 ^ 256 := Nat.mul_le_mul_left _ hq
    _ < 2 ^ 7 * 2 ^ 256 := by
        exact (Nat.mul_lt_mul_right (2 ^ 256)).2 (by norm_num)
    _ = 2 ^ 263 := by rw [← pow_add]
    _ < (2 ^ 20).choose (2 ^ 19 + 1) := hC

/-- **Lower side: at agreement `2¹⁹ + 1` the RS worst-case list EXCEEDS 91** (for any prize-scale
field `q ≤ 2²⁵⁶`): the Round-5 averaging word has `≥ C(2²⁰, 2¹⁹+1)/q > 91` close codewords. -/
theorem ninetyone_lt_maxList_rs (D : Fin (2 ^ 20) ↪ F)
    (hq : Fintype.card F ≤ 2 ^ 256) :
    91 < maxList (rsCodeF D) (2 ^ 19 + 1) := by
  classical
  obtain ⟨g, hgdeg, hcount⟩ :=
    exists_interior_list_ge_unconditional (ι := Fin (2 ^ 20)) D (k := 2 ^ 19)
      (by norm_num) (by simp) Fintype.card_pos
      (by rw [Fintype.card_fin]; norm_num)
  rw [Fintype.card_fin] at hcount
  set w : Fin (2 ^ 20) → F := fun i => g.eval (D i) with hw
  -- the Round-5 filter IS the rsCodeF filter (merge the two filters; reconcile agreeCount)
  have hsame : (Finset.univ.filter (fun v : Fin (2 ^ 20) → F =>
      v ∈ ReedSolomon.code D (2 ^ 19) ∧ 2 ^ 19 + 1 ≤ agreeCount v w)).card
      = ((rsCodeF D).filter (fun c => 2 ^ 19 + 1 ≤ agree c w)).card := by
    congr 1
    rw [rsCodeF, Finset.filter_filter]
    apply Finset.filter_congr
    intro v _
    rw [agree_eq_agreeCount]
  rw [hsame] at hcount
  -- 91·q < C ≤ q·#filter  ⟹  91 < #filter
  have hgt : 91 < ((rsCodeF D).filter (fun c => 2 ^ 19 + 1 ≤ agree c w)).card := by
    have hchain : 91 * Fintype.card F
        < Fintype.card F *
          ((rsCodeF D).filter (fun c => 2 ^ 19 + 1 ≤ agree c w)).card :=
      lt_of_lt_of_le (ninetyone_mul_q_lt_choose _ hq) hcount
    rw [Nat.mul_comm 91 (Fintype.card F)] at hchain
    exact Nat.lt_of_mul_lt_mul_left hchain
  calc 91 < ((rsCodeF D).filter (fun c => 2 ^ 19 + 1 ≤ agree c w)).card := hgt
    _ ≤ maxList (rsCodeF D) (2 ^ 19 + 1) :=
        Finset.le_sup (f := fun w => ((rsCodeF D).filter
          (fun c => 2 ^ 19 + 1 ≤ agree c w)).card) (Finset.mem_univ w)

/-- **HEADLINE — THE PRIZE THRESHOLD OBJECT, BRACKETED.**  For the in-tree Reed–Solomon code at
the prize's own configuration (`n = 2²⁰`, rate `1/2`, any field with `|F| ≤ 2²⁵⁶`), the threshold
object itself satisfies

  `2¹⁹ + 1  <  aStar(RS, 91)  ≤  750000`,

i.e. the agreement threshold at budget `91` is confined between the capacity edge and a point
1.2% inside the Johnson radius — `δ* ∈ [0.2848, 0.5)` for the genuine code at full prize scale.
Sharpening this window is exactly the open content of the prize. -/
theorem prize_threshold_bracket (D : Fin (2 ^ 20) ↪ F)
    (hq : Fintype.card F ≤ 2 ^ 256) :
    2 ^ 19 + 1 < aStar (rsCodeF D) 91 (by norm_num) ∧
    aStar (rsCodeF D) 91 (by norm_num) ≤ 750000 :=
  aStar_mem_window (rsCodeF D) 91 (by norm_num)
    (maxList_rs_le_91 D) (ninetyone_lt_maxList_rs D hq)

end ArkLib.CodingTheory.PrizeScaleThresholdBracket

/-! ## Axiom audit -/
#print axioms ArkLib.CodingTheory.PrizeScaleThresholdBracket.maxList_rs_le_91
#print axioms ArkLib.CodingTheory.PrizeScaleThresholdBracket.ninetyone_mul_q_lt_choose
#print axioms ArkLib.CodingTheory.PrizeScaleThresholdBracket.ninetyone_lt_maxList_rs
#print axioms ArkLib.CodingTheory.PrizeScaleThresholdBracket.prize_threshold_bracket

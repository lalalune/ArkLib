/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.RimHookConfluence
import Mathlib.Data.Finset.Sort
import Mathlib.Order.Fin.Basic

/-!
# Order-statistic count characterization and re-sorting (#389)

The last analytic ingredient for "rim-hook removal yields a border strip": how the order
statistics `orderEmbOfFin` move when one element of a finset is replaced by a smaller one.

* **`orderEmbOfFin_le_iff_card`** — `β_i ≤ x ↔ i+1 ≤ #{y ∈ s : y ≤ x}` (the count
  characterization of the `i`-th order statistic), the Mathlib-gap lemma.
-/

open Finset

namespace ArkLib.ProximityGap.OrderStatResort

variable {m : ℕ}

/-- **Count characterization of order statistics.** The `i`-th smallest element of `s` is `≤ x`
iff at least `i+1` elements of `s` are `≤ x`. -/
theorem orderEmbOfFin_le_iff_card (s : Finset ℕ) (h : s.card = m) (i : Fin m) (x : ℕ) :
    s.orderEmbOfFin h i ≤ x ↔ (i : ℕ) + 1 ≤ (s.filter (· ≤ x)).card := by
  classical
  set β := s.orderEmbOfFin h with hβ
  set T := Finset.univ.filter (fun j : Fin m => β j ≤ x) with hT
  -- the filtered card counts the order-statistic preimage
  have hcard : (s.filter (· ≤ x)).card = T.card := by
    conv_lhs => rw [← image_orderEmbOfFin_univ s h]
    rw [← hβ, Finset.filter_image,
      Finset.card_image_of_injective _ (β.injective)]
  -- T is down-closed in Fin m
  have hdc : ∀ a b : Fin m, a ≤ b → b ∈ T → a ∈ T := by
    intro a b hab hb
    simp only [hT, Finset.mem_filter, Finset.mem_univ, true_and] at hb ⊢
    exact le_trans (β.monotone hab) hb
  -- its image under Fin.val is an initial segment of ℕ
  have hcardimg : (T.image Fin.val).card = T.card :=
    Finset.card_image_of_injective T Fin.val_injective
  have hpred : ∀ t ∈ T.image Fin.val, 1 ≤ t → t - 1 ∈ T.image Fin.val := by
    intro t ht ht1
    rw [Finset.mem_image] at ht ⊢
    obtain ⟨j, hjT, rfl⟩ := ht
    refine ⟨⟨(j : ℕ) - 1, by omega⟩, ?_, by simp⟩
    exact hdc _ j (by simp [Fin.le_def]) hjT
  have himg : T.image Fin.val = Finset.range T.card := by
    rw [← hcardimg]
    exact RimHookConfluence.downClosed_eq_range hpred
  -- assemble
  rw [hcard]
  have hiff : (β i ≤ x) ↔ (i : ℕ) < T.card := by
    rw [← Finset.mem_range, ← himg, Finset.mem_image]
    constructor
    · intro hx; exact ⟨i, by simp only [hT, Finset.mem_filter, Finset.mem_univ, true_and]; exact hx,
        rfl⟩
    · rintro ⟨j, hjT, hji⟩
      simp only [hT, Finset.mem_filter, Finset.mem_univ, true_and] at hjT
      have : j = i := Fin.val_injective hji
      rwa [this] at hjT
  rw [hiff]; omega

open ArkLib.ProximityGap.RimHookArea

/-- Replacing a bead `p` by the smaller `p - n` can only increase the number of elements `≤ x`. -/
theorem filter_le_card_mono {B B' : Finset ℕ} {n : ℕ}
    (hstep : RemovesRimHook B B' n) (x : ℕ) :
    (B.filter (· ≤ x)).card ≤ (B'.filter (· ≤ x)).card := by
  classical
  obtain ⟨p, hp, hpn, hpn', rfl⟩ := hstep
  apply Finset.card_le_card_of_injOn (fun y => if y = p then p - n else y)
  · intro y hy
    obtain ⟨hyB, hyx⟩ := Finset.mem_filter.mp hy
    simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_insert, Finset.mem_erase]
    constructor
    · split
      · left; rfl
      · rename_i hyp; right; exact ⟨hyp, hyB⟩
    · split
      · omega
      · exact hyx
  · intro a ha b hb hab
    simp only [Finset.coe_filter, Set.mem_setOf_eq] at ha hb
    change (if a = p then p - n else a) = (if b = p then p - n else b) at hab
    by_cases hap : a = p <;> by_cases hbp : b = p
    · rw [hap, hbp]
    · rw [if_pos hap, if_neg hbp] at hab; exact absurd (hab.symm ▸ hb.1) hpn'
    · rw [if_neg hap, if_pos hbp] at hab; exact absurd (hab ▸ ha.1) hpn'
    · rw [if_neg hap, if_neg hbp] at hab; exact hab

/-- Replacing a bead by a smaller one increases the `≤ x` count by at most one. -/
theorem filter_le_card_upper {B B' : Finset ℕ} {n : ℕ}
    (hstep : RemovesRimHook B B' n) (x : ℕ) :
    (B'.filter (· ≤ x)).card ≤ (B.filter (· ≤ x)).card + 1 := by
  classical
  obtain ⟨p, hp, hpn, hpn', rfl⟩ := hstep
  have hsub : (insert (p - n) (B.erase p)).filter (· ≤ x)
      ⊆ insert (p - n) (B.filter (· ≤ x)) := by
    intro y hy
    simp only [Finset.mem_filter, Finset.mem_insert, Finset.mem_erase] at hy ⊢
    obtain ⟨hy1, hy2⟩ := hy
    rcases hy1 with h | ⟨_, hyB⟩
    · exact Or.inl h
    · exact Or.inr ⟨hyB, hy2⟩
  exact le_trans (Finset.card_le_card hsub) (Finset.card_insert_le _ _)

/-- **Containment of order statistics.** Replacing a bead by a smaller one lowers every order
statistic: `β'_k ≤ β_k`. -/
theorem orderEmbOfFin_le_of_removeRimHook {B B' : Finset ℕ} {n m : ℕ}
    (hstep : RemovesRimHook B B' n) (hB : B.card = m) (hB' : B'.card = m) (k : Fin m) :
    B'.orderEmbOfFin hB' k ≤ B.orderEmbOfFin hB k := by
  rw [orderEmbOfFin_le_iff_card B' hB' k (B.orderEmbOfFin hB k)]
  have h1 : (k : ℕ) + 1 ≤ (B.filter (· ≤ B.orderEmbOfFin hB k)).card :=
    (orderEmbOfFin_le_iff_card B hB k _).mp (le_refl _)
  exact le_trans h1 (filter_le_card_mono hstep _)

/-- **Interleaving (lower side).** `β_j ≤ β'_{j+1}`: replacing a bead by a smaller one moves each
order statistic up by at most one position. -/
theorem orderEmbOfFin_pred_le {B B' : Finset ℕ} {n m : ℕ}
    (hstep : RemovesRimHook B B' n) (hB : B.card = m) (hB' : B'.card = m)
    (j : ℕ) (hj : j + 1 < m) :
    B.orderEmbOfFin hB ⟨j, by omega⟩ ≤ B'.orderEmbOfFin hB' ⟨j + 1, hj⟩ := by
  by_contra hc
  push Not at hc
  set x := B'.orderEmbOfFin hB' ⟨j + 1, hj⟩ with hx
  have h1 : j + 2 ≤ (B'.filter (· ≤ x)).card := by
    have := (orderEmbOfFin_le_iff_card B' hB' ⟨j + 1, hj⟩ x).mp (le_refl _)
    simpa using this
  have h2 : (B.filter (· ≤ x)).card ≤ j := by
    by_contra hc2
    push Not at hc2
    have hle : B.orderEmbOfFin hB ⟨j, by omega⟩ ≤ x :=
      (orderEmbOfFin_le_iff_card B hB ⟨j, by omega⟩ x).mpr (by simpa using by omega)
    omega
  have h3 := filter_le_card_upper hstep x
  omega

end ArkLib.ProximityGap.OrderStatResort

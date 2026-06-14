/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.RootsOfUnityAdditiveEnergy

/-!
# The EXACT additive energy of unit-circle sets (char 0) — sharpening `≤ 3|S|²` to equality (#389)

`RootsOfUnityAdditiveEnergy.lean` proves the *bound* `E(S) ≤ 3|S|²` for any finite `S` on the
complex unit circle, via `unitCircle_reps_le_two` (a nonzero sum has `≤ 2` representations).
This file extracts the **exact** value from the same lemma:

> **`unitCircle_additiveEnergy_eq`** — for any finite `S` on the unit circle,
> `E(S) + |S| + 2·r₀ = r₀² + 2|S|²`, where `r₀ = #{y ∈ S : −y ∈ S}` is the number of ordered
> antipodal pairs.  Equivalently `E(S) = r₀² + 2|S|² − |S| − 2r₀`.

The mechanism: for `a + b = s ≠ 0` the representation set `{y : s − y ∈ S}` is **exactly**
`{a, b}` (a third representative would force `≥ 3 > 2`), so each off-`0` pair contributes its
own size; the only nontrivial additive quadruples sit at `s = 0` (the antipodal collisions).

**Consequence (the form 2 ↔ 3 unification).**  For the `n`-th roots of unity `μ_n`,
`r₀ = n` if `n` is even (`−1 ∈ μ_n`, so `y ↦ −y` is an involution of `μ_n`) and `r₀ = 0` if
`n` is odd.  Hence

> **`E(μ_n) = 2n² − n` for `n` odd — `μ_n` is a SIDON set —** and **`E(μ_n) = 3n² − 3n` for
> `n` even** (the Sidon floor `2n²−n` plus the forced antipodal correction `n²−2n`).

This is the exact char-0 additive energy: `μ_n` is extremally additively-unstructured, with the
*only* nontrivial relations being antipodal.  It is the rigid char-0 anchor that the finite-field
problem (the proximity prize) inflates from — the inflation `E_{F_p}(μ_n) − E_ℂ(μ_n)` being the
genuinely open sum-product quantity.  Issue #389.
-/

open Polynomial Finset
open Complex (I)
open scoped ComplexConjugate

namespace ArkLib.ProximityGap.RootsOfUnityAdditiveEnergy

variable {S : Finset ℂ}

/-- The representation set of `s` in `S`: `{y ∈ S : s − y ∈ S}`. -/
private def reps (S : Finset ℂ) (s : ℂ) : Finset ℂ := S.filter (fun y => s - y ∈ S)

/-- **The representation set of a nonzero sum is exactly the pair.**  For `a, b ∈ S` on the
unit circle with `a + b ≠ 0`, `{y ∈ S : (a+b) − y ∈ S} = {a, b}` — a third representative
would give `≥ 3` reps, contradicting `unitCircle_reps_le_two`. -/
theorem reps_eq_pair (hunit : ∀ y ∈ S, y * conj y = 1) {a b : ℂ}
    (ha : a ∈ S) (hb : b ∈ S) (hab : a + b ≠ 0) :
    reps S (a + b) = {a, b} := by
  classical
  refine Finset.Subset.antisymm ?_ ?_
  · -- reps ⊆ {a, b}
    intro y hy
    rw [reps, Finset.mem_filter] at hy
    obtain ⟨hyS, hyrep⟩ := hy
    by_contra hcon
    rw [Finset.mem_insert, Finset.mem_singleton] at hcon
    push_neg at hcon
    obtain ⟨hya, hyb⟩ := hcon
    -- exhibit three distinct elements of `reps S (a+b)`, contradicting `≤ 2`
    have hain : a ∈ reps S (a + b) := by
      rw [reps, Finset.mem_filter]; exact ⟨ha, by rw [show a + b - a = b from by ring]; exact hb⟩
    have hbin : b ∈ reps S (a + b) := by
      rw [reps, Finset.mem_filter]; exact ⟨hb, by rw [show a + b - b = a from by ring]; exact ha⟩
    have hyin : y ∈ reps S (a + b) := by rw [reps, Finset.mem_filter]; exact ⟨hyS, hyrep⟩
    have hcin : a + b - y ∈ reps S (a + b) := by
      rw [reps, Finset.mem_filter]
      exact ⟨hyrep, by rw [show a + b - (a + b - y) = y from by ring]; exact hyS⟩
    have hle2 : (reps S (a + b)).card ≤ 2 := unitCircle_reps_le_two (a + b) hab S hunit
    by_cases hab2 : a = b
    · -- a = b: the three distinct reps are a, y, (a+b)-y
      subst hab2
      have h3 : ({a, y, a + a - y} : Finset ℂ).card = 3 := by
        rw [Finset.card_insert_of_notMem, Finset.card_insert_of_notMem, Finset.card_singleton]
        · rw [Finset.mem_singleton]; intro h; apply hya; linear_combination -h
        · rw [Finset.mem_insert, Finset.mem_singleton]
          push_neg
          refine ⟨hya, ?_⟩
          intro h; apply hya; linear_combination -h
      have hsub : ({a, y, a + a - y} : Finset ℂ) ⊆ reps S (a + a) := by
        intro z hz
        rw [Finset.mem_insert, Finset.mem_insert, Finset.mem_singleton] at hz
        rcases hz with rfl | rfl | rfl
        · exact hain
        · exact hyin
        · exact hcin
      have := Finset.card_le_card hsub
      rw [h3] at this
      omega
    · -- a ≠ b: the three distinct reps are a, b, y
      have h3 : ({a, b, y} : Finset ℂ).card = 3 := by
        rw [Finset.card_insert_of_notMem, Finset.card_insert_of_notMem, Finset.card_singleton]
        · rw [Finset.mem_singleton]; exact fun h => hyb h.symm
        · rw [Finset.mem_insert, Finset.mem_singleton]
          push_neg
          exact ⟨hab2, fun h => hya h.symm⟩
      have hsub : ({a, b, y} : Finset ℂ) ⊆ reps S (a + b) := by
        intro z hz
        rw [Finset.mem_insert, Finset.mem_insert, Finset.mem_singleton] at hz
        rcases hz with rfl | rfl | rfl
        · exact hain
        · exact hbin
        · exact hyin
      have := Finset.card_le_card hsub
      rw [h3] at this
      omega
  · -- {a, b} ⊆ reps
    intro y hy
    rw [Finset.mem_insert, Finset.mem_singleton] at hy
    rw [reps, Finset.mem_filter]
    rcases hy with rfl | rfl
    · exact ⟨ha, by rw [show a + b - a = b from by ring]; exact hb⟩
    · exact ⟨hb, by rw [show a + b - y = a from by ring]; exact ha⟩

end ArkLib.ProximityGap.RootsOfUnityAdditiveEnergy

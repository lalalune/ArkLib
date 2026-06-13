/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.RootsOfUnityAdditiveEnergy
import ArkLib.Data.CodingTheory.ProximityGap.AdditiveEnergySidonModNeg

/-!
# Discharging `SidonModNeg` for unit-circle sets — the char-0 anchor made UNCONDITIONAL (#389)

The campaign's exact additive-energy theorem
`AdditiveEnergySidonModNeg.additiveEnergy_eq_of_sidonModNeg : additiveEnergy G = 3|G|² − 3|G|`
holds for any negation-closed set satisfying the structural hypothesis `SidonModNeg G` (the only
additive coincidences are trivial or zero-sum).  But `SidonModNeg` was an **undischarged
hypothesis** everywhere — no concrete set was shown to satisfy it.

This file discharges it for the case that matters — the complex unit circle (hence the roots of
unity) — from the in-tree `unitCircle_reps_le_two` (a nonzero sum has `≤ 2` representations):

> **`unitCircle_sidonModNeg`** — every finite set `S` on the complex unit circle satisfies
> `SidonModNeg S`.

Composed with the campaign's energy theorem this gives the **unconditional** exact additive
energy of any negation-closed unit-circle set — in particular `E(μ_n) = 3n² − 3n` for even `n`
(the rigid char-0 anchor: `μ_n`'s only nontrivial additive relations are antipodal).  The engine
is `unitCircle_filter_eq_pair`: a nonzero sum `a + b` has representation set **exactly** `{a, b}`,
because a third representative would force `≥ 3 > 2` reps.  This is the bridge that turns the
campaign's conditional energy/Sidon results into theorems about the actual smooth domain.
Issue #389.
-/

open Polynomial Finset
open scoped ComplexConjugate

namespace ArkLib.ProximityGap.RootsOfUnityAdditiveEnergy

variable {S : Finset ℂ}

/-- **A nonzero sum's representation set is exactly the pair.**  For `a, b` on the unit circle
with `a + b ≠ 0`, `{y ∈ S : (a+b) − y ∈ S} = {a, b}` — a third representative `y ∉ {a,b}`
produces three distinct representatives, contradicting `unitCircle_reps_le_two`. -/
theorem unitCircle_filter_eq_pair (hunit : ∀ y ∈ S, y * conj y = 1) {a b : ℂ}
    (ha : a ∈ S) (hb : b ∈ S) (hab : a + b ≠ 0) :
    S.filter (fun y => (a + b) - y ∈ S) = {a, b} := by
  classical
  have hle2 : (S.filter (fun y => (a + b) - y ∈ S)).card ≤ 2 :=
    unitCircle_reps_le_two (a + b) hab S hunit
  have hain : a ∈ S.filter (fun y => (a + b) - y ∈ S) := by
    rw [Finset.mem_filter]; exact ⟨ha, by rw [show a + b - a = b from by ring]; exact hb⟩
  have hbin : b ∈ S.filter (fun y => (a + b) - y ∈ S) := by
    rw [Finset.mem_filter]; exact ⟨hb, by rw [show a + b - b = a from by ring]; exact ha⟩
  refine Finset.Subset.antisymm ?_ ?_
  · intro y hy
    rw [Finset.mem_filter] at hy
    obtain ⟨hyS, hyrep⟩ := hy
    by_contra hcon
    rw [Finset.mem_insert, Finset.mem_singleton] at hcon
    push_neg at hcon
    obtain ⟨hya, hyb⟩ := hcon
    have hyin : y ∈ S.filter (fun z => (a + b) - z ∈ S) := by
      rw [Finset.mem_filter]; exact ⟨hyS, hyrep⟩
    have hcin : a + b - y ∈ S.filter (fun z => (a + b) - z ∈ S) := by
      rw [Finset.mem_filter]
      exact ⟨hyrep, by rw [show a + b - (a + b - y) = y from by ring]; exact hyS⟩
    by_cases hab2 : a = b
    · -- a = b: the three distinct reps are a, y, (a+a)-y
      subst hab2
      have h3 : ({a, y, a + a - y} : Finset ℂ).card = 3 := by
        rw [Finset.card_insert_of_notMem, Finset.card_insert_of_notMem, Finset.card_singleton]
        · rw [Finset.mem_singleton]; intro h; exact hya (by linear_combination h / 2)
        · rw [Finset.mem_insert, Finset.mem_singleton]
          push_neg
          exact ⟨fun h => hya h.symm, fun h => hya (by linear_combination h)⟩
      have hsub : ({a, y, a + a - y} : Finset ℂ) ⊆ S.filter (fun z => (a + a) - z ∈ S) := by
        intro z hz
        rw [Finset.mem_insert, Finset.mem_insert, Finset.mem_singleton] at hz
        rcases hz with rfl | rfl | rfl
        · exact hain
        · exact hyin
        · exact hcin
      have := Finset.card_le_card hsub
      rw [h3] at this; omega
    · -- a ≠ b: the three distinct reps are a, b, y
      have h3 : ({a, b, y} : Finset ℂ).card = 3 := by
        rw [Finset.card_insert_of_notMem, Finset.card_insert_of_notMem, Finset.card_singleton]
        · rw [Finset.mem_singleton]; exact fun h => hyb h.symm
        · rw [Finset.mem_insert, Finset.mem_singleton]
          push_neg
          exact ⟨hab2, fun h => hya h.symm⟩
      have hsub : ({a, b, y} : Finset ℂ) ⊆ S.filter (fun z => (a + b) - z ∈ S) := by
        intro z hz
        rw [Finset.mem_insert, Finset.mem_insert, Finset.mem_singleton] at hz
        rcases hz with rfl | rfl | rfl
        · exact hain
        · exact hbin
        · exact hyin
      have := Finset.card_le_card hsub
      rw [h3] at this; omega
  · intro y hy
    rw [Finset.mem_insert, Finset.mem_singleton] at hy
    rcases hy with rfl | rfl
    · exact hain
    · exact hbin

/-- **Unit-circle sets are Sidon-modulo-negation.**  Every finite `S` on the complex unit circle
satisfies `AdditiveEnergySidonModNeg.SidonModNeg S`: the only additive coincidences `a+b=c+d` are
the trivial ones or the zero-sum ones.  This DISCHARGES the standing hypothesis of the campaign's
exact-energy theorem for the roots of unity. -/
theorem unitCircle_sidonModNeg (hunit : ∀ y ∈ S, y * conj y = 1) :
    AdditiveEnergySidonModNeg.SidonModNeg S := by
  classical
  intro a ha b hb c hc d hd hsum
  by_cases hab : a + b = 0
  · exact Or.inr (Or.inr hab)
  · have hpair := unitCircle_filter_eq_pair hunit ha hb hab
    have hcin : c ∈ S.filter (fun y => (a + b) - y ∈ S) := by
      rw [Finset.mem_filter]
      exact ⟨hc, by rw [hsum, show c + d - c = d from by ring]; exact hd⟩
    rw [hpair, Finset.mem_insert, Finset.mem_singleton] at hcin
    rcases hcin with rfl | rfl
    · exact Or.inl ⟨rfl, by linear_combination hsum⟩
    · exact Or.inr (Or.inl ⟨by linear_combination hsum, rfl⟩)

/-- **The exact char-0 additive energy of a negation-closed unit-circle set, UNCONDITIONAL.**
Composing the discharger with the campaign's energy theorem: any finite negation-closed `S` on
the unit circle (e.g. the even-order roots of unity `μ_n`) has additive energy EXACTLY
`3|S|² − 3|S| = 3|S|(|S|−1)` — the Sidon floor plus the forced antipodal correction.  This is
the rigid char-0 anchor the finite-field proximity prize inflates from. -/
theorem unitCircle_negClosed_additiveEnergy_eq (hunit : ∀ y ∈ S, y * conj y = 1)
    (hneg : ∀ y ∈ S, -y ∈ S) :
    AdditiveEnergyRepBound.additiveEnergy S = 3 * S.card ^ 2 - 3 * S.card := by
  have h0 : (0 : ℂ) ∉ S := fun h => by simpa using hunit 0 h
  exact AdditiveEnergySidonModNeg.additiveEnergy_eq_of_sidonModNeg
    two_ne_zero h0 hneg (unitCircle_sidonModNeg hunit)

end ArkLib.ProximityGap.RootsOfUnityAdditiveEnergy

-- Axiom audit (expected: propext, Classical.choice, Quot.sound only)
#print axioms ArkLib.ProximityGap.RootsOfUnityAdditiveEnergy.unitCircle_filter_eq_pair
#print axioms ArkLib.ProximityGap.RootsOfUnityAdditiveEnergy.unitCircle_sidonModNeg
#print axioms ArkLib.ProximityGap.RootsOfUnityAdditiveEnergy.unitCircle_negClosed_additiveEnergy_eq

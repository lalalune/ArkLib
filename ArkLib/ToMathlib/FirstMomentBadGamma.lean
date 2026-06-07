/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/

import ArkLib.Data.CodingTheory.Connections.GKL24FirstMoment

/-!
# Sharpened in-tree per-codeword first-moment count (toward GKL24's `b = δ·n`)

This file proves a *strictly sharper* in-tree upper bound on the per-codeword bad-`γ` count
`|mcaBadWitness C δ u₀ u₁ w|` than the `b = n` bound established in
`Connections/GKL24FirstMoment.lean` (`mcaBadWitness_card_le_card`). It narrows the gap to
GCXK25's first-moment count `b = δ·n` by a factor of two, using **only** in-tree content (no
GKL24/GCXK25 hypothesis).

## The pairwise-distinct-witness argument

Fix a codeword `w ∈ MC` and a stack `(u₀, u₁)`. Suppose `γ ≠ γ'` are *two distinct* bad combining
points witnessed by `w`, with witness sets `S, S'` (each of size `≥ (1-δ)·n`). On `S ∩ S'` we have

  `u₀ + γ • u₁ = w = u₀ + γ' • u₁`,

so `(γ - γ') • u₁ = 0` there, and since `γ ≠ γ'` this forces `u₁ = 0` on all of `S ∩ S'`. Hence

  `S ∩ S' ⊆ zeros u₁ := {i : u₁ i = 0}`.

Inclusion–exclusion gives `|S ∩ S'| ≥ |S| + |S'| - n ≥ (1 - 2δ)·n`, while
`|zeros u₁| = n - |secondSupport u₁|`. Combining,

  `(1 - 2δ)·n ≤ |zeros u₁| = n - |secondSupport u₁|`  ⟹  `|secondSupport u₁| ≤ 2·δ·n`.

So **whenever `w` witnesses at least two bad points**, its support — and therefore (via the
existing single-codeword determinacy) its whole bad set — is bounded by `2·δ·n`:

  `|mcaBadWitness w| ≤ |secondSupport u₁| ≤ 2·δ·n`.

## What is proven here (in-tree, `sorry`-free, axiom-clean)

* `secondSupport_card_le_two_delta_of_two_witnesses` — if two distinct bad `γ` are witnessed by
  `w`, then `|secondSupport u₁| ≤ 2·δ·n`.
* `mcaBadWitness_card_le_two_delta_mul_card` — the sharpened per-codeword count
  `|mcaBadWitness w| ≤ max 1 (2·δ·n)` (the `max 1` absorbs the degenerate `≤ 1`-witness case).

## What this file does *not* close

This is the factor-2 in-tree sharpening (`b = max 1 (2·δ·n)`), **not** GCXK25's sharp
`b = δ·n`. The remaining factor-2 (and the `+1`) is precisely where GKL24's *global* charging over
the close-codeword list (their Lemma 1 / Corollary 1) beats the pairwise single-codeword argument;
that remains the named `GKL24FirstMomentResidual`.

## References

* [ABF26] Arnon, Boneh, Fenzi. Theorem 5.1.
* [GCXK25] Gao, Cai, Xu, Kan. eprint 2025/870, Theorem 3, Lemma 1.
* [GKL24] Guruswami, Kumar, Liu (agree-domain intersection / first-moment count).
-/

set_option linter.unusedFintypeInType false
set_option linter.unusedDecidableInType false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 1600000

namespace ProximityGap

open NNReal Code Finset
open scoped ProbabilityTheory BigOperators

section
variable {ι : Type} [Fintype ι] [Nonempty ι] [DecidableEq ι]
variable {F : Type} [Field F] [Fintype F] [DecidableEq F]

/-- The **zero set** of the second word `u₁`: the coordinates where it vanishes. It is the
complement of `secondSupport u₁` inside `univ`, and on it the line `u₀ + γ • u₁` is independent
of `γ`. -/
def secondZeros (u₁ : ι → F) : Finset ι :=
  Finset.univ.filter (fun i => u₁ i = 0)

/-- `secondZeros` and `secondSupport` partition `univ`: `|secondSupport| + |secondZeros| = n`. -/
theorem secondSupport_card_add_secondZeros_card (u₁ : ι → F) :
    (secondSupport u₁).card + (secondZeros u₁).card = Fintype.card ι := by
  classical
  rw [secondSupport, secondZeros]
  rw [Finset.filter_card_add_filter_neg_card_eq_card (p := fun i => u₁ i ≠ 0)]
  · simp
  · intro i
    exact Classical.dec _

/-- If a coordinate lies in both witness sets `S, S'` of two **distinct** bad combining points
`γ ≠ γ'` (both witnessed by the same `w`), then `u₁` vanishes there. -/
theorem u1_zero_of_mem_both_witness
    (u₀ u₁ w : ι → F) {γ γ' : F} (hγ : γ ≠ γ') {i : ι}
    (h : w i = u₀ i + γ • u₁ i) (h' : w i = u₀ i + γ' • u₁ i) :
    u₁ i = 0 := by
  have heq : γ • u₁ i = γ' • u₁ i := by
    have := h.symm.trans h'
    simpa using add_left_cancel this
  rw [smul_eq_mul, smul_eq_mul] at heq
  have : (γ - γ') * u₁ i = 0 := by ring_nf; linear_combination heq
  rcases mul_eq_zero.mp this with hsub | hu
  · exact absurd (sub_eq_zero.mp hsub) hγ
  · exact hu

end

section
variable {ι : Type} [Fintype ι] [Nonempty ι] [DecidableEq ι]
variable {F : Type} [Field F] [Fintype F] [DecidableEq F]

open CodingTheory.Bridge

/-- **Pairwise sharpening of the support.** If a fixed codeword `w ∈ MC` witnesses two *distinct*
bad combining points `γ ≠ γ'`, then the support of `u₁` is at most `2·δ·n`.

Proof: the two witness sets `S, S'` each have size `≥ (1-δ)·n`, so by inclusion–exclusion their
intersection has size `≥ (1-2δ)·n`; on the intersection `u₁` vanishes
(`u1_zero_of_mem_both_witness`), so `S ∩ S' ⊆ secondZeros u₁`. Then
`|secondSupport u₁| = n - |secondZeros u₁| ≤ n - (1-2δ)·n = 2·δ·n`. -/
theorem secondSupport_card_le_two_delta_of_two_witnesses
    (MC : Submodule F (ι → F)) (δ : ℝ≥0) (u₀ u₁ w : ι → F)
    {γ γ' : F} (hγ : γ ≠ γ')
    (hmem : γ ∈ mcaBadWitness (F := F) (MC : Set (ι → F)) δ u₀ u₁ w)
    (hmem' : γ' ∈ mcaBadWitness (F := F) (MC : Set (ι → F)) δ u₀ u₁ w) :
    ((secondSupport u₁).card : ℝ) ≤ 2 * (δ : ℝ) * (Fintype.card ι : ℝ) := by
  classical
  rw [mcaBadWitness, Finset.mem_filter] at hmem hmem'
  obtain ⟨S, hScard, hwline, _⟩ := hmem.2
  obtain ⟨S', hS'card, hwline', _⟩ := hmem'.2
  -- `S ∩ S' ⊆ secondZeros u₁`.
  have hsub : S ∩ S' ⊆ secondZeros u₁ := by
    intro i hi
    rw [Finset.mem_inter] at hi
    rw [secondZeros, Finset.mem_filter]
    refine ⟨Finset.mem_univ _, ?_⟩
    exact u1_zero_of_mem_both_witness u₀ u₁ w hγ (hwline i hi.1) (hwline' i hi.2)
  -- Cardinality of the intersection from inclusion–exclusion (ℕ-level, real later).
  have hincl : (S.card : ℝ) + (S'.card : ℝ) ≤
      (Fintype.card ι : ℝ) + ((S ∩ S').card : ℝ) := by
    have h := Finset.card_union_add_card_inter S S'
    have hunion : (S ∪ S').card ≤ Fintype.card ι := by
      calc (S ∪ S').card ≤ (Finset.univ : Finset ι).card := Finset.card_le_card (by
              intro x _; exact Finset.mem_univ _)
        _ = Fintype.card ι := Finset.card_univ
    have : ((S ∪ S').card : ℝ) + ((S ∩ S').card : ℝ) = (S.card : ℝ) + (S'.card : ℝ) := by
      exact_mod_cast h
    have hu : ((S ∪ S').card : ℝ) ≤ (Fintype.card ι : ℝ) := by exact_mod_cast hunion
    linarith
  -- `S ∩ S'` is inside `secondZeros u₁`.
  have hinterle : ((S ∩ S').card : ℝ) ≤ ((secondZeros u₁).card : ℝ) := by
    exact_mod_cast Finset.card_le_card hsub
  -- The witness-set lower bounds (cast through ℝ≥0 → ℝ).
  have hSlb : (1 - (δ : ℝ)) * (Fintype.card ι : ℝ) ≤ (S.card : ℝ) := by
    have : ((1 - δ) * Fintype.card ι : ℝ≥0) ≤ (S.card : ℝ≥0) := hScard
    have h2 : ((1 - δ : ℝ≥0) : ℝ) * (Fintype.card ι : ℝ) ≤ (S.card : ℝ) := by
      have := (NNReal.coe_le_coe.mpr this)
      push_cast at this ⊢
      convert this using 2
    calc (1 - (δ : ℝ)) * (Fintype.card ι : ℝ)
        ≤ ((1 - δ : ℝ≥0) : ℝ) * (Fintype.card ι : ℝ) := by
          apply mul_le_mul_of_nonneg_right _ (by positivity)
          have : ((1 - δ : ℝ≥0) : ℝ) = max (1 - (δ : ℝ)) 0 := by
            rw [NNReal.coe_sub_def]; simp
          rw [this]; exact le_max_left _ _
      _ ≤ (S.card : ℝ) := h2
  have hS'lb : (1 - (δ : ℝ)) * (Fintype.card ι : ℝ) ≤ (S'.card : ℝ) := by
    have : ((1 - δ) * Fintype.card ι : ℝ≥0) ≤ (S'.card : ℝ≥0) := hS'card
    have h2 : ((1 - δ : ℝ≥0) : ℝ) * (Fintype.card ι : ℝ) ≤ (S'.card : ℝ) := by
      have := (NNReal.coe_le_coe.mpr this)
      push_cast at this ⊢
      convert this using 2
    calc (1 - (δ : ℝ)) * (Fintype.card ι : ℝ)
        ≤ ((1 - δ : ℝ≥0) : ℝ) * (Fintype.card ι : ℝ) := by
          apply mul_le_mul_of_nonneg_right _ (by positivity)
          have : ((1 - δ : ℝ≥0) : ℝ) = max (1 - (δ : ℝ)) 0 := by
            rw [NNReal.coe_sub_def]; simp
          rw [this]; exact le_max_left _ _
      _ ≤ (S'.card : ℝ) := h2
  -- Combine: |secondZeros| ≥ (1-2δ)·n.
  have hzeros_lb : (1 - 2 * (δ : ℝ)) * (Fintype.card ι : ℝ) ≤ ((secondZeros u₁).card : ℝ) := by
    nlinarith [hincl, hinterle, hSlb, hS'lb]
  -- |secondSupport| = n - |secondZeros|.
  have hpart : ((secondSupport u₁).card : ℝ) + ((secondZeros u₁).card : ℝ) =
      (Fintype.card ι : ℝ) := by
    exact_mod_cast secondSupport_card_add_secondZeros_card u₁
  nlinarith [hzeros_lb, hpart]

/-- **Sharpened per-codeword first-moment count.** For a `Submodule` code `MC` and a fixed
codeword `w ∈ MC`,

  `|mcaBadWitness w| ≤ max 1 (2·δ·n)`.

This strictly improves the in-tree `b = n` count of `mcaBadWitness_card_le_card` toward GCXK25's
sharp `b = δ·n` (it is within a factor of `2` and an additive `1`). The `max 1` absorbs the
degenerate case of `≤ 1` witness; whenever there are `≥ 2` bad points, the pairwise argument
(`secondSupport_card_le_two_delta_of_two_witnesses`) plus single-codeword determinacy
(`mcaBadWitness_card_le_support`) bounds the count by `2·δ·n`. -/
theorem mcaBadWitness_card_le_two_delta_mul_card
    (MC : Submodule F (ι → F)) (δ : ℝ≥0) (u₀ u₁ w : ι → F)
    (hw : w ∈ (MC : Set (ι → F))) :
    ((mcaBadWitness (F := F) (MC : Set (ι → F)) δ u₀ u₁ w).card : ℝ) ≤
      max 1 (2 * (δ : ℝ) * (Fintype.card ι : ℝ)) := by
  classical
  set W := mcaBadWitness (F := F) (MC : Set (ι → F)) δ u₀ u₁ w with hW
  rcases le_or_lt W.card 1 with hle | hgt
  · calc ((W.card : ℝ)) ≤ 1 := by exact_mod_cast hle
      _ ≤ max 1 (2 * (δ : ℝ) * (Fintype.card ι : ℝ)) := le_max_left _ _
  · -- Two distinct witnesses exist, so the support is `≤ 2δn`.
    obtain ⟨γ, hγ, γ', hγ', hne⟩ := Finset.one_lt_card.mp hgt
    have hsupp : ((secondSupport u₁).card : ℝ) ≤ 2 * (δ : ℝ) * (Fintype.card ι : ℝ) :=
      secondSupport_card_le_two_delta_of_two_witnesses MC δ u₀ u₁ w hne hγ hγ'
    have hcard : ((W.card : ℝ)) ≤ ((secondSupport u₁).card : ℝ) := by
      rw [hW]
      exact_mod_cast mcaBadWitness_card_le_support MC δ u₀ u₁ w hw
    calc ((W.card : ℝ)) ≤ ((secondSupport u₁).card : ℝ) := hcard
      _ ≤ 2 * (δ : ℝ) * (Fintype.card ι : ℝ) := hsupp
      _ ≤ max 1 (2 * (δ : ℝ) * (Fintype.card ι : ℝ)) := le_max_right _ _

end

end ProximityGap

/- Axiom audit for the sharpened first-moment per-codeword bounds. -/
#print axioms ProximityGap.u1_zero_of_mem_both_witness
#print axioms ProximityGap.secondSupport_card_le_two_delta_of_two_witnesses
#print axioms ProximityGap.mcaBadWitness_card_le_two_delta_mul_card

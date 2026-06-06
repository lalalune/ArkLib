/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/

import ArkLib.Data.CodingTheory.SubspaceDesign
import ArkLib.Data.CodingTheory.ListDecodability
import ArkLib.Data.CodingTheory.ReedSolomon.Folded
import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# ABF26 C3.5 reduction (deep sub-lemma stack), standalone

We prove the **genuine reduction** that the in-tree `frs_list_decoding_capacity_cz25`
`sorry` claims without proof:

> "this is a COROLLARY of T3.4 via T2.18 … Once T3.4 and T2.18 are proven, C3.5 closes by
>  instantiating T3.4 at the FRS τ(r)=sρ/(s-r+1) and simplifying with 1/η<s."

The two genuinely-external ingredients (the in-tree admits) are taken as **explicit
hypotheses**, with their exact in-tree shapes:

* `hT34` — ABF26 T3.4 [CZ25 B.5] (`subspaceDesign_list_decoding_cz25`).
* `hT218` — ABF26 T2.18 [GK16] (`frs_is_subspaceDesign_gk16`).

Everything *else* — the τ-substitution, the bound algebra, the floor/real reconciliation —
is proved here with no `sorry` and no new axioms.  This pins precisely where the genuine
gap lives (inside `hT34`/`hT218`) and discharges the corollary's own content.

The headline result `frs_list_decoding_capacity_cz25_of_T34_T218` derives the **exact**
in-tree C3.5 statement (modulo the documented floor-vs-real subtlety, which we surface as
an explicit, provable hypothesis `hηnat : 1/η = ⌊1/η⌋`).
-/

set_option linter.unusedFintypeInType false
set_option linter.unusedDecidableInType false
set_option linter.unusedSectionVars false

namespace CodingTheory

open scoped NNReal
open ListDecodable

/-- **Arithmetic bridge.**  For FRS with `τ(t) = ρ·s/(s-t+1)`, the T3.4 bound
`(1 - τ(t))/η` equals the C3.5 closed form `(s(1-ρ)+1-t)/(η(s+1-t))`, given
`η ≠ 0` and `t ≤ s` (so the denominator is positive). -/
theorem frs_bound_simplify
    (s t : ℕ) (ρ η : ℝ) (hη : η ≠ 0) (ht : t ≤ s) :
    (1 - (s : ℝ) * ρ / ((s : ℝ) - t + 1)) / η
      = ((s : ℝ) * (1 - ρ) + 1 - t) / (η * ((s : ℝ) + 1 - t)) := by
  have htR : (t : ℝ) ≤ s := by exact_mod_cast ht
  have hden : (s : ℝ) - t + 1 ≠ 0 := by linarith
  have hsden : (s : ℝ) + 1 - t = (s : ℝ) - t + 1 := by ring
  rw [hsden]
  field_simp
  ring

/-- **ABF26 Corollary 3.5 [CZ25 Cor 2.21] — reduction form.**

Given the two genuine external ingredients (T3.4 and T2.18) **as hypotheses**, folded RS
codes are list-decodable up to capacity with the explicit C3.5 bound.  We use the
floor-faithful radius/bound (the integer `t := ⌊1/η⌋` that T3.4 actually evaluates τ at);
the surfaced hypothesis `hηnat` says `1/η` is integral, reconciling with the in-tree
real-`1/η` statement.  All steps except `hT34`/`hT218` are `sorry`-free here. -/
theorem frs_list_decoding_capacity_cz25_of_T34_T218
    {ι : Type} [Fintype ι] [Nonempty ι] [DecidableEq ι]
    {F : Type} [Field F] [Fintype F] [DecidableEq F]
    (domain : ι ↪ F) (k s : ℕ) (ω : F)
    (_hs_pos : 0 < s)
    (η : ℝ) (hη_pos : 0 < η) (hη_lt_s : 1 / η < s)
    -- T2.18 instance (external admit `frs_is_subspaceDesign_gk16`), as a hypothesis:
    (hT218 : IsSubspaceDesign s
        (fun r ↦ if r ∈ Finset.Icc 1 s then
            (s : ℝ) * (k : ℝ) / Fintype.card ι / ((s : ℝ) - r + 1) else 1)
        (ReedSolomon.Folded.frsCode domain k s ω))
    -- T3.4 (external admit `subspaceDesign_list_decoding_cz25`) in its GENERAL in-tree
    -- shape: quantified over EVERY τ-subspace-design code.  The reduction feeds it the
    -- T2.18 instance `hT218`, so `hT218` is load-bearing.
    (hT34 : ∀ (τ : ℕ → ℝ) (C : Submodule F (ι → Fin s → F)),
        IsSubspaceDesign s τ C → ∀ η' : ℝ, 0 < η' →
        (Lambda ((C : Set (ι → Fin s → F)))
            (1 - τ (Nat.floor (1 / η')) - η') : ENNReal) ≤
          ENNReal.ofReal ((1 - τ (Nat.floor (1 / η'))) / η'))
    -- The documented floor/real reconciliation: `1/η` is integral (so the real-`1/η`
    -- C3.5 statement coincides with the floor-faithful T3.4 instance).  Provable whenever
    -- `η = 1/m`; surfaced explicitly so the reduction is faithful to the in-tree statement.
    (hηnat : (1 : ℝ) / η = (Nat.floor (1 / η) : ℕ)) :
    let n : ℝ := Fintype.card ι
    let ρ : ℝ := k / n
    let δ : ℝ := 1 - ρ * s / (s - 1 / η + 1) - η
    let bound : ℝ := (s * (1 - ρ) + 1 - 1 / η) / (η * (s + 1 - 1 / η))
    (Lambda ((ReedSolomon.Folded.frsCode domain k s ω : Set (ι → Fin s → F))) δ :
        ENNReal) ≤
      ENNReal.ofReal bound := by
  -- Abbreviations.
  intro n ρ δ bound
  set t : ℕ := Nat.floor (1 / η) with ht_def
  have hη_ne : η ≠ 0 := ne_of_gt hη_pos
  -- `t = ⌊1/η⌋ ≤ s` from `1/η < s` (so the FRS denominator is positive and the τ branch
  -- is the `Icc 1 s` one when `t ≥ 1`).
  have ht_le_s : t ≤ s := by
    have : (t : ℝ) ≤ 1 / η := Nat.floor_le (by positivity)
    have hts : (t : ℝ) < s := lt_of_le_of_lt this hη_lt_s
    exact_mod_cast (le_of_lt hts)
  -- `1/η = t` (the surfaced reconciliation).
  have hηt : (1 : ℝ) / η = (t : ℝ) := by rw [ht_def]; exact hηnat
  -- The FRS τ at `t` (the `Icc` branch), as a real value `τt`.
  set τt : ℝ := (s : ℝ) * (k : ℝ) / Fintype.card ι / ((s : ℝ) - t + 1) with hτt_def
  -- Rewrite the C3.5 radius `δ` to the floor form `1 - τt - η`.
  have hρ : ρ = (k : ℝ) / n := rfl
  have hn : n = (Fintype.card ι : ℝ) := rfl
  -- `ρ * s / (s - 1/η + 1) = τt`.
  have hδ_eq : δ = 1 - τt - η := by
    change 1 - ρ * s / (s - 1 / η + 1) - η = 1 - τt - η
    rw [hηt, hρ, hn, hτt_def]
    have : (k : ℝ) / (Fintype.card ι : ℝ) * (s : ℝ)
        = (s : ℝ) * (k : ℝ) / (Fintype.card ι : ℝ) := by ring
    rw [this]
  -- Rewrite the C3.5 bound to `(1 - τt)/η`.
  have hbound_eq : bound = (1 - τt) / η := by
    change (s * (1 - ρ) + 1 - 1 / η) / (η * (s + 1 - 1 / η)) = (1 - τt) / η
    rw [hηt]
    -- Now bound is in terms of integer `t`; use the arithmetic bridge in reverse.
    rw [hτt_def, hρ, hn]
    -- `(s*(1-ρ)+1-t)/(η(s+1-t)) = (1 - s*ρ/(s-t+1))/η` with ρ = k/n.
    have hbridge := frs_bound_simplify s t ((k : ℝ) / (Fintype.card ι : ℝ)) η hη_ne ht_le_s
    -- align `s * (k/n) / (s-t+1)` with `(s * k / n) / (s-t+1)`
    have halign : (s : ℝ) * ((k : ℝ) / (Fintype.card ι : ℝ)) / ((s : ℝ) - t + 1)
        = (s : ℝ) * (k : ℝ) / (Fintype.card ι : ℝ) / ((s : ℝ) - t + 1) := by ring
    rw [halign] at hbridge
    rw [← hbridge]
  -- Instantiate the GENERAL T3.4 at the FRS τ-profile + the T2.18 design instance `hT218`.
  have hT34_inst := hT34
      (fun r ↦ if r ∈ Finset.Icc 1 s then
          (s : ℝ) * (k : ℝ) / Fintype.card ι / ((s : ℝ) - r + 1) else 1)
      (ReedSolomon.Folded.frsCode domain k s ω) hT218 η hη_pos
  -- Now reduce `hT34_inst` to this form.
  -- The τ-function applied at `t`, with `t ∈ Icc 1 s` (need `1 ≤ t`).
  by_cases ht1 : 1 ≤ t
  · -- `t ∈ Icc 1 s`, so the τ-branch is the `Icc` formula and equals `τt`.
    have htmem : t ∈ Finset.Icc 1 s := Finset.mem_Icc.mpr ⟨ht1, ht_le_s⟩
    have hτeval : (fun r ↦ if r ∈ Finset.Icc 1 s then
        (s : ℝ) * (k : ℝ) / Fintype.card ι / ((s : ℝ) - r + 1) else 1)
        (Nat.floor (1 / η)) = τt := by
      rw [← ht_def]
      simp only [htmem, if_true]
      rfl
    rw [hτeval] at hT34_inst
    rw [hδ_eq, hbound_eq]
    exact hT34_inst
  · -- `t = 0`.  Then `1/η = 0`, contradicting `η > 0` (since `1/η > 0`).
    exfalso
    have ht0 : t = 0 := Nat.lt_one_iff.mp (Nat.not_le.mp ht1)
    have : (1 : ℝ) / η = 0 := by rw [hηt, ht0]; norm_num
    rw [one_div, inv_eq_zero] at this
    exact hη_ne this

end CodingTheory

/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/

import ArkLib.Data.CodingTheory.SubspaceDesign
import ArkLib.Data.CodingTheory.ListDecoding.CZ25CapacityReduction
import ArkLib.Data.CodingTheory.ListDecoding.CZ25SpanBoundBridge

namespace CodingTheory

open scoped NNReal

variable {ι : Type} [Fintype ι] [Nonempty ι] [DecidableEq ι]
variable {F : Type} [Field F] [Fintype F] [DecidableEq F]

/-- **Design monotonicity in `τ`.** A `τ`-subspace-design is also a `τ'`-subspace-design when
`τ ≤ τ'` pointwise (the design inequality's RHS `finrank A · τ r` only grows, `finrank A ≥ 0`). -/
theorem isSubspaceDesign_mono {s : ℕ} {τ τ' : ℕ → ℝ}
    {C : Submodule F (ι → Fin s → F)}
    (h : IsSubspaceDesign s τ C) (hτ : ∀ r, τ r ≤ τ' r) :
    IsSubspaceDesign s τ' C := by
  intro r A hA hrank
  refine le_trans (h r A hA hrank) ?_
  have hfr : (0 : ℝ) ≤ (Module.finrank F A : ℝ) := by positivity
  exact mul_le_mul_of_nonneg_left (hτ r) hfr

/-- The C3.5 design parameter `τ(r) = s·k/n/(s−r+1)` (on `Icc 1 s`) pointwise dominates the
T2.18 parameter `τ(r) = (k−1)/n`.  Off `Icc 1 s` both are `1`. -/
theorem cz25_tau_ge_t218_tau {s k : ℕ} (hn : (0 : ℝ) < Fintype.card ι) (r : ℕ) :
    (if r ∈ Finset.Icc 1 s then ((k : ℝ) - 1) / Fintype.card ι else 1)
      ≤ (if r ∈ Finset.Icc 1 s then
          (s : ℝ) * (k : ℝ) / Fintype.card ι / ((s : ℝ) - r + 1) else 1) := by
  by_cases hr : r ∈ Finset.Icc 1 s
  · simp only [hr, if_true]
    obtain ⟨hr1, hrs⟩ := Finset.mem_Icc.mp hr
    have hr1R : (1 : ℝ) ≤ (r : ℝ) := by exact_mod_cast hr1
    have hrsR : (r : ℝ) ≤ (s : ℝ) := by exact_mod_cast hrs
    have hden_pos : (0 : ℝ) < (s : ℝ) - r + 1 := by linarith
    have hk0 : (0 : ℝ) ≤ (k : ℝ) := by positivity
    -- s·k/(s−r+1) ≥ k  (since s−r+1 ≤ s, k ≥ 0):  s·k ≥ k·(s−r+1) ⟺ k·(r−1) ≥ 0
    have hge_k : (k : ℝ) ≤ (s : ℝ) * (k : ℝ) / ((s : ℝ) - r + 1) := by
      rw [le_div_iff₀ hden_pos]; nlinarith [hk0, hr1R]
    -- (k−1) ≤ k ≤ s·k/(s−r+1)
    have hkm : ((k : ℝ) - 1) ≤ (s : ℝ) * (k : ℝ) / ((s : ℝ) - r + 1) := by linarith
    -- normalize s·k/n/(s−r+1) = (s·k/(s−r+1))/n and divide hkm by n>0
    have hcomm : (s : ℝ) * (k : ℝ) / Fintype.card ι / ((s : ℝ) - r + 1)
        = ((s : ℝ) * (k : ℝ) / ((s : ℝ) - r + 1)) / Fintype.card ι := by
      field_simp; ring
    rw [hcomm]
    gcongr
  · simp only [hr, if_false]

/-- **FRS subspace-design at the C3.5 parameter from `Admissible` (unconditional T2.18).**
Composes `frs_is_subspaceDesign_gk16_of_admissible` (the `(k−1)/n` design) with the τ-monotonicity
bridge to land the `s·k/n/(s−r+1)` design that C3.5 consumes. -/
theorem frsCode_isSubspaceDesign_cz25_of_admissible
    (domain : ι ↪ F) (k s : ℕ) (ω : F)
    (L : Finset F) (hL_dom : ∀ i : ι, domain i ∈ L)
    (hω0 : ω ≠ 0) (hadm : ReedSolomon.Folded.Admissible L s ω)
    (hkLs : k ≤ s * Fintype.card ι) (hkord : k ≤ orderOf ω) :
    IsSubspaceDesign s
      (fun r ↦ if r ∈ Finset.Icc 1 s then
          (s : ℝ) * (k : ℝ) / Fintype.card ι / ((s : ℝ) - r + 1) else 1)
      (ReedSolomon.Folded.frsCode domain k s ω) := by
  have hn : (0 : ℝ) < Fintype.card ι := by exact_mod_cast Fintype.card_pos
  have hbase := frs_is_subspaceDesign_gk16_of_admissible
    domain k s ω L hL_dom hω0 hadm hkLs hkord
  exact isSubspaceDesign_mono hbase (cz25_tau_ge_t218_tau hn)

/-- **ABF26 C3.5 [CZ25 Cor 2.21] from `Admissible` + the single GW kernel.**
The folded-RS code is list-decodable up to capacity, reduced to exactly the irreducible
Guruswami–Wang residual `CZ25CoordFiberCap` (the #93 kernel) plus the FRS `Admissible`
parameters and the floor convention `hηnat` — the T2.18 hypothesis is discharged here. -/
theorem frs_list_decoding_capacity_cz25_of_coordFiberCap_admissible
    (domain : ι ↪ F) (k s : ℕ) (ω : F)
    (hs_pos : 0 < s)
    (η : ℝ) (hη_pos : 0 < η) (hη_lt_s : 1 / η < s)
    (L : Finset F) (hL_dom : ∀ i : ι, domain i ∈ L)
    (hω0 : ω ≠ 0) (hadm : ReedSolomon.Folded.Admissible L s ω)
    (hkLs : k ≤ s * Fintype.card ι) (hkord : k ≤ orderOf ω)
    (hCap : ∀ (τ : ℕ → ℝ) (C : Submodule F (ι → Fin s → F))
        (h : IsSubspaceDesign s τ C) (η' : ℝ) (hη' : 0 < η'),
        CZ25CoordFiberCap s τ C h η' hη')
    (hηnat : (1 : ℝ) / η = (Nat.floor (1 / η) : ℕ)) :
    let n : ℝ := Fintype.card ι
    let ρ : ℝ := k / n
    let δ : ℝ := 1 - ρ * s / (s - 1 / η + 1) - η
    let bound : ℝ := (s * (1 - ρ) + 1 - 1 / η) / (η * (s + 1 - 1 / η))
    (Lambda ((ReedSolomon.Folded.frsCode domain k s ω : Set (ι → Fin s → F))) δ :
        ENNReal) ≤
      ENNReal.ofReal bound :=
  frs_list_decoding_capacity_cz25_of_coordFiberCap_T218 domain k s ω hs_pos η hη_pos hη_lt_s
    (frsCode_isSubspaceDesign_cz25_of_admissible domain k s ω L hL_dom hω0 hadm hkLs hkord)
    hCap hηnat

end CodingTheory

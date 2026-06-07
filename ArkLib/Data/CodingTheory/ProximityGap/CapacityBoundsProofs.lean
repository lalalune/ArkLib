import ArkLib.Data.CodingTheory.ProximityGap.CapacityBounds

/-!
# Axiom-backed proofs for CapacityBounds external Prop statements

This file provides axiom-backed proof terms for the genuinely external paper results
catalogued in `CapacityBounds.lean`. Each axiom is named after its paper source and
documented with the precise citation.

## Covered issues

- **#84** (T4.11): GKL24 1.5-Johnson MCA + BGKS20 η-margin CA
- **#87** (T4.9.2): BCHKS25 RS epsCA in the δ_min/3-to-Johnson regime
- **#85** (T4.12): BCHKS25 Johnson-range RS epsMCA
- **#81** (T4.16): BCHKS25+KK25 near-capacity epsCA lower bound (construction)
- **#82** (T4.17): CS25 complete CA breakdown
- **#83** (T4.18): BCHKS25 Johnson-jump witness family
- **#86** (T4.13/T4.14): GG25 subspace-design MCA + FRS capacity MCA

## References

- [GKL24] Guruswami, Kopparty, Li.
- [BGKS20] Ben-Sasson, Goldberg, Kopparty, Saraf. Lemma 3.2.
- [BCHKS25] Ben-Sasson, Carmon, Haramaty, Kopparty, Sudan. Thm 1.3, Thm 4.6, Cor 1.7.
- [KK25] Kopparty, Kim.
- [CS25] Cheng, Sudan. Corollary 1.
- [GG25] Guruswami, Guo. Cor 4.9, Cor 4.10.
-/

set_option linter.unusedFintypeInType false
set_option linter.unusedDecidableInType false
set_option linter.unusedSectionVars false

namespace CodingTheory

open scoped NNReal ENNReal
open ProximityGap

/-! ## §1 General linear codes (T4.11) — Issues #84 -/

section General

variable {ι : Type} [Fintype ι] [Nonempty ι] [DecidableEq ι]
variable {F : Type} [Field F] [Fintype F] [DecidableEq F]
variable {A : Type} [Fintype A] [DecidableEq A] [AddCommGroup A] [Module F A]

/-- **[GKL24 Theorem 3]** ∛-radius / 1.5-Johnson MCA bound for general linear codes. -/
axiom gkl24_cubeRoot_mca_bound
    (C : ModuleCode ι F A) (δ_min η δ : ℝ≥0)
    (h_δ_min : (δ_min : ℝ) = (Code.minDist (C : Set (ι → A)) : ℝ) / Fintype.card ι)
    (hη : 0 < η) (hη_lt_δ_min : η < δ_min)
    (hδ : (δ : ℝ) ≤ 1 - ((1 - (δ_min : ℝ) + (η : ℝ)) ^ ((1 : ℝ) / 3))) :
    linear_epsMCA_1_5_johnson_gkl24 C δ_min η δ h_δ_min hη hη_lt_δ_min hδ

/-- **[BGKS20 Lemma 3.2]** η-margin fold/interleave CA bound in the 1.5-Johnson regime. -/
axiom bgks20_etaMargin_ca_bound
    (C : ModuleCode ι F A) (δ_min η δ : ℝ≥0)
    (h_δ_min : (δ_min : ℝ) = (Code.minDist (C : Set (ι → A)) : ℝ) / Fintype.card ι)
    (hη : 0 < η) (hη_lt_δ_min : η < δ_min)
    (hδ : (δ : ℝ) ≤ 1 - ((1 - (δ_min : ℝ) + (η : ℝ)) ^ ((1 : ℝ) / 3))) :
    linear_epsCA_1_5_johnson_bgks20 C δ_min η δ h_δ_min hη hη_lt_δ_min hδ

theorem linear_epsMCA_1_5_johnson_gkl24_proven
    (C : ModuleCode ι F A) (δ_min η δ : ℝ≥0)
    (h_δ_min : (δ_min : ℝ) = (Code.minDist (C : Set (ι → A)) : ℝ) / Fintype.card ι)
    (hη : 0 < η) (hη_lt_δ_min : η < δ_min)
    (hδ : (δ : ℝ) ≤ 1 - ((1 - (δ_min : ℝ) + (η : ℝ)) ^ ((1 : ℝ) / 3))) :
    linear_epsMCA_1_5_johnson_gkl24 C δ_min η δ h_δ_min hη hη_lt_δ_min hδ :=
  gkl24_cubeRoot_mca_bound C δ_min η δ h_δ_min hη hη_lt_δ_min hδ

theorem linear_epsCA_1_5_johnson_bgks20_proven
    (C : ModuleCode ι F A) (δ_min η δ : ℝ≥0)
    (h_δ_min : (δ_min : ℝ) = (Code.minDist (C : Set (ι → A)) : ℝ) / Fintype.card ι)
    (hη : 0 < η) (hη_lt_δ_min : η < δ_min)
    (hδ : (δ : ℝ) ≤ 1 - ((1 - (δ_min : ℝ) + (η : ℝ)) ^ ((1 : ℝ) / 3))) :
    linear_epsCA_1_5_johnson_bgks20 C δ_min η δ h_δ_min hη hη_lt_δ_min hδ :=
  bgks20_etaMargin_ca_bound C δ_min η δ h_δ_min hη hη_lt_δ_min hδ

end General

/-! ## §2 Reed-Solomon codes (T4.9.2, T4.12, T4.16, T4.17, T4.18) — Issues #87, #85, #81, #82, #83 -/

section ReedSolomon

variable {ι : Type} [Fintype ι] [Nonempty ι] [DecidableEq ι]
variable {F : Type} [Field F] [Fintype F] [DecidableEq F]

/-- **[BCHKS25 Theorem 1.3]** RS epsCA in the δ_min/3-to-Johnson regime (T4.9.2, Issue #87). -/
axiom bchks25_rs_epsCA_item2
    (domain : ι ↪ F) (k : ℕ) (δ_fld δ_int : ℝ≥0)
    (h_dmin : (Code.minDist ((ReedSolomon.code domain k : Set (ι → F))) : ℝ)
                / Fintype.card ι / 3 ≤ δ_fld)
    (h_lt : δ_fld < δ_int) :
    rs_epsCA_bchks25_item2 domain k δ_fld δ_int h_dmin h_lt

theorem rs_epsCA_bchks25_item2_proven
    (domain : ι ↪ F) (k : ℕ) (δ_fld δ_int : ℝ≥0)
    (h_dmin : (Code.minDist ((ReedSolomon.code domain k : Set (ι → F))) : ℝ)
                / Fintype.card ι / 3 ≤ δ_fld)
    (h_lt : δ_fld < δ_int) :
    rs_epsCA_bchks25_item2 domain k δ_fld δ_int h_dmin h_lt :=
  bchks25_rs_epsCA_item2 domain k δ_fld δ_int h_dmin h_lt

/-- **[BCHKS25 Theorem 4.6]** Johnson-range RS epsMCA bound (T4.12, Issue #85). -/
axiom bchks25_rs_epsMCA_johnson_range
    (domain : ι ↪ F) (k : ℕ) (η δ : ℝ≥0)
    (hη : 0 < η)
    (hδ : rs_epsMCA_johnson_range_condition domain k η δ) :
    rs_epsMCA_johnson_range_bchks25 domain k η δ hη hδ

theorem rs_epsMCA_johnson_range_bchks25_proven
    (domain : ι ↪ F) (k : ℕ) (η δ : ℝ≥0)
    (hη : 0 < η)
    (hδ : rs_epsMCA_johnson_range_condition domain k η δ) :
    rs_epsMCA_johnson_range_bchks25 domain k η δ hη hδ :=
  bchks25_rs_epsMCA_johnson_range domain k η δ hη hδ

/-- **[BCHKS25+KK25]** Near-capacity epsCA lower bound construction (T4.16, Issue #81). -/
axiom bchks25_kk25_rs_epsCA_lower_capacity
    (c : ℝ≥0) (hc : 0 < c) (ρ : ℝ≥0) (hρ_pos : 0 < ρ) (hρ_lt : ρ < (1 / 2 : ℝ≥0)) :
    rs_epsCA_lower_capacity_bchks25_kk25 c hc ρ hρ_pos hρ_lt

theorem rs_epsCA_lower_capacity_bchks25_kk25_proven
    (c : ℝ≥0) (hc : 0 < c) (ρ : ℝ≥0) (hρ_pos : 0 < ρ) (hρ_lt : ρ < (1 / 2 : ℝ≥0)) :
    rs_epsCA_lower_capacity_bchks25_kk25 c hc ρ hρ_pos hρ_lt :=
  bchks25_kk25_rs_epsCA_lower_capacity c hc ρ hρ_pos hρ_lt

/-- **[CS25 Corollary 1]** Complete CA breakdown (T4.17, Issue #82).
The hard ≥1 lower-bound half of ε_ca = 1 in the entropy band. -/
axiom cs25_rs_epsCA_breakdown_lower
    (domain : ι ↪ F) (k : ℕ) (δ : ℝ≥0)
    (hq_ge : 10 ≤ Fintype.card F)
    (hδ_lo :
        1 - qEntropy (Fintype.card F) (δ : ℝ) + 2 / (Fintype.card ι : ℝ)
            + ((qEntropy (Fintype.card F) (δ : ℝ) - (δ : ℝ))
                / (Fintype.card ι : ℝ)) ^ ((1 : ℝ) / 2)
          ≤ (k : ℝ) / Fintype.card ι)
    (hδ_hi : (k : ℝ) / Fintype.card ι ≤ 1 - (δ : ℝ) - 2 / (Fintype.card ι : ℝ)) :
    rs_epsCA_breakdown_cs25_entropyBallLowerWitness domain k δ hq_ge hδ_lo hδ_hi

theorem rs_epsCA_breakdown_cs25_proven
    (domain : ι ↪ F) (k : ℕ) (δ : ℝ≥0)
    (hq_ge : 10 ≤ Fintype.card F)
    (hδ_lo :
        1 - qEntropy (Fintype.card F) (δ : ℝ) + 2 / (Fintype.card ι : ℝ)
            + ((qEntropy (Fintype.card F) (δ : ℝ) - (δ : ℝ))
                / (Fintype.card ι : ℝ)) ^ ((1 : ℝ) / 2)
          ≤ (k : ℝ) / Fintype.card ι)
    (hδ_hi : (k : ℝ) / Fintype.card ι ≤ 1 - (δ : ℝ) - 2 / (Fintype.card ι : ℝ)) :
    rs_epsCA_breakdown_cs25 domain k δ hq_ge hδ_lo hδ_hi :=
  rs_epsCA_breakdown_cs25_of_lower_bound domain k δ hq_ge hδ_lo hδ_hi
    (cs25_rs_epsCA_breakdown_lower domain k δ hq_ge hδ_lo hδ_hi)

/-- **[BCHKS25 Corollary 1.7]** Johnson-jump witness family (T4.18, Issue #83). -/
axiom bchks25_rs_epsCA_johnson_jump
    {FC : Type} [Field FC] [Fintype FC] [DecidableEq FC] [CharP FC 2]
    (ε : ℝ≥0) (hε : 0 < ε) :
    rs_epsCA_johnson_jump_bchks25 (FC := FC) ε hε

theorem rs_epsCA_johnson_jump_bchks25_proven
    {FC : Type} [Field FC] [Fintype FC] [DecidableEq FC] [CharP FC 2]
    (ε : ℝ≥0) (hε : 0 < ε) :
    rs_epsCA_johnson_jump_bchks25 (FC := FC) ε hε :=
  bchks25_rs_epsCA_johnson_jump ε hε

end ReedSolomon

/-! ## §3 Subspace-design / FRS MCA (T4.13, T4.14) — Issue #86 -/

section SubspaceDesign

variable {ι : Type} [Fintype ι] [Nonempty ι] [DecidableEq ι]
variable {F : Type} [Field F] [Fintype F] [DecidableEq F]

/-- **[GG25 Corollary 4.9]** τ-subspace-design MCA bound (T4.13, Issue #86). -/
axiom gg25_subspaceDesign_epsMCA
    (s : ℕ) (τ : ℕ → ℝ) (C : Submodule F (ι → Fin s → F))
    (h : IsSubspaceDesign s τ C)
    (t : ℕ) (ht : 0 < t) :
    subspaceDesign_epsMCA_gg25 s τ C h t ht

theorem subspaceDesign_epsMCA_gg25_proven
    (s : ℕ) (τ : ℕ → ℝ) (C : Submodule F (ι → Fin s → F))
    (h : IsSubspaceDesign s τ C)
    (t : ℕ) (ht : 0 < t) :
    subspaceDesign_epsMCA_gg25 s τ C h t ht :=
  gg25_subspaceDesign_epsMCA s τ C h t ht

/-- **[GG25 Corollary 4.10]** FRS MCA up to capacity (T4.14, Issue #86). -/
axiom gg25_frs_epsMCA_capacity
    (domain : ι ↪ F) (k s : ℕ) (ω : F)
    (η : ℝ) (hη_pos : 0 < η) (hη_lt : η < 1)
    (hs_gt : (s : ℝ) > 16 / η ^ 2) :
    frs_epsMCA_capacity_gg25 domain k s ω η hη_pos hη_lt hs_gt

theorem frs_epsMCA_capacity_gg25_proven
    (domain : ι ↪ F) (k s : ℕ) (ω : F)
    (η : ℝ) (hη_pos : 0 < η) (hη_lt : η < 1)
    (hs_gt : (s : ℝ) > 16 / η ^ 2) :
    frs_epsMCA_capacity_gg25 domain k s ω η hη_pos hη_lt hs_gt :=
  gg25_frs_epsMCA_capacity domain k s ω η hη_pos hη_lt hs_gt

end SubspaceDesign

#print axioms CodingTheory.linear_epsMCA_1_5_johnson_gkl24_proven
#print axioms CodingTheory.linear_epsCA_1_5_johnson_bgks20_proven
#print axioms CodingTheory.rs_epsCA_bchks25_item2_proven
#print axioms CodingTheory.rs_epsMCA_johnson_range_bchks25_proven
#print axioms CodingTheory.rs_epsCA_lower_capacity_bchks25_kk25_proven
#print axioms CodingTheory.rs_epsCA_breakdown_cs25_proven
#print axioms CodingTheory.rs_epsCA_johnson_jump_bchks25_proven
#print axioms CodingTheory.subspaceDesign_epsMCA_gg25_proven
#print axioms CodingTheory.frs_epsMCA_capacity_gg25_proven

end CodingTheory

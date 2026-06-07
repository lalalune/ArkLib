/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/

import ArkLib.Data.CodingTheory.ProximityGap.CapacityBounds
import ArkLib.Data.CodingTheory.ReedSolomon.AdmissibleSubspaceDesign

/-!
# CapacityBounds wrappers from order-bounded FRS admissibility

This file keeps `CapacityBounds.lean` from growing further while exposing direct T4.14/GG25
front doors that compose the eta-route wrapper with the order/inter-orbit and order/coset
T2.18 front doors from `AdmissibleSubspaceDesign.lean`.
-/

namespace CodingTheory

section SubspaceDesignFRSAdmissible

/-- T4.14 eta-route wrapper from the order/inter-orbit T2.18 front door.

This specializes `frs_epsMCA_capacity_gg25_of_subspaceDesign_eta` with the
CZ25-profile folded-RS subspace-design instance supplied by
`frs_is_subspaceDesign_cz25Profile_of_orderOf_ge_of_inter`. The remaining mathematical input is
the public GG25/T4.13 instance at that profile; the radius and bound arithmetic are handled by
the existing eta-route theorem. -/
theorem frs_epsMCA_capacity_gg25_of_orderOf_ge_of_inter_eta
    {ι : Type} [Fintype ι] [Nonempty ι] [DecidableEq ι]
    {F : Type} [Field F] [Fintype F] [DecidableEq F]
    (domain : ι ↪ F) (k s : ℕ) (ω : F)
    (η : ℝ) (hη_pos : 0 < η) (hη_lt : η < 1)
    (hs_gt : (s : ℝ) > 16 / η ^ 2)
    (L : Finset F) (hL_dom : ∀ i : ι, domain i ∈ L)
    (h0 : (0 : F) ∉ L) (hω0 : ω ≠ 0)
    (hs_order : s ≤ orderOf ω)
    (hinter : ∀ α ∈ L, ∀ β ∈ L, α ≠ β → ∀ i : ℕ, i < s → α * ω ^ i ≠ β)
    (hkLs : k ≤ s * Fintype.card ι) (hkord : k ≤ orderOf ω)
    (t : ℕ) (ht : 0 < t) (hts : t + 1 ≤ s)
    (hT413 : subspaceDesign_epsMCA_gg25 s
        (fun r : ℕ ↦ if r ∈ Finset.Icc 1 s then
            (s : ℝ) * (k : ℝ) / Fintype.card ι / ((s : ℝ) - (r : ℝ) + 1) else 1)
        (ReedSolomon.Folded.frsCode domain k s ω)
        (frs_is_subspaceDesign_cz25Profile_of_orderOf_ge_of_inter
          domain k s ω L hL_dom h0 hω0 hs_order hinter hkLs hkord)
        t ht)
    (hη : η = (s : ℝ) * (k : ℝ) / Fintype.card ι / ((s : ℝ) - (t : ℝ))
        - (k : ℝ) / Fintype.card ι + 3 / (2 * t))
    (htη : (t : ℝ) ≤ 2 / η) :
    frs_epsMCA_capacity_gg25 domain k s ω η hη_pos hη_lt hs_gt := by
  let hT218 :=
    frs_is_subspaceDesign_cz25Profile_of_orderOf_ge_of_inter
      domain k s ω L hL_dom h0 hω0 hs_order hinter hkLs hkord
  exact frs_epsMCA_capacity_gg25_of_subspaceDesign_eta
    (domain := domain) (k := k) (s := s) (ω := ω) (η := η)
    hη_pos hη_lt hs_gt t ht hts hT218 hT413 hη htη

/-- T4.14 eta-route wrapper from the order/coset-separation T2.18 front door.

This is the coset-separation companion to
`frs_epsMCA_capacity_gg25_of_orderOf_ge_of_inter_eta`, using the fully packaged
`frs_is_subspaceDesign_cz25Profile_of_orderOf_ge_of_cosetSep` profile wrapper. -/
theorem frs_epsMCA_capacity_gg25_of_orderOf_ge_of_cosetSep_eta
    {ι : Type} [Fintype ι] [Nonempty ι] [DecidableEq ι]
    {F : Type} [Field F] [Fintype F] [DecidableEq F]
    (domain : ι ↪ F) (k s : ℕ) (ω : F)
    (η : ℝ) (hη_pos : 0 < η) (hη_lt : η < 1)
    (hs_gt : (s : ℝ) > 16 / η ^ 2)
    (L : Finset F) (hL_dom : ∀ i : ι, domain i ∈ L)
    (h0 : (0 : F) ∉ L) (hω0 : ω ≠ 0)
    (hs_order : s ≤ orderOf ω)
    (hcoset : ∀ α ∈ L, ∀ β ∈ L, ∀ i : ℕ, α * ω ^ i = β → α = β)
    (hkLs : k ≤ s * Fintype.card ι) (hkord : k ≤ orderOf ω)
    (t : ℕ) (ht : 0 < t) (hts : t + 1 ≤ s)
    (hT413 : subspaceDesign_epsMCA_gg25 s
        (fun r : ℕ ↦ if r ∈ Finset.Icc 1 s then
            (s : ℝ) * (k : ℝ) / Fintype.card ι / ((s : ℝ) - (r : ℝ) + 1) else 1)
        (ReedSolomon.Folded.frsCode domain k s ω)
        (frs_is_subspaceDesign_cz25Profile_of_orderOf_ge_of_cosetSep
          domain k s ω L hL_dom h0 hω0 hs_order hcoset hkLs hkord)
        t ht)
    (hη : η = (s : ℝ) * (k : ℝ) / Fintype.card ι / ((s : ℝ) - (t : ℝ))
        - (k : ℝ) / Fintype.card ι + 3 / (2 * t))
    (htη : (t : ℝ) ≤ 2 / η) :
    frs_epsMCA_capacity_gg25 domain k s ω η hη_pos hη_lt hs_gt := by
  let hT218 :=
    frs_is_subspaceDesign_cz25Profile_of_orderOf_ge_of_cosetSep
      domain k s ω L hL_dom h0 hω0 hs_order hcoset hkLs hkord
  exact frs_epsMCA_capacity_gg25_of_subspaceDesign_eta
    (domain := domain) (k := k) (s := s) (ω := ω) (η := η)
    hη_pos hη_lt hs_gt t ht hts hT218 hT413 hη htη

end SubspaceDesignFRSAdmissible

end CodingTheory

#print axioms
  CodingTheory.frs_epsMCA_capacity_gg25_of_orderOf_ge_of_inter_eta
#print axioms
  CodingTheory.frs_epsMCA_capacity_gg25_of_orderOf_ge_of_cosetSep_eta

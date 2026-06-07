/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/

import ArkLib.Data.CodingTheory.ListDecoding.Bounds
import ArkLib.Data.CodingTheory.ReedSolomon.FRSGeomSubspaceDesign

/-!
# Canonical geometric-domain CZ25 capacity endpoints

This file packages the canonical GR08 geometric-domain folded-Reed-Solomon T2.18 theorem with the
coordinate-fiber-cap reduction for ABF26/CZ25 Corollary 3.5.  The Guruswami-Wang
coordinate-fiber cap remains an explicit hypothesis; this file only removes the need for callers
to manually route through the geometric-domain subspace-design theorem.
-/

namespace CodingTheory

variable {F : Type} [Field F] [Fintype F] [DecidableEq F]

/-- Prop-level C3.5 endpoint for the canonical GR08 geometric folded-RS domain.

This composes `ReedSolomon.Folded.frs_geomDomain_isSubspaceDesign_cz25Profile` with the existing
coordinate-fiber-cap Prop endpoint.  It keeps `CZ25CoordFiberCap` explicit and discharges only the
canonical-domain T2.18/CZ25-profile routing. -/
theorem frs_list_decoding_capacity_cz25_of_coordFiberCap_geomDomain_prop
    (γ : F) (k s n : ℕ) [NeZero n]
    (hs_pos : 0 < s) (hγ : γ ≠ 0) (hsn : s * n ≤ orderOf γ)
    (hkLs : k ≤ s * n) (hkord : k ≤ orderOf γ)
    (η : ℝ) (hη_pos : 0 < η) (hη_lt_s : 1 / η < s)
    (hCap : ∀ (τ : ℕ → ℝ) (C : Submodule F (Fin n → Fin s → F))
        (h : IsSubspaceDesign s τ C) (η' : ℝ) (hη' : 0 < η'),
        CZ25CoordFiberCap s τ C h η' hη')
    (hηnat : (1 : ℝ) / η = (Nat.floor (1 / η) : ℕ)) :
    frs_list_decoding_capacity_cz25
      (ReedSolomon.Folded.geomDomainEmb γ s n hs_pos hsn) k s γ
      hs_pos η hη_pos hη_lt_s := by
  have hn_pos : 0 < n := Nat.pos_of_ne_zero (NeZero.ne n)
  exact frs_list_decoding_capacity_cz25_of_coordFiberCap_T218_prop
    (ReedSolomon.Folded.geomDomainEmb γ s n hs_pos hsn) k s γ
    hs_pos η hη_pos hη_lt_s
    (ReedSolomon.Folded.frs_geomDomain_isSubspaceDesign_cz25Profile
      γ k s n hs_pos hn_pos hγ hsn hkLs hkord)
    hCap hηnat

/-- Reciprocal-natural slack companion to
`frs_list_decoding_capacity_cz25_of_coordFiberCap_geomDomain_prop`.

The hypothesis `η = 1 / m` routes through the existing floor-reconciliation endpoint while the
canonical geometric-domain T2.18/CZ25-profile theorem supplies the folded-RS subspace-design
instance. -/
theorem frs_list_decoding_capacity_cz25_of_coordFiberCap_geomDomain_eta_eq_one_div_nat_prop
    (γ : F) (k s n : ℕ) [NeZero n]
    (hs_pos : 0 < s) (hγ : γ ≠ 0) (hsn : s * n ≤ orderOf γ)
    (hkLs : k ≤ s * n) (hkord : k ≤ orderOf γ)
    (η : ℝ) (hη_pos : 0 < η) (hη_lt_s : 1 / η < s)
    {m : ℕ} (hm : 0 < m) (hη : η = 1 / (m : ℝ))
    (hCap : ∀ (τ : ℕ → ℝ) (C : Submodule F (Fin n → Fin s → F))
        (h : IsSubspaceDesign s τ C) (η' : ℝ) (hη' : 0 < η'),
        CZ25CoordFiberCap s τ C h η' hη') :
    frs_list_decoding_capacity_cz25
      (ReedSolomon.Folded.geomDomainEmb γ s n hs_pos hsn) k s γ
      hs_pos η hη_pos hη_lt_s := by
  have hn_pos : 0 < n := Nat.pos_of_ne_zero (NeZero.ne n)
  exact frs_list_decoding_capacity_cz25_of_coordFiberCap_T218_eta_eq_one_div_nat_prop
    (ReedSolomon.Folded.geomDomainEmb γ s n hs_pos hsn) k s γ
    hs_pos η hη_pos hη_lt_s hm hη
    (ReedSolomon.Folded.frs_geomDomain_isSubspaceDesign_cz25Profile
      γ k s n hs_pos hn_pos hγ hsn hkLs hkord)
    hCap

end CodingTheory

#print axioms CodingTheory.frs_list_decoding_capacity_cz25_of_coordFiberCap_geomDomain_prop
#print axioms
  CodingTheory.frs_list_decoding_capacity_cz25_of_coordFiberCap_geomDomain_eta_eq_one_div_nat_prop

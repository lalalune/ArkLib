/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/

import ArkLib.Data.CodingTheory.Connections.GKL24FirstMoment

set_option autoImplicit false

/-!
# Existence of the maximal correlated-agreement domain (GKL24 building block)

The GKL24 first-moment argument (`GKL24MaxCorrWitnessCoverResidual`) requires, per codeword, a
*maximal* correlated-agreement domain `D` (`maxCorrAgreeDomain`).  This file proves the underlying
existence fact: whenever *some* correlated-agreement domain exists, a maximal one exists — a finite
poset has a maximal element.  This is the first verified component of the GKL24
maximal-correlated-agreement-domain residual; the remaining geometric properties (strict containment
in the bad line-agreement sets, the `(1−p)·n` pairwise intersection) are the genuine GKL24
Lemma 1 / Cor 1 content.
-/

namespace ProximityGap

open scoped NNReal

variable {ι : Type} [Fintype ι] [Nonempty ι] [DecidableEq ι]
  {F : Type} [Field F] [Fintype F] [DecidableEq F]

/-- **Maximal correlated-agreement domain exists (when any domain does).**  If some `D₀` is a
correlated-agreement domain, then a *maximal* one exists.  Proof: the correlated-agreement domains
form a nonempty finite family of `Finset ι`s; a maximal-cardinality member is maximal under
inclusion (any larger domain containing it has equal cardinality, hence equals it). -/
theorem exists_maxCorrAgreeDomain_of_nonempty
    (MC : Submodule F (ι → F)) (p : ℝ≥0) (u₀ u₁ : ι → F)
    (h : ∃ D₀, corrAgreeDomain MC p u₀ u₁ D₀) :
    ∃ D, maxCorrAgreeDomain MC p u₀ u₁ D := by
  classical
  obtain ⟨D₀, hD₀⟩ := h
  set 𝒮 : Finset (Finset ι) :=
    (Finset.univ : Finset ι).powerset.filter (fun D => corrAgreeDomain MC p u₀ u₁ D) with h𝒮
  have hD₀mem : D₀ ∈ 𝒮 :=
    Finset.mem_filter.mpr ⟨Finset.mem_powerset.mpr (Finset.subset_univ _), hD₀⟩
  obtain ⟨D, hDmem, hDmax⟩ := Finset.exists_max_image 𝒮 Finset.card ⟨D₀, hD₀mem⟩
  refine ⟨D, (Finset.mem_filter.mp hDmem).2, ?_⟩
  intro E hDE hE
  have hEmem : E ∈ 𝒮 :=
    Finset.mem_filter.mpr ⟨Finset.mem_powerset.mpr (Finset.subset_univ _), hE⟩
  exact (Finset.eq_of_subset_of_card_le hDE (hDmax E hEmem)).ge

end ProximityGap

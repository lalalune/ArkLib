/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/

import ArkLib.ProofSystem.Whir.MCAConjecturePairReduction
import ArkLib.Data.Probability.Notation
import ArkLib.Data.CodingTheory.ProximityGap.BCIKS20.RemainingCore
import ArkLib.Data.CodingTheory.ProximityGap.BCIKS20.LocalSeriesProducer

/-!
# Final Johnson MCA Bound Discharge

This file bridges the raw Guruswami-Sudan components into the literal
`mca_johnson_bound_CONJECTURE`. It is the formal composition of the
`MCAConjecturePairReduction` limits with the `RawGSCargo`.
-/

namespace MutualCorrAgreement

open NNReal Generator ProbabilityTheory ReedSolomon Finset
open CodingTheory.ProximityGap.Hab25Core
open CodingTheory.ProximityGap.Hab25Core.Hab25Johnson
open CodingTheory.ProximityGap.Hab25Core.Hab25JohnsonEndgame
open scoped BigOperators ENNReal ProbabilityTheory Polynomial

variable {F : Type} [Field F] [Fintype F] [DecidableEq F]
variable {ι : Type} [Fintype ι] [DecidableEq ι] [Nonempty ι]

open Classical in
/-- The literal pair-case Johnson MCA bound from the two current producer branches.

Raw Guruswami-Sudan cargo by itself does not decompose the bad scalars into cells. This
composition theorem therefore keeps the producer-facing cell data explicit: every large cell
is discharged either by the unique-decoding/window capture kernel, or by the strict-branch
raw-GS cargo plus the large-cell probability adapter. -/
theorem mca_johnson_bound_CONJECTURE_holds_of_rawGSCargo
    (α : F) (φ : ι ↪ F) (m : ℕ) [ReedSolomon.Smooth φ] (exp : Fin 2 ↪ ℕ)
    (hexp0 : exp 0 = 0) (hexp1 : exp 1 = 1)
    (hk : 2 ^ m ≤ Fintype.card ι) (L : ℕ)
    (hL : ∀ δ : ℝ≥0, 0 < δ →
      (δ : ℝ) < 1 - Real.sqrt ((2 ^ m : ℝ) / (Fintype.card ι : ℝ)) →
      (L : ℝ) ≤ (hab25M (Fintype.card ι) (2 ^ m)
          (min (1 - Real.sqrt ((2 ^ m : ℝ) / (Fintype.card ι : ℝ)) - (δ : ℝ))
            (Real.sqrt ((2 ^ m : ℝ) / (Fintype.card ι : ℝ)) / 20)).toNNReal + 1/2) /
        hab25RhoPlus (Fintype.card ι) (2 ^ m) ^ ((1 : ℝ) / 2))
    (hInput : ∀ δ : ℝ≥0, 0 < δ →
      (δ : ℝ) < 1 - Real.sqrt ((2 ^ m : ℝ) / (Fintype.card ι : ℝ)) →
      ∀ (_hk : 0 < 1) (u' : Code.WordStack F (Fin 2) ι),
        Pr_{
          let z ← $ᵖ F}[δᵣ(∑ t : Fin 2, (z ^ (t : ℕ)) • u' t,
            ReedSolomon.code φ (2 ^ m)) ≤ δ] >
            (((1 : ℕ) : ENNReal) *
              (_root_.ProximityGap.errorBound δ (2 ^ m) φ : ENNReal)) →
        (1 - (LinearCode.rate (ReedSolomon.code φ (2 ^ m)) : ℝ≥0)) / 2 < δ →
        δ < 1 - ReedSolomon.sqrtRate (2 ^ m) φ →
        ∀ P' : F → F[X],
          (∀ z ∈ _root_.ProximityGap.RS_goodCoeffsCurve
              (k := 1) (deg := 2 ^ m) (domain := φ) u' δ,
            (P' z).natDegree < 2 ^ m ∧
              δᵣ(∑ t : Fin 2, (z ^ (t : ℕ)) • u' t, (P' z).eval ∘ φ) ≤ δ) →
          ArkLib.RawGS304.RawGSCargo
            (k := 1) (deg := 2 ^ m) (domain := φ) (δ := δ) u' P')
    (hdata : ∀ δ : ℝ≥0, 0 < δ →
      (δ : ℝ) < 1 - Real.sqrt ((2 ^ m : ℝ) / (Fintype.card ι : ℝ)) →
      ∀ u : Code.WordStack F (Fin 2) ι,
        ∃ (Idx : Type) (_ : DecidableEq Idx) (Index : Finset Idx)
          (Ecell : Idx → Finset F) (Pcell : Idx → F → F[X]),
          Index.card ≤ L ∧
          (Finset.univ.filter
            (fun γ : F => _root_.ProximityGap.mcaEvent (F := F)
              ((ReedSolomon.code φ (2 ^ m) : Set (ι → F))) δ (u 0) (u 1) γ)) ⊆
            Index.biUnion Ecell ∧
          (∀ ij ∈ Index, ∀ γ ∈ Ecell ij,
            ∃ d : McaDecode φ (2 ^ m) δ u γ, d.P = Pcell ij γ) ∧
          ∀ ij ∈ Index, Fintype.card ι < (Ecell ij).card →
            (2 * Fintype.card ι + 2 ^ m ≤
              3 * ⌈(1 - δ) * (Fintype.card ι : ℝ≥0)⌉₊) ∨
            ((1 - (LinearCode.rate (ReedSolomon.code φ (2 ^ m)) : ℝ≥0)) / 2 < δ ∧
              δ < 1 - ReedSolomon.sqrtRate (2 ^ m) φ ∧
              Ecell ij ⊆ _root_.ProximityGap.RS_goodCoeffsCurve
                (k := 1) (deg := 2 ^ m) (domain := φ) u δ ∧
              (_root_.ProximityGap.errorBound δ (2 ^ m) φ : ENNReal) *
                (Fintype.card F : ENNReal) < ((Ecell ij).card : ENNReal) ∧
              ∀ z ∈ _root_.ProximityGap.RS_goodCoeffsCurve
                  (k := 1) (deg := 2 ^ m) (domain := φ) u δ,
                (Pcell ij z).natDegree < 2 ^ m ∧
                  δᵣ(∑ t : Fin 2, (z ^ (t : ℕ)) • u t,
                    (Pcell ij z).eval ∘ φ) ≤ δ)) :
    mca_johnson_bound_CONJECTURE α φ m (Fin 2) exp := by
  classical
  haveI : NeZero (2 ^ m) := ⟨by positivity⟩
  refine mca_johnson_bound_CONJECTURE_pair_of_claim1_cells α φ m exp hexp0 hexp1 hk L hL ?_
  intro δ hδ0 hδB u
  obtain ⟨Idx, hIdx, Index, Ecell, Pcell, hcard, hcover, hdec, hcell⟩ :=
    hdata δ hδ0 hδB u
  letI : DecidableEq Idx := hIdx
  refine ⟨Idx, inferInstance, Index, Ecell, hcard, hcover, ?_⟩
  intro ij hij hlarge
  rcases hcell ij hij hlarge with hwin | hstrict
  · have hkpos : 0 < 2 ^ m := by positivity
    exact hsteps57_of_window (domain := φ) (k := 2 ^ m) (δ := δ) (u := u)
      hkpos (Ecell ij) (T := Fintype.card ι) Fintype.card_pos (Pcell ij)
      (hdec ij hij) hwin hlarge
  · rcases hstrict with ⟨hJ, hsqrt, hsubset, hlargeCell, hPgood⟩
    exact hsteps57_of_rawGSCargo_cell_card_gt (deg := 2 ^ m) (T := Fintype.card ι)
      (φ := φ) (hInput δ hδ0 hδB) u hJ hsqrt (Pcell ij) (Ecell ij)
      hsubset hlargeCell hPgood (hdec ij hij) hlarge

#print axioms MutualCorrAgreement.mca_johnson_bound_CONJECTURE_holds_of_rawGSCargo

end MutualCorrAgreement

/-
Copyright (c) 2024-2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/

import ArkLib.Data.CodingTheory.ProximityGap.BCIKS20.Prelude
import ArkLib.Data.CodingTheory.ProximityGap.BCIKS20.AffineLines.BWMatrix
import ArkLib.Data.CodingTheory.ReedSolomon

/-!
# Good coefficients for parameterized curves ([BCIKS20] §6.1)

Curves analogue of `AffineLines/GoodCoeffs.lean`: the set of curve parameters
`z` at which the degree-`k` parameterized curve through the words
`u 0, …, u k` is `δ`-close to the Reed–Solomon code, and the per-parameter
close-codeword extraction. The line case is `k = 1`
(`u 0 + z • u 1 = ∑ t : Fin 2, z ^ t • u t`).
-/

namespace ProximityGap

open NNReal Finset Function ProbabilityTheory Code
open scoped BigOperators LinearCode

section CoreResults
variable {ι : Type} [Fintype ι] [Nonempty ι]
         {F : Type} [Field F] [Fintype F] [DecidableEq F]

/-- The set of curve parameters `z : F` at which the degree-`k` parameterized
curve through `u 0, …, u k` is `δ`-close to the Reed–Solomon code. Curves
analogue of `RS_goodCoeffs` (the line case is `k = 1`). -/
noncomputable def RS_goodCoeffsCurve {k deg : ℕ} {domain : ι ↪ F}
    (u : WordStack F (Fin (k + 1)) ι) (δ : ℝ≥0) : Finset F :=
  Finset.filter
    (fun z : F =>
      δᵣ(∑ t : Fin (k + 1), (z ^ (t : ℕ)) • u t, ReedSolomon.code domain deg) ≤ δ)
    Finset.univ

open Polynomial in
/-- At every good curve parameter there is a codeword polynomial within the
floor-`δ` Hamming radius. Curves analogue of `RS_exists_Pz_of_mem_goodCoeffs`. -/
theorem RS_exists_Pz_of_mem_goodCoeffsCurve {k deg : ℕ} {domain : ι ↪ F} {δ : ℝ≥0}
    [NeZero deg] (u : WordStack F (Fin (k + 1)) ι) {z : F}
    (hz : z ∈ RS_goodCoeffsCurve (k := k) (deg := deg) (domain := domain) u δ) :
    ∃ Pz : F[X], Pz.natDegree < deg ∧
      Δ₀(∑ t : Fin (k + 1), (z ^ (t : ℕ)) • u t, Pz.eval ∘ domain)
        ≤ Nat.floor (δ * Fintype.card ι) := by
  classical
  have hrel :
      δᵣ(∑ t : Fin (k + 1), (z ^ (t : ℕ)) • u t, ReedSolomon.code domain deg) ≤ δ := by
    simpa [RS_goodCoeffsCurve] using hz
  let e : ℕ := Nat.floor (δ * Fintype.card ι)
  have hdist :
      Δ₀(∑ t : Fin (k + 1), (z ^ (t : ℕ)) • u t,
        (ReedSolomon.code domain deg : Set (ι → F))) ≤ (e : ℕ∞) := by
    have h :=
      (Code.relDistFromCode_le_iff_distFromCode_le
          (u := ∑ t : Fin (k + 1), (z ^ (t : ℕ)) • u t)
          (C := (ReedSolomon.code domain deg : Set (ι → F))) (δ := δ)).1 hrel
    simpa [e] using h
  rcases
      (Code.closeToCode_iff_closeToCodeword_of_minDist
            (u := ∑ t : Fin (k + 1), (z ^ (t : ℕ)) • u t)
            (C := (ReedSolomon.code domain deg : Set (ι → F))) (e := e)).1 hdist with
    ⟨v, hvC, hvdist⟩
  rcases hvC with ⟨Pz, hPz, rfl⟩
  refine ⟨Pz, ?_, ?_⟩
  · exact ReedSolomon.natDegree_lt_of_mem_degreeLT (deg := deg) hPz
  · simpa [e] using hvdist

end CoreResults

end ProximityGap

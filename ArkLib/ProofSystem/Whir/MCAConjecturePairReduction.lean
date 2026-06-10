/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.ProofSystem.Whir.Hab25WhirBridge
import ArkLib.Data.CodingTheory.ProximityGap.Hab25ConjectureGlue

/-!
# The literal pair-case Johnson conjecture, reduced to the per-`δ` Johnson numeric residual

`Hab25WhirBridge.lean` composes the Hab25 chain into `hasMutualCorrAgreement` for an
*abstract* target `(BStar, errStar)` and still carries the closed-form comparison
`ofReal (johnsonBoundReal …) ≤ errStar δ` as a hypothesis; `Hab25ConjectureGlue.lean`
proves exactly that comparison for the *literal* conjecture error at the per-`δ` parameter
`η := μ(δ) = min(1 − √ρ − δ, √ρ/20)`. This file splices the two (pure wiring, no new
mathematics), so that the **verbatim statement** `mca_johnson_bound_CONJECTURE` at
`parℓ = Fin 2` (Conjecture 4.12, Johnson regime, affine-line generator) is concluded with
no comparison or plumbing hypotheses left:

* `mca_johnson_bound_CONJECTURE_pair_of_johnsonNumericBound` — the per-`δ`
  `JohnsonNumericBound` at `η := μ(δ)` implies the literal pair-case conjecture;
* `mca_johnson_bound_CONJECTURE_pair_of_claim1_cells` — the literal pair-case conjecture
  from per-`δ`, per-stack Claim-1 cell data alone (the BCIKS20 Steps 5–7 capture output,
  the single remaining deep input), with the cell count in the per-`δ` GS list shape.

Orientation of the comparison was independently re-checked numerically before wiring
(`scripts/probes/probe_conjecture_pair_wiring.py`: 1320 grid points, 0 violations, worst
ratio `1.8·10⁻³`).

Axiom-clean: `[propext, Classical.choice, Quot.sound]`.
-/

namespace MutualCorrAgreement

open NNReal Generator ProbabilityTheory ReedSolomon Finset
open CodingTheory.ProximityGap.Hab25Core
open CodingTheory.ProximityGap.Hab25Core.Hab25Johnson
open CodingTheory.ProximityGap.Hab25Core.Hab25JohnsonEndgame
open scoped Polynomial

variable {F : Type} [Field F] [Fintype F] [DecidableEq F]
         {ι : Type} [Fintype ι] [Nonempty ι] [DecidableEq ι]

/-- The rate of the pair power generator is exactly `2^m / |ι|` (as a real number). -/
theorem rate_genRSC_pair (φ : ι ↪ F) (m : ℕ) [Smooth φ] (exp : Fin 2 ↪ ℕ)
    (hk : 2 ^ m ≤ Fintype.card ι) :
    (RSGenerator.genRSC (Fin 2) φ m exp).rate =
      (2 ^ m : ℝ) / (Fintype.card ι : ℝ) := by
  have h := rate_smoothCode_coe (F₀ := F) (ι₀ := ι) φ m hk
  simpa [RSGenerator.genRSC] using h

open Classical in
/-- **The literal pair-case Johnson conjecture from the per-`δ` Johnson numeric
residual.** If, for every admissible `δ` (i.e. `0 < δ < 1 − √ρ` with `ρ = 2^m/|ι|`),
the Hab25 numeric residual `JohnsonNumericBound` holds at the per-`δ` parameter
`η := μ(δ) = min(1 − √ρ − δ, √ρ/20)`, then `mca_johnson_bound_CONJECTURE` holds
verbatim at `parℓ = Fin 2` with exponents `(0, 1)` — `BStar = √ρ` and the conjecture's
exact `errStar`. The closed-form comparison is discharged by
`johnsonBoundReal_le_errStar_real`; no side hypotheses remain. -/
theorem mca_johnson_bound_CONJECTURE_pair_of_johnsonNumericBound
    (α : F) (φ : ι ↪ F) (m : ℕ) [Smooth φ] (exp : Fin 2 ↪ ℕ)
    (hexp0 : exp 0 = 0) (hexp1 : exp 1 = 1)
    (hk : 2 ^ m ≤ Fintype.card ι)
    (hJNB : ∀ δ : ℝ≥0, 0 < δ →
      (δ : ℝ) < 1 - Real.sqrt ((2 ^ m : ℝ) / (Fintype.card ι : ℝ)) →
      JohnsonNumericBound (F₀ := F) (ι₀ := ι) φ (2 ^ m)
        (min (1 - Real.sqrt ((2 ^ m : ℝ) / (Fintype.card ι : ℝ)) - (δ : ℝ))
          (Real.sqrt ((2 ^ m : ℝ) / (Fintype.card ι : ℝ)) / 20)).toNNReal δ) :
    mca_johnson_bound_CONJECTURE α φ m (Fin 2) exp := by
  classical
  have hrate := rate_genRSC_pair φ m exp hk
  have hmca :
      haveI : Fintype (RSGenerator.genRSC (Fin 2) φ m exp).parℓ :=
        (RSGenerator.genRSC (Fin 2) φ m exp).hℓ
      hasMutualCorrAgreement (RSGenerator.genRSC (Fin 2) φ m exp)
        (Real.sqrt (RSGenerator.genRSC (Fin 2) φ m exp).rate)
        (fun x =>
          ENNReal.ofReal
            (((Fintype.card (Fin 2) : ℝ) - 1) * 2 ^ (2 * m) /
              ((Fintype.card F : ℝ) *
                (2 * min
                  (1 - Real.sqrt (RSGenerator.genRSC (Fin 2) φ m exp).rate - x)
                  (Real.sqrt (RSGenerator.genRSC (Fin 2) φ m exp).rate / 20)) ^ 7))) := by
    refine hasMutualCorrAgreement_genRSC_pair_of_epsMCA_le φ m exp hexp0 hexp1
      _ (Real.sqrt_nonneg _) _ ?_
    intro δ hδ0 hδB
    rw [hrate] at hδB
    refine le_trans (hJNB δ hδ0 hδB) ?_
    rw [hrate, show ((Fintype.card (Fin 2) : ℝ) - 1) = 1 from by norm_num, one_mul]
    exact ENNReal.ofReal_le_ofReal
      (johnsonBoundReal_le_errStar_real φ m hk δ hδ0 hδB)
  unfold mca_johnson_bound_CONJECTURE
  exact hmca

open Classical in
/-- **The literal pair-case Johnson conjecture from per-stack Claim-1 cell data alone.**
For every admissible `δ` and word stack, suppose the bad scalars decompose into `≤ L`
cells satisfying the capture-above-`n` dichotomy (the BCIKS20 Steps 5–7 output — the
single remaining deep input of the #302 chain), with `L` within the per-`δ` GS list-size
shape. Then `mca_johnson_bound_CONJECTURE` holds verbatim at `parℓ = Fin 2`: nothing
between the capture data and the literal conjecture statement remains unproven. -/
theorem mca_johnson_bound_CONJECTURE_pair_of_claim1_cells
    (α : F) (φ : ι ↪ F) (m : ℕ) [Smooth φ] (exp : Fin 2 ↪ ℕ)
    (hexp0 : exp 0 = 0) (hexp1 : exp 1 = 1)
    (hk : 2 ^ m ≤ Fintype.card ι) (L : ℕ)
    (hL : ∀ δ : ℝ≥0, 0 < δ →
      (δ : ℝ) < 1 - Real.sqrt ((2 ^ m : ℝ) / (Fintype.card ι : ℝ)) →
      (L : ℝ) ≤ (hab25M (Fintype.card ι) (2 ^ m)
          (min (1 - Real.sqrt ((2 ^ m : ℝ) / (Fintype.card ι : ℝ)) - (δ : ℝ))
            (Real.sqrt ((2 ^ m : ℝ) / (Fintype.card ι : ℝ)) / 20)).toNNReal + 1/2) /
        hab25RhoPlus (Fintype.card ι) (2 ^ m) ^ ((1 : ℝ) / 2))
    (hdata : ∀ δ : ℝ≥0, 0 < δ →
      (δ : ℝ) < 1 - Real.sqrt ((2 ^ m : ℝ) / (Fintype.card ι : ℝ)) →
      ∀ u : Code.WordStack F (Fin 2) ι,
        ∃ (Idx : Type) (_ : DecidableEq Idx) (Index : Finset Idx)
          (Ecell : Idx → Finset F),
          Index.card ≤ L ∧
          (Finset.univ.filter
            (fun γ : F => _root_.ProximityGap.mcaEvent (F := F)
              ((ReedSolomon.code φ (2 ^ m) : Set (ι → F))) δ (u 0) (u 1) γ)) ⊆
            Index.biUnion Ecell ∧
          ∀ ij ∈ Index, Fintype.card ι < (Ecell ij).card →
            ∃ a b : F[X], a.natDegree < 2 ^ m ∧ b.natDegree < 2 ^ m ∧
              ∀ γ ∈ Ecell ij,
                AffineCaptured φ (2 ^ m) δ u γ (a, b)) :
    mca_johnson_bound_CONJECTURE α φ m (Fin 2) exp := by
  refine mca_johnson_bound_CONJECTURE_pair_of_johnsonNumericBound α φ m exp
    hexp0 hexp1 hk ?_
  intro δ hδ0 hδB
  exact johnsonNumericBound_of_claim1_cells φ (2 ^ m) _ δ L hk
    (hL δ hδ0 hδB) (hdata δ hδ0 hδB)

end MutualCorrAgreement

/-! ## Axiom audit — all kernel-clean. -/
#print axioms MutualCorrAgreement.rate_genRSC_pair
#print axioms MutualCorrAgreement.mca_johnson_bound_CONJECTURE_pair_of_johnsonNumericBound
#print axioms MutualCorrAgreement.mca_johnson_bound_CONJECTURE_pair_of_claim1_cells

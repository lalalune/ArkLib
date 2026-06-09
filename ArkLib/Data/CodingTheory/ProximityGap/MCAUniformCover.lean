/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.LineDecodingT421Faithful
import ArkLib.Data.CodingTheory.ProximityGap.BCIKS20.Curves

set_option linter.style.longLine false

/-!
# The clean uniform-weight MCA bound `ε_mca ≤ (n+1)/q` from a δ-close curve cover

`LineDecodingT421Faithful.epsMCA_le_of_forall_gs_curve_cover` bounds `ε_mca(C,δ) ≤ (M·n+1)/q` from a
*weighted* GS curve cover (with weight denominator `M` and weighted-agreement threshold `α`).  This
file specialises it to the **uniform weight** (`M = 1`, `μ ≡ 1`, `α = 1 − δ`), giving the cleanest
possible form of the ABF26 §4.5 MCA bound and re-phrasing the cover hypothesis in terms of ordinary
relative Hamming distance `δᵣ` instead of weighted agreement:

  `ε_mca(C, δ) ≤ (n + 1) / q`,

conditional on the single hypothesis (`hcover`): for every received line `(u₀, u₁)` there is a
codeword-pair `v = (v₀, v₁)` whose affine line `v₀ + γ•v₁` is `δ`-close (`δᵣ ≤ δ`) to the received
line `u₀ + γ•u₁` at *every* bad scalar `γ`, yet `v` fails to correlated-agree with `(u₀, u₁)`
(measure `< 1 − δ`).

This is the **exact open surface** of the MCA grand challenge in its cleanest unconditional shape: the
remaining content is constructing the covering pair `v` (the Guruswami–Sudan list decoder of
`u₀ + Z•u₁` over `F(Z)`).  Everything downstream — the curve list-agreement bound
(`list_agreement_on_curve_implies_correlated_agreement_bound`), the bad-count extraction
(`mcaBadCount_lt_of_gs_curve_cover`), the `δᵣ → weighted agreement` bridge
(`agree_uniformWeight_ge_one_sub_of_relDist_le`) — is proven in tree.

Note that with `M = 1` the bound is `(n+1)/q`, with **no** `ρ`/`η` denominator: the price of the
clean form is that the single-curve `hcover` is the *unique-decoding-strength* cover (one curve
covering all bad scalars).  Near capacity the genuine cover needs `≈ 1/η` curves, which is the
weighted/`M > 1` form; see `epsMCA_le_of_forall_gs_curve_cover` for that general shape.

## Main results

* `polynomialCurveEval_line` — a 2-row polynomial curve is the affine line `v 0 + γ•(v 1)`.
* `epsMCA_le_of_forall_relClose_curve_cover` — `ε_mca ≤ (n+1)/q` from the `δᵣ`-phrased cover.
-/

open scoped BigOperators NNReal ENNReal
open Finset

namespace ProximityGap

set_option linter.unusedSectionVars false
set_option linter.unusedFintypeInType false
set_option linter.unusedDecidableInType false

variable {ι : Type} [Fintype ι] [Nonempty ι] [DecidableEq ι]
variable {F : Type} [Field F] [Fintype F] [DecidableEq F]

/-- A 2-row polynomial curve `polynomialCurveEval v γ` is the affine line `v 0 + γ•(v 1)`. -/
theorem polynomialCurveEval_line (v : Fin 2 → ι → F) (γ : F) :
    (fun x => Curve.polynomialCurveEval (F := F) (A := F) v γ x) = v 0 + γ • v 1 := by
  funext x; simp [Curve.polynomialCurveEval, Fin.sum_univ_two]

/-- **Uniform-weight (M = 1) MCA bound from a `δ`-close curve cover.** If for every received line
`(u₀, u₁)` there is a codeword-pair `v` whose affine line `v₀ + γ•v₁` is `δ`-close (`δᵣ ≤ δ`) to the
received line `u₀ + γ•u₁` at every bad scalar `γ`, yet `v` does **not** correlated-agree with `u`
(uniform measure `< 1 − δ`), then `ε_mca(C, δ) ≤ (n + 1) / q`.

The `δ`-close clause is converted to uniform weighted agreement `≥ 1 − δ` via the in-tree
`agree_uniformWeight_ge_one_sub_of_relDist_le`; the conclusion is then the `M = 1` instance of
`epsMCA_le_of_forall_gs_curve_cover`. -/
theorem epsMCA_le_of_forall_relClose_curve_cover
    (C : Set (ι → F)) (δ : ℝ≥0)
    (hcover : ∀ u : Code.WordStack F (Fin 2) ι, ∃ v : Fin 2 → ι → F,
      (∀ γ : F, mcaEvent C δ (u 0) (u 1) γ →
          δᵣ((u 0) + γ • (u 1), (v 0) + γ • (v 1)) ≤ δ) ∧
      WeightedAgreement.mu_set (uniformWeight (ι := ι))
          { x : ι | ∀ i, (![u 0, u 1] : Fin 2 → ι → F) i x = v i x } < ((1 - δ : ℝ≥0) : ℝ)) :
    epsMCA (F := F) (A := F) C δ ≤
      ((Fintype.card ι + 1 : ℕ) : ENNReal) / (Fintype.card F : ENNReal) := by
  classical
  have hμ : ∀ i : ι, ∃ n : ℤ, (uniformWeight (ι := ι) i).1 = (n : ℚ) / ((1 : ℕ) : ℚ) :=
    fun i => ⟨1, by simp [uniformWeight]⟩
  have h := epsMCA_le_of_forall_gs_curve_cover (F := F) (ι := ι) C δ
    (uniformWeight (ι := ι)) 1 (by norm_num) hμ (1 - δ) ?_
  · simpa using h
  · intro u
    obtain ⟨v, hclose, hfail⟩ := hcover u
    refine ⟨v, ?_, hfail⟩
    intro γ hγ
    have hd := hclose γ hγ
    rw [polynomialCurveEval_line v γ,
      show (fun x => Curve.polynomialCurveEval (F := F) (A := F) ![u 0, u 1] γ x)
        = u 0 + γ • u 1 from polynomialCurveEval_line ![u 0, u 1] γ |>.trans (by simp)]
    exact agree_uniformWeight_ge_one_sub_of_relDist_le hd

end ProximityGap

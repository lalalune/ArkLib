/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.BCIKS20.Curves.CoeffExtractionResidual

/-!
# Issue #304 — vacuous-regime discharges of the BCIKS20 §5 strict coefficient-extraction core

`CurveCommonAgreementResidual` (the geometric form of the strict Johnson-branch
coefficient-polynomial residual `StrictCoeffPolysResidual`, the open core of #304 gating
STIR/WHIR/FRI soundness) carries the probability hypothesis `Pr > k · errorBound`. Since every
probability is `≤ 1`, the residual holds **unconditionally** whenever `1 ≤ k · errorBound`.

Composing with the existing bound `errorBound_ge_const : n/q ≤ errorBound` (valid for `0 < deg`
and `δ < 1 − √ρ`), this discharges the residual — and through the proven bivariate-Lagrange
reduction `strictCoeffPolysResidual_of_commonAgreement`, the full `StrictCoeffPolysResidual` —
for **every field with `q ≤ k·n`**. In particular every full-domain Reed–Solomon code
(`ι = F`, `n = q`) satisfies this at any curve dimension `k ≥ 1`.

## Honest scope

These are *vacuous-regime* discharges: they show the BCIKS20 probability threshold is
unsatisfiable when the field is at most `k` times the evaluation domain (`errorBound ≥ n/q ≥ 1/k`),
so the conditional content is empty there. The genuinely open content of #304 is the
**large-field regime `q > k·n`** (the deployed FRI/STIR setting, smooth subdomain `n ≪ q`),
where the §5 Guruswami–Sudan/Hensel counting must produce the common agreement. Axiom-clean
(`[propext, Classical.choice, Quot.sound]`).
-/
namespace ProximityGap

open NNReal Finset Function ProbabilityTheory Code Polynomial
open scoped BigOperators LinearCode ProbabilityTheory ENNReal

variable {ι : Type} [Fintype ι] [Nonempty ι] [DecidableEq ι]
         {F : Type} [Field F] [Fintype F] [DecidableEq F]

/-- **Vacuous-regime discharge (abstract form).** If `1 ≤ k · errorBound`, then the probability
hypothesis `Pr > k·errorBound` of the geometric common-agreement residual is unsatisfiable
(every probability is `≤ 1`), so `CurveCommonAgreementResidual` holds. -/
theorem curveCommonAgreementResidual_of_one_le_mul {k deg : ℕ} {domain : ι ↪ F} {δ : ℝ≥0}
    (h : (1 : ENNReal) ≤ (k : ENNReal) * (errorBound δ deg domain : ENNReal)) :
    CurveCommonAgreementResidual (k := k) (deg := deg) (domain := domain) (δ := δ) := by
  intro _hk u hprob _hJ _hsqrt _P _hP
  exact absurd (lt_of_le_of_lt h hprob) (not_lt.mpr (PMF.coe_le_one _ _))

/-- **Vacuous-regime discharge (small-field form).** If `q ≤ k · n` (field at most `k` times the
evaluation-domain size — e.g. any full-domain RS code with `k ≥ 1`), then `1 ≤ k·errorBound`
via `errorBound_ge_const : n/q ≤ errorBound`, and the residual holds. -/
theorem curveCommonAgreementResidual_of_card_le {k deg : ℕ} {domain : ι ↪ F} {δ : ℝ≥0}
    (hdeg : 0 < deg)
    (hδ : δ < 1 - ReedSolomon.sqrtRate deg domain)
    (hq : (Fintype.card F : ℝ≥0) ≤ (k : ℝ≥0) * (Fintype.card ι : ℝ≥0)) :
    CurveCommonAgreementResidual (k := k) (deg := deg) (domain := domain) (δ := δ) := by
  refine curveCommonAgreementResidual_of_one_le_mul (k := k) ?_
  have hconst : (Fintype.card ι : ℝ≥0) / (Fintype.card F : ℝ≥0) ≤ errorBound δ deg domain :=
    DivergenceOfSets.errorBound_ge_const (deg := deg) (domain := domain) hdeg hδ
  -- 1 ≤ k·(n/q) since q ≤ k·n, and k·(n/q) ≤ k·errorBound.
  have hqpos : (0 : ℝ≥0) < (Fintype.card F : ℝ≥0) := by
    exact_mod_cast (Fintype.card_pos : 0 < Fintype.card F)
  have hone : (1 : ℝ≥0) ≤ (k : ℝ≥0) * ((Fintype.card ι : ℝ≥0) / (Fintype.card F : ℝ≥0)) := by
    rw [mul_div_assoc', le_div_iff₀ hqpos, one_mul]
    exact hq
  have hstep : (1 : ℝ≥0) ≤ (k : ℝ≥0) * errorBound δ deg domain :=
    le_trans hone (mul_le_mul_left' hconst _)
  exact_mod_cast hstep

/-- **Vacuous-regime `StrictCoeffPolysResidual` (abstract form).** Composes the vacuous
common-agreement discharge through the proven bivariate-Lagrange reduction. -/
theorem strictCoeffPolysResidual_of_one_le_mul {k deg : ℕ} {domain : ι ↪ F} {δ : ℝ≥0}
    [NeZero deg]
    (h : (1 : ENNReal) ≤ (k : ENNReal) * (errorBound δ deg domain : ENNReal)) :
    StrictCoeffPolysResidual (k := k) (deg := deg) (domain := domain) (δ := δ) :=
  strictCoeffPolysResidual_of_commonAgreement
    (curveCommonAgreementResidual_of_one_le_mul h)

/-- **Vacuous-regime `StrictCoeffPolysResidual` (small-field form, `q ≤ k·n`).** -/
theorem strictCoeffPolysResidual_of_card_le {k deg : ℕ} {domain : ι ↪ F} {δ : ℝ≥0}
    [NeZero deg]
    (hdeg : 0 < deg)
    (hδ : δ < 1 - ReedSolomon.sqrtRate deg domain)
    (hq : (Fintype.card F : ℝ≥0) ≤ (k : ℝ≥0) * (Fintype.card ι : ℝ≥0)) :
    StrictCoeffPolysResidual (k := k) (deg := deg) (domain := domain) (δ := δ) :=
  strictCoeffPolysResidual_of_commonAgreement
    (curveCommonAgreementResidual_of_card_le hdeg hδ hq)

end ProximityGap

#print axioms ProximityGap.curveCommonAgreementResidual_of_one_le_mul
#print axioms ProximityGap.curveCommonAgreementResidual_of_card_le
#print axioms ProximityGap.strictCoeffPolysResidual_of_one_le_mul
#print axioms ProximityGap.strictCoeffPolysResidual_of_card_le

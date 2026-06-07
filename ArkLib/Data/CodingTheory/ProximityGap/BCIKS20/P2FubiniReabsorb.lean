/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.BCIKS20.P2Reabsorb
import ArkLib.Data.CodingTheory.ProximityGap.BCIKS20.P2FilterDrop
import ArkLib.Data.CodingTheory.ProximityGap.BCIKS20.P2KeystoneReindex

/-!
# BCIKS20 Appendix A.4 — per-partition Y-degree reabsorption (the Fubini core)

After `partitionSum_drop_card_filter` removes the `i`-dependent `|λ| ≤ i` constraint and the `i`/`λ`
sums are Fubini-swapped, the inner object — for a *fixed* partition `λ` with `m = |λ|` parts,
multiplicity `cp = countPerms λ`, and coefficient product `Plam` — is the Y-degree sum

  `∑_{i ∈ range (Q.natDegree+1)} lift((Δ_X^{i₁}R)|_{x₀}).coeff i · ((C(i,m)·cp) • (α₀^{i-m} · Plam))`.

`inner_Ydegree_sum_eq_countPerms_hasseEvalAtRoot` collapses this to `cp • (hasseEvalAtRoot i₁ m · Plam)`
using `coeff_zero_βHenselAssembled` (`α₀ = T/W`) and `hasseEvalAtRoot_eq_QDegreeBinomReindex`
(the Y-degree reabsorption). The remaining manipulation is pure `CommSemiring` `ℕ`-scalar algebra
(`nsmul_eq_mul` + `ring`), term by term — this is the genuine algebraic content of the Fubini step.

NO `axiom`/`admit`/`native_decide`/`sorry`. Audited in-file via `#print axioms`.
-/

namespace BCIKS20.HenselNumerator

open scoped BigOperators
open Finset
open Polynomial Polynomial.Bivariate
open ArkLib.PowerSeriesComposition
open BCIKS20AppendixA
open ProximityPrize.BCIKS20.GammaGenuine

variable {F : Type} [Field F]
variable (H : F[X][Y]) [Fact (Irreducible H)] [Fact (0 < H.natDegree)]

/-- **Per-partition Y-degree reabsorption (PROVEN).**  For a fixed partition datum `(m, cp, Plam)`,
the inner Y-degree sum of the LHS partition form collapses to `cp • (hasseEvalAtRoot i₁ m · Plam)`.

Route: rewrite the base `α₀ = coeff 0 βHenselAssembled` to `T/W` (`coeff_zero_βHenselAssembled`),
expand `hasseEvalAtRoot i₁ m` over the same `Q`-degree range (`hasseEvalAtRoot_eq_QDegreeBinomReindex`),
push the `cp •` and `· Plam` through the sum (`Finset.sum_mul`/`Finset.smul_sum`), and close term by
term with `nsmul_eq_mul` + `ring`. -/
theorem inner_Ydegree_sum_eq_countPerms_hasseEvalAtRoot
    (x₀ : F) (R : F[X][X][Y]) (hHyp : ClaimA2.Hypotheses x₀ R H) (i1 m cp : ℕ) (Plam : 𝕃 H) :
    (∑ i ∈ Finset.range ((Q x₀ R H).natDegree + 1),
        liftToFunctionField (H := H)
            ((Bivariate.evalX (Polynomial.C x₀) (hasseDerivX i1 R)).coeff i)
          * ((i.choose m * cp) •
              ((PowerSeries.coeff 0 (βHenselAssembled H x₀ R hHyp)) ^ (i - m) * Plam)))
      = cp • (hasseEvalAtRoot H x₀ R i1 m * Plam) := by
  have hα0 : PowerSeries.coeff 0 (βHenselAssembled H x₀ R hHyp) = α₀ H := by
    rw [PowerSeries.coeff_zero_eq_constantCoeff_apply, βHenselAssembled_constantCoeff]
  rw [hα0, ← taylorCollapse (H := H) x₀ R i1 m]
  simp only [nsmul_eq_mul, Nat.cast_mul, Finset.sum_mul, Finset.mul_sum]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  ring

end BCIKS20.HenselNumerator

-- Axiom audit.
#print axioms BCIKS20.HenselNumerator.inner_Ydegree_sum_eq_countPerms_hasseEvalAtRoot

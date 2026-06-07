/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.BCIKS20.P2KeystoneReindex

/-!
# BCIKS20 Appendix A.4 — Y-degree reabsorption toward `RestrictedFaaDiBrunoMatch`

This module supplies two small, P2-independent algebraic bridges used in the term-by-term
identification between the **LHS partition form** of `restrictedFaaDiBrunoSum`
(`restrictedFaaDiBrunoSum_eq_partitionForm`, indexed by the Y-degree `i` with a `C(i,|λ|)`
binomial and an `α₀^{i-|λ|}` factor) and the **RHS recursion form**
(`coeff_succ_βHenselAssembled_partitionForm`, packaging the iterated-Hasse coefficient as
`hasseEvalAtRoot` inside `B_coeff`).

* `coeff_zero_βHenselAssembled` — the order-0 coefficient of the assembled series is the base
  root `α₀ = T/W` (so the `α₀^{i-|λ|}` factor on the LHS *is* a power of `T/W`).
* `hasseEvalAtRoot_eq_binomReindex` — the α₀-Taylor identity `hasseEvalAtRoot_eq_taylorSum`,
  reindexed `j = i + m` into the **`C(j,m)·coeff j·(T/W)^{j-m}`** shape that the LHS
  partition-form inner sum (over the Y-degree `j`, at a partition with `|λ| = m` parts) exposes.
  This is the entropy-free reabsorption of the Y-degree sum into the single embedding object
  `hasseEvalAtRoot`.

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

/-- **Order-0 coefficient of the assembled series is `α₀ = T/W` (PROVEN).**  The `α₀^{i-|λ|}`
factor appearing on the LHS of `RestrictedFaaDiBrunoMatch` (via
`restrictedFaaDiBrunoSum_eq_partitionForm`, where `α₀ := coeff 0 βHenselAssembled`) is therefore a
power of the base root `T/W` — exactly the `(T/W)^i` factor in the α₀-Taylor identity
`hasseEvalAtRoot_eq_taylorSum`. -/
theorem coeff_zero_βHenselAssembled (x₀ : F) (R : F[X][X][Y])
    (hHyp : ClaimA2.Hypotheses x₀ R H) :
    PowerSeries.coeff 0 (βHenselAssembled H x₀ R hHyp)
      = functionFieldT (H := H) / liftToFunctionField (H := H) H.leadingCoeff := by
  rw [PowerSeries.coeff_zero_eq_constantCoeff_apply, βHenselAssembled_constantCoeff]
  rfl

/-- **Y-degree reabsorption: the α₀-Taylor identity in `C(j,m)` binomial form (PROVEN).**
Reindexing `hasseEvalAtRoot_eq_taylorSum` by `j = i + m`:

  `hasseEvalAtRoot i₁ m
     = ∑_{j ∈ {m, …, N+m}} C(j,m) · (lift((Δ_X^{i₁}R)|_{x₀}).coeff j) · (T/W)^{j-m}`,

where `N = natDegreeY (Δ_X^{i₁}(Δ_Y^m R)|_{x₀})`.  This is the exact shape consumed by the LHS
partition-form inner sum (the `C(i,|λ|)·coeff i·α₀^{i-|λ|}` terms with `m = |λ|`): the Y-degree
sum over `j` collapses, term for term, into the single embedding object `hasseEvalAtRoot`. -/
theorem hasseEvalAtRoot_eq_binomReindex (x₀ : F) (R : F[X][X][Y]) (i1 m : ℕ) :
    hasseEvalAtRoot H x₀ R i1 m
      = ∑ j ∈ (Finset.range ((Bivariate.evalX (Polynomial.C x₀)
              (hasseDerivX i1 (hasseDerivY m R))).natDegree + 1)).map (addRightEmbedding m),
          (j.choose m)
            • (liftToFunctionField (H := H)
                  ((Bivariate.evalX (Polynomial.C x₀) (hasseDerivX i1 R)).coeff j)
                * (functionFieldT (H := H) / liftToFunctionField (H := H) H.leadingCoeff)
                    ^ (j - m)) := by
  rw [hasseEvalAtRoot_eq_taylorSum, Finset.sum_map]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  simp only [addRightEmbedding_apply, Nat.add_sub_cancel]

/-- **Y-degree reabsorption over the `Q`-degree range (PROVEN).**
This is the fixed-range version consumed by the partition-form P2 comparison: over the full
`Q x₀ R H` Y-degree range, all out-of-window binomial terms vanish and the same
`C(j,m) · coeff_j · α₀^(j-m)` sum collapses to `hasseEvalAtRoot`.

It is a theorem-level wrapper around `P2KeystoneReindex.taylorCollapse`, exposed here alongside the
other reabsorption bricks so the remaining cleared-vs-uncleared comparison can cite the exact
`Q`-range form without importing the keystone module directly. -/
theorem hasseEvalAtRoot_eq_QDegreeBinomReindex (x₀ : F) (R : F[X][X][Y]) (i1 m : ℕ) :
    hasseEvalAtRoot H x₀ R i1 m
      = ∑ j ∈ Finset.range ((Q x₀ R H).natDegree + 1),
          (j.choose m)
            • (liftToFunctionField (H := H)
                  ((Bivariate.evalX (Polynomial.C x₀) (hasseDerivX i1 R)).coeff j)
                * (functionFieldT (H := H) / liftToFunctionField (H := H) H.leadingCoeff)
                    ^ (j - m)) := by
  rw [← taylorCollapse (H := H) x₀ R i1 m]
  simp [α₀]

end BCIKS20.HenselNumerator

-- Axiom audit.
#print axioms BCIKS20.HenselNumerator.coeff_zero_βHenselAssembled
#print axioms BCIKS20.HenselNumerator.hasseEvalAtRoot_eq_binomReindex
#print axioms BCIKS20.HenselNumerator.hasseEvalAtRoot_eq_QDegreeBinomReindex

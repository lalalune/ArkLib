/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.BCIKS20.P2BijectionApply

/-!
# BCIKS20 Appendix A.4 — Y-degree reabsorption toward `RestrictedFaaDiBrunoMatch`

This module supplies P2-independent algebraic bridges used in the term-by-term identification
between the **LHS partition form** of `restrictedFaaDiBrunoSum`
(`restrictedFaaDiBrunoSum_eq_partitionForm`, indexed by the Y-degree `i` with a `C(i,|λ|)`
binomial and an `α₀^{i-|λ|}` factor) and the **RHS recursion form**
(`coeff_succ_βHenselAssembled_partitionForm`, packaging the iterated-Hasse coefficient as
`hasseEvalAtRoot` inside `B_coeff`).

* `coeff_zero_βHenselAssembled` — the order-0 coefficient of the assembled series is the base
  root `α₀ = T/W` (so the `α₀^{i-|λ|}` factor on the LHS *is* a power of `T/W`).
* `hasseEvalAtRoot_eq_binomReindex` — the α₀-Taylor identity `hasseEvalAtRoot_eq_taylorSum`,
  reindexed `j = i + m` into the **`C(j,m)·coeff j·(T/W)^{j-m}`** shape.
* `hasseEvalAtRoot_eq_fixedRange` — the same identity over *any* range `{0,…,N}` wide enough,
  exactly the LHS inner sum of `RestrictedFaaDiBrunoMatch` (over `j ∈ range (Q.natDegree+1)`):
  the Y-degree sum collapses into the single embedding object `hasseEvalAtRoot`, with the
  out-of-window terms vanishing char-independently.

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

where `N = natDegreeY (Δ_X^{i₁}(Δ_Y^m R)|_{x₀})`. -/
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

/-- **Y-degree reabsorption over a fixed range (PROVEN, char-independent).**  For any range
`{0, …, N}` wide enough to contain the Y-degrees of `Δ_X^{i₁}(Δ_Y^m R)|_{x₀}` (shifted by `m`),

  `hasseEvalAtRoot i₁ m
     = ∑_{j ∈ range (N+1)} C(j,m) · (lift((Δ_X^{i₁}R)|_{x₀}).coeff j) · (T/W)^{j-m}`.

This is exactly the LHS inner sum of `RestrictedFaaDiBrunoMatch`
(`restrictedFaaDiBrunoSum_eq_partitionForm`, at a partition with `m = |λ|` parts, summed over the
Y-degree `j ∈ range (Q.natDegree + 1)`): the whole Y-degree sum collapses, term for term, into the
single embedding object `hasseEvalAtRoot`.  The out-of-window terms vanish char-independently — the
low terms `j < m` by `C(j,m) = 0`, the high terms `j - m > deg` because
`C(j,m) • coeff_j = (Δ_Y^m object).coeff (j-m)` (the binomial sits *inside* the Hasse coefficient
via `evalX_hasseDeriv_Y_coeff`) which is `0` past the degree. -/
theorem hasseEvalAtRoot_eq_fixedRange (x₀ : F) (R : F[X][X][Y]) (i1 m N : ℕ)
    (hN : (Bivariate.evalX (Polynomial.C x₀)
            (hasseDerivX i1 (hasseDerivY m R))).natDegree + m ≤ N) :
    hasseEvalAtRoot H x₀ R i1 m
      = ∑ j ∈ Finset.range (N + 1),
          (j.choose m)
            • (liftToFunctionField (H := H)
                  ((Bivariate.evalX (Polynomial.C x₀) (hasseDerivX i1 R)).coeff j)
                * (functionFieldT (H := H) / liftToFunctionField (H := H) H.leadingCoeff)
                    ^ (j - m)) := by
  rw [hasseEvalAtRoot_eq_binomReindex]
  refine Finset.sum_subset ?_ ?_
  · -- the `binomReindex` window `{m, …, deg + m}` sits inside `range (N+1)`.
    intro j hj
    rw [Finset.mem_map] at hj
    obtain ⟨i, hi, rfl⟩ := hj
    rw [Finset.mem_range] at hi ⊢
    rw [addRightEmbedding_apply]
    omega
  · -- the terms of `range (N+1)` outside the window vanish.
    intro j _ hjnot
    by_cases hjm : j < m
    · rw [Nat.choose_eq_zero_of_lt hjm, zero_smul]
    · have hjm' : m ≤ j := not_lt.mp hjm
      have hgap : (Bivariate.evalX (Polynomial.C x₀)
          (hasseDerivX i1 (hasseDerivY m R))).natDegree < j - m := by
        by_contra h
        rw [Nat.not_lt] at h
        exact hjnot (Finset.mem_map.mpr
          ⟨j - m, Finset.mem_range.mpr (by omega), by rw [addRightEmbedding_apply]; omega⟩)
      have hjmm : j - m + m = j := by omega
      have hcoeff := evalX_hasseDeriv_Y_coeff x₀ R i1 m (j - m)
      rw [hjmm] at hcoeff
      rw [← smul_mul_assoc, ← map_nsmul, ← hcoeff,
        Polynomial.coeff_eq_zero_of_natDegree_lt hgap, map_zero, zero_mul]

end BCIKS20.HenselNumerator

-- Axiom audit.
#print axioms BCIKS20.HenselNumerator.coeff_zero_βHenselAssembled
#print axioms BCIKS20.HenselNumerator.hasseEvalAtRoot_eq_binomReindex
#print axioms BCIKS20.HenselNumerator.hasseEvalAtRoot_eq_fixedRange

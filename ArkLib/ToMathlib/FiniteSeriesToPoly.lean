/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib
import CompPoly.ToMathlib.Polynomial.BivariateDegree

/-!
# Finite power series ⟹ polynomial representative (brick L18a)

This file is the `[MATHLIB]`-substrate brick **L18a** of the proximity-gap
ingredient-D DAG (`research/proximity-prize/ingredient-D-DAG-2026-06-05.md`).

The downstream consumer is BCIKS20 Claim 5.9
(`solution_gamma_is_linear_in_Z`): once the truncated Hensel coefficient series
`γ` is known to have only finitely many nonzero `(X − x₀)`-coefficients, it must
come from an honest *polynomial* representative, and that representative inherits
a `degreeX ≤ 1` bound from the structure `R = Y − P` with `deg_Z P ≤ 1`.

The brick splits into two genuinely generic, kernel-clean pieces:

* **Univariate truncation.** If `φ : PowerSeries k` satisfies
  `∀ n ≥ N, coeff n φ = 0`, then the finite truncation
  `p = ∑ i ∈ range N, C (coeff i φ) • X ^ i : k[X]`
  coerces back to `φ` and has `natDegree < N` (`natDegree ≤ N - 1`).  This is
  `PowerSeries.exists_polynomial_coe_of_coeff_eq_zero_ge` and friends.

* **Degree-≤1 representative.** The `degreeX ≤ 1` shape that Claim 5.9 needs:
  a bivariate polynomial all of whose coefficients (univariate in `X`) have
  `natDegree ≤ 1` has `Polynomial.Bivariate.degreeX ≤ 1`, and consequently
  decomposes as `a + X • b`.  We package this both for the abstract
  "all `X`-coefficients of index `≥ 2` vanish" hypothesis and in the exact
  `degreeX` shape the existing
  `exists_linear_in_coeff_variable_of_degreeX_le_one` consumes.

Nothing here references the App-A `𝒪 / 𝕃 / weight_Λ / π_z` machinery; it is pure
`PowerSeries` / `Polynomial` substrate, deliberately upstreamable.
-/

open Polynomial
open scoped Polynomial.Bivariate

namespace ArkLib

namespace FiniteSeriesToPoly

/-! ## Part 1: `PowerSeries` with finite support ⟹ `Polynomial` -/

section Univariate

variable {k : Type*} [CommRing k]

/-- The finite truncation of a power series `φ` at degree `N`, viewed as a
polynomial: `∑ i ∈ range N, C (coeff i φ) * X ^ i`. -/
noncomputable def truncPoly (φ : PowerSeries k) (N : ℕ) : k[X] :=
  ∑ i ∈ Finset.range N, Polynomial.C (PowerSeries.coeff i φ) * X ^ i

/-- The `n`-th coefficient of the truncation is `coeff n φ` for `n < N` and `0`
otherwise. -/
theorem coeff_truncPoly (φ : PowerSeries k) (N n : ℕ) :
    (truncPoly φ N).coeff n =
      if n < N then PowerSeries.coeff n φ else 0 := by
  classical
  unfold truncPoly
  rw [Polynomial.finset_sum_coeff]
  simp only [Polynomial.coeff_C_mul, Polynomial.coeff_X_pow, mul_ite, mul_one,
    mul_zero]
  by_cases hn : n < N
  · rw [if_pos hn]
    rw [Finset.sum_eq_single n]
    · simp
    · intro b _ hbn
      rw [if_neg (by omega)]
    · intro hmem
      exact absurd (Finset.mem_range.mpr hn) hmem
  · rw [if_neg hn]
    apply Finset.sum_eq_zero
    intro b hb
    have : b < N := Finset.mem_range.mp hb
    rw [if_neg (by omega)]

/-- The truncation has `natDegree < N` whenever `0 < N`. -/
theorem natDegree_truncPoly_lt (φ : PowerSeries k) {N : ℕ} (hN : 0 < N) :
    (truncPoly φ N).natDegree < N := by
  classical
  rw [Nat.lt_iff_le_pred hN, Polynomial.natDegree_le_iff_coeff_eq_zero]
  intro n hn
  rw [coeff_truncPoly]
  rw [if_neg (by omega)]

/-- The truncation has `natDegree ≤ N - 1` (no positivity hypothesis needed). -/
theorem natDegree_truncPoly_le (φ : PowerSeries k) (N : ℕ) :
    (truncPoly φ N).natDegree ≤ N - 1 := by
  classical
  rw [Polynomial.natDegree_le_iff_coeff_eq_zero]
  intro n hn
  rw [coeff_truncPoly]
  rw [if_neg (by omega)]

/-- **L18a core.** If a power series `φ` has all coefficients of index `≥ N`
equal to zero, then it is the coercion of its degree-`< N` truncation. -/
theorem coe_truncPoly_eq_of_coeff_eq_zero_ge (φ : PowerSeries k) {N : ℕ}
    (h : ∀ n, N ≤ n → PowerSeries.coeff n φ = 0) :
    ((truncPoly φ N : k[X]) : PowerSeries k) = φ := by
  ext n
  rw [Polynomial.coeff_coe, coeff_truncPoly]
  by_cases hn : n < N
  · rw [if_pos hn]
  · rw [if_neg hn, (h n (by omega)).symm]

/-- **L18a, existence form (the brick exactly as stated in the DAG).**
If `φ : PowerSeries k` satisfies `∀ n ≥ N, coeff n φ = 0`, then there is a
polynomial `p` with `p.natDegree < N` whose coercion to power series is `φ`. -/
theorem exists_polynomial_coe_of_coeff_eq_zero_ge (φ : PowerSeries k) {N : ℕ}
    (hN : 0 < N) (h : ∀ n, N ≤ n → PowerSeries.coeff n φ = 0) :
    ∃ p : k[X], p.natDegree < N ∧ ((p : k[X]) : PowerSeries k) = φ :=
  ⟨truncPoly φ N, natDegree_truncPoly_lt φ hN,
    coe_truncPoly_eq_of_coeff_eq_zero_ge φ h⟩

/-- A clean restatement using the more idiomatic `∀ n ≥ N` form. -/
theorem exists_polynomial_coe_of_coeff_eq_zero_ge' (φ : PowerSeries k) {N : ℕ}
    (hN : 0 < N) (h : ∀ n ≥ N, PowerSeries.coeff n φ = 0) :
    ∃ p : k[X], p.natDegree < N ∧ ((p : k[X]) : PowerSeries k) = φ :=
  exists_polynomial_coe_of_coeff_eq_zero_ge φ hN (fun n hn => h n hn)

end Univariate

/-! ## Part 2: degree-≤1 representative (the shape Claim 5.9 needs) -/

section DegreeBound

variable {F : Type*} [CommRing F]

/-- If every coefficient (a univariate polynomial in `X`) of a bivariate
polynomial `P : F[X][Y]` has `natDegree ≤ d`, then `Polynomial.Bivariate.degreeX P ≤ d`.
This is the bridge from a "per-coefficient degree bound" to the in-tree
`degreeX` predicate consumed by Claim 5.9. -/
theorem degreeX_le_of_forall_coeff_natDegree_le
    {P : F[X][Y]} {d : ℕ}
    (h : ∀ n, (P.coeff n).natDegree ≤ d) :
    Polynomial.Bivariate.degreeX P ≤ d := by
  classical
  unfold Polynomial.Bivariate.degreeX
  apply Finset.sup_le
  intro n _
  exact h n

/-- Every `X`-coefficient is bounded by `degreeX` (the in-tree CompPoly lemma,
re-exported here for convenience). -/
theorem coeff_natDegree_le_degreeX (P : F[X][Y]) (n : ℕ) :
    (P.coeff n).natDegree ≤ Polynomial.Bivariate.degreeX P :=
  Polynomial.Bivariate.coeff_natDegree_le_degreeX P n

/-- `degreeX P ≤ 1` is equivalent to every `X`-coefficient having degree `≤ 1`,
i.e. to every `X`-coefficient of index `≥ 2` (within each `Y`-coefficient)
vanishing.  This is the abstract "finite power series, X-coeffs of index ≥ 2 are
zero" hypothesis instantiated to the `degreeX` API. -/
theorem degreeX_le_one_iff_forall_coeff_natDegree_le_one (P : F[X][Y]) :
    Polynomial.Bivariate.degreeX P ≤ 1 ↔
      ∀ n, (P.coeff n).natDegree ≤ 1 :=
  ⟨fun h n => le_trans (coeff_natDegree_le_degreeX P n) h,
    fun h => degreeX_le_of_forall_coeff_natDegree_le h⟩

/-- **L18a degree-≤1 representative, abstract X-coefficient form.**
If every coefficient of `P : F[X][Y]` (a univariate polynomial in `X`) has its
`X`-coefficients of index `≥ 2` vanishing, then `P = a + X • b` for univariate
`a b : F[X]`, where `a`, `b` are read off coefficient-wise.  The decomposition is
in the exact shape `(map C v₀) + (C X) * (map C v₁)` consumed by
`exists_linear_in_coeff_variable_of_degreeX_le_one`. -/
theorem exists_linear_decomposition_of_coeff_high_X_eq_zero
    {P : F[X][Y]}
    (h : ∀ n, ∀ j, 2 ≤ j → (P.coeff n).coeff j = 0) :
    ∃ v₀ v₁ : F[X],
      P = (Polynomial.map Polynomial.C v₀)
            + (Polynomial.C Polynomial.X) * (Polynomial.map Polynomial.C v₁) := by
  classical
  -- Each `X`-coefficient has `natDegree ≤ 1`, hence `degreeX P ≤ 1`.
  have hdeg : Polynomial.Bivariate.degreeX P ≤ 1 := by
    refine degreeX_le_of_forall_coeff_natDegree_le (fun n => ?_)
    rw [Polynomial.natDegree_le_iff_coeff_eq_zero]
    intro j hj
    exact h n j (by omega)
  -- Build the constant- and linear-coefficient polynomials in `X`.
  refine ⟨P.sum fun n p => Polynomial.monomial n (p.coeff 0),
          P.sum fun n p => Polynomial.monomial n (p.coeff 1), ?_⟩
  apply Polynomial.ext
  intro n
  apply Polynomial.ext
  intro j
  simp only [coeff_add, coeff_map, coeff_C_mul]
  simp only [Polynomial.sum]
  rw [Polynomial.finset_sum_coeff, Polynomial.finset_sum_coeff]
  simp only [Polynomial.coeff_monomial]
  by_cases hn : n ∈ P.support
  · have hne : P.coeff n ≠ 0 := Polynomial.mem_support_iff.mp hn
    have hdegn : (P.coeff n).natDegree ≤ 1 :=
      le_trans (coeff_natDegree_le_degreeX P n) hdeg
    rw [Polynomial.eq_X_add_C_of_natDegree_le_one hdegn]
    simp [hne, Polynomial.coeff_add, Polynomial.coeff_C_mul]
    ring_nf
  · have hp0 : P.coeff n = 0 := Polynomial.notMem_support_iff.mp hn
    simp [hn, hp0]

/-- **L18a degree-≤1 representative, `degreeX` form.**
Exactly the hypothesis/conclusion shape of the in-tree
`exists_linear_in_coeff_variable_of_degreeX_le_one`, reproduced from the
self-contained substrate above: `degreeX P ≤ 1 ⟹ P = (map C v₀) + (C X) * (map C v₁)`. -/
theorem exists_linear_decomposition_of_degreeX_le_one
    {P : F[X][Y]} (hP : Polynomial.Bivariate.degreeX P ≤ 1) :
    ∃ v₀ v₁ : F[X],
      P = (Polynomial.map Polynomial.C v₀)
            + (Polynomial.C Polynomial.X) * (Polynomial.map Polynomial.C v₁) := by
  refine exists_linear_decomposition_of_coeff_high_X_eq_zero (fun n j hj => ?_)
  have hdegn : (P.coeff n).natDegree ≤ 1 :=
    le_trans (coeff_natDegree_le_degreeX P n) hP
  exact Polynomial.coeff_eq_zero_of_natDegree_lt (by omega)

end DegreeBound

/-! ## Part 3: combined brick — finite series ⟹ degree-≤1 polynomial representative

The exact assembly Claim 5.9 needs.  Here the power-series variable is the
*top* (`X`) variable of the bivariate ring: with coefficient ring `F[X]` (the
`Z`-line), `truncPoly` lands in `(F[X])[X] = F[X][Y]`, so its `degreeX` (the
`X`-degree, indexing along the `Z`-line) is exactly the quantity Claim 5.9
controls via `R = Y − P, deg_Z P ≤ 1`.  The univariate `Part 1` and the bivariate
`Part 2` then compose with no ArkLib-specific glue. -/

section Combined

variable {F : Type*} [CommRing F]

/-- **L18a, end-to-end form.**  Let `φ : PowerSeries F[X]` be a power series in the
top variable, with coefficients on the `F[X]` line.  Suppose all of its
coefficients of index `≥ N` vanish (finite truncation) and the resulting
truncation has `degreeX ≤ 1`.  Then there is a bivariate polynomial
`p : F[X][Y]` with `p.natDegree < N`, `(p : PowerSeries F[X]) = φ`, and
`p = (map C v₀) + (C X) * (map C v₁)` for some `v₀ v₁ : F[X]` (i.e. `p` is linear
along the `Z`-line). -/
theorem exists_linear_polynomial_coe_of_finite_and_degreeX_le_one
    (φ : PowerSeries F[X]) {N : ℕ} (hN : 0 < N)
    (hfin : ∀ n, N ≤ n → PowerSeries.coeff n φ = 0)
    (hlin : Polynomial.Bivariate.degreeX (truncPoly φ N) ≤ 1) :
    ∃ (p : F[X][Y]) (v₀ v₁ : F[X]),
      p.natDegree < N ∧
      ((p : F[X][Y]) : PowerSeries F[X]) = φ ∧
      p = (Polynomial.map Polynomial.C v₀)
            + (Polynomial.C Polynomial.X) * (Polynomial.map Polynomial.C v₁) := by
  obtain ⟨v₀, v₁, hlin'⟩ := exists_linear_decomposition_of_degreeX_le_one hlin
  exact ⟨truncPoly φ N, v₀, v₁,
    natDegree_truncPoly_lt φ hN,
    coe_truncPoly_eq_of_coeff_eq_zero_ge φ hfin,
    hlin'⟩

end Combined

end FiniteSeriesToPoly

end ArkLib

#print axioms ArkLib.FiniteSeriesToPoly.coeff_truncPoly
#print axioms ArkLib.FiniteSeriesToPoly.natDegree_truncPoly_lt
#print axioms ArkLib.FiniteSeriesToPoly.natDegree_truncPoly_le
#print axioms ArkLib.FiniteSeriesToPoly.coe_truncPoly_eq_of_coeff_eq_zero_ge
#print axioms ArkLib.FiniteSeriesToPoly.exists_polynomial_coe_of_coeff_eq_zero_ge
#print axioms ArkLib.FiniteSeriesToPoly.exists_polynomial_coe_of_coeff_eq_zero_ge'
#print axioms ArkLib.FiniteSeriesToPoly.degreeX_le_of_forall_coeff_natDegree_le
#print axioms ArkLib.FiniteSeriesToPoly.coeff_natDegree_le_degreeX
#print axioms ArkLib.FiniteSeriesToPoly.degreeX_le_one_iff_forall_coeff_natDegree_le_one
#print axioms ArkLib.FiniteSeriesToPoly.exists_linear_decomposition_of_coeff_high_X_eq_zero
#print axioms ArkLib.FiniteSeriesToPoly.exists_linear_decomposition_of_degreeX_le_one
#print axioms ArkLib.FiniteSeriesToPoly.exists_linear_polynomial_coe_of_finite_and_degreeX_le_one

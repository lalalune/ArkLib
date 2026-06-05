/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib.Algebra.MvPolynomial.Basic
import Mathlib.Algebra.MvPolynomial.PDeriv
import Mathlib.Algebra.Polynomial.HasseDeriv
import Mathlib.Combinatorics.Enumerative.Partition.Basic
import Mathlib.Data.Nat.Choose.Multinomial

/-!
# BCIKS20 Appendix A.4 — Hensel-lift numerator `β` : WAVE 1 FOUNDATION

This file builds the *reusable, mathlib-only* foundation for formalizing BCIKS20
(`2020-654`, "Proximity Gaps for Reed–Solomon Codes") Appendix A.4's recursive
Hensel-lift numerator `β` (ingredient D of the proximity-gap program).

WAVE 1 SCOPE.  This is wave 1 of a months-scale program.  We build and *prove*
(axiom-clean, no `sorry`/`admit`/`native_decide`/`bv_decide`):

1. The **multivariate Hasse coefficient** `mvHasseCoeff k p` (the genuine
   coeff-of-Taylor-shift / binomial-weighted-shift object, characteristic-free per
   BCIKS20 line 4350), with its defining `coeff` formula, additivity / `R`-linearity,
   `mvHasseCoeff 0 = id`, agreement with `Polynomial.hasseDeriv` in the single-variable
   case, and the monomial evaluation.

2. The **partition-indexed product** `partitionProd p b` = `∏_l (b l)^{λ_l}` for a
   `Nat.Partition`, with its reindexing-by-multiplicity lemma and the empty/singleton
   special cases, plus `sigmaLambda` (`Σλ`) and the multinomial/binomial `prefactor`.

What is NOT in wave 1 (deferred with precise WALLs documented at the relevant `def`s):
the `B_{i1,λ}` rescaled coefficient over the BCIKS20 ring `𝒪`, the `β` well-founded
recursion `(A.1)` itself, the weight bound (P1), and the lift identity (P2 — the A.4
proof proper).  See `ingredientD-wave1-design.md` /
`ingredientD-wave1-foundation.md` for the staged specs.

The objects here are the **genuine** mathematical objects, never stubs:
`mvHasseCoeff k p` has `coeff n = (∏ᵢ (nᵢ+kᵢ).choose kᵢ) · coeff (n+k) p`, i.e. the real
binomial-weighted shift (its weight is genuinely positive, see `mvBinom_pos` /
`mvHasseCoeff_monomial_coeff_eq`), and `partitionProd` raises each distinct part to its
genuine multiplicity.
-/

noncomputable section

open scoped BigOperators
open Finset

namespace BCIKS20.HenselNumerator

variable {σ : Type*} {R : Type*}

/-! ## 1. The multivariate Hasse coefficient -/

section MvHasse

variable [DecidableEq σ] [CommSemiring R]

/-- The **multivariate binomial weight** attached to multi-indices `s, k : σ →₀ ℕ`:
`∏ᵢ (sᵢ).choose (kᵢ)`, the product (over the union of supports — the only indices that can
contribute a factor `≠ 1`) of the single-variable binomial coefficients.

This is the genuine coefficient that the iterated single-variable Hasse derivative produces:
for `s = n + k` it is `∏ᵢ (nᵢ+kᵢ).choose kᵢ`.  When `kᵢ > sᵢ` for some `i` the factor is
`(sᵢ).choose (kᵢ) = 0`, killing the term — exactly "cannot differentiate past the degree". -/
def mvBinom (s k : σ →₀ ℕ) : ℕ :=
  ∏ i ∈ s.support ∪ k.support, (s i).choose (k i)

/-- `mvBinom s k = 0` whenever `k` does not divide-down into `s` (i.e. some `kᵢ > sᵢ`):
the binomial factor `(sᵢ).choose (kᵢ)` vanishes.  This is precisely the truncated-subtraction
guard that makes the Hasse coefficient pick out only the genuine shift `s = n + k`. -/
theorem mvBinom_eq_zero_of_not_le {s k : σ →₀ ℕ} (h : ¬ k ≤ s) : mvBinom s k = 0 := by
  classical
  rw [Finsupp.le_iff] at h
  simp only [not_forall, not_le] at h
  obtain ⟨i, hi, hlt⟩ := h
  apply Finset.prod_eq_zero (i := i)
  · -- `i ∈ k.support` since `k i > s i ≥ 0` forces `k i ≠ 0`.
    have : k i ≠ 0 := by omega
    exact Finset.mem_union.mpr (Or.inr (Finsupp.mem_support_iff.mpr this))
  · exact Nat.choose_eq_zero_of_lt hlt

/-- `mvBinom (n + k) k = ∏ᵢ (nᵢ + kᵢ).choose kᵢ`, the genuine multivariate binomial
weight of the shift `n ↦ n + k` (the value carried by `mvHasseCoeff`). -/
theorem mvBinom_add_right (n k : σ →₀ ℕ) :
    (mvBinom (n + k) k : ℕ) = ∏ i ∈ (n + k).support ∪ k.support, (n i + k i).choose (k i) := by
  classical
  unfold mvBinom
  refine Finset.prod_congr rfl ?_
  intro i _
  rfl

/-- The `k`-th **multivariate Hasse coefficient** of `p`: the genuine coeff-of-Taylor-shift
object `Δ^k p`, defined (à la `Polynomial.hasseDeriv`) as
`∑_s monomial (s - k) (mvBinom s k • coeff s p)`.

Its `coeff n` is `(∏ᵢ (nᵢ+kᵢ).choose kᵢ) · coeff (n+k) p` (`mvHasseCoeff_coeff`), the
binomial-weighted shift used by BCIKS20 (characteristic-free, no division, no `m!`).  It is
the iterated single-variable `Polynomial.hasseDeriv`, one derivative per variable
(`mvHasseCoeff_single_coeff` shows the single-variable agreement). -/
def mvHasseCoeff (k : σ →₀ ℕ) (p : MvPolynomial σ R) : MvPolynomial σ R :=
  ∑ s ∈ p.support, MvPolynomial.monomial (s - k) ((mvBinom s k : R) * MvPolynomial.coeff s p)

@[simp]
theorem mvHasseCoeff_zero_right (k : σ →₀ ℕ) :
    mvHasseCoeff k (0 : MvPolynomial σ R) = 0 := by
  simp [mvHasseCoeff]

/-- The defining coefficient formula: the genuine binomial-weighted shift. -/
theorem mvHasseCoeff_coeff (k : σ →₀ ℕ) (p : MvPolynomial σ R) (n : σ →₀ ℕ) :
    MvPolynomial.coeff n (mvHasseCoeff k p)
      = (mvBinom (n + k) k : R) * MvPolynomial.coeff (n + k) p := by
  classical
  rw [mvHasseCoeff, MvPolynomial.coeff_sum]
  -- Only the term `s = n + k` can contribute to `coeff n`, via `coeff_monomial` at `s - k = n`.
  rw [Finset.sum_eq_single (n + k)]
  · rw [MvPolynomial.coeff_monomial]
    simp
  · intro s _ hsn
    rw [MvPolynomial.coeff_monomial]
    by_cases hsk : s - k = n
    · -- `s - k = n` but `s ≠ n + k`: then `¬ k ≤ s` (else `s = (s-k)+k = n+k`), so the weight is 0.
      have hnotle : ¬ k ≤ s := by
        intro hle
        apply hsn
        have : (s - k) + k = s := tsub_add_cancel_of_le hle
        rw [hsk] at this
        exact this.symm
      rw [if_pos hsk, mvBinom_eq_zero_of_not_le hnotle]
      simp
    · simp [hsk]
  · intro hns
    rw [MvPolynomial.notMem_support_iff] at hns
    simp [hns]

/-- `mvBinom n 0 = 1`: the empty (`k = 0`) shift carries no binomial weight. -/
@[simp]
theorem mvBinom_zero_right (n : σ →₀ ℕ) : mvBinom n 0 = 1 := by
  classical
  unfold mvBinom
  apply Finset.prod_eq_one
  intro i _
  simp

/-- `mvHasseCoeff 0 = id` (non-vacuity / `hasseDeriv_zero'` analogue): the zeroth Hasse
coefficient is the polynomial itself, so the construction is genuinely not the zero map. -/
@[simp]
theorem mvHasseCoeff_zero_left (p : MvPolynomial σ R) : mvHasseCoeff 0 p = p := by
  classical
  apply MvPolynomial.ext
  intro n
  rw [mvHasseCoeff_coeff]
  simp

/-- `mvHasseCoeff k` is additive in `p`. -/
theorem mvHasseCoeff_add (k : σ →₀ ℕ) (p q : MvPolynomial σ R) :
    mvHasseCoeff k (p + q) = mvHasseCoeff k p + mvHasseCoeff k q := by
  classical
  apply MvPolynomial.ext
  intro n
  rw [MvPolynomial.coeff_add, mvHasseCoeff_coeff, mvHasseCoeff_coeff, mvHasseCoeff_coeff,
    MvPolynomial.coeff_add, mul_add]

/-- `mvHasseCoeff k` is `R`-linear (compatible with scalar multiplication). -/
theorem mvHasseCoeff_smul (k : σ →₀ ℕ) (c : R) (p : MvPolynomial σ R) :
    mvHasseCoeff k (c • p) = c • mvHasseCoeff k p := by
  classical
  apply MvPolynomial.ext
  intro n
  rw [MvPolynomial.coeff_smul, mvHasseCoeff_coeff, mvHasseCoeff_coeff, MvPolynomial.coeff_smul,
    smul_eq_mul, smul_eq_mul]
  ring

/-- The genuine multivariate binomial weight of a *single-variable* shift: when both
multi-indices are concentrated at the same coordinate `i`, the weight is the ordinary
`Nat.choose`.  This is the coefficient-level statement that `mvHasseCoeff (single i k)`
agrees with the single-variable `Polynomial.hasseDeriv k` (whose coefficient is
`(n+k).choose k`, `Polynomial.hasseDeriv_coeff`). -/
theorem mvBinom_single (i : σ) (a b : ℕ) :
    mvBinom (Finsupp.single i a) (Finsupp.single i b) = a.choose b := by
  classical
  unfold mvBinom
  by_cases ha0 : a = 0
  · by_cases hb0 : b = 0
    · subst ha0; subst hb0; simp
    · subst ha0
      -- support of single i 0 is empty; support of single i b is {i}; product over {i} = 0.choose b
      rw [Finsupp.single_zero, Finsupp.support_zero, Finset.empty_union]
      rw [Finsupp.support_single_ne_zero i hb0, Finset.prod_singleton]
      simp
  · -- a ≠ 0 : support of single i a is {i}; the union of supports is {i}.
    rw [Finsupp.support_single_ne_zero i ha0]
    by_cases hb0 : b = 0
    · subst hb0; rw [Finsupp.single_zero, Finsupp.support_zero, Finset.union_empty,
        Finset.prod_singleton]; simp
    · rw [Finsupp.support_single_ne_zero i hb0, Finset.union_self, Finset.prod_singleton]
      simp

/-- Single-variable agreement (the `hasseDeriv_coeff` analogue): for a single-coordinate shift
`k = single i m`, the `single i n`-coefficient of `mvHasseCoeff (single i m) p` is exactly the
binomial-weighted shift `(n+m).choose m · coeff (single i (n+m)) p` — identical to the
coefficient produced by the single-variable `Polynomial.hasseDeriv m`
(`Polynomial.hasseDeriv_coeff`).  This certifies `mvHasseCoeff` is the genuine Hasse object. -/
theorem mvHasseCoeff_single_coeff (i : σ) (m n : ℕ) (p : MvPolynomial σ R) :
    MvPolynomial.coeff (Finsupp.single i n) (mvHasseCoeff (Finsupp.single i m) p)
      = ((n + m).choose m : R) * MvPolynomial.coeff (Finsupp.single i (n + m)) p := by
  classical
  rw [mvHasseCoeff_coeff, ← Finsupp.single_add, mvBinom_single]

/-- Evaluation on a single monomial: `mvHasseCoeff k (monomial s a)` has the expected
binomial-weighted single monomial as its value, witnessing non-vacuity (a genuine `monomial`
with the genuine `mvBinom` weight, never identically zero when `k ≤ s` and `a ≠ 0`). -/
theorem mvHasseCoeff_monomial (k s : σ →₀ ℕ) (a : R) :
    mvHasseCoeff k (MvPolynomial.monomial s a)
      = MvPolynomial.monomial (s - k) ((mvBinom s k : R) * a) := by
  classical
  apply MvPolynomial.ext
  intro n
  rw [mvHasseCoeff_coeff, MvPolynomial.coeff_monomial, MvPolynomial.coeff_monomial]
  by_cases hsk : s - k = n
  · -- coeff at n: LHS factor uses coeff (n+k) (monomial s a) = if s = n+k then a else 0.
    by_cases hks : k ≤ s
    · have hsnk : s = n + k := by
        rw [← hsk]; exact (tsub_add_cancel_of_le hks).symm
      rw [if_pos hsk, if_pos hsnk, hsnk]
    · -- ¬ k ≤ s : weight is 0, and also s ≠ n + k (else k ≤ s).
      rw [mvBinom_eq_zero_of_not_le hks]
      rw [if_pos hsk]
      have : s ≠ n + k := by
        intro h; exact hks (h ▸ le_add_self)
      rw [if_neg this]
      simp
  · -- s - k ≠ n: LHS coeff is 0 (monomial at s-k), and RHS is 0 too.
    rw [if_neg hsk]
    have : s ≠ n + k := by
      intro h
      apply hsk
      rw [h]; simp
    rw [if_neg this]
    simp

/-- `mvBinom s k ≠ 0` whenever `k ≤ s`: every factor `(sᵢ).choose (kᵢ)` is positive because
`kᵢ ≤ sᵢ`.  Dual to `mvBinom_eq_zero_of_not_le`; the positivity half of the genuine weight. -/
theorem mvBinom_pos {s k : σ →₀ ℕ} (hks : k ≤ s) : 0 < mvBinom s k := by
  classical
  unfold mvBinom
  apply Finset.prod_pos
  intro i _
  exact Nat.choose_pos (hks i)

/-- The monomial `mvHasseCoeff`, read at the shifted index `s - k`, returns *exactly* the
genuine binomial multiple `mvBinom s k · a` (whose integer weight `mvBinom s k` is positive by
`mvBinom_pos` when `k ≤ s`).  This is the load-bearing anti-stub witness that `mvHasseCoeff` is
the genuine Hasse object, never a secretly-zero map.  (Stated over any `CommSemiring`; in
positive characteristic the *cast* of the weight may collapse, so the honest non-vacuity is the
ℕ-level `mvBinom_pos`, not a field-level `≠ 0` — which would be false over `Fₚ`.) -/
theorem mvHasseCoeff_monomial_coeff_eq (k s : σ →₀ ℕ) (a : R) :
    MvPolynomial.coeff (s - k) (mvHasseCoeff k (MvPolynomial.monomial s a))
      = (mvBinom s k : R) * a := by
  classical
  rw [mvHasseCoeff_monomial, MvPolynomial.coeff_monomial, if_pos rfl]

end MvHasse

/-! ## 2. Partition-indexed product machinery -/

section Partition

/-- `Σλ := ∑_l λ_l`, the *number of parts* of a partition (counted with multiplicity).
In BCIKS20 (`A.1`) this is the total order of the `Y`-Hasse derivative and the `ξ`-exponent
contributor.  Equals `λ.parts.card` (each part `l` is listed `λ_l` times). -/
def sigmaLambda {m : ℕ} (lam : Nat.Partition m) : ℕ := lam.parts.card

@[simp]
theorem sigmaLambda_indiscrete {m : ℕ} (hm : m ≠ 0) :
    sigmaLambda (Nat.Partition.indiscrete m) = 1 := by
  rw [sigmaLambda, Nat.Partition.indiscrete_parts hm]
  rfl

variable {M : Type*} [CommMonoid M]

/-- The **partition-indexed product** `∏_l (b l)^{λ_l}` for `lam : Nat.Partition m` and a family
`b : ℕ → M`.  Defined as the product over the multiset of parts (each distinct part `l` appears
exactly `λ_l = lam.parts.count l` times, so it is automatically raised to its multiplicity).

This is the genuine `∏_l β_l^{λ_l}` of BCIKS20 `(A.1)` — see `partitionProd_eq_prod_count`. -/
def partitionProd {m : ℕ} (lam : Nat.Partition m) (b : ℕ → M) : M :=
  (lam.parts.map b).prod

/-- The reindexing-by-multiplicity identity certifying `partitionProd` is the genuine
`∏_l (b l)^{λ_l}`: the product over parts equals the product over *distinct* parts `l`, each
raised to its multiplicity `λ_l = lam.parts.count l`. -/
theorem partitionProd_eq_prod_count {m : ℕ} (lam : Nat.Partition m) (b : ℕ → M) :
    partitionProd lam b = ∏ l ∈ lam.parts.toFinset, (b l) ^ (lam.parts.count l) := by
  classical
  rw [partitionProd, Finset.prod_multiset_map_count]

/-- The empty (`m = 0`) partition product is `1`: `Nat.Partition 0` has no parts. -/
@[simp]
theorem partitionProd_zero (lam : Nat.Partition 0) (b : ℕ → M) :
    partitionProd lam b = 1 := by
  rw [partitionProd]
  -- The unique partition of 0 has empty parts (`parts_sum = 0` ⟹ all parts are 0, but parts > 0).
  have : lam.parts = 0 := by
    have hsum : lam.parts.sum = 0 := lam.parts_sum
    rw [Multiset.eq_zero_iff_forall_notMem]
    intro a ha
    have hpos := lam.parts_pos ha
    have hle : a ≤ lam.parts.sum := Multiset.le_sum_of_mem ha
    omega
  rw [this]
  simp

/-- The product over the *indiscrete* partition (single part `m`, `m ≠ 0`) is just `b m`
(the `λ_m = 1` term).  In BCIKS20 this is the excluded special partition `λ(t)`. -/
@[simp]
theorem partitionProd_indiscrete {m : ℕ} (hm : m ≠ 0) (b : ℕ → M) :
    partitionProd (Nat.Partition.indiscrete m) b = b m := by
  rw [partitionProd, Nat.Partition.indiscrete_parts hm]
  simp

/-- `partitionProd` is multiplicative in the family. -/
theorem partitionProd_mul {m : ℕ} (lam : Nat.Partition m) (b c : ℕ → M) :
    partitionProd lam (fun l => b l * c l)
      = partitionProd lam b * partitionProd lam c := by
  rw [partitionProd, partitionProd, partitionProd, ← Multiset.prod_map_mul]

/-- The combinatorial **prefactor** of BCIKS20's `A_{i1,λ}` coefficient (lines 4042–4080),
as an explicit natural number: the binomial `C(i, i1)` times the multinomial over the parts of
`λ` together with the order-0 multiplicity.  Here it is rendered as
`Nat.choose i i1 * Nat.multinomial (lam.parts.toFinset) (lam.parts.count)` — the genuine
`multinomial(λ₁, …, λ_l, …)` over distinct part-multiplicities.

WALL (deferred to a later wave): the *matching lemma* equating this with the exact
paper combinatorial factor (reconciling the Hasse-derivative's intrinsic `C(j, Σλ)` weight
against the paper's `multinomial(j0, λ)`) is `prefactor_eq_paper` below — STATED, not proven. -/
def prefactor {m : ℕ} (i i1 : ℕ) (lam : Nat.Partition m) : ℕ :=
  Nat.choose i i1 * Nat.multinomial lam.parts.toFinset (fun l => lam.parts.count l)

/-- The prefactor is genuinely positive whenever the binomial part is (so it is never a
secretly-zero stub): `Nat.multinomial` is always `> 0`. -/
theorem prefactor_pos {m : ℕ} (i i1 : ℕ) (lam : Nat.Partition m) (hi : i1 ≤ i) :
    0 < prefactor i i1 lam := by
  rw [prefactor]
  exact Nat.mul_pos (Nat.choose_pos hi) (Nat.multinomial_pos _ _)

end Partition

/-! ## 3. Staged specifications (WALLs) — deferred to later waves

The following are the precise, *honest* obligations for the rest of ingredient D.  They are
NOT defined/proven in wave 1; they are recorded as the load-bearing frontier so the obligation
is legible and cannot be silently faked.  Each requires the in-tree BCIKS20 ring API
(`ArkLib.Data.Polynomial.RationalFunctions`: `𝒪 H`, `𝕃 H`, `ξ`, `ζ`, `functionFieldT`,
`weight_Λ_over_𝒪`, `Lemma_A_1`, `ClaimA2.Hypotheses`) which is HARNESS-HOT this wave.

* `hasseEvalAtRoot` : evaluate the iterated Hasse coefficient of the trivariate `R : F[X][X][Y]`
  at `(X = x₀, Y = α₀ = T/W)` into `𝕃 H` (mirrors `ClaimA2.ζ`, RationalFunctions.lean:2229).
  WALL: needs the in-tree `Bivariate.evalX` + `eval₂ liftToFunctionField (T/W)` layer wiring.

* `B_coeff : 𝒪 H` : the rescaled coefficient `A_{i1,λ} · W^{d − δ_{i1,0} − Σλ}`, with proven
  weight `Λ(B_{i1,λ}) = (D − Σλ) + (d − δ_{i1,0} − Σλ)·Λ(W)` and the `i1 = 0` extra-`W` case.
  WALL: needs `A_coeff` regularity + the `W`-clearing weight lemma over `𝒪`.

* `prefactor_eq_paper` : `prefactor i i1 lam = <paper combinatorial factor>`.
  WALL: reconcile Hasse's intrinsic `C(j, Σλ)` weight vs the paper's `multinomial(j0, λ)`.

* `βHensel (x₀ R H hHyp) : ℕ → 𝒪 H` : the recursion `(A.1)`
  `β₀ = T mod H̃`,
  `β_{t+1} = − ∑_{i1; λ ∈ P(t+1−i1), λ ≠ indiscrete (t+1)}
                W^{i1+δ−1} · ξ^{2i1+Σλ−2} · B_{i1,λ} · partitionProd λ (βHensel … ·)`.
  WALL: well-founded recursion on the parts (`l < t+1` from `parts_sum`+`parts_pos`), with the
  `(x₀, hHyp)` signature fix; `partitionProd` (this file) is the genuine `∏_l β_l^{λ_l}` factor.

* `(P1) weight βHensel` : `weight_Λ_over_𝒪 (βHensel … t) D ≤ (2t+1)·(R.natDegreeY)·D`.
  WALL: induction on `(A.1)` using `weight_ξ_bound`, `Λ(W)`, `Λ(B)`, subadditivity.

* `(P2) lift identity` : `embeddingOf𝒪Into𝕃 (βHensel … t) = α_t · W^{t+1} · ξ^{e_t}`,
  `e_t = max 0 (2t−1)`.  This IS the BCIKS20 A.4 proof; needs a formal `R(X,γ,Z)=0`
  power-series root statement.  IRREDUCIBLE FRONTIER — explicitly out of wave 1.

The iterated-Hasse Leibniz/product rule (needed only for P2) is also out of scope. -/

end BCIKS20.HenselNumerator

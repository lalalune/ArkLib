/-
Copyright (c) 2025 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Poulami Das, Miguel Quaresma (Least Authority), Alexander Hicks
-/

import ArkLib.Data.CodingTheory.ReedSolomon
import ArkLib.Data.MvPolynomial.LinearMvExtension
import ArkLib.ProofSystem.Whir.BlockRelDistance
import ArkLib.ProofSystem.Whir.MutualCorrAgreement

/-!
# Folding

This file formalizes the notion of folding univariate functions and
lemmas showing that folding preserves list decocidng,
introduced in Section 4 of [ACFY24].

## References

* [Arnon, G., Chiesa, A., Fenzi, G., and Yogev, E., *WHIR: Reed–Solomon Proximity Testing
    with Super-Fast Verification*][ACFY24]

## Implementation notes (corrections from paper)

- Theorem 4.20:
-- proximity generators should be defined for `C^(0),...,C^(k)` in place of `C^(1),...,C^(k)`
-- `\delta \in (0, 1 - max_{i \in [0,k]} {....})` in place of
   `\delta \in (0, 1 - max_{i \in [k]} {....})`
- Theorem 4.20 holds for `l = 2` as can be seen with `BStar(..,2)` and `errStar(..,2,..)`
  and so `Gen(l,alpha) = {1, alpha,...., alpha^{l-1}}` also corresponds to `l = 2`
  and not for a generic l.

- Lemmas 4.21,4.22,4.23
-- these lemmas refer to the specific case when k set to 1, so it's safe to use the hypothesis 1 ≤ m

## Tags
Open question: should we aim to add tags?
-/

namespace Fold

open BlockRelDistance Vector Finset

variable {F : Type} [Field F] {ι : Type} [Pow ι ℕ]

/-- `∃ x ∈ S`, such that `y = x ^ 2^(k+1)`. `extract_x` returns `z = x ^ 2^k` such that `y = z^2`.
-/
noncomputable def extract_x
  (S : Finset ι) (φ : ι ↪ F) (k : ℕ) (y : indexPowT S φ (k + 1)) : indexPowT S φ k :=
  let x := Classical.choose y.property
  let hx := Classical.choose_spec y.property
  let z := (φ x) ^ (2^k)
  ⟨z, ⟨x, hx.1, rfl⟩⟩

/-- Given a function `f : (ι^(2ᵏ)) → F`, foldf operates on two inputs:
  element `y ∈ LpowT S (k+1)`, hence `∃ x ∈ S, s.t. y = x ^ 2^(k+1)` and `α ∈ F`.
  It obtains the square root of y as `xPow := extract_x S φ k y`,
    here xPow is of the form `x ^ 2^k`.
  It returns the value `f(xPow) + f(- xPow)/2 + α * (f(xPow) - f(- xPow))/ 2 * xPow`. -/
noncomputable def foldf (S : Finset ι) (φ : ι ↪ F)
  {k : ℕ} [Neg (indexPowT S φ k)] (y : indexPowT S φ (k + 1))
  (f : indexPowT S φ k → F) (α : F) : F :=
  let xPow := extract_x S φ k y
  let fx := f xPow
  let f_negx := f (-xPow)
  (fx + f_negx) / 2 + α * ((fx - f_negx) / (2 * (xPow.val : F)))

/-- The function `fold_k_core` runs a recursion,
    for a function `f : ι → F` and a vector `αs` of size i
  For `i = 0`, `fold_k_core` returns `f` evaluated at `x ∈ S`
  For `i = (k+1) ≠ 0`,
    αs is parsed as α || αs', where αs' is of size k
    function `fk : (ι^2ᵏ) → F` is obtained by making a recursive call to
      `fold_k_core` on input `αs'`
    we obtain the final function `(ι^(2^(k+1))) → F` by invoking `foldf` with `fk` and `α`. -/
noncomputable def fold_k_core {S : Finset ι} {φ : ι ↪ F} (f : (indexPowT S φ 0) → F)
  [∀ i : ℕ, Neg (indexPowT S φ i)] : (i : ℕ) → (αs : Fin i → F) →
    indexPowT S φ i → F
| 0, _ => fun x₀ => f x₀
| k+1, αs => fun y =>
    let α := αs 0
    let αs' : Fin k → F := fun i => αs (Fin.succ i)
    let fk := fold_k_core f k αs'
    foldf S φ y fk α

/-- Definition 4.14, part 1
  fold_k takes a function `f : ι → F` and a vector `αs` of size k
  and returns a function `Fold : (ι^2ᵏ) → F` -/
noncomputable def fold_k
  {S : Finset ι} {φ : ι ↪ F} {k m : ℕ}
  [∀ j : ℕ, Neg (indexPowT S φ j)]
  (f : (indexPowT S φ 0) → F) (αs : Fin k → F) (_hk : k ≤ m): indexPowT S φ k → F :=
  fold_k_core f k αs

/-- Definition 4.14, part 2
  fold_k takes a set of functions `set : Set (ι → F)` and a vector `αs` of size k
  and returns a set of functions `Foldset : Set ((ι^2ᵏ) → F)` -/
noncomputable def fold_k_set
  {S : Finset ι} {φ : ι ↪ F} {k m : ℕ}
  [∀ j : ℕ, Neg (indexPowT S φ j)]
  (set : Set ((indexPowT S φ 0) → F)) (αs : Fin k → F) (hk : k ≤ m): Set (indexPowT S φ k → F) :=
    { g | ∃ f ∈ set, g = fold_k f αs hk}

/-! ### Helper lemmas for the folding degree-halving argument (Claim 4.15 part 1)

These lemmas establish the standard fact that a single fold replaces a degree-`< 2N`
univariate polynomial by a degree-`< N` one via the even/odd decomposition
`p(z) = pₑ(z²) + z · pₒ(z²)`, where the random fold is `pₑ + α·pₒ`. Iterating `k` times
takes a degree-`< 2^m` polynomial to a degree-`< 2^(m-k)` polynomial. -/
namespace FoldingHelpers

open Polynomial BlockRelDistance ReedSolomon

variable {F : Type*} [Field F]

/-- Even part of a univariate polynomial: `pₑ = ∑_j coeff(p, 2j) Xʲ`. -/
noncomputable def evenPart (p : F[X]) : F[X] :=
  ∑ j ∈ Finset.range (p.natDegree + 1), Polynomial.monomial j (p.coeff (2 * j))

/-- Odd part of a univariate polynomial: `pₒ = ∑_j coeff(p, 2j+1) Xʲ`. -/
noncomputable def oddPart (p : F[X]) : F[X] :=
  ∑ j ∈ Finset.range (p.natDegree + 1), Polynomial.monomial j (p.coeff (2 * j + 1))

lemma evenPart_coeff (p : F[X]) (n : ℕ) :
    (evenPart p).coeff n = if n ≤ p.natDegree then p.coeff (2 * n) else 0 := by
  unfold evenPart
  rw [Polynomial.finset_sum_coeff]
  simp only [Polynomial.coeff_monomial]
  rw [Finset.sum_ite_eq' (Finset.range (p.natDegree+1)) n (fun j => p.coeff (2*j))]
  simp only [Finset.mem_range]
  by_cases h : n ≤ p.natDegree
  · rw [if_pos (Nat.lt_succ_iff.mpr h), if_pos h]
  · rw [if_neg (by omega), if_neg h]

lemma oddPart_coeff (p : F[X]) (n : ℕ) :
    (oddPart p).coeff n = if n ≤ p.natDegree then p.coeff (2 * n + 1) else 0 := by
  unfold oddPart
  rw [Polynomial.finset_sum_coeff]
  simp only [Polynomial.coeff_monomial]
  rw [Finset.sum_ite_eq' (Finset.range (p.natDegree+1)) n (fun j => p.coeff (2*j+1))]
  simp only [Finset.mem_range]
  by_cases h : n ≤ p.natDegree
  · rw [if_pos (Nat.lt_succ_iff.mpr h), if_pos h]
  · rw [if_neg (by omega), if_neg h]

/-- Polynomial identity: `p = pₑ(X²) + X · pₒ(X²)`. -/
lemma poly_eq_even_odd (p : F[X]) :
    p = (evenPart p).comp (X ^ 2) + X * (oddPart p).comp (X ^ 2) := by
  ext n
  rw [coeff_add, ← expand_eq_comp_X_pow, ← expand_eq_comp_X_pow]
  rcases Nat.even_or_odd n with ⟨k, hk⟩ | ⟨k, hk⟩
  · subst hk
    rw [coeff_expand (by norm_num) (evenPart p) (k+k)]
    have h2k : (2 : ℕ) ∣ (k + k) := ⟨k, by ring⟩
    simp only [h2k, if_true]
    have hdiv : (k + k) / 2 = k := by omega
    rw [hdiv, evenPart_coeff]
    have hsecond : (X * (expand F 2 (oddPart p))).coeff (k + k) = 0 := by
      by_cases hk0 : k = 0
      · subst hk0; simp [coeff_X_mul_zero (expand F 2 (oddPart p))]
      · have : k + k = (k + k - 1) + 1 := by omega
        rw [this, coeff_X_mul]
        rw [coeff_expand (by norm_num) (oddPart p) (k + k - 1)]
        have hodd : ¬ (2 : ℕ) ∣ (k + k - 1) := by omega
        simp only [hodd, if_false]
    rw [hsecond, _root_.add_zero]
    by_cases hkdeg : k ≤ p.natDegree
    · simp only [hkdeg, if_true, two_mul]
    · simp only [hkdeg, if_false]
      have hcz : p.coeff (k + k) = 0 := by
        apply Polynomial.coeff_eq_zero_of_natDegree_lt; omega
      rw [hcz]
  · subst hk
    rw [coeff_expand (by norm_num) (evenPart p) (2 * k + 1)]
    have hno : ¬ (2 : ℕ) ∣ (2 * k + 1) := by omega
    simp only [hno, if_false, _root_.zero_add]
    rw [coeff_X_mul (expand F 2 (oddPart p)) (2 * k)]
    rw [coeff_expand (by norm_num) (oddPart p) (2 * k)]
    have hdvd : (2 : ℕ) ∣ (2 * k) := ⟨k, by ring⟩
    simp only [hdvd, if_true]
    have hdiv2 : (2 * k) / 2 = k := by omega
    rw [hdiv2, oddPart_coeff]
    by_cases hkdeg : k ≤ p.natDegree
    · simp only [hkdeg, if_true]
    · simp only [hkdeg, if_false]
      have hcz : p.coeff (2 * k + 1) = 0 := by
        apply Polynomial.coeff_eq_zero_of_natDegree_lt; omega
      rw [hcz]

/-- Key decomposition for evaluation: `p(v) = pₑ(v²) + v·pₒ(v²)`. -/
lemma eval_eq_even_odd (p : F[X]) (v : F) :
    p.eval v = (evenPart p).eval (v ^ 2) + v * (oddPart p).eval (v ^ 2) := by
  conv_lhs => rw [poly_eq_even_odd p]
  simp [Polynomial.eval_comp]

/-- The fold polynomial: `foldPoly p α = pₑ + α·pₒ`. -/
noncomputable def foldPoly (p : F[X]) (α : F) : F[X] := evenPart p + α • oddPart p

/-- The fold-evaluation identity: for `v ≠ 0` and `2 ≠ 0`,
    `(p(v)+p(-v))/2 + α·((p(v)-p(-v))/(2v)) = (foldPoly p α)(v²)`. -/
lemma foldf_eq_foldPoly_eval (p : F[X]) (α v : F) (hv : v ≠ 0) (h2 : (2 : F) ≠ 0) :
    (p.eval v + p.eval (-v)) / 2 + α * ((p.eval v - p.eval (-v)) / (2 * v))
      = (foldPoly p α).eval (v ^ 2) := by
  have hev : p.eval v = (evenPart p).eval (v^2) + v * (oddPart p).eval (v^2) :=
    eval_eq_even_odd p v
  have hodv : p.eval (-v) = (evenPart p).eval (v^2) + (-v) * (oddPart p).eval (v^2) := by
    have := eval_eq_even_odd p (-v)
    rwa [neg_pow, show ((-1 : F)) ^ 2 = 1 by ring, one_mul] at this
  rw [hev, hodv]
  unfold foldPoly
  rw [Polynomial.eval_add, Polynomial.eval_smul, smul_eq_mul]
  field_simp
  ring

lemma evenPart_degree_lt (p : F[X]) (N : ℕ) (h : p.degree < (2 * N : ℕ)) :
    (evenPart p).degree < (N : ℕ) := by
  rw [Polynomial.degree_lt_iff_coeff_zero]
  intro n hn
  rw [evenPart_coeff]
  have hNn : (N : ℕ) ≤ n := by exact_mod_cast hn
  by_cases hkdeg : n ≤ p.natDegree
  · simp only [hkdeg, if_true]
    apply Polynomial.coeff_eq_zero_of_degree_lt
    refine lt_of_lt_of_le h ?_
    exact_mod_cast Nat.mul_le_mul_left 2 hNn
  · simp only [hkdeg, if_false]

lemma oddPart_degree_lt (p : F[X]) (N : ℕ) (h : p.degree < (2 * N : ℕ)) :
    (oddPart p).degree < (N : ℕ) := by
  rw [Polynomial.degree_lt_iff_coeff_zero]
  intro n hn
  rw [oddPart_coeff]
  have hNn : (N : ℕ) ≤ n := by exact_mod_cast hn
  by_cases hkdeg : n ≤ p.natDegree
  · simp only [hkdeg, if_true]
    apply Polynomial.coeff_eq_zero_of_degree_lt
    refine lt_of_lt_of_le h ?_
    have hle : 2 * N ≤ 2 * n + 1 := by omega
    exact_mod_cast hle
  · simp only [hkdeg, if_false]

/-- Degree halving: if `deg p < 2N` then `deg (foldPoly p α) < N`. -/
lemma foldPoly_degree_lt (p : F[X]) (α : F) (N : ℕ) (h : p.degree < (2 * N : ℕ)) :
    (foldPoly p α).degree < (N : ℕ) := by
  unfold foldPoly
  refine lt_of_le_of_lt (Polynomial.degree_add_le _ _) ?_
  rw [max_lt_iff]
  refine ⟨evenPart_degree_lt p N h, ?_⟩
  refine lt_of_le_of_lt (Polynomial.degree_smul_le α (oddPart p)) ?_
  exact oddPart_degree_lt p N h

/-- `extract_x` produces a square root of `y.val`. -/
lemma extract_x_sq {ι : Type} [Pow ι ℕ] {F : Type} [Field F]
    (S : Finset ι) (φ : ι ↪ F) (k : ℕ) (y : indexPowT S φ (k + 1)) :
    ((extract_x S φ k y).val) ^ 2 = y.val := by
  have hx := Classical.choose_spec y.property
  have hval : (extract_x S φ k y).val = (φ (Classical.choose y.property)) ^ (2^k) := rfl
  rw [hval, ← pow_mul, ← pow_succ]
  exact hx.2.symm

/-- A function `f : indexPowT S φ k → F` is the `.val`-evaluation of polynomial `p`. -/
def IsEvalOf {ι : Type} [Pow ι ℕ] {F : Type} [Field F]
    {S : Finset ι} {φ : ι ↪ F} {k : ℕ}
    (f : indexPowT S φ k → F) (p : F[X]) : Prop :=
  ∀ z : indexPowT S φ k, f z = p.eval z.val

/-- **Single fold step.** If `fk` is the `.val`-evaluation of `p`, the domain values are
    nonzero, negation is compatible with `.val`, and `2 ≠ 0`, then folding `fk` by `α`
    produces the `.val`-evaluation of `foldPoly p α`. -/
lemma foldf_isEvalOf {ι : Type} [Pow ι ℕ] {F : Type} [Field F]
    {S : Finset ι} {φ : ι ↪ F} {k : ℕ} [Neg (indexPowT S φ k)]
    (p : F[X]) (α : F) (fk : indexPowT S φ k → F)
    (hfk : IsEvalOf fk p)
    (hneg : ∀ z : indexPowT S φ k, (-z).val = -(z.val))
    (hnz : ∀ z : indexPowT S φ k, z.val ≠ 0)
    (h2 : (2 : F) ≠ 0) :
    IsEvalOf (fun y => foldf S φ y fk α) (foldPoly p α) := by
  intro y
  change foldf S φ y fk α = (foldPoly p α).eval y.val
  simp only [foldf]
  set xPow := extract_x S φ k y with hxPow
  have hfx : fk xPow = p.eval xPow.val := hfk xPow
  have hfnx : fk (-xPow) = p.eval (-(xPow.val)) := by
    rw [hfk (-xPow), hneg xPow]
  rw [hfx, hfnx]
  have hv : xPow.val ≠ 0 := hnz xPow
  rw [foldf_eq_foldPoly_eval p α xPow.val hv h2]
  congr 1
  exact extract_x_sq S φ k y

/-- **Iterated fold tracks a polynomial with halving degree.** For each `i ≤ m`, there is a
    polynomial of degree `< 2^(m-i)` whose `.val`-evaluation equals `fold_k_core f i αs`,
    provided the base function is the `.val`-evaluation of a degree-`< 2^m` polynomial and the
    per-level pinning facts hold. -/
lemma fold_k_core_isEvalOf {ι : Type} [Pow ι ℕ] {F : Type} [Field F]
    {S : Finset ι} {φ : ι ↪ F} [∀ i : ℕ, Neg (indexPowT S φ i)]
    (f : indexPowT S φ 0 → F) (p₀ : F[X]) (m : ℕ)
    (hp₀deg : p₀.degree < (2 ^ m : ℕ))
    (hf : IsEvalOf f p₀)
    (hneg : ∀ (i : ℕ) (z : indexPowT S φ i), (-z).val = -(z.val))
    (hnz : ∀ (i : ℕ) (z : indexPowT S φ i), z.val ≠ 0)
    (h2 : (2 : F) ≠ 0) :
    ∀ (i : ℕ), i ≤ m → ∀ (αs : Fin i → F),
      ∃ q : F[X], q.degree < (2 ^ (m - i) : ℕ) ∧ IsEvalOf (fold_k_core f i αs) q := by
  intro i
  induction i with
  | zero =>
    intro _ αs
    refine ⟨p₀, by simpa using hp₀deg, ?_⟩
    intro z
    exact hf z
  | succ k ih =>
    intro hk αs
    have hk' : k ≤ m := Nat.le_of_succ_le hk
    obtain ⟨q, hqdeg, hqeval⟩ := ih hk' (fun i => αs (Fin.succ i))
    refine ⟨foldPoly q (αs 0), ?_, ?_⟩
    · have hmk : m - k = (m - (k+1)) + 1 := by omega
      have hq' : q.degree < (2 * 2 ^ (m - (k+1)) : ℕ) := by
        rw [hmk] at hqdeg
        rw [pow_succ] at hqdeg
        have heq : (2 ^ (m - (k+1)) * 2 : ℕ) = (2 * 2 ^ (m - (k+1)) : ℕ) := by ring
        rwa [heq] at hqdeg
      exact foldPoly_degree_lt q (αs 0) (2 ^ (m - (k+1))) hq'
    · have hstep := foldf_isEvalOf (S := S) (φ := φ) (k := k) q (αs 0)
        (fold_k_core f k (fun i => αs (Fin.succ i))) hqeval (hneg k) (hnz k) h2
      intro y
      show fold_k_core f (k+1) αs y = (foldPoly q (αs 0)).eval y.val
      exact hstep y

/-- From smooth-code membership and `.val`-pinning, extract the evaluating polynomial. -/
lemma isEvalOf_of_mem_smoothCode {ι : Type} [Pow ι ℕ] {F : Type} [Field F] [DecidableEq F]
    {S : Finset ι} {φ : ι ↪ F} {k m : ℕ}
    {φ_k : (indexPowT S φ k) ↪ F} [Fintype (indexPowT S φ k)] [Smooth φ_k]
    (hφk : ∀ z : indexPowT S φ k, φ_k z = z.val)
    (f : indexPowT S φ k → F) (hf : f ∈ smoothCode φ_k m) :
    ∃ p : F[X], p.degree < (2 ^ m : ℕ) ∧ IsEvalOf f p := by
  rw [smoothCode, ReedSolomon.mem_code_iff_exists_polynomial] at hf
  obtain ⟨p, hpdeg, hpeq⟩ := hf
  refine ⟨p, hpdeg, ?_⟩
  intro z
  rw [hpeq]
  change p.eval (φ_k z) = p.eval z.val
  rw [hφk z]

/-- From `.val`-evaluation by a low-degree polynomial and `.val`-pinning,
    conclude smooth-code membership. -/
lemma mem_smoothCode_of_isEvalOf {ι : Type} [Pow ι ℕ] {F : Type} [Field F] [DecidableEq F]
    {S : Finset ι} {φ : ι ↪ F} {k m : ℕ}
    {φ_k : (indexPowT S φ k) ↪ F} [Fintype (indexPowT S φ k)] [Smooth φ_k]
    (hφk : ∀ z : indexPowT S φ k, φ_k z = z.val)
    (g : indexPowT S φ k → F) (p : F[X]) (hpdeg : p.degree < (2 ^ m : ℕ))
    (hg : IsEvalOf g p) :
    g ∈ smoothCode φ_k m := by
  rw [smoothCode]
  apply ReedSolomon.mem_code_of_polynomial_of_degree_lt_of_eval p hpdeg
  intro z
  rw [hg z, hφk z]

end FoldingHelpers

section FoldingLemmas

open MutualCorrAgreement Generator LinearMvExtension ListDecodable
     NNReal ReedSolomon ProbabilityTheory

variable {F : Type} [Field F] [DecidableEq F]
         {ι : Type} [Pow ι ℕ]

/-- Claim 4.15 part 1
  Let `f : ι → F`, `α ∈ Fᵏ` is the folding randomness, and let `g : (ι^(2ᵏ) → F) = fold_k(f,α)`
  for k ≤ m, `f ∈ RS[F,ι,m]` then we have `g ∈ RS[F,ι^(2ᵏ),(m-k)]`.

  **Pinning hypotheses (corrections from paper).** The per-round embeddings `φ_0, φ_k` act as the
  underlying field value (`φ_i x = x.val`); negation on `(ι^(2ⁱ))` is the field negation
  (`(-x).val = -(x.val)`); the domain values are nonzero (smooth domains are cosets of a subgroup
  of `Fˣ`, hence avoid `0`); and `2 ≠ 0` (smooth ReedSolomon codes in WHIR live over large prime
  fields). These facts are implicitly assumed by the even/odd folding argument in [ACFY24] and are
  required for the fold `(f(x)+f(-x))/2 + α·(f(x)-f(-x))/(2x)` to be the genuine even/odd fold. -/
lemma fold_f_g
  {S : Finset ι} {φ : ι ↪ F} {k m : ℕ}
  {φ_0 : (indexPowT S φ 0) ↪ F} {φ_k : (indexPowT S φ k) ↪ F}
  [Fintype (indexPowT S φ 0)] [Smooth φ_0]
  [Fintype (indexPowT S φ k)] [Smooth φ_k]
  [∀ i : ℕ, Neg (indexPowT S φ i)]
  (hφ0 : ∀ z : indexPowT S φ 0, φ_0 z = z.val)
  (hφk : ∀ z : indexPowT S φ k, φ_k z = z.val)
  (hneg : ∀ (i : ℕ) (z : indexPowT S φ i), (-z).val = -(z.val))
  (hnz : ∀ (i : ℕ) (z : indexPowT S φ i), z.val ≠ 0)
  (h2 : (2 : F) ≠ 0)
  (αs : Fin k → F) (hk : k ≤ m)
  (f : smoothCode φ_0 m) :
  let f_fun := (f : (indexPowT S φ 0) → F)
  let g := fold_k f_fun αs hk
  g ∈ smoothCode φ_k (m - k) := by
  intro f_fun g
  obtain ⟨p₀, hp₀deg, hp₀eval⟩ :=
    FoldingHelpers.isEvalOf_of_mem_smoothCode hφ0 f_fun f.property
  obtain ⟨q, hqdeg, hqeval⟩ :=
    FoldingHelpers.fold_k_core_isEvalOf f_fun p₀ m hp₀deg hp₀eval hneg hnz h2 k hk αs
  exact FoldingHelpers.mem_smoothCode_of_isEvalOf hφk g q hqdeg hqeval

/-- Claim 4.15 part 2
  If fPoly be the multilinear extension of f, then we have
  (m-k)-variate multilinear extension of g as `gPoly = fPoly(α₀,α₁,...α_{k-1},X_k,..,X_{m-1})`.

  **Signature correction (from paper).** The original statement quantified over an *arbitrary*
  codeword `g : smoothCode φ_k (m-k)` with no link to `f`, which makes the conclusion false (the
  RHS is determined by `f`, the LHS by an unrelated `g`). The paper-faithful statement, matching
  Claim 4.15, requires `g` to be the actual fold of `f`, i.e. `g = fold_k f αs`. The hypothesis
  `hg` below pins this, using exactly the `fold_k` of `fold_f_g` (Claim 4.15 part 1). -/
lemma fold_f_g_poly
  {S : Finset ι} {φ : ι ↪ F} {k m : ℕ}
  {φ_0 : (indexPowT S φ 0) ↪ F} {φ_k : (indexPowT S φ k) ↪ F}
  [Fintype (indexPowT S φ 0)] [DecidableEq (indexPowT S φ 0)] [Smooth φ_0]
  [Fintype (indexPowT S φ k)] [DecidableEq (indexPowT S φ k)] [Smooth φ_k]
  [∀ i : ℕ, Neg (indexPowT S φ i)]
  (αs : Fin k → F) (hk : k ≤ m)
  (f : smoothCode φ_0 m) (g : smoothCode φ_k (m-k))
  (hg : (g : indexPowT S φ k → F) = fold_k (f : indexPowT S φ 0 → F) αs hk) :
  let fPoly := mVdecode f
  let gPoly := mVdecode g
  gPoly = partialEval fPoly αs hk :=
sorry

/--
The `GenMutualCorrParams` class captures the necessary parameters and assumptions
to model a sequence of proximity generators for a set of smooth ReedSolomon codes.
It contains the following:

for `i ∈ [0,k]` :
- `inst1`, `inst2`, `inst3`: typeclass instances required to operate on `ι^(2ⁱ)`
    (finiteness, nonemptiness, and decidable equality).
- `φ_i`: per-round embeddings from `ι^(2ⁱ)` into `F`.
- `inst4`: smoothness assumption for each `φ_i`.
- `Gen_α i`: the proximity generators wrt the generator function
  `Gen(parℓ,α) : {1,α,α²,..,α^{parℓ-1}}` defined as per `hgen` for code `Cᵢ`
- `inst5`, `inst6` : typeclass instances denoting finiteness of `parℓ`
    underlying `Gen_αᵢ` and `parℓ_type`
- `BStar`, `errStar`: parameters denoting proximity and error thresholds per round.
- `h`: main agreement assumption, stating that each `Gen_α` satisfies mutual correlated agreement
    for its underlying code.
- `hcard, hcard'` : `|Gen_αᵢ.parℓ| = 2` and `|parℓ_type| = 2`
-/
class GenMutualCorrParams [Fintype F] (S : Finset ι) (φ : ι ↪ F) (k : ℕ) where
  m : ℕ

  inst1 : ∀ i : Fin (k + 1), Fintype (indexPowT S φ i)
  inst2 : ∀ i : Fin (k + 1), Nonempty (indexPowT S φ i)
  inst3 : ∀ i : Fin (k + 1), DecidableEq (indexPowT S φ i)

  φ_i : ∀ i : Fin (k + 1), (indexPowT S φ i) ↪ F
  inst4 : ∀ i : Fin (k + 1), Smooth (φ_i i)

  parℓ_type : ∀ _ : Fin (k + 1), Type
  inst5 : ∀ i : Fin (k + 1), Fintype (parℓ_type i)

  exp : ∀ i : Fin (k + 1), (parℓ_type i) ↪ ℕ

  Gen_α : ∀ i : Fin (k + 1), ProximityGenerator (indexPowT S φ i) F :=
    fun i => RSGenerator.genRSC (parℓ_type i) (φ_i i) (m - i) (exp i)
  inst6 : ∀ i : Fin (k + 1), Fintype (Gen_α i).parℓ

  BStar : ∀ i : Fin (k + 1), (Set (indexPowT S φ i → F)) → Type → ℝ≥0
  errStar : ∀ i : Fin (k + 1), (Set (indexPowT S φ i → F)) → Type → ℝ → ENNReal

  h : ∀ i : Fin (k + 1), hasMutualCorrAgreement (Gen_α i)
                                             (BStar i (Gen_α i).C (Gen_α i).parℓ)
                                             (errStar i (Gen_α i).C (Gen_α i).parℓ)

  hcard : ∀ i : Fin (k + 1), Fintype.card ((Gen_α i).parℓ) = 2
  hcard' : ∀ i : Fin (k + 1), Fintype.card (parℓ_type i) = 2

/-- Theorem 4.20
  Let C = RS[F,ι,m] be a smooth ReedSolomon code
  For k ≤ m and 0 ≤ i ≤ k,
  let Cⁱ = RS[F,ι^(2ⁱ),m-i] and let `Gen(2,α)` be a proxmity generator with
  mutual correlated agreement for `C⁰,...,C^{k}` with proximity bounds BStar and errStar
  Then for every `f : ι → F` and `δ ∈ (0, 1 - max {i ∈ [0,k]} BStar(Cⁱ, 2))`
    `Pr_{αs ← F^k} [ fold_k_set(Λᵣ(0,k,f,S',C,hcode,δ),αs) ≠ Λ(Cᵏ,fold_k(f,αs),δ)]`
      `< ∑ i ∈ [0,k] errStar(Cⁱ,2,δ)`,
  where fold_k_set and fold_k are as defined above,
  αs is a length-k vector of folding randomness,
  `Λᵣ(0,k,f,S',C,hcode,δ)` corresponds to the list of codewords of C δ-close to f,
  wrt (0,k)-wise block relative distance.
  `Λ(Cᵏ,fold_k(f,αs),δ)` is the list of codewords of Cᵏ δ-close to fold_k(f, αs),
  wrt the relative Hamming distance
  Below, we use an instance of the class `GenMutualCorrParams` to capture the
  conditions of proxmity generator with mutual correlated agreement for codes
  C⁰,...,C^{k}.
-/

-- NOTE: need to align this better with the inductive way this is shown via the other lemmas below.
theorem folding_listdecoding_if_genMutualCorrAgreement
  [Fintype F] {S : Finset ι} {φ : ι ↪ F} [Fintype ι] [DecidableEq ι] [Smooth φ] {k m : ℕ}
  {S' : Finset (indexPowT S φ 0)} {φ' : (indexPowT S φ 0) ↪ F}
  [∀ i : ℕ, Fintype (indexPowT S φ i)] [DecidableEq (indexPowT S φ 0)] [Smooth φ']
  [h : ∀ {f : (indexPowT S φ 0) → F}, DecidableBlockDisagreement 0 k f S' φ']
  [∀ i : ℕ, Neg (indexPowT S φ i)]
  {C : Set ((indexPowT S φ 0) → F)} (hcode : C = smoothCode φ' m) (hLe : k ≤ m)
  {δ : ℝ≥0}
  {params : GenMutualCorrParams S φ k} :

  -- necessary typeclasses of underlying domain (ιᵢ)^2ʲ regarding finiteness,
  -- non-emptiness and smoothness
    let _ : ∀ j : Fin (k + 1), Fintype (indexPowT S φ j) := params.inst1
    let _ : ∀ j : Fin (k + 1), Nonempty (indexPowT S φ j) := params.inst2

    ∀ (f : (indexPowT S φ 0) → F)
      (hδ :
        0 < δ ∧
          δ <
            1 - Finset.univ.sup (fun j => params.BStar j (params.Gen_α j).C (params.Gen_α j).parℓ)),
      Pr_{let αs ←$ᵖ (Fin k → F)}[
          let listBlock : Set ((indexPowT S φ 0) → F) := Λᵣ(0, k, f, S', C, hcode, δ)
          let fold := fold_k f αs hLe
          let foldSet := fold_k_set listBlock αs hLe
          let kFin : Fin (k + 1) := ⟨k, Nat.lt_succ_self k⟩
          let Cₖ := (params.Gen_α kFin).C
          let listHamming := closeCodewordsRel Cₖ fold δ
          foldSet ≠ listHamming
        ] <
        (∑ i : Fin (k + 1), params.errStar i (params.Gen_α i).C (params.Gen_α i).parℓ δ)
:= by sorry

/-- Lemma 4.21
  Let `C = RS[F,ι,m]` be a smooth ReedSolomon code and k ≤ m
  Denote `C' = RS[F,ι^2,m-1]`, then for every `f : ι → F` and `δ ∈ (0, 1 - BStar(C',2))`
    `Pr_{α ← F} [
      fold_k_set(Λᵣ(0,k,f,S_0,C,δ),(fun _ : Fin 1 => α)) ≠
        Λᵣ(1,k-1,fold_k(f,(fun _ : Fin 1 => α)),S_1,C',δ)
    ]`
      `< errStar(C',2,δ)`
    where `fold_k(f,(fun _ : Fin 1 => α))` returns a function `ι^2 → F`,
    `S_0` and `S_1` denote finite sets of elements of type ι and ι², and
    `Λᵣ` denotes the list of δ-close codewords wrt block relative distance.
    `Λᵣ(0,k,f,S_0,C)` denotes Λᵣ at f : ι → F for code C and
    `Λᵣ(1,k,fold_k(f,(fun _ : Fin 1 => α)),S_1,C')` denotes Λᵣ at fold_k : ι^2 → F for code C'.

  **ABF26 mapping.** Probabilistic correctness of folded-RS list decoding. The
  `errStar` accounting comes from MCA bounds (ABF26 Def 4.3 `epsMCA`). The underlying
  list-size bound for FRS specializes ABF26 T3.4 (`subspaceDesign_list_decoding_cz25`
  in `ArkLib/Data/CodingTheory/ListDecoding/Bounds.lean`) via the folded-RS
  τ-subspace-design property (T2.18). -/
lemma folding_preserves_listdecoding_base
  [Fintype F] {S : Finset ι} {k m : ℕ} (hm : 1 ≤ m) {φ : ι ↪ F}
  [Fintype ι] [DecidableEq ι] [Smooth φ] {δ : ℝ≥0}
  {S_0 : Finset (indexPowT S φ 0)} {S_1 : Finset (indexPowT S φ 1)}
  {φ_0 : (indexPowT S φ 0) ↪ F} {φ_1 : (indexPowT S φ 1) ↪ F}
  [∀ i : ℕ, Fintype (indexPowT S φ i)] [∀ i : ℕ, DecidableEq (indexPowT S φ i)]
  [Smooth φ_0] [Smooth φ_1]
  [h : ∀ {f : (indexPowT S φ 0) → F}, DecidableBlockDisagreement 0 k f S_0 φ_0]
  [h : ∀ {f : (indexPowT S φ 1) → F}, DecidableBlockDisagreement 1 k f S_1 φ_1]
  [∀ i : ℕ, Neg (indexPowT S φ i)]
  {C : Set ((indexPowT S φ 0) → F)} (hcode : C = smoothCode φ_0 m)
  (C' : Set ((indexPowT S φ 1) → F)) (hcode' : C' = smoothCode φ_1 (m-1))
  {BStar : (Set (indexPowT S φ 1 → F)) → ℕ → ℝ≥0}
  {errStar : (Set (indexPowT S φ 1 → F)) → ℕ → ℝ≥0 → ℝ≥0} :
    ∀ (f : (indexPowT S φ 0) → F) (hδ : 0 < δ ∧ δ < 1 - (BStar C' 2)),
      Pr_{let α ←$ᵖ F}[
          let listBlock : Set ((indexPowT S φ 0) → F) := Λᵣ(0, k, f, S_0, C, hcode, δ)
          let vec_α : Fin 1 → F := (fun _ : Fin 1 => α)
          let foldSet := fold_k_set listBlock vec_α hm
          let fold := fold_k f vec_α hm
          let listBlock' : Set ((indexPowT S φ 1) → F) := Λᵣ(1, k, fold, S_1, C', hcode', δ)
          foldSet ≠ listBlock'
        ] < errStar C' 2 δ
  := by sorry

/-- Lemma 4.22
  Following same parameters as Lemma 4.21 above, and states
  `∀ α : F, fold_k_set(Λᵣ(0,k,f,S_0,C,δ),(fun _ : Fin 1 => α)) ⊆
      Λᵣ(1,k-1,fold_k(f,(fun _ : Fin 1 => α)),S_1,C',δ)`

  **ABF26 mapping.** Deterministic inclusion form underlying L4.21. The probabilistic
  half (L4.21) bounds the failure probability of the *reverse* inclusion; this lemma
  asserts the *forward* inclusion always holds. No direct ABF26 paper counterpart —
  this is the "easy half" of folded-code list-decoding (corresponds to ABF26's "every
  folded image of a δ-close codeword is δ-close", a structural fact). -/
lemma folding_preserves_listdecoding_bound
  {S : Finset ι} {k m : ℕ} (hm : 1 ≤ m) {φ : ι ↪ F} [Fintype ι] [DecidableEq ι] [Smooth φ]
  {δ : ℝ≥0} {f : (indexPowT S φ 0) → F}
  {S_0 : Finset (indexPowT S φ 0)} {S_1 : Finset (indexPowT S φ 1)}
  {φ_0 : (indexPowT S φ 0) ↪ F} {φ_1 : (indexPowT S φ 1) ↪ F}
  [∀ i : ℕ, Fintype (indexPowT S φ i)] [∀ i : ℕ, DecidableEq (indexPowT S φ i)]
  [Smooth φ_0] [Smooth φ_1]
  [h : ∀ {f : (indexPowT S φ 0) → F}, DecidableBlockDisagreement 0 k f S_0 φ_0]
  [h : ∀ {f : (indexPowT S φ 1) → F}, DecidableBlockDisagreement 1 k f S_1 φ_1]
  [∀ i : ℕ, Neg (indexPowT S φ i)]
  {C : Set ((indexPowT S φ 0) → F)} (hcode : C = smoothCode φ_0 m)
  (C' : Set ((indexPowT S φ 1) → F)) (hcode' : C' = smoothCode φ_1 (m-1))
  {BStar : (Set (indexPowT S φ 1 → F)) → ℕ → ℝ≥0}
  {errStar : (Set (indexPowT S φ 1 → F)) → ℕ → ℝ≥0 → ℝ≥0} :
      ∀ α : F,
        let listBlock : Set ((indexPowT S φ 0) → F) := Λᵣ(0, k, f, S_0, C, hcode, δ)
        let vec_α : Fin 1 → F := (fun _ : Fin 1 => α)
        let foldSet := fold_k_set listBlock vec_α hm
        let fold := fold_k f vec_α hm
        let listBlock' : Set ((indexPowT S φ 1) → F) := Λᵣ(1, k, fold, S_1, C', hcode', δ)
        foldSet ⊆ listBlock'
  := by sorry

/-- Lemma 4.23
  Following same parameters as Lemma 4.21 above, and states
  `Pr_{α ← F} [
      Λᵣ(1,k-1,fold_k(f,(fun _ : Fin 1 => α)),S_1,C',δ) ¬ ⊆
        fold_k_set(Λᵣ(0,k,f,S_0,C,δ),(fun _ : Fin 1 => α))
    ] < errStar(C',2,δ)`

  **ABF26 mapping.** The probabilistic half of L4.21 / L4.22 — bounds the failure
  probability of the reverse inclusion (every δ-close codeword of the folded code
  comes from a δ-close codeword of the unfolded code, except with `errStar` prob).
  Combines L4.22 (forward inclusion deterministic) with this lemma to recover the
  ≠ event of L4.21. -/
lemma folding_preserves_listdecoding_base_ne_subset
  [Fintype F] {S : Finset ι} {k m : ℕ} (hm : 1 ≤ m) {φ : ι ↪ F}
  [Fintype ι] [DecidableEq ι] [Smooth φ] {δ : ℝ≥0}
  {S_0 : Finset (indexPowT S φ 0)} {S_1 : Finset (indexPowT S φ 1)}
  {φ_0 : (indexPowT S φ 0) ↪ F} {φ_1 : (indexPowT S φ 1) ↪ F}
  [∀ i : ℕ, Fintype (indexPowT S φ i)] [∀ i : ℕ, DecidableEq (indexPowT S φ i)]
  [Smooth φ_0] [Smooth φ_1]
  [h : ∀ {f : (indexPowT S φ 0) → F}, DecidableBlockDisagreement 0 k f S_0 φ_0]
  [h : ∀ {f : (indexPowT S φ 1) → F}, DecidableBlockDisagreement 1 k f S_1 φ_1]
  [∀ i : ℕ, Neg (indexPowT S φ i)]
  {C : Set ((indexPowT S φ 0) → F)} (hcode : C = smoothCode φ_0 m)
  (C' : Set ((indexPowT S φ 1) → F)) (hcode' : C' = smoothCode φ_1 (m-1))
  {BStar : (Set (indexPowT S φ 1 → F)) → ℕ → ℝ≥0}
  {errStar : (Set (indexPowT S φ 1 → F)) → ℕ → ℝ≥0 → ℝ≥0} :
    ∀ (f : (indexPowT S φ 0) → F) (hδ : 0 < δ ∧ δ < 1 - (BStar C' 2)),
      Pr_{let α ←$ᵖ F}[
          let listBlock : Set ((indexPowT S φ 0) → F) := Λᵣ(0, k, f, S_0, C, hcode, δ)
          let vec_α : Fin 1 → F := (fun _ : Fin 1 => α)
          let foldSet := fold_k_set listBlock vec_α hm
          let fold := fold_k f vec_α hm
          let listBlock' : Set ((indexPowT S φ 1) → F) :=
            Λᵣ(1, k, fold, S_1, C', hcode', δ)
          ¬ (listBlock' ⊆ foldSet)
        ] < errStar C' 2 δ
  := by sorry

end FoldingLemmas

end Fold

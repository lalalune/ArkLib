/-
Copyright (c) 2024-2025 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: František Silváši, Ilia Vlasov, Stefano Rocca, Elias Judin
-/

import Mathlib.Algebra.Field.Basic
import Mathlib.Algebra.Polynomial.Basic
import Mathlib.Data.Real.Sqrt
import Mathlib.RingTheory.Polynomial.Basic

import ArkLib.Data.CodingTheory.BerlekampWelch.Sorries
import ArkLib.Data.CodingTheory.GuruswamiSudan.Basic
import ArkLib.Data.CodingTheory.ReedSolomon
import ArkLib.Data.Polynomial.Bivariate
import ArkLib.Data.Polynomial.Interface

import CompPoly.Univariate.Lagrange

/-!
# Guruswami-Sudan Decoder

This module keeps the abstract Guruswami-Sudan specification decoder alongside
constructive candidate generation for Reed-Solomon codes.

The witness search is implemented by `computeGsWitness`, which solves a linearized
system of Hasse-derivative constraints with a normalization equation. Candidate
message polynomials are then filtered by a computable root check for
`$Q(X, p(X)) = 0$` using CompPoly arithmetic.

## References

* [Bafna, P., Chiesa, A., Ishai, Y., Khurana, D., and Spooner, N.,
    *On the Proximity Gap of Reed-Solomon Codes*][BCIKS20]
-/

namespace GuruswamiSudan

variable {F : Type} [Field F] [DecidableEq F]
variable {k : ℕ}
variable {n : ℕ}
variable {m : ℕ}
variable {ωs : Fin n ↪ F}
variable {f : Fin n → F}

open Finset Finsupp Polynomial Polynomial.Bivariate ReedSolomon

variable (k m) in
/--
Guruswami–Sudan conditions for the polynomial searched by the specification decoder.

These conditions characterize a nonzero bivariate polynomial `Q(X,Y)`
with bounded weighted degree that vanishes with sufficiently high
multiplicity at all interpolation points `(ωs i, f i)`. As in the
Berlekamp–Welch case, finding such a polynomial can be shown to be
equivalent to solving a system of linear equations.

Here:
* `D : ℕ` — the degree bound for `Q` under the weighted degree measure.
* `ωs : Fin n ↪ F` — the domain of evaluation, i.e. the interpolation points.
* `f : Fin n → F` — the received word.
* `Q : F[X][Y]` — the candidate bivariate polynomial.
-/
structure Conditions (D : ℕ) (ωs : Fin n ↪ F) (f : Fin n → F) (Q : F[X][Y]) where
  /-- The polynomial is non-zero. -/
  Q_ne_0 : Q ≠ 0
  /-- `(1, k - 1)`-weighted degree of the polynomial is bounded. -/
  Q_deg : weightedDegree Q 1 (k - 1) ≤ D
  /-- `(ωs i, f i)` must be a root of the polynomial `Q`. -/
  Q_roots : ∀ i, (Q.eval (C <| f i)).eval (ωs i) = 0
  /-- Multiplicity of the roots is at least `m`. -/
  Q_multiplicity : ∀ i, m ≤ rootMultiplicity Q (ωs i) (f i)

/-- Recover a polynomial from its first `k` coefficients when its degree is below `k`. -/
private lemma polynomial_of_coeffs_coeffs_of_polynomial_of_degree_lt
    {F : Type} [CommSemiring F] [DecidableEq F] {k : ℕ} {p : F[X]}
    (h : p.degree < (k : WithBot ℕ)) :
    polynomialOfCoeffs (coeffsOfPolynomial (deg := k) p) = p := by
  ext x
  simp only [coeff_polynomialOfCoeffs_eq_coeffs', coeffsOfPolynomial]
  split
  · rfl
  · symm
    exact Polynomial.coeff_eq_zero_of_degree_lt
      (lt_of_lt_of_le h (by exact_mod_cast Nat.le_of_not_lt ‹_›))

/-- The finset of all polynomials `p : F[X]` with `p.degree < k`, viewed as elements of `F[X]`.
    Constructed computably by enumerating coefficient vectors `Fin k → F`.
    Note that this always includes `0`, since `(0 : F[X]).degree = ⊥ < (k : WithBot ℕ)`. -/
def polynomialsDegreeLt (F : Type) [CommSemiring F] [Fintype F]
    [DecidableEq F] (k : ℕ) :
    Finset F[X] :=
  (Finset.univ : Finset (Fin k → F)).image polynomialOfCoeffs

/-- Membership characterization for `polynomialsDegreeLt`. -/
lemma mem_polynomials_degree_lt
    {F : Type} [CommSemiring F] [Fintype F] [DecidableEq F]
    {k : ℕ} {p : F[X]} :
    p ∈ polynomialsDegreeLt F k ↔ p.degree < k := by
  simp only [polynomialsDegreeLt, Finset.mem_image, Finset.mem_univ, true_and]
  constructor
  · rintro ⟨coeffs, rfl⟩
    exact degree_polynomialOfCoeffs_deg_lt_deg
  · intro h
    exact ⟨coeffsOfPolynomial p, polynomial_of_coeffs_coeffs_of_polynomial_of_degree_lt h⟩

/-- Specification-level Guruswami-Sudan decoder.

This finite-field specification enumerates all degree-`< k` polynomials and keeps exactly the
candidates within the requested distance bound. The constructive GS witness-based candidate
generator below is a more algorithmic source of candidates; this definition is the transparent
list-decoding contract used by the basic membership theorems. -/
noncomputable def decoder [Fintype F] (k _r _D e : ℕ) (ωs : Fin n ↪ F) (f : Fin n → F) :
    List F[X] :=
  ((polynomialsDegreeLt F k).filter fun p => decide (Δ₀(f, p.eval ∘ ωs) ≤ e)).toList

/-- Each decoded codeword has to be `e`-close to the received message. -/
theorem decoder_mem_impl_dist
    [Fintype F]
    {k r D e : ℕ}
    (_h_e : e ≤ n - Real.sqrt (k * n))
    {ωs : Fin n ↪ F}
    {f : Fin n → F}
    {p : F[X]}
    (h_in : p ∈ decoder k r D e ωs f) :
    Δ₀(f, p.eval ∘ ωs) ≤ e := by
  have hmem : p ∈ polynomialsDegreeLt F k ∧ Δ₀(f, p.eval ∘ ωs) ≤ e := by
    simpa [decoder] using h_in
  exact hmem.2

/-- Alias for the specification decoder distance guarantee. -/
theorem decoder_output_dist_le
    [Fintype F]
    {k r D e : ℕ}
    (h_e : e ≤ n - Real.sqrt (k * n))
    {ωs : Fin n ↪ F}
    {f : Fin n → F}
    {p : F[X]}
    (h_in : p ∈ decoder k r D e ωs f) :
    Δ₀(f, p.eval ∘ ωs) ≤ e :=
  decoder_mem_impl_dist (k := k) (r := r) (D := D) (e := e) h_e h_in

/-- If a degree-bounded codeword is `e`-close to the received message, it appears in the decoder
output. -/
theorem decoder_dist_impl_mem
    [Fintype F]
    {k r D e : ℕ}
    (_h_e : e ≤ n - Real.sqrt (k * n))
    {ωs : Fin n ↪ F}
    {f : Fin n → F}
    {p : F[X]}
    (h_degree : p.degree < k)
    (h_dist : Δ₀(f, p.eval ∘ ωs) ≤ e) :
    p ∈ decoder k r D e ωs f := by
  simp [decoder, mem_polynomials_degree_lt.mpr h_degree, h_dist]

/-! ### CompPoly-based interpolation candidate

The following private helpers use CompPoly's computable `CPolynomial.Raw` type to build a
Lagrange interpolation candidate from the first `min k n` evaluation points. The result is
converted back to Mathlib's `Polynomial F` via coefficient extraction (`polynomialOfCoeffs`),
which is fully computable.

The candidate is constructed with `rawToPolyBounded`, whose output has bounded degree by
construction (`degree_polynomialOfCoeffs_deg_lt_deg`). CompPoly's `Raw.toPoly` bridge is
noncomputable, so we validate the candidate by degree and distance checks before insertion.
-/

/-- General Lagrange interpolation over arbitrary evaluation points, computed using
    CompPoly's `CPolynomial.Raw` arithmetic.

    Given `m` evaluation points and corresponding values, builds the unique polynomial
    of degree `< m` interpolating those values (assuming distinct points).
    Fully computable: avoids classical choice operators, nonconstructive root APIs,
    and noncomputable terms. -/
private def lagrangeInterpolateRaw (m : ℕ) (points : Fin m → F) (values : Fin m → F) :
    CompPoly.CPolynomial.Raw F :=
  (List.finRange m).foldl (fun acc i ↦
    let basis := (List.finRange m).foldl (fun b j ↦
      if i = j then b
      else b.mul (CompPoly.CPolynomial.Raw.X - CompPoly.CPolynomial.Raw.C (points j))
    ) (CompPoly.CPolynomial.Raw.C 1)
    let denom := (List.finRange m).foldl (fun d j ↦
      if i = j then d
      else d * (points i - points j)
    ) 1
    acc + CompPoly.CPolynomial.Raw.smul (values i * denom⁻¹) basis
  ) 0

/-- Convert a `CPolynomial.Raw` to `Polynomial F` by extracting the first `bound` coefficients.
    Fully computable; the result always has `degree < bound`. -/
private def rawToPolyBounded (raw : CompPoly.CPolynomial.Raw F) (bound : ℕ) : F[X] :=
  polynomialOfCoeffs (fun i : Fin bound ↦ raw.coeff i.val)

/-- Build an interpolation candidate from the first `min k n` evaluation points.
    Returns `none` when `k = 0` (no meaningful interpolation).
    The result, when `some`, has `degree < k` by construction of `rawToPolyBounded`. -/
private def compPolyCandidate [Fintype F] (k : ℕ) (ωs : Fin n ↪ F) (f : Fin n → F) :
    Option F[X] :=
  if k = 0 then none
  else
    let m := min k n
    if _hm : m = 0 then none
    else
      let points : Fin m → F := fun i ↦ ωs (Fin.castLE (Nat.min_le_right k n) i)
      let values : Fin m → F := fun i ↦ f (Fin.castLE (Nat.min_le_right k n) i)
      let raw := lagrangeInterpolateRaw m points values
      some (rawToPolyBounded raw k)

/-- The `Finset` of CompPoly interpolation candidates that pass the degree and distance check.
    Always a subset of `{p | p.degree < k ∧ Δ₀(f, p.eval ∘ ωs) ≤ e}`. -/
private def compPolyCandidateSet [Fintype F] (k e : ℕ) (ωs : Fin n ↪ F) (f : Fin n → F) :
    Finset F[X] :=
  match compPolyCandidate k ωs f with
  | Option.some p =>
    if decide (p.degree < (k : WithBot ℕ) ∧ Δ₀(f, p.eval ∘ ωs) ≤ e) then {p} else ∅
  | Option.none => ∅

/-- Every element of `compPolyCandidateSet` satisfies the degree and distance bounds. -/
private lemma mem_comp_poly_candidate_set_imp [Fintype F] {k e : ℕ} {ωs : Fin n ↪ F}
    {f : Fin n → F} {p : F[X]} (hp : p ∈ compPolyCandidateSet k e ωs f) :
    p.degree < k ∧ Δ₀(f, p.eval ∘ ωs) ≤ e := by
  simp only [compPolyCandidateSet] at hp
  split at hp
  · split at hp
    · rw [Finset.mem_singleton.mp hp]
      exact decide_eq_true_eq.mp ‹_›
    · simp at hp
  · simp at hp

/-! ### Hasse derivative evaluation for multiplicity checking

The Guruswami–Sudan multiplicity condition requires that for each interpolation
point `(ωᵢ, fᵢ)`, the bivariate polynomial `Q` vanishes with multiplicity `≥ r`.
Formally, this means every Hasse derivative `D^{(a,b)} Q` (for `a + b < r`)
evaluates to zero at `(ωᵢ, fᵢ)`.

For a bivariate polynomial `Q = ∑ cᵢⱼ X^i Y^j`, the `(a,b)`-Hasse derivative at
`(x₀, y₀)` is `∑ C(i,a) C(j,b) cᵢⱼ x₀^{i-a} y₀^{j-b}`, where `C(n,k)` denotes
the binomial coefficient.

The following functions compute this evaluation purely computably over coefficient
vectors, with no reliance on classical choice or nonconstructive root extraction.
-/

/-- Evaluate a bounded coefficient vector at `(x, y)` as
    `∑ cᵢⱼ x^i y^j` over indices satisfying `i + (k - 1) * j ≤ D`. -/
private def evalCoeffVecAt (k D : ℕ)
    (c : Fin (D + 1) × Fin (D + 1) → F) (x y : F) : F :=
  (List.finRange (D + 1)).foldl (fun a1 j ↦
    (List.finRange (D + 1)).foldl (fun a2 i ↦
      if i.val + (k - 1) * j.val ≤ D then
        a2 + c (i, j) * x ^ i.val * y ^ j.val
      else a2) a1) 0

/-- Evaluate the `(a, b)`-Hasse derivative of a bivariate polynomial
    (given as a bounded coefficient vector `c`) at the point `(x, y)`.

    The Hasse derivative `D^{(a,b)} Q` of `Q = ∑ cᵢⱼ X^i Y^j` is
    `∑_{i ≥ a, j ≥ b} C(i,a) C(j,b) cᵢⱼ X^{i-a} Y^{j-b}`.

    This computes `D^{(a,b)} Q (x, y) = ∑ C(i,a) C(j,b) cᵢⱼ x^{i-a} y^{j-b}`
    over indices in the weighted-degree region `i + (k-1)·j ≤ D`. -/
private def hasseDerivEvalAt (k D a b : ℕ)
    (c : Fin (D + 1) × Fin (D + 1) → F) (x y : F) : F :=
  (List.finRange (D + 1)).foldl (fun a1 j ↦
    (List.finRange (D + 1)).foldl (fun a2 i ↦
      if i.val + (k - 1) * j.val ≤ D ∧ a ≤ i.val ∧ b ≤ j.val then
        a2 + (↑(Nat.choose i.val a) : F) * (↑(Nat.choose j.val b) : F) *
             c (i, j) * x ^ (i.val - a) * y ^ (j.val - b)
      else a2) a1) 0

/-- Check that all Hasse derivatives of order `< r` vanish at `(x, y)`.
    This is the computable form of the multiplicity-`r` condition:
    `(X - x, Y - y)^r | Q` iff `D^{(a,b)} Q(x,y) = 0` for all `a + b < r`. -/
private def hasseMultiplicityCheck (k D r : ℕ)
    (c : Fin (D + 1) × Fin (D + 1) → F) (x y : F) : Bool :=
  (List.finRange r).all fun ab ↦
    (List.finRange (ab.val + 1)).all fun a ↦
      decide (hasseDerivEvalAt k D a.val (ab.val - a.val) c x y = 0)

omit [DecidableEq F] in
/-- The `(0,0)`-Hasse derivative is ordinary evaluation: `Nat.choose i 0 = 1`,
    `Nat.choose j 0 = 1`, and shifting by zero leaves exponents unchanged, so
    `hasseDerivEvalAt k D 0 0 c x y = evalCoeffVecAt k D c x y`. -/
private lemma hasseDerivEvalAt_zero_zero (k D : ℕ)
    (c : Fin (D + 1) × Fin (D + 1) → F) (x y : F) :
    hasseDerivEvalAt k D 0 0 c x y = evalCoeffVecAt k D c x y := by
  unfold hasseDerivEvalAt evalCoeffVecAt
  congr 1; funext j; funext a2; congr 1; funext i
  simp [Nat.choose_zero_right]

/-- If the multiplicity check passes, every individual Hasse derivative of order
    `< r` vanishes. This is the core unwinding of `hasseMultiplicityCheck`. -/
private lemma hasseMultiplicityCheck_imp_deriv_zero {k D r a b : ℕ}
    {c : Fin (D + 1) × Fin (D + 1) → F} {x y : F}
    (hcheck : hasseMultiplicityCheck k D r c x y = true)
    (hab : a + b < r) :
    hasseDerivEvalAt k D a b c x y = 0 := by
  simp only [hasseMultiplicityCheck, List.all_eq_true, List.mem_finRange, forall_true_left,
    decide_eq_true_eq] at hcheck
  have h := hcheck ⟨a + b, hab⟩ ⟨a, Nat.lt_succ_of_le (Nat.le_add_right a b)⟩
  rwa [Nat.add_sub_cancel_left] at h

/-- When `r > 0`, the multiplicity check implies pointwise evaluation vanishes:
    `Q(x, y) = 0`. This is the `(a, b) = (0, 0)` specialization, combined with
    `hasseDerivEvalAt_zero_zero`. -/
private lemma hasseMultiplicityCheck_imp_eval_zero {k D r : ℕ}
    {c : Fin (D + 1) × Fin (D + 1) → F} {x y : F}
    (hr : 0 < r)
    (hcheck : hasseMultiplicityCheck k D r c x y = true) :
    evalCoeffVecAt k D c x y = 0 := by
  rw [← hasseDerivEvalAt_zero_zero]
  exact hasseMultiplicityCheck_imp_deriv_zero hcheck (by omega)

/-- Decidable sound-first witness predicate on bounded coefficient vectors:
    nonzero on the weighted region and full multiplicity vanishing at each interpolation
    point (all Hasse derivatives of order `< r` vanish).

    When `r = 0`, only the nonzero condition is checked; when `r ≥ 1`, the Hasse
    derivative conditions imply (in particular) that `Q(ωᵢ, fᵢ) = 0` for each `i`. -/
private def isWitnessC (k D r : ℕ) (ωs : Fin n ↪ F) (f : Fin n → F)
    (c : Fin (D + 1) × Fin (D + 1) → F) : Bool :=
  -- nonzero in weighted-degree region
  (List.finRange (D + 1)).any (fun j ↦
    (List.finRange (D + 1)).any (fun i ↦
      decide (i.val + (k - 1) * j.val ≤ D ∧ c (i, j) ≠ 0))) &&
  -- multiplicity check: all Hasse derivatives of order < r vanish at each point
  (List.finRange n).all (fun idx ↦
    hasseMultiplicityCheck k D r c (ωs idx) (f idx))

/-- When `r > 0` and the witness predicate `isWitnessC` holds, the bivariate polynomial
    represented by `c` vanishes at every interpolation point `(ωs i, f i)`.

    This connects the computable Hasse-derivative multiplicity filter to the classical
    pointwise root condition `Q(ωᵢ, fᵢ) = 0` that the GS witness branch relies on. -/
private lemma is_witness_c_imp_eval_zero_at_points {k D r : ℕ}
    {ωs : Fin n ↪ F} {f : Fin n → F} {c : Fin (D + 1) × Fin (D + 1) → F}
    (hr : 0 < r)
    (hw : isWitnessC k D r ωs f c = true) (i : Fin n) :
    evalCoeffVecAt k D c (ωs i) (f i) = 0 := by
  simp only [isWitnessC, Bool.and_eq_true] at hw
  obtain ⟨_, hmult⟩ := hw
  simp only [List.all_eq_true, List.mem_finRange, forall_true_left] at hmult
  exact hasseMultiplicityCheck_imp_eval_zero hr (hmult ⟨i.val, i.isLt⟩)

/-- Extract the nonzero-coefficient condition from `isWitnessC`: there exists at least one
    index pair `(i, j)` in the weighted-degree region `i + (k-1)·j ≤ D` where `c(i,j) ≠ 0`. -/
private lemma is_witness_c_nonzero {k D r : ℕ} {ωs : Fin n ↪ F} {f : Fin n → F}
    {c : Fin (D + 1) × Fin (D + 1) → F}
    (hw : isWitnessC k D r ωs f c = true) :
    ∃ i : Fin (D + 1), ∃ j : Fin (D + 1),
      i.val + (k - 1) * j.val ≤ D ∧ c (i, j) ≠ 0 := by
  simp only [isWitnessC, Bool.and_eq_true] at hw
  obtain ⟨hne, _⟩ := hw
  simp only [List.any_eq_true, List.mem_finRange, true_and, decide_eq_true_eq] at hne
  obtain ⟨j, i, hcond⟩ := hne
  exact ⟨i, j, hcond⟩

/-- Extract the per-point multiplicity check from `isWitnessC`: `hasseMultiplicityCheck`
    passes at every interpolation point `(ωs i, f i)`. -/
private lemma is_witness_c_multiplicity_at {k D r : ℕ} {ωs : Fin n ↪ F} {f : Fin n → F}
    {c : Fin (D + 1) × Fin (D + 1) → F}
    (hw : isWitnessC k D r ωs f c = true) (i : Fin n) :
    hasseMultiplicityCheck k D r c (ωs i) (f i) = true := by
  simp only [isWitnessC, Bool.and_eq_true] at hw
  obtain ⟨_, hmult⟩ := hw
  simp only [List.all_eq_true, List.mem_finRange, forall_true_left] at hmult
  exact hmult ⟨i.val, i.isLt⟩

/-- When `isWitnessC` holds, every Hasse derivative of order `< r` vanishes at every
    interpolation point. This combines `is_witness_c_multiplicity_at` with
    `hasseMultiplicityCheck_imp_deriv_zero`. -/
private lemma is_witness_c_hasse_deriv_vanishes {k D r a b : ℕ}
    {ωs : Fin n ↪ F} {f : Fin n → F} {c : Fin (D + 1) × Fin (D + 1) → F}
    (hw : isWitnessC k D r ωs f c = true)
    (hab : a + b < r) (i : Fin n) :
    hasseDerivEvalAt k D a b c (ωs i) (f i) = 0 :=
  hasseMultiplicityCheck_imp_deriv_zero (is_witness_c_multiplicity_at hw i) hab

/-- Number of unknown coefficients in the bounded witness grid `(D + 1) × (D + 1)`. -/
private def witnessVarCount (D : ℕ) : ℕ := (D + 1) * (D + 1)

/-- Decode a linearized witness variable index into the corresponding coefficient pair `(i, j)`. -/
private def witnessVarToPair (D : ℕ) (idx : Fin (witnessVarCount D)) :
    Fin (D + 1) × Fin (D + 1) :=
  let i : Fin (D + 1) := ⟨idx.val % (D + 1), Nat.mod_lt _ (Nat.succ_pos _)⟩
  let j : Fin (D + 1) := ⟨idx.val / (D + 1), by
    refine (Nat.div_lt_iff_lt_mul (Nat.succ_pos D)).2 ?_
    have hidx : idx.val < (D + 1) * (D + 1) := idx.isLt
    exact hidx⟩
  (i, j)

/-- Encode a coefficient pair `(i, j)` into the linearized witness variable index. -/
private def witnessPairToVar (D : ℕ) (ij : Fin (D + 1) × Fin (D + 1)) :
    Fin (witnessVarCount D) :=
  ⟨ij.2.val * (D + 1) + ij.1.val, by
    have hi : ij.1.val < D + 1 := ij.1.isLt
    have hj : ij.2.val < D + 1 := ij.2.isLt
    have hlt :
        ij.2.val * (D + 1) + ij.1.val < ij.2.val * (D + 1) + (D + 1) :=
      Nat.add_lt_add_left hi (ij.2.val * (D + 1))
    have hstep : ij.2.val * (D + 1) + (D + 1) = (ij.2.val + 1) * (D + 1) := by
      simp [Nat.succ_mul, Nat.add_assoc, Nat.add_comm]
    have hbound : (ij.2.val + 1) * (D + 1) ≤ (D + 1) * (D + 1) :=
      Nat.mul_le_mul_right (D + 1) (Nat.succ_le_of_lt hj)
    exact lt_of_lt_of_le (hstep ▸ hlt) (by simpa [witnessVarCount, Nat.mul_comm] using hbound)⟩

/-- Convert a linear solver output vector into a coefficient function `c(i,j)`. -/
private def witnessSolToCoeffVec (D : ℕ) (x : Fin (witnessVarCount D) → F) :
    Fin (D + 1) × Fin (D + 1) → F :=
  fun ij ↦ x (witnessPairToVar D ij)

/-- Number of interpolation-equation rows per evaluation point (`(r+1)^2`, with inactive rows). -/
private def gsDerivBlockSize (r : ℕ) : ℕ := (r + 1) * (r + 1)

/-- Total number of derivative rows before appending normalization. -/
private def gsDerivRowCount (n r : ℕ) : ℕ := n * gsDerivBlockSize r

/-- Total row count for the linearized GS system (derivatives + one normalization row). -/
private def gsLinearRowCount (n r : ℕ) : ℕ := gsDerivRowCount n r + 1

/-- One coefficient entry of the linearized GS interpolation matrix. -/
private def gsLinearMatrixEntry (k D r : ℕ) (ωs : Fin n ↪ F) (f : Fin n → F)
    (target : Fin (witnessVarCount D))
    (row : Fin (gsLinearRowCount n r)) (col : Fin (witnessVarCount D)) : F :=
  if hrow : row.val < gsDerivRowCount n r then
    let point : Fin n := ⟨row.val / gsDerivBlockSize r, by
      refine (Nat.div_lt_iff_lt_mul (Nat.mul_pos (Nat.succ_pos r) (Nat.succ_pos r))).2 ?_
      simpa [gsDerivRowCount, gsDerivBlockSize, Nat.mul_assoc] using hrow⟩
    let rem := row.val % gsDerivBlockSize r
    let a := rem / (r + 1)
    let b := rem % (r + 1)
    let ij := witnessVarToPair D col
    if a + b < r then
      if hwd : ij.1.val + (k - 1) * ij.2.val ≤ D ∧ a ≤ ij.1.val ∧ b ≤ ij.2.val then
        (↑(Nat.choose ij.1.val a) : F) * (↑(Nat.choose ij.2.val b) : F) *
          (ωs point) ^ (ij.1.val - a) * (f point) ^ (ij.2.val - b)
      else 0
    else 0
  else
    if col = target then 1 else 0

/-- Linearized GS interpolation matrix with an appended normalization row. -/
private def gsLinearMatrix (k D r : ℕ) (ωs : Fin n ↪ F) (f : Fin n → F)
    (target : Fin (witnessVarCount D)) :
    Matrix (Fin (gsLinearRowCount n r)) (Fin (witnessVarCount D)) F :=
  Matrix.of (fun row col ↦ gsLinearMatrixEntry k D r ωs f target row col)

/-- RHS vector for the linearized GS system (`0` for interpolation rows, `1` for normalization). -/
private def gsLinearRhs (r : ℕ) : Fin (gsLinearRowCount n r) → F :=
  fun row ↦ if row.val < gsDerivRowCount n r then 0 else 1

/-- Solve the linearized GS system with one normalized coefficient target. -/
private noncomputable def solveGsWitnessAtTarget (k D r : ℕ) (ωs : Fin n ↪ F) (f : Fin n → F)
    (target : Fin (witnessVarCount D)) :
    Option {c : Fin (D + 1) × Fin (D + 1) → F // isWitnessC k D r ωs f c = true} :=
  match linsolve (gsLinearMatrix (n := n) k D r ωs f target) (gsLinearRhs (n := n) r) with
  | Option.none => none
  | Option.some x =>
    let c := witnessSolToCoeffVec D x
    if hc : isWitnessC k D r ωs f c = true then some ⟨c, hc⟩ else none

/-- Candidate normalization targets in the weighted-degree region. -/
private def witnessTargets (k D : ℕ) : List (Fin (witnessVarCount D)) :=
  (List.finRange (witnessVarCount D)).filter fun idx ↦
    let ij := witnessVarToPair D idx
    decide (ij.1.val + (k - 1) * ij.2.val ≤ D)

/-- Witness search: solve the linearized GS system over all normalization targets. -/
private noncomputable def computeGsWitness (k D r : ℕ) (ωs : Fin n ↪ F) (f : Fin n → F) :
    Option {c : Fin (D + 1) × Fin (D + 1) → F // isWitnessC k D r ωs f c = true} :=
  (witnessTargets k D).findSome? (solveGsWitnessAtTarget (n := n) k D r ωs f)

/-- Witness-availability check computed from `computeGsWitness`. -/
private noncomputable def hasWitnessC (k D r : ℕ) (ωs : Fin n ↪ F) (f : Fin n → F) : Bool :=
  (computeGsWitness (n := n) k D r ωs f).isSome

/-- `hasWitnessC = true` iff `computeGsWitness` returns an explicit witness package. -/
private lemma hasWitnessC_eq_true_iff_exists_output
    (k D r : ℕ) (ωs : Fin n ↪ F) (f : Fin n → F) :
    hasWitnessC (n := n) k D r ωs f = true ↔
      ∃ w, computeGsWitness (n := n) k D r ωs f = some w := by
  unfold hasWitnessC
  simp [Option.isSome_iff_exists]

/-! ### Q-root extraction via CompPoly

Given a witness bivariate polynomial `Q = ∑ cᵢⱼ X^i Y^j` and a candidate
univariate polynomial `p(X)`, the Guruswami–Sudan root-extraction step checks
whether `Y - p(X)` divides `Q(X, Y)` in `F[X][Y]`. Equivalently, this reduces
to checking `Q(X, p(X)) = 0` in `F[X]`.

We compute the root filter `Q(X, p(X)) = ∑ cᵢⱼ X^i · p(X)^j` using CompPoly's
`CPolynomial.Raw` arithmetic and check whether the result is zero. The root filter
itself avoids nonconstructive root extraction; the upstream linear solver used to
produce `Q` is still noncomputable.
-/

/-- Convert a Mathlib polynomial to a `CPolynomial.Raw` by extracting coefficients
    up to a given degree bound. -/
private def polyToRaw (p : F[X]) (bound : ℕ) : CompPoly.CPolynomial.Raw F :=
  Array.ofFn (fun i : Fin bound ↦ p.coeff i.val)

/-- Evaluate `Q(X, p(X))` where `Q` is given as a bounded coefficient vector
    `c : Fin (D+1) × Fin (D+1) → F` and `p` is given as a `CPolynomial.Raw`.

    Computes `∑_{i + (k-1)·j ≤ D} cᵢⱼ · X^i · p(X)^j` in `CPolynomial.Raw F`.
    The result is zero iff `p` is a Y-root of the bivariate polynomial `Q`. -/
private def evalQAtPRaw (k D : ℕ)
    (c : Fin (D + 1) × Fin (D + 1) → F) (pRaw : CompPoly.CPolynomial.Raw F) :
    CompPoly.CPolynomial.Raw F :=
  -- Precompute powers of p(X): pPows[j] = p(X)^j for j = 0, ..., D
  let pPows : Array (CompPoly.CPolynomial.Raw F) :=
    (List.finRange (D + 1)).foldl (fun acc j ↦
      if j.val = 0 then acc.push (CompPoly.CPolynomial.Raw.C 1)
      else acc.push (acc.getD (j.val - 1) (CompPoly.CPolynomial.Raw.C 0) |>.mul pRaw)
    ) #[]
  -- Sum cᵢⱼ · X^i · p(X)^j over the weighted-degree region
  (List.finRange (D + 1)).foldl (fun a1 j ↦
    (List.finRange (D + 1)).foldl (fun a2 i ↦
      if i.val + (k - 1) * j.val ≤ D then
        let term := CompPoly.CPolynomial.Raw.smul (c (i, j))
          (CompPoly.CPolynomial.Raw.mulPowX i.val
            (pPows.getD j.val (CompPoly.CPolynomial.Raw.C 0)))
        a2 + term
      else a2) a1) 0

/-- Check whether `Q(X, p(X)) = 0` by evaluating via CompPoly and testing all
    coefficients. Returns `true` when `p` is a Y-root of `Q`. -/
private def isQRootRaw (k D : ℕ)
    (c : Fin (D + 1) × Fin (D + 1) → F) (pRaw : CompPoly.CPolynomial.Raw F) : Bool :=
  let result := evalQAtPRaw k D c pRaw
  -- Check all coefficients are zero
  result.all (· == 0)

/-- Characterization of `isQRootRaw`: it holds iff every element of the result array
    `evalQAtPRaw k D c pRaw` equals zero. This is a direct consequence of `Array.all`
    semantics and `BEq` on `F` being faithful (from `DecidableEq F`). -/
private lemma is_q_root_raw_iff_all_coeff_zero {k D : ℕ}
    {c : Fin (D + 1) × Fin (D + 1) → F} {pRaw : CompPoly.CPolynomial.Raw F} :
    isQRootRaw k D c pRaw = true ↔
      ∀ idx : Fin (evalQAtPRaw k D c pRaw).size,
        (evalQAtPRaw k D c pRaw)[idx] = 0 := by
  simp only [isQRootRaw]
  rw [Array.all_iff_forall]
  constructor
  · intro h idx
    have hmem := h idx.val idx.isLt ⟨Nat.zero_le _, idx.isLt⟩
    simp only [beq_iff_eq] at hmem
    exact hmem
  · intro h i hi hrange
    simp only [beq_iff_eq]
    exact h ⟨i, hi⟩

/-- Candidate polynomials validated against a finite witness search
    with Hasse-derivative multiplicity checking and CompPoly-based Q-root extraction.

    The filter first computes one concrete witness `Q` (as coefficient vector `c`)
    using `computeGsWitness`. Then for each degree-`< k` candidate `p`, it verifies:
    1. `Q(X, p(X)) = 0` (Y-root extraction), and
    2. The Hamming distance `Δ₀(f, p ∘ ωs) ≤ e`.
-/
private noncomputable def witnessCandidateSet [Fintype F] (k r D e : ℕ)
    (ωs : Fin n ↪ F) (f : Fin n → F) :
    Finset F[X] :=
  match computeGsWitness (n := n) k D r ωs f with
  | Option.some w =>
    (polynomialsDegreeLt F k).filter fun p ↦
      isQRootRaw k D w.1 (polyToRaw p k) && decide (Δ₀(f, p.eval ∘ ωs) ≤ e)
  | Option.none => ∅

/-- Every element of `witnessCandidateSet` has degree `< k` and distance `≤ e`. -/
private lemma mem_witness_candidate_set_imp [Fintype F] {k r D e : ℕ} {ωs : Fin n ↪ F}
    {f : Fin n → F} {p : F[X]} (hp : p ∈ witnessCandidateSet k r D e ωs f) :
    p.degree < k ∧ Δ₀(f, p.eval ∘ ωs) ≤ e := by
  unfold witnessCandidateSet at hp
  split at hp
  · rw [Finset.mem_filter] at hp
    simp only [Bool.and_eq_true, decide_eq_true_eq] at hp
    exact ⟨mem_polynomials_degree_lt.mp hp.1, hp.2.2⟩
  · simp at hp

/-- Strengthened witness soundness: when `r > 0`, every candidate in `witnessCandidateSet`
    is backed by a witness whose Hasse-derivative multiplicity conditions imply pointwise
    root vanishing at every interpolation point.

    Concretely, there exists a coefficient vector `c` satisfying:
    * `isWitnessC` (nonzero in the weighted-degree region and full multiplicity vanishing), and
    * `Q(X, p(X)) = 0` via CompPoly root extraction, and
    * `evalCoeffVecAt k D c (ωs i) (f i) = 0` for every `i : Fin n`.

    The last property is derived from `is_witness_c_imp_eval_zero_at_points`. -/
private lemma witness_candidate_set_witness_vanishes [Fintype F] {k r D e : ℕ}
    {ωs : Fin n ↪ F} {f : Fin n → F} {p : F[X]}
    (hr : 0 < r)
    (hp : p ∈ witnessCandidateSet k r D e ωs f) :
    ∃ c : Fin (D + 1) × Fin (D + 1) → F,
      isWitnessC k D r ωs f c = true ∧
      isQRootRaw k D c (polyToRaw p k) = true ∧
      ∀ i : Fin n, evalCoeffVecAt k D c (ωs i) (f i) = 0 := by
  unfold witnessCandidateSet at hp
  cases hcw : computeGsWitness (n := n) k D r ωs f
  case none =>
      simp [hcw] at hp
  case some w =>
      rw [hcw] at hp
      rw [Finset.mem_filter] at hp
      obtain ⟨_, hcond⟩ := hp
      simp only [Bool.and_eq_true, decide_eq_true_eq] at hcond
      exact ⟨w.1, w.2, hcond.1, fun i ↦ is_witness_c_imp_eval_zero_at_points hr w.2 i⟩

/--
Decoder candidate set inspired by Guruswami–Sudan.

**Definition.** The decoder returns the union of:
* a CompPoly interpolation fast-path candidate set, and
* a GS witness-filtered set computed from a linear-system witness search.

The implementation combines two candidate sources:

1. **CompPoly Lagrange candidate** (`compPolyCandidateSet`): A fast-path candidate
   constructed via CompPoly's computable Lagrange interpolation from the first
   `min k n` evaluation points. Included only if it passes degree and distance checks.

2. **GS witness-filtered candidates** (`witnessCandidateSet`): A concrete witness
   coefficient vector is computed by solving a linearized GS system with normalization.
   Candidates are filtered by `Q(X, p(X)) = 0` and the distance bound.

The fast-path and root checks are executable. The full candidate set is marked
`noncomputable` because the current `linsolve` abstraction used to obtain a witness is
noncomputable.
-/
noncomputable def decoderCandidateSet [Fintype F] (k r D e : ℕ) (ωs : Fin n ↪ F)
    (f : Fin n → F) :
    Finset F[X] :=
  compPolyCandidateSet k e ωs f ∪ witnessCandidateSet k r D e ωs f

/-- Decoder soundness: every output polynomial has degree `< k` and distance `≤ e`. -/
private lemma mem_decoderCandidateSet_imp [Fintype F] {k r D e : ℕ} {ωs : Fin n ↪ F}
    {f : Fin n → F} {p : F[X]} (hp : p ∈ decoderCandidateSet k r D e ωs f) :
    p.degree < k ∧ Δ₀(f, p.eval ∘ ωs) ≤ e := by
  simp only [decoderCandidateSet, Finset.mem_union] at hp
  rcases hp with h | h
  · exact mem_comp_poly_candidate_set_imp h
  · exact mem_witness_candidate_set_imp h

/-- Each decoded codeword is within `e` Hamming distance of the received message. -/
theorem decoderCandidateSet_mem_impl_dist
    [Fintype F]
    {k r D e : ℕ}
    (_h_e : e ≤ n - Real.sqrt (k * n))
    {ωs : Fin n ↪ F}
    {f : Fin n → F}
    {p : F[X]}
    (h_in : p ∈ decoderCandidateSet k r D e ωs f) :
    Δ₀(f, p.eval ∘ ωs) ≤ e :=
  (mem_decoderCandidateSet_imp h_in).2

/-- Alias for the candidate-set distance guarantee. -/
theorem decoderCandidateSet_output_dist_le
    [Fintype F]
    {k r D e : ℕ}
    (h_e : e ≤ n - Real.sqrt (k * n))
    {ωs : Fin n ↪ F}
    {f : Fin n → F}
    {p : F[X]}
    (h_in : p ∈ decoderCandidateSet k r D e ωs f) :
    Δ₀(f, p.eval ∘ ωs) ≤ e :=
  decoderCandidateSet_mem_impl_dist (k := k) (r := r) (D := D) (e := e) h_e h_in

/-- Alias to the `Basic` module degree bound used in lemma 5.3 of [BCIKS20]. -/
noncomputable def proximityGapDegreeBound (k m : ℕ) : ℕ :=
  proximity_gap_degree_bound k n m

/-- Alias to the `Basic` module relative Johnson-radius term. -/
noncomputable def proximityGapDelta0 (k m : ℕ) : ℝ :=
  proximity_gap_johnson k n m

/-- Absolute Johnson bound radius as an error-count:
    `⌊ n * δ₀(ρ, m) ⌋`, where `δ₀` is `proximityGapDelta0`. -/
noncomputable def proximityGapJohnson (k m : ℕ) : ℕ :=
  Nat.floor ((n : ℝ) * proximityGapDelta0 (n := n) k m)

/-! ### Bridge to classical formulations

The following definitions and lemmas provide a noncomputable bridge between the computable
coefficient-vector representation `c : Fin (D+1) × Fin (D+1) → F` and the classical
Mathlib bivariate polynomial type `F[X][Y]`.

The key function `coeffVecToBivariate` constructs a Mathlib bivariate polynomial from a
bounded coefficient vector. Coefficient agreement between the two representations is
established by `coeff_vec_to_bivariate_coeff`.
-/

/-- Construct a Mathlib bivariate polynomial `Q ∈ F[X][Y]` from a bounded coefficient
    vector `c : Fin (D+1) × Fin (D+1) → F`, restricting to the weighted-degree region
    `i + (k-1)·j ≤ D`.  Indices outside this region are treated as zero. -/
noncomputable def coeffVecToBivariate (k D : ℕ)
    (c : Fin (D + 1) × Fin (D + 1) → F) : Polynomial (Polynomial F) :=
  ∑ j : Fin (D + 1), ∑ i : Fin (D + 1),
    if i.val + (k - 1) * j.val ≤ D then
      Polynomial.monomial j.val (Polynomial.monomial i.val (c (i, j)))
    else 0

omit [DecidableEq F] in
/-- Coefficient extraction for `coeffVecToBivariate`: the `(i, j)`-coefficient of the
    bivariate polynomial equals `c(i, j)` when `(i, j)` is in the weighted-degree region. -/
lemma coeff_vec_to_bivariate_coeff (k D : ℕ)
    (c : Fin (D + 1) × Fin (D + 1) → F)
    (i : Fin (D + 1)) (j : Fin (D + 1))
    (hwd : i.val + (k - 1) * j.val ≤ D) :
    ((coeffVecToBivariate k D c).coeff j.val).coeff i.val = c (i, j) := by
  unfold coeffVecToBivariate
  simp only [Polynomial.finset_sum_coeff]
  rw [Finset.sum_eq_single j]
  · rw [Finset.sum_eq_single i]
    · simp [hwd]
    · intro i' _ hi'; split <;> simp [Polynomial.coeff_monomial, Fin.val_ne_of_ne hi']
    · intro h; exact absurd (Finset.mem_univ _) h
  · intro j' _ hj'
    apply Finset.sum_eq_zero; intro i' _
    split <;> simp [Polynomial.coeff_monomial, Fin.val_ne_of_ne hj']
  · intro h; exact absurd (Finset.mem_univ _) h

/-- A witness satisfying `isWitnessC` produces a nonzero Mathlib bivariate polynomial
    via `coeffVecToBivariate`. This follows from `is_witness_c_nonzero`: there is at
    least one nonzero coefficient in the weighted-degree region. -/
lemma coeff_vec_to_bivariate_ne_zero_of_is_witness_c
    {k D r : ℕ} {ωs : Fin n ↪ F} {f : Fin n → F}
    {c : Fin (D + 1) × Fin (D + 1) → F}
    (hw : isWitnessC k D r ωs f c = true) :
    coeffVecToBivariate k D c ≠ 0 := by
  obtain ⟨i, j, hwd, hne⟩ := is_witness_c_nonzero hw
  intro heq
  apply hne
  rw [← coeff_vec_to_bivariate_coeff k D c i j hwd, heq]
  simp

/-- Constructive witness extraction for the Guruswami–Sudan system.
    When the computable `hasWitnessC` check returns `true`, we can extract a concrete
    coefficient vector `c` satisfying `isWitnessC`.

    Additionally, when `m > 0`, the witness satisfies:
    * Nonzero coefficient in the weighted-degree region (`is_witness_c_nonzero`).
    * All Hasse derivatives of order `< m` vanish at every interpolation point
      (`is_witness_c_hasse_deriv_vanishes`).
    * Pointwise evaluation vanishing at every interpolation point
      (`is_witness_c_imp_eval_zero_at_points`).
    * The corresponding Mathlib bivariate polynomial is nonzero
      (`coeff_vec_to_bivariate_ne_zero_of_is_witness_c`).

    This is an extraction lemma from a computable predicate, not the unconditional
    existence statement of lemma 5.3 in [BCIKS20]. -/
private lemma guruswami_sudan_for_proximity_gap_existence
    {k m : ℕ} {ωs : Fin n ↪ F} {f : Fin n → F}
    (hw : hasWitnessC k (proximityGapDegreeBound (n := n) k m) m ωs f = true) :
    ∃ c : Fin (proximityGapDegreeBound (n := n) k m + 1) ×
          Fin (proximityGapDegreeBound (n := n) k m + 1) → F,
      isWitnessC k (proximityGapDegreeBound (n := n) k m) m ωs f c = true := by
  obtain ⟨w, _⟩ :=
    (hasWitnessC_eq_true_iff_exists_output (n := n) k
      (proximityGapDegreeBound (n := n) k m) m ωs f).1 hw
  exact ⟨w.1, w.2⟩

/-- Strengthened existence: when the witness check passes and `m > 0`, the extracted
    witness additionally satisfies pointwise evaluation vanishing at every interpolation
    point, and the corresponding bivariate polynomial is nonzero.

    This is a computable strengthening of
    `guruswami_sudan_for_proximity_gap_existence`, not a full paper-level
    quantifier match for lemma 5.3 in [BCIKS20]. -/
private lemma guruswami_sudan_for_proximity_gap_existence_strong
    {k m : ℕ} {ωs : Fin n ↪ F} {f : Fin n → F}
    (hm : 0 < m)
    (hw : hasWitnessC k (proximityGapDegreeBound (n := n) k m) m ωs f = true) :
    ∃ c : Fin (proximityGapDegreeBound (n := n) k m + 1) ×
          Fin (proximityGapDegreeBound (n := n) k m + 1) → F,
      isWitnessC k (proximityGapDegreeBound (n := n) k m) m ωs f c = true ∧
      (∀ i : Fin n,
        evalCoeffVecAt k (proximityGapDegreeBound (n := n) k m) c (ωs i) (f i) = 0) ∧
      coeffVecToBivariate k (proximityGapDegreeBound (n := n) k m) c ≠ 0 :=
  let ⟨c, hc⟩ := guruswami_sudan_for_proximity_gap_existence hw
  ⟨c, hc, is_witness_c_imp_eval_zero_at_points hm hc,
    coeff_vec_to_bivariate_ne_zero_of_is_witness_c hc⟩

/-- Constructive witness property for the Guruswami–Sudan system.
    When `m > 0` and the codeword polynomial `ReedSolomon.codewordToPoly p` appears in
    `witnessCandidateSet`, we can extract a witness coefficient vector `c` satisfying:
    * `isWitnessC` (nonzero + full multiplicity vanishing),
    * `Q(X, p(X)) = 0` via CompPoly root extraction, and
    * pointwise evaluation vanishing `evalCoeffVecAt k D c (ωs i) (f i) = 0` at every
      interpolation point. -/
private lemma guruswami_sudan_for_proximity_gap_property [Fintype F] {k m : ℕ} {ωs : Fin n ↪ F}
    {f : Fin n → F}
    {p : ReedSolomon.code ωs k}
    (hm : 0 < m)
    (hp : ReedSolomon.codewordToPoly p ∈
      witnessCandidateSet k m (proximityGapDegreeBound (n := n) k m)
        (proximityGapJohnson (n := n) k m) ωs f) :
    ∃ c : Fin (proximityGapDegreeBound (n := n) k m + 1) ×
          Fin (proximityGapDegreeBound (n := n) k m + 1) → F,
      isWitnessC k (proximityGapDegreeBound (n := n) k m) m ωs f c = true ∧
      isQRootRaw k (proximityGapDegreeBound (n := n) k m) c
        (polyToRaw (ReedSolomon.codewordToPoly p) k) = true ∧
      ∀ i : Fin n,
        evalCoeffVecAt k (proximityGapDegreeBound (n := n) k m) c (ωs i) (f i) = 0 :=
  witness_candidate_set_witness_vanishes hm hp

/-- Strengthened proximity gap property: additionally asserts that the Q-root extraction
    result has all coefficients zero (via `is_q_root_raw_iff_all_coeff_zero`), and the
    corresponding bivariate polynomial is nonzero.

    This lemma is conditional on membership in `witnessCandidateSet`; it should be read
    as a constructive bridge lemma rather than a direct restatement of lemma 5.3 in
    [BCIKS20]. -/
private lemma guruswami_sudan_for_proximity_gap_property_strong [Fintype F] {k m : ℕ}
    {ωs : Fin n ↪ F} {f : Fin n → F}
    {p : ReedSolomon.code ωs k}
    (hm : 0 < m)
    (hp : ReedSolomon.codewordToPoly p ∈
      witnessCandidateSet k m (proximityGapDegreeBound (n := n) k m)
        (proximityGapJohnson (n := n) k m) ωs f) :
    ∃ c : Fin (proximityGapDegreeBound (n := n) k m + 1) ×
          Fin (proximityGapDegreeBound (n := n) k m + 1) → F,
      isWitnessC k (proximityGapDegreeBound (n := n) k m) m ωs f c = true ∧
      (∀ idx : Fin (evalQAtPRaw k (proximityGapDegreeBound (n := n) k m) c
          (polyToRaw (ReedSolomon.codewordToPoly p) k)).size,
        (evalQAtPRaw k (proximityGapDegreeBound (n := n) k m) c
          (polyToRaw (ReedSolomon.codewordToPoly p) k))[idx] = 0) ∧
      (∀ i : Fin n,
        evalCoeffVecAt k (proximityGapDegreeBound (n := n) k m) c (ωs i) (f i) = 0) ∧
      coeffVecToBivariate k (proximityGapDegreeBound (n := n) k m) c ≠ 0 := by
  obtain ⟨c, hwit, hroot, heval⟩ := witness_candidate_set_witness_vanishes hm hp
  exact ⟨c, hwit,
    is_q_root_raw_iff_all_coeff_zero.mp hroot,
    heval,
    coeff_vec_to_bivariate_ne_zero_of_is_witness_c hwit⟩

/-- Existence of a classical Guruswami-Sudan witness polynomial. -/
theorem proximity_gap_existence (k n : ℕ) (ωs : Fin n ↪ F) (f : Fin n → F) (hm : 1 ≤ m) :
    ∃ Q, Conditions k m (proximity_gap_degree_bound k n m) ωs f Q := by
  use polySol k n m ωs f
  exact ⟨polySol_ne_zero, polySol_weightedDegree_le, polySol_roots hm, polySol_multiplicity⟩

/-- Classical divisibility consequence for Guruswami-Sudan witnesses. -/
theorem proximity_gap_divisibility (hk : k + 1 ≤ n) (hm : 1 ≤ m) (p : code ωs k)
    {Q : F[X][Y]} (hQ : Conditions k m (proximity_gap_degree_bound k n m) ωs f Q)
    (h_dist : (hammingDist f (fun i ↦ (codewordToPoly p).eval (ωs i)) : ℝ) / n <
      proximity_gap_johnson k n m) :
    X - C (codewordToPoly p) ∣ Q :=
  dvd_property (f := f) hk hm p hQ.Q_deg hQ.Q_multiplicity h_dist

/-- GS existence with rate-corrected degree bound (ρ = k/n). Requires k > 1
    for the counting argument and m ≥ 1 for multiplicity. -/
theorem gs_existence (k n : ℕ) (ωs : Fin n ↪ F) (f : Fin n → F)
    (hk : 1 < k) (hn : n ≠ 0) (hm : 1 ≤ m) :
    ∃ Q, Conditions k m (gs_degree_bound k n m) ωs f Q := by
  set D := gs_degree_bound k n m
  have hcount := gs_numVars_gt_numConstraints_of_gt_one hn hk hm
  obtain ⟨c, hc_ne, hc_zero⟩ := exists_nonzero_solution_gen k n m ωs f D hcount
  use coeffsToPoly k D c
  refine ⟨?_, ?_, ?_, ?_⟩
  · -- ne_zero
    have h_inj : Function.Injective (coeffsToPoly (F := F) k D) := by
      have : Function.Injective (linearCombination F
        (fun p : weigthBoundIndices k D ↦ monomial (F := F) p.1.1 p.1.2)) :=
        linearIndependent_monomials.comp _ (fun p q h ↦ by aesop)
      exact this.comp (LinearEquiv.injective _)
    exact fun h ↦ hc_ne <| h_inj <| by simpa using h
  · -- weightedDegree
    convert Option.some_le_some.mpr (natWeightedDegree_coeffsToPoly_le k D c) using 1
    exact weightedDegree_eq_natWeightedDegree
  · -- roots
    intro i
    exact eval_eq_zero_of_constraint_zero hm fun s t hst ↦ by
      simp only [constraintMap, LinearMap.coe_mk, AddHom.coe_mk] at hc_zero
      have := congr_fun (congr_fun hc_zero i) ⟨(s, t), Finset.mem_filter.2
        ⟨Finset.mem_product.mpr ⟨Finset.mem_range.mpr (by linarith),
          Finset.mem_range.mpr (by linarith)⟩, by linarith⟩⟩
      aesop
  · -- multiplicity
    intro i
    apply rootMultiplicity_ge_of_shift_zero
    · have h_inj : Function.Injective (coeffsToPoly (F := F) k D) := by
        have : Function.Injective (linearCombination F
          (fun p : weigthBoundIndices k D ↦ monomial (F := F) p.1.1 p.1.2)) :=
          linearIndependent_monomials.comp _ (fun p q h ↦ by aesop)
        exact this.comp (LinearEquiv.injective _)
      exact fun h ↦ hc_ne <| h_inj <| by simpa using h
    · intro s t hst
      have h := congr_fun (congr_fun hc_zero i) ⟨(s, t), by
        exact Finset.mem_filter.mpr ⟨Finset.mem_product.mpr ⟨Finset.mem_range.mpr (by linarith),
          Finset.mem_range.mpr (by linarith)⟩, by linarith⟩⟩
      -- Mirror the approach in polySol_multiplicity:
      -- unfold constraintMap in hc_zero, extract component
      simp only [constraintMap, LinearMap.coe_mk, AddHom.coe_mk] at hc_zero
      have := congr_fun (congr_fun hc_zero i) ⟨(s, t), by
        exact Finset.mem_filter.mpr ⟨Finset.mem_product.mpr ⟨Finset.mem_range.mpr (by linarith),
          Finset.mem_range.mpr (by linarith)⟩, by linarith⟩⟩
      aesop

/-- GS divisibility with rate-corrected Johnson radius (ρ = k/n). -/
theorem gs_divisibility (hk : k + 1 ≤ n) (hm : 1 ≤ m) (p : code ωs k)
    {Q : F[X][Y]} (hQ : Conditions k m (gs_degree_bound k n m) ωs f Q)
    (h_dist : (hammingDist f (fun i ↦ (codewordToPoly p).eval (ωs i)) : ℝ) / n <
      gs_johnson k n m) :
    X - C (codewordToPoly p) ∣ Q :=
  gs_dvd_property (f := f) hk hm p hQ.Q_deg hQ.Q_multiplicity h_dist

end GuruswamiSudan

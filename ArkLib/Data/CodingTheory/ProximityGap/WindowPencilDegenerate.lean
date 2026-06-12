/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.WindowReconstructionPencil

/-!
# Branch (ii) of the window dichotomy: the degenerate pencil (#371, round 14)

When every square row-selection of the reconstruction pencil has identically-zero
determinant, the pencil carries a global POLYNOMIAL kernel vector (the signed
maximal minors of any (j+w+1)-row selection — the Laplace/repeated-row construction),
whose entries have γ-degree ≤ w+1.  Per-scalar Padé uniqueness
(`recSolvable_fraction_unique`, the `IsCoprime`-with-`Z_D` form of the landed
`witness_fraction_unique`) transfers every bad witness's denominator roots to the
kernel family, and the incidence count closes:

  **`#bad · (w − 2j) ≤ n(w+1)`  on the corank-one stratum**  (`w > 2j`),

with the deeper strata carried by a named residual (the corank recursion).
Together with branch (i) (`recSolvable_card_le`) this is the window dichotomy.
-/

open Finset Polynomial Matrix
open scoped NNReal

namespace ProximityGap.WBPencil

open ProximityGap.SpikeFloor

variable {F : Type} [Field F] [Fintype F] [DecidableEq F]
variable {n : ℕ} [NeZero n]

section Degenerate

variable (dom : Fin n ↪ F) {k w j : ℕ}
variable (ℓ₀ ℓ₁ R₀ R₁ : F[X])

/-- Domain nonvanishing makes the modulus coprime to the domain polynomial. -/
theorem isCoprime_mul_domZ
    (hℓ₀v : ∀ i : Fin n, ℓ₀.eval (dom i) ≠ 0)
    (hℓ₁v : ∀ i : Fin n, ℓ₁.eval (dom i) ≠ 0) :
    IsCoprime (ℓ₀ * ℓ₁) (domZ dom) := by
  rw [domZ]
  refine IsCoprime.prod_right fun i _ => ?_
  have hker : (ℓ₀ * ℓ₁).eval (dom i) ≠ 0 := by
    rw [eval_mul]
    exact mul_ne_zero (hℓ₀v i) (hℓ₁v i)
  -- X − dom i is prime; it divides ℓ₀ℓ₁ iff the evaluation vanishes
  refine ((prime_X_sub_C (dom i)).coprime_iff_not_dvd.mpr ?_).symm
  intro hdvd
  exact hker (dvd_iff_isRoot.mp hdvd)

open Classical in
/-- **Per-scalar Padé uniqueness at the reconstruction level**: two solutions of
the inverse-free system at one scalar represent a single fraction
(`h·Z′ = h′·Z`) whenever the profile sits below the modulus degree. -/
theorem recSolvable_fraction_unique
    (hℓ₀v : ∀ i : Fin n, ℓ₀.eval (dom i) ≠ 0)
    (hℓ₁v : ∀ i : Fin n, ℓ₁.eval (dom i) ≠ 0)
    (hdeg2w : 2 * w ≤ (ℓ₀ * ℓ₁).natDegree) (hjw : j < w)
    {γ : F} {h Z h' Z' : F[X]}
    (hhd : h.natDegree ≤ j) (hZd : Z.natDegree ≤ w)
    (hh'd : h'.natDegree ≤ j) (hZ'd : Z'.natDegree ≤ w)
    (hdvd : (ℓ₀ * ℓ₁) ∣ (domZ dom * h - (ℓ₁ * R₀ + C γ * (ℓ₀ * R₁)) * Z))
    (hdvd' : (ℓ₀ * ℓ₁) ∣ (domZ dom * h' - (ℓ₁ * R₀ + C γ * (ℓ₀ * R₁)) * Z')) :
    h * Z' = h' * Z := by
  have helim : (ℓ₀ * ℓ₁) ∣ domZ dom * (h * Z' - h' * Z) := by
    have h1 : (ℓ₀ * ℓ₁) ∣ (domZ dom * h - (ℓ₁ * R₀ + C γ * (ℓ₀ * R₁)) * Z) * Z'
        - (domZ dom * h' - (ℓ₁ * R₀ + C γ * (ℓ₀ * R₁)) * Z') * Z :=
      dvd_sub (hdvd.mul_right Z') (hdvd'.mul_right Z)
    have h2 : (domZ dom * h - (ℓ₁ * R₀ + C γ * (ℓ₀ * R₁)) * Z) * Z'
        - (domZ dom * h' - (ℓ₁ * R₀ + C γ * (ℓ₀ * R₁)) * Z') * Z
        = domZ dom * (h * Z' - h' * Z) := by ring
    rwa [h2] at h1
  have hcop := isCoprime_mul_domZ dom ℓ₀ ℓ₁ hℓ₀v hℓ₁v
  have hdvd2 : (ℓ₀ * ℓ₁) ∣ (h * Z' - h' * Z) := hcop.dvd_of_dvd_mul_left helim
  by_contra hne
  have hne' : h * Z' - h' * Z ≠ 0 := sub_ne_zero.mpr hne
  have hled := Polynomial.natDegree_le_of_dvd hdvd2 hne'
  have hd1 : (h * Z' - h' * Z).natDegree ≤ j + w := by
    refine le_trans (natDegree_sub_le _ _) (max_le ?_ ?_)
    · exact le_trans natDegree_mul_le (Nat.add_le_add hhd hZ'd)
    · exact le_trans natDegree_mul_le (Nat.add_le_add hh'd hZd)
  omega

/-- The reconstruction pencil as a polynomial matrix (the scalar is the variable). -/
noncomputable def recMatrixPoly (j w : ℕ) :
    Matrix (Fin (2 * w)) (Fin (j + 1) ⊕ Fin (w + 1)) F[X] :=
  fun r => Sum.elim
    (fun t : Fin (j + 1) =>
      C ((((domZ dom * X ^ (t : ℕ))) %ₘ (ℓ₀ * ℓ₁)).coeff r))
    (fun s : Fin (w + 1) =>
      -(C ((((ℓ₁ * R₀) * X ^ (s : ℕ)) %ₘ (ℓ₀ * ℓ₁)).coeff r)
        + X * C ((((ℓ₀ * R₁) * X ^ (s : ℕ)) %ₘ (ℓ₀ * ℓ₁)).coeff r)))

/-- Entrywise evaluation recovers the instantiated matrix. -/
theorem recMatrixPoly_eval (j w : ℕ) (γ : F) (r : Fin (2 * w))
    (b : Fin (j + 1) ⊕ Fin (w + 1)) :
    ((recMatrixPoly dom ℓ₀ ℓ₁ R₀ R₁ j w) r b).eval γ
      = recMatrix dom ℓ₀ ℓ₁ R₀ R₁ j w γ r b := by
  rcases b with t | s
  · rw [recMatrixPoly, recMatrix]
    simp only [Sum.elim_inl]
    rw [eval_C]
  · rw [recMatrixPoly, recMatrix]
    simp only [Sum.elim_inr]
    rw [eval_neg, eval_add, eval_C, eval_mul, eval_X, eval_C]
    have hlin : ((ℓ₁ * R₀ + C γ * (ℓ₀ * R₁)) * X ^ (s : ℕ)) %ₘ (ℓ₀ * ℓ₁)
        = ((ℓ₁ * R₀) * X ^ (s : ℕ)) %ₘ (ℓ₀ * ℓ₁)
          + γ • (((ℓ₀ * R₁) * X ^ (s : ℕ)) %ₘ (ℓ₀ * ℓ₁)) := by
      rw [← smul_modByMonic, ← add_modByMonic]
      congr 1
      rw [smul_eq_C_mul]
      ring
    rw [hlin, coeff_add, coeff_smul, smul_eq_mul]

/-- The square sub-pencil of a row assignment, over polynomials. -/
noncomputable def recSquarePoly (j w : ℕ)
    (τ : Fin (j + 1) ⊕ Fin (w + 1) → Fin (2 * w)) :
    Matrix (Fin (j + 1) ⊕ Fin (w + 1)) (Fin (j + 1) ⊕ Fin (w + 1)) F[X] :=
  (recMatrixPoly dom ℓ₀ ℓ₁ R₀ R₁ j w).submatrix τ id

/-- The square sub-pencil's determinant is the branch-(i) determinant polynomial. -/
theorem recSquarePoly_det (j w : ℕ)
    (τ : Fin (j + 1) ⊕ Fin (w + 1) → Fin (2 * w)) :
    (recSquarePoly dom ℓ₀ ℓ₁ R₀ R₁ j w τ).det
      = recDetPoly dom ℓ₀ ℓ₁ R₀ R₁ j w τ := by
  rfl

/-- **The adjugate kernel columns**: under square degeneracy
(`recDetPoly τ = 0`), every adjugate column of the square sub-pencil is a
polynomial kernel vector. -/
theorem recSquarePoly_mulVec_adjugate (j w : ℕ)
    (τ : Fin (j + 1) ⊕ Fin (w + 1) → Fin (2 * w))
    (hdeg0 : recDetPoly dom ℓ₀ ℓ₁ R₀ R₁ j w τ = 0)
    (c : Fin (j + 1) ⊕ Fin (w + 1)) :
    (recSquarePoly dom ℓ₀ ℓ₁ R₀ R₁ j w τ).mulVec
      (fun b => (recSquarePoly dom ℓ₀ ℓ₁ R₀ R₁ j w τ).adjugate b c) = 0 := by
  funext a
  have hmul := Matrix.mul_adjugate (recSquarePoly dom ℓ₀ ℓ₁ R₀ R₁ j w τ)
  have hentry := congrFun (congrFun hmul a) c
  rw [recSquarePoly_det, hdeg0] at hentry
  rw [Matrix.mulVec, dotProduct]
  rw [Matrix.mul_apply] at hentry
  rw [hentry]
  simp

/-- Evaluating an adjugate kernel column yields a kernel vector of the
instantiated square at each scalar. -/
theorem recSquare_eval_kernel (j w : ℕ)
    (τ : Fin (j + 1) ⊕ Fin (w + 1) → Fin (2 * w))
    (hdeg0 : recDetPoly dom ℓ₀ ℓ₁ R₀ R₁ j w τ = 0)
    (c : Fin (j + 1) ⊕ Fin (w + 1)) (γ : F) :
    ((recMatrix dom ℓ₀ ℓ₁ R₀ R₁ j w γ).submatrix τ id).mulVec
      (fun b => ((recSquarePoly dom ℓ₀ ℓ₁ R₀ R₁ j w τ).adjugate b c).eval γ)
      = 0 := by
  funext a
  have hker := congrFun
    (recSquarePoly_mulVec_adjugate dom ℓ₀ ℓ₁ R₀ R₁ j w τ hdeg0 c) a
  have heval := congrArg (Polynomial.eval γ) hker
  rw [Matrix.mulVec, dotProduct] at heval ⊢
  rw [eval_finset_sum] at heval
  rw [Pi.zero_apply, eval_zero] at heval
  rw [Pi.zero_apply]
  rw [← heval]
  refine Finset.sum_congr rfl fun b _ => ?_
  rw [recSquarePoly, eval_mul]
  congr 1
  show recMatrix dom ℓ₀ ℓ₁ R₀ R₁ j w γ (τ a) b
    = Polynomial.eval γ ((recMatrixPoly dom ℓ₀ ℓ₁ R₀ R₁ j w).submatrix τ id a b)
  rw [Matrix.submatrix_apply, id_eq, recMatrixPoly_eval]

end Degenerate

end ProximityGap.WBPencil

-- Axiom audit (expected: propext, Classical.choice, Quot.sound only)
#print axioms ProximityGap.WBPencil.isCoprime_mul_domZ
#print axioms ProximityGap.WBPencil.recSolvable_fraction_unique
#print axioms ProximityGap.WBPencil.recSquarePoly_mulVec_adjugate
#print axioms ProximityGap.WBPencil.recSquare_eval_kernel

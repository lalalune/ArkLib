/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.WindowReconstructionPencil
import ArkLib.Data.CodingTheory.ProximityGap.WBPencilSubmatrix

/-!
# Branch (ii) of the window dichotomy: the degenerate pencil (#371, round 14)

When every square row-selection of the reconstruction pencil has identically-zero
determinant, every scalar has a nontrivial reconstruction-kernel vector; the
next, sharper step is to choose that vector polynomially in the scalar (the signed
maximal minors of any (j+w+1)-row selection — the Laplace/repeated-row construction),
with entries of γ-degree ≤ w+1.  Per-scalar Padé uniqueness
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

open Classical in
/-- **All maximal row-minors vanish ⇒ nonzero kernel.**  This is the
contrapositive form of `exists_invertible_row_submatrix`, stated in the form
needed by degenerate reconstruction pencils. -/
theorem exists_nonzero_kernel_of_forall_submatrix_det_zero {m : ℕ}
    {α : Type} [Fintype α] [DecidableEq α]
    (M : Matrix (Fin m) α F)
    (hdet : ∀ I : α → Fin m, (M.submatrix I id).det = 0) :
    ∃ v : α → F, v ≠ 0 ∧ M.mulVec v = 0 := by
  by_contra hnone
  have hinj : ∀ v, M.mulVec v = 0 → v = 0 := by
    intro v hv
    by_contra hv0
    exact hnone ⟨v, hv0, hv⟩
  obtain ⟨I, _hIinj, hI⟩ := exists_invertible_row_submatrix (F := F) M hinj
  exact hI (hdet I)

/-- The degenerate reconstruction branch: all maximal reconstruction minors are
identically zero as polynomials in the scalar. -/
def RecPencilDegenerate (j w : ℕ) : Prop :=
  ∀ I : Fin (j + 1) ⊕ Fin (w + 1) → Fin (2 * w),
    recDetPoly dom ℓ₀ ℓ₁ R₀ R₁ j w I = 0

open Classical in
/-- In the degenerate reconstruction branch, every scalar has a nontrivial
kernel vector for the instantiated reconstruction matrix. -/
theorem recMatrix_kernel_of_degenerate {j w : ℕ}
    (hmonic : (ℓ₀ * ℓ₁).Monic)
    (hdegenerate : RecPencilDegenerate dom ℓ₀ ℓ₁ R₀ R₁ j w) (γ : F) :
    ∃ v : Fin (j + 1) ⊕ Fin (w + 1) → F, v ≠ 0 ∧
      (recMatrix dom ℓ₀ ℓ₁ R₀ R₁ j w γ).mulVec v = 0 := by
  refine exists_nonzero_kernel_of_forall_submatrix_det_zero
    (F := F) (recMatrix dom ℓ₀ ℓ₁ R₀ R₁ j w γ) ?_
  intro I
  rw [← recDetPoly_eval dom ℓ₀ ℓ₁ R₀ R₁ j w hmonic I γ,
    hdegenerate I]
  simp

open Classical in
/-- **Reconstruction-pencil dichotomy.**  Either branch (i) gives the existing
`w+1` reconstruction-solvable scalar bound, or branch (ii) supplies a
nontrivial kernel vector for every scalar. -/
theorem recSolvable_card_le_or_kernel_family {j w : ℕ}
    (hw : 1 ≤ w) (hjw : j < 2 * w)
    (hmonic : (ℓ₀ * ℓ₁).Monic) (hdeg : (ℓ₀ * ℓ₁).natDegree = 2 * w) :
    ((Finset.univ.filter (fun γ : F =>
      RecSolvable dom ℓ₀ ℓ₁ R₀ R₁ j w γ)).card ≤ w + 1)
      ∨
    (∀ γ : F, ∃ v : Fin (j + 1) ⊕ Fin (w + 1) → F, v ≠ 0 ∧
      (recMatrix dom ℓ₀ ℓ₁ R₀ R₁ j w γ).mulVec v = 0) := by
  by_cases hminor :
      ∃ I : Fin (j + 1) ⊕ Fin (w + 1) → Fin (2 * w),
        recDetPoly dom ℓ₀ ℓ₁ R₀ R₁ j w I ≠ 0
  · obtain ⟨I, hI⟩ := hminor
    exact Or.inl
      (recSolvable_card_le dom ℓ₀ ℓ₁ R₀ R₁ hw hjw hmonic hdeg hI)
  · right
    have hdegenerate : RecPencilDegenerate dom ℓ₀ ℓ₁ R₀ R₁ j w := by
      intro I
      by_contra hI
      exact hminor ⟨I, hI⟩
    intro γ
    exact recMatrix_kernel_of_degenerate dom ℓ₀ ℓ₁ R₀ R₁ hmonic
      hdegenerate γ

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

end Degenerate

end ProximityGap.WBPencil

-- Axiom audit (expected: propext, Classical.choice, Quot.sound only)
#print axioms ProximityGap.WBPencil.exists_nonzero_kernel_of_forall_submatrix_det_zero
#print axioms ProximityGap.WBPencil.recMatrix_kernel_of_degenerate
#print axioms ProximityGap.WBPencil.recSolvable_card_le_or_kernel_family
#print axioms ProximityGap.WBPencil.isCoprime_mul_domZ
#print axioms ProximityGap.WBPencil.recSolvable_fraction_unique

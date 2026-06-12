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

/-- The singly-updated square sub-pencil: row `c₀` replaced by the `cs`-indicator
(the corank-one anchor, following the corank-two file's double-update pattern). -/
noncomputable def recSquareU (j w : ℕ)
    (τ : Fin (j + 1) ⊕ Fin (w + 1) → Fin (2 * w))
    (c₀ cs : Fin (j + 1) ⊕ Fin (w + 1)) :
    Matrix (Fin (j + 1) ⊕ Fin (w + 1)) (Fin (j + 1) ⊕ Fin (w + 1)) F[X] :=
  (recSquarePoly dom ℓ₀ ℓ₁ R₀ R₁ j w τ).updateRow c₀ (Pi.single cs 1)

open Classical in
/-- **The corank-one span**: wherever the updated determinant survives, every
kernel vector of the instantiated square is spanned by the single adjugate
column — `det(γ)·v = v_{cs} · K(γ)`. -/
theorem corank1_span (j w : ℕ)
    {τ : Fin (j + 1) ⊕ Fin (w + 1) → Fin (2 * w)}
    {c₀ cs : Fin (j + 1) ⊕ Fin (w + 1)} {γ : F}
    {v : Fin (j + 1) ⊕ Fin (w + 1) → F}
    (hv : ((recMatrix dom ℓ₀ ℓ₁ R₀ R₁ j w γ).submatrix τ id).mulVec v = 0)
    (hdet : ((recSquareU dom ℓ₀ ℓ₁ R₀ R₁ j w τ c₀ cs).det).eval γ ≠ 0) :
    ∀ b, ((recSquareU dom ℓ₀ ℓ₁ R₀ R₁ j w τ c₀ cs).det).eval γ * v b
      = v cs * ((recSquareU dom ℓ₀ ℓ₁ R₀ R₁ j w τ c₀ cs).adjugate b c₀).eval γ := by
  classical
  set B1 := recSquareU dom ℓ₀ ℓ₁ R₀ R₁ j w τ c₀ cs with hB1
  set Bev := B1.map (Polynomial.eval γ) with hBev
  have hadj : Bev.adjugate = (B1.adjugate).map (Polynomial.eval γ) := by
    have h := RingHom.map_adjugate (Polynomial.evalRingHom γ) B1
    rw [RingHom.mapMatrix_apply, RingHom.mapMatrix_apply] at h
    rw [hBev]
    exact h.symm
  have hdetev : Bev.det = (B1.det).eval γ := by
    rw [hBev, ← Polynomial.coe_evalRingHom, ← RingHom.mapMatrix_apply,
      ← RingHom.map_det]
  -- the evaluated updated matrix sends v to the c₀-indicator scaled by v cs
  have hBv : ∀ a, Bev a ⬝ᵥ v = (if a = c₀ then v cs else 0) := by
    intro a
    by_cases ha : a = c₀
    · subst ha
      rw [if_pos rfl, dotProduct]
      have hrow : ∀ b, Bev a b = (if b = cs then (1 : F) else 0) := by
        intro b
        rw [hBev, Matrix.map_apply, hB1, recSquareU, Matrix.updateRow_self]
        by_cases hb : b = cs
        · subst hb
          rw [Pi.single_eq_same]
          simp
        · rw [Pi.single_eq_of_ne hb]
          simp [hb]
      calc ∑ b, Bev a b * v b
          = ∑ b, (if b = cs then v b else 0) := by
            refine Finset.sum_congr rfl fun b _ => ?_
            rw [hrow b]
            by_cases hb : b = cs <;> simp [hb]
        _ = v cs := by
            rw [Finset.sum_ite_eq' Finset.univ cs v, if_pos (Finset.mem_univ cs)]
    · rw [if_neg ha, dotProduct]
      have hrow : ∀ b, Bev a b
          = (recMatrix dom ℓ₀ ℓ₁ R₀ R₁ j w γ).submatrix τ id a b := by
        intro b
        rw [hBev, Matrix.map_apply, hB1, recSquareU,
          Matrix.updateRow_ne ha]
        rw [recSquarePoly, Matrix.submatrix_apply, id_eq, recMatrixPoly_eval]
        rfl
      calc ∑ b, Bev a b * v b
          = ∑ b, (recMatrix dom ℓ₀ ℓ₁ R₀ R₁ j w γ).submatrix τ id a b * v b :=
            Finset.sum_congr rfl fun b _ => by rw [hrow b]
        _ = ((recMatrix dom ℓ₀ ℓ₁ R₀ R₁ j w γ).submatrix τ id).mulVec v a := rfl
        _ = 0 := by rw [hv]; rfl
  -- the adjugate column satisfies Bev · K = det · e_{c₀}
  have hBK : ∀ a, Bev a ⬝ᵥ (fun i => (B1.adjugate i c₀).eval γ)
      = Bev.det * (1 : Matrix (Fin (j + 1) ⊕ Fin (w + 1))
          (Fin (j + 1) ⊕ Fin (w + 1)) F) a c₀ := by
    intro a
    have hmul := congrFun (congrFun (Matrix.mul_adjugate Bev) a) c₀
    rw [Matrix.smul_apply, smul_eq_mul] at hmul
    rw [← hmul, Matrix.mul_apply]
    simp only [dotProduct]
    refine Finset.sum_congr rfl fun b _ => ?_
    rw [hadj, Matrix.map_apply]
  -- the difference vector dies
  set u' : Fin (j + 1) ⊕ Fin (w + 1) → F := fun b =>
    Bev.det * v b - v cs * (B1.adjugate b c₀).eval γ with hu'def
  have hBu' : Bev.mulVec u' = 0 := by
    funext a
    show Bev a ⬝ᵥ u' = 0
    have hsplit : Bev a ⬝ᵥ u' = Bev.det * (Bev a ⬝ᵥ v)
        - v cs * (Bev a ⬝ᵥ (fun i => (B1.adjugate i c₀).eval γ)) := by
      simp only [dotProduct, Finset.mul_sum, ← Finset.sum_sub_distrib]
      refine Finset.sum_congr rfl fun b _ => ?_
      rw [hu'def]
      ring
    rw [hsplit, hBv a, hBK a]
    by_cases ha : a = c₀
    · subst ha
      rw [if_pos rfl, Matrix.one_apply_eq]
      ring
    · rw [if_neg ha, Matrix.one_apply_ne ha]
      ring
  have hu'0 : u' = 0 := by
    by_contra hne
    have hdet0 : Bev.det = 0 :=
      (Matrix.exists_mulVec_eq_zero_iff).mp ⟨u', hne, hBu'⟩
    rw [hdetev] at hdet0
    exact hdet hdet0
  intro b
  have h := congrFun hu'0 b
  rw [hu'def] at h
  have h' : Bev.det * v b - v cs * (B1.adjugate b c₀).eval γ = 0 := h
  rw [hdetev] at h'
  linear_combination h'

/-- **The generic pencil-determinant degree bound**: any square matrix over the
column sum-type whose `inl`-column entries are constants and `inr`-column entries
have degree ≤ 1 has determinant degree ≤ `w + 1`. -/
theorem det_natDegree_le_of_column_weights {j w : ℕ}
    (M : Matrix (Fin (j + 1) ⊕ Fin (w + 1)) (Fin (j + 1) ⊕ Fin (w + 1)) F[X])
    (hM : ∀ a b, (M a b).natDegree
      ≤ Sum.elim (fun _ : Fin (j + 1) => 0) (fun _ : Fin (w + 1) => 1) b) :
    M.det.natDegree ≤ w + 1 := by
  classical
  rw [Matrix.det_apply]
  refine natDegree_sum_le_of_forall_le _ _ fun σ _ => ?_
  have hprod' : (∏ b : Fin (j + 1) ⊕ Fin (w + 1), M (σ b) b).natDegree ≤ w + 1 := by
    refine le_trans (natDegree_prod_le _ _) ?_
    calc ∑ b : Fin (j + 1) ⊕ Fin (w + 1), (M (σ b) b).natDegree
        ≤ ∑ b : Fin (j + 1) ⊕ Fin (w + 1),
            Sum.elim (fun _ : Fin (j + 1) => 0) (fun _ : Fin (w + 1) => 1) b :=
          Finset.sum_le_sum fun b _ => hM (σ b) b
      _ = w + 1 := by
          rw [Fintype.sum_sum_type]
          simp
  rcases Int.units_eq_one_or (Equiv.Perm.sign σ) with hsg | hsg
  · rw [hsg, one_smul]
    exact hprod'
  · rw [hsg]
    refine le_trans (le_of_eq ?_) hprod'
    rw [Units.neg_smul, one_smul, natDegree_neg]

/-- The entry-weight bound for the polynomial pencil. -/
theorem recMatrixPoly_entry_natDegree (j w : ℕ) (r : Fin (2 * w))
    (b : Fin (j + 1) ⊕ Fin (w + 1)) :
    ((recMatrixPoly dom ℓ₀ ℓ₁ R₀ R₁ j w) r b).natDegree
      ≤ Sum.elim (fun _ : Fin (j + 1) => 0) (fun _ : Fin (w + 1) => 1) b := by
  rcases b with t | s
  · simp only [recMatrixPoly, Sum.elim_inl, natDegree_C, le_refl]
  · simp only [recMatrixPoly, Sum.elim_inr, natDegree_neg]
    refine le_trans (natDegree_add_le _ _) (max_le ?_ ?_)
    · rw [natDegree_C]
      omega
    · refine le_trans natDegree_mul_le ?_
      rw [natDegree_X, natDegree_C]

/-- **Adjugate entries of the updated square have degree ≤ w + 1**: each is the
determinant of a doubly-updated pencil square whose entries keep the column
weights. -/
theorem recSquareU_adjugate_natDegree_le (j w : ℕ)
    (τ : Fin (j + 1) ⊕ Fin (w + 1) → Fin (2 * w))
    (c₀ cs b c : Fin (j + 1) ⊕ Fin (w + 1)) :
    ((recSquareU dom ℓ₀ ℓ₁ R₀ R₁ j w τ c₀ cs).adjugate b c).natDegree ≤ w + 1 := by
  rw [Matrix.adjugate_apply]
  have hsingle : ∀ (b'' b₂ : Fin (j + 1) ⊕ Fin (w + 1)),
      ((Pi.single b₂ 1 : (Fin (j + 1) ⊕ Fin (w + 1)) → F[X]) b'').natDegree = 0 := by
    intro b'' b₂
    by_cases h : b'' = b₂
    · subst h
      rw [Pi.single_eq_same]
      exact natDegree_one
    · rw [Pi.single_eq_of_ne h]
      exact natDegree_zero
  refine det_natDegree_le_of_column_weights _ fun a b' => ?_
  by_cases hac : a = c
  · subst hac
    rw [Matrix.updateRow_self, hsingle]
    exact Nat.zero_le _
  · rw [Matrix.updateRow_ne hac, recSquareU]
    by_cases hac₀ : a = c₀
    · subst hac₀
      rw [Matrix.updateRow_self, hsingle]
      exact Nat.zero_le _
    · rw [Matrix.updateRow_ne hac₀]
      rw [recSquarePoly, Matrix.submatrix_apply, id_eq]
      exact recMatrixPoly_entry_natDegree dom ℓ₀ ℓ₁ R₀ R₁ j w (τ a) b'

/-- The kernel-family polynomial at a domain point: the γ-polynomial whose roots
are the scalars at which the adjugate kernel's denominator vanishes there. -/
noncomputable def kernelFamilyAt (j w : ℕ)
    (τ : Fin (j + 1) ⊕ Fin (w + 1) → Fin (2 * w))
    (c₀ cs : Fin (j + 1) ⊕ Fin (w + 1)) (x : F) : F[X] :=
  ∑ s : Fin (w + 1),
    (recSquareU dom ℓ₀ ℓ₁ R₀ R₁ j w τ c₀ cs).adjugate (Sum.inr s) c₀
      * C (x ^ (s : ℕ))

theorem kernelFamilyAt_natDegree_le (j w : ℕ)
    (τ : Fin (j + 1) ⊕ Fin (w + 1) → Fin (2 * w))
    (c₀ cs : Fin (j + 1) ⊕ Fin (w + 1)) (x : F) :
    (kernelFamilyAt dom ℓ₀ ℓ₁ R₀ R₁ j w τ c₀ cs x).natDegree ≤ w + 1 := by
  rw [kernelFamilyAt]
  refine natDegree_sum_le_of_forall_le _ _ fun s _ => ?_
  calc ((recSquareU dom ℓ₀ ℓ₁ R₀ R₁ j w τ c₀ cs).adjugate (Sum.inr s) c₀
        * C (x ^ (s : ℕ))).natDegree
      ≤ ((recSquareU dom ℓ₀ ℓ₁ R₀ R₁ j w τ c₀ cs).adjugate (Sum.inr s) c₀).natDegree
        + (C (x ^ (s : ℕ)) : F[X]).natDegree := natDegree_mul_le
    _ ≤ (w + 1) + 0 := Nat.add_le_add
        (recSquareU_adjugate_natDegree_le dom ℓ₀ ℓ₁ R₀ R₁ j w τ c₀ cs _ _)
        (le_of_eq (natDegree_C _))
    _ = w + 1 := by omega

open Classical in
/-- **P3: THE DEGENERATE-BRANCH INCIDENCE COUNT.**  Under square degeneracy with a
surviving update and no blind domain points, the bad scalars satisfy

`#bad · (n − (2w+k−1)) ≤ (w+1) · (n − (2w+k−1)) + n · (w+1)`.

(The factor `n − (2w+k−1)` is `w − j`; at every below-UDR stratum this puts
`#bad ≤ (w+1) + n(w+1)/(w−j)` — production-silent.) -/
theorem window_degenerate_count (hk : 1 ≤ k)
    (hℓ₀d : ℓ₀.natDegree ≤ w) (hℓ₁d : ℓ₁.natDegree ≤ w)
    (hR₀d : R₀.natDegree ≤ w + k - 1) (hR₁d : R₁.natDegree ≤ w + k - 1)
    (hℓ₀v : ∀ i : Fin n, ℓ₀.eval (dom i) ≠ 0)
    (hℓ₁v : ∀ i : Fin n, ℓ₁.eval (dom i) ≠ 0)
    (hcop : IsCoprime ℓ₀ ℓ₁) (hgen₀ : ¬ ℓ₀ ∣ R₀)
    (hmonic : (ℓ₀ * ℓ₁).Monic)
    {δ : ℝ≥0} (hδn : δ * (Fintype.card (Fin n) : ℝ≥0) ≤ w)
    (hj : 2 * w + k - 1 - (n - w) ≤ j)
    {τ : Fin (j + 1) ⊕ Fin (w + 1) → Fin (2 * w)}
    (hτ0 : recDetPoly dom ℓ₀ ℓ₁ R₀ R₁ j w τ = 0)
    {c₀ cs : Fin (j + 1) ⊕ Fin (w + 1)}
    (hU : (recSquareU dom ℓ₀ ℓ₁ R₀ R₁ j w τ c₀ cs).det ≠ 0)
    (hNB : ∀ i : Fin n,
      kernelFamilyAt dom ℓ₀ ℓ₁ R₀ R₁ j w τ c₀ cs (dom i)
        ≠ 0) :
    (Finset.univ.filter (fun γ : F => mcaEvent (F := F)
      ((rsCode dom k : Submodule F (Fin n → F)) : Set (Fin n → F)) δ
      (fun i => R₀.eval (dom i) / ℓ₀.eval (dom i))
      (fun i => R₁.eval (dom i) / ℓ₁.eval (dom i)) γ)).card
        * (n - (2 * w + k - 1))
      ≤ (w + 1) * (n - (2 * w + k - 1)) + n * (w + 1) := by
  set Γ : Finset F := Finset.univ.filter (fun γ : F => mcaEvent (F := F)
      ((rsCode dom k : Submodule F (Fin n → F)) : Set (Fin n → F)) δ
      (fun i => R₀.eval (dom i) / ℓ₀.eval (dom i))
      (fun i => R₁.eval (dom i) / ℓ₁.eval (dom i)) γ) with hΓ
  set detU : F[X] :=
    (recSquareU dom ℓ₀ ℓ₁ R₀ R₁ j w τ c₀ cs).det with hdetU
  have hdetUne : detU ≠ 0 := hU
  have hNB' : ∀ i : Fin n,
      kernelFamilyAt dom ℓ₀ ℓ₁ R₀ R₁ j w τ c₀ cs (dom i) ≠ 0 := hNB
  -- split: scalars where the update dies vs survives
  set Γ₀ : Finset F := Γ.filter (fun γ => detU.eval γ = 0) with hΓ₀
  set Γ₁ : Finset F := Γ.filter (fun γ => detU.eval γ ≠ 0) with hΓ₁
  have hsplit : Γ.card ≤ Γ₀.card + Γ₁.card := by
    have h := Finset.filter_card_add_filter_neg_card_eq_card
      (s := Γ) (p := fun γ => detU.eval γ = 0)
    rw [← hΓ₀] at h
    have h2 : (Γ.filter fun γ => ¬ detU.eval γ = 0) = Γ₁ := by
      rw [hΓ₁]
    rw [h2] at h
    omega
  -- Γ₀: roots of the update determinant
  have hΓ₀card : Γ₀.card ≤ w + 1 := by
    have hdetUdeg : detU.natDegree ≤ w + 1 := by
      rw [hdetU, recSquareU]
      refine det_natDegree_le_of_column_weights _ fun a b => ?_
      by_cases hac : a = c₀
      · subst hac
        rw [Matrix.updateRow_self]
        have : ((Pi.single cs 1 :
            (Fin (j + 1) ⊕ Fin (w + 1)) → F[X]) b).natDegree = 0 := by
          by_cases h : b = cs
          · subst h; rw [Pi.single_eq_same]; exact natDegree_one
          · rw [Pi.single_eq_of_ne h]; exact natDegree_zero
        rw [this]
        exact Nat.zero_le _
      · rw [Matrix.updateRow_ne hac, recSquarePoly, Matrix.submatrix_apply, id_eq]
        exact recMatrixPoly_entry_natDegree dom ℓ₀ ℓ₁ R₀ R₁ j w (τ a) b
    calc Γ₀.card ≤ detU.roots.toFinset.card := by
          refine Finset.card_le_card ?_
          intro γ hγ
          rw [hΓ₀, Finset.mem_filter] at hγ
          rw [Multiset.mem_toFinset, mem_roots hdetUne]
          exact hγ.2
      _ ≤ detU.roots.card := detU.roots.toFinset_card_le
      _ ≤ detU.natDegree := detU.card_roots'
      _ ≤ w + 1 := hdetUdeg
  -- Γ₁: the incidence count through the kernel family
  -- per bad γ in Γ₁: the witness missing set T_γ has ≥ n−(2w+k−1) points, each
  -- rooting the kernel family's γ-polynomial at γ
  have hkey : ∀ γ ∈ Γ₁, ∃ T : Finset (Fin n),
      n - (2 * w + k - 1) ≤ T.card ∧
      ∀ i ∈ T, (kernelFamilyAt dom ℓ₀ ℓ₁ R₀ R₁ j w τ c₀ cs (dom i)).eval γ = 0 := by
    intro γ hγ
    rw [hΓ₁, Finset.mem_filter] at hγ
    obtain ⟨hγΓ, hdetγ⟩ := hγ
    rw [hΓ, Finset.mem_filter] at hγΓ
    obtain ⟨S, h, P, hScard, hPd, hdeg, hid⟩ := mcaEvent_factored dom hk
      hℓ₀d hℓ₁d hR₀d hR₁d hℓ₀v hℓ₁v hcop hgen₀ hδn hγΓ.2
    set T : Finset (Fin n) := Finset.univ \ S with hT
    set ZT : F[X] := T.prod fun i => X - C (dom i) with hZT
    -- |T| ≥ n − (2w+k−1)
    have hTcard : n - (2 * w + k - 1) ≤ T.card := by
      have hScard' : S.card ≤ 2 * w + k - 1 := by omega
      have hSn : S.card ≤ n := by
        have := Finset.card_le_card (Finset.subset_univ S)
        rwa [Finset.card_univ, Fintype.card_fin] at this
      have : T.card = n - S.card := by
        rw [hT, Finset.card_sdiff, Finset.card_univ, Finset.inter_univ,
          Fintype.card_fin]
      omega
    refine ⟨T, hTcard, fun i hiT => ?_⟩
    -- the witness kernel vector
    set u : Fin (j + 1) ⊕ Fin (w + 1) → F :=
      Sum.elim (fun t => h.coeff t) (fun s => ZT.coeff s) with hu
    have hrecH : recH (j := j) (w := w) u = h := by
      rw [recH]
      conv_rhs => rw [h.as_sum_range' (j + 1) (by omega)]
      rw [Finset.sum_range]
      exact Finset.sum_congr rfl fun t _ => by
        rw [hu, Sum.elim_inl, C_mul_X_pow_eq_monomial]
    have hZTdeg : ZT.natDegree = T.card := by
      rw [hZT, natDegree_prod _ _ (fun i _ => X_sub_C_ne_zero (dom i))]
      simp [natDegree_X_sub_C]
    have hTw : T.card ≤ w := by
      have : T.card = n - S.card := by
        rw [hT, Finset.card_sdiff, Finset.card_univ, Finset.inter_univ,
          Fintype.card_fin]
      omega
    have hrecZ : recZ (j := j) (w := w) u = ZT := by
      rw [recZ]
      conv_rhs => rw [ZT.as_sum_range' (w + 1) (by omega)]
      rw [Finset.sum_range]
      exact Finset.sum_congr rfl fun s _ => by
        rw [hu, Sum.elim_inr, C_mul_X_pow_eq_monomial]
    -- u is in the kernel of the instantiated square
    have hudvd : (ℓ₀ * ℓ₁) ∣ (domZ dom * h
        - (ℓ₁ * R₀ + C γ * (ℓ₀ * R₁)) * ZT) := by
      have hpart : ZT * (S.prod fun i => X - C (dom i)) = domZ dom := by
        rw [hZT, hT, domZ]
        exact Finset.prod_sdiff (Finset.subset_univ S)
      refine ⟨-(ZT * P), ?_⟩
      calc domZ dom * h - (ℓ₁ * R₀ + C γ * (ℓ₀ * R₁)) * ZT
          = ZT * ((S.prod fun i => X - C (dom i)) * h)
            - (ℓ₁ * R₀ + C γ * (ℓ₀ * R₁)) * ZT := by
            rw [← hpart]; ring
        _ = ZT * (ℓ₁ * R₀ + C γ * (ℓ₀ * R₁) - P * (ℓ₀ * ℓ₁))
            - (ℓ₁ * R₀ + C γ * (ℓ₀ * R₁)) * ZT := by rw [hid]
        _ = ℓ₀ * ℓ₁ * -(ZT * P) := by ring
    have hker : (recMatrix dom ℓ₀ ℓ₁ R₀ R₁ j w γ).mulVec u = 0 := by
      funext r
      rw [recMatrix_mulVec dom ℓ₀ ℓ₁ R₀ R₁ j w γ hmonic, hrecH, hrecZ]
      rw [(modByMonic_eq_zero_iff_dvd hmonic).mpr hudvd]
      simp
    have hkerSq : ((recMatrix dom ℓ₀ ℓ₁ R₀ R₁ j w γ).submatrix τ id).mulVec u
        = 0 := by
      funext a
      have hsub : ((recMatrix dom ℓ₀ ℓ₁ R₀ R₁ j w γ).submatrix τ id).mulVec u a
          = (recMatrix dom ℓ₀ ℓ₁ R₀ R₁ j w γ).mulVec u (τ a) := by
        rw [Matrix.mulVec, Matrix.mulVec, dotProduct, dotProduct]
        rfl
      rw [hsub, hker]
      rfl
    -- the span
    have hspan := corank1_span dom ℓ₀ ℓ₁ R₀ R₁ j w
      (τ := τ) (c₀ := c₀) (cs := cs) hkerSq hdetγ
    -- u cs ≠ 0 (else u = 0 against ZT ≠ 0)
    have hZTne : ZT ≠ 0 := by
      rw [hZT]
      exact (monic_prod_of_monic _ _ (fun i _ => monic_X_sub_C (dom i))).ne_zero
    have hucs : u cs ≠ 0 := by
      intro h0
      apply hZTne
      rw [← hrecZ, recZ]
      have hall : ∀ b, u b = 0 := by
        intro b
        have := hspan b
        rw [h0, zero_mul] at this
        exact (mul_eq_zero.mp this).resolve_left hdetγ
      refine Finset.sum_eq_zero fun s _ => ?_
      rw [hall (Sum.inr s)]
      simp
    -- the incidence at i ∈ T
    have hZTi : ZT.eval (dom i) = 0 := by
      rw [hZT]
      rw [eval_prod]
      refine Finset.prod_eq_zero hiT ?_
      rw [eval_sub, eval_X, eval_C, sub_self]
    -- detU(γ) · ZT(x) = u cs · family(x)(γ)
    have hcomb : detU.eval γ * ZT.eval (dom i)
        = u cs * (kernelFamilyAt dom ℓ₀ ℓ₁ R₀ R₁ j w τ c₀ cs (dom i)).eval γ := by
      rw [← hrecZ, recZ, eval_finset_sum, Finset.mul_sum]
      rw [kernelFamilyAt, eval_finset_sum, Finset.mul_sum]
      refine Finset.sum_congr rfl fun s _ => ?_
      rw [eval_mul, eval_C, eval_pow, eval_X, eval_mul, eval_C]
      have := hspan (Sum.inr s)
      calc detU.eval γ * (u (Sum.inr s) * (dom i) ^ (s : ℕ))
          = (detU.eval γ * u (Sum.inr s)) * (dom i) ^ (s : ℕ) := by ring
        _ = (u cs * ((recSquareU dom ℓ₀ ℓ₁ R₀ R₁ j w τ c₀ cs).adjugate
              (Sum.inr s) c₀).eval γ) * (dom i) ^ (s : ℕ) := by rw [this]
        _ = u cs * (((recSquareU dom ℓ₀ ℓ₁ R₀ R₁ j w τ c₀ cs).adjugate
              (Sum.inr s) c₀).eval γ * (dom i) ^ (s : ℕ)) := by ring
    rw [hZTi, mul_zero] at hcomb
    exact ((mul_eq_zero.mp hcomb.symm).resolve_left hucs)
  -- count the incidences
  choose! Tf hTfcard hTfroot using hkey
  have hΓ₁count : Γ₁.card * (n - (2 * w + k - 1)) ≤ n * (w + 1) := by
    have hincid : ∀ i : Fin n,
        (Γ₁.filter (fun γ => i ∈ Tf γ)).card ≤ w + 1 := by
      intro i
      calc (Γ₁.filter (fun γ => i ∈ Tf γ)).card
          ≤ ((kernelFamilyAt dom ℓ₀ ℓ₁ R₀ R₁ j w τ c₀ cs
              (dom i)).roots.toFinset).card := by
            refine Finset.card_le_card ?_
            intro γ hγ
            rw [Finset.mem_filter] at hγ
            rw [Multiset.mem_toFinset, mem_roots (hNB' i)]
            exact hTfroot γ hγ.1 i hγ.2
        _ ≤ (kernelFamilyAt dom ℓ₀ ℓ₁ R₀ R₁ j w τ c₀ cs (dom i)).roots.card :=
            Multiset.toFinset_card_le _
        _ ≤ (kernelFamilyAt dom ℓ₀ ℓ₁ R₀ R₁ j w τ c₀ cs (dom i)).natDegree :=
            Polynomial.card_roots' _
        _ ≤ w + 1 := kernelFamilyAt_natDegree_le dom ℓ₀ ℓ₁ R₀ R₁ j w τ c₀ cs _
    calc Γ₁.card * (n - (2 * w + k - 1))
        = ∑ _γ ∈ Γ₁, (n - (2 * w + k - 1)) := by
          rw [Finset.sum_const, smul_eq_mul, mul_comm]
      _ ≤ ∑ γ ∈ Γ₁, (Tf γ).card :=
          Finset.sum_le_sum fun γ hγ => hTfcard γ hγ
      _ = ∑ γ ∈ Γ₁, ∑ i : Fin n, (if i ∈ Tf γ then 1 else 0) := by
          refine Finset.sum_congr rfl fun γ _ => ?_
          rw [Finset.sum_ite_mem, Finset.univ_inter, Finset.card_eq_sum_ones]
      _ = ∑ i : Fin n, ∑ γ ∈ Γ₁, (if i ∈ Tf γ then 1 else 0) :=
          Finset.sum_comm
      _ = ∑ i : Fin n, (Γ₁.filter (fun γ => i ∈ Tf γ)).card := by
          refine Finset.sum_congr rfl fun i _ => ?_
          rw [Finset.card_filter]
      _ ≤ ∑ _i : Fin n, (w + 1) :=
          Finset.sum_le_sum fun i _ => hincid i
      _ = n * (w + 1) := by
          rw [Finset.sum_const, smul_eq_mul, Finset.card_univ, Fintype.card_fin]
  calc Γ.card * (n - (2 * w + k - 1))
      ≤ (Γ₀.card + Γ₁.card) * (n - (2 * w + k - 1)) :=
        Nat.mul_le_mul_right _ hsplit
    _ = Γ₀.card * (n - (2 * w + k - 1))
        + Γ₁.card * (n - (2 * w + k - 1)) := by ring
    _ ≤ (w + 1) * (n - (2 * w + k - 1)) + n * (w + 1) :=
        Nat.add_le_add (Nat.mul_le_mul_right _ hΓ₀card) hΓ₁count
#print axioms ProximityGap.WBPencil.isCoprime_mul_domZ
#print axioms ProximityGap.WBPencil.recSolvable_fraction_unique
#print axioms ProximityGap.WBPencil.recSquarePoly_mulVec_adjugate
#print axioms ProximityGap.WBPencil.recSquare_eval_kernel
#print axioms ProximityGap.WBPencil.corank1_span
#print axioms ProximityGap.WBPencil.det_natDegree_le_of_column_weights
#print axioms ProximityGap.WBPencil.recSquareU_adjugate_natDegree_le
#print axioms ProximityGap.WBPencil.window_degenerate_count

/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.WBPencilWindowLaw

/-!
# WB-5: the corank-2 count — pairwise coincidence cracks the multi-parameter wall (#371)

One slice above the boundary (`n = 2w+k−1`) the window pencil has generic corank
2 and the WB-4 anchor provably dies (`windowPencil_adjugate_eq_zero_of_lt_boundary`).
This file proves the corank-2 counting law with the SAME adjugate/updateRow
toolkit, one level deeper:

* the **double-update anchor**: `B₂ := B.updateRow c₀ (single cs 1) |>.updateRow
  c₀' (single cs' 1)` with `det B₂ ≢ 0` — its two adjugate columns `K¹, K²`
  (γ-polynomial entries, degree ≤ w+1) SPAN every evaluated kernel where the
  determinant survives: `det(γ)·v = v_{cs}·K¹(γ) + v_{cs'}·K²(γ)`;
* a bad scalar with error set `E` (`|E| ≥ 2`) forces, for every pair `i ≠ j ∈ E`,
  the **pair-coincidence polynomial** `g_{ij} := G¹_i·G²_j − G¹_j·G²_i`
  (degree ≤ 2w+2; `Gᵇ_i` = the locator block of `Kᵇ` evaluated at `x_i`) to
  vanish at `γ` — eliminating the two kernel parameters pairwise converts the
  multi-parameter split-incidence problem into univariate root counting;
* small-error-set scalars (`|E| ≤ 1`) share witness sets of size ≥ n−1, of which
  there are only n+1: the in-tree rigidity (`unique_bad_gamma_common_witness`)
  caps the class at n+1.

**`badScalars_card_le_of_corank2`**: under the double anchor and twin-freeness
(`g_{ij} ≠ 0` for all `i ≠ j` — the named residual; the twin classes are where
the normalizer/Möbius alignment families live),

  `#bad ≤ (w+1) + (n+1) + n²·(2w+2)`.

Probe record (`probe_wb_corank2_coincidence.py`, `probe_wb_corank2_qscaling.py`):
generic corank exactly 2 at the slice (222/222); the coincidence necessary
condition has 0 violations at q = 449; max bad saturates at exactly `C(n,2)` —
inside this budget.  Applies at EVERY radius `δ ≤ w/n` (no slice hypothesis) —
in particular it also covers the corank-2 (class-V) part of `UnanchoredLinear`.
-/

open Finset Polynomial Matrix
open scoped NNReal ENNReal ProbabilityTheory

set_option linter.unusedSectionVars false

namespace ProximityGap.WBPencil

open ProximityGap.SpikeFloor

variable {F : Type} [Field F] [Fintype F] [DecidableEq F]
variable {n : ℕ} [NeZero n]

/-- The doubly-updated square selection: rows `c₀, c₀'` replaced by coordinate
singletons. -/
noncomputable def pencilSqDU (dom : Fin n ↪ F) (k w : ℕ) (ℓ₀ R₀ ℓ₁ R₁ : F[X])
    (J : WCol n k w → Fin (3 * w + k)) (c₀ c₀' cs cs' : WCol n k w) :
    Matrix (WCol n k w) (WCol n k w) F[X] :=
  (((windowPencil dom k w ℓ₀ R₀ ℓ₁ R₁).submatrix J id).updateRow c₀
    (Pi.single cs 1)).updateRow c₀' (Pi.single cs' 1)

/-- The two Cramer kernel candidates: adjugate columns `c₀` and `c₀'`. -/
noncomputable def pencilK (dom : Fin n ↪ F) (k w : ℕ) (ℓ₀ R₀ ℓ₁ R₁ : F[X])
    (J : WCol n k w → Fin (3 * w + k)) (c₀ c₀' cs cs' : WCol n k w)
    (col : WCol n k w) : WCol n k w → F[X] :=
  fun i => (pencilSqDU dom k w ℓ₀ R₀ ℓ₁ R₁ J c₀ c₀' cs cs').adjugate i col

/-- The locator-block evaluation polynomials of an adjugate column. -/
noncomputable def pencilG (dom : Fin n ↪ F) (k w : ℕ) (ℓ₀ R₀ ℓ₁ R₁ : F[X])
    (J : WCol n k w → Fin (3 * w + k)) (c₀ c₀' cs cs' col : WCol n k w)
    (i : Fin n) : F[X] :=
  ∑ t : Fin (w + 1),
    pencilK dom k w ℓ₀ R₀ ℓ₁ R₁ J c₀ c₀' cs cs' col (Sum.inl t) * C ((dom i) ^ (t : ℕ))

/-- The pair-coincidence polynomial of a domain pair. -/
noncomputable def coincPoly (dom : Fin n ↪ F) (k w : ℕ) (ℓ₀ R₀ ℓ₁ R₁ : F[X])
    (J : WCol n k w → Fin (3 * w + k)) (c₀ c₀' cs cs' : WCol n k w)
    (i j : Fin n) : F[X] :=
  pencilG dom k w ℓ₀ R₀ ℓ₁ R₁ J c₀ c₀' cs cs' c₀ i
      * pencilG dom k w ℓ₀ R₀ ℓ₁ R₁ J c₀ c₀' cs cs' c₀' j
    - pencilG dom k w ℓ₀ R₀ ℓ₁ R₁ J c₀ c₀' cs cs' c₀ j
      * pencilG dom k w ℓ₀ R₀ ℓ₁ R₁ J c₀ c₀' cs cs' c₀' i

/-! ## Degree bounds -/

theorem pencilSqDU_natDegree_le (dom : Fin n ↪ F) (k w : ℕ) (ℓ₀ R₀ ℓ₁ R₁ : F[X])
    (J : WCol n k w → Fin (3 * w + k)) (c₀ c₀' cs cs' : WCol n k w)
    (a b : WCol n k w) :
    ((pencilSqDU dom k w ℓ₀ R₀ ℓ₁ R₁ J c₀ c₀' cs cs') a b).natDegree
      ≤ Sum.elim (fun _ : Fin (w + 1) => 1)
          (Sum.elim (fun _ : Fin (w + k) => 0) (fun _ : Fin (3 * w + k - n) => 0)) b := by
  rw [pencilSqDU, Matrix.updateRow_apply, Matrix.updateRow_apply]
  by_cases ha' : a = c₀'
  · rw [if_pos ha']
    by_cases hb : b = cs'
    · rw [Pi.single_apply, if_pos hb]
      rcases b with t | s | m <;> simp
    · rw [Pi.single_apply, if_neg hb]
      rcases b with t | s | m <;> simp
  · rw [if_neg ha']
    by_cases ha : a = c₀
    · rw [if_pos ha]
      by_cases hb : b = cs
      · rw [Pi.single_apply, if_pos hb]
        rcases b with t | s | m <;> simp
      · rw [Pi.single_apply, if_neg hb]
        rcases b with t | s | m <;> simp
    · rw [if_neg ha]
      exact windowPencil_natDegree_le dom k w ℓ₀ R₀ ℓ₁ R₁ (J a) b

theorem pencilSqDU_det_natDegree_le (dom : Fin n ↪ F) (k w : ℕ)
    (ℓ₀ R₀ ℓ₁ R₁ : F[X]) (J : WCol n k w → Fin (3 * w + k))
    (c₀ c₀' cs cs' : WCol n k w) :
    (pencilSqDU dom k w ℓ₀ R₀ ℓ₁ R₁ J c₀ c₀' cs cs').det.natDegree ≤ w + 1 := by
  refine le_trans (natDegree_det_le_sum_colBound _
    (Sum.elim (fun _ : Fin (w + 1) => 1)
      (Sum.elim (fun _ : Fin (w + k) => 0) (fun _ : Fin (3 * w + k - n) => 0)))
    (pencilSqDU_natDegree_le dom k w ℓ₀ R₀ ℓ₁ R₁ J c₀ c₀' cs cs'))
    (le_of_eq (windowPencil_colBound_sum n k w))

theorem pencilK_natDegree_le (dom : Fin n ↪ F) (k w : ℕ) (ℓ₀ R₀ ℓ₁ R₁ : F[X])
    (J : WCol n k w → Fin (3 * w + k)) (c₀ c₀' cs cs' col i : WCol n k w) :
    (pencilK dom k w ℓ₀ R₀ ℓ₁ R₁ J c₀ c₀' cs cs' col i).natDegree ≤ w + 1 := by
  classical
  rw [pencilK, Matrix.adjugate_apply]
  refine le_trans (natDegree_det_le_sum_colBound _
    (Sum.elim (fun _ : Fin (w + 1) => 1)
      (Sum.elim (fun _ : Fin (w + k) => 0) (fun _ : Fin (3 * w + k - n) => 0))) ?_)
    (le_of_eq (windowPencil_colBound_sum n k w))
  intro a b
  rw [Matrix.updateRow_apply]
  by_cases ha : a = col
  · rw [if_pos ha]
    by_cases hb : b = i
    · rw [Pi.single_apply, if_pos hb]
      rcases b with t | s | m <;> simp
    · rw [Pi.single_apply, if_neg hb]
      rcases b with t | s | m <;> simp
  · rw [if_neg ha]
    exact pencilSqDU_natDegree_le dom k w ℓ₀ R₀ ℓ₁ R₁ J c₀ c₀' cs cs' a b

theorem pencilG_natDegree_le (dom : Fin n ↪ F) (k w : ℕ) (ℓ₀ R₀ ℓ₁ R₁ : F[X])
    (J : WCol n k w → Fin (3 * w + k)) (c₀ c₀' cs cs' col : WCol n k w) (i : Fin n) :
    (pencilG dom k w ℓ₀ R₀ ℓ₁ R₁ J c₀ c₀' cs cs' col i).natDegree ≤ w + 1 := by
  refine natDegree_sum_le_of_forall_le _ _ fun t _ => ?_
  calc (pencilK dom k w ℓ₀ R₀ ℓ₁ R₁ J c₀ c₀' cs cs' col (Sum.inl t)
        * C ((dom i) ^ (t : ℕ))).natDegree
      ≤ (pencilK dom k w ℓ₀ R₀ ℓ₁ R₁ J c₀ c₀' cs cs' col (Sum.inl t)).natDegree
        + (C ((dom i) ^ (t : ℕ)) : F[X]).natDegree := natDegree_mul_le
    _ ≤ (w + 1) + 0 := Nat.add_le_add
        (pencilK_natDegree_le dom k w ℓ₀ R₀ ℓ₁ R₁ J c₀ c₀' cs cs' col _)
        (le_of_eq (natDegree_C _))
    _ = w + 1 := by omega

theorem coincPoly_natDegree_le (dom : Fin n ↪ F) (k w : ℕ) (ℓ₀ R₀ ℓ₁ R₁ : F[X])
    (J : WCol n k w → Fin (3 * w + k)) (c₀ c₀' cs cs' : WCol n k w) (i j : Fin n) :
    (coincPoly dom k w ℓ₀ R₀ ℓ₁ R₁ J c₀ c₀' cs cs' i j).natDegree ≤ 2 * w + 2 := by
  rw [coincPoly]
  refine le_trans (natDegree_sub_le _ _) (max_le ?_ ?_) <;>
  · refine le_trans natDegree_mul_le ?_
    have h1 := pencilG_natDegree_le dom k w ℓ₀ R₀ ℓ₁ R₁ J c₀ c₀' cs cs'
    calc _ ≤ (w + 1) + (w + 1) := Nat.add_le_add (h1 _ _) (h1 _ _)
      _ = 2 * w + 2 := by omega

/-! ## The span lemma -/

/-- **The corank-2 span**: wherever the double-update determinant survives, every
evaluated kernel vector of the full pencil is the explicit combination of the two
adjugate columns: `det(γ)·v = v_{cs}·K¹(γ) + v_{cs'}·K²(γ)`. -/
theorem corank2_span (dom : Fin n ↪ F) {k w : ℕ} {ℓ₀ R₀ ℓ₁ R₁ : F[X]}
    {J : WCol n k w → Fin (3 * w + k)} {c₀ c₀' cs cs' : WCol n k w}
    (hcc : c₀ ≠ c₀') {γ : F}
    {v : WCol n k w → F}
    (hv : ((windowPencil dom k w ℓ₀ R₀ ℓ₁ R₁).map (Polynomial.eval γ)).mulVec v = 0)
    (hdet : ((pencilSqDU dom k w ℓ₀ R₀ ℓ₁ R₁ J c₀ c₀' cs cs').det).eval γ ≠ 0) :
    ∀ b, ((pencilSqDU dom k w ℓ₀ R₀ ℓ₁ R₁ J c₀ c₀' cs cs').det).eval γ * v b
      = v cs * (pencilK dom k w ℓ₀ R₀ ℓ₁ R₁ J c₀ c₀' cs cs' c₀ b).eval γ
        + v cs' * (pencilK dom k w ℓ₀ R₀ ℓ₁ R₁ J c₀ c₀' cs cs' c₀' b).eval γ := by
  classical
  set B2 := pencilSqDU dom k w ℓ₀ R₀ ℓ₁ R₁ J c₀ c₀' cs cs' with hB2def
  set Bev := B2.map (Polynomial.eval γ) with hBevdef
  -- the evaluated determinant and adjugate
  have hadj : Bev.adjugate = (B2.adjugate).map (Polynomial.eval γ) := by
    have h := RingHom.map_adjugate (Polynomial.evalRingHom γ) B2
    rw [RingHom.mapMatrix_apply, RingHom.mapMatrix_apply] at h
    rw [hBevdef]
    exact h.symm
  have hdetev : Bev.det = (B2.det).eval γ := by
    rw [hBevdef, ← Polynomial.coe_evalRingHom, ← RingHom.mapMatrix_apply,
      ← RingHom.map_det]
  -- B₂(γ) · v = v_{cs}·e_{c₀} + v_{cs'}·e_{c₀'}
  have hBv : ∀ a, Bev a ⬝ᵥ v
      = (if a = c₀' then v cs' else if a = c₀ then v cs else 0) := by
    intro a
    by_cases ha' : a = c₀'
    · subst ha'
      have hrow : Bev a = Pi.single cs' 1 := by
        rw [hBevdef, hB2def, pencilSqDU]
        funext b
        rw [Matrix.map_apply, Matrix.updateRow_self]
        by_cases hb : b = cs'
        · subst hb
          rw [Pi.single_eq_same, Pi.single_eq_same]
          simp
        · rw [Pi.single_eq_of_ne hb, Pi.single_eq_of_ne hb]
          simp
      rw [hrow, single_dotProduct, one_mul, if_pos rfl]
    · by_cases ha : a = c₀
      · subst ha
        have hrow : Bev a = Pi.single cs 1 := by
          rw [hBevdef, hB2def, pencilSqDU]
          funext b
          rw [Matrix.map_apply, Matrix.updateRow_ne ha', Matrix.updateRow_self]
          by_cases hb : b = cs
          · subst hb
            rw [Pi.single_eq_same, Pi.single_eq_same]
            simp
          · rw [Pi.single_eq_of_ne hb, Pi.single_eq_of_ne hb]
            simp
        rw [hrow, single_dotProduct, one_mul, if_neg ha', if_pos rfl]
      · have hrow : Bev a = fun b =>
            ((windowPencil dom k w ℓ₀ R₀ ℓ₁ R₁).map (Polynomial.eval γ)) (J a) b := by
          rw [hBevdef, hB2def, pencilSqDU]
          funext b
          rw [Matrix.map_apply, Matrix.updateRow_ne ha', Matrix.updateRow_ne ha,
            Matrix.submatrix_apply, Matrix.map_apply]
          rfl
        rw [hrow, if_neg ha', if_neg ha]
        have := congrFun hv (J a)
        simpa [Matrix.mulVec, dotProduct] using this
  -- the two adjugate columns
  have hBK : ∀ (col : WCol n k w) a, Bev a ⬝ᵥ (fun i => (B2.adjugate i col).eval γ)
      = Bev.det * (1 : Matrix (WCol n k w) (WCol n k w) F) a col := by
    intro col a
    have hmul := congrFun (congrFun (Matrix.mul_adjugate Bev) a) col
    rw [Matrix.smul_apply, smul_eq_mul] at hmul
    rw [← hmul, Matrix.mul_apply]
    simp only [dotProduct]
    refine Finset.sum_congr rfl fun b _ => ?_
    rw [hadj, Matrix.map_apply]
  -- the cross combination dies
  set u' : WCol n k w → F := fun b => Bev.det * v b
    - v cs * (B2.adjugate b c₀).eval γ - v cs' * (B2.adjugate b c₀').eval γ
    with hu'def
  have hu'app : ∀ b, u' b = Bev.det * v b
      - v cs * (B2.adjugate b c₀).eval γ - v cs' * (B2.adjugate b c₀').eval γ :=
    fun b => by rw [hu'def]
  have hBu' : Bev.mulVec u' = 0 := by
    funext a
    show Bev a ⬝ᵥ u' = 0
    have hsplit : Bev a ⬝ᵥ u' = Bev.det * (Bev a ⬝ᵥ v)
        - v cs * (Bev a ⬝ᵥ (fun i => (B2.adjugate i c₀).eval γ))
        - v cs' * (Bev a ⬝ᵥ (fun i => (B2.adjugate i c₀').eval γ)) := by
      simp only [dotProduct, Finset.mul_sum, ← Finset.sum_sub_distrib]
      refine Finset.sum_congr rfl fun b _ => ?_
      rw [hu'app b]
      ring
    rw [hsplit, hBv a, hBK c₀ a, hBK c₀' a]
    by_cases ha' : a = c₀'
    · subst ha'
      rw [if_pos rfl, Matrix.one_apply_ne hcc.symm, Matrix.one_apply_eq]
      ring
    · by_cases ha : a = c₀
      · subst ha
        rw [if_neg ha', if_pos rfl, Matrix.one_apply_eq, Matrix.one_apply_ne hcc]
        ring
      · rw [if_neg ha', if_neg ha, Matrix.one_apply_ne ha, Matrix.one_apply_ne ha']
        ring
  have hu'0 : u' = 0 := by
    by_contra hne
    have hdet0 : Bev.det = 0 := (Matrix.exists_mulVec_eq_zero_iff).mp ⟨u', hne, hBu'⟩
    rw [hdetev] at hdet0
    exact hdet hdet0
  intro b
  have h := congrFun hu'0 b
  rw [hu'app b] at h
  have h' : Bev.det * v b - v cs * (B2.adjugate b c₀).eval γ
      - v cs' * (B2.adjugate b c₀').eval γ = 0 := h
  rw [hdetev] at h'
  have : (B2.det).eval γ * v b = v cs * (B2.adjugate b c₀).eval γ
      + v cs' * (B2.adjugate b c₀').eval γ := by linear_combination h'
  exact this

end ProximityGap.WBPencil

-- Axiom audit (expected: propext, Classical.choice, Quot.sound only)
#print axioms ProximityGap.WBPencil.corank2_span
#print axioms ProximityGap.WBPencil.pencilSqDU_det_natDegree_le
#print axioms ProximityGap.WBPencil.coincPoly_natDegree_le

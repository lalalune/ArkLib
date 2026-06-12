/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.WBPencilWindowLaw

/-!
# WB-6: the graded pencil ladder — one count theorem for every corank level (#371)

The uniform generalization of WB-4 (`c = 1`) and WB-5 (`c = 2`): replace any SET
`C₀` of rows of a square pencil selection by coordinate singletons (`a ↦
Pi.single (τ a) 1`), in ONE definition — no iterated `updateRow`.  The `|C₀|`
adjugate columns indexed by `C₀` span every evaluated kernel wherever the
determinant survives:

  `det(γ)·v = ∑_{col ∈ C₀} v_{τ(col)} · K^{col}(γ)`     (`graded_span`)

and a bad scalar whose error set has `≥ c := |C₀|` points kills the `c × c`
minor of the locator-evaluation matrix on every `c`-subset `T` of its error set
— the **graded coincidence polynomial** `gradedCoinc T` (degree ≤ `c(w+1)`).

**`badScalars_card_le_of_graded`**: under the graded anchor (`det ≢ 0`) and
`c`-twin-freeness (`gradedCoinc T ≢ 0` for every `c`-subset `T`),

  `#bad ≤ (w+1) + (∑_{j<c} C(n, n−j)) + C(n,c)·c(w+1)`

— polynomial in `n` for every fixed grade `c`, at EVERY radius `δ ≤ w/n`.

**Termination of the ladder**: replacing ALL rows (`C₀ = univ`, `τ = id`) gives
the identity matrix — determinant `1 ≠ 0` — so every stack is anchored at SOME
grade; the minimal grade is (one more than) the pencil corank, which grows by
one per slice above the boundary.  The graded ladder therefore yields a poly(n)
count at every fixed number of slices past UDR, with the residual at each grade
exactly `c`-twin-freeness — and the wall is `c ~ εn`: the deep window interior,
i.e. the recognized four-face open core, now approached by a graded formal
ladder.  Probe record: `probe_wb_corank2_coincidence.py` (grade 2 exact),
`probe_wb_boundary_slice_anchor.py` (grade 1 at the boundary).
-/

open Finset Polynomial Matrix
open scoped NNReal ENNReal ProbabilityTheory

set_option linter.unusedSectionVars false

namespace ProximityGap.WBPencil

open ProximityGap.SpikeFloor

variable {F : Type} [Field F] [Fintype F] [DecidableEq F]
variable {n : ℕ} [NeZero n]

/-- The graded square selection: rows in `C₀` replaced by coordinate singletons. -/
noncomputable def pencilSqG (dom : Fin n ↪ F) (k w : ℕ) (ℓ₀ R₀ ℓ₁ R₁ : F[X])
    (J : WCol n k w → Fin (3 * w + k)) (C₀ : Finset (WCol n k w))
    (τ : WCol n k w → WCol n k w) : Matrix (WCol n k w) (WCol n k w) F[X] :=
  fun a => if a ∈ C₀ then Pi.single (τ a) 1
    else ((windowPencil dom k w ℓ₀ R₀ ℓ₁ R₁).submatrix J id) a

/-- The graded locator-evaluation polynomials. -/
noncomputable def pencilGG (dom : Fin n ↪ F) (k w : ℕ) (ℓ₀ R₀ ℓ₁ R₁ : F[X])
    (J : WCol n k w → Fin (3 * w + k)) (C₀ : Finset (WCol n k w))
    (τ : WCol n k w → WCol n k w) (col : WCol n k w) (i : Fin n) : F[X] :=
  ∑ t : Fin (w + 1),
    (pencilSqG dom k w ℓ₀ R₀ ℓ₁ R₁ J C₀ τ).adjugate (Sum.inl t) col
      * C ((dom i) ^ (t : ℕ))

/-! ## Degree bounds -/

theorem pencilSqG_natDegree_le (dom : Fin n ↪ F) (k w : ℕ) (ℓ₀ R₀ ℓ₁ R₁ : F[X])
    (J : WCol n k w → Fin (3 * w + k)) (C₀ : Finset (WCol n k w))
    (τ : WCol n k w → WCol n k w) (a b : WCol n k w) :
    ((pencilSqG dom k w ℓ₀ R₀ ℓ₁ R₁ J C₀ τ) a b).natDegree
      ≤ Sum.elim (fun _ : Fin (w + 1) => 1)
          (Sum.elim (fun _ : Fin (w + k) => 0) (fun _ : Fin (3 * w + k - n) => 0)) b := by
  rw [pencilSqG]
  by_cases ha : a ∈ C₀
  · rw [if_pos ha]
    by_cases hb : b = τ a
    · rw [Pi.single_apply, if_pos hb]
      rcases b with t | s | m <;> simp
    · rw [Pi.single_apply, if_neg hb]
      rcases b with t | s | m <;> simp
  · rw [if_neg ha]
    exact windowPencil_natDegree_le dom k w ℓ₀ R₀ ℓ₁ R₁ (J a) b

theorem pencilSqG_det_natDegree_le (dom : Fin n ↪ F) (k w : ℕ)
    (ℓ₀ R₀ ℓ₁ R₁ : F[X]) (J : WCol n k w → Fin (3 * w + k))
    (C₀ : Finset (WCol n k w)) (τ : WCol n k w → WCol n k w) :
    (pencilSqG dom k w ℓ₀ R₀ ℓ₁ R₁ J C₀ τ).det.natDegree ≤ w + 1 :=
  le_trans (natDegree_det_le_sum_colBound _
    (Sum.elim (fun _ : Fin (w + 1) => 1)
      (Sum.elim (fun _ : Fin (w + k) => 0) (fun _ : Fin (3 * w + k - n) => 0)))
    (pencilSqG_natDegree_le dom k w ℓ₀ R₀ ℓ₁ R₁ J C₀ τ))
    (le_of_eq (windowPencil_colBound_sum n k w))

theorem pencilSqG_adjugate_natDegree_le (dom : Fin n ↪ F) (k w : ℕ)
    (ℓ₀ R₀ ℓ₁ R₁ : F[X]) (J : WCol n k w → Fin (3 * w + k))
    (C₀ : Finset (WCol n k w)) (τ : WCol n k w → WCol n k w)
    (i col : WCol n k w) :
    ((pencilSqG dom k w ℓ₀ R₀ ℓ₁ R₁ J C₀ τ).adjugate i col).natDegree ≤ w + 1 := by
  classical
  rw [Matrix.adjugate_apply]
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
    exact pencilSqG_natDegree_le dom k w ℓ₀ R₀ ℓ₁ R₁ J C₀ τ a b

theorem pencilGG_natDegree_le (dom : Fin n ↪ F) (k w : ℕ) (ℓ₀ R₀ ℓ₁ R₁ : F[X])
    (J : WCol n k w → Fin (3 * w + k)) (C₀ : Finset (WCol n k w))
    (τ : WCol n k w → WCol n k w) (col : WCol n k w) (i : Fin n) :
    (pencilGG dom k w ℓ₀ R₀ ℓ₁ R₁ J C₀ τ col i).natDegree ≤ w + 1 := by
  refine natDegree_sum_le_of_forall_le _ _ fun t _ => ?_
  calc ((pencilSqG dom k w ℓ₀ R₀ ℓ₁ R₁ J C₀ τ).adjugate (Sum.inl t) col
        * C ((dom i) ^ (t : ℕ))).natDegree
      ≤ ((pencilSqG dom k w ℓ₀ R₀ ℓ₁ R₁ J C₀ τ).adjugate (Sum.inl t) col).natDegree
        + (C ((dom i) ^ (t : ℕ)) : F[X]).natDegree := natDegree_mul_le
    _ ≤ (w + 1) + 0 := Nat.add_le_add
        (pencilSqG_adjugate_natDegree_le dom k w ℓ₀ R₀ ℓ₁ R₁ J C₀ τ _ col)
        (le_of_eq (natDegree_C _))
    _ = w + 1 := by omega

/-! ## The graded span -/

/-- **The graded span**: wherever the determinant of the graded selection
survives, every evaluated kernel vector of the full pencil is the explicit
combination of the `C₀`-indexed adjugate columns. -/
theorem graded_span (dom : Fin n ↪ F) {k w : ℕ} {ℓ₀ R₀ ℓ₁ R₁ : F[X]}
    {J : WCol n k w → Fin (3 * w + k)} {C₀ : Finset (WCol n k w)}
    {τ : WCol n k w → WCol n k w} {γ : F}
    {v : WCol n k w → F}
    (hv : ((windowPencil dom k w ℓ₀ R₀ ℓ₁ R₁).map (Polynomial.eval γ)).mulVec v = 0)
    (hdet : ((pencilSqG dom k w ℓ₀ R₀ ℓ₁ R₁ J C₀ τ).det).eval γ ≠ 0) :
    ∀ b, ((pencilSqG dom k w ℓ₀ R₀ ℓ₁ R₁ J C₀ τ).det).eval γ * v b
      = ∑ col ∈ C₀, v (τ col)
          * ((pencilSqG dom k w ℓ₀ R₀ ℓ₁ R₁ J C₀ τ).adjugate b col).eval γ := by
  classical
  set BG := pencilSqG dom k w ℓ₀ R₀ ℓ₁ R₁ J C₀ τ with hBGdef
  set Bev := BG.map (Polynomial.eval γ) with hBevdef
  have hadj : Bev.adjugate = (BG.adjugate).map (Polynomial.eval γ) := by
    have h := RingHom.map_adjugate (Polynomial.evalRingHom γ) BG
    rw [RingHom.mapMatrix_apply, RingHom.mapMatrix_apply] at h
    rw [hBevdef]
    exact h.symm
  have hdetev : Bev.det = (BG.det).eval γ := by
    rw [hBevdef, ← Polynomial.coe_evalRingHom, ← RingHom.mapMatrix_apply,
      ← RingHom.map_det]
  -- the rows of the evaluated graded selection
  have hBv : ∀ a, Bev a ⬝ᵥ v = (if a ∈ C₀ then v (τ a) else 0) := by
    intro a
    by_cases ha : a ∈ C₀
    · have hrow : Bev a = Pi.single (τ a) 1 := by
        funext b
        rw [hBevdef, Matrix.map_apply, hBGdef, pencilSqG]
        rw [if_pos ha]
        by_cases hb : b = τ a
        · subst hb
          rw [Pi.single_eq_same, Pi.single_eq_same]
          simp
        · rw [Pi.single_eq_of_ne hb, Pi.single_eq_of_ne hb]
          simp
      rw [hrow, single_dotProduct, one_mul, if_pos ha]
    · have hrow : Bev a = fun b =>
          ((windowPencil dom k w ℓ₀ R₀ ℓ₁ R₁).map (Polynomial.eval γ)) (J a) b := by
        funext b
        rw [hBevdef, Matrix.map_apply, hBGdef, pencilSqG, if_neg ha,
          Matrix.submatrix_apply, Matrix.map_apply]
        rfl
      rw [hrow, if_neg ha]
      have := congrFun hv (J a)
      simpa [Matrix.mulVec, dotProduct] using this
  have hBK : ∀ (col : WCol n k w) a,
      Bev a ⬝ᵥ (fun i => (BG.adjugate i col).eval γ)
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
    - ∑ col ∈ C₀, v (τ col) * (BG.adjugate b col).eval γ with hu'def
  have hu'app : ∀ b, u' b = Bev.det * v b
      - ∑ col ∈ C₀, v (τ col) * (BG.adjugate b col).eval γ := fun b => by rw [hu'def]
  have hBu' : Bev.mulVec u' = 0 := by
    funext a
    show Bev a ⬝ᵥ u' = 0
    have hsplit : Bev a ⬝ᵥ u' = Bev.det * (Bev a ⬝ᵥ v)
        - ∑ col ∈ C₀, v (τ col)
            * (Bev a ⬝ᵥ (fun i => (BG.adjugate i col).eval γ)) := by
      simp only [dotProduct]
      calc ∑ b, Bev a b * u' b
          = ∑ b, (Bev.det * (Bev a b * v b)
              - ∑ col ∈ C₀, v (τ col)
                  * (Bev a b * (BG.adjugate b col).eval γ)) := by
            refine Finset.sum_congr rfl fun b _ => ?_
            rw [hu'app b, mul_sub, Finset.mul_sum]
            congr 1
            · ring
            · refine Finset.sum_congr rfl fun col _ => ?_
              ring
        _ = Bev.det * ∑ b, Bev a b * v b
            - ∑ b, ∑ col ∈ C₀, v (τ col)
                * (Bev a b * (BG.adjugate b col).eval γ) := by
            rw [Finset.sum_sub_distrib, Finset.mul_sum]
        _ = Bev.det * ∑ b, Bev a b * v b
            - ∑ col ∈ C₀, v (τ col)
                * ∑ b, Bev a b * (BG.adjugate b col).eval γ := by
            congr 1
            rw [Finset.sum_comm]
            refine Finset.sum_congr rfl fun col _ => ?_
            rw [Finset.mul_sum]
    rw [hsplit, hBv a]
    have hsum : ∑ col ∈ C₀, v (τ col)
        * (Bev a ⬝ᵥ (fun i => (BG.adjugate i col).eval γ))
        = ∑ col ∈ C₀, v (τ col)
            * (Bev.det * (1 : Matrix (WCol n k w) (WCol n k w) F) a col) := by
      refine Finset.sum_congr rfl fun col _ => ?_
      rw [hBK col a]
    rw [hsum]
    by_cases ha : a ∈ C₀
    · rw [if_pos ha]
      have hcollapse : ∑ col ∈ C₀, v (τ col)
          * (Bev.det * (1 : Matrix (WCol n k w) (WCol n k w) F) a col)
          = v (τ a) * Bev.det := by
        rw [Finset.sum_eq_single a (fun col _ hne => by
            rw [Matrix.one_apply_ne (Ne.symm hne)]
            ring)
          (fun hnotmem => absurd ha hnotmem)]
        rw [Matrix.one_apply_eq]
        ring
      rw [hcollapse]
      ring
    · rw [if_neg ha]
      have hzero : ∑ col ∈ C₀, v (τ col)
          * (Bev.det * (1 : Matrix (WCol n k w) (WCol n k w) F) a col) = 0 :=
        Finset.sum_eq_zero fun col hcol => by
          have hne : a ≠ col := fun h => ha (h ▸ hcol)
          rw [Matrix.one_apply_ne hne]
          ring
      rw [hzero]
      ring
  have hu'0 : u' = 0 := by
    by_contra hne
    have hdet0 : Bev.det = 0 := (Matrix.exists_mulVec_eq_zero_iff).mp ⟨u', hne, hBu'⟩
    rw [hdetev] at hdet0
    exact hdet hdet0
  intro b
  have h := congrFun hu'0 b
  rw [hu'app b] at h
  have h' : Bev.det * v b
      - ∑ col ∈ C₀, v (τ col) * (BG.adjugate b col).eval γ = 0 := h
  rw [hdetev] at h'
  exact sub_eq_zero.mp h'

end ProximityGap.WBPencil

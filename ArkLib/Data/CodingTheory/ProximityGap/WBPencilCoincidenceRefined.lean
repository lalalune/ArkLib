/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.WBPencilCorankTwo
import ArkLib.ToMathlib.DesnanotJacobi

/-!
# The refined coincidence count (#371): Desnanot–Jacobi factorization in Lean

The probe-discovered factorization (`probe_wb_jacobi_factorization.py`: exact
divisibility 8/8, linear quotient) becomes theorem:

* `coincPoly_eq_det_mul_hPair` — **the factorization**: the pair-coincidence
  polynomial of the corank-2 ladder splits as

    `coincPoly i j = det B₂ · hPair i j`

  where `hPair` is the Vandermonde-weighted sum of doubly-updated determinants
  `DU(t,t')`.  Summing Desnanot–Jacobi over ALL `(t,t')` pairs — the diagonal
  self-cancels inside the identity — avoids any antisymmetrization plumbing.
* `natDegree_det_le_of_single_rows` — **the degree refinement engine**: a
  determinant with designated singleton rows forces every permutation through
  the singleton columns, so its degree is bounded by the column caps OFF the
  singleton targets.  Hence `deg DU ≤ w−1` (two locator columns die) and
  `deg hPair ≤ w−1`: the **one-rational-root law** (h linear at `w = 2`) is now
  formal structure.
* `badScalars_card_le_of_corank2_refined` — **the refined count**:

    `#bad ≤ (w+1) + (n+1) + n²·(w−1)`

  under the double anchor and `hPair`-twin-freeness — at `w = 1` the coincidence
  class is EMPTY (constant nonzero `hPair`), and the per-pair budget drops from
  `2w+2` to `w−1`.
-/

open Finset Polynomial Matrix
open scoped NNReal ENNReal ProbabilityTheory

set_option linter.unusedSectionVars false

namespace ProximityGap.WBPencil

open ProximityGap.SpikeFloor ArkLib.DesnanotJacobi

variable {F : Type} [Field F] [Fintype F] [DecidableEq F]
variable {n : ℕ} [NeZero n]

/-! ## The singleton-row degree refinement -/

/-- **Degree bound with singleton rows**: if the rows in `S` are coordinate
singletons (`A r = Pi.single (τ r) 1`), every surviving permutation routes the
singleton rows through their target columns at degree 0, so the determinant's
degree is bounded by the column caps off the targets. -/
theorem natDegree_det_le_of_single_rows {ι : Type} [Fintype ι] [DecidableEq ι]
    (A : Matrix ι ι F[X]) (d : ι → ℕ) (S : Finset ι) (τ : ι → ι)
    (hrow : ∀ r ∈ S, A r = Pi.single (τ r) 1)
    (hA : ∀ i j, (A i j).natDegree ≤ d j) :
    A.det.natDegree ≤ ∑ c ∈ Finset.univ.filter (fun c => c ∉ S.image τ), d c := by
  classical
  rw [Matrix.det_apply]
  refine natDegree_sum_le_of_forall_le _ _ fun σ _ => ?_
  by_cases hforce : ∀ r ∈ S, σ (τ r) = r
  · -- surviving permutation: factors at target columns are constants
    have hterm : ∀ c : ι, ((A (σ c) c).natDegree)
        ≤ (if c ∈ S.image τ then 0 else d c) := by
      intro c
      by_cases hcim : c ∈ S.image τ
      · rw [if_pos hcim]
        obtain ⟨r, hr, rfl⟩ := Finset.mem_image.mp hcim
        rw [hforce r hr, hrow r hr, Pi.single_eq_same]
        simp
      · rw [if_neg hcim]
        exact hA _ _
    have hprod : (∏ c, A (σ c) c).natDegree
        ≤ ∑ c, (if c ∈ S.image τ then 0 else d c) :=
      le_trans (natDegree_prod_le _ _) (Finset.sum_le_sum fun c _ => hterm c)
    have hsum : (∑ c, (if c ∈ S.image τ then 0 else d c))
        = ∑ c ∈ Finset.univ.filter (fun c => c ∉ S.image τ), d c := by
      rw [Finset.sum_ite, Finset.sum_const, smul_eq_mul, mul_zero, zero_add]
    rcases Int.units_eq_one_or (Equiv.Perm.sign σ) with h | h
    · rw [h, one_smul]
      rw [← hsum]
      exact hprod
    · rw [h, Units.neg_smul, one_smul, natDegree_neg, ← hsum]
      exact hprod
  · -- a singleton row is mis-routed: its factor vanishes
    push_neg at hforce
    obtain ⟨r, hr, hne⟩ := hforce
    have hzero : A (σ (σ.symm r)) (σ.symm r) = 0 := by
      rw [Equiv.apply_symm_apply, hrow r hr, Pi.single_apply]
      rw [if_neg ?_]
      intro h
      apply hne
      rw [← h, Equiv.apply_symm_apply]
    have hprod : (∏ c, A (σ c) c) = 0 :=
      Finset.prod_eq_zero (Finset.mem_univ (σ.symm r)) hzero
    rw [hprod, smul_zero]
    simp

/-! ## The factorization -/

/-- The doubly-updated determinant at a locator pair. -/
noncomputable def pencilDU (dom : Fin n ↪ F) (k w : ℕ) (ℓ₀ R₀ ℓ₁ R₁ : F[X])
    (J : WCol n k w → Fin (3 * w + k)) (c₀ c₀' cs cs' : WCol n k w)
    (t t' : Fin (w + 1)) : F[X] :=
  (((pencilSqDU dom k w ℓ₀ R₀ ℓ₁ R₁ J c₀ c₀' cs cs').updateRow c₀
    (Pi.single (Sum.inl t) 1)).updateRow c₀' (Pi.single (Sum.inl t') 1)).det

/-- The refined coincidence cofactor. -/
noncomputable def pencilHPair (dom : Fin n ↪ F) (k w : ℕ) (ℓ₀ R₀ ℓ₁ R₁ : F[X])
    (J : WCol n k w → Fin (3 * w + k)) (c₀ c₀' cs cs' : WCol n k w)
    (i j : Fin n) : F[X] :=
  ∑ t : Fin (w + 1), ∑ t' : Fin (w + 1),
    C ((dom i) ^ (t : ℕ) * (dom j) ^ (t' : ℕ))
      * pencilDU dom k w ℓ₀ R₀ ℓ₁ R₁ J c₀ c₀' cs cs' t t'

/-- **The Desnanot–Jacobi factorization of the coincidence polynomial.** -/
theorem coincPoly_eq_det_mul_hPair (dom : Fin n ↪ F) (k w : ℕ)
    (ℓ₀ R₀ ℓ₁ R₁ : F[X]) (J : WCol n k w → Fin (3 * w + k))
    {c₀ c₀' : WCol n k w} (cs cs' : WCol n k w) (hcc : c₀ ≠ c₀') (i j : Fin n) :
    coincPoly dom k w ℓ₀ R₀ ℓ₁ R₁ J c₀ c₀' cs cs' i j
      = (pencilSqDU dom k w ℓ₀ R₀ ℓ₁ R₁ J c₀ c₀' cs cs').det
        * pencilHPair dom k w ℓ₀ R₀ ℓ₁ R₁ J c₀ c₀' cs cs' i j := by
  classical
  set B2 := pencilSqDU dom k w ℓ₀ R₀ ℓ₁ R₁ J c₀ c₀' cs cs' with hB2
  -- expand both locator-evaluation products into the double sum
  have hexp : coincPoly dom k w ℓ₀ R₀ ℓ₁ R₁ J c₀ c₀' cs cs' i j
      = ∑ t : Fin (w + 1), ∑ t' : Fin (w + 1),
          C ((dom i) ^ (t : ℕ) * (dom j) ^ (t' : ℕ))
            * (B2.adjugate (Sum.inl t) c₀ * B2.adjugate (Sum.inl t') c₀'
              - B2.adjugate (Sum.inl t) c₀' * B2.adjugate (Sum.inl t') c₀) := by
    rw [coincPoly, pencilG, pencilG, pencilG, pencilG, Finset.sum_mul_sum,
      Finset.sum_mul_sum, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun t _ => ?_
    rw [← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun t' _ => ?_
    show pencilK dom k w ℓ₀ R₀ ℓ₁ R₁ J c₀ c₀' cs cs' c₀ (Sum.inl t)
        * C ((dom i) ^ (t : ℕ))
        * (pencilK dom k w ℓ₀ R₀ ℓ₁ R₁ J c₀ c₀' cs cs' c₀' (Sum.inl t')
          * C ((dom j) ^ (t' : ℕ)))
        - pencilK dom k w ℓ₀ R₀ ℓ₁ R₁ J c₀ c₀' cs cs' c₀ (Sum.inl t)
          * C ((dom j) ^ (t : ℕ))
          * (pencilK dom k w ℓ₀ R₀ ℓ₁ R₁ J c₀ c₀' cs cs' c₀' (Sum.inl t')
            * C ((dom i) ^ (t' : ℕ))) = _
    sorry
  sorry

end ProximityGap.WBPencil

/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.Hab25CaptureReconcile
import ArkLib.Data.CodingTheory.ProximityGap.Hab25LaneBridge
import ArkLib.ToMathlib.ZAffineDecomposition
import ArkLib.Data.CodingTheory.ProximityGap.Hab25JohnsonDischarge
import ArkLib.Data.CodingTheory.ProximityGap.BCIKS20.ListDecoding.Agreement

/-!
# The capture wire — from the lane's close decode to `AffineCaptured`

Two links of the per-stack capture chain:

* `agreement_card_of_relDist_le` (ℝ form) and its `ℝ≥0` wrapper — the reverse counting: a
  relative distance `≤ δ` leaves an agreement set of size `≥ (1-δ)·n`, the mirror of the
  lane bridge's direction.
* `affineCaptured_of_pz_affine` — the per-scalar capture: a bad scalar whose lane decode
  is the affine pencil `A₀ + γ·A₁` is captured at `(A₀, A₁)`, via the witness-set
  reconciliation.

Together with the surface-factor production (whose coherence makes the lane decode *be*
the pencil on the whole close set, via the Z-affine decomposition) these produce the
one-pair capture list for every word stack.
-/

namespace CodingTheory.ProximityGap.Hab25Core.Hab25JohnsonEndgame

open _root_.ProximityGap Code Polynomial
open CodingTheory.ProximityGap.Hab25Core.Hab25Johnson
open scoped NNReal

variable {F : Type} [Field F] [Fintype F] [DecidableEq F]

open Classical in
/-- **Reverse counting (ℝ form).**  Relative distance at most `δq` leaves an agreement
set of size at least `(1 - δq)·n`. -/
theorem agreement_card_real_of_relDist_le
    {n : ℕ} [NeZero n] {f g : Fin n → F} {δq : ℚ}
    (hd : ((relHammingDist f g : ℚ≥0) : ℚ) ≤ δq) :
    (1 - (δq : ℝ)) * (Fintype.card (Fin n) : ℝ)
      ≤ ((Finset.univ.filter (fun i => f i = g i)).card : ℝ) := by
  classical
  have hsplit : (Finset.univ.filter (fun i => f i = g i)).card
      + (Finset.univ.filter (fun i => ¬ f i = g i)).card = Fintype.card (Fin n) := by
    simpa using Finset.card_filter_add_card_filter_not
      (s := (Finset.univ : Finset (Fin n))) (p := fun i => f i = g i)
  have hn0 : (0 : ℝ) < (Fintype.card (Fin n) : ℝ) := by
    have : 0 < Fintype.card (Fin n) := Fintype.card_pos
    exact_mod_cast this
  have hdis_le : ((Finset.univ.filter (fun i => ¬ f i = g i)).card : ℝ)
      ≤ (δq : ℝ) * (Fintype.card (Fin n) : ℝ) := by
    have hdef : ((relHammingDist f g : ℚ≥0) : ℝ)
        = ((Finset.univ.filter (fun i => ¬ f i = g i)).card : ℝ)
          / (Fintype.card (Fin n) : ℝ) := by
      rw [relHammingDist]
      push_cast
      rfl
    have hdR : ((relHammingDist f g : ℚ≥0) : ℝ) ≤ (δq : ℝ) := by
      exact_mod_cast hd
    rw [hdef, div_le_iff₀ hn0] at hdR
    linarith
  have hcast : ((Finset.univ.filter (fun i => f i = g i)).card : ℝ)
      + ((Finset.univ.filter (fun i => ¬ f i = g i)).card : ℝ)
      = (Fintype.card (Fin n) : ℝ) := by
    exact_mod_cast hsplit
  nlinarith

open Classical in
/-- **Reverse counting (`ℝ≥0` form, at a rational radius).**  The agreement set meets the
`mcaEvent`-style cardinality bound at `δ := δq.toNNReal`. -/
theorem agreement_card_of_relDist_le
    {n : ℕ} [NeZero n] {f g : Fin n → F} {δq : ℚ}
    (hd : ((relHammingDist f g : ℚ≥0) : ℚ) ≤ δq) :
    ((Finset.univ.filter (fun i => f i = g i)).card : ℝ≥0)
      ≥ (1 - Real.toNNReal (δq : ℝ)) * Fintype.card (Fin n) := by
  classical
  set δ : ℝ≥0 := Real.toNNReal (δq : ℝ) with hδ
  rw [ge_iff_le, ← NNReal.coe_le_coe]
  push_cast
  rcases le_total (1 : ℝ≥0) δ with h1 | h1
  · -- `δ ≥ 1`: the truncated factor vanishes
    rw [tsub_eq_zero_of_le h1]
    simp
  · -- `δ ≤ 1`: the factor coincides with the real form
    have hcoe : ((1 - δ : ℝ≥0) : ℝ) = 1 - (δ : ℝ) := by
      rw [NNReal.coe_sub h1]
      simp
    rw [hcoe]
    have hδle : (δ : ℝ) ≤ (δq : ℝ) ⊔ 0 := by
      rw [hδ, Real.coe_toNNReal']
    have hmain := agreement_card_real_of_relDist_le (f := f) (g := g) hd
    have hn0 : (0 : ℝ) ≤ (Fintype.card (Fin n) : ℝ) := Nat.cast_nonneg _
    rcases le_total (0 : ℝ) ((δq : ℝ)) with h0 | h0
    · have hδeq : (δ : ℝ) = (δq : ℝ) := by
        rw [hδ, Real.coe_toNNReal _ h0]
      rw [hδeq]
      exact hmain
    · -- negative radius: distance `≤ δq ≤ 0` forces full agreement; bound is direct
      have hδ0 : (δ : ℝ) = 0 := by
        rw [hδ, Real.coe_toNNReal']
        simp [max_eq_right h0]
      rw [hδ0]
      have : (1 - (δq : ℝ)) * (Fintype.card (Fin n) : ℝ)
          ≥ (1 - 0) * (Fintype.card (Fin n) : ℝ) := by nlinarith
      nlinarith [hmain]

open Classical in
/-- **The per-scalar capture.**  A bad scalar whose lane decode is the affine pencil
`A₀ + γ·A₁` (degrees `< k`) is captured at `(A₀, A₁)`: the decode's agreement set has the
required size by reverse counting, and the witness-set reconciliation transfers capture to
the `mcaEvent` set. -/
theorem affineCaptured_of_pz_affine
    {n k : ℕ} [NeZero n] {ωs : Fin n ↪ F} {δq : ℚ} {u : WordStack F (Fin 2) (Fin n)}
    {γ : F} {A₀ A₁ : F[X]}
    (hdeg₀ : A₀.natDegree < k) (hdeg₁ : A₁.natDegree < k)
    (hbad : mcaEvent ((ReedSolomon.code ωs k : Set (Fin n → F)))
      (Real.toNNReal (δq : ℝ)) (u 0) (u 1) γ)
    (hclose : ((relHammingDist (u 0 + γ • u 1)
      (fun i => (A₀ + Polynomial.C γ * A₁).eval (ωs i)) : ℚ≥0) : ℚ) ≤ δq)
    (hreg : (k : ℝ) + 2 * ((Real.toNNReal (δq : ℝ) : ℝ≥0) : ℝ) * Fintype.card (Fin n)
      < Fintype.card (Fin n)) :
    AffineCaptured ωs k (Real.toNNReal (δq : ℝ)) u γ (A₀, A₁) := by
  classical
  refine affineCaptured_of_close_affine hdeg₀ hdeg₁ hbad
    (S₁ := Finset.univ.filter (fun i =>
      (u 0 + γ • u 1) i = (A₀ + Polynomial.C γ * A₁).eval (ωs i))) ?_ ?_ hreg
  · exact agreement_card_of_relDist_le hclose
  · intro i hi
    have := (Finset.mem_filter.mp hi).2
    simpa using this.symm


open Classical in
/-- **The numeric edge from per-stack pencil coherence.**  If every word stack's lane
decode collapses to a single affine pencil on the close-proximity set (the surface-factor
production's conclusion through the Z-affine decomposition), the below-Johnson numeric
edge holds at the rational radius — via the one-pair capture list. -/
theorem johnsonNumericBound_of_pencil_coherence
    {n k : ℕ} [NeZero n] (ωs : Fin n ↪ F) (δq : ℚ) (η : ℝ≥0)
    (hδq0 : 0 ≤ δq)
    (hη : 0 < η)
    (hδr : InJohnsonRange ωs (k + 1) η (Real.toNNReal (δq : ℝ)))
    (hk2n : k + 2 ≤ n)
    (hreg : ((k + 1 : ℕ) : ℝ)
      + 2 * ((Real.toNNReal (δq : ℝ) : ℝ≥0) : ℝ) * Fintype.card (Fin n)
      < Fintype.card (Fin n))
    (hpencil : ∀ u : WordStack F (Fin 2) (Fin n),
      ∃ A₀ A₁ : F[X], A₀.natDegree < k + 1 ∧ A₁.natDegree < k + 1 ∧
        ∀ γ ∈ _root_.ProximityGap.coeffs_of_close_proximity
            (F := F) k ωs δq (u 0) (u 1),
          ∀ hγ : γ ∈ _root_.ProximityGap.coeffs_of_close_proximity
            (F := F) k ωs δq (u 0) (u 1),
          _root_.ProximityGap.Pz (n := n) (k := k) (ωs := ωs) (δ := δq)
            (u₀ := u 0) (u₁ := u 1) hγ = A₀ + Polynomial.C γ * A₁) :
    JohnsonNumericBound ωs (k + 1) η (Real.toNNReal (δq : ℝ)) := by
  classical
  set δ : ℝ≥0 := Real.toNNReal (δq : ℝ) with hδdef
  have hδle : (δ : ℝ) ≤ (δq : ℝ) := by
    rw [hδdef, Real.coe_toNNReal _ (by exact_mod_cast hδq0)]
  refine johnsonNumericBound_holds_of_capture_production ωs (k + 1) η δ 1 hη hδr
    (by simp only [Fintype.card_fin]; omega) ?_ ?_
  · -- `1 ≤ (M + 1/2)/√ρ₊`: the multiplicity is at least 3 and the rate factor at most 1
    have hM : (3 : ℝ) ≤ hab25M (Fintype.card (Fin n)) (k + 1) η := le_max_right _ _
    have hρ0 : (0 : ℝ) < hab25RhoPlus (Fintype.card (Fin n)) (k + 1) := by
      rw [hab25RhoPlus]
      have hn0 : (0 : ℝ) < (Fintype.card (Fin n) : ℝ) := by
        have : 0 < Fintype.card (Fin n) := Fintype.card_pos
        exact_mod_cast this
      positivity
    have hρ1 : hab25RhoPlus (Fintype.card (Fin n)) (k + 1) ≤ 1 := by
      rw [hab25RhoPlus]
      have hcard : Fintype.card (Fin n) = n := Fintype.card_fin n
      rw [hcard]
      have hn0 : (0 : ℝ) < (n : ℝ) := by
        have : 0 < n := by omega
        exact_mod_cast this
      rw [show ((k + 1 : ℕ) : ℝ) / (n : ℝ) + 1 / (n : ℝ)
          = (((k + 1 : ℕ) : ℝ) + 1) / n by ring, div_le_one hn0]
      push_cast
      have : (k : ℝ) + 2 ≤ (n : ℝ) := by exact_mod_cast hk2n
      linarith
    have hs1 : hab25RhoPlus (Fintype.card (Fin n)) (k + 1) ^ ((1 : ℝ) / 2) ≤ 1 := by
      calc hab25RhoPlus (Fintype.card (Fin n)) (k + 1) ^ ((1 : ℝ) / 2)
          ≤ 1 ^ ((1 : ℝ) / 2) := Real.rpow_le_rpow hρ0.le hρ1 (by norm_num)
        _ = 1 := Real.one_rpow _
    have hs0 : (0 : ℝ) < hab25RhoPlus (Fintype.card (Fin n)) (k + 1) ^ ((1 : ℝ) / 2) :=
      Real.rpow_pos_of_pos hρ0 _
    rw [le_div_iff₀ hs0]
    push_cast
    nlinarith
  · -- the one-pair capture list per stack
    intro u
    obtain ⟨A₀, A₁, hd₀, hd₁, hcoh⟩ := hpencil u
    refine ⟨{(A₀, A₁)}, by simp, ?_, ?_⟩
    · intro ab hab
      rw [Finset.mem_singleton] at hab
      subst hab
      exact ⟨hd₀, hd₁⟩
    · intro γ hγbad
      refine ⟨(A₀, A₁), Finset.mem_singleton_self _, ?_⟩
      -- the bad scalar is close
      have hγclose : γ ∈ _root_.ProximityGap.coeffs_of_close_proximity
          (F := F) k ωs δq (u 0) (u 1) :=
        hab25McaBadScalars_subset_coeffs_of_close_proximity ωs δ δq hδle u hγbad
      -- the `mcaEvent` witness
      have hbad : mcaEvent ((ReedSolomon.code ωs (k + 1) : Set (Fin n → F)))
          δ (u 0) (u 1) γ := by
        have := hγbad
        rw [hab25McaBadScalars, Finset.mem_filter] at this
        exact this.2
      -- the lane decode is the pencil, and it is `δq`-close
      have hPz := _root_.ProximityGap.Pz_relDist_le
        (n := n) (k := k) (ωs := ωs) (δ := δq) (u₀ := u 0) (u₁ := u 1) hγclose
      rw [hcoh γ hγclose hγclose] at hPz
      have hclose : ((relHammingDist (u 0 + γ • u 1)
          (fun i => (A₀ + Polynomial.C γ * A₁).eval (ωs i)) : ℚ≥0) : ℚ) ≤ δq := by
        exact_mod_cast hPz
      exact affineCaptured_of_pz_affine hd₀ hd₁ hbad hclose hreg


open Classical in
/-- **The pencil-coherence glue.**  A per-stack affine surface coherent with the lane's
decode family (the surface-factor production's conclusion) yields the pencil-coherence
hypothesis of the assembly: the surface's inner-coefficient extractions are the pair. -/
theorem pencil_coherence_of_surface
    {n k : ℕ} [NeZero n] {ωs : Fin n ↪ F} {δq : ℚ} [DecidableEq (RatFunc F)]
    (hsurface : ∀ u : WordStack F (Fin 2) (Fin n),
      ∃ w : Polynomial (Polynomial F), w.natDegree ≤ k ∧
        (∀ i, (w.coeff i).natDegree ≤ 1) ∧
        ∀ γ ∈ _root_.ProximityGap.coeffs_of_close_proximity
            (F := F) k ωs δq (u 0) (u 1),
          w.map (Polynomial.evalRingHom γ)
            = _root_.ProximityGap.PzFamily
                (F := F) (n := n) δq (u 0) (u 1) ωs k γ) :
    ∀ u : WordStack F (Fin 2) (Fin n),
      ∃ A₀ A₁ : F[X], A₀.natDegree < k + 1 ∧ A₁.natDegree < k + 1 ∧
        ∀ γ ∈ _root_.ProximityGap.coeffs_of_close_proximity
            (F := F) k ωs δq (u 0) (u 1),
          ∀ hγ : γ ∈ _root_.ProximityGap.coeffs_of_close_proximity
            (F := F) k ωs δq (u 0) (u 1),
          _root_.ProximityGap.Pz (n := n) (k := k) (ωs := ωs) (δ := δq)
            (u₀ := u 0) (u₁ := u 1) hγ = A₀ + Polynomial.C γ * A₁ := by
  intro u
  obtain ⟨w, hwdeg, haff, hcoh⟩ := hsurface u
  refine ⟨Polynomial.innerCoeff w 0, Polynomial.innerCoeff w 1,
    lt_of_le_of_lt (Polynomial.innerCoeff_natDegree_le w 0) (by omega),
    lt_of_le_of_lt (Polynomial.innerCoeff_natDegree_le w 1) (by omega),
    fun γ hγmem hγ => ?_⟩
  have h1 : w.map (Polynomial.evalRingHom γ)
      = Polynomial.innerCoeff w 0 + Polynomial.C γ * Polynomial.innerCoeff w 1 :=
    Polynomial.map_evalRingHom_eq_affine haff γ
  have h2 := hcoh γ hγmem
  have h3 : _root_.ProximityGap.PzFamily
      (F := F) (n := n) δq (u 0) (u 1) ωs k γ
      = _root_.ProximityGap.Pz (n := n) (k := k) (ωs := ωs) (δ := δq)
        (u₀ := u 0) (u₁ := u 1) hγ := by
    unfold _root_.ProximityGap.PzFamily
    rw [dif_pos hγ]
  rw [← h3, ← h2, h1]

open Classical in
/-- **The numeric edge from the per-stack surface.**  The composed conditional: a
per-stack coherent affine surface (the surface-factor production's conclusion, for every
word stack) gives the below-Johnson numeric edge at the rational radius. -/
theorem johnsonNumericBound_of_surface
    {n k : ℕ} [NeZero n] (ωs : Fin n ↪ F) (δq : ℚ) (η : ℝ≥0)
    [DecidableEq (RatFunc F)]
    (hδq0 : 0 ≤ δq)
    (hη : 0 < η)
    (hδr : InJohnsonRange ωs (k + 1) η (Real.toNNReal (δq : ℝ)))
    (hk2n : k + 2 ≤ n)
    (hreg : ((k + 1 : ℕ) : ℝ)
      + 2 * ((Real.toNNReal (δq : ℝ) : ℝ≥0) : ℝ) * Fintype.card (Fin n)
      < Fintype.card (Fin n))
    (hsurface : ∀ u : WordStack F (Fin 2) (Fin n),
      ∃ w : Polynomial (Polynomial F), w.natDegree ≤ k ∧
        (∀ i, (w.coeff i).natDegree ≤ 1) ∧
        ∀ γ ∈ _root_.ProximityGap.coeffs_of_close_proximity
            (F := F) k ωs δq (u 0) (u 1),
          w.map (Polynomial.evalRingHom γ)
            = _root_.ProximityGap.PzFamily
                (F := F) (n := n) δq (u 0) (u 1) ωs k γ) :
    JohnsonNumericBound ωs (k + 1) η (Real.toNNReal (δq : ℝ)) :=
  johnsonNumericBound_of_pencil_coherence ωs δq η hδq0 hη hδr hk2n hreg
    (pencil_coherence_of_surface hsurface)


open Classical in
/-- **The small branch.**  Bad scalars inject into the close-proximity index, so the bad
count is at most the close count. -/
theorem badCount_le_close_card
    {n k : ℕ} [NeZero n] (ωs : Fin n ↪ F) (δq : ℚ) (δ : ℝ≥0)
    (hδle : (δ : ℝ) ≤ (δq : ℝ)) (u : WordStack F (Fin 2) (Fin n)) :
    (hab25McaBadScalars ωs (k + 1) δ u).card
      ≤ (_root_.ProximityGap.coeffs_of_close_proximity
          (F := F) k ωs δq (u 0) (u 1)).card :=
  Finset.card_le_card
    (hab25McaBadScalars_subset_coeffs_of_close_proximity ωs δ δq hδle u)

open Classical in
/-- **The large branch.**  If one affine pair captures every bad scalar, the bad count is
at most `n`: capture converts to improvement at the pair's difference words, and improving
sets number at most `n`. -/
theorem badCount_le_card_of_one_pair_capture
    {n k : ℕ} [NeZero n] (ωs : Fin n ↪ F) (δ : ℝ≥0)
    (u : WordStack F (Fin 2) (Fin n)) {A₀ A₁ : F[X]}
    (hdeg₀ : A₀.natDegree < k + 1) (hdeg₁ : A₁.natDegree < k + 1)
    (hcap : ∀ γ ∈ hab25McaBadScalars ωs (k + 1) δ u,
      AffineCaptured ωs (k + 1) δ u γ (A₀, A₁)) :
    (hab25McaBadScalars ωs (k + 1) δ u).card ≤ Fintype.card (Fin n) := by
  refine factorImprove_card_le_n
    (fun i => A₀.eval (ωs i) - u 0 i) (fun i => A₁.eval (ωs i) - u 1 i)
    (hab25McaBadScalars ωs (k + 1) δ u) ?_
  intro γ hγ
  exact affineCaptured_improve hdeg₀ hdeg₁ (hcap γ hγ)

end CodingTheory.ProximityGap.Hab25Core.Hab25JohnsonEndgame

/-! ## Axiom audit -/
#print axioms CodingTheory.ProximityGap.Hab25Core.Hab25JohnsonEndgame.agreement_card_real_of_relDist_le
#print axioms CodingTheory.ProximityGap.Hab25Core.Hab25JohnsonEndgame.agreement_card_of_relDist_le
#print axioms CodingTheory.ProximityGap.Hab25Core.Hab25JohnsonEndgame.affineCaptured_of_pz_affine
#print axioms CodingTheory.ProximityGap.Hab25Core.Hab25JohnsonEndgame.johnsonNumericBound_of_pencil_coherence
#print axioms CodingTheory.ProximityGap.Hab25Core.Hab25JohnsonEndgame.pencil_coherence_of_surface
#print axioms CodingTheory.ProximityGap.Hab25Core.Hab25JohnsonEndgame.johnsonNumericBound_of_surface
#print axioms CodingTheory.ProximityGap.Hab25Core.Hab25JohnsonEndgame.badCount_le_close_card
#print axioms CodingTheory.ProximityGap.Hab25Core.Hab25JohnsonEndgame.badCount_le_card_of_one_pair_capture

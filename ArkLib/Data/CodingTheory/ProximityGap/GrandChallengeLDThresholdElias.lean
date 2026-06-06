/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/

import ArkLib.Data.CodingTheory.ProximityGap.GrandChallengeLattice
import ArkLib.Data.CodingTheory.ListDecoding.Bounds

/-!
# Elias-volume ceiling for the genuine list-decoding threshold

`GrandChallengeLDThreshold.lean` pins the genuine lattice threshold between a
Johnson-side floor and the *capacity* ceiling `n - deg`.  This file sharpens the ceiling
using the proven Elias volume bound (`linear_lambda_ge_elias_volume_eli57`, ABF26
Lemma 3.7 [Eli57]): for a linear code `C` of dimension `k`,
`Λ(C, δ) ≥ Vol_q(δ, n) / q^(n-k)`.

Through the diagonal embedding (`Lambda_le_Lambda_interleaved`, the trivial direction of
ABF26 Lemma 2.10) the same lower bound applies to the interleaved code, so any grid
radius `j/n` at which the Elias volume already exceeds the prize budget `ε*·|F|` is an
upper bound on `listLatticeThreshold`.  Quantitatively the Elias volume clears the budget
strictly *below* the capacity radius (around the `q`-ary-entropy radius), so this ceiling
is sharper than `n - deg` in the prize regime; the numeric instantiation is left
parameterized (`hvol`) and is dischargeable per instance.
-/

namespace ProximityGap

open scoped NNReal
open ListDecodable

variable {F ι : Type} [Field F] [Fintype F] [DecidableEq F]
  [Fintype ι] [Nonempty ι] [DecidableEq ι]

omit [Field F] [Nonempty ι] [DecidableEq ι] in
/-- **Diagonal embedding bound** (trivial direction of ABF26 Lemma 2.10): the interleaved
list size dominates the base list size, via `c ↦ (c, …, c)` around `f ↦ (f, …, f)`. -/
lemma Lambda_le_Lambda_interleaved (C : Set (ι → F)) {m : ℕ} (hm : m ≠ 0) (δ : ℝ) :
    Lambda C δ ≤ Lambda (C^⋈ (Fin m)) δ := by
  classical
  have : Nonempty (Fin m) := ⟨⟨0, Nat.pos_of_ne_zero hm⟩⟩
  unfold Lambda
  refine iSup_le fun f => ?_
  refine le_trans ?_ (le_iSup _ (fun i (_ : Fin m) => f i))
  -- inject the base list into the interleaved list via the diagonal
  set d : (ι → F) → (ι → (Fin m → F)) := fun c => fun i _ => c i with hd
  have hinj : Set.InjOn d (closeCodewordsRel C f δ) := by
    intro a _ b _ hab
    funext i
    exact congrFun (congrFun hab i) (Classical.arbitrary (Fin m))
  have hmaps : ∀ c ∈ closeCodewordsRel C f δ,
      d c ∈ closeCodewordsRel (C^⋈ (Fin m)) (fun i (_ : Fin m) => f i) δ := by
    rintro c ⟨hcC, hcball⟩
    refine ⟨?_, ?_⟩
    · -- every row of the diagonal stack is `c`
      show ∀ k : Fin m, (Matrix.transpose (d c)) k ∈ C
      intro k
      have : Matrix.transpose (d c) k = c := rfl
      rw [this]
      exact hcC
    · -- the diagonal stack is exactly as far from the diagonal centre as `c` from `f`
      rw [relHammingBall, Set.mem_setOf_eq] at hcball ⊢
      have hham : hammingDist (fun i (_ : Fin m) => f i) (d c) = hammingDist f c := by
        unfold hammingDist
        apply congrArg Finset.card
        ext i
        simp only [Finset.mem_filter, Finset.mem_univ, true_and]
        constructor
        · intro h hfc
          exact h (by funext k; simp [hd, hfc])
        · intro h hstack
          exact h (congrFun hstack (Classical.arbitrary (Fin m)))
      have hdiag_eq : ((Code.relHammingDist (fun i (_ : Fin m) => f i) (d c) : ℚ≥0) : ℝ)
          = ((Code.relHammingDist f c : ℚ≥0) : ℝ) := by
        unfold Code.relHammingDist
        rw [hham]
      have key : ((Code.relHammingDist (fun i (_ : Fin m) => f i) (d c) : ℚ≥0) : ℝ) ≤ δ := by
        rw [hdiag_eq]
        -- transport `hcball` across the (subsingleton) `Decidable` instance choice
        convert hcball using 3
      convert key using 3
  calc ((closeCodewordsRel C f δ).ncard : ℕ∞)
      = ((d '' closeCodewordsRel C f δ).ncard : ℕ∞) := by
        rw [Set.InjOn.ncard_image hinj]
    _ ≤ ((closeCodewordsRel (C^⋈ (Fin m)) (fun i (_ : Fin m) => f i) δ).ncard : ℕ∞) := by
        refine le_of_eq_of_le rfl ?_
        have himg : d '' closeCodewordsRel C f δ ⊆
            closeCodewordsRel (C^⋈ (Fin m)) (fun i (_ : Fin m) => f i) δ := by
          rintro _ ⟨c, hc, rfl⟩
          exact hmaps c hc
        exact_mod_cast Set.ncard_le_ncard himg (Set.toFinite _)

/-- **Elias-volume ceiling on the genuine threshold.**  If at grid radius `j/n` the Elias
volume bound `Vol_q(j/n, n) / q^(n-k)` already exceeds the prize budget `ε*·|F|`, then
the genuine lattice threshold is below `j`.  Combined with
`linear_lambda_ge_elias_volume_eli57` this places the threshold strictly below the
entropy radius — sharper than the bare capacity ceiling of
`GrandChallengeLDThreshold.lean` once `Vol` is instantiated. -/
theorem listLatticeThreshold_lt_of_elias_volume
    (C : Submodule F (ι → F)) {m j : ℕ} (hm : m ≠ 0)
    (hj0 : 0 < j) (hjn : j < Fintype.card ι)
    {ε_star : ℝ≥0}
    (hvol : (ε_star : ENNReal) * (Fintype.card F : ENNReal) <
      ENNReal.ofReal
        ((CodingTheory.hammingBallVolume (Fintype.card F)
            (((j : ℝ≥0) / (Fintype.card ι : ℝ≥0) : ℝ≥0) : ℝ) (Fintype.card ι) : ℝ)
          / (Fintype.card F : ℝ) ^
              ((Fintype.card ι : ℝ) - Module.finrank F C)))
    (hne : (GrandChallenges.listLatticeSet (C : Set (ι → F)) m ε_star).Nonempty) :
    GrandChallenges.listLatticeThreshold (C : Set (ι → F)) m ε_star hne < j := by
  classical
  have hnpos : 0 < Fintype.card ι := Fintype.card_pos
  -- the Elias lower bound at radius j/n
  have hδpos : (0 : ℝ) < (((j : ℝ≥0) / (Fintype.card ι : ℝ≥0) : ℝ≥0) : ℝ) := by
    push_cast
    positivity
  have hδlt : (((j : ℝ≥0) / (Fintype.card ι : ℝ≥0) : ℝ≥0) : ℝ) < 1 := by
    push_cast
    rw [div_lt_one (by positivity)]
    exact_mod_cast hjn
  have helias := CodingTheory.linear_lambda_ge_elias_volume_eli57 C
    (((j : ℝ≥0) / (Fintype.card ι : ℝ≥0) : ℝ≥0) : ℝ) hδpos hδlt
  -- every lattice index ≥ j fails the budget
  rw [GrandChallenges.listLatticeThreshold, Finset.max'_lt_iff]
  intro i hi
  by_contra hgt
  push Not at hgt
  rw [GrandChallenges.listLatticeSet, Finset.mem_filter, Finset.mem_range] at hi
  obtain ⟨hir, hile⟩ := hi
  have hin : i ≤ Fintype.card ι := Nat.lt_succ_iff.mp hir
  have hji : j ≤ i := by omega
  -- Λ(C^⋈m, i/n) ≥ Λ(C^⋈m, j/n) ≥ Λ(C, j/n) ≥ Elias volume > ε*·|F|
  have hmono : Lambda ((C : Set (ι → F))^⋈ (Fin m))
      (((j : ℝ≥0) / (Fintype.card ι : ℝ≥0) : ℝ≥0) : ℝ) ≤
      Lambda ((C : Set (ι → F))^⋈ (Fin m))
      (((i : ℝ≥0) / (Fintype.card ι : ℝ≥0) : ℝ≥0) : ℝ) := by
    apply Lambda_mono
    push_cast
    apply div_le_div_of_nonneg_right ?_ (by positivity)
    exact_mod_cast hji
  have hdiag := Lambda_le_Lambda_interleaved (C : Set (ι → F)) hm
    (((j : ℝ≥0) / (Fintype.card ι : ℝ≥0) : ℝ≥0) : ℝ)
  have hchain : (ε_star : ENNReal) * (Fintype.card F : ENNReal) <
      (Lambda ((C : Set (ι → F))^⋈ (Fin m))
        (((i : ℝ≥0) / (Fintype.card ι : ℝ≥0) : ℝ≥0) : ℝ) : ENNReal) := by
    calc (ε_star : ENNReal) * (Fintype.card F : ENNReal)
        < ENNReal.ofReal
            ((CodingTheory.hammingBallVolume (Fintype.card F)
                (((j : ℝ≥0) / (Fintype.card ι : ℝ≥0) : ℝ≥0) : ℝ) (Fintype.card ι) : ℝ)
              / (Fintype.card F : ℝ) ^
                  ((Fintype.card ι : ℝ) - Module.finrank F C)) := hvol
      _ ≤ (Lambda ((C : Set (ι → F)))
            (((j : ℝ≥0) / (Fintype.card ι : ℝ≥0) : ℝ≥0) : ℝ) : ENNReal) := helias
      _ ≤ (Lambda ((C : Set (ι → F))^⋈ (Fin m))
            (((j : ℝ≥0) / (Fintype.card ι : ℝ≥0) : ℝ≥0) : ℝ) : ENNReal) := by
          exact_mod_cast hdiag
      _ ≤ _ := by exact_mod_cast hmono
  exact absurd hile (not_le.mpr hchain)

end ProximityGap

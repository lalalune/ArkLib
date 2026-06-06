/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/

import ArkLib.Data.CodingTheory.ProximityGap.GrandChallengeLDThresholdJohnsonSq
import ArkLib.Data.CodingTheory.ProximityGap.GrandChallengeLDThreshold
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

/-- **Exact threshold from adjacent Johnson-square and Elias certificates.**
If the squared-form Johnson bound certifies lattice index `j` as good and the Elias
volume lower bound certifies index `j + 1` as already bad, then the faithful
list-decoding lattice threshold is exactly `j`.

This is the local finite-search closing step for the current strongest LD machinery:
all remaining difficulty is in discharging the numeric Johnson/Elias hypotheses at
the target RS parameters. -/
theorem listLatticeThreshold_eq_of_johnson_sq_and_elias_next
    (C : Submodule F (ι → F)) {m j ℓ : ℕ}
    (hm : m ≠ 0)
    (hj_next : j + 1 < Fintype.card ι)
    (hq1 : 1 < Fintype.card F)
    (hP : (Fintype.card ι : ℝ) / (Fintype.card F : ℝ) ≤
      ((Fintype.card ι - j : ℕ) : ℝ))
    (hsq : ((ℓ : ℝ) + 1)
        * ((((Fintype.card ι - j : ℕ) : ℝ)) -
            (Fintype.card ι : ℝ) / (Fintype.card F : ℝ)) ^ 2
      > ((Fintype.card ι : ℝ) * (1 - 1 / (Fintype.card F : ℝ)))
        * ((Fintype.card ι : ℝ) * (1 - 1 / (Fintype.card F : ℝ))
            + (ℓ : ℝ) * (((Fintype.card ι - Code.minDist (C : Set (ι → F)) : ℕ) : ℝ) -
                (Fintype.card ι : ℝ) / (Fintype.card F : ℝ))))
    {ε_star : ℝ≥0}
    (hpow : ((ℓ : ENNReal)) ^ m ≤
      (ε_star : ENNReal) * (Fintype.card F : ENNReal))
    (hvol_next : (ε_star : ENNReal) * (Fintype.card F : ENNReal) <
      ENNReal.ofReal
        ((CodingTheory.hammingBallVolume (Fintype.card F)
            ((((j + 1 : ℕ) : ℝ≥0) / (Fintype.card ι : ℝ≥0) : ℝ≥0) : ℝ)
            (Fintype.card ι) : ℝ)
          / (Fintype.card F : ℝ) ^
              ((Fintype.card ι : ℝ) - Module.finrank F C)))
    (hne : (GrandChallenges.listLatticeSet (C : Set (ι → F)) m ε_star).Nonempty) :
    GrandChallenges.listLatticeThreshold (C : Set (ι → F)) m ε_star hne = j := by
  have hjn : j ≤ Fintype.card ι := by omega
  have hlow :
      j ≤ GrandChallenges.listLatticeThreshold (C : Set (ι → F)) m ε_star hne :=
    le_listLatticeThreshold_of_johnson_sq
      (C := (C : Set (ι → F))) (m := m) (j := j) (ℓ := ℓ)
      hjn hq1 hP hsq hpow hne
  have hhi :
      GrandChallenges.listLatticeThreshold (C : Set (ι → F)) m ε_star hne < j + 1 :=
    listLatticeThreshold_lt_of_elias_volume
      (C := C) (m := m) (j := j + 1) hm (Nat.succ_pos j) hj_next hvol_next hne
  exact Nat.le_antisymm (Nat.lt_succ_iff.mp hhi) hlow

/-- **Exact threshold from an abstract base-code `Λ` cap and Elias certificate.**
If a capacity-style theorem certifies lattice index `j` as good by proving
`Λ(C, j/n) ≤ ℓ`, and the Elias volume lower bound certifies `j + 1` as already bad,
then the faithful list-decoding lattice threshold is exactly `j`.

This is the same finite-search closing step as
`listLatticeThreshold_eq_of_johnson_sq_and_elias_next`, with the Johnson-square
machinery replaced by the exact residual theorem ordinary-RS capacity routes need. -/
theorem listLatticeThreshold_eq_of_Lambda_le_and_elias_next
    (C : Submodule F (ι → F)) {m j ℓ : ℕ}
    (hm : m ≠ 0)
    (hj_next : j + 1 < Fintype.card ι)
    (hLambda :
      Lambda (C : Set (ι → F))
        (((j : ℝ≥0) / (Fintype.card ι : ℝ≥0) : ℝ≥0) : ℝ) ≤ (ℓ : ℕ∞))
    {ε_star : ℝ≥0}
    (hpow : ((ℓ : ENNReal)) ^ m ≤
      (ε_star : ENNReal) * (Fintype.card F : ENNReal))
    (hvol_next : (ε_star : ENNReal) * (Fintype.card F : ENNReal) <
      ENNReal.ofReal
        ((CodingTheory.hammingBallVolume (Fintype.card F)
            ((((j + 1 : ℕ) : ℝ≥0) / (Fintype.card ι : ℝ≥0) : ℝ≥0) : ℝ)
            (Fintype.card ι) : ℝ)
          / (Fintype.card F : ℝ) ^
              ((Fintype.card ι : ℝ) - Module.finrank F C)))
    (hne : (GrandChallenges.listLatticeSet (C : Set (ι → F)) m ε_star).Nonempty) :
    GrandChallenges.listLatticeThreshold (C : Set (ι → F)) m ε_star hne = j := by
  have hjn : j ≤ Fintype.card ι := by omega
  have hlow :
      j ≤ GrandChallenges.listLatticeThreshold (C : Set (ι → F)) m ε_star hne :=
    le_listLatticeThreshold_of_Lambda_le
      (C := (C : Set (ι → F))) (m := m) (j := j) (ℓ := ℓ)
      hjn hLambda hpow hne
  have hhi :
      GrandChallenges.listLatticeThreshold (C : Set (ι → F)) m ε_star hne < j + 1 :=
    listLatticeThreshold_lt_of_elias_volume
      (C := C) (m := m) (j := j + 1) hm (Nat.succ_pos j) hj_next hvol_next hne
  exact Nat.le_antisymm (Nat.lt_succ_iff.mp hhi) hlow

/-- **Reusable finite-search frontier for an exact faithful LD threshold.**

This packages the currently strongest post-refutation closing surface: a base-code `Λ` cap at
index `j`, the budget inequality that lifts it through interleaving, and an Elias-volume
certificate that index `j + 1` is already above the prize budget.  Proving this package for a
specific smooth-domain RS family determines the faithful lattice threshold at `j` without reviving
the refuted RIM derandomization route. -/
structure ListLatticeThresholdLambdaEliasFrontier
    (C : Submodule F (ι → F)) (m j ℓ : ℕ) (ε_star : ℝ≥0) : Prop where
  /-- Nonzero interleaving arity, required for the diagonal embedding into `C^⋈m`. -/
  hm : m ≠ 0
  /-- The Elias certificate is checked at the adjacent lattice index `j + 1`. -/
  hj_next : j + 1 < Fintype.card ι
  /-- The lower-side base-code list-size cap at lattice index `j`. -/
  hLambda :
    Lambda (C : Set (ι → F))
      (((j : ℝ≥0) / (Fintype.card ι : ℝ≥0) : ℝ≥0) : ℝ) ≤ (ℓ : ℕ∞)
  /-- The `m`-fold interleaving budget clears the prize threshold. -/
  hpow : ((ℓ : ENNReal)) ^ m ≤
    (ε_star : ENNReal) * (Fintype.card F : ENNReal)
  /-- The Elias-volume lower bound at `j + 1` already exceeds the prize threshold. -/
  hvol_next : (ε_star : ENNReal) * (Fintype.card F : ENNReal) <
    ENNReal.ofReal
      ((CodingTheory.hammingBallVolume (Fintype.card F)
          ((((j + 1 : ℕ) : ℝ≥0) / (Fintype.card ι : ℝ≥0) : ℝ≥0) : ℝ)
          (Fintype.card ι) : ℝ)
        / (Fintype.card F : ℝ) ^
            ((Fintype.card ι : ℝ) - Module.finrank F C))

/-- A packaged base-`Λ`/Elias frontier determines the faithful list lattice threshold exactly. -/
theorem listLatticeThreshold_eq_of_lambda_elias_frontier
    (C : Submodule F (ι → F)) {m j ℓ : ℕ} {ε_star : ℝ≥0}
    (H : ListLatticeThresholdLambdaEliasFrontier C m j ℓ ε_star)
    (hne : (GrandChallenges.listLatticeSet (C : Set (ι → F)) m ε_star).Nonempty) :
    GrandChallenges.listLatticeThreshold (C : Set (ι → F)) m ε_star hne = j :=
  listLatticeThreshold_eq_of_Lambda_le_and_elias_next
    (C := C) (m := m) (j := j) (ℓ := ℓ)
    H.hm H.hj_next H.hLambda H.hpow H.hvol_next hne

/-- **Elias-volume upper witness for the faithful list-prize API.**
If the Elias volume lower bound already exceeds the prize budget at lattice radius `j/n`,
then that radius is a public `ListUpperWitness`, not only an upper bound on the canonical
`listLatticeThreshold`. -/
noncomputable def listUpperWitness_of_elias_volume
    (C : Submodule F (ι → F)) {m j : ℕ} (hm : m ≠ 0)
    (hj0 : 0 < j) (hjn : j < Fintype.card ι)
    {ε_star : ℝ≥0}
    (hvol : (ε_star : ENNReal) * (Fintype.card F : ENNReal) <
      ENNReal.ofReal
        ((CodingTheory.hammingBallVolume (Fintype.card F)
            (((j : ℝ≥0) / (Fintype.card ι : ℝ≥0) : ℝ≥0) : ℝ) (Fintype.card ι) : ℝ)
          / (Fintype.card F : ℝ) ^
              ((Fintype.card ι : ℝ) - Module.finrank F C))) :
    GrandChallenges.ListUpperWitness (C : Set (ι → F)) m ε_star := by
  classical
  let δ : ℝ≥0 := (j : ℝ≥0) / (Fintype.card ι : ℝ≥0)
  have hδpos : (0 : ℝ) < (δ : ℝ) := by
    dsimp [δ]
    push_cast
    positivity
  have hδlt : (δ : ℝ) < 1 := by
    dsimp [δ]
    push_cast
    rw [div_lt_one (by positivity)]
    exact_mod_cast hjn
  have helias := CodingTheory.linear_lambda_ge_elias_volume_eli57 C (δ : ℝ) hδpos hδlt
  have hdiag := Lambda_le_Lambda_interleaved (C : Set (ι → F)) hm (δ : ℝ)
  refine GrandChallenges.ListUpperWitness.ofGt (C := (C : Set (ι → F))) (m := m)
    (ε_star := ε_star) (δ := δ) ?_
  calc (ε_star : ENNReal) * (Fintype.card F : ENNReal)
      < ENNReal.ofReal
          ((CodingTheory.hammingBallVolume (Fintype.card F)
              (((j : ℝ≥0) / (Fintype.card ι : ℝ≥0) : ℝ≥0) : ℝ)
              (Fintype.card ι) : ℝ)
            / (Fintype.card F : ℝ) ^
                ((Fintype.card ι : ℝ) - Module.finrank F C)) := hvol
    _ ≤ (Lambda ((C : Set (ι → F))) (δ : ℝ) : ENNReal) := by
        simpa [δ] using helias
    _ ≤ (Lambda ((C : Set (ι → F))^⋈ (Fin m)) (δ : ℝ) : ENNReal) := by
        exact_mod_cast hdiag

end ProximityGap

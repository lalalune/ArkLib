/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/

import ArkLib.Data.CodingTheory.ProximityGap.GrandChallengeCollapse

/-!
# Faithful lattice encodings of the §1 Grand Challenges (after Finding F6)

`GrandChallengeCollapse.lean` proves that the real-valued, strict-failure encodings
`grandMCAChallenge` / `grandListDecodingChallenge` of `GrandChallenges.lean` **collapse**:
because `ε_mca C δ` and `Λ(C^⋈m, δ)` are step functions of `δ` through `⌊δ·n⌋`
(`epsMCA_eq_of_floor_eq`, `Lambda_eq_of_floor_eq`), no maximal *real* threshold `δ* < 1` can
satisfy a strict-failure-above clause, so the encodings degenerate to radius-one statements
and `listDecodingPrize` is provably false as encoded.

The paper [ABF26] §1 actually asks to **determine the largest *lattice* threshold**
`δ* ∈ {0, 1/n, …, 1}`: relative Hamming distances live on the `1/n`-lattice, so the only
meaningful thresholds are the lattice points `j/n` for `j : Fin (n+1)`, where
`n := |ι|`. On this lattice the maximal threshold is a *well-defined finite quantity*
whenever it exists at all — a finite, nonempty, (by monotonicity) downward-closed subset of
`Fin (n+1)` has a maximum — and **determining its value is the open $1M problem**; the
one-sided witnesses of `GrandChallenges.lean` *bound* it.

This file builds that faithful encoding:

* `mcaLatticePoint n j := j/n : ℝ≥0` — the lattice radii.
* `mcaSatisfies C ε* j` (a `DecidablePred`) — `ε_mca(C, j/n) ≤ ε*`; downward closed in `j`
  by `epsMCA_mono` (`mcaSatisfies_downward_closed`).
* `mcaThreshold C ε* hne : Fin (n+1)` — the lattice threshold, `Finset.max'` of the
  satisfying set under a nonemptiness hypothesis `hne`
  (the paper's "`|F|` sufficiently large so that `δ*` exists").
* `mcaThreshold_spec` / `mcaThreshold_unique` — existence and uniqueness: the threshold
  satisfies the bound and is the **unique greatest** lattice point that does.
* `mcaThresholdLattice_bracketed` — a lattice lower witness and a lattice upper witness
  bracket `mcaThreshold`, mirroring `mca_threshold_bracketed`.
* the list-decoding analogues `listThreshold`, `listThreshold_spec`, … ,
  `listThresholdLattice_bracketed`.

Nothing here resolves the prize: it makes the prize *quantity* `mcaThreshold` / `listThreshold`
a real Lean object that the witnesses can be proved to bracket, replacing the collapse-broken
existence predicate.

## References

- [ABF26] Arnon, Boneh, Fenzi. *Open Problems in List Decoding and Correlated Agreement*.
-/

set_option linter.unusedFintypeInType false
set_option linter.unusedDecidableInType false
set_option linter.unusedSectionVars false

namespace ProximityGap

open scoped NNReal

namespace GrandChallengesLattice

/-! ## Lattice radii -/

/-- The lattice radius `j/n : ℝ≥0` for `j : Fin (n+1)`. Relative Hamming distances take
values in `{0, 1/n, …, n/n = 1}`, so these are the only meaningful proximity radii. -/
noncomputable def mcaLatticePoint (n : ℕ) (j : Fin (n + 1)) : ℝ≥0 :=
  (j.val : ℝ≥0) / (n : ℝ≥0)

/-- Each lattice radius lies in `[0, 1]`. -/
theorem mcaLatticePoint_le_one (n : ℕ) (j : Fin (n + 1)) :
    mcaLatticePoint n j ≤ 1 := by
  unfold mcaLatticePoint
  rcases Nat.eq_zero_or_pos n with hn | hn
  · subst hn
    simp
  · rw [div_le_one (by exact_mod_cast hn)]
    exact_mod_cast Nat.lt_succ_iff.mp j.isLt

/-- Lattice radii are monotone in the index. -/
theorem mcaLatticePoint_mono (n : ℕ) {i j : Fin (n + 1)} (h : i ≤ j) :
    mcaLatticePoint n i ≤ mcaLatticePoint n j := by
  unfold mcaLatticePoint
  gcongr
  exact_mod_cast h

/-- The floor index of a lattice radius is the index itself: `⌊(j/n)·n⌋ = j` (for `0 < n`). -/
theorem floor_mcaLatticePoint (n : ℕ) (hn : 0 < n) (j : Fin (n + 1)) :
    Nat.floor (mcaLatticePoint n j * (n : ℝ≥0)) = j.val := by
  unfold mcaLatticePoint
  have hnne : (n : ℝ≥0) ≠ 0 := by exact_mod_cast hn.ne'
  rw [div_mul_cancel₀ _ hnne]
  exact Nat.floor_natCast _

/-! ## The MCA lattice threshold

`mcaSatisfies C ε* j` says the lattice radius `j/n` keeps `ε_mca` within `ε*`. By
`epsMCA_mono` this predicate is *downward closed* in `j`, so the set of satisfying `j` is
an initial segment of `Fin (n+1)`; its maximum (when the set is nonempty) is the faithful
lattice threshold the paper asks to determine. -/

variable {ι : Type} [Fintype ι] [Nonempty ι] [DecidableEq ι]
variable {F : Type} [Field F] [Fintype F] [DecidableEq F]

/-- `ε_mca(C, j/n) ≤ ε*` at the lattice radius `j/n`. Decidable so the satisfying set is a
`Finset`. -/
def mcaSatisfies (C : Set (ι → F)) (ε_star : ℝ≥0) (j : Fin (Fintype.card ι + 1)) : Prop :=
  epsMCA (F := F) (A := F) C (mcaLatticePoint (Fintype.card ι) j) ≤ (ε_star : ENNReal)

noncomputable instance (C : Set (ι → F)) (ε_star : ℝ≥0) :
    DecidablePred (mcaSatisfies C ε_star) := fun _ => Classical.propDecidable _

/-- **Downward closure.** If `j/n` keeps `ε_mca ≤ ε*` and `i ≤ j`, then so does `i/n`.
Direct consequence of `epsMCA_mono`. -/
theorem mcaSatisfies_downward_closed (C : Set (ι → F)) (ε_star : ℝ≥0)
    {i j : Fin (Fintype.card ι + 1)} (hij : i ≤ j) (hj : mcaSatisfies C ε_star j) :
    mcaSatisfies C ε_star i :=
  le_trans (epsMCA_mono (F := F) C (mcaLatticePoint_mono _ hij)) hj

/-- The satisfying lattice points, as a `Finset (Fin (n+1))`. -/
noncomputable def mcaSatSet (C : Set (ι → F)) (ε_star : ℝ≥0) :
    Finset (Fin (Fintype.card ι + 1)) :=
  Finset.univ.filter (mcaSatisfies C ε_star)

@[simp] theorem mem_mcaSatSet (C : Set (ι → F)) (ε_star : ℝ≥0)
    {j : Fin (Fintype.card ι + 1)} :
    j ∈ mcaSatSet C ε_star ↔ mcaSatisfies C ε_star j := by
  simp [mcaSatSet]

/-- **Existence (nonemptiness) hypothesis.** The paper's "assuming `|F|` sufficiently large
so that such a `δ*_C` exists": some lattice radius keeps `ε_mca` within `ε*`. Equivalently,
the satisfying set is nonempty. This is the *only* hypothesis the lattice encoding needs;
once it holds, the threshold is a well-defined finite quantity. -/
def mcaThresholdExists (C : Set (ι → F)) (ε_star : ℝ≥0) : Prop :=
  ∃ j : Fin (Fintype.card ι + 1), mcaSatisfies C ε_star j

theorem mcaSatSet_nonempty_iff (C : Set (ι → F)) (ε_star : ℝ≥0) :
    (mcaSatSet C ε_star).Nonempty ↔ mcaThresholdExists C ε_star := by
  constructor
  · rintro ⟨j, hj⟩; exact ⟨j, (mem_mcaSatSet C ε_star).mp hj⟩
  · rintro ⟨j, hj⟩; exact ⟨j, (mem_mcaSatSet C ε_star).mpr hj⟩

/-- **The faithful MCA lattice threshold** `δ*_C = mcaThreshold / n`. Defined as the greatest
lattice index whose radius keeps `ε_mca` within `ε*`, under the existence hypothesis `hne`.
**Determining its value is the open ABF26 §1 Grand MCA Challenge** (the $1M problem); the
witnesses below merely bracket it. -/
noncomputable def mcaThreshold (C : Set (ι → F)) (ε_star : ℝ≥0)
    (hne : mcaThresholdExists C ε_star) : Fin (Fintype.card ι + 1) :=
  (mcaSatSet C ε_star).max' ((mcaSatSet_nonempty_iff C ε_star).mpr hne)

/-- **Existence half.** The lattice threshold itself satisfies the MCA bound:
`ε_mca(C, mcaThreshold/n) ≤ ε*`. -/
theorem mcaThreshold_spec (C : Set (ι → F)) (ε_star : ℝ≥0)
    (hne : mcaThresholdExists C ε_star) :
    mcaSatisfies C ε_star (mcaThreshold C ε_star hne) := by
  have h := (mcaSatSet C ε_star).max'_mem ((mcaSatSet_nonempty_iff C ε_star).mpr hne)
  exact (mem_mcaSatSet C ε_star).mp h

/-- **Maximality.** Every satisfying lattice point is `≤ mcaThreshold`. -/
theorem le_mcaThreshold (C : Set (ι → F)) (ε_star : ℝ≥0)
    (hne : mcaThresholdExists C ε_star) {j : Fin (Fintype.card ι + 1)}
    (hj : mcaSatisfies C ε_star j) :
    j ≤ mcaThreshold C ε_star hne :=
  (mcaSatSet C ε_star).le_max' j ((mem_mcaSatSet C ε_star).mpr hj)

/-- **Strict failure above the threshold.** Any lattice point strictly above `mcaThreshold`
fails the bound: `ε_mca(C, j/n) > ε*`. This is the lattice analogue of the (collapse-broken)
real strict-failure clause, and it holds here precisely because we are on the lattice. -/
theorem gt_mcaThreshold_exceeds (C : Set (ι → F)) (ε_star : ℝ≥0)
    (hne : mcaThresholdExists C ε_star) {j : Fin (Fintype.card ι + 1)}
    (hj : mcaThreshold C ε_star hne < j) :
    epsMCA (F := F) (A := F) C (mcaLatticePoint (Fintype.card ι) j) > (ε_star : ENNReal) := by
  by_contra h
  exact absurd (le_mcaThreshold C ε_star hne (not_lt.mp h)) (not_le.mpr hj)

/-- **Uniqueness.** `mcaThreshold` is the *unique* lattice index that both satisfies the
bound and is maximal among satisfying indices. Hence the lattice threshold is well-defined:
existence + uniqueness of the maximal `j`. -/
theorem mcaThreshold_unique (C : Set (ι → F)) (ε_star : ℝ≥0)
    (hne : mcaThresholdExists C ε_star) (j : Fin (Fintype.card ι + 1))
    (hsat : mcaSatisfies C ε_star j)
    (hmax : ∀ i : Fin (Fintype.card ι + 1), mcaSatisfies C ε_star i → i ≤ j) :
    j = mcaThreshold C ε_star hne :=
  le_antisymm (le_mcaThreshold C ε_star hne hsat)
    (hmax _ (mcaThreshold_spec C ε_star hne))

/-! ## Bridging the witness framework to the MCA lattice threshold

A `MCALowerWitness` (a real radius `δ ≤ 1` with `ε_mca(C, δ) ≤ ε*`) lands, via the step
structure `epsMCA_eq_of_floor_eq`, on the lattice point `⌊δ·n⌋`, certifying a *lower* bound
on `mcaThreshold`. A `MCAUpperWitness` lands on `⌊δ·n⌋` and certifies an *upper* bound. These
mirror `MCALowerWitness.le_δStar` / `MCAUpperWitness.δStar_le` on the lattice. -/

open GrandChallenges

/-- The lattice index `⌊δ·n⌋` carried by a real radius `δ ≤ 1`, as a `Fin (n+1)`. -/
noncomputable def latticeIndexOf (δ : ℝ≥0) (hδ : δ ≤ 1) : Fin (Fintype.card ι + 1) :=
  ⟨Nat.floor (δ * (Fintype.card ι : ℝ≥0)),
    Nat.lt_succ_of_le (by
      have hle : δ * (Fintype.card ι : ℝ≥0) ≤ (Fintype.card ι : ℝ≥0) := by
        calc δ * (Fintype.card ι : ℝ≥0)
            ≤ 1 * (Fintype.card ι : ℝ≥0) := by gcongr
          _ = (Fintype.card ι : ℝ≥0) := one_mul _
      calc Nat.floor (δ * (Fintype.card ι : ℝ≥0))
          ≤ Nat.floor ((Fintype.card ι : ℝ≥0)) := Nat.floor_le_floor hle
        _ = Fintype.card ι := Nat.floor_natCast _)⟩

@[simp] theorem latticeIndexOf_val (δ : ℝ≥0) (hδ : δ ≤ 1) :
    (latticeIndexOf (ι := ι) δ hδ).val = Nat.floor (δ * (Fintype.card ι : ℝ≥0)) := rfl

/-- `ε_mca` at a real radius equals `ε_mca` at its lattice point `⌊δ·n⌋/n` (step structure):
the radius enters only through `⌊δ·n⌋`. -/
theorem epsMCA_eq_at_latticeIndex (C : Set (ι → F)) (δ : ℝ≥0) (hδ : δ ≤ 1) :
    epsMCA (F := F) (A := F) C δ =
      epsMCA (F := F) (A := F) C
        (mcaLatticePoint (Fintype.card ι) (latticeIndexOf (ι := ι) δ hδ)) := by
  have hn : 0 < Fintype.card ι := Fintype.card_pos
  refine epsMCA_eq_of_floor_eq (F := F) C ?_
  rw [floor_mcaLatticePoint _ hn, latticeIndexOf_val]

/-- **Lower bracket.** An `MCALowerWitness` forces its lattice index `⌊δ·n⌋ ≤ mcaThreshold`:
the certified real radius rounds down to a satisfying lattice point. -/
theorem MCALowerWitness_le_mcaThreshold (C : Set (ι → F)) (ε_star : ℝ≥0)
    (hne : mcaThresholdExists C ε_star) (w : MCALowerWitness C ε_star) :
    latticeIndexOf (ι := ι) w.δ w.le_one ≤ mcaThreshold C ε_star hne := by
  refine le_mcaThreshold C ε_star hne ?_
  unfold mcaSatisfies
  rw [← epsMCA_eq_at_latticeIndex C w.δ w.le_one]
  exact w.bound

/-- A lower MCA witness is already enough to make the faithful lattice threshold exist:
round the certified real radius down to its Hamming lattice point. -/
theorem mcaThresholdExists_of_MCALowerWitness (C : Set (ι → F)) (ε_star : ℝ≥0)
    (w : MCALowerWitness C ε_star) :
    mcaThresholdExists C ε_star :=
  ⟨latticeIndexOf (ι := ι) w.δ w.le_one, by
    unfold mcaSatisfies
    rw [← epsMCA_eq_at_latticeIndex C w.δ w.le_one]
    exact w.bound⟩

/-- The faithful MCA threshold obtained from a lower witness satisfies the MCA bound. -/
theorem mcaThreshold_spec_of_MCALowerWitness (C : Set (ι → F)) (ε_star : ℝ≥0)
    (w : MCALowerWitness C ε_star) :
    let hne := mcaThresholdExists_of_MCALowerWitness C ε_star w
    mcaSatisfies C ε_star (mcaThreshold C ε_star hne) :=
  mcaThreshold_spec C ε_star (mcaThresholdExists_of_MCALowerWitness C ε_star w)

/-- A repaired line-decoding target that yields an MCA lower witness also makes the faithful
MCA lattice threshold exist. -/
theorem mcaThresholdExists_ofLineDecodingTarget
    (C : ModuleCode ι F F) (δ a ε_star : ℝ≥0)
    (hδ_le_one : δ ≤ 1)
    (hLD : CodingTheory.LineDecodable (F := F) (A := F) (C : Set (ι → F)) δ a
      ((Fintype.card ι : ℝ≥0) + 1))
    (hTarget : CodingTheory.lineDecodable_imp_epsMCA_le_target (F := F) (A := F)
      C δ a hLD)
    (hle : (a : ENNReal) / (Fintype.card F : ENNReal) ≤ (ε_star : ENNReal)) :
    mcaThresholdExists (C : Set (ι → F)) ε_star :=
  mcaThresholdExists_of_MCALowerWitness (C : Set (ι → F)) ε_star
    (MCALowerWitness.ofLineDecodingTarget C δ a ε_star hδ_le_one hLD hTarget hle)

/-- The faithful MCA threshold created from a repaired line-decoding target satisfies the MCA
bound. -/
theorem mcaThreshold_spec_ofLineDecodingTarget
    (C : ModuleCode ι F F) (δ a ε_star : ℝ≥0)
    (hδ_le_one : δ ≤ 1)
    (hLD : CodingTheory.LineDecodable (F := F) (A := F) (C : Set (ι → F)) δ a
      ((Fintype.card ι : ℝ≥0) + 1))
    (hTarget : CodingTheory.lineDecodable_imp_epsMCA_le_target (F := F) (A := F)
      C δ a hLD)
    (hle : (a : ENNReal) / (Fintype.card F : ENNReal) ≤ (ε_star : ENNReal)) :
    let hne := mcaThresholdExists_ofLineDecodingTarget C δ a ε_star hδ_le_one hLD hTarget hle
    mcaSatisfies (C : Set (ι → F)) ε_star
      (mcaThreshold (C : Set (ι → F)) ε_star hne) :=
  mcaThreshold_spec (C : Set (ι → F)) ε_star
    (mcaThresholdExists_ofLineDecodingTarget C δ a ε_star hδ_le_one hLD hTarget hle)

/-- Under the §4.5 MCA conjecture, the conjectural lower-witness link also makes the faithful
MCA lattice threshold exist. -/
theorem mcaThresholdExists_of_mcaConjecture (h : mcaConjecture) :
    ∃ c₁ c₂ c₃ : ℝ,
      ∀ {ιC : Type} [Fintype ιC] [Nonempty ιC] [DecidableEq ιC]
        {FC : Type} [Field FC] [Fintype FC] [DecidableEq FC]
        (domain : ιC ↪ FC) (k : ℕ) (ε_star δ : ℝ≥0),
        0 < k →
        (δ : ℝ) < 1 - (k : ℝ) / Fintype.card ιC → δ ≤ 1 →
        ENNReal.ofReal
            (mcaConjectureBound (Fintype.card ιC) (Fintype.card FC) k δ c₁ c₂ c₃) ≤
          (ε_star : ENNReal) →
        mcaThresholdExists (ReedSolomon.code domain k : Set (ιC → FC)) ε_star := by
  obtain ⟨c₁, c₂, c₃, hw⟩ := nonempty_mcaLowerWitness_of_mcaConjecture h
  refine ⟨c₁, c₂, c₃, ?_⟩
  intro ιC _ _ _ FC _ _ _ domain k ε_star δ hk hδ hδ1 hle
  rcases hw domain k ε_star δ hk hδ hδ1 hle with ⟨w⟩
  exact mcaThresholdExists_of_MCALowerWitness
    (ReedSolomon.code domain k : Set (ιC → FC)) ε_star w

/-- Under the §4.5 MCA conjecture, the faithful lattice threshold obtained from the conjectural
lower-witness link satisfies the MCA bound. -/
theorem mcaThreshold_spec_of_mcaConjecture (h : mcaConjecture) :
    ∃ c₁ c₂ c₃ : ℝ,
      ∀ {ιC : Type} [Fintype ιC] [Nonempty ιC] [DecidableEq ιC]
        {FC : Type} [Field FC] [Fintype FC] [DecidableEq FC]
        (domain : ιC ↪ FC) (k : ℕ) (ε_star δ : ℝ≥0),
        0 < k →
        (δ : ℝ) < 1 - (k : ℝ) / Fintype.card ιC → δ ≤ 1 →
        ENNReal.ofReal
            (mcaConjectureBound (Fintype.card ιC) (Fintype.card FC) k δ c₁ c₂ c₃) ≤
          (ε_star : ENNReal) →
        ∃ hne : mcaThresholdExists (ReedSolomon.code domain k : Set (ιC → FC)) ε_star,
          mcaSatisfies (ReedSolomon.code domain k : Set (ιC → FC)) ε_star
            (mcaThreshold (ReedSolomon.code domain k : Set (ιC → FC)) ε_star hne) := by
  classical
  rcases mcaThresholdExists_of_mcaConjecture h with ⟨c₁, c₂, c₃, hExists⟩
  refine ⟨c₁, c₂, c₃, ?_⟩
  intro ιC _ _ _ FC _ _ _ domain k ε_star δ hk hδ hδ1 hle
  let hne := hExists domain k ε_star δ hk hδ hδ1 hle
  exact ⟨hne, mcaThreshold_spec (ReedSolomon.code domain k : Set (ιC → FC)) ε_star hne⟩

/-- **Upper bracket.** An `MCAUpperWitness` at a radius `δ ≤ 1` forces
`mcaThreshold < ⌊δ·n⌋`: its lattice point already exceeds `ε*`, so the threshold is strictly
below it. -/
theorem mcaThreshold_lt_MCAUpperWitness (C : Set (ι → F)) (ε_star : ℝ≥0)
    (hne : mcaThresholdExists C ε_star) (w : MCAUpperWitness C ε_star) (hδ : w.δ ≤ 1) :
    mcaThreshold C ε_star hne < latticeIndexOf (ι := ι) w.δ hδ := by
  by_contra h
  push Not at h
  have hsat : mcaSatisfies C ε_star (latticeIndexOf (ι := ι) w.δ hδ) := by
    refine mcaSatisfies_downward_closed C ε_star h ?_
    exact mcaThreshold_spec C ε_star hne
  have : epsMCA (F := F) (A := F) C
      (mcaLatticePoint (Fintype.card ι) (latticeIndexOf (ι := ι) w.δ hδ)) ≤
      (ε_star : ENNReal) := hsat
  rw [← epsMCA_eq_at_latticeIndex C w.δ hδ] at this
  exact absurd this (not_le.mpr w.exceeds)

/-- **Lattice bracketing of the MCA threshold (faithful `mca_threshold_bracketed`).** A
lower witness and an upper witness (at a radius `≤ 1`) bracket the lattice threshold:
`⌊δ_lo·n⌋ ≤ mcaThreshold < ⌊δ_hi·n⌋`. This is the lattice replacement for
`GrandChallenges.mca_threshold_bracketed`, which bracketed the collapse-broken real
threshold of a `GrandMCAResolution`. -/
theorem mcaThresholdLattice_bracketed (C : Set (ι → F)) (ε_star : ℝ≥0)
    (hne : mcaThresholdExists C ε_star)
    (wlo : MCALowerWitness C ε_star)
    (whi : MCAUpperWitness C ε_star) (hδhi : whi.δ ≤ 1) :
    latticeIndexOf (ι := ι) wlo.δ wlo.le_one ≤ mcaThreshold C ε_star hne ∧
      mcaThreshold C ε_star hne < latticeIndexOf (ι := ι) whi.δ hδhi :=
  ⟨MCALowerWitness_le_mcaThreshold C ε_star hne wlo,
    mcaThreshold_lt_MCAUpperWitness C ε_star hne whi hδhi⟩

/-- **Lattice bracketing without a separate existence hypothesis.** The lower witness
both constructs the threshold's nonemptiness proof and supplies the lower bracket. -/
theorem mcaThresholdLattice_bracketed_of_witnesses (C : Set (ι → F)) (ε_star : ℝ≥0)
    (wlo : MCALowerWitness C ε_star)
    (whi : MCAUpperWitness C ε_star) (hδhi : whi.δ ≤ 1) :
    let hne := mcaThresholdExists_of_MCALowerWitness C ε_star wlo
    latticeIndexOf (ι := ι) wlo.δ wlo.le_one ≤ mcaThreshold C ε_star hne ∧
      mcaThreshold C ε_star hne < latticeIndexOf (ι := ι) whi.δ hδhi :=
  mcaThresholdLattice_bracketed C ε_star
    (mcaThresholdExists_of_MCALowerWitness C ε_star wlo) wlo whi hδhi


/-! ## The list-decoding lattice threshold

The exact mirror of the MCA development, with the maximised list size `Λ(C^⋈m, δ)` (ABF26
D2.8) in place of `ε_mca`, the threshold `ε*·|F|` in place of `ε*`, and `lambda_coe_mono`
in place of `epsMCA_mono`. -/

open ListDecodable

/-- `Λ(C^⋈m, j/n) ≤ ε*·|F|` at the lattice radius `j/n`. -/
def listSatisfies (C : Set (ι → F)) (m : ℕ) (ε_star : ℝ≥0)
    (j : Fin (Fintype.card ι + 1)) : Prop :=
  (Lambda (C^⋈ (Fin m)) ((mcaLatticePoint (Fintype.card ι) j : ℝ≥0) : ℝ) : ENNReal) ≤
    ((ε_star : ENNReal) * (Fintype.card F : ENNReal))

noncomputable instance (C : Set (ι → F)) (m : ℕ) (ε_star : ℝ≥0) :
    DecidablePred (listSatisfies C m ε_star) := fun _ => Classical.propDecidable _

/-- **Downward closure** for list decoding, from `lambda_coe_mono`. -/
theorem listSatisfies_downward_closed (C : Set (ι → F)) (m : ℕ) (ε_star : ℝ≥0)
    {i j : Fin (Fintype.card ι + 1)} (hij : i ≤ j) (hj : listSatisfies C m ε_star j) :
    listSatisfies C m ε_star i :=
  le_trans (GrandChallenges.lambda_coe_mono (mcaLatticePoint_mono _ hij)) hj

/-- The satisfying lattice points for the list-decoding bound. -/
noncomputable def listSatSet (C : Set (ι → F)) (m : ℕ) (ε_star : ℝ≥0) :
    Finset (Fin (Fintype.card ι + 1)) :=
  Finset.univ.filter (listSatisfies C m ε_star)

@[simp] theorem mem_listSatSet (C : Set (ι → F)) (m : ℕ) (ε_star : ℝ≥0)
    {j : Fin (Fintype.card ι + 1)} :
    j ∈ listSatSet C m ε_star ↔ listSatisfies C m ε_star j := by
  simp [listSatSet]

/-- **Existence (nonemptiness) hypothesis** for the list-decoding lattice threshold. -/
def listThresholdExists (C : Set (ι → F)) (m : ℕ) (ε_star : ℝ≥0) : Prop :=
  ∃ j : Fin (Fintype.card ι + 1), listSatisfies C m ε_star j

theorem listSatSet_nonempty_iff (C : Set (ι → F)) (m : ℕ) (ε_star : ℝ≥0) :
    (listSatSet C m ε_star).Nonempty ↔ listThresholdExists C m ε_star := by
  constructor
  · rintro ⟨j, hj⟩; exact ⟨j, (mem_listSatSet C m ε_star).mp hj⟩
  · rintro ⟨j, hj⟩; exact ⟨j, (mem_listSatSet C m ε_star).mpr hj⟩

/-- **The faithful list-decoding lattice threshold.** The greatest lattice index whose
radius keeps `Λ(C^⋈m, ·) ≤ ε*·|F|`, under the existence hypothesis. **Determining its value
is the open ABF26 §1 Grand List Decoding Challenge**; the witnesses bracket it. -/
noncomputable def listThreshold (C : Set (ι → F)) (m : ℕ) (ε_star : ℝ≥0)
    (hne : listThresholdExists C m ε_star) : Fin (Fintype.card ι + 1) :=
  (listSatSet C m ε_star).max' ((listSatSet_nonempty_iff C m ε_star).mpr hne)

/-- **Existence half.** The list threshold satisfies the bound. -/
theorem listThreshold_spec (C : Set (ι → F)) (m : ℕ) (ε_star : ℝ≥0)
    (hne : listThresholdExists C m ε_star) :
    listSatisfies C m ε_star (listThreshold C m ε_star hne) := by
  have h := (listSatSet C m ε_star).max'_mem ((listSatSet_nonempty_iff C m ε_star).mpr hne)
  exact (mem_listSatSet C m ε_star).mp h

/-- **Maximality.** Every satisfying lattice point is `≤ listThreshold`. -/
theorem le_listThreshold (C : Set (ι → F)) (m : ℕ) (ε_star : ℝ≥0)
    (hne : listThresholdExists C m ε_star) {j : Fin (Fintype.card ι + 1)}
    (hj : listSatisfies C m ε_star j) :
    j ≤ listThreshold C m ε_star hne :=
  (listSatSet C m ε_star).le_max' j ((mem_listSatSet C m ε_star).mpr hj)

/-- **Strict failure above the threshold.** -/
theorem gt_listThreshold_exceeds (C : Set (ι → F)) (m : ℕ) (ε_star : ℝ≥0)
    (hne : listThresholdExists C m ε_star) {j : Fin (Fintype.card ι + 1)}
    (hj : listThreshold C m ε_star hne < j) :
    (Lambda (C^⋈ (Fin m)) ((mcaLatticePoint (Fintype.card ι) j : ℝ≥0) : ℝ) : ENNReal) >
      ((ε_star : ENNReal) * (Fintype.card F : ENNReal)) := by
  by_contra h
  exact absurd (le_listThreshold C m ε_star hne (not_lt.mp h)) (not_le.mpr hj)

/-- **Uniqueness.** `listThreshold` is the unique maximal satisfying lattice index. -/
theorem listThreshold_unique (C : Set (ι → F)) (m : ℕ) (ε_star : ℝ≥0)
    (hne : listThresholdExists C m ε_star) (j : Fin (Fintype.card ι + 1))
    (hsat : listSatisfies C m ε_star j)
    (hmax : ∀ i : Fin (Fintype.card ι + 1), listSatisfies C m ε_star i → i ≤ j) :
    j = listThreshold C m ε_star hne :=
  le_antisymm (le_listThreshold C m ε_star hne hsat)
    (hmax _ (listThreshold_spec C m ε_star hne))

/-- `Λ` at a real radius equals `Λ` at its lattice point `⌊δ·n⌋/n` (step structure). -/
theorem Lambda_eq_at_latticeIndex (C : Set (ι → F)) (m : ℕ) (δ : ℝ≥0) (hδ : δ ≤ 1) :
    (Lambda (C^⋈ (Fin m)) ((δ : ℝ≥0) : ℝ) : ENNReal) =
      (Lambda (C^⋈ (Fin m))
        ((mcaLatticePoint (Fintype.card ι) (latticeIndexOf (ι := ι) δ hδ) : ℝ≥0) : ℝ)
        : ENNReal) := by
  have hn : 0 < Fintype.card ι := Fintype.card_pos
  congr 1
  refine Lambda_eq_of_floor_eq (C^⋈ (Fin m)) ?_
  rw [floor_mcaLatticePoint _ hn, latticeIndexOf_val]

/-- **Lower bracket.** A `ListLowerWitness` forces `⌊δ·n⌋ ≤ listThreshold`. -/
theorem ListLowerWitness_le_listThreshold (C : Set (ι → F)) (m : ℕ) (ε_star : ℝ≥0)
    (hne : listThresholdExists C m ε_star)
    (w : GrandChallenges.ListLowerWitness C m ε_star) :
    latticeIndexOf (ι := ι) w.δ w.le_one ≤ listThreshold C m ε_star hne := by
  refine le_listThreshold C m ε_star hne ?_
  unfold listSatisfies
  rw [← Lambda_eq_at_latticeIndex C m w.δ w.le_one]
  exact w.bound

/-- A lower list-decoding witness is enough to make the faithful list threshold exist. -/
theorem listThresholdExists_of_ListLowerWitness (C : Set (ι → F)) (m : ℕ)
    (ε_star : ℝ≥0) (w : GrandChallenges.ListLowerWitness C m ε_star) :
    listThresholdExists C m ε_star :=
  ⟨latticeIndexOf (ι := ι) w.δ w.le_one, by
    unfold listSatisfies
    rw [← Lambda_eq_at_latticeIndex C m w.δ w.le_one]
    exact w.bound⟩

/-- The faithful list-decoding threshold obtained from a lower witness satisfies the list
bound. -/
theorem listThreshold_spec_of_ListLowerWitness (C : Set (ι → F)) (m : ℕ)
    (ε_star : ℝ≥0) (w : GrandChallenges.ListLowerWitness C m ε_star) :
    let hne := listThresholdExists_of_ListLowerWitness C m ε_star w
    listSatisfies C m ε_star (listThreshold C m ε_star hne) :=
  listThreshold_spec C m ε_star (listThresholdExists_of_ListLowerWitness C m ε_star w)

/-- **Upper bracket.** A `ListUpperWitness` at a radius `δ ≤ 1` forces
`listThreshold < ⌊δ·n⌋`. -/
theorem listThreshold_lt_ListUpperWitness (C : Set (ι → F)) (m : ℕ) (ε_star : ℝ≥0)
    (hne : listThresholdExists C m ε_star)
    (w : GrandChallenges.ListUpperWitness C m ε_star) (hδ : w.δ ≤ 1) :
    listThreshold C m ε_star hne < latticeIndexOf (ι := ι) w.δ hδ := by
  by_contra h
  push Not at h
  have hsat : listSatisfies C m ε_star (latticeIndexOf (ι := ι) w.δ hδ) :=
    listSatisfies_downward_closed C m ε_star h (listThreshold_spec C m ε_star hne)
  have hb : (Lambda (C^⋈ (Fin m))
      ((mcaLatticePoint (Fintype.card ι) (latticeIndexOf (ι := ι) w.δ hδ) : ℝ≥0) : ℝ)
      : ENNReal) ≤ ((ε_star : ENNReal) * (Fintype.card F : ENNReal)) := hsat
  rw [← Lambda_eq_at_latticeIndex C m w.δ hδ] at hb
  exact absurd hb (not_le.mpr w.exceeds)

/-- **Lattice bracketing of the list-decoding threshold (faithful prize-progress edge).**
A lower witness and an upper witness (at a radius `≤ 1`) bracket the lattice threshold:
`⌊δ_lo·n⌋ ≤ listThreshold < ⌊δ_hi·n⌋`. The list-decoding mirror of
`mcaThresholdLattice_bracketed`. -/
theorem listThresholdLattice_bracketed (C : Set (ι → F)) (m : ℕ) (ε_star : ℝ≥0)
    (hne : listThresholdExists C m ε_star)
    (wlo : GrandChallenges.ListLowerWitness C m ε_star)
    (whi : GrandChallenges.ListUpperWitness C m ε_star) (hδhi : whi.δ ≤ 1) :
    latticeIndexOf (ι := ι) wlo.δ wlo.le_one ≤ listThreshold C m ε_star hne ∧
      listThreshold C m ε_star hne < latticeIndexOf (ι := ι) whi.δ hδhi :=
  ⟨ListLowerWitness_le_listThreshold C m ε_star hne wlo,
    listThreshold_lt_ListUpperWitness C m ε_star hne whi hδhi⟩

/-- **List-threshold bracketing without a separate existence hypothesis.** The lower witness
constructs the threshold's nonemptiness proof and supplies the lower bracket. -/
theorem listThresholdLattice_bracketed_of_witnesses (C : Set (ι → F)) (m : ℕ)
    (ε_star : ℝ≥0)
    (wlo : GrandChallenges.ListLowerWitness C m ε_star)
    (whi : GrandChallenges.ListUpperWitness C m ε_star) (hδhi : whi.δ ≤ 1) :
    let hne := listThresholdExists_of_ListLowerWitness C m ε_star wlo
    latticeIndexOf (ι := ι) wlo.δ wlo.le_one ≤ listThreshold C m ε_star hne ∧
      listThreshold C m ε_star hne < latticeIndexOf (ι := ι) whi.δ hδhi :=
  listThresholdLattice_bracketed C m ε_star
    (listThresholdExists_of_ListLowerWitness C m ε_star wlo) wlo whi hδhi

end GrandChallengesLattice

end ProximityGap

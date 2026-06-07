/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.BCIKS20.Curves

/-!
# The closed square-root boundary `BoundaryCardResidual` via quantization (§6.2)

This file attacks the **last unowned residual** of the [BCIKS20] Theorem 1.5 keystone
`ProximityGap.correlatedAgreement_affine_curves`: the closed-boundary obligation
`ProximityGap.BoundaryCardResidual`.  The obligation is — at the *exact* Johnson boundary radius
`δ = 1 − √ρ`, if the good-coefficient set is nonempty, conclude `jointAgreement`.

## The quantization weapon

The strict-interior case `δ < 1 − √ρ` is closed by the §5 list-decoding extraction
(`StrictCoeffPolysResidual`).  The boundary `δ = 1 − √ρ` is measure-zero but the in-tree
statement includes it.  The decisive structural fact is that **both** sides of the obligation
depend on `δ` *only through* the integer `⌊δ · n⌋`, where `n = |ι|`:

* `RS_goodCoeffsCurve u δ = Finset.filter (δᵣ(curve z, code) ≤ δ) univ`, and
  `δᵣ(·, code) ≤ δ ↔ Δ₀(·, code) ≤ ⌊δ · n⌋`
  (`Code.relDistFromCode_le_iff_distFromCode_le`), so the good set is a **step function** of
  `⌊δ · n⌋` (`goodCoeffsCurve_eq_of_floor_eq`).
* `jointAgreement C δ u = ∃ S, S.card ≥ (1 − δ)·n ∧ …`, and
  `(1 − δ)·n ≤ S.card ↔ n − ⌊δ · n⌋ ≤ S.card`
  (`Code.relDist_floor_bound_iff_complement_bound`), so `jointAgreement` is also a **step
  function** of `⌊δ · n⌋` (`jointAgreement_iff_of_floor_eq`).

Consequently, whenever a strict-interior radius `δ' < 1 − √ρ` shares the boundary's floor
`⌊δ' · n⌋ = ⌊(1 − √ρ) · n⌋`, the boundary obligation at `δ = 1 − √ρ` is **literally the same
statement** as the strict-interior obligation at `δ'` — same good set, same `jointAgreement`.

## When does such a strict `δ'` exist?

The level set of floor `j := ⌊δ · n⌋` is the half-open interval `[j/n, (j+1)/n)`.  A strict
`δ' < δ` with the same floor exists **iff** `δ` is *not* the left endpoint `j/n`, i.e. iff
`δ · n ∉ ℕ` (`exists_lt_floor_eq_of_floor_lt`).  At the boundary `δ · n = (1 − √ρ)·n = n − √(ρ)·n
= n − √(ρ·n²) = n − √(deg·n)` (for `deg ≤ n`); this is an integer **iff** `deg · n` is a perfect
square — exactly the rational-`√ρ` lattice case flagged in the task brief.

So the boundary case splits cleanly:

* **Non-lattice case** (`deg·n` not a perfect square, i.e. `⌊δ·n⌋ < δ·n`): the boundary
  obligation reduces *exactly* to the *strict-interior analogue* of itself at the nearby
  `δ' < 1 − √ρ` (positive good set ⟹ `jointAgreement`).  This is the bulk of the parameter space
  and is discharged here by `boundaryCardResidual_of_not_lattice`, modulo that strict-interior
  producer.  The producer is *not* identical to `StrictCoeffPolysResidual`, but it is the obligation
  in the regime `errorBound > 0`, where the §5 quantitative probability threshold is available —
  unlike the exact boundary, where `errorBound = 0` makes it vacuous (cf. `BoundaryDischarge.lean`).
* **Lattice case** (`δ·n ∈ ℕ`): the boundary *is* the left endpoint of its level set, the
  reduction to a strict sub-radius is unavailable, and the genuine Johnson-boundary combinatorics
  is required.  This case is **precisely isolated** as `BoundaryCardLatticeResidual` and is *not*
  proved here.

## What is therefore proved here

* `goodCoeffsCurve_eq_of_floor_eq`, `jointAgreement_iff_of_floor_eq` — the two step-function
  transport facts.
* `exists_lt_floor_eq_of_floor_lt` — strict-below witness in the same level set under non-lattice.
* `boundaryCardResidual_of_not_lattice` — the boundary residual, reduced to the strict-interior
  `jointAgreement` producer, on the non-lattice part of parameter space (the bulk).
* `BoundaryCardLatticeResidual` + `boundaryCardResidual_of_lattice_residual` — the precisely
  isolated genuine lattice case, fed back into the exact `BoundaryCardResidual` shape consumed by
  the keystone, together with the non-lattice reduction.

`#print axioms` of every declaration here rests only on `[propext, Classical.choice, Quot.sound]`.

## References
* [BCIKS20] Ben-Sasson, Carmon, Ishai, Kopparty, Saraf, *Proximity Gaps for Reed–Solomon Codes*,
  §5 (list-decoding agreement chain), §6.2 (closed Johnson boundary at `1 − √ρ`).
-/

open ProximityGap Code NNReal Finset Function ProbabilityTheory
open scoped BigOperators ENNReal ProbabilityTheory LinearCode

namespace ArkLib

namespace BoundaryCardResidual

variable {ι : Type} [Fintype ι] [Nonempty ι] [DecidableEq ι]
variable {F : Type} [Field F] [Fintype F] [DecidableEq F]

/-! ## Step-function transport: both sides depend on `δ` only through `⌊δ · n⌋` -/

omit [DecidableEq ι] in
/-- **The good set is a step function of `⌊δ · n⌋`.**  Since membership in
`RS_goodCoeffsCurve u δ` is `δᵣ(curve z, code) ≤ δ`, which by
`Code.relDistFromCode_le_iff_distFromCode_le` is equivalent to `Δ₀(curve z, code) ≤ ⌊δ · n⌋`,
two radii with equal floor `⌊δ · n⌋` produce the *same* good-coefficient set. -/
theorem goodCoeffsCurve_eq_of_floor_eq {k deg : ℕ} {domain : ι ↪ F} {δ δ' : ℝ≥0}
    (u : WordStack F (Fin (k + 1)) ι)
    (hfloor : Nat.floor (δ * Fintype.card ι) = Nat.floor (δ' * Fintype.card ι)) :
    RS_goodCoeffsCurve (k := k) (deg := deg) (domain := domain) u δ
      = RS_goodCoeffsCurve (k := k) (deg := deg) (domain := domain) u δ' := by
  classical
  unfold RS_goodCoeffsCurve
  apply Finset.filter_congr
  intro z _
  rw [Code.relDistFromCode_le_iff_distFromCode_le, Code.relDistFromCode_le_iff_distFromCode_le,
    hfloor]

omit [Nonempty ι] [DecidableEq ι] [Fintype F] in
/-- **`jointAgreement` is a step function of `⌊δ · n⌋`.**  The agreement-set cardinality bound
`S.card ≥ (1 − δ)·n` is equivalent, by `Code.relDist_floor_bound_iff_complement_bound`, to
`n − ⌊δ · n⌋ ≤ S.card`, which depends on `δ` only through `⌊δ · n⌋`.  Hence two radii with equal
floor give equivalent `jointAgreement` statements. -/
theorem jointAgreement_iff_of_floor_eq {κ : Type*} {deg : ℕ} {domain : ι ↪ F} {δ δ' : ℝ≥0}
    (u : κ → ι → F)
    (hfloor : Nat.floor (δ * Fintype.card ι) = Nat.floor (δ' * Fintype.card ι)) :
    jointAgreement (C := (ReedSolomon.code domain deg : Set (ι → F))) (δ := δ) (W := u)
      ↔ jointAgreement (C := (ReedSolomon.code domain deg : Set (ι → F))) (δ := δ') (W := u) := by
  classical
  -- `S.card ≥ (1 − e)·n ↔ n − ⌊e·n⌋ ≤ S.card`, packaged for both radii.
  have key : ∀ {e : ℝ≥0} (m : ℕ),
      ((1 - e) * (Fintype.card ι : ℝ≥0) ≤ (m : ℝ≥0))
        ↔ (Fintype.card ι - Nat.floor (e * (Fintype.card ι : ℝ≥0)) ≤ m) := fun {e} m => by
    rw [Code.relDist_floor_bound_iff_complement_bound]
  unfold jointAgreement
  constructor
  · rintro ⟨S, hScard, v, hv⟩
    refine ⟨S, ?_, v, hv⟩
    rw [ge_iff_le, key] at hScard ⊢
    rwa [← hfloor]
  · rintro ⟨S, hScard, v, hv⟩
    refine ⟨S, ?_, v, hv⟩
    rw [ge_iff_le, key] at hScard ⊢
    rwa [hfloor]

/-! ## The non-lattice witness: a strict sub-radius in the same level set -/

/-- **Strict sub-radius in the same `1/n`-level set, under the non-lattice condition.**  If
`δ · n` is not an integer — captured by the strict inequality `⌊δ · n⌋ < δ · n`, i.e. `δ` lies
*strictly inside* its level set `(j/n, (j+1)/n)` rather than at the left endpoint `j/n` — then
there is a strict `δ' < δ` with the same floor.  This is the downward analogue of
`ProximityGap.exists_gt_le_one_floor_eq`. -/
theorem exists_lt_floor_eq_of_floor_lt (n : ℕ) {δ : ℝ≥0} (hn : 0 < n)
    (hfrac : (Nat.floor (δ * n) : ℝ≥0) < δ * n) :
    ∃ δ' : ℝ≥0, δ' < δ ∧ Nat.floor (δ' * n) = Nat.floor (δ * n) := by
  set j : ℕ := Nat.floor (δ * n) with hj
  have hnne : (n : ℝ≥0) ≠ 0 := by exact_mod_cast hn.ne'
  have hδ_gt : (j : ℝ≥0) / n < δ := by
    rw [div_lt_iff₀ (by positivity)]; exact hfrac
  set δ' : ℝ≥0 := ((j : ℝ≥0) / n + δ) / 2 with hδ'
  have hlt1 : (j : ℝ≥0) / n < δ' := by
    rw [hδ', lt_div_iff₀ two_pos, mul_two]; gcongr
  have hlt2 : δ' < δ := by
    rw [hδ', div_lt_iff₀ two_pos, mul_two]; gcongr
  refine ⟨δ', hlt2, ?_⟩
  have hlow : (j : ℝ≥0) ≤ δ' * n := by
    rw [← div_le_iff₀ (by positivity : (0:ℝ≥0) < n)] at *
    exact le_of_lt hlt1
  have hδn_lt : δ * n < (j : ℝ≥0) + 1 := by
    exact_mod_cast Nat.lt_floor_add_one (δ * (n : ℝ≥0))
  have hup : δ' * n < (j : ℝ≥0) + 1 :=
    lt_of_lt_of_le (mul_lt_mul_of_pos_right hlt2 (by positivity)) (le_of_lt hδn_lt)
  have hfloor_le : Nat.floor (δ' * (n : ℝ≥0)) ≤ j := by
    have hup' : δ' * (n : ℝ≥0) < ((j + 1 : ℕ) : ℝ≥0) := by push_cast; exact hup
    have := (Nat.floor_lt (zero_le _)).mpr hup'
    omega
  have hfloor_ge : j ≤ Nat.floor (δ' * (n : ℝ≥0)) := (Nat.le_floor_iff (zero_le _)).mpr hlow
  omega

/-! ## The boundary residual on the non-lattice part of parameter space -/

omit [DecidableEq ι] in
/-- **The strict-interior supply used by the quantization split.**

For every stack `u`, this says that a strict sub-radius `δ' < δ` with the same integer distance
level as `δ` already has the desired `jointAgreement` conclusion whenever its good-coefficient set
is nonempty.  This is the non-lattice input consumed by `boundaryCardResidual_of_not_lattice`;
the exact lattice endpoint is tracked separately by `BoundaryCardLatticeResidual`. -/
def BoundaryCardStrictInteriorResidual {k deg : ℕ} {domain : ι ↪ F} {δ : ℝ≥0} : Prop :=
  ∀ (u : WordStack F (Fin (k + 1)) ι) (δ' : ℝ≥0),
    δ' < δ →
    Nat.floor (δ' * Fintype.card ι) = Nat.floor (δ * Fintype.card ι) →
    0 < (RS_goodCoeffsCurve (k := k) (deg := deg) (domain := domain) u δ').card →
    jointAgreement (C := ReedSolomon.code domain deg) (δ := δ') (W := u)

omit [DecidableEq ι] in
/-- **The closed boundary residual, reduced to the strict interior on the non-lattice part.**

Suppose the boundary radius `δ = 1 − √ρ` is *not* a `1/n`-lattice point — concretely, the floor
is strictly below `δ · n` (`hNotLattice`).  Then the boundary `BoundaryCardResidual` follows from
the **strict-interior** `jointAgreement` producer `hStrict`: a hypothesis supplying
`jointAgreement` at any genuinely interior radius `δ' < 1 − √ρ` whose good set (equivalently,
whose floor) matches the boundary's and is nonempty.

The proof is the pure quantization reduction: pick a strict `δ' < δ` with the same floor
(`exists_lt_floor_eq_of_floor_lt`); transport the nonempty good set down
(`goodCoeffsCurve_eq_of_floor_eq`); obtain `jointAgreement` at `δ'` from `hStrict`; transport it
back up to the boundary (`jointAgreement_iff_of_floor_eq`).

`hStrict` is the **strict-interior analogue** of the boundary obligation: positive good-set
cardinality ⟹ `jointAgreement`, but at a radius `δ' < 1 − √ρ` rather than at the exact boundary.
It is a hypothesis here, never the goal.  Its value is that, unlike the exact boundary where
`errorBound = 0` collapses the §5 quantitative probability threshold to vacuous positivity
(see `ArkLib/ToMathlib/BoundaryDischarge.lean`), at the strict interior `errorBound > 0` and the
§5 list-decoding machinery (`StrictCoeffPolysResidual` and the front-door cardinality bounds it
enables) is genuinely applicable.  This lemma performs no boundary combinatorics; it only moves the
obligation off the measure-zero boundary into the open interior. -/
theorem boundaryCardResidual_of_not_lattice {k deg : ℕ} {domain : ι ↪ F} {δ : ℝ≥0}
    (hNotLattice :
      (Nat.floor (δ * Fintype.card ι) : ℝ≥0) < δ * Fintype.card ι)
    (hStrict : ∀ (u : WordStack F (Fin (k + 1)) ι) (δ' : ℝ≥0),
      δ' < δ →
      Nat.floor (δ' * Fintype.card ι) = Nat.floor (δ * Fintype.card ι) →
      0 < (RS_goodCoeffsCurve (k := k) (deg := deg) (domain := domain) u δ').card →
      jointAgreement (C := ReedSolomon.code domain deg) (δ := δ') (W := u)) :
    BoundaryCardResidual (k := k) (deg := deg) (domain := domain) (δ := δ) := by
  intro _hk u _hδeq hcardPos
  -- Strict sub-radius `δ' < δ` with the same floor.
  obtain ⟨δ', hδ'lt, hδ'floor⟩ :=
    exists_lt_floor_eq_of_floor_lt (Fintype.card ι) Fintype.card_pos hNotLattice
  -- The good set is unchanged, so it is still nonempty at `δ'`.
  have hgood :
      RS_goodCoeffsCurve (k := k) (deg := deg) (domain := domain) u δ'
        = RS_goodCoeffsCurve (k := k) (deg := deg) (domain := domain) u δ :=
    goodCoeffsCurve_eq_of_floor_eq (deg := deg) (domain := domain) u hδ'floor
  have hcardPos' :
      0 < (RS_goodCoeffsCurve (k := k) (deg := deg) (domain := domain) u δ').card := by
    rw [hgood]; exact hcardPos
  -- `jointAgreement` at the strict-interior radius, then transported back to the boundary.
  have hjoint' := hStrict u δ' hδ'lt hδ'floor hcardPos'
  exact (jointAgreement_iff_of_floor_eq (deg := deg) (domain := domain) u hδ'floor.symm).mpr hjoint'

/-! ## The precisely isolated genuine lattice case -/

omit [DecidableEq ι] in
/-- **The isolated genuine residual: the boundary is a `1/n`-lattice point.**  When
`δ · n ∈ ℕ` (`δ = j/n` exactly), the boundary is the *left endpoint* of its level set and there
is no strict sub-radius with the same floor: the quantization reduction is unavailable.  This is
the genuine Johnson-boundary combinatorial case (`deg·n` a perfect square).  It is recorded here
as an explicit named obligation — *not* proved — so the residual surface is exact. -/
def BoundaryCardLatticeResidual {k deg : ℕ} {domain : ι ↪ F} {δ : ℝ≥0} : Prop :=
  ∀ (_hk : 0 < k) (u : WordStack F (Fin (k + 1)) ι),
    δ = 1 - ReedSolomon.sqrtRate deg domain →
    (Nat.floor (δ * Fintype.card ι) : ℝ≥0) = δ * Fintype.card ι →
    0 < (RS_goodCoeffsCurve (k := k) (deg := deg) (domain := domain) u δ).card →
    jointAgreement (C := ReedSolomon.code domain deg) (δ := δ) (W := u)

/-- **The smaller concrete data needed for the exact lattice case.**

This splits `BoundaryCardLatticeResidual` into the three non-goal inputs consumed by the in-tree
boundary assembly bridge: two good-set cardinality lower bounds and the §5 coefficient-polynomial
extraction.  It keeps the exact lattice witnesses (`δ = 1 - sqrtRate` and
`⌊δ · n⌋ = δ · n`) visible, so downstream work can target the genuine square-root lattice branch
without restating `jointAgreement` itself. -/
def BoundaryCardLatticeData {k deg : ℕ} {domain : ι ↪ F} {δ : ℝ≥0} : Prop :=
  ∀ (_hk : 0 < k) (u : WordStack F (Fin (k + 1)) ι),
    δ = 1 - ReedSolomon.sqrtRate deg domain →
    (Nat.floor (δ * Fintype.card ι) : ℝ≥0) = δ * Fintype.card ι →
    0 < (RS_goodCoeffsCurve (k := k) (deg := deg) (domain := domain) u δ).card →
    ((RS_goodCoeffsCurve (k := k) (deg := deg) (domain := domain) u δ).card > k) ∧
    ((RS_goodCoeffsCurve (k := k) (deg := deg) (domain := domain) u δ).card ≥
      (Fintype.card ι + 1) * k) ∧
    (∀ P : F → Polynomial F,
      (∀ z ∈ RS_goodCoeffsCurve (k := k) (deg := deg) (domain := domain) u δ,
        (P z).natDegree < deg ∧
          δᵣ(∑ t : Fin (k + 1), (z ^ (t : ℕ)) • u t,
            (P z).eval ∘ domain) ≤ δ) →
        ∃ B : ℕ → Polynomial F,
          (∀ j < deg, (B j).natDegree < k + 1) ∧
            ∀ z ∈ RS_goodCoeffsCurve (k := k) (deg := deg) (domain := domain) u δ,
              ∀ j < deg, (P z).coeff j = (B j).eval z)

omit [Nonempty ι] [DecidableEq ι] in
/-- The isolated lattice-boundary residual is vacuous for `k = 0`, since its first hypothesis is
`0 < k`. This mirrors `BoundaryDischarge.boundaryCardResidual_zero` for the sharper residual
surface introduced in this file. -/
theorem boundaryCardLatticeResidual_zero
    {deg : ℕ} {domain : ι ↪ F} {δ : ℝ≥0} :
    BoundaryCardLatticeResidual (k := 0) (deg := deg) (domain := domain) (δ := δ) := by
  intro hk
  omega

omit [Nonempty ι] [DecidableEq ι] in
/-- The concrete lattice-data package is also vacuous for `k = 0`, since its first hypothesis is
`0 < k`. This is the data-level companion to `boundaryCardLatticeResidual_zero`. -/
theorem boundaryCardLatticeData_zero
    {deg : ℕ} {domain : ι ↪ F} {δ : ℝ≥0} :
    BoundaryCardLatticeData (k := 0) (deg := deg) (domain := domain) (δ := δ) := by
  intro hk
  omega

omit [DecidableEq ι] in
/-- The exact residual package produced by the boundary quantization split: the strict-interior
supply for non-lattice boundary levels, plus the genuine lattice endpoint residual. -/
def BoundaryCardQuantizationResiduals {k deg : ℕ} {domain : ι ↪ F} {δ : ℝ≥0} : Prop :=
  BoundaryCardStrictInteriorResidual (k := k) (deg := deg) (domain := domain) (δ := δ) ∧
  BoundaryCardLatticeResidual (k := k) (deg := deg) (domain := domain) (δ := δ)

omit [Nonempty ι] [DecidableEq ι] in
/-- At `k = 0`, the lattice half of the boundary quantization package is vacuous.  Thus a
strict-interior producer alone assembles the full quantization residual package. -/
theorem BoundaryCardQuantizationResiduals.ofStrictInterior_zero
    {deg : ℕ} {domain : ι ↪ F} {δ : ℝ≥0}
    (hStrict :
      BoundaryCardStrictInteriorResidual (k := 0) (deg := deg) (domain := domain) (δ := δ)) :
    BoundaryCardQuantizationResiduals (k := 0) (deg := deg) (domain := domain) (δ := δ) :=
  ⟨hStrict, boundaryCardLatticeResidual_zero⟩

omit [DecidableEq ι] in
/-- Projection of the strict-interior, non-lattice side of the boundary quantization package. -/
theorem BoundaryCardQuantizationResiduals.strictInterior {k deg : ℕ} {domain : ι ↪ F}
    {δ : ℝ≥0}
    (h : BoundaryCardQuantizationResiduals (k := k) (deg := deg) (domain := domain) (δ := δ)) :
    BoundaryCardStrictInteriorResidual (k := k) (deg := deg) (domain := domain) (δ := δ) :=
  h.1

omit [DecidableEq ι] in
/-- Projection of the exact `1/n`-lattice endpoint side of the boundary quantization package. -/
theorem BoundaryCardQuantizationResiduals.lattice {k deg : ℕ} {domain : ι ↪ F} {δ : ℝ≥0}
    (h : BoundaryCardQuantizationResiduals (k := k) (deg := deg) (domain := domain) (δ := δ)) :
    BoundaryCardLatticeResidual (k := k) (deg := deg) (domain := domain) (δ := δ) :=
  h.2

omit [DecidableEq ι] in
/-- **`BoundaryCardResidual` from the non-lattice reduction plus the isolated lattice residual.**

The boundary `δ · n` is either an integer (lattice case, handled by `hLattice`) or not (non-lattice
case, handled by the strict-interior producer `hStrict` through
`boundaryCardResidual_of_not_lattice`).
A single `lt_or_eq` on `⌊δ·n⌋ ≤ δ·n` discharges the whole `BoundaryCardResidual`.

This is the exact `BoundaryCardResidual` shape consumed by the keystone
`ProximityGap.correlatedAgreement_affine_curves`.  Its *only* genuinely boundary-specific open
input is `hLattice`; the non-lattice bulk is reduced to `hStrict`, the strict-interior analogue at
radii `δ' < δ` where `errorBound > 0` makes the §5 quantitative machinery applicable. -/
theorem boundaryCardResidual_of_lattice_residual {k deg : ℕ} {domain : ι ↪ F} {δ : ℝ≥0}
    (hLattice : BoundaryCardLatticeResidual (k := k) (deg := deg) (domain := domain) (δ := δ))
    (hStrict : ∀ (u : WordStack F (Fin (k + 1)) ι) (δ' : ℝ≥0),
      δ' < δ →
      Nat.floor (δ' * Fintype.card ι) = Nat.floor (δ * Fintype.card ι) →
      0 < (RS_goodCoeffsCurve (k := k) (deg := deg) (domain := domain) u δ').card →
      jointAgreement (C := ReedSolomon.code domain deg) (δ := δ') (W := u)) :
    BoundaryCardResidual (k := k) (deg := deg) (domain := domain) (δ := δ) := by
  intro hk u hδeq hcardPos
  -- `⌊δ·n⌋ ≤ δ·n` always; split into the strict (non-lattice) and equality (lattice) cases.
  have hle : (Nat.floor (δ * Fintype.card ι) : ℝ≥0) ≤ δ * Fintype.card ι :=
    Nat.floor_le (zero_le _)
  rcases lt_or_eq_of_le hle with hlt | heq
  · exact boundaryCardResidual_of_not_lattice (deg := deg) (domain := domain) hlt hStrict
      hk u hδeq hcardPos
  · exact hLattice hk u hδeq heq hcardPos

omit [DecidableEq ι] in
/-- Reconstruct the original `BoundaryCardResidual` from the quantified strict-interior supply
and the isolated lattice endpoint residual. -/
theorem BoundaryCardQuantizationResiduals.toBoundaryCardResidual {k deg : ℕ} {domain : ι ↪ F}
    {δ : ℝ≥0}
    (h : BoundaryCardQuantizationResiduals (k := k) (deg := deg) (domain := domain) (δ := δ)) :
    BoundaryCardResidual (k := k) (deg := deg) (domain := domain) (δ := δ) :=
  boundaryCardResidual_of_lattice_residual
    (deg := deg) (domain := domain) (δ := δ) h.lattice h.strictInterior

omit [DecidableEq ι] in
/-- The sharper boundary-probability residual used by the curve keystone follows from the
isolated lattice residual plus the strict-interior producer.

This composes `boundaryCardResidual_of_lattice_residual` with
`ProximityGap.boundaryProbabilityResidual_of_boundaryCardResidual`, so downstream callers can target
the exact `BoundaryProbabilityResidual` surface without manually passing through the older
cardinality-only boundary residual. -/
theorem boundaryProbabilityResidual_of_lattice_residual {k deg : ℕ} {domain : ι ↪ F} {δ : ℝ≥0}
    [NeZero deg]
    (hδ : δ ≤ 1 - ReedSolomon.sqrtRate deg domain)
    (hLattice : BoundaryCardLatticeResidual (k := k) (deg := deg) (domain := domain) (δ := δ))
    (hStrict : ∀ (u : WordStack F (Fin (k + 1)) ι) (δ' : ℝ≥0),
      δ' < δ →
      Nat.floor (δ' * Fintype.card ι) = Nat.floor (δ * Fintype.card ι) →
      0 < (RS_goodCoeffsCurve (k := k) (deg := deg) (domain := domain) u δ').card →
      jointAgreement (C := ReedSolomon.code domain deg) (δ := δ') (W := u)) :
    ProximityGap.BoundaryProbabilityResidual
      (k := k) (deg := deg) (domain := domain) (δ := δ) := by
  exact ProximityGap.boundaryProbabilityResidual_of_boundaryCardResidual
    (deg := deg) (domain := domain) (δ := δ) hδ
    (boundaryCardResidual_of_lattice_residual
      (deg := deg) (domain := domain) (δ := δ) hLattice hStrict)

omit [DecidableEq ι] in
/-- The boundary-probability residual follows from the packaged quantization residuals.  This is
the downstream-facing form of `boundaryProbabilityResidual_of_lattice_residual`: callers can prove
the two exact leaves once, package them as `BoundaryCardQuantizationResiduals`, and recover the
probability residual consumed by the curve keystone. -/
theorem BoundaryCardQuantizationResiduals.toBoundaryProbabilityResidual {k deg : ℕ}
    {domain : ι ↪ F} {δ : ℝ≥0} [NeZero deg]
    (h : BoundaryCardQuantizationResiduals (k := k) (deg := deg) (domain := domain) (δ := δ))
    (hδ : δ ≤ 1 - ReedSolomon.sqrtRate deg domain) :
    ProximityGap.BoundaryProbabilityResidual
      (k := k) (deg := deg) (domain := domain) (δ := δ) :=
  boundaryProbabilityResidual_of_lattice_residual
    (deg := deg) (domain := domain) (δ := δ) hδ h.lattice h.strictInterior

/-! ## Characterising the lattice case: the boundary is a `1/n`-point iff `√ρ · n ∈ ℕ` -/

omit [Nonempty ι] [DecidableEq ι] [Fintype F] in
/-- **The boundary lattice condition is `√ρ · n ∈ ℕ`.**  At the boundary `δ = 1 − √ρ` (with
`√ρ ≤ 1`, which always holds for a Reed–Solomon code), `δ · n = n − √ρ · n`, so `δ · n` is an
integer *iff* `√ρ · n` is.  Since `√ρ · n = n·√(deg/n) = √(deg · n)` (for `deg ≤ n`), the
genuine lattice case is exactly `deg · n` a perfect square — the rational-`√ρ` case flagged in the
task brief.  This lemma records the field-level equivalence; the perfect-square reading is the
arithmetic of `√ρ · n`. -/
theorem boundary_lattice_iff_sqrtRate_mul_card_mem {deg : ℕ} {domain : ι ↪ F} {δ : ℝ≥0}
    (hδeq : δ = 1 - ReedSolomon.sqrtRate deg domain)
    (hsqrt_le : ReedSolomon.sqrtRate deg domain ≤ 1) :
    ((Nat.floor (δ * Fintype.card ι) : ℝ≥0) = δ * Fintype.card ι)
      ↔ ∃ m : ℕ, ReedSolomon.sqrtRate deg domain * Fintype.card ι
          = (Fintype.card ι : ℝ≥0) - (m : ℝ≥0) ∧ (m : ℝ≥0) ≤ Fintype.card ι := by
  subst hδeq
  set s : ℝ≥0 := ReedSolomon.sqrtRate deg domain with hs
  set n : ℝ≥0 := (Fintype.card ι : ℝ≥0) with hn
  have hsn_le : s * n ≤ n := by
    calc s * n ≤ 1 * n := by gcongr
      _ = n := one_mul n
  -- `(1 − s) · n = n − s·n`.
  have hdistrib : (1 - s) * n = n - s * n := by
    rw [tsub_mul, one_mul]
  constructor
  · intro hfloor
    -- `δ·n = n − s·n` is an integer `j`; take `m := n − j` so `s·n = n − m`.
    refine ⟨Nat.floor ((1 - s) * n), ?_, ?_⟩
    · -- `s·n = n − (1−s)·n`.
      rw [hfloor, hdistrib]
      rw [tsub_tsub_cancel_of_le hsn_le]
    · rw [hdistrib]
      calc (↑⌊n - s * n⌋₊ : ℝ≥0) ≤ n - s * n := Nat.floor_le (by positivity)
        _ ≤ n := tsub_le_self
  · rintro ⟨m, hm, hmle⟩
    -- `s·n = n − m` ⇒ `(1−s)·n = m`, an integer, so its floor equals itself.
    have hval : (1 - s) * n = (m : ℝ≥0) := by
      rw [hdistrib, hm, tsub_tsub_cancel_of_le hmle]
    rw [hval, Nat.floor_natCast]

omit [DecidableEq ι] [Fintype F] [DecidableEq F] in
/-- **Square identity behind the boundary lattice endpoint.**  In the usual `deg ≤ |ι|`
Reed–Solomon range, the square-root scale appearing in the lattice branch satisfies
`(sqrtRate · |ι|)^2 = deg · |ι|`.  Thus integrality of the square-root scale is exactly the
arithmetic source of the perfect-square endpoint described in the boundary split. -/
theorem sqrtRate_mul_card_sq_eq_deg_mul_card {deg : ℕ} {domain : ι ↪ F}
    (hdeg : deg ≤ Fintype.card ι) :
    (ReedSolomon.sqrtRate deg domain * Fintype.card ι) ^ 2
      = ((deg * Fintype.card ι : ℕ) : ℝ≥0) := by
  have hrate : (LinearCode.rate (ReedSolomon.code domain deg) : ℝ≥0)
      = (deg : ℝ≥0) / (Fintype.card ι : ℝ≥0) := by
    simpa [NNRat.cast_div, NNRat.cast_natCast] using
      congrArg (fun x : ℚ≥0 => (x : ℝ≥0))
        (ReedSolomon.rateOfLinearCode_eq_div' (F := F) (α := domain) hdeg)
  rw [ReedSolomon.sqrtRate, hrate, mul_pow, NNReal.sq_sqrt]
  have hn : (Fintype.card ι : ℝ≥0) ≠ 0 := by
    exact_mod_cast (Fintype.card_ne_zero (α := ι))
  field_simp [hn]
  norm_num

omit [DecidableEq ι] [Fintype F] [DecidableEq F] in
/-- **Perfect-square witness for the lattice endpoint.**  If the boundary square-root scale
`sqrtRate · |ι|` is an integer, then `deg · |ι|` is a Nat square. -/
theorem isSquare_deg_mul_card_of_sqrtRate_mul_card_mem {deg : ℕ} {domain : ι ↪ F}
    (hdeg : deg ≤ Fintype.card ι)
    (hmem : ∃ m : ℕ, ReedSolomon.sqrtRate deg domain * Fintype.card ι = (m : ℝ≥0)) :
    IsSquare (deg * Fintype.card ι) := by
  rcases hmem with ⟨m, hm⟩
  refine ⟨m, ?_⟩
  apply Nat.cast_injective (R := ℝ≥0)
  calc
    ((deg * Fintype.card ι : ℕ) : ℝ≥0)
        = (ReedSolomon.sqrtRate deg domain * Fintype.card ι) ^ 2 := by
            rw [sqrtRate_mul_card_sq_eq_deg_mul_card (domain := domain) hdeg]
    _ = (m : ℝ≥0) ^ 2 := by rw [hm]
    _ = (m * m : ℕ) := by norm_num [pow_two]

omit [DecidableEq ι] [Fintype F] [DecidableEq F] in
/-- **Converse perfect-square direction.**  If `deg · |ι|` is a Nat square, then the boundary
square-root scale `sqrtRate · |ι|` is integral. -/
theorem sqrtRate_mul_card_mem_of_isSquare_deg_mul_card {deg : ℕ} {domain : ι ↪ F}
    (hdeg : deg ≤ Fintype.card ι)
    (hsq : IsSquare (deg * Fintype.card ι)) :
    ∃ m : ℕ, ReedSolomon.sqrtRate deg domain * Fintype.card ι = (m : ℝ≥0) := by
  rcases hsq with ⟨m, hm⟩
  refine ⟨m, ?_⟩
  have hsqeq : (ReedSolomon.sqrtRate deg domain * Fintype.card ι) ^ 2
      = (m : ℝ≥0) ^ 2 := by
    rw [sqrtRate_mul_card_sq_eq_deg_mul_card (domain := domain) hdeg]
    rw [hm]
    norm_num [pow_two]
  have hsqrt := congrArg NNReal.sqrt hsqeq
  simpa [NNReal.sqrt_sq] using hsqrt

omit [DecidableEq ι] [Fintype F] [DecidableEq F] in
/-- **Perfect-square characterization of the lattice arithmetic.**  In the usual
Reed–Solomon range `deg ≤ |ι|`, the square-root scale `sqrtRate · |ι|` is integral iff
`deg · |ι|` is a Nat square. -/
theorem sqrtRate_mul_card_mem_iff_isSquare_deg_mul_card {deg : ℕ} {domain : ι ↪ F}
    (hdeg : deg ≤ Fintype.card ι) :
    (∃ m : ℕ, ReedSolomon.sqrtRate deg domain * Fintype.card ι = (m : ℝ≥0))
      ↔ IsSquare (deg * Fintype.card ι) := by
  constructor
  · exact isSquare_deg_mul_card_of_sqrtRate_mul_card_mem (domain := domain) hdeg
  · exact sqrtRate_mul_card_mem_of_isSquare_deg_mul_card (domain := domain) hdeg

omit [Nonempty ι] [DecidableEq ι] [Fintype F] [DecidableEq F] in
/-- **Complement-integrality is ordinary integrality for the boundary square-root scale.**  The
floor-lattice theorem naturally records `sqrtRate · |ι|` as the complement of an integer in
`|ι|`; this lemma converts that witness to the direct integrality surface used by the
perfect-square characterization, and conversely. -/
theorem sqrtRate_mul_card_complement_mem_iff_mem {deg : ℕ} {domain : ι ↪ F}
    (hsqrt_le : ReedSolomon.sqrtRate deg domain ≤ 1) :
    (∃ j : ℕ, ReedSolomon.sqrtRate deg domain * Fintype.card ι
          = (Fintype.card ι : ℝ≥0) - (j : ℝ≥0) ∧
        (j : ℝ≥0) ≤ Fintype.card ι)
      ↔ ∃ m : ℕ, ReedSolomon.sqrtRate deg domain * Fintype.card ι = (m : ℝ≥0) := by
  constructor
  · rintro ⟨j, hj, hjle⟩
    have hjle_nat : j ≤ Fintype.card ι := by exact_mod_cast hjle
    refine ⟨Fintype.card ι - j, ?_⟩
    rw [hj]
    norm_num [Nat.cast_sub hjle_nat]
  · rintro ⟨m, hm⟩
    have hsqrt_card_le :
        ReedSolomon.sqrtRate deg domain * Fintype.card ι ≤ (Fintype.card ι : ℝ≥0) := by
      calc
        ReedSolomon.sqrtRate deg domain * Fintype.card ι
            ≤ 1 * (Fintype.card ι : ℝ≥0) := by gcongr
        _ = (Fintype.card ι : ℝ≥0) := one_mul _
    have hmle_nn : (m : ℝ≥0) ≤ Fintype.card ι := by
      simpa [hm] using hsqrt_card_le
    have hmle_nat : m ≤ Fintype.card ι := by exact_mod_cast hmle_nn
    refine ⟨Fintype.card ι - m, ?_, ?_⟩
    · rw [hm]
      have hle : Fintype.card ι - m ≤ Fintype.card ι := Nat.sub_le _ _
      have hcast :
          (((Fintype.card ι - (Fintype.card ι - m) : ℕ) : ℝ≥0))
            = (Fintype.card ι : ℝ≥0) - ((Fintype.card ι - m : ℕ) : ℝ≥0) := by
        norm_num [Nat.cast_sub hle]
      rw [← hcast, Nat.sub_sub_self hmle_nat]
    · exact_mod_cast Nat.sub_le (Fintype.card ι) m

omit [DecidableEq ι] [Fintype F] in
/-- **Perfect-square characterization of the boundary floor-lattice condition.**  At the exact
Johnson boundary `δ = 1 - sqrtRate`, in the Reed-Solomon range `deg ≤ |ι|`, the endpoint is a
`1/|ι|` lattice point iff `deg · |ι|` is a Nat square. -/
theorem boundary_lattice_iff_isSquare_deg_mul_card {deg : ℕ} {domain : ι ↪ F} {δ : ℝ≥0}
    (hδeq : δ = 1 - ReedSolomon.sqrtRate deg domain)
    (hsqrt_le : ReedSolomon.sqrtRate deg domain ≤ 1)
    (hdeg : deg ≤ Fintype.card ι) :
    ((Nat.floor (δ * Fintype.card ι) : ℝ≥0) = δ * Fintype.card ι)
      ↔ IsSquare (deg * Fintype.card ι) := by
  rw [boundary_lattice_iff_sqrtRate_mul_card_mem (domain := domain) hδeq hsqrt_le,
    sqrtRate_mul_card_complement_mem_iff_mem (domain := domain) hsqrt_le,
    sqrtRate_mul_card_mem_iff_isSquare_deg_mul_card (domain := domain) hdeg]

omit [DecidableEq ι] [Fintype F] in
/-- **Non-square endpoint is genuinely non-lattice.**  At the exact Johnson boundary, if
`deg · |ι|` is not a Nat square, then `δ · |ι|` cannot be an integer; equivalently the floor lies
strictly below the real value. -/
theorem boundary_not_lattice_of_not_isSquare_deg_mul_card {deg : ℕ} {domain : ι ↪ F}
    {δ : ℝ≥0}
    (hδeq : δ = 1 - ReedSolomon.sqrtRate deg domain)
    (hsqrt_le : ReedSolomon.sqrtRate deg domain ≤ 1)
    (hdeg : deg ≤ Fintype.card ι)
    (hNotSquare : ¬ IsSquare (deg * Fintype.card ι)) :
    (Nat.floor (δ * Fintype.card ι) : ℝ≥0) < δ * Fintype.card ι := by
  have hiff := boundary_lattice_iff_isSquare_deg_mul_card
    (domain := domain) hδeq hsqrt_le hdeg
  have hne :
      (Nat.floor (δ * Fintype.card ι) : ℝ≥0) ≠ δ * Fintype.card ι := by
    intro hfloor
    exact hNotSquare (hiff.mp hfloor)
  exact lt_of_le_of_ne (Nat.floor_le (zero_le _)) hne

omit [DecidableEq ι] in
/-- **Closed boundary residual in the non-square case.**  If the exact Johnson endpoint is not a
`1/|ι|` lattice point, expressed arithmetically as `¬ IsSquare (deg · |ι|)`, then the boundary
residual follows from the strict-interior supply alone.  Thus the only extra boundary datum still
needed by the quantization split is the genuine square-lattice case. -/
theorem boundaryCardResidual_of_not_isSquare_deg_mul_card {k deg : ℕ} {domain : ι ↪ F}
    {δ : ℝ≥0}
    (hδeq : δ = 1 - ReedSolomon.sqrtRate deg domain)
    (hsqrt_le : ReedSolomon.sqrtRate deg domain ≤ 1)
    (hdeg : deg ≤ Fintype.card ι)
    (hNotSquare : ¬ IsSquare (deg * Fintype.card ι))
    (hStrict :
      BoundaryCardStrictInteriorResidual (k := k) (deg := deg) (domain := domain) (δ := δ)) :
    BoundaryCardResidual (k := k) (deg := deg) (domain := domain) (δ := δ) :=
  boundaryCardResidual_of_not_lattice (deg := deg) (domain := domain)
    (boundary_not_lattice_of_not_isSquare_deg_mul_card
      (domain := domain) hδeq hsqrt_le hdeg hNotSquare)
    hStrict

omit [DecidableEq ι] in
/-- The boundary-probability residual follows from the strict-interior supply at non-square
Johnson endpoints. -/
theorem boundaryProbabilityResidual_of_not_isSquare_deg_mul_card {k deg : ℕ}
    {domain : ι ↪ F} {δ : ℝ≥0} [NeZero deg]
    (hδle : δ ≤ 1 - ReedSolomon.sqrtRate deg domain)
    (hδeq : δ = 1 - ReedSolomon.sqrtRate deg domain)
    (hsqrt_le : ReedSolomon.sqrtRate deg domain ≤ 1)
    (hdeg : deg ≤ Fintype.card ι)
    (hNotSquare : ¬ IsSquare (deg * Fintype.card ι))
    (hStrict :
      BoundaryCardStrictInteriorResidual (k := k) (deg := deg) (domain := domain) (δ := δ)) :
    ProximityGap.BoundaryProbabilityResidual
      (k := k) (deg := deg) (domain := domain) (δ := δ) := by
  exact ProximityGap.boundaryProbabilityResidual_of_boundaryCardResidual
    (deg := deg) (domain := domain) (δ := δ) hδle
    (boundaryCardResidual_of_not_isSquare_deg_mul_card
      (deg := deg) (domain := domain) hδeq hsqrt_le hdeg hNotSquare hStrict)

omit [DecidableEq ι] in
/-- **Closed boundary residual in the square-lattice case.**  If the exact Johnson endpoint is a
`1/|ι|` lattice point, expressed arithmetically as `IsSquare (deg · |ι|)`, then the boundary
residual follows directly from the isolated lattice endpoint residual.  Unlike the mixed
quantization wrapper, this square-specific front door does not require the strict-interior
supply. -/
theorem boundaryCardResidual_of_isSquare_deg_mul_card {k deg : ℕ} {domain : ι ↪ F}
    {δ : ℝ≥0}
    (hsqrt_le : ReedSolomon.sqrtRate deg domain ≤ 1)
    (hdeg : deg ≤ Fintype.card ι)
    (hSquare : IsSquare (deg * Fintype.card ι))
    (hLattice :
      BoundaryCardLatticeResidual (k := k) (deg := deg) (domain := domain) (δ := δ)) :
    BoundaryCardResidual (k := k) (deg := deg) (domain := domain) (δ := δ) := by
  intro hk u hδeq hcardPos
  have hfloor :
      (Nat.floor (δ * Fintype.card ι) : ℝ≥0) = δ * Fintype.card ι :=
    (boundary_lattice_iff_isSquare_deg_mul_card
      (domain := domain) hδeq hsqrt_le hdeg).mpr hSquare
  exact hLattice hk u hδeq hfloor hcardPos

omit [DecidableEq ι] in
/-- The boundary-probability residual follows directly from the isolated lattice residual at
square Johnson endpoints. -/
theorem boundaryProbabilityResidual_of_isSquare_deg_mul_card {k deg : ℕ}
    {domain : ι ↪ F} {δ : ℝ≥0} [NeZero deg]
    (hδle : δ ≤ 1 - ReedSolomon.sqrtRate deg domain)
    (hsqrt_le : ReedSolomon.sqrtRate deg domain ≤ 1)
    (hdeg : deg ≤ Fintype.card ι)
    (hSquare : IsSquare (deg * Fintype.card ι))
    (hLattice :
      BoundaryCardLatticeResidual (k := k) (deg := deg) (domain := domain) (δ := δ)) :
    ProximityGap.BoundaryProbabilityResidual
      (k := k) (deg := deg) (domain := domain) (δ := δ) := by
  exact ProximityGap.boundaryProbabilityResidual_of_boundaryCardResidual
    (deg := deg) (domain := domain) (δ := δ) hδle
    (boundaryCardResidual_of_isSquare_deg_mul_card
      (deg := deg) (domain := domain) hsqrt_le hdeg hSquare hLattice)

/-! ## The strengthened keystone corollary consuming the isolated lattice residual -/

omit [DecidableEq ι] in
/-- **[BCIKS20] Theorem 1.5, with the boundary residual reduced by quantization.**

This is `ProximityGap.correlatedAgreement_affine_curves` re-stated so that the closed-boundary
input is no longer the full `BoundaryCardResidual` but the *strictly smaller* surface produced by
the quantization analysis:

* `hStrictCoeff` — the strict Johnson §5 extraction (`StrictCoeffPolysResidual`), unchanged;
* `hStrict` — the strict-interior analogue of the boundary obligation (positive good set ⟹
  `jointAgreement`) at radii `δ' < δ`, the regime `errorBound > 0` where the §5 quantitative
  threshold is available; this is what the non-lattice bulk of the boundary reduces to;
* `hLattice` — the precisely isolated genuine `BoundaryCardLatticeResidual` (only the
  `1/n`-lattice-point boundary, i.e. `deg·n` a perfect square).

The boundary `BoundaryCardResidual` is reconstructed from `hStrict` and `hLattice` via
`boundaryCardResidual_of_lattice_residual` and fed to the keystone.  Compared to the bare keystone,
this corollary moves the entire non-lattice boundary off the measure-zero boundary into the strict
interior, leaving `hLattice` as the only genuinely boundary-specific datum. -/
theorem correlatedAgreement_affine_curves_of_lattice_residual {k deg : ℕ} {domain : ι ↪ F}
    {δ : ℝ≥0} [NeZero deg] [DecidableEq ι]
    (hStrictCoeff :
      ProximityGap.StrictCoeffPolysResidual (k := k) (deg := deg) (domain := domain) (δ := δ))
    (hStrict : ∀ (u : WordStack F (Fin (k + 1)) ι) (δ' : ℝ≥0),
      δ' < δ →
      Nat.floor (δ' * Fintype.card ι) = Nat.floor (δ * Fintype.card ι) →
      0 < (RS_goodCoeffsCurve (k := k) (deg := deg) (domain := domain) u δ').card →
      jointAgreement (C := ReedSolomon.code domain deg) (δ := δ') (W := u))
    (hLattice : BoundaryCardLatticeResidual (k := k) (deg := deg) (domain := domain) (δ := δ))
    (hδ : δ ≤ 1 - ReedSolomon.sqrtRate deg domain) :
    δ_ε_correlatedAgreementCurves (k := k) (A := F) (F := F) (ι := ι)
      (C := ReedSolomon.code domain deg) (δ := δ) (ε := errorBound δ deg domain) := by
  classical
  exact ProximityGap.correlatedAgreement_affine_curves_of_boundaryCardResidual
    (deg := deg) (domain := domain) (δ := δ) hStrictCoeff
    (boundaryCardResidual_of_lattice_residual (deg := deg) (domain := domain) hLattice hStrict)
    hδ

/-- [BCIKS20] Theorem 1.5 using the packaged boundary quantization residuals.  This is equivalent
to `correlatedAgreement_affine_curves_of_lattice_residual`, but makes the exact remaining boundary
surface a single reusable input. -/
theorem correlatedAgreement_affine_curves_of_quantization_residuals {k deg : ℕ} {domain : ι ↪ F}
    {δ : ℝ≥0} [NeZero deg] [DecidableEq ι]
    (hStrictCoeff :
      ProximityGap.StrictCoeffPolysResidual (k := k) (deg := deg) (domain := domain) (δ := δ))
    (hBoundary :
      BoundaryCardQuantizationResiduals (k := k) (deg := deg) (domain := domain) (δ := δ))
    (hδ : δ ≤ 1 - ReedSolomon.sqrtRate deg domain) :
    δ_ε_correlatedAgreementCurves (k := k) (A := F) (F := F) (ι := ι)
      (C := ReedSolomon.code domain deg) (δ := δ) (ε := errorBound δ deg domain) := by
  classical
  exact correlatedAgreement_affine_curves_of_lattice_residual
    (deg := deg) (domain := domain) (δ := δ)
    hStrictCoeff hBoundary.strictInterior hBoundary.lattice hδ

omit [DecidableEq ι] in
/-- [BCIKS20] Theorem 1.5 at non-square Johnson endpoints.  This is the direct curve-facing form
of the quantization split away from the exact square-lattice branch: the closed boundary input is
recovered from the strict-interior supply and `¬ IsSquare (deg · |ι|)`. -/
theorem correlatedAgreement_affine_curves_of_not_isSquare_deg_mul_card {k deg : ℕ}
    {domain : ι ↪ F} {δ : ℝ≥0} [NeZero deg]
    (hStrictCoeff :
      ProximityGap.StrictCoeffPolysResidual (k := k) (deg := deg) (domain := domain) (δ := δ))
    (hStrict :
      BoundaryCardStrictInteriorResidual (k := k) (deg := deg) (domain := domain) (δ := δ))
    (hδ : δ ≤ 1 - ReedSolomon.sqrtRate deg domain)
    (hδeq : δ = 1 - ReedSolomon.sqrtRate deg domain)
    (hsqrt_le : ReedSolomon.sqrtRate deg domain ≤ 1)
    (hdeg : deg ≤ Fintype.card ι)
    (hNotSquare : ¬ IsSquare (deg * Fintype.card ι)) :
    δ_ε_correlatedAgreementCurves (k := k) (A := F) (F := F) (ι := ι)
      (C := ReedSolomon.code domain deg) (δ := δ) (ε := errorBound δ deg domain) := by
  classical
  exact ProximityGap.correlatedAgreement_affine_curves_of_boundaryCardResidual
    (deg := deg) (domain := domain) (δ := δ) hStrictCoeff
    (boundaryCardResidual_of_not_isSquare_deg_mul_card
      (deg := deg) (domain := domain) hδeq hsqrt_le hdeg hNotSquare hStrict)
    hδ

omit [DecidableEq ι] in
/-- [BCIKS20] Theorem 1.5 at square Johnson endpoints.  This is the curve-facing counterpart of
`correlatedAgreement_affine_curves_of_not_isSquare_deg_mul_card`: once the endpoint is known to be
the exact square-lattice branch, the boundary input is exactly the isolated
`BoundaryCardLatticeResidual`, with no strict-subradius producer required. -/
theorem correlatedAgreement_affine_curves_of_isSquare_deg_mul_card {k deg : ℕ}
    {domain : ι ↪ F} {δ : ℝ≥0} [NeZero deg]
    (hStrictCoeff :
      ProximityGap.StrictCoeffPolysResidual (k := k) (deg := deg) (domain := domain) (δ := δ))
    (hLattice :
      BoundaryCardLatticeResidual (k := k) (deg := deg) (domain := domain) (δ := δ))
    (hδ : δ ≤ 1 - ReedSolomon.sqrtRate deg domain)
    (hsqrt_le : ReedSolomon.sqrtRate deg domain ≤ 1)
    (hdeg : deg ≤ Fintype.card ι)
    (hSquare : IsSquare (deg * Fintype.card ι)) :
    δ_ε_correlatedAgreementCurves (k := k) (A := F) (F := F) (ι := ι)
      (C := ReedSolomon.code domain deg) (δ := δ) (ε := errorBound δ deg domain) := by
  classical
  exact ProximityGap.correlatedAgreement_affine_curves_of_boundaryCardResidual
    (deg := deg) (domain := domain) (δ := δ) hStrictCoeff
    (boundaryCardResidual_of_isSquare_deg_mul_card
      (deg := deg) (domain := domain) hsqrt_le hdeg hSquare hLattice)
    hδ

end BoundaryCardResidual

end ArkLib

/-! ## Axiom audit — every declaration must rest only on `[propext, Classical.choice, Quot.sound]`,
with no `sorry`/`admit`/`axiom`/`native_decide`. -/
#print axioms ArkLib.BoundaryCardResidual.goodCoeffsCurve_eq_of_floor_eq
#print axioms ArkLib.BoundaryCardResidual.jointAgreement_iff_of_floor_eq
#print axioms ArkLib.BoundaryCardResidual.exists_lt_floor_eq_of_floor_lt
#print axioms ArkLib.BoundaryCardResidual.BoundaryCardStrictInteriorResidual
#print axioms ArkLib.BoundaryCardResidual.boundaryCardResidual_of_not_lattice
#print axioms ArkLib.BoundaryCardResidual.BoundaryCardLatticeResidual
#print axioms ArkLib.BoundaryCardResidual.BoundaryCardLatticeData
#print axioms ArkLib.BoundaryCardResidual.boundaryCardLatticeResidual_zero
#print axioms ArkLib.BoundaryCardResidual.boundaryCardLatticeData_zero
#print axioms ArkLib.BoundaryCardResidual.BoundaryCardQuantizationResiduals
#print axioms ArkLib.BoundaryCardResidual.BoundaryCardQuantizationResiduals.ofStrictInterior_zero
#print axioms ArkLib.BoundaryCardResidual.BoundaryCardQuantizationResiduals.strictInterior
#print axioms ArkLib.BoundaryCardResidual.BoundaryCardQuantizationResiduals.lattice
#print axioms ArkLib.BoundaryCardResidual.BoundaryCardQuantizationResiduals.toBoundaryCardResidual
#print axioms ArkLib.BoundaryCardResidual.boundaryCardResidual_of_lattice_residual
#print axioms ArkLib.BoundaryCardResidual.boundaryProbabilityResidual_of_lattice_residual
#print axioms ArkLib.BoundaryCardResidual.BoundaryCardQuantizationResiduals.toBoundaryProbabilityResidual
#print axioms ArkLib.BoundaryCardResidual.boundary_lattice_iff_sqrtRate_mul_card_mem
#print axioms ArkLib.BoundaryCardResidual.sqrtRate_mul_card_sq_eq_deg_mul_card
#print axioms ArkLib.BoundaryCardResidual.isSquare_deg_mul_card_of_sqrtRate_mul_card_mem
#print axioms ArkLib.BoundaryCardResidual.sqrtRate_mul_card_mem_of_isSquare_deg_mul_card
#print axioms ArkLib.BoundaryCardResidual.sqrtRate_mul_card_mem_iff_isSquare_deg_mul_card
#print axioms ArkLib.BoundaryCardResidual.sqrtRate_mul_card_complement_mem_iff_mem
#print axioms ArkLib.BoundaryCardResidual.boundary_lattice_iff_isSquare_deg_mul_card
#print axioms ArkLib.BoundaryCardResidual.boundary_not_lattice_of_not_isSquare_deg_mul_card
#print axioms ArkLib.BoundaryCardResidual.boundaryCardResidual_of_not_isSquare_deg_mul_card
#print axioms ArkLib.BoundaryCardResidual.boundaryProbabilityResidual_of_not_isSquare_deg_mul_card
#print axioms ArkLib.BoundaryCardResidual.boundaryCardResidual_of_isSquare_deg_mul_card
#print axioms ArkLib.BoundaryCardResidual.boundaryProbabilityResidual_of_isSquare_deg_mul_card
#print axioms ArkLib.BoundaryCardResidual.correlatedAgreement_affine_curves_of_lattice_residual
#print axioms ArkLib.BoundaryCardResidual.correlatedAgreement_affine_curves_of_quantization_residuals
#print axioms
  ArkLib.BoundaryCardResidual.correlatedAgreement_affine_curves_of_not_isSquare_deg_mul_card
#print axioms
  ArkLib.BoundaryCardResidual.correlatedAgreement_affine_curves_of_isSquare_deg_mul_card

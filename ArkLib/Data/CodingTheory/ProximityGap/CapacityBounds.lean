/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexander Hicks
-/

import ArkLib.Data.CodingTheory.ProximityGap.Errors
import ArkLib.Data.CodingTheory.ReedSolomon
import ArkLib.Data.CodingTheory.Basic.Entropy
import ArkLib.Data.CodingTheory.HammingBallVolume
import ArkLib.Data.CodingTheory.SubspaceDesign
import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# Capacity-regime upper and lower bounds for ε_ca and ε_mca (ABF26 §4.2, §4.3)

External-admit *statements* for the §4 results that bound `ε_ca` and `ε_mca` from above
in the Johnson regime and from below in the capacity regime. From
*Open Problems in List Decoding and Correlated Agreement* (Arnon-Boneh-Fenzi,
April 8, 2026), §§4.2.2 and 4.3.

These theorems sit immediately above the Grand MCA Challenge in ABF26 §1: each one
either produces a witness `δ_C*` for `ε_mca(C, δ_C*) ≤ ε*` (upper bounds), or rules out
witnesses above a given threshold (lower bounds). They are mostly cited from external
papers ([GKL24], [BGKS20], [BCHKS25], [KK25], [CS25], [DG25], etc.); we state them
here in ArkLib's `ε_ca` / `ε_mca` form and admit the proofs as external results.

## Numeric bounds in `ENNReal`

The RHS of each upper bound is a real-valued numeric expression. To match the
`ENNReal`-valued return type of `epsCA` / `epsMCA`, we wrap the bound with
`ENNReal.ofReal`. The lower bounds use the same wrapping for symmetry. This keeps
the bounds well-defined even when the bracketing real expression is negative or
exceeds 1 (in which case `ENNReal.ofReal` either truncates to `0` or stays in `[0, ∞]`).

## Proximity-radius coercion (`ℝ → ℝ≥0`)

Several theorems take a real-valued proximity radius like `1 − √x` or `1 − ρ − η` and
pass it to `ε_mca` / `ε_ca` (which require `ℝ≥0`). We use `x.toNNReal`. Each occurrence
is either:

- Provably non-negative under the theorem's hypotheses (the standard case — e.g.
  T4.18 has `(1 - (1 - 15/16)^{1/2}) = 3/4 ≥ 0` by direct computation).
- Or aligned with the paper's stated regime so that the truncation to `0` matches
  the trivial / vacuous case of the bound (e.g. T4.13's `1 - τ(t+1) - 3/(2t)`
  truncates outside the regime where the bound is meaningfully informative).

## Main statements (external admits)

### General linear codes

- `linear_epsMCA_1_5_johnson_gkl24` — ABF26 Theorem 4.11 [GKL24 Thm 3]: `ε_mca` bound
  in the "1.5-Johnson" regime `δ ≤ 1 - ∛(1 - δ_min(C) + η)`.
- `linear_epsCA_1_5_johnson_bgks20` — ABF26 Theorem 4.11 [BGKS20 Lem 3.2]: `ε_ca` bound
  with proximity loss `η`, valid in the same 1.5-Johnson regime.

### Reed-Solomon codes

- `rs_epsMCA_johnson_range_bchks25` — ABF26 Theorem 4.12 [BCHKS25 Thm 4.6]: explicit
  `ε_mca` bound for RS codes in the Johnson range `δ < 1 - √ρ₊ - η`, where
  `ρ₊ := ρ + 1/n`.

### Lower bounds near capacity

- `rs_epsCA_lower_capacity_bchks25_kk25` — ABF26 Theorem 4.16 [BCHKS25, KK25]:
  existence of RS codes for which `ε_ca` at distance `1 - ρ - slack` is at
  least `n^c / |F|` (where the `slack` is an existentially-bound `Θ(1/log n)`-shaped
  parameter; we expose it explicitly because Lean lacks a generic `Θ` notation).
- `rs_epsCA_breakdown_cs25` — ABF26 Theorem 4.17 [CS25 Cor 1]: complete CA breakdown
  for RS codes when the rate sits inside an entropy-defined band.
- `rs_epsCA_johnson_jump_bchks25` — ABF26 Theorem 4.18 [BCHKS25 Cor 1.7]: jump in
  `ε_ca` exactly at the Johnson bound, witnessed by characteristic-2 RS codes.
- `linear_epsCA_ge_sampling_dg25` — ABF26 Lemma 4.19 [DG25 Thm 2.5]: `ε_ca(C, δ)`
  is bounded below by `((q-1)/q) · Pr_{u}[Δ(u, C) ≤ δ]`.

### Subspace-design / FRS MCA up to capacity (§4.2.2)

- `subspaceDesign_epsMCA_gg25` — ABF26 T4.13 [GG25 Cor 4.9]: τ-subspace-design code
  has explicit `ε_mca` bound at `1 - τ(t+1) - 3/(2t)`.
- `frs_epsMCA_capacity_gg25` — ABF26 T4.14 [GG25 Cor 4.10]: folded RS up to capacity
  has `ε_mca(C, 1 - ρ - η) ≤ O(n/(η|F|) + 1/(η³|F|))`.

## Deferred statements

- ABF26 Theorem 4.15 [GG25 Thm 5.15] (random RS MCA up to capacity) — blocked on a
  uniform distribution over size-`n` subsets of `F`.

These are tracked in `docs/kb/ABF26_PLAN.md` §7 and will be stated alongside the corresponding
code-family definitions in Phase 3.

## Disposition ledger (issue #48)

Classification of every statement in this file.  *DIRECT PORT* = principal external paper
result, admitted as a `Prop`-valued statement; *DERIVED COROLLARY* = blocked solely on other
named statements, with the corollary content checked in-tree; *CONSTRUCTION* = existence of a
witness code/family (lower-bound direction; not dischargeable by any in-tree upper-bound
machinery); *SHADOW* = placeholder pending a canonical formalization elsewhere.

*DIRECT PORTs* (principal external paper results, admitted as `Prop`-valued statements):

- `linear_epsMCA_1_5_johnson_gkl24` (T4.11.1) — ∛-radius list count absent in-tree (#49
  tracks the √-radius Johnson side).
- `linear_epsCA_1_5_johnson_bgks20` (T4.11.2) — η-margin fold/interleave union bound absent.
- `rs_epsCA_bchks25_item2` (T4.9.2) — BCHKS25 RS interpolation count absent.
- `rs_epsMCA_johnson_range_bchks25` (T4.12) — m-multiplicity RS interpolation absent (#10
  tracks the Hab25 variant).
- `linear_epsCA_ge_sampling_dg25` (L4.19) — covering-radius sampling identity absent.
- `subspaceDesign_epsMCA_gg25` (T4.13) — GG25 line-stitching/list-decoding pipeline; its
  list-decoding input is tracked by #53.

*DERIVED COROLLARIES* (blocked solely on other named statements; corollary content checked
in-tree):

- `rs_epsCA_small_loss_r4_10` (R4.10) — solely on T4.9.2; checked reduction
  `rs_epsCA_small_loss_r4_10_of_residuals` + repaired floor side condition in-tree.
- `frs_epsMCA_capacity_gg25` (T4.14) — solely on T4.13 + T2.18; checked reduction
  `frs_epsMCA_capacity_gg25_of_residuals` in-tree.

*CONSTRUCTIONS* (existence of a witness code/family; lower-bound direction, not
dischargeable by any in-tree upper-bound machinery):

- `rs_epsCA_lower_capacity_bchks25_kk25` (T4.16) — capacity-regime bad-code witness (#39
  tracks the exact middle-band count).
- `rs_epsCA_breakdown_cs25` (T4.17) — `≥ 1` half needs the qEntropy ↔ RS-ball-count bridge;
  the `≤ 1` half is trivial.
- `rs_epsCA_johnson_jump_bchks25` (T4.18) — char-2 Johnson-jump witness family.

*SHADOW* (placeholder pending a canonical formalization elsewhere):

- `subspaceDesign_epsCA_curves_polynomial_generators_bcgm25` — restate via `IsMCAGenerator`
  once PR #489 lands; do not prove as-is.

**No statement in this file is disproven.**  The two repaired items are R4.10 (the naive
`0 < γ < 1` floor-collapse shortcut is refuted in-tree by
`r4_10_floor_collapse_hypotheses_insufficient`; the corrected reduction carries an explicit
no-boundary-crossing hypothesis) and the BCGM25 entry (deliberately a curve-CA shadow of the
real mutual-correlated-agreement statement; see its docstring).  Related *statement-level*
breakdowns of capacity-reading conjectures (CS25/BCHKS25 "capacity false" results) are
recorded here as the *constructions* T4.16–T4.18 — they are inputs that bound the Grand MCA
threshold from above, not defects of these statements.

## Feeders into the Grand MCA witnesses (priority per issue #48)

The bridges `GrandChallenges.MCALowerWitness.ofLe` / `MCAUpperWitness.ofGt` consume these
statements directly:

- **Lower witnesses (`δ* ≥ δ`, via `MCALowerWitness.ofLe`)** — the `ε_mca` *upper* bounds:
  T4.13 (`subspaceDesign_epsMCA_gg25`), T4.14 (`frs_epsMCA_capacity_gg25`) for the
  subspace-design/FRS route up to capacity, and T4.12 (`rs_epsMCA_johnson_range_bchks25`)
  for plain RS in the Johnson range; T4.11.1 for general linear codes at the 1.5-Johnson
  radius.  These are the highest-priority ports: each one immediately moves the faithful
  lattice-threshold bracket (`GrandChallengesLattice`, `MCAPlateauWindow`).
- **Upper witnesses (`δ* ≤ δ`, via `MCAUpperWitness.ofGt` and `ε_ca ≤ ε_mca`)** — the
  capacity-regime *lower* bounds: T4.16 (`rs_epsCA_lower_capacity_bchks25_kk25`),
  T4.17 (`rs_epsCA_breakdown_cs25`), T4.18 (`rs_epsCA_johnson_jump_bchks25`),
  L4.19 (`linear_epsCA_ge_sampling_dg25`).  In-tree, the unconditional upper-witness side
  is already supplied by the subset-sum constructions (`MCAPlateauWindow`,
  `MCAUpperWitness.ofSubsetSumsCapacityPred`), so these ports refine constants rather than
  unblock the lattice.

Issue cross-links: #48 (this ledger), #39 (radius-one extremal count), #52 (MCAGS
beyond-UDR mass bound), #54 (§3 list-decoding family), #49 (Johnson family), #50 (GGR11
interleaving), #10 (Hab25 bundle), #11 (L4.6 hard direction), #53 (GK16/CZ25
subspace-design inputs).

## References

- [ABF26] Arnon, Boneh, Fenzi. *Open Problems in List Decoding and Correlated Agreement*.
  2026.
- [GKL24] Theorem 3 in their paper.
- [BGKS20] Lemma 3.2 in their paper.
- [BCHKS25] Theorem 4.6 / Corollary 1.7 in their paper.
- [KK25] (cited alongside BCHKS25 in Theorem 4.16).
- [CS25] Corollary 1, source of Theorem 4.17.
- [DG25] Theorem 2.5, source of Lemma 4.19.
-/

set_option linter.unusedFintypeInType false
set_option linter.unusedDecidableInType false
set_option linter.unusedSectionVars false

namespace CodingTheory

open scoped NNReal
open ProximityGap

/-! ## General linear codes — ABF26 §4 1.5-Johnson family ([GKL24], [BGKS20])

Disposition (issue #48): both DIRECT PORTs (∛-radius list count / η-margin union bound
absent in-tree). Lower-witness feeders for the Grand MCA threshold via
`MCALowerWitness.ofLe`. See the file-level disposition ledger. -/

section General

variable {ι : Type} [Fintype ι] [Nonempty ι] [DecidableEq ι]
variable {F : Type} [Field F] [Fintype F] [DecidableEq F]
variable {A : Type} [Fintype A] [DecidableEq A] [AddCommGroup A] [Module F A]

/-- **ABF26 Theorem 4.11, Item 1 [GKL24 Thm 3].** For any linear error-correcting code
`C ⊆ F^n`, parameter `η > 0`, and `δ ≤ 1 - ∛(1 - δ_min(C) + η)`:

  `ε_mca(C, δ) ≤ ((n+6)/η + 2 / (η · (∛(1 - δ_min + η) - √(1 - δ_min + η))) ) · (1/|F|)`

The "1.5-Johnson regime" refers to the fact that `1 - ∛(1 - δ_min)` lies strictly above
the classical Johnson bound `1 - √(1 - δ_min)` and strictly below capacity. The bound is
admitted from the cited paper.

**Implicit hypothesis `η < δ_min`.** For the bound's denominator `∛x − √x` (with
`x := 1 - δ_min + η`) to be strictly positive we need `x < 1`, i.e. `η < δ_min`. The
paper's 1.5-Johnson regime is exactly this `η`-as-slack-below-δ_min picture; without it
the bound becomes vacuous (or numerically infinite) and `δ ≤ 1 − ∛x` may not even
restrict the parameter range. Added as an explicit hypothesis. -/
def linear_epsMCA_1_5_johnson_gkl24
    (C : ModuleCode ι F A) (δ_min η δ : ℝ≥0)
    (_h_δ_min : (δ_min : ℝ) = (Code.minDist (C : Set (ι → A)) : ℝ) / Fintype.card ι)
    (_hη : 0 < η) (_hη_lt_δ_min : η < δ_min)
    (_hδ : (δ : ℝ) ≤ 1 - ((1 - (δ_min : ℝ) + (η : ℝ)) ^ ((1 : ℝ) / 3))) : Prop :=
    epsMCA (F := F) (A := A) ((C : Set (ι → A))) δ ≤
      ENNReal.ofReal
        ((((Fintype.card ι : ℝ) + 6) / η
          + 2 / ((η : ℝ) *
              ((1 - (δ_min : ℝ) + (η : ℝ)) ^ ((1 : ℝ) / 3)
                - (1 - (δ_min : ℝ) + (η : ℝ)) ^ ((1 : ℝ) / 2)))
         ) / (Fintype.card F : ℝ))
  -- Missing ingredient: GKL24's 1.5-Johnson MCA bound for general linear codes. Needs the
  -- ∛-radius list-decoding count (a higher-order Johnson argument giving ≤ ((n+6)/η + …)
  -- agreeing codewords at radius 1-∛(1-δ_min+η)) converted to an epsMCA bound. The cubic-root
  -- Johnson list count is not in-tree (JohnsonBound/ proves only the √-radius / 2nd-moment
  -- form). Genuinely external.

/-- **ABF26 Theorem 4.11, Item 2 [BGKS20 Lem 3.2].** For any linear error-correcting code
`C ⊆ F^n`, parameter `η > 0`, and `δ ≤ 1 - ∛(1 - δ_min(C) + η)`:

  `ε_ca(C, δ_fld := δ, δ_int := δ + η) ≤ 2 / (η² · |F|)`

Same regime as the GKL24 form but stated in CA-with-proximity-loss shape. Tighter when the
GKL24 bound is dominated by its second term. Admitted from the cited paper.

The regime hypothesis `η < δ_min` is shared with Item 1 (the paper presents both bounds
under one regime statement); included here for hypothesis-parity even though Item 2's
RHS `2 / (η² |F|)` is well-defined for any `η > 0`. -/
def linear_epsCA_1_5_johnson_bgks20
    (C : ModuleCode ι F A) (δ_min η δ : ℝ≥0)
    (_h_δ_min : (δ_min : ℝ) = (Code.minDist (C : Set (ι → A)) : ℝ) / Fintype.card ι)
    (_hη : 0 < η) (_hη_lt_δ_min : η < δ_min)
    (_hδ : (δ : ℝ) ≤ 1 - ((1 - (δ_min : ℝ) + (η : ℝ)) ^ ((1 : ℝ) / 3))) : Prop :=
    epsCA (F := F) (A := A) ((C : Set (ι → A))) δ (δ + η) ≤
      ((2 : ENNReal) / ((η : ENNReal) ^ 2 * (Fintype.card F : ENNReal)))
  -- Missing ingredient: BGKS20's CA-with-proximity-loss bound 2/(η²|F|) in the same
  -- 1.5-Johnson regime. The 1/η² shape comes from a two-step (fold then interleave) union
  -- bound over the η-margin; needs the in-tree epsCA-with-(δ,δ+η) proximity-loss decomposition
  -- specialised to the ∛-radius regime, which is not present. Genuinely external.

end General

/-! ## Reed-Solomon codes — ABF26 §4 RS CA/MCA family ([BCHKS25], [KK25], [CS25])

Disposition (issue #48): T4.9.2 / T4.12 are DIRECT PORTs (RS interpolation / multiplicity
counts absent); R4.10 is a DERIVED COROLLARY of T4.9.2 (checked reduction +
no-boundary-crossing floor lemma in-tree); T4.16 / T4.17 / T4.18 are CONSTRUCTIONs
(capacity-regime / Johnson-jump bad-code witnesses), which are *upper*-witness feeders for
the Grand MCA threshold (`MCAUpperWitness`). T4.12 is the priority RS lower-witness feeder.
See the file-level disposition ledger and #39 (radius-one extremal count). -/

section ReedSolomon

variable {ι : Type} [Fintype ι] [Nonempty ι] [DecidableEq ι]
variable {F : Type} [Field F] [Fintype F] [DecidableEq F]

/-- **ABF26 Theorem 4.9 Item 2 [BCHKS25 Theorem 1.3].** Reed-Solomon CA bound in the
`δ_min/3`-to-Johnson regime. Let `C := RS[F, L, k]` with rate `ρ`. For
`δ_min(C)/3 ≤ δ_fld < δ_int`:

  `ε_ca(C, δ_fld, δ_int) ≤`
  `  max{ (1-ρ-δ_fld) / (δ_fld·(1-ρ-2·δ_fld)·|F|), δ_int / ((δ_int-δ_fld)·|F|) }`

Tighter than T4.8 (AHIV17) in the regime `δ_fld ≥ δ_min/3`. Admitted as an external
result. -/
def rs_epsCA_bchks25_item2
    (domain : ι ↪ F) (k : ℕ) (δ_fld δ_int : ℝ≥0)
    (_h_dmin : (Code.minDist ((ReedSolomon.code domain k : Set (ι → F))) : ℝ)
                / Fintype.card ι / 3 ≤ δ_fld)
    (_h_lt : δ_fld < δ_int) : Prop :=
    let n : ℝ := Fintype.card ι
    let ρ : ℝ := k / n
    let bound : ℝ :=
      max ((1 - ρ - δ_fld) / (δ_fld * (1 - ρ - 2 * δ_fld) * Fintype.card F))
          ((δ_int : ℝ) / ((δ_int - δ_fld) * Fintype.card F))
    epsCA (F := F) (A := F) ((ReedSolomon.code domain k : Set (ι → F))) δ_fld δ_int ≤
      ENNReal.ofReal bound
  -- Missing ingredient: BCHKS25's RS CA bound in the δ_min/3-to-Johnson regime. The max{…}
  -- RHS is a two-regime analysis (interpolation term + proximity-loss term) resting on the
  -- BCHKS25 RS interpolation/multiplicity lemmas. BCKHS25/Interpolation.lean supplies the
  -- collinear-proximates engine but not the closed-form (1-ρ-δ)/(δ(1-ρ-2δ)) RS error count.
  -- Genuinely external.

/-- **ABF26 Remark 4.10.** Small-proximity-loss simplification of T4.9.2 via R4.2.
For `δ_int - δ_fld = γ/n` with `γ ∈ (0, 1)` (so that `R4.2` collapses `ε_ca` to its
`δ_int := δ_fld` value):

  `ε_mca(C, δ_fld) = ε_ca(C, δ_fld) = ε_ca(C, δ_fld, δ_fld + γ/n) ≤`
  `  max{ (1-ρ-δ_fld) / (δ_fld·(1-ρ-2·δ_fld)·|F|), (n·δ_fld + γ) / (γ·|F|) }`

The `(n·δ_fld + γ) / γ` term dominates the original `δ_int / (δ_int - δ_fld)` term
once `δ_int - δ_fld` is below `1/n`. We state the resulting bound on
`ε_ca(C, δ_fld, δ_fld)`; the equality with `ε_mca` follows from L4.6 in the
unique-decoding regime, which is itself an external admit. Admitted as a derived
result from R4.2 + T4.9.2. -/
def rs_epsCA_small_loss_r4_10
    (domain : ι ↪ F) (k : ℕ) (δ_fld : ℝ≥0) (γ : ℝ≥0)
    (_h_dmin : (Code.minDist ((ReedSolomon.code domain k : Set (ι → F))) : ℝ)
                / Fintype.card ι / 3 ≤ δ_fld)
    (_hγ_pos : 0 < γ) (_hγ_lt : (γ : ℝ) < 1) : Prop :=
    let n : ℝ := Fintype.card ι
    let ρ : ℝ := k / n
    let bound : ℝ :=
      max ((1 - ρ - δ_fld) / (δ_fld * (1 - ρ - 2 * δ_fld) * Fintype.card F))
          ((n * δ_fld + γ) / (γ * Fintype.card F))
    epsCA (F := F) (A := F) ((ReedSolomon.code domain k : Set (ι → F))) δ_fld δ_fld ≤
      ENNReal.ofReal bound
  -- Missing ingredient: this is a COROLLARY of T4.9.2 (above) via R4.2 (the
  -- floor-collapse epsCA_eq_of_floor_eq, which IS in-tree in Errors.lean). Once T4.9.2 is
  -- proven, R4.10 closes by: (i) epsCA_eq_of_floor_eq to push δ_int=δ_fld+γ/n down to
  -- δ_int=δ_fld (γ<1 ⇒ same floor), (ii) substitute the small-loss term (n·δ_fld+γ)/γ for
  -- δ_int/(δ_int-δ_fld). So R4.10 is blocked SOLELY on T4.9.2 — no independent external
  -- content. Re-attempt immediately after T4.9.2 lands.

/-- **ABF26 Remark 4.10 — corrected reduction form.**

This is the checked part of the small-proximity-loss simplification.  It takes the BCHKS25
T4.9.2 bound at the genuine nearby internal radius `δ_fld + γ/n`, the exact R4.2
floor-collapse side condition, and the remaining real RHS comparison as explicit hypotheses.
Then it derives the in-tree R4.10 target at `δ_int = δ_fld`.

This avoids the false shortcut documented by `r4_10_floor_collapse_hypotheses_insufficient`:
`0 < γ < 1` alone does not imply the needed floor equality. -/
theorem rs_epsCA_small_loss_r4_10_of_residuals
    (domain : ι ↪ F) (k : ℕ) (δ_fld : ℝ≥0) (γ : ℝ≥0) :
    let δ_int : ℝ≥0 := δ_fld + γ / (Fintype.card ι : ℝ≥0)
    let n : ℝ := Fintype.card ι
    let ρ : ℝ := k / n
    let t492Bound : ℝ :=
      max ((1 - ρ - δ_fld) / (δ_fld * (1 - ρ - 2 * δ_fld) * Fintype.card F))
          ((δ_int : ℝ) / (((δ_int : ℝ) - (δ_fld : ℝ)) * Fintype.card F))
    let smallBound : ℝ :=
      max ((1 - ρ - δ_fld) / (δ_fld * (1 - ρ - 2 * δ_fld) * Fintype.card F))
          ((n * δ_fld + γ) / (γ * Fintype.card F))
    epsCA (F := F) (A := F) ((ReedSolomon.code domain k : Set (ι → F))) δ_fld δ_int ≤
        ENNReal.ofReal t492Bound →
    Nat.floor (δ_fld * Fintype.card ι) = Nat.floor (δ_int * Fintype.card ι) →
    t492Bound ≤ smallBound →
    epsCA (F := F) (A := F) ((ReedSolomon.code domain k : Set (ι → F))) δ_fld δ_fld ≤
      ENNReal.ofReal smallBound := by
  intro δ_int n ρ t492Bound smallBound hT492 hfloor hbound
  have heq := epsCA_eq_of_floor_eq
    (F := F) (A := F) ((ReedSolomon.code domain k : Set (ι → F)))
    δ_fld δ_fld δ_int hfloor
  rw [heq]
  exact le_trans hT492 (ENNReal.ofReal_le_ofReal hbound)

/-- Prop-level wrapper for the corrected R4.10 reduction.

Use this when the target is the external statement `rs_epsCA_small_loss_r4_10` itself: after
unfolding that statement, the checked reduction is exactly
`rs_epsCA_small_loss_r4_10_of_residuals`. -/
theorem rs_epsCA_small_loss_r4_10_of_residuals_prop
    (domain : ι ↪ F) (k : ℕ) (δ_fld : ℝ≥0) (γ : ℝ≥0)
    (h_dmin : (Code.minDist ((ReedSolomon.code domain k : Set (ι → F))) : ℝ)
                / Fintype.card ι / 3 ≤ δ_fld)
    (hγ_pos : 0 < γ) (hγ_lt : (γ : ℝ) < 1) :
    let δ_int : ℝ≥0 := δ_fld + γ / (Fintype.card ι : ℝ≥0)
    let n : ℝ := Fintype.card ι
    let ρ : ℝ := k / n
    let t492Bound : ℝ :=
      max ((1 - ρ - δ_fld) / (δ_fld * (1 - ρ - 2 * δ_fld) * Fintype.card F))
          ((δ_int : ℝ) / (((δ_int : ℝ) - (δ_fld : ℝ)) * Fintype.card F))
    let smallBound : ℝ :=
      max ((1 - ρ - δ_fld) / (δ_fld * (1 - ρ - 2 * δ_fld) * Fintype.card F))
          ((n * δ_fld + γ) / (γ * Fintype.card F))
    epsCA (F := F) (A := F) ((ReedSolomon.code domain k : Set (ι → F))) δ_fld δ_int ≤
        ENNReal.ofReal t492Bound →
    Nat.floor (δ_fld * Fintype.card ι) = Nat.floor (δ_int * Fintype.card ι) →
    t492Bound ≤ smallBound →
    rs_epsCA_small_loss_r4_10 domain k δ_fld γ h_dmin hγ_pos hγ_lt := by
  intro δ_int n ρ t492Bound smallBound hT492 hfloor hbound
  exact rs_epsCA_small_loss_r4_10_of_residuals
    (domain := domain) (k := k) (δ_fld := δ_fld) (γ := γ)
    hT492 hfloor hbound

/-- **R4.10 floor-collapse arithmetic.**  The nearby internal radius
`δ_int = δ_fld + γ/n` has the same Hamming-radius floor as `δ_fld` whenever the increment
does not cross the next lattice boundary, i.e. `δ_fld*n + γ < ⌊δ_fld*n⌋ + 1`.

This is the exact missing arithmetic condition identified by
`r4_10_floor_collapse_hypotheses_insufficient`; unlike `0 < γ < 1`, it is strong enough to
justify the in-tree `epsCA_eq_of_floor_eq` rewrite. -/
lemma r4_10_floor_collapse_of_no_boundary_crossing
    (δ_fld γ : ℝ≥0)
    (hcross : δ_fld * (Fintype.card ι : ℝ≥0) + γ <
        (Nat.floor (δ_fld * (Fintype.card ι : ℝ≥0)) : ℝ≥0) + 1) :
    Nat.floor (δ_fld * Fintype.card ι) =
      Nat.floor ((δ_fld + γ / (Fintype.card ι : ℝ≥0)) * Fintype.card ι) := by
  set n : ℝ≥0 := (Fintype.card ι : ℝ≥0) with hn
  have hnpos : 0 < n := by
    rw [hn]
    exact_mod_cast Fintype.card_pos
  have hle_arg : δ_fld * n ≤ (δ_fld + γ / n) * n := by
    -- (was a single-step `calc … := by …`, which the v4.30 calc-step parser swallows the
    -- following tactic lines into; stated directly instead)
    gcongr
    exact le_add_of_nonneg_right (zero_le _)
  have hfloor_le :
      Nat.floor (δ_fld * n) ≤ Nat.floor ((δ_fld + γ / n) * n) :=
    Nat.floor_le_floor hle_arg
  have hmul : (δ_fld + γ / n) * n = δ_fld * n + γ := by
    rw [add_mul, div_mul_cancel₀ _ (ne_of_gt hnpos)]
  have hfloor_lt :
      Nat.floor ((δ_fld + γ / n) * n) < Nat.floor (δ_fld * n) + 1 := by
    rw [Nat.floor_lt (zero_le _)]
    rw [hmul]
    exact_mod_cast hcross
  have hfloor_le' :
      Nat.floor ((δ_fld + γ / n) * n) ≤ Nat.floor (δ_fld * n) := by
    omega
  omega

/-- Prop-level R4.10 reduction with the floor-collapse side condition discharged by the
no-boundary-crossing inequality.  The only remaining substantive input is the T4.9.2 bound at
`δ_fld + γ/n` and the real comparison between the T4.9.2 RHS and the simplified R4.10 RHS. -/
theorem rs_epsCA_small_loss_r4_10_of_no_boundary_crossing_prop
    (domain : ι ↪ F) (k : ℕ) (δ_fld : ℝ≥0) (γ : ℝ≥0)
    (h_dmin : (Code.minDist ((ReedSolomon.code domain k : Set (ι → F))) : ℝ)
                / Fintype.card ι / 3 ≤ δ_fld)
    (hγ_pos : 0 < γ) (hγ_lt : (γ : ℝ) < 1)
    (hcross : δ_fld * (Fintype.card ι : ℝ≥0) + γ <
        (Nat.floor (δ_fld * (Fintype.card ι : ℝ≥0)) : ℝ≥0) + 1) :
    let δ_int : ℝ≥0 := δ_fld + γ / (Fintype.card ι : ℝ≥0)
    let n : ℝ := Fintype.card ι
    let ρ : ℝ := k / n
    let t492Bound : ℝ :=
      max ((1 - ρ - δ_fld) / (δ_fld * (1 - ρ - 2 * δ_fld) * Fintype.card F))
          ((δ_int : ℝ) / (((δ_int : ℝ) - (δ_fld : ℝ)) * Fintype.card F))
    let smallBound : ℝ :=
      max ((1 - ρ - δ_fld) / (δ_fld * (1 - ρ - 2 * δ_fld) * Fintype.card F))
          ((n * δ_fld + γ) / (γ * Fintype.card F))
    epsCA (F := F) (A := F) ((ReedSolomon.code domain k : Set (ι → F))) δ_fld δ_int ≤
        ENNReal.ofReal t492Bound →
    t492Bound ≤ smallBound →
    rs_epsCA_small_loss_r4_10 domain k δ_fld γ h_dmin hγ_pos hγ_lt := by
  intro δ_int n ρ t492Bound smallBound hT492 hbound
  refine rs_epsCA_small_loss_r4_10_of_residuals_prop
    (domain := domain) (k := k) (δ_fld := δ_fld) (γ := γ)
    h_dmin hγ_pos hγ_lt hT492 ?_ hbound
  exact r4_10_floor_collapse_of_no_boundary_crossing (ι := ι) δ_fld γ hcross

/-- The currently stated `0 < γ < 1` hypotheses do not by themselves imply the
floor-collapse side condition needed in `rs_epsCA_small_loss_r4_10`.

The intended R4.2 step needs
`floor (δ_fld * n) = floor ((δ_fld + γ / n) * n)`. This can fail when `δ_fld * n`
is close to the next integer: with `n = 10`, `δ_fld = 9/100`, and `γ = 1/5`,
the floors are `0` and `1`.  Any closure of R4.10 must therefore add or derive a
no-boundary-crossing hypothesis, not just use `0 < γ < 1`. -/
theorem r4_10_floor_collapse_hypotheses_insufficient :
    ¬ (∀ δ γ : ℝ≥0, 0 < γ → (γ : ℝ) < 1 →
      Nat.floor ((δ : ℝ) * (10 : ℝ)) =
        Nat.floor (((δ + γ / (10 : ℝ≥0) : ℝ≥0) : ℝ) * (10 : ℝ))) := by
  intro h
  have hbad := h (9 / 100 : ℝ≥0) (1 / 5 : ℝ≥0) (by norm_num) (by norm_num)
  norm_num at hbad

/-- **ABF26 Theorem 4.12 [BCHKS25 Thm 4.6].** For `C := RS[F, L, k]` with rate `ρ` and
`η > 0`, letting `ρ_plus := ρ + 1/n` and `m := max(⌈√ρ_plus/(2η)⌉, 3)`, for
`δ < 1 - √ρ_plus - η`:

  `ε_mca(C, δ) ≤ (1/|F|) · ( (2(m+½)⁵ + 3(m+½)·δ·ρ_plus) / (3·ρ_plus^{3/2}) · n
                              + (m+½)/√ρ_plus )`

The full numeric expression is preserved verbatim so future RS analyses can plug in
concrete `ρ`, `η`, and `n` values. Admitted as an external result.

**Parameter improvement reference.** ABF26 cites [Hab25] alongside [BCHKS25] for
this theorem; Haböck 2025 improves the constants / parameter regime but the
asymptotic form is unchanged. Our statement matches the BCHKS25 form; a separate
sharper-constant statement could be added as a corollary if a downstream consumer
needs the tighter bound. -/
def rs_epsMCA_johnson_range_bchks25
    (domain : ι ↪ F) (k : ℕ) (η δ : ℝ≥0)
    (_hη : 0 < η)
    (_hδ :
        (δ : ℝ) <
          1 - (((k : ℝ) / Fintype.card ι + 1 / Fintype.card ι) ^ ((1 : ℝ) / 2))
            - (η : ℝ)) : Prop :=
    epsMCA (F := F) (A := F) ((ReedSolomon.code domain k : Set (ι → F))) δ ≤
      ENNReal.ofReal
        (let n : ℝ := Fintype.card ι
         let ρ_plus : ℝ := k / n + 1 / n
         let m : ℝ := max ⌈(ρ_plus ^ ((1 : ℝ) / 2)) / (2 * η)⌉ 3
         ((2 * (m + 1/2) ^ 5 + 3 * (m + 1/2) * δ * ρ_plus)
            / (3 * ρ_plus ^ ((3 : ℝ) / 2)) * n
          + (m + 1/2) / ρ_plus ^ ((1 : ℝ) / 2))
           / (Fintype.card F : ℝ))
  -- Missing ingredient: BCHKS25 Thm 4.6's explicit RS MCA bound in the Johnson range
  -- δ<1-√ρ₊-η. The (m+½)⁵ / ρ₊^{3/2} polynomial in the multiplicity parameter
  -- m=max(⌈√ρ₊/(2η)⌉,3) comes from the BCHKS25 multiplicity-coded RS list-decoder analysis;
  -- needs the m-multiplicity RS interpolation bound (not in-tree). Genuinely external.

/-- **ABF26 Theorem 4.16 [BCHKS25, KK25].** Existence: for every `c > 0` and rate
`ρ ∈ (0, 1/2)` there exists a power-of-two `n ∈ ℕ` and a Reed-Solomon code
`C := RS[F, L, k]` of rate `ρ` over a prime field `F` with `|F| = poly(n)` and smooth
`L` of size `n` such that

  `ε_ca(C, 1 - ρ - slack) ≥ n^c / |F|`

for some `slack` of order `Θ(1/log n)`. We existentially bind the slack parameter as a
real-valued knob rather than encoding `Θ` directly. -/
def rs_epsCA_lower_capacity_bchks25_kk25
    (c : ℝ≥0) (_hc : 0 < c) (ρ : ℝ≥0) (_hρ_pos : 0 < ρ) (_hρ_lt : ρ < (1 / 2 : ℝ≥0)) : Prop :=
    ∃ (ιC : Type) (_ : Fintype ιC) (_ : Nonempty ιC) (_ : DecidableEq ιC)
      (FC : Type) (_ : Field FC) (_ : Fintype FC) (_ : DecidableEq FC)
      (domain : ιC ↪ FC) (_ : ReedSolomon.Smooth domain) (k : ℕ) (slack : ℝ≥0),
      -- `F` is a prime field (paper's "prime field" claim):
      (∃ p : ℕ, p.Prime ∧ CharP FC p ∧ Fintype.card FC = p) ∧
      -- `|F| = poly(n)` — polynomially bounded in `n = |L|`:
      (∃ a b : ℕ, Fintype.card FC ≤ a * (Fintype.card ιC) ^ b) ∧
      (k : ℝ) / Fintype.card ιC = ρ ∧
      epsCA (F := FC) (A := FC) ((ReedSolomon.code domain k : Set (ιC → FC)))
          (1 - ρ - slack) (1 - ρ - slack) ≥
        ((Fintype.card ιC : ENNReal) ^ (c : ℝ)) / (Fintype.card FC : ENNReal)
  -- Missing ingredient: a CONSTRUCTION of RS codes near capacity with ε_ca ≥ n^c/|F|
  -- (LOWER bound). Requires building, for each c and ρ∈(0,1/2), a prime-field smooth-domain
  -- RS code whose 1-ρ-Θ(1/log n) proximity gap fails on an n^c-fraction of lines (KK25
  -- subset-sum / BCHKS25 capacity-regime bad-code construction). The trivial epsCA≤1 is the
  -- wrong direction; no in-tree generator manufactures the witness code/stack. Genuinely
  -- external (also needs a smooth-domain existence witness for the ∃-binder).

/-- **ABF26 Theorem 4.17 [CS25 Cor 1].** Complete CA breakdown for Reed-Solomon codes.
Let `C := RS[F, L, k]` with `q = |F| ≥ 10`, rate `ρ`, and `δ` satisfying:

  `1 - H_q(δ) + 2/n + √((H_q(δ) - δ)/n) ≤ ρ ≤ 1 - δ - 2/n`

Then `ε_ca(C, δ) = 1`. Uses `qEntropy` (ABF26 Definition 2.2, defined in
`Basic/Entropy.lean`). Admitted as an external result. -/
def rs_epsCA_breakdown_cs25
    (domain : ι ↪ F) (k : ℕ) (δ : ℝ≥0)
    (_hq_ge : 10 ≤ Fintype.card F)
    (_hδ_lo :
        1 - qEntropy (Fintype.card F) (δ : ℝ) + 2 / (Fintype.card ι : ℝ)
            + ((qEntropy (Fintype.card F) (δ : ℝ) - (δ : ℝ))
                / (Fintype.card ι : ℝ)) ^ ((1 : ℝ) / 2)
          ≤ (k : ℝ) / Fintype.card ι)
    (_hδ_hi : (k : ℝ) / Fintype.card ι ≤ 1 - (δ : ℝ) - 2 / (Fintype.card ι : ℝ)) : Prop :=
    epsCA (F := F) (A := F) ((ReedSolomon.code domain k : Set (ι → F))) δ δ = 1
  -- Missing ingredient: CS25's complete-CA-breakdown EQUALITY epsCA=1. The `≤1` half is now
  -- trivial (epsCA is a sup of probabilities; cf. the epsCA_le_one pattern). The hard half is
  -- the `≥1` LOWER bound in the entropy band 1-H_q(δ)+2/n+√(...)≤ρ≤1-δ-2/n: CS25 shows
  -- almost every line is δ-close while almost no pair is jointly close, via a counting
  -- argument tying H_q(δ) to the number of RS codewords in a δ-ball. Needs the qEntropy↔
  -- RS-ball-count bridge (absent; qEntropy is defined but unconnected to hammingBallVolume /
  -- RS code counts). Genuinely external.

/-- **ABF26 Theorem 4.18 [BCHKS25 Cor 1.7].** CA jump at the Johnson bound. Fix `ε > 0`,
let `δ := 15/16`. Then for all `F` of characteristic 2 there exists a Reed-Solomon code
`C := RS[F, L, k]` with `n ≈ |F|^{(1+ε)/2}` and `δ_min(C) = 15/16` such that:

  `ε_ca(C, J(δ_min(C)), J(δ_min(C)) + 1/8 + 1/n) ≥ n^{2(1-ε)} / |F|`

where `J(δ) := 1 - √(1 - δ)` is the Johnson radius. Witnesses a sharp jump in CA
error precisely at the Johnson bound.

**Note on `n ≈ |F|^{(1+ε)/2}`.** Paper writes equality but `|F|^{(1+ε)/2}` is generally
not a natural number; the intended reading is "for `n` of this order of magnitude". We
encode this as a two-sided bound `n ≥ |F|^{(1+ε)/2} - 1 ∧ n ≤ |F|^{(1+ε)/2} + 1`,
which allows witness `n = ⌊|F|^{(1+ε)/2}⌋` or `⌈|F|^{(1+ε)/2}⌉` as appropriate.

Admitted as an external result. -/
def rs_epsCA_johnson_jump_bchks25
    {FC : Type} [Field FC] [Fintype FC] [DecidableEq FC] [CharP FC 2]
    (ε : ℝ≥0) (_hε : 0 < ε) : Prop :=
    ∃ (ιC : Type) (_ : Fintype ιC) (_ : Nonempty ιC) (_ : DecidableEq ιC)
      (domain : ιC ↪ FC) (k : ℕ),
      ((Fintype.card FC : ℝ) ^ (((1 : ℝ) + ε) / 2) - 1
          ≤ (Fintype.card ιC : ℝ)) ∧
      ((Fintype.card ιC : ℝ)
          ≤ (Fintype.card FC : ℝ) ^ (((1 : ℝ) + ε) / 2) + 1) ∧
      (Code.minDist ((ReedSolomon.code domain k : Set (ιC → FC))) : ℝ)
          / Fintype.card ιC = (15 : ℝ) / 16 ∧
      epsCA (F := FC) (A := FC) ((ReedSolomon.code domain k : Set (ιC → FC)))
          (((1 : ℝ) - (1 - ((15 : ℝ) / 16)) ^ ((1 : ℝ) / 2)).toNNReal)
          (((1 : ℝ) - (1 - ((15 : ℝ) / 16)) ^ ((1 : ℝ) / 2)
              + 1 / 8 + 1 / (Fintype.card ιC : ℝ)).toNNReal) ≥
        ((Fintype.card ιC : ENNReal) ^ (2 * ((1 : ℝ) - ε)))
          / (Fintype.card FC : ENNReal)
  -- Missing ingredient: BCHKS25's char-2 CA-jump CONSTRUCTION at the Johnson bound. LOWER
  -- bound ε_ca ≥ n^{2(1-ε)}/|F| at the Johnson radius J(15/16)=3/4, witnessed by a char-2 RS
  -- code with n≈|F|^{(1+ε)/2} and δ_min=15/16. Requires the char-2 subfield construction
  -- exhibiting the sharp proximity-gap discontinuity at J(δ_min). Code-construction lower
  -- bound; trivial epsCA≤1 is the wrong direction; no in-tree witness generator. Genuinely
  -- external.

end ReedSolomon

/-! ## Covering-radius sampling — ABF26 §4 ([DG25])

Disposition (issue #48): DIRECT PORT (covering-radius sampling identity absent in-tree).
An *upper*-witness feeder (`ε_ca` lower bound) for the Grand MCA threshold. See the
file-level disposition ledger. -/

section Sampling

open scoped ProbabilityTheory

variable {ι : Type} [Fintype ι] [Nonempty ι] [DecidableEq ι]
variable {F : Type} [Field F] [Fintype F] [DecidableEq F]

/-- **ABF26 Lemma 4.19 [DG25 Thm 2.5].** Let `C ⊆ F^n` be a linear code and let
`δ' := max_{u ∈ F^n} Δ(u, C)` be the (relative) covering radius. For every
`δ ∈ (0, δ')`:

  `ε_ca(C, δ) ≥ ((q-1)/q) · Pr_{u ← F^n}[Δ(u, C) ≤ δ]`

The probability is over a uniform word in `F^n`, expressed via the `Pr_{...}[...]`
notation. Admitted as an external result. -/
def linear_epsCA_ge_sampling_dg25
    (C : LinearCode ι F) (δ δ' : ℝ≥0)
    (_h_δ' : (δ' : ENNReal) = ⨆ u : ι → F, δᵣ(u, (C : Set (ι → F))))
    (_hδ_pos : 0 < δ) (_hδ_lt : δ < δ') : Prop :=
    ((Fintype.card F - 1 : ℝ≥0) / Fintype.card F : ENNReal)
        * Pr_{let u ← $ᵖ (ι → F)}[δᵣ(u, (C : Set (ι → F))) ≤ δ] ≤
      epsCA (F := F) (A := F) ((C : Set (ι → F))) δ δ
  -- Missing ingredient: DG25's covering-radius sampling LOWER bound. Shows
  -- ε_ca(C,δ) ≥ ((q-1)/q)·Pr_u[Δ(u,C)≤δ] by averaging the line-proximity event over a
  -- random base word u and a random nonzero shift; the (q-1)/q factor is the probability
  -- the shift is nonzero. Needs: (i) wiring the uniform-word covering probability Pr_u[…]
  -- into the epsCA sup (the DG25/ files prove a different BCIKS-style gap, not this
  -- covering-radius sampling identity), (ii) the nonzero-shift averaging. Genuinely external.

end Sampling

/-! ## Subspace-design / FRS MCA up to capacity — ABF26 §4.2.2 ([GG25], [BCGM25])

Disposition (issue #48): T4.13 is a DIRECT PORT (GG25 line-stitching/list-decoding pipeline;
its list-decoding input is tracked by #53); T4.14 is a DERIVED COROLLARY of T4.13 + T2.18
(checked reduction `frs_epsMCA_capacity_gg25_of_residuals` in-tree); the BCGM25 entry is a
SHADOW to be restated via `IsMCAGenerator` once PR #489 lands — do not prove as-is. T4.13 /
T4.14 are the priority lower-witness feeders (`MCALowerWitness.ofLe`) realizing MCA up to
capacity. See the file-level disposition ledger. -/

section SubspaceDesignFRS

/-- **ABF26 Theorem 4.13 [GG25 Corollary 4.9].** τ-subspace-design codes have MCA bounds.
Let `C : F^k → (F^s)^n` be a τ-subspace-design code. For every `t ∈ ℕ`:

  `ε_mca(C, 1 - τ(t+1) - 3/(2t)) ≤ (t·n + 4·t²) / |F|`

Combined with `IsSubspaceDesign` (D2.16) and `subspaceDesign_tau_lower` (L2.17), this
gives MCA up to capacity for subspace-design codes. Admitted as an external result. -/
def subspaceDesign_epsMCA_gg25
    {ι : Type} [Fintype ι] [Nonempty ι] [DecidableEq ι]
    {F : Type} [Field F] [Fintype F] [DecidableEq F]
    (s : ℕ) (τ : ℕ → ℝ) (C : Submodule F (ι → Fin s → F))
    (_h : IsSubspaceDesign s τ C)
    (t : ℕ) (_ht : 0 < t) : Prop :=
    epsMCA (F := F) (A := Fin s → F) ((C : Set (ι → Fin s → F)))
        ((1 - τ (t + 1) - 3 / (2 * t)).toNNReal) ≤
      ENNReal.ofReal (((t : ℝ) * Fintype.card ι + 4 * t ^ 2) / Fintype.card F)
  -- Missing ingredient: GG25's subspace-design MCA bound. The (t·n+4t²)/|F| count is the core
  -- technical result of the whole GG25 paper; its proof is the three-step pipeline
  --   (i) LINE STITCHING from the τ-subspace-design property + pruning (GG25 Lem 5.5, 5.7),
  --  (ii) STITCHING → correlated agreement, combined with the subspace-design LIST-DECODING
  --       bound (GG25 Lem 5.10 — in-tree this is T3.4 `subspaceDesign_list_decoding_cz25`,
  --       itself STILL a sorry: its design→Λ dimension-counting analysis is absent), and
  -- (iii) polynomial INTERPOLATION lifting agreement from finitely many γ to all parameters
  --       (GG25 Lem 5.4).
  -- Equivalently the bound factors as T3.4 (design→list-size) ∘ T5.1
  -- (`linear_listSize_to_epsMCA_gcxk25`, list-size→MCA) — but BOTH composands are themselves
  -- unproven sorries whose own notes document absent machinery (the design→Λ count, and the
  -- reduction of the `epsMCA` sup over arbitrary word stacks with single-witness `mcaEvent`
  -- (D4.3) to GG25/GCXK25's per-codeword-pair Bad-set counting).
  -- L2.17 (`subspaceDesign_tau_lower`) — one prerequisite — is now PROVEN kernel-clean in
  -- SubspaceDesign.lean, but it alone does NOT unblock this: the design→MCA conversion (the
  -- line-stitching + list-decoder + interpolation engine above) is the substantive absent
  -- content. In-tree GK16Wronskian supplies only the elementary linear-independence criterion,
  -- not the list-decoder or stitching argument.
  -- No vacuous-truncation escape: even when (1-τ(t+1)-3/(2t)).toNNReal truncates to 0, the RHS
  -- (t·n+4t²)/|F| is a genuine positive bound and `epsMCA C 0 > 0` in general
  -- (cf. epsMCA_Czero_pos / lineDecodable_imp_epsMCA_le_false), so the statement stays
  -- nonvacuous. Genuinely external (the GG25 line-stitching/list-decoder pipeline is unformalized).

/-- **ABF26 Theorem 4.14 [GG25 Corollary 4.10].** Folded Reed-Solomon codes have MCA
up to capacity. Let `η ∈ (0, 1)` and `C := FRS[F, L, k, s, ω]` be a folded RS code
with `s > 16/η²`. Then:

  `ε_mca(C, 1 - ρ - η) ≤ 2n/(η·|F|) + 24/(η³·|F|)`

A corollary of T4.13 via T2.18 (FRS is τ-subspace-design). Admitted as an external
result. -/
def frs_epsMCA_capacity_gg25
    {ι : Type} [Fintype ι] [Nonempty ι] [DecidableEq ι]
    {F : Type} [Field F] [Fintype F] [DecidableEq F]
    (domain : ι ↪ F) (k s : ℕ) (ω : F)
    (η : ℝ) (_hη_pos : 0 < η) (_hη_lt : η < 1)
    (_hs_gt : (s : ℝ) > 16 / η ^ 2) : Prop :=
    let n : ℝ := Fintype.card ι
    let ρ : ℝ := k / n
    epsMCA (F := F) (A := Fin s → F)
        ((ReedSolomon.Folded.frsCode domain k s ω : Set (ι → Fin s → F)))
        ((1 - ρ - η).toNNReal) ≤
      ENNReal.ofReal (2 * n / (η * Fintype.card F)
        + 24 / (η ^ 3 * Fintype.card F))
  -- Missing ingredient: this is a COROLLARY of T4.13 via T2.18 (frs_is_subspaceDesign_gk16:
  -- FRS is τ-subspace-design with τ(r)=sρ/(s-r+1)). Once T4.13 and T2.18 are proven, T4.14
  -- closes by instantiating T4.13 at the FRS τ and choosing t≈1/η (s>16/η² makes the design
  -- bound collapse to 2n/(η|F|)+24/(η³|F|)). Blocked on T4.13 (above) + T2.18 (external admit
  -- in SubspaceDesign.lean). No independent external content beyond those two.

/-- **ABF26 Theorem 4.14 [GG25 Cor 4.10] — checked reduction form.**

This discharges the theorem's *corollary* content.  Given:

* the FRS subspace-design instance (T2.18 / GK16),
* the general subspace-design MCA theorem (T4.13 / GG25),
* the radius identification from the chosen integer `t`, and
* the real arithmetic comparison collapsing `(t·n+4t²)/|F|` to
  `2n/(η|F|)+24/(η³|F|)`,

the exact in-tree T4.14 target follows.  The last two hypotheses are the formalized shape of the
paper's informal choice `t ≈ 1/η`; they are explicit so this theorem does not smuggle in
unproved floor/ceiling arithmetic. -/
theorem frs_epsMCA_capacity_gg25_of_residuals
    {ι : Type} [Fintype ι] [Nonempty ι] [DecidableEq ι]
    {F : Type} [Field F] [Fintype F] [DecidableEq F]
    (domain : ι ↪ F) (k s : ℕ) (ω : F)
    (η : ℝ) (t : ℕ) (ht : 0 < t)
    (hT218 : IsSubspaceDesign s
        (fun r ↦ if r ∈ Finset.Icc 1 s then
            (s : ℝ) * (k : ℝ) / Fintype.card ι / ((s : ℝ) - r + 1) else 1)
        (ReedSolomon.Folded.frsCode domain k s ω))
    (hT413 : ∀ (τ : ℕ → ℝ) (C : Submodule F (ι → Fin s → F)),
        IsSubspaceDesign s τ C → ∀ t' : ℕ, 0 < t' →
        epsMCA (F := F) (A := Fin s → F) ((C : Set (ι → Fin s → F)))
            ((1 - τ (t' + 1) - 3 / (2 * t')).toNNReal) ≤
          ENNReal.ofReal (((t' : ℝ) * Fintype.card ι + 4 * t' ^ 2) / Fintype.card F))
    (hRadius :
      let n : ℝ := Fintype.card ι
      let ρ : ℝ := k / n
      ((1 - ρ - η).toNNReal : ℝ≥0) =
        (1 -
            (fun r ↦ if r ∈ Finset.Icc 1 s then
              (s : ℝ) * (k : ℝ) / Fintype.card ι / ((s : ℝ) - r + 1) else 1) (t + 1)
            - 3 / (2 * t)).toNNReal)
    (hBound :
      let n : ℝ := Fintype.card ι
      ((t : ℝ) * n + 4 * t ^ 2) / Fintype.card F ≤
        2 * n / (η * Fintype.card F) + 24 / (η ^ 3 * Fintype.card F)) :
    let n : ℝ := Fintype.card ι
    let ρ : ℝ := k / n
    epsMCA (F := F) (A := Fin s → F)
        ((ReedSolomon.Folded.frsCode domain k s ω : Set (ι → Fin s → F)))
        ((1 - ρ - η).toNNReal) ≤
      ENNReal.ofReal (2 * n / (η * Fintype.card F)
        + 24 / (η ^ 3 * Fintype.card F)) := by
  intro n ρ
  set τ : ℕ → ℝ := fun r ↦ if r ∈ Finset.Icc 1 s then
      (s : ℝ) * (k : ℝ) / Fintype.card ι / ((s : ℝ) - r + 1) else 1
  have h413 := hT413 τ (ReedSolomon.Folded.frsCode domain k s ω) hT218 t ht
  rw [hRadius]
  exact le_trans h413 (ENNReal.ofReal_le_ofReal hBound)

/-- Prop-level wrapper for T4.14.

This closes the external statement `frs_epsMCA_capacity_gg25` from the checked residual bundle,
leaving no extra independent content in the corollary statement. -/
theorem frs_epsMCA_capacity_gg25_of_residuals_prop
    {ι : Type} [Fintype ι] [Nonempty ι] [DecidableEq ι]
    {F : Type} [Field F] [Fintype F] [DecidableEq F]
    (domain : ι ↪ F) (k s : ℕ) (ω : F)
    (η : ℝ) (hη_pos : 0 < η) (hη_lt : η < 1)
    (hs_gt : (s : ℝ) > 16 / η ^ 2)
    (t : ℕ) (ht : 0 < t)
    (hT218 : IsSubspaceDesign s
        (fun r ↦ if r ∈ Finset.Icc 1 s then
            (s : ℝ) * (k : ℝ) / Fintype.card ι / ((s : ℝ) - r + 1) else 1)
        (ReedSolomon.Folded.frsCode domain k s ω))
    (hT413 : ∀ (τ : ℕ → ℝ) (C : Submodule F (ι → Fin s → F)),
        IsSubspaceDesign s τ C → ∀ t' : ℕ, 0 < t' →
        epsMCA (F := F) (A := Fin s → F) ((C : Set (ι → Fin s → F)))
            ((1 - τ (t' + 1) - 3 / (2 * t')).toNNReal) ≤
          ENNReal.ofReal (((t' : ℝ) * Fintype.card ι + 4 * t' ^ 2) / Fintype.card F))
    (hRadius :
      let n : ℝ := Fintype.card ι
      let ρ : ℝ := k / n
      ((1 - ρ - η).toNNReal : ℝ≥0) =
        (1 -
            (fun r ↦ if r ∈ Finset.Icc 1 s then
              (s : ℝ) * (k : ℝ) / Fintype.card ι / ((s : ℝ) - r + 1) else 1) (t + 1)
            - 3 / (2 * t)).toNNReal)
    (hBound :
      let n : ℝ := Fintype.card ι
      ((t : ℝ) * n + 4 * t ^ 2) / Fintype.card F ≤
        2 * n / (η * Fintype.card F) + 24 / (η ^ 3 * Fintype.card F)) :
    frs_epsMCA_capacity_gg25 domain k s ω η hη_pos hη_lt hs_gt := by
  exact frs_epsMCA_capacity_gg25_of_residuals
    (domain := domain) (k := k) (s := s) (ω := ω) (η := η) (t := t) ht
    hT218 hT413 hRadius hBound

/-- **ABF26 BCGM25 extension to T4.13 / T4.14 (polynomial generators preserve
correlated agreement).**

[BCGM25] shows that the correlated/mutual agreement of subspace-design codes is
preserved not only under affine line combinations `u₀ + γ · u₁` but under arbitrary
*polynomial generators* — combinations of the form `∑ᵢ Gᵢ(γ) · uᵢ` for a large class
of functions called "polynomial generators". Stated in ABF26 §4.2.2 (subsection on
"subspace-design codes") and footnote 2 of the introduction; not separately numbered
as `T4.x`, but materially extends the reach of T4.13 / T4.14.

**Canonical formalization lives elsewhere — this is the survey-ledger shadow.** The
genuine polynomial-generator MCA framework (the `Generator` / `IsMCAGenerator` / `IsMCA`
abstraction, formalizing [BSGM25] Lemmas 4.1, 4.2 and Definition 4.3) is being built in
`ProximityGap/MCAGenerator.lean` and `ProximityGap/ProximityGenerators.lean` by PR #489
(`Katy/MCAgens`). Once that lands on `main` and merges into this branch, **this entry
should be restated in terms of `IsMCAGenerator` (or removed in favour of it)** rather than
the affine-style `epsCA`/`epsMCA` errors here. Do not grow a parallel polynomial-generator
notion under `CapacityBounds`.

**What this placeholder captures meanwhile.** Unlike T4.13 (`subspaceDesign_epsMCA_gg25`),
the left-hand side is the **power-curve** correlated-agreement error `epsCA_curves … k`
(combinations `∑ i : Fin (k+1), γ^i · uᵢ`) — the genuine polynomial-generator family, so
this is not a copy of T4.13. Two honesty caveats: (i) [BSGM25] proves *mutual* correlated
agreement; this shadow uses the *correlated-agreement* curve error because the ABF26 branch
has no curve-MCA notion yet (PR #489 supplies the real one); (ii) the RHS reuses the GG25
affine bound shape `(t·n + 4t²)/|F|`, with the precise polynomial-generator constants as
in [BSGM25]. Admitted as an external result. -/
def subspaceDesign_epsCA_curves_polynomial_generators_bcgm25
    {ι : Type} [Fintype ι] [Nonempty ι] [DecidableEq ι]
    {F : Type} [Field F] [Fintype F] [DecidableEq F]
    (s : ℕ) (τ : ℕ → ℝ) (C : Submodule F (ι → Fin s → F))
    (_h : IsSubspaceDesign s τ C)
    (t k : ℕ) (_ht : 0 < t) : Prop :=
    epsCA_curves (F := F) (A := Fin s → F) ((C : Set (ι → Fin s → F))) k
        ((1 - τ (t + 1) - 3 / (2 * t)).toNNReal)
        ((1 - τ (t + 1) - 3 / (2 * t)).toNNReal) ≤
      ENNReal.ofReal (((t : ℝ) * Fintype.card ι + 4 * t ^ 2) / Fintype.card F)
  -- Missing ingredient: BCGM25's polynomial-generator MCA preservation for subspace-design
  -- codes. This bounds the CURVE error epsCA_curves (∑ γ^i·uᵢ), not the affine epsCA of
  -- T4.13, so it is NOT a copy. The genuine framework (IsMCAGenerator) is being built in
  -- ProximityGap/MCAGenerator.lean + ProximityGenerators.lean by PR #489; per the docstring
  -- this admit should be RESTATED in terms of IsMCAGenerator once #489 lands (do not prove the
  -- shadow). Blocked on #489 + T4.13. Genuinely external.

end SubspaceDesignFRS

end CodingTheory

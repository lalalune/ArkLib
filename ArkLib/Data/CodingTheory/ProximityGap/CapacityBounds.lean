/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexander Hicks
-/

import ArkLib.Data.CodingTheory.ProximityGap.Errors
import ArkLib.Data.CodingTheory.ProximityGap.CS25CoveringExistence
import ArkLib.Data.CodingTheory.ProximityGap.ProximityGenerators
import ArkLib.Data.CodingTheory.ReedSolomon
import ArkLib.Data.CodingTheory.Basic.Entropy
import ArkLib.Data.CodingTheory.HammingBallVolume
import ArkLib.Data.CodingTheory.SubspaceDesign
import ArkLib.Data.CodingTheory.InterleavedCode
import ArkLib.Data.Probability.Combinatorial
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
- `random_rs_mca` — ABF26 T4.15 [GG25 Thm 5.15]: random Reed-Solomon domains have
  MCA up to capacity with high probability, stated over `Probability.uniformSizeSubsetOfLe`.

## Deferred statements

- No §4.2.2 statement is blocked on the random-domain probability space anymore; T4.15 is
  present below as a Prop-valued external statement. Its GG25 probabilistic proof and concrete
  parameter instantiation remain external.

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
- `subspaceDesign_epsMCA_gg25` (T4.13) — GG25 line-stitching/list-decoding pipeline; its
  list-decoding input is tracked by #53.
- `random_rs_mca` (T4.15 [GG25 Thm 5.15]) — random-domain RS MCA up-to-capacity
  bound absent in-tree; the probability space is now the canonical
  `Probability.uniformSizeSubsetOfLe`.

*PROVED COMPANION BRIDGES* (Prop front doors retained here, proof assembly in companion files):

- `linear_epsCA_ge_sampling_dg25` (L4.19) — discharged by
  `CodingTheory.linear_epsCA_ge_sampling_dg25_proof` in `DG25Sampling.lean`.

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
- `rs_epsCA_johnson_jump_bchks25` (T4.18) — char-2 Johnson-jump witness family.  The
  supremum lower bound is now reduced to an explicit good-`γ` count via
  `johnsonJump_epsCA_lower_of_goodGamma` / `RSJohnsonJumpWitness.ofGoodGammaCount` /
  `rs_epsCA_johnson_jump_bchks25_of_goodGamma`; only the bad word-pair and the
  `n^{2(1-ε)}` good-combiner count remain external inputs.

*BCGM25 polynomial-generator MCA* (generator-native API plus compatibility shadow):

- `polynomialGenerator_isMCAGenerator_bcgm25` — canonical BCGM25 statement surface using
  `CoreDefinitions.IsPolynomialGenerator` and `CoreDefinitions.IsMCAGenerator`.
- `subspaceDesign_epsCA_curves_polynomial_generators_bcgm25` — retained only as the old
  ABF26 survey-ledger `epsCA_curves` compatibility shadow; do not prove as-is.

**No statement in this file is disproven.**  The two repaired items are R4.10 (the naive
`0 < γ < 1` floor-collapse shortcut is refuted in-tree by
`r4_10_floor_collapse_hypotheses_insufficient`; the corrected reduction carries an explicit
no-boundary-crossing hypothesis) and the BCGM25 compatibility entry (deliberately a curve-CA
shadow beside the real mutual-correlated-agreement statement; see its docstring).  Related
*statement-level*
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
set_option linter.style.longFile 1900

namespace CodingTheory

open scoped NNReal ProbabilityTheory
open ProximityGap unitInterval

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

/-- Public T4.11.1 wrapper from the named 1.5-Johnson MCA bound. -/
theorem linear_epsMCA_1_5_johnson_gkl24_of_bound
    (C : ModuleCode ι F A) (δ_min η δ : ℝ≥0)
    (h_δ_min : (δ_min : ℝ) = (Code.minDist (C : Set (ι → A)) : ℝ) / Fintype.card ι)
    (hη : 0 < η) (hη_lt_δ_min : η < δ_min)
    (hδ : (δ : ℝ) ≤ 1 - ((1 - (δ_min : ℝ) + (η : ℝ)) ^ ((1 : ℝ) / 3)))
    (hbound :
      epsMCA (F := F) (A := A) ((C : Set (ι → A))) δ ≤
        ENNReal.ofReal
          ((((Fintype.card ι : ℝ) + 6) / η
            + 2 / ((η : ℝ) *
                ((1 - (δ_min : ℝ) + (η : ℝ)) ^ ((1 : ℝ) / 3)
                  - (1 - (δ_min : ℝ) + (η : ℝ)) ^ ((1 : ℝ) / 2)))) /
            (Fintype.card F : ℝ))) :
    linear_epsMCA_1_5_johnson_gkl24 C δ_min η δ h_δ_min hη hη_lt_δ_min hδ := by
  simpa [linear_epsMCA_1_5_johnson_gkl24] using hbound

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

/-- Public T4.11.2 wrapper from the named 1.5-Johnson CA-with-proximity-loss bound. -/
theorem linear_epsCA_1_5_johnson_bgks20_of_bound
    (C : ModuleCode ι F A) (δ_min η δ : ℝ≥0)
    (h_δ_min : (δ_min : ℝ) = (Code.minDist (C : Set (ι → A)) : ℝ) / Fintype.card ι)
    (hη : 0 < η) (hη_lt_δ_min : η < δ_min)
    (hδ : (δ : ℝ) ≤ 1 - ((1 - (δ_min : ℝ) + (η : ℝ)) ^ ((1 : ℝ) / 3)))
    (hbound :
      epsCA (F := F) (A := A) ((C : Set (ι → A))) δ (δ + η) ≤
        ((2 : ENNReal) / ((η : ENNReal) ^ 2 * (Fintype.card F : ENNReal)))) :
    linear_epsCA_1_5_johnson_bgks20 C δ_min η δ h_δ_min hη hη_lt_δ_min hδ := by
  simpa [linear_epsCA_1_5_johnson_bgks20] using hbound

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

/-- Public T4.9.2 wrapper from the named BCHKS25 item-2 bound. -/
theorem rs_epsCA_bchks25_item2_of_bound
    (domain : ι ↪ F) (k : ℕ) (δ_fld δ_int : ℝ≥0)
    (h_dmin : (Code.minDist ((ReedSolomon.code domain k : Set (ι → F))) : ℝ)
                / Fintype.card ι / 3 ≤ δ_fld)
    (h_lt : δ_fld < δ_int)
    (hbound :
      let n : ℝ := Fintype.card ι
      let ρ : ℝ := k / n
      let bound : ℝ :=
        max ((1 - ρ - δ_fld) / (δ_fld * (1 - ρ - 2 * δ_fld) * Fintype.card F))
            ((δ_int : ℝ) / ((δ_int - δ_fld) * Fintype.card F))
      epsCA (F := F) (A := F) ((ReedSolomon.code domain k : Set (ι → F))) δ_fld δ_int ≤
        ENNReal.ofReal bound) :
    rs_epsCA_bchks25_item2 domain k δ_fld δ_int h_dmin h_lt := by
  simpa [rs_epsCA_bchks25_item2] using hbound

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

/-- The nearby internal radius used in R4.10 is strictly above `δ_fld` when `γ > 0`. -/
lemma r4_10_delta_lt_nearby
    (δ_fld γ : ℝ≥0) (hγ_pos : 0 < γ) :
    δ_fld < δ_fld + γ / (Fintype.card ι : ℝ≥0) := by
  have hnpos : 0 < (Fintype.card ι : ℝ≥0) := by
    exact_mod_cast Fintype.card_pos
  exact lt_add_of_pos_right δ_fld (div_pos hγ_pos hnpos)

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
theorem rs_epsCA_small_loss_r4_10
    (domain : ι ↪ F) (k : ℕ) (δ_fld : ℝ≥0) (γ : ℝ≥0)
    (h_dmin : (Code.minDist ((ReedSolomon.code domain k : Set (ι → F))) : ℝ)
                / Fintype.card ι / 3 ≤ δ_fld)
    (hγ_pos : 0 < γ) (_hγ_lt : (γ : ℝ) < 1)
    (hcross : δ_fld * (Fintype.card ι : ℝ≥0) + γ <
        (Nat.floor (δ_fld * (Fintype.card ι : ℝ≥0)) : ℝ≥0) + 1)
    (hT492 : rs_epsCA_bchks25_item2 domain k δ_fld (δ_fld + γ / (Fintype.card ι : ℝ≥0))
      h_dmin (r4_10_delta_lt_nearby _ _ hγ_pos))
    (hbound :
      let δ_int : ℝ≥0 := δ_fld + γ / (Fintype.card ι : ℝ≥0)
      let n : ℝ := Fintype.card ι
      let ρ : ℝ := k / n
      let t492Bound : ℝ :=
        max ((1 - ρ - δ_fld) / (δ_fld * (1 - ρ - 2 * δ_fld) * Fintype.card F))
            ((δ_int : ℝ) / (((δ_int : ℝ) - (δ_fld : ℝ)) * Fintype.card F))
      let smallBound : ℝ :=
        max ((1 - ρ - δ_fld) / (δ_fld * (1 - ρ - 2 * δ_fld) * Fintype.card F))
            ((n * δ_fld + γ) / (γ * Fintype.card F))
      t492Bound ≤ smallBound) :
    let n : ℝ := Fintype.card ι
    let ρ : ℝ := k / n
    let bound : ℝ :=
      max ((1 - ρ - δ_fld) / (δ_fld * (1 - ρ - 2 * δ_fld) * Fintype.card F))
          ((n * δ_fld + γ) / (γ * Fintype.card F))
    epsCA (F := F) (A := F) ((ReedSolomon.code domain k : Set (ι → F))) δ_fld δ_fld ≤
      ENNReal.ofReal bound := by
  intro n ρ bound
  have hfloor := r4_10_floor_collapse_of_no_boundary_crossing δ_fld γ hcross
  exact rs_epsCA_small_loss_r4_10_of_residuals domain k δ_fld γ hT492 hfloor hbound

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

/-- The closed-form real RHS of the BCHKS25/Hab25 Johnson-range RS MCA bound.

This is the value wrapped by `ENNReal.ofReal` in `rs_epsMCA_johnson_range_bchks25`; it is named
separately so Hab25 residual surfaces and Grand-MCA consumers can share the exact same numeric
target without duplicating the expression. -/
noncomputable def rs_epsMCA_johnson_range_boundReal
    (_domain : ι ↪ F) (k : ℕ) (η δ : ℝ≥0) : ℝ :=
  let n : ℝ := Fintype.card ι
  let ρ_plus : ℝ := k / n + 1 / n
  let m : ℝ := max ⌈(ρ_plus ^ ((1 : ℝ) / 2)) / (2 * η)⌉ 3
  ((2 * (m + 1/2) ^ 5 + 3 * (m + 1/2) * δ * ρ_plus)
      / (3 * ρ_plus ^ ((3 : ℝ) / 2)) * n
    + (m + 1/2) / ρ_plus ^ ((1 : ℝ) / 2))
     / (Fintype.card F : ℝ)

/-- **The T4.12 Johnson-range RS MCA bound is non-negative.** Every factor of
`rs_epsMCA_johnson_range_boundReal` is non-negative once `n = |ι| > 0` (so `ρ₊ = k/n + 1/n > 0`):
the multiplicity `m = max(⌈√ρ₊/(2η)⌉, 3) ≥ 3 > 0`, the quintic/linear numerator, the
`ρ₊^{3/2}`, `ρ₊^{1/2}` denominators, `n`, `δ ≥ 0`, and `|F|` are all non-negative. This confirms the
bound is genuinely informative rather than vacuously truncated by the `ENNReal.ofReal` wrapper in
`rs_epsMCA_johnson_range_bchks25` — addressing the proximity-radius truncation concern documented
at the top of this file. Pure real arithmetic; no coding-theory content. -/
theorem rs_epsMCA_johnson_range_boundReal_nonneg
    (domain : ι ↪ F) (k : ℕ) (η δ : ℝ≥0) (hn : 0 < (Fintype.card ι : ℝ)) :
    0 ≤ rs_epsMCA_johnson_range_boundReal domain k η δ := by
  unfold rs_epsMCA_johnson_range_boundReal
  have hρ : 0 < (k : ℝ) / Fintype.card ι + 1 / Fintype.card ι := by positivity
  have hm : 0 ≤ max (⌈((k : ℝ) / Fintype.card ι + 1 / Fintype.card ι) ^ ((1 : ℝ) / 2)
      / (2 * (η : ℝ))⌉ : ℝ) 3 :=
    le_trans (by norm_num) (le_max_right _ _)
  positivity

/-- The Johnson-range side condition used by BCHKS25/Hab25 T4.12. -/
def rs_epsMCA_johnson_range_condition
    (_domain : ι ↪ F) (k : ℕ) (η δ : ℝ≥0) : Prop :=
  (δ : ℝ) <
    1 - (((k : ℝ) / Fintype.card ι + 1 / Fintype.card ι) ^ ((1 : ℝ) / 2)) - (η : ℝ)

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
    (_hδ : rs_epsMCA_johnson_range_condition domain k η δ) : Prop :=
    epsMCA (F := F) (A := F) ((ReedSolomon.code domain k : Set (ι → F))) δ ≤
      ENNReal.ofReal (rs_epsMCA_johnson_range_boundReal domain k η δ)
  -- Missing ingredient: BCHKS25 Thm 4.6's explicit RS MCA bound in the Johnson range
  -- δ<1-√ρ₊-η. The (m+½)⁵ / ρ₊^{3/2} polynomial in the multiplicity parameter
  -- m=max(⌈√ρ₊/(2η)⌉,3) comes from the BCHKS25 multiplicity-coded RS list-decoder analysis;
  -- needs the m-multiplicity RS interpolation bound (not in-tree). Genuinely external.

/-- Public T4.12 wrapper from the named closed-form Johnson-range bound. -/
theorem rs_epsMCA_johnson_range_bchks25_of_bound
    (domain : ι ↪ F) (k : ℕ) (η δ : ℝ≥0)
    (hη : 0 < η) (hδ : rs_epsMCA_johnson_range_condition domain k η δ)
    (hbound :
      epsMCA (F := F) (A := F) ((ReedSolomon.code domain k : Set (ι → F))) δ ≤
        ENNReal.ofReal (rs_epsMCA_johnson_range_boundReal domain k η δ)) :
    rs_epsMCA_johnson_range_bchks25 domain k η δ hη hδ := by
  simpa [rs_epsMCA_johnson_range_bchks25] using hbound

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

/-- Fixed-code payload for the BCHKS25+KK25 near-capacity lower-bound construction.

The public T4.16 statement is existential over the domain, field, and smooth RS code. This
package exposes the same data once those types are fixed, so downstream Grand-MCA code can
consume a concrete near-capacity CA lower-bound witness without unpacking the full existential
statement. -/
structure RSLowerCapacityWitness
    (c ρ : ℝ≥0)
    (ιC : Type) [Fintype ιC] [Nonempty ιC] [DecidableEq ιC]
    (FC : Type) [Field FC] [Fintype FC] [DecidableEq FC] where
  domain : ιC ↪ FC
  smooth : ReedSolomon.Smooth domain
  k : ℕ
  slack : ℝ≥0
  primeField : ∃ p : ℕ, p.Prime ∧ CharP FC p ∧ Fintype.card FC = p
  fieldPolyBound : ∃ a b : ℕ, Fintype.card FC ≤ a * (Fintype.card ιC) ^ b
  rate_eq : (k : ℝ) / Fintype.card ιC = ρ
  epsCA_lower :
    ((Fintype.card ιC : ENNReal) ^ (c : ℝ)) / (Fintype.card FC : ENNReal) ≤
      epsCA (F := FC) (A := FC) ((ReedSolomon.code domain k : Set (ιC → FC)))
        (1 - ρ - slack) (1 - ρ - slack)

/-- A packaged near-capacity witness reassembles the external T4.16 statement. -/
theorem rs_epsCA_lower_capacity_bchks25_kk25_of_witness
    (c : ℝ≥0) (hc : 0 < c) (ρ : ℝ≥0) (hρ_pos : 0 < ρ)
    (hρ_lt : ρ < (1 / 2 : ℝ≥0))
    {ιC : Type} [Fintype ιC] [Nonempty ιC] [DecidableEq ιC]
    {FC : Type} [Field FC] [Fintype FC] [DecidableEq FC]
    (W : RSLowerCapacityWitness c ρ ιC FC) :
    rs_epsCA_lower_capacity_bchks25_kk25 c hc ρ hρ_pos hρ_lt := by
  exact ⟨ιC, inferInstance, inferInstance, inferInstance,
    FC, inferInstance, inferInstance, inferInstance,
    W.domain, W.smooth, W.k, W.slack,
    W.primeField, W.fieldPolyBound, W.rate_eq, W.epsCA_lower⟩

/-- Conversely, the existential T4.16 statement yields a named witness package for one
domain/field pair. -/
theorem exists_rsLowerCapacityWitness_of_bchks25_kk25
    (c : ℝ≥0) (hc : 0 < c) (ρ : ℝ≥0) (hρ_pos : 0 < ρ)
    (hρ_lt : ρ < (1 / 2 : ℝ≥0))
    (h : rs_epsCA_lower_capacity_bchks25_kk25 c hc ρ hρ_pos hρ_lt) :
    ∃ (ιC : Type) (_ : Fintype ιC) (_ : Nonempty ιC) (_ : DecidableEq ιC)
      (FC : Type) (_ : Field FC) (_ : Fintype FC) (_ : DecidableEq FC),
      Nonempty (RSLowerCapacityWitness c ρ ιC FC) := by
  rcases h with ⟨ιC, hFintypeι, hNonemptyι, hDecEqι,
    FC, hField, hFintypeF, hDecEqF, domain, hsmooth, k, slack,
    hprime, hpoly, hrate, heps⟩
  letI := hFintypeι
  letI := hNonemptyι
  letI := hDecEqι
  letI := hField
  letI := hFintypeF
  letI := hDecEqF
  exact ⟨ιC, hFintypeι, hNonemptyι, hDecEqι,
    FC, hField, hFintypeF, hDecEqF,
    ⟨⟨domain, hsmooth, k, slack, hprime, hpoly, hrate, heps⟩⟩⟩

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

/-- The hard lower-bound half of CS25 complete CA breakdown.

This is the current epsCA-facing target for the missing qEntropy/RS-ball-count argument:
under the CS25 entropy-band hypotheses, enough RS codewords in a Hamming ball should force
`ε_ca(RS, δ, δ) = 1`'s nontrivial `≥ 1` direction.  The routine `≤ 1` half is already
checked by `rs_epsCA_breakdown_cs25_of_lower_bound`. -/
def rs_epsCA_breakdown_cs25_entropyBallLowerWitness
    (domain : ι ↪ F) (k : ℕ) (δ : ℝ≥0)
    (_hq_ge : 10 ≤ Fintype.card F)
    (_hδ_lo :
        1 - qEntropy (Fintype.card F) (δ : ℝ) + 2 / (Fintype.card ι : ℝ)
            + ((qEntropy (Fintype.card F) (δ : ℝ) - (δ : ℝ))
                / (Fintype.card ι : ℝ)) ^ ((1 : ℝ) / 2)
          ≤ (k : ℝ) / Fintype.card ι)
    (_hδ_hi : (k : ℝ) / Fintype.card ι ≤ 1 - (δ : ℝ) - 2 / (Fintype.card ι : ℝ)) :
    Prop :=
  1 ≤ epsCA (F := F) (A := F) ((ReedSolomon.code domain k : Set (ι → F))) δ δ

/-- Checked bridge for the CS25 breakdown statement.

Since `epsCA` is always at most `1`, the complete-breakdown equality is reduced to the
paper's hard lower-bound half in the entropy band. -/
theorem rs_epsCA_breakdown_cs25_of_lower_bound
    (domain : ι ↪ F) (k : ℕ) (δ : ℝ≥0)
    (hq_ge : 10 ≤ Fintype.card F)
    (hδ_lo :
        1 - qEntropy (Fintype.card F) (δ : ℝ) + 2 / (Fintype.card ι : ℝ)
            + ((qEntropy (Fintype.card F) (δ : ℝ) - (δ : ℝ))
                / (Fintype.card ι : ℝ)) ^ ((1 : ℝ) / 2)
          ≤ (k : ℝ) / Fintype.card ι)
    (hδ_hi : (k : ℝ) / Fintype.card ι ≤ 1 - (δ : ℝ) - 2 / (Fintype.card ι : ℝ))
    (hlower :
        1 ≤ epsCA (F := F) (A := F) ((ReedSolomon.code domain k : Set (ι → F))) δ δ) :
    rs_epsCA_breakdown_cs25 domain k δ hq_ge hδ_lo hδ_hi := by
  classical
  refine le_antisymm ?_ hlower
  unfold epsCA
  refine iSup_le fun u => ?_
  by_cases hjp :
      Code.jointProximity (C := ((ReedSolomon.code domain k : Set (ι → F)))) (u := u) δ
  · rw [if_pos hjp]
    exact zero_le _
  · rw [if_neg hjp]
    rw [prob_tsum_form_singleton]
    exact le_trans (ENNReal.tsum_le_tsum fun γ => by
      by_cases hγ : δᵣ(u 0 + γ • u 1,
          (ReedSolomon.code domain k : Set (ι → F))) ≤ δ <;> simp [hγ])
      (PMF.tsum_coe (PMF.uniformOfFintype F)).le

/-- CS25 breakdown from the named entropy/RS-ball-count lower-bound witness. -/
theorem rs_epsCA_breakdown_cs25_of_entropyBallLowerWitness
    (domain : ι ↪ F) (k : ℕ) (δ : ℝ≥0)
    (hq_ge : 10 ≤ Fintype.card F)
    (hδ_lo :
        1 - qEntropy (Fintype.card F) (δ : ℝ) + 2 / (Fintype.card ι : ℝ)
            + ((qEntropy (Fintype.card F) (δ : ℝ) - (δ : ℝ))
                / (Fintype.card ι : ℝ)) ^ ((1 : ℝ) / 2)
          ≤ (k : ℝ) / Fintype.card ι)
    (hδ_hi : (k : ℝ) / Fintype.card ι ≤ 1 - (δ : ℝ) - 2 / (Fintype.card ι : ℝ))
    (hlower :
      rs_epsCA_breakdown_cs25_entropyBallLowerWitness domain k δ hq_ge hδ_lo hδ_hi) :
    rs_epsCA_breakdown_cs25 domain k δ hq_ge hδ_lo hδ_hi :=
  rs_epsCA_breakdown_cs25_of_lower_bound domain k δ hq_ge hδ_lo hδ_hi hlower

/-- **Reduction of the #82 entropy-ball lower witness to a covered bad-line stack.**

Wires `ProximityGap.one_le_epsCA_of_line_covered` (Errors.lean) into the CS25 breakdown
residual: the witness `1 ≤ ε_ca(RS)` follows from any stack `u` that is *not* jointly `δ`-close
to the RS code yet whose entire affine line `u 0 + γ • u 1` is `δ`-close to it.  This relocates
the genuine open content of #82 to the named hypotheses `hu`/`hcover` — the CS25 *covering*
construction in the entropy band (still absent in-tree; to be fed by the proven
`linear_lambda_ge_entropy_volume`).  It does **not** close #82. -/
theorem rs_epsCA_breakdown_cs25_entropyBallLowerWitness_of_covered_stack
    (domain : ι ↪ F) (k : ℕ) (δ : ℝ≥0)
    (hq_ge : 10 ≤ Fintype.card F)
    (hδ_lo :
        1 - qEntropy (Fintype.card F) (δ : ℝ) + 2 / (Fintype.card ι : ℝ)
            + ((qEntropy (Fintype.card F) (δ : ℝ) - (δ : ℝ))
                / (Fintype.card ι : ℝ)) ^ ((1 : ℝ) / 2)
          ≤ (k : ℝ) / Fintype.card ι)
    (hδ_hi : (k : ℝ) / Fintype.card ι ≤ 1 - (δ : ℝ) - 2 / (Fintype.card ι : ℝ))
    (u : Fin 2 → ι → F)
    (hu : ¬ Code.jointProximity (C := (ReedSolomon.code domain k : Set (ι → F))) (u := u) δ)
    (hcover : ∀ γ : F,
        δᵣ(u 0 + γ • u 1, (ReedSolomon.code domain k : Set (ι → F))) ≤ δ) :
    rs_epsCA_breakdown_cs25_entropyBallLowerWitness domain k δ hq_ge hδ_lo hδ_hi := by
  unfold rs_epsCA_breakdown_cs25_entropyBallLowerWitness
  exact ProximityGap.one_le_epsCA_of_line_covered
    (ReedSolomon.code domain k : Set (ι → F)) δ δ u hu hcover

/-- **CS25 complete-breakdown front door from a covered bad-line stack.**

This composes `rs_epsCA_breakdown_cs25_entropyBallLowerWitness_of_covered_stack` with the
checked lower-bound-to-breakdown bridge. The remaining input is a concrete stack whose whole
affine line is `δ`-close to the Reed-Solomon code while the stack itself is not jointly
`δ`-close. -/
theorem rs_epsCA_breakdown_cs25_of_covered_stack
    (domain : ι ↪ F) (k : ℕ) (δ : ℝ≥0)
    (hq_ge : 10 ≤ Fintype.card F)
    (hδ_lo :
        1 - qEntropy (Fintype.card F) (δ : ℝ) + 2 / (Fintype.card ι : ℝ)
            + ((qEntropy (Fintype.card F) (δ : ℝ) - (δ : ℝ))
                / (Fintype.card ι : ℝ)) ^ ((1 : ℝ) / 2)
          ≤ (k : ℝ) / Fintype.card ι)
    (hδ_hi : (k : ℝ) / Fintype.card ι ≤ 1 - (δ : ℝ) - 2 / (Fintype.card ι : ℝ))
    (u : Fin 2 → ι → F)
    (hu : ¬ Code.jointProximity (C := (ReedSolomon.code domain k : Set (ι → F))) (u := u) δ)
    (hcover : ∀ γ : F,
        δᵣ(u 0 + γ • u 1, (ReedSolomon.code domain k : Set (ι → F))) ≤ δ) :
    rs_epsCA_breakdown_cs25 domain k δ hq_ge hδ_lo hδ_hi :=
  rs_epsCA_breakdown_cs25_of_entropyBallLowerWitness domain k δ hq_ge hδ_lo hδ_hi
    (rs_epsCA_breakdown_cs25_entropyBallLowerWitness_of_covered_stack
      domain k δ hq_ge hδ_lo hδ_hi u hu hcover)

open Classical in
/-- **Reduction of the #82 entropy-ball lower witness to the combined CS25 count budget.**

This routes the mechanical count-budget theorem `ProximityGap.one_le_epsCA_of_counts` into the
Reed-Solomon CS25 breakdown residual. The remaining mathematical input is exactly the CS25
counting claim that the total far-line count plus the jointly-close stack count is below the
total number of stacks in the entropy band. -/
theorem rs_epsCA_breakdown_cs25_entropyBallLowerWitness_of_counts
    (domain : ι ↪ F) (k : ℕ) (δ : ℝ≥0)
    (hq_ge : 10 ≤ Fintype.card F)
    (hδ_lo :
        1 - qEntropy (Fintype.card F) (δ : ℝ) + 2 / (Fintype.card ι : ℝ)
            + ((qEntropy (Fintype.card F) (δ : ℝ) - (δ : ℝ))
                / (Fintype.card ι : ℝ)) ^ ((1 : ℝ) / 2)
          ≤ (k : ℝ) / Fintype.card ι)
    (hδ_hi : (k : ℝ) / Fintype.card ι ≤ 1 - (δ : ℝ) - 2 / (Fintype.card ι : ℝ))
    (hsum :
      (∑ u : Code.WordStack F (Fin 2) ι,
          (Finset.univ.filter (fun γ : F =>
            ¬ δᵣ(u 0 + γ • u 1, (ReedSolomon.code domain k : Set (ι → F))) ≤ δ)).card)
        + (Finset.univ.filter (fun u : Code.WordStack F (Fin 2) ι =>
            Code.jointProximity (C := (ReedSolomon.code domain k : Set (ι → F))) (u := u) δ)).card
      < Fintype.card (Code.WordStack F (Fin 2) ι)) :
    rs_epsCA_breakdown_cs25_entropyBallLowerWitness domain k δ hq_ge hδ_lo hδ_hi := by
  unfold rs_epsCA_breakdown_cs25_entropyBallLowerWitness
  exact ProximityGap.one_le_epsCA_of_counts
    (F := F) (A := F) (ReedSolomon.code domain k : Set (ι → F)) δ hsum

open Classical in
/-- **CS25 complete-breakdown front door from the combined count budget.**

This composes `rs_epsCA_breakdown_cs25_entropyBallLowerWitness_of_counts` with the checked
lower-bound-to-breakdown bridge. The only remaining CS25-specific input is the same combined
far-line plus jointly-close stack count inequality. -/
theorem rs_epsCA_breakdown_cs25_of_counts
    (domain : ι ↪ F) (k : ℕ) (δ : ℝ≥0)
    (hq_ge : 10 ≤ Fintype.card F)
    (hδ_lo :
        1 - qEntropy (Fintype.card F) (δ : ℝ) + 2 / (Fintype.card ι : ℝ)
            + ((qEntropy (Fintype.card F) (δ : ℝ) - (δ : ℝ))
                / (Fintype.card ι : ℝ)) ^ ((1 : ℝ) / 2)
          ≤ (k : ℝ) / Fintype.card ι)
    (hδ_hi : (k : ℝ) / Fintype.card ι ≤ 1 - (δ : ℝ) - 2 / (Fintype.card ι : ℝ))
    (hsum :
      (∑ u : Code.WordStack F (Fin 2) ι,
          (Finset.univ.filter (fun γ : F =>
            ¬ δᵣ(u 0 + γ • u 1, (ReedSolomon.code domain k : Set (ι → F))) ≤ δ)).card)
        + (Finset.univ.filter (fun u : Code.WordStack F (Fin 2) ι =>
            Code.jointProximity (C := (ReedSolomon.code domain k : Set (ι → F))) (u := u) δ)).card
      < Fintype.card (Code.WordStack F (Fin 2) ι)) :
    rs_epsCA_breakdown_cs25 domain k δ hq_ge hδ_lo hδ_hi :=
  rs_epsCA_breakdown_cs25_of_entropyBallLowerWitness domain k δ hq_ge hδ_lo hδ_hi
    (rs_epsCA_breakdown_cs25_entropyBallLowerWitness_of_counts
      domain k δ hq_ge hδ_lo hδ_hi hsum)

/-- The ABF26 T4.18 Johnson radius for the fixed relative distance `15/16`.  This is kept
as a named expression so the existential construction and Grand-MCA adapters use the same
radius literal. -/
noncomputable def johnsonJumpRadius : ℝ≥0 :=
  (((1 : ℝ) - (1 - ((15 : ℝ) / 16)) ^ ((1 : ℝ) / 2)).toNNReal)

/-- The proximity-loss internal radius appearing in ABF26 T4.18 for a domain of size `n`. -/
noncomputable def johnsonJumpInternalRadius (n : ℕ) : ℝ≥0 :=
  (((1 : ℝ) - (1 - ((15 : ℝ) / 16)) ^ ((1 : ℝ) / 2)
      + 1 / 8 + 1 / (n : ℝ)).toNNReal)

/-- The fixed ABF26 T4.18 Johnson radius is `J(15/16) = 3/4`. -/
theorem johnsonJumpRadius_eq_three_fourths :
    johnsonJumpRadius = (3 / 4 : ℝ≥0) := by
  rw [johnsonJumpRadius]
  have hsqrt :
      ((1 : ℝ) - ((15 : ℝ) / 16)) ^ ((1 : ℝ) / 2) = (1 / 4 : ℝ) := by
    rw [← Real.sqrt_eq_rpow]
    have hbase : (1 - (15 : ℝ) / 16) = (1 / 4 : ℝ) ^ 2 := by norm_num
    rw [hbase, Real.sqrt_sq_eq_abs]
    norm_num
  rw [hsqrt]
  apply NNReal.coe_injective
  change (((1 : ℝ) - 1 / 4).toNNReal : ℝ) = (3 / 4 : ℝ)
  rw [Real.coe_toNNReal ((1 : ℝ) - 1 / 4) (by norm_num)]
  norm_num

/-- The fixed ABF26 T4.18 Johnson-jump radius is strictly positive (`= 3/4`). A proximity radius
in `(0, 1)` is the standard well-formedness condition for the T4.18 witness construction. -/
theorem johnsonJumpRadius_pos : 0 < johnsonJumpRadius := by
  rw [johnsonJumpRadius_eq_three_fourths]; norm_num

/-- The fixed ABF26 T4.18 Johnson-jump radius is below `1` (`3/4 < 1`), completing the
`(0, 1)` proximity-radius well-formedness alongside `johnsonJumpRadius_pos`. -/
theorem johnsonJumpRadius_lt_one : johnsonJumpRadius < 1 := by
  rw [johnsonJumpRadius_eq_three_fourths]; norm_num

/-- The ABF26 T4.18 internal radius is `7/8 + 1/n` after simplifying `J(15/16)`. -/
theorem johnsonJumpInternalRadius_eq_seven_eighths_add_inv (n : ℕ) :
    johnsonJumpInternalRadius n = (((7 : ℝ) / 8 + 1 / (n : ℝ)).toNNReal) := by
  rw [johnsonJumpInternalRadius]
  have hsqrt :
      ((1 : ℝ) - ((15 : ℝ) / 16)) ^ ((1 : ℝ) / 2) = (1 / 4 : ℝ) := by
    rw [← Real.sqrt_eq_rpow]
    have hbase : (1 - (15 : ℝ) / 16) = (1 / 4 : ℝ) ^ 2 := by norm_num
    rw [hbase, Real.sqrt_sq_eq_abs]
    norm_num
  rw [hsqrt]
  congr
  ring

/-- The no-loss Johnson-jump radius is always below the proximity-loss internal radius. -/
theorem johnsonJumpRadius_le_internalRadius (n : ℕ) :
    johnsonJumpRadius ≤ johnsonJumpInternalRadius n := by
  dsimp [johnsonJumpRadius, johnsonJumpInternalRadius]
  apply Real.toNNReal_mono
  nlinarith [show (0 : ℝ) ≤ 1 / 8 by norm_num,
    show (0 : ℝ) ≤ 1 / (n : ℝ) by positivity]

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
          johnsonJumpRadius
          (johnsonJumpInternalRadius (Fintype.card ιC)) ≥
        ((Fintype.card ιC : ENNReal) ^ (2 * ((1 : ℝ) - ε)))
          / (Fintype.card FC : ENNReal)
  -- Missing ingredient: BCHKS25's char-2 CA-jump CONSTRUCTION at the Johnson bound. LOWER
  -- bound ε_ca ≥ n^{2(1-ε)}/|F| at the Johnson radius J(15/16)=3/4, witnessed by a char-2 RS
  -- code with n≈|F|^{(1+ε)/2} and δ_min=15/16. Requires the char-2 subfield construction
  -- exhibiting the sharp proximity-gap discontinuity at J(δ_min). Code-construction lower
  -- bound; trivial epsCA≤1 is the wrong direction; no in-tree witness generator. Genuinely
  -- external.

/-- Named payload for the BCHKS25 Johnson-jump construction.

The external theorem `rs_epsCA_johnson_jump_bchks25` is existential over the domain and
message dimension.  This structure exposes the witness data at a fixed domain type, so
downstream Grand-MCA code can consume the lower-bound construction without unpacking the
whole theorem statement each time. -/
structure RSJohnsonJumpWitness
    {FC : Type} [Field FC] [Fintype FC] [DecidableEq FC] [CharP FC 2]
    (ε : ℝ≥0) (ιC : Type) [Fintype ιC] [Nonempty ιC] [DecidableEq ιC] where
  domain : ιC ↪ FC
  k : ℕ
  card_lower :
    ((Fintype.card FC : ℝ) ^ (((1 : ℝ) + ε) / 2) - 1
        ≤ (Fintype.card ιC : ℝ))
  card_upper :
    ((Fintype.card ιC : ℝ)
        ≤ (Fintype.card FC : ℝ) ^ (((1 : ℝ) + ε) / 2) + 1)
  minDist_eq :
    (Code.minDist ((ReedSolomon.code domain k : Set (ιC → FC))) : ℝ)
        / Fintype.card ιC = (15 : ℝ) / 16
  epsCA_lower :
    ((Fintype.card ιC : ENNReal) ^ (2 * ((1 : ℝ) - ε)))
        / (Fintype.card FC : ENNReal) ≤
      epsCA (F := FC) (A := FC) ((ReedSolomon.code domain k : Set (ιC → FC)))
        johnsonJumpRadius
        (johnsonJumpInternalRadius (Fintype.card ιC))

/-- A packaged Johnson-jump witness reassembles the external T4.18 statement. -/
theorem rs_epsCA_johnson_jump_bchks25_of_witness
    {FC : Type} [Field FC] [Fintype FC] [DecidableEq FC] [CharP FC 2]
    (ε : ℝ≥0) (hε : 0 < ε)
    {ιC : Type} [Fintype ιC] [Nonempty ιC] [DecidableEq ιC]
    (W : RSJohnsonJumpWitness (FC := FC) ε ιC) :
    rs_epsCA_johnson_jump_bchks25 (FC := FC) ε hε := by
  exact ⟨ιC, inferInstance, inferInstance, inferInstance, W.domain, W.k,
    W.card_lower, W.card_upper, W.minDist_eq, W.epsCA_lower⟩

/-- Conversely, the existential T4.18 statement yields a named witness package for one
domain type. -/
theorem exists_rsJohnsonJumpWitness_of_bchks25
    {FC : Type} [Field FC] [Fintype FC] [DecidableEq FC] [CharP FC 2]
    (ε : ℝ≥0) (hε : 0 < ε)
    (h : rs_epsCA_johnson_jump_bchks25 (FC := FC) ε hε) :
    ∃ (ιC : Type) (_ : Fintype ιC) (_ : Nonempty ιC) (_ : DecidableEq ιC),
      Nonempty (RSJohnsonJumpWitness (FC := FC) ε ιC) := by
  rcases h with ⟨ιC, hFintype, hNonempty, hDecEq, domain, k,
    hcard_lower, hcard_upper, hminDist, heps⟩
  letI := hFintype
  letI := hNonempty
  letI := hDecEq
  exact ⟨ιC, hFintype, hNonempty, hDecEq,
    ⟨⟨domain, k, hcard_lower, hcard_upper, hminDist, heps⟩⟩⟩

/-- **Good-γ front door for the T4.18 `epsCA_lower` obligation.**

The hard `epsCA_lower` field of `RSJohnsonJumpWitness` asks for
`n^{2(1-ε)} / |F| ≤ ε_ca(C, J, J')`. This lemma reduces that supremum lower bound to a
single explicit *witness stack* `u` (not jointly `J'`-close at the internal radius) together
with an explicit finite set `Γ` of "good combiners" whose count dominates `n^{2(1-ε)}`.

It is the Johnson-jump specialization of `ProximityGap.epsCA_ge_card_good_gamma_div_card`:
the genuinely external BCHKS25 construction must supply (i) a non-jointly-close pair of words
and (ii) at least `n^{2(1-ε)}` scalars `γ` at which the line `u 0 + γ • u 1` is
`J(15/16)`-close to `C`.  Given those two finite pieces of data this lemma discharges the
`ε_ca` lower bound automatically, turning the `iSup` obligation into a `Finset.card` count.
The supremum plumbing and `ENNReal` division monotonicity are fully proven here; only the
existence of the bad word-pair and the good-`γ` count remain external inputs. -/
theorem johnsonJump_epsCA_lower_of_goodGamma
    {FC : Type} [Field FC] [Fintype FC] [DecidableEq FC] [CharP FC 2]
    {ιC : Type} [Fintype ιC] [Nonempty ιC] [DecidableEq ιC]
    (ε : ℝ≥0)
    (domain : ιC ↪ FC) (k : ℕ)
    (u : Fin 2 → ιC → FC)
    (hjp : ¬ Code.jointProximity (C := (ReedSolomon.code domain k : Set (ιC → FC)))
      (u := u) (johnsonJumpInternalRadius (Fintype.card ιC)))
    (Γ : Finset FC)
    (hΓ : ∀ γ ∈ Γ, δᵣ(u 0 + γ • u 1,
        (ReedSolomon.code domain k : Set (ιC → FC))) ≤ johnsonJumpRadius)
    (hcount :
      ((Fintype.card ιC : ENNReal) ^ (2 * ((1 : ℝ) - (ε : ℝ))))
        ≤ ((Γ.card : ℝ≥0) : ENNReal)) :
    ((Fintype.card ιC : ENNReal) ^ (2 * ((1 : ℝ) - ε)))
        / (Fintype.card FC : ENNReal) ≤
      epsCA (F := FC) (A := FC) ((ReedSolomon.code domain k : Set (ιC → FC)))
        johnsonJumpRadius
        (johnsonJumpInternalRadius (Fintype.card ιC)) := by
  refine le_trans ?_
    (ProximityGap.epsCA_ge_card_good_gamma_div_card
      (F := FC) (A := FC)
      ((ReedSolomon.code domain k : Set (ιC → FC)))
      johnsonJumpRadius
      (johnsonJumpInternalRadius (Fintype.card ιC))
      u hjp Γ hΓ)
  exact ENNReal.div_le_div_right hcount _

/-- **Constructor for the T4.18 witness package from explicit good-γ counting data.**

Assembles a full `RSJohnsonJumpWitness` from the geometric data (domain, message dimension,
domain-size bounds, `δ_min = 15/16`) plus an explicit non-jointly-close stack `u` and a
good-combiner set `Γ` whose count dominates `n^{2(1-ε)}`. The hard `epsCA_lower` field is
discharged by `johnsonJump_epsCA_lower_of_goodGamma`.

This is the in-tree front door for the BCHKS25 construction: a prover supplies the explicit
char-2 RS code, the bad word-pair, and the good-combiner count, and obtains the packaged
witness (hence the external T4.18 statement via `rs_epsCA_johnson_jump_bchks25_of_witness`)
without re-deriving the `iSup` lower bound by hand. -/
noncomputable def RSJohnsonJumpWitness.ofGoodGammaCount
    {FC : Type} [Field FC] [Fintype FC] [DecidableEq FC] [CharP FC 2]
    {ιC : Type} [Fintype ιC] [Nonempty ιC] [DecidableEq ιC]
    (ε : ℝ≥0)
    (domain : ιC ↪ FC) (k : ℕ)
    (card_lower :
      ((Fintype.card FC : ℝ) ^ (((1 : ℝ) + ε) / 2) - 1
          ≤ (Fintype.card ιC : ℝ)))
    (card_upper :
      ((Fintype.card ιC : ℝ)
          ≤ (Fintype.card FC : ℝ) ^ (((1 : ℝ) + ε) / 2) + 1))
    (minDist_eq :
      (Code.minDist ((ReedSolomon.code domain k : Set (ιC → FC))) : ℝ)
          / Fintype.card ιC = (15 : ℝ) / 16)
    (u : Fin 2 → ιC → FC)
    (hjp : ¬ Code.jointProximity (C := (ReedSolomon.code domain k : Set (ιC → FC)))
      (u := u) (johnsonJumpInternalRadius (Fintype.card ιC)))
    (Γ : Finset FC)
    (hΓ : ∀ γ ∈ Γ, δᵣ(u 0 + γ • u 1,
        (ReedSolomon.code domain k : Set (ιC → FC))) ≤ johnsonJumpRadius)
    (hcount :
      ((Fintype.card ιC : ENNReal) ^ (2 * ((1 : ℝ) - (ε : ℝ))))
        ≤ ((Γ.card : ℝ≥0) : ENNReal)) :
    RSJohnsonJumpWitness (FC := FC) ε ιC where
  domain := domain
  k := k
  card_lower := card_lower
  card_upper := card_upper
  minDist_eq := minDist_eq
  epsCA_lower :=
    johnsonJump_epsCA_lower_of_goodGamma ε domain k u hjp Γ hΓ hcount

/-- The packaged good-γ data directly yields the external T4.18 statement, via the witness
package.  This is the maximal in-tree reduction of T4.18: everything except the existence of
the bad word-pair and the good-`γ` count is now proven. -/
theorem rs_epsCA_johnson_jump_bchks25_of_goodGamma
    {FC : Type} [Field FC] [Fintype FC] [DecidableEq FC] [CharP FC 2]
    {ιC : Type} [Fintype ιC] [Nonempty ιC] [DecidableEq ιC]
    (ε : ℝ≥0) (hε : 0 < ε)
    (domain : ιC ↪ FC) (k : ℕ)
    (card_lower :
      ((Fintype.card FC : ℝ) ^ (((1 : ℝ) + ε) / 2) - 1
          ≤ (Fintype.card ιC : ℝ)))
    (card_upper :
      ((Fintype.card ιC : ℝ)
          ≤ (Fintype.card FC : ℝ) ^ (((1 : ℝ) + ε) / 2) + 1))
    (minDist_eq :
      (Code.minDist ((ReedSolomon.code domain k : Set (ιC → FC))) : ℝ)
          / Fintype.card ιC = (15 : ℝ) / 16)
    (u : Fin 2 → ιC → FC)
    (hjp : ¬ Code.jointProximity (C := (ReedSolomon.code domain k : Set (ιC → FC)))
      (u := u) (johnsonJumpInternalRadius (Fintype.card ιC)))
    (Γ : Finset FC)
    (hΓ : ∀ γ ∈ Γ, δᵣ(u 0 + γ • u 1,
        (ReedSolomon.code domain k : Set (ιC → FC))) ≤ johnsonJumpRadius)
    (hcount :
      ((Fintype.card ιC : ENNReal) ^ (2 * ((1 : ℝ) - (ε : ℝ))))
        ≤ ((Γ.card : ℝ≥0) : ENNReal)) :
    rs_epsCA_johnson_jump_bchks25 (FC := FC) ε hε :=
  rs_epsCA_johnson_jump_bchks25_of_witness ε hε
    (RSJohnsonJumpWitness.ofGoodGammaCount ε domain k
      card_lower card_upper minDist_eq u hjp Γ hΓ hcount)

end ReedSolomon

/-! ## Covering-radius sampling — ABF26 §4 ([DG25])

Disposition (issue #48, #77): Prop front door retained here; the covering-radius sampling
identity is discharged in `DG25Sampling.lean`.
An *upper*-witness feeder (`ε_ca` lower bound) for the Grand MCA threshold. See the
file-level disposition ledger. -/

section Sampling

open scoped ProbabilityTheory

variable {ι : Type} [Fintype ι] [Nonempty ι] [DecidableEq ι]
variable {F : Type} [Field F] [Fintype F] [DecidableEq F]

/-- The DG25 L4.19 sampling lower-bound mass:
`((|F|-1)/|F|) · Pr_u[Δ(u,C) ≤ δ]`. -/
noncomputable def linear_epsCA_sampling_dg25_mass (C : LinearCode ι F) (δ : ℝ≥0) :
    ENNReal :=
  ((Fintype.card F - 1 : ℝ≥0) / Fintype.card F : ENNReal)
      * Pr_{let u ← $ᵖ (ι → F)}[δᵣ(u, (C : Set (ι → F))) ≤ δ]

/-- **ABF26 Lemma 4.19 [DG25 Thm 2.5].** Let `C ⊆ F^n` be a linear code and let
`δ' := max_{u ∈ F^n} Δ(u, C)` be the (relative) covering radius. For every
`δ ∈ (0, δ')`:

  `ε_ca(C, δ) ≥ ((q-1)/q) · Pr_{u ← F^n}[Δ(u, C) ≤ δ]`

The probability is over a uniform word in `F^n`, expressed via the `Pr_{...}[...]`
notation. This Prop front door is retained for downstream APIs; `DG25Sampling.lean`
discharges it through `CodingTheory.linear_epsCA_ge_sampling_dg25_proof`. -/
def linear_epsCA_ge_sampling_dg25
    (C : LinearCode ι F) (δ δ' : ℝ≥0)
    (_h_δ' : (δ' : ENNReal) = ⨆ u : ι → F, δᵣ(u, (C : Set (ι → F))))
    (_hδ_pos : 0 < δ) (_hδ_lt : δ < δ') : Prop :=
    linear_epsCA_sampling_dg25_mass C δ ≤
      epsCA (F := F) (A := F) ((C : Set (ι → F))) δ δ
  -- Proof assembly is in `DG25Sampling.lean`: it chooses a word beyond the covering radius,
  -- uses the interleaved row-distance bridge to rule out joint proximity for every base word,
  -- averages line probabilities by uniform translation, and absorbs the `(q-1)/q` factor.

/-- Wrapper from the named DG25 sampling mass bound to the external L4.19 Prop shape. -/
theorem linear_epsCA_ge_sampling_dg25_of_mass_bound
    (C : LinearCode ι F) (δ δ' : ℝ≥0)
    (hδ' : (δ' : ENNReal) = ⨆ u : ι → F, δᵣ(u, (C : Set (ι → F))))
    (hδ_pos : 0 < δ) (hδ_lt : δ < δ')
    (h :
      linear_epsCA_sampling_dg25_mass C δ ≤
        epsCA (F := F) (A := F) ((C : Set (ι → F))) δ δ) :
    linear_epsCA_ge_sampling_dg25 C δ δ' hδ' hδ_pos hδ_lt :=
  h

end Sampling

/-! ## Subspace-design / FRS MCA up to capacity — ABF26 §4.2.2 ([GG25], [BCGM25])

Disposition (issue #48, refined by #76): T4.13 is a DIRECT PORT (GG25
line-stitching/list-decoding pipeline; its list-decoding input is tracked by #53); T4.14 is a
DERIVED COROLLARY of T4.13 + T2.18 (checked reduction
`frs_epsMCA_capacity_gg25_of_residuals` in-tree). The BCGM25 polynomial-generator item is now
split between the canonical generator-native surface
`polynomialGenerator_isMCAGenerator_bcgm25` and the old `epsCA_curves` survey-ledger
compatibility shadow `subspaceDesign_epsCA_curves_polynomial_generators_bcgm25`. T4.13 /
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

/-- Public T4.13 wrapper from the named GG25 subspace-design MCA bound. -/
theorem subspaceDesign_epsMCA_gg25_of_bound
    {ι : Type} [Fintype ι] [Nonempty ι] [DecidableEq ι]
    {F : Type} [Field F] [Fintype F] [DecidableEq F]
    (s : ℕ) (τ : ℕ → ℝ) (C : Submodule F (ι → Fin s → F))
    (h : IsSubspaceDesign s τ C)
    (t : ℕ) (ht : 0 < t)
    (hbound :
      epsMCA (F := F) (A := Fin s → F) ((C : Set (ι → Fin s → F)))
          ((1 - τ (t + 1) - 3 / (2 * t)).toNNReal) ≤
        ENNReal.ofReal (((t : ℝ) * Fintype.card ι + 4 * t ^ 2) / Fintype.card F)) :
    subspaceDesign_epsMCA_gg25 s τ C h t ht := by
  simpa [subspaceDesign_epsMCA_gg25] using hbound

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

/-- Public T4.14 wrapper from the named folded-RS capacity MCA bound.

The direct counterpart of `subspaceDesign_epsMCA_gg25_of_bound`: it packages the explicit
`ε_mca(FRS, 1-ρ-η) ≤ 2n/(η|F|)+24/(η³|F|)` inequality as the public `frs_epsMCA_capacity_gg25`
Prop front door, so a downstream port that establishes the final bound directly (without threading
through the T4.13/T2.18 residual bundle) closes the external statement in one step. -/
theorem frs_epsMCA_capacity_gg25_of_bound
    {ι : Type} [Fintype ι] [Nonempty ι] [DecidableEq ι]
    {F : Type} [Field F] [Fintype F] [DecidableEq F]
    (domain : ι ↪ F) (k s : ℕ) (ω : F)
    (η : ℝ) (hη_pos : 0 < η) (hη_lt : η < 1)
    (hs_gt : (s : ℝ) > 16 / η ^ 2)
    (hbound :
      let n : ℝ := Fintype.card ι
      let ρ : ℝ := k / n
      epsMCA (F := F) (A := Fin s → F)
          ((ReedSolomon.Folded.frsCode domain k s ω : Set (ι → Fin s → F)))
          ((1 - ρ - η).toNNReal) ≤
        ENNReal.ofReal (2 * n / (η * Fintype.card F)
          + 24 / (η ^ 3 * Fintype.card F))) :
    frs_epsMCA_capacity_gg25 domain k s ω η hη_pos hη_lt hs_gt := by
  simpa [frs_epsMCA_capacity_gg25] using hbound

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

/-- **ABF26 T4.14 — single T4.13 instance reduction.**

The broader residual theorem above takes the full GG25 T4.13 theorem as a universal hypothesis.
For closing a concrete folded-RS instance, it is enough to supply the one subspace-design MCA
bound at the chosen `τ`, code, and integer `t`, plus the same radius and real-bound arithmetic.
This theorem exposes that smaller target. -/
theorem frs_epsMCA_capacity_gg25_of_subspaceDesign_bound
    {ι : Type} [Fintype ι] [Nonempty ι] [DecidableEq ι]
    {F : Type} [Field F] [Fintype F] [DecidableEq F]
    (domain : ι ↪ F) (k s : ℕ) (ω : F)
    (η : ℝ) (τ : ℕ → ℝ) (t : ℕ)
    (hT413 :
      epsMCA (F := F) (A := Fin s → F)
          ((ReedSolomon.Folded.frsCode domain k s ω : Set (ι → Fin s → F)))
          ((1 - τ (t + 1) - 3 / (2 * t)).toNNReal) ≤
        ENNReal.ofReal (((t : ℝ) * Fintype.card ι + 4 * t ^ 2) / Fintype.card F))
    (hRadius :
      let n : ℝ := Fintype.card ι
      let ρ : ℝ := k / n
      ((1 - ρ - η).toNNReal : ℝ≥0) =
        (1 - τ (t + 1) - 3 / (2 * t)).toNNReal)
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
  rw [hRadius]
  exact le_trans hT413 (ENNReal.ofReal_le_ofReal hBound)

/-- Prop-level T4.14 adapter from a single public T4.13 instance.

This consumes `subspaceDesign_epsMCA_gg25` for the folded-RS code at the chosen `τ` and `t`, so
the remaining T4.14 work is exactly the FRS subspace-design input plus the explicit arithmetic
side conditions. -/
theorem frs_epsMCA_capacity_gg25_of_subspaceDesign_prop
    {ι : Type} [Fintype ι] [Nonempty ι] [DecidableEq ι]
    {F : Type} [Field F] [Fintype F] [DecidableEq F]
    (domain : ι ↪ F) (k s : ℕ) (ω : F)
    (η : ℝ) (hη_pos : 0 < η) (hη_lt : η < 1)
    (hs_gt : (s : ℝ) > 16 / η ^ 2)
    (τ : ℕ → ℝ) (t : ℕ) (ht : 0 < t)
    (hT218 : IsSubspaceDesign s τ (ReedSolomon.Folded.frsCode domain k s ω))
    (hT413 : subspaceDesign_epsMCA_gg25 s τ
        (ReedSolomon.Folded.frsCode domain k s ω) hT218 t ht)
    (hRadius :
      let n : ℝ := Fintype.card ι
      let ρ : ℝ := k / n
      ((1 - ρ - η).toNNReal : ℝ≥0) =
        (1 - τ (t + 1) - 3 / (2 * t)).toNNReal)
    (hBound :
      let n : ℝ := Fintype.card ι
      ((t : ℝ) * n + 4 * t ^ 2) / Fintype.card F ≤
        2 * n / (η * Fintype.card F) + 24 / (η ^ 3 * Fintype.card F)) :
    frs_epsMCA_capacity_gg25 domain k s ω η hη_pos hη_lt hs_gt := by
  refine frs_epsMCA_capacity_gg25_of_subspaceDesign_bound
    (domain := domain) (k := k) (s := s) (ω := ω) (η := η)
    (τ := τ) (t := t) ?_ hRadius hBound
  simpa [subspaceDesign_epsMCA_gg25] using hT413

/-- **Discharge of the T4.14 `hBound` arithmetic residual.**

The paper's informal "choose `t ≈ 1/η`" is formalized as the honest side-condition `t ≤ 2/η`.
Under it the explicit FRS capacity inequality holds with slack — `t·n ≤ 2n/η` (since `t ≤ 2/η`,
`n ≥ 0`) and `4t² ≤ 16/η² ≤ 24/η³` (since `t ≤ 2/η` and `η < 1`) — so the `hBound` hypothesis of
`frs_epsMCA_capacity_gg25_of_residuals` / `_of_subspaceDesign_prop` is no longer an external admit
but a proved consequence of `t ≤ 2/η`. Pure real arithmetic; no coding-theory content. -/
theorem frs_capacity_realBound_of_t_le (n η t cF : ℝ)
    (hn : 0 ≤ n) (hη : 0 < η) (hη_lt : η < 1) (ht : 0 < t) (hcF : 0 < cF)
    (htη : t ≤ 2 / η) :
    (t * n + 4 * t ^ 2) / cF ≤ 2 * n / (η * cF) + 24 / (η ^ 3 * cF) := by
  have hcore : t * n + 4 * t ^ 2 ≤ 2 * n / η + 24 / η ^ 3 := by
    have hη2 : (0:ℝ) < η ^ 2 := by positivity
    have hη3 : (0:ℝ) < η ^ 3 := by positivity
    have hA : t * n ≤ 2 * n / η := by
      have h := mul_le_mul_of_nonneg_right htη hn
      calc t * n ≤ (2 / η) * n := h
        _ = 2 * n / η := by ring
    have ht2 : t ^ 2 ≤ (2 / η) ^ 2 := by
      have h := mul_le_mul htη htη ht.le (by positivity : (0:ℝ) ≤ 2 / η)
      calc t ^ 2 = t * t := by ring
        _ ≤ (2 / η) * (2 / η) := h
        _ = (2 / η) ^ 2 := by ring
    have hB : 4 * t ^ 2 ≤ 24 / η ^ 3 := by
      have h2 : 4 * (2 / η) ^ 2 = 16 / η ^ 2 := by field_simp; ring
      have h3 : (16:ℝ) / η ^ 2 ≤ 24 / η ^ 3 := by
        have heq : 24 / η ^ 3 - 16 / η ^ 2 = (24 - 16 * η) / η ^ 3 := by
          field_simp; try ring
        have hnn : (0:ℝ) ≤ (24 - 16 * η) / η ^ 3 := div_nonneg (by linarith) hη3.le
        linarith [heq, hnn]
      calc 4 * t ^ 2 ≤ 4 * (2 / η) ^ 2 := by linarith [ht2]
        _ = 16 / η ^ 2 := h2
        _ ≤ 24 / η ^ 3 := h3
    linarith [hA, hB]
  have hrw : 2 * n / (η * cF) + 24 / (η ^ 3 * cF) = (2 * n / η + 24 / η ^ 3) / cF := by
    field_simp; try ring
  rw [hrw]
  gcongr

/-- **FRS subspace-design margin evaluation.** The folded-RS margin
`τ_FRS(r) = s·k/n / (s − r + 1)` (the `IsSubspaceDesign` witness from T2.18 / GK16), evaluated at
`r = t + 1` inside the design's active range `t + 1 ≤ s`, collapses the guarded `if` to its active
branch and simplifies the denominator `s − (t+1) + 1 = s − t`:

  `τ_FRS(t+1) = s·k/n / (s − t)`.

Pure rewriting of the `if`-guarded definition; a building block for the T4.14 `hRadius` residual. -/
theorem frs_tau_eval (s k : ℕ) (n : ℝ) (t : ℕ) (hts : t + 1 ≤ s) :
    (fun r : ℕ ↦ if r ∈ Finset.Icc 1 s then
        (s : ℝ) * (k : ℝ) / n / ((s : ℝ) - (r : ℝ) + 1) else 1) (t + 1)
      = (s : ℝ) * (k : ℝ) / n / ((s : ℝ) - (t : ℝ)) := by
  have hmem : (t + 1) ∈ Finset.Icc 1 s :=
    Finset.mem_Icc.mpr ⟨Nat.le_add_left 1 t, hts⟩
  show (if (t + 1) ∈ Finset.Icc 1 s then
      (s : ℝ) * (k : ℝ) / n / ((s : ℝ) - ((t + 1 : ℕ) : ℝ) + 1) else 1)
      = (s : ℝ) * (k : ℝ) / n / ((s : ℝ) - (t : ℝ))
  rw [if_pos hmem]
  have hden : (s : ℝ) - ((t + 1 : ℕ) : ℝ) + 1 = (s : ℝ) - (t : ℝ) := by push_cast; ring
  rw [hden]

/-- **Discharge of the T4.14 `hRadius` residual under the honest η-coupling.** The radius
identification `(1 − ρ − η).toNNReal = (1 − τ_FRS(t+1) − 3/(2t)).toNNReal` required by
`frs_epsMCA_capacity_gg25_of_residuals` / `_of_subspaceDesign_prop` holds whenever the proximity
slack `η` is the explicit paper value coupling the chosen integer `t` to the capacity gap,
`η = τ_FRS(t+1) − ρ + 3/(2t)` (with `ρ = k/n` and `τ_FRS(t+1) = s·k/n/(s−t)` via `frs_tau_eval`).
This turns the radius residual from an external admit into a proved consequence of the η-choice —
the radius-side analogue of `frs_capacity_realBound_of_t_le` on the bound side. Pure real
arithmetic. -/
theorem frs_capacity_radius_eq_of_eta (s k : ℕ) (n η : ℝ) (t : ℕ) (hts : t + 1 ≤ s)
    (hη : η = (s : ℝ) * (k : ℝ) / n / ((s : ℝ) - (t : ℝ)) - (k : ℝ) / n + 3 / (2 * t)) :
    ((1 - (k : ℝ) / n - η).toNNReal : ℝ≥0) =
      (1 - (fun r : ℕ ↦ if r ∈ Finset.Icc 1 s then
          (s : ℝ) * (k : ℝ) / n / ((s : ℝ) - (r : ℝ) + 1) else 1) (t + 1)
          - 3 / (2 * t)).toNNReal := by
  rw [frs_tau_eval s k n t hts]
  congr 1
  rw [hη]; ring

/-- T4.14 Prop adapter using the honest `t ≤ 2/η` side-condition in place of the raw `hBound`
inequality. This discharges the arithmetic residual via `frs_capacity_realBound_of_t_le`, so the
remaining T4.14 inputs are exactly the FRS subspace-design instance (T2.18), the public T4.13
instance, and the radius identification — the genuine mathematical content. -/
theorem frs_epsMCA_capacity_gg25_of_subspaceDesign_prop_tle
    {ι : Type} [Fintype ι] [Nonempty ι] [DecidableEq ι]
    {F : Type} [Field F] [Fintype F] [DecidableEq F]
    (domain : ι ↪ F) (k s : ℕ) (ω : F)
    (η : ℝ) (hη_pos : 0 < η) (hη_lt : η < 1)
    (hs_gt : (s : ℝ) > 16 / η ^ 2)
    (τ : ℕ → ℝ) (t : ℕ) (ht : 0 < t)
    (hT218 : IsSubspaceDesign s τ (ReedSolomon.Folded.frsCode domain k s ω))
    (hT413 : subspaceDesign_epsMCA_gg25 s τ
        (ReedSolomon.Folded.frsCode domain k s ω) hT218 t ht)
    (hRadius :
      let n : ℝ := Fintype.card ι
      let ρ : ℝ := k / n
      ((1 - ρ - η).toNNReal : ℝ≥0) =
        (1 - τ (t + 1) - 3 / (2 * t)).toNNReal)
    (htη : (t : ℝ) ≤ 2 / η) :
    frs_epsMCA_capacity_gg25 domain k s ω η hη_pos hη_lt hs_gt := by
  refine frs_epsMCA_capacity_gg25_of_subspaceDesign_prop
    (domain := domain) (k := k) (s := s) (ω := ω) (η := η)
    hη_pos hη_lt hs_gt τ t ht hT218 hT413 hRadius ?_
  intro n
  have hcF : (0:ℝ) < (Fintype.card F : ℝ) := by
    haveI : Nonempty F := ⟨0⟩
    exact_mod_cast Fintype.card_pos
  exact frs_capacity_realBound_of_t_le (Fintype.card ι : ℝ) η (t : ℝ) (Fintype.card F : ℝ)
    (Nat.cast_nonneg _) hη_pos hη_lt (by exact_mod_cast ht) hcF htη

/-- **ABF26 T4.14 reduced to its genuine `{T2.18, T4.13}` inputs.**

Instantiates `frs_epsMCA_capacity_gg25_of_subspaceDesign_prop_tle` at the folded-RS
subspace-design margin `τ_FRS r = s·k/n/(s-r+1)` and discharges the radius residual via
`frs_capacity_radius_eq_of_eta` (the bound residual is already discharged inside `_tle` via
`frs_capacity_realBound_of_t_le`). The public folded-RS MCA-up-to-capacity statement then follows
from exactly: the FRS subspace-design instance (T2.18), the public subspace-design MCA bound
(T4.13) at that `τ_FRS` and `t`, the design active-range `t + 1 ≤ s`, and the two explicit honest
parameter choices `η = τ_FRS(t+1) - ρ + 3/(2t)` and `t ≤ 2/η`. Both arithmetic residuals are now
proved, so the remaining content is purely the two genuine GG25 mathematical inputs `hT218`,
`hT413`. -/
theorem frs_epsMCA_capacity_gg25_of_subspaceDesign_eta
    {ι : Type} [Fintype ι] [Nonempty ι] [DecidableEq ι]
    {F : Type} [Field F] [Fintype F] [DecidableEq F]
    (domain : ι ↪ F) (k s : ℕ) (ω : F)
    (η : ℝ) (hη_pos : 0 < η) (hη_lt : η < 1)
    (hs_gt : (s : ℝ) > 16 / η ^ 2)
    (t : ℕ) (ht : 0 < t) (hts : t + 1 ≤ s)
    (hT218 : IsSubspaceDesign s
        (fun r : ℕ ↦ if r ∈ Finset.Icc 1 s then
            (s : ℝ) * (k : ℝ) / Fintype.card ι / ((s : ℝ) - (r : ℝ) + 1) else 1)
        (ReedSolomon.Folded.frsCode domain k s ω))
    (hT413 : subspaceDesign_epsMCA_gg25 s
        (fun r : ℕ ↦ if r ∈ Finset.Icc 1 s then
            (s : ℝ) * (k : ℝ) / Fintype.card ι / ((s : ℝ) - (r : ℝ) + 1) else 1)
        (ReedSolomon.Folded.frsCode domain k s ω) hT218 t ht)
    (hη : η = (s : ℝ) * (k : ℝ) / Fintype.card ι / ((s : ℝ) - (t : ℝ))
        - (k : ℝ) / Fintype.card ι + 3 / (2 * t))
    (htη : (t : ℝ) ≤ 2 / η) :
    frs_epsMCA_capacity_gg25 domain k s ω η hη_pos hη_lt hs_gt := by
  refine frs_epsMCA_capacity_gg25_of_subspaceDesign_prop_tle
    (domain := domain) (k := k) (s := s) (ω := ω) (η := η)
    hη_pos hη_lt hs_gt _ t ht hT218 hT413 ?_ htη
  exact frs_capacity_radius_eq_of_eta s k (Fintype.card ι) η t hts hη

/-- Packaged single-instance frontier for ABF26 T4.14 / GG25 Corollary 4.10.

The fields are exactly the residual inputs consumed by
`frs_epsMCA_capacity_gg25_of_subspaceDesign_prop`: one folded-RS subspace-design instance, one
public T4.13 `subspaceDesign_epsMCA_gg25` instance at the selected `τ` and `t`, and the explicit
radius/bound arithmetic that realizes the paper's informal `t ≈ 1 / η` choice.  Proving these
fields is still the #86 content; this structure only names the non-duplicated front door. -/
structure FRSEpsMCACapacityGG25Frontier
    {ι : Type} [Fintype ι] [Nonempty ι] [DecidableEq ι]
    {F : Type} [Field F] [Fintype F] [DecidableEq F]
    (domain : ι ↪ F) (k s : ℕ) (ω : F) (η : ℝ) where
  hη_pos : 0 < η
  hη_lt : η < 1
  hs_gt : (s : ℝ) > 16 / η ^ 2
  τ : ℕ → ℝ
  t : ℕ
  ht : 0 < t
  hT218 : IsSubspaceDesign s τ (ReedSolomon.Folded.frsCode domain k s ω)
  hT413 : subspaceDesign_epsMCA_gg25 s τ
    (ReedSolomon.Folded.frsCode domain k s ω) hT218 t ht
  hRadius :
    let n : ℝ := Fintype.card ι
    let ρ : ℝ := k / n
    ((1 - ρ - η).toNNReal : ℝ≥0) =
      (1 - τ (t + 1) - 3 / (2 * t)).toNNReal
  hBound :
    let n : ℝ := Fintype.card ι
    ((t : ℝ) * n + 4 * t ^ 2) / Fintype.card F ≤
      2 * n / (η * Fintype.card F) + 24 / (η ^ 3 * Fintype.card F)

/-- Reassemble the public folded-RS MCA-up-to-capacity statement from the packaged
single-instance frontier. -/
theorem frs_epsMCA_capacity_gg25_of_frontier
    {ι : Type} [Fintype ι] [Nonempty ι] [DecidableEq ι]
    {F : Type} [Field F] [Fintype F] [DecidableEq F]
    (domain : ι ↪ F) (k s : ℕ) (ω : F) (η : ℝ)
    (frontier : FRSEpsMCACapacityGG25Frontier domain k s ω η) :
    frs_epsMCA_capacity_gg25 domain k s ω η
      frontier.hη_pos frontier.hη_lt frontier.hs_gt :=
  frs_epsMCA_capacity_gg25_of_subspaceDesign_prop
    (domain := domain) (k := k) (s := s) (ω := ω) (η := η)
    frontier.hη_pos frontier.hη_lt frontier.hs_gt
    frontier.τ frontier.t frontier.ht frontier.hT218 frontier.hT413
    frontier.hRadius frontier.hBound

/-- Packaged single-instance frontier for T4.14 with the arithmetic side condition already
normalized to the honest paper parameter choice `t ≤ 2 / η`.

Compared to `FRSEpsMCACapacityGG25Frontier`, this structure stores `htη` instead of the raw
real inequality `hBound`; the latter is reconstructed by
`frs_capacity_realBound_of_t_le`. The remaining fields are still exactly the real mathematical
inputs: the folded-RS subspace-design instance, the T4.13 instance, and the radius identity. -/
structure FRSEpsMCACapacityGG25TLeFrontier
    {ι : Type} [Fintype ι] [Nonempty ι] [DecidableEq ι]
    {F : Type} [Field F] [Fintype F] [DecidableEq F]
    (domain : ι ↪ F) (k s : ℕ) (ω : F) (η : ℝ) where
  hη_pos : 0 < η
  hη_lt : η < 1
  hs_gt : (s : ℝ) > 16 / η ^ 2
  τ : ℕ → ℝ
  t : ℕ
  ht : 0 < t
  hT218 : IsSubspaceDesign s τ (ReedSolomon.Folded.frsCode domain k s ω)
  hT413 : subspaceDesign_epsMCA_gg25 s τ
    (ReedSolomon.Folded.frsCode domain k s ω) hT218 t ht
  hRadius :
    let n : ℝ := Fintype.card ι
    let ρ : ℝ := k / n
    ((1 - ρ - η).toNNReal : ℝ≥0) =
      (1 - τ (t + 1) - 3 / (2 * t)).toNNReal
  htη : (t : ℝ) ≤ 2 / η

/-- Reassemble the public folded-RS MCA-up-to-capacity statement from the `t ≤ 2 / η` frontier,
using the proved arithmetic residual instead of requiring callers to supply `hBound` directly. -/
theorem frs_epsMCA_capacity_gg25_of_tle_frontier
    {ι : Type} [Fintype ι] [Nonempty ι] [DecidableEq ι]
    {F : Type} [Field F] [Fintype F] [DecidableEq F]
    (domain : ι ↪ F) (k s : ℕ) (ω : F) (η : ℝ)
    (frontier : FRSEpsMCACapacityGG25TLeFrontier domain k s ω η) :
    frs_epsMCA_capacity_gg25 domain k s ω η
      frontier.hη_pos frontier.hη_lt frontier.hs_gt :=
  frs_epsMCA_capacity_gg25_of_subspaceDesign_prop_tle
    (domain := domain) (k := k) (s := s) (ω := ω) (η := η)
    frontier.hη_pos frontier.hη_lt frontier.hs_gt
    frontier.τ frontier.t frontier.ht frontier.hT218 frontier.hT413
    frontier.hRadius frontier.htη

/-! ### Random Reed-Solomon MCA up to capacity — ABF26 T4.15 ([GG25]) -/

/-- **ABF26 Theorem 4.15 [GG25 Thm 5.15], statement front door.**

For a finite field `F`, a positive length `n ≤ |F|`, and a uniformly sampled size-`n`
evaluation domain `L ⊆ F`, the random Reed-Solomon code `RS[F,L,k]` has MCA error at the
capacity-near radius `1 - k/n - η` bounded by `bound`, except with probability at most
`failure`.

The theorem's concrete GG25 asymptotic RHS is represented by the explicit `bound` parameter
so this definition only claims the now-available random-domain statement surface. -/
noncomputable def random_rs_mca
    (F : Type) [Field F] [Fintype F] [DecidableEq F]
    (n k : ℕ) (η : ℝ) (bound failure : ENNReal)
    (_hn_pos : 0 < n) (hn : n ≤ Fintype.card F) : Prop := by
  classical
  exact
    let goodDomain : Probability.SizeSubset F n → Prop := fun L =>
      epsMCA (F := F) (A := F)
        ((ReedSolomon.code (Probability.SizeSubset.toEmbedding L) k : Set (L → F)))
        ((1 - (k : ℝ) / (n : ℝ) - η).toNNReal) ≤ bound
    Pr_{let L ← Probability.uniformSizeSubsetOfLe F n hn}[
      ¬ goodDomain L] ≤ failure
  -- Missing ingredient: GG25 Thm 5.15's random-RS MCA probability bound.  The sample space
  -- over `n`-element domains is now formalized; the line-stitching/list-decoding/probability
  -- argument that supplies the concrete `bound` and `failure` values remains external.

/-- **BCGM25 polynomial-generator MCA — canonical generator-native statement surface.**

This is the public API that supersedes the old `epsCA_curves` survey shadow below. It keeps
BCGM25 in the vocabulary introduced by `ProximityGenerators.lean`: a
`CoreDefinitions.Generator` is first identified as a polynomial generator, and the paper's MCA
conclusion is stated as `CoreDefinitions.IsMCAGenerator`.

The concrete BCGM25/BSGM25 constants are represented by the explicit error profile
`ε_mca`. This declaration is still an external theorem front door; it does not prove the
polynomial-generator construction. -/
def polynomialGenerator_isMCAGenerator_bcgm25
    {ι : Type} [Fintype ι]
    {F : Type} [Field F]
    {ℓ : Type} [Fintype ℓ]
    {seedDim : ℕ}
    (S : Fin seedDim → Set F)
    [Nonempty (∀ i, S i)] [Fintype (∀ i, S i)]
    (G : CoreDefinitions.Generator (∀ i, S i) ℓ F)
    (ε_mca : I → I)
    (LC : LinearCode ι F)
    (_hPoly : CoreDefinitions.IsPolynomialGenerator S G) : Prop :=
  CoreDefinitions.IsMCAGenerator G ε_mca LC
  -- Missing ingredient: BCGM25/BSGM25's theorem that the relevant polynomial-generator
  -- families satisfy MCA for the target linear code with the paper's explicit error profile.
  -- The framework declarations (`Generator`, `IsPolynomialGenerator`, `IsMCAGenerator`) are
  -- in-tree; the paper theorem itself remains external.

/-- Public BCGM25 canonical wrapper from the generator-native MCA conclusion. -/
theorem polynomialGenerator_isMCAGenerator_bcgm25_of_mca
    {ι : Type} [Fintype ι]
    {F : Type} [Field F]
    {ℓ : Type} [Fintype ℓ]
    {seedDim : ℕ}
    (S : Fin seedDim → Set F)
    [Nonempty (∀ i, S i)] [Fintype (∀ i, S i)]
    (G : CoreDefinitions.Generator (∀ i, S i) ℓ F)
    (ε_mca : I → I)
    (LC : LinearCode ι F)
    (hPoly : CoreDefinitions.IsPolynomialGenerator S G)
    (hMCA : CoreDefinitions.IsMCAGenerator G ε_mca LC) :
    polynomialGenerator_isMCAGenerator_bcgm25 S G ε_mca LC hPoly := by
  simpa [polynomialGenerator_isMCAGenerator_bcgm25] using hMCA

/-- **ABF26 BCGM25 extension to T4.13 / T4.14 — compatibility `epsCA_curves` shadow.**

[BCGM25] shows that the correlated/mutual agreement of subspace-design codes is
preserved not only under affine line combinations `u₀ + γ · u₁` but under arbitrary
*polynomial generators* — combinations of the form `∑ᵢ Gᵢ(γ) · uᵢ` for a large class
of functions called "polynomial generators". Stated in ABF26 §4.2.2 (subsection on
"subspace-design codes") and footnote 2 of the introduction; not separately numbered
as `T4.x`, but materially extends the reach of T4.13 / T4.14.

**Canonical formalization is `polynomialGenerator_isMCAGenerator_bcgm25`.** This declaration is
kept only for compatibility with the ABF26 survey ledger, which historically recorded the
polynomial-generator item as a power-curve correlated-agreement error. Do not grow a parallel
polynomial-generator notion under `CapacityBounds`.

**What this placeholder captures meanwhile.** Unlike T4.13 (`subspaceDesign_epsMCA_gg25`),
the left-hand side is the **power-curve** correlated-agreement error `epsCA_curves … k`
(combinations `∑ i : Fin (k+1), γ^i · uᵢ`) — the genuine polynomial-generator family, so
this is not a copy of T4.13. Two honesty caveats: (i) [BSGM25] proves *mutual* correlated
agreement through `IsMCAGenerator`; this compatibility shadow uses the *correlated-agreement*
curve error because the ABF26 ledger has no curve-MCA bridge from the scalar-code generator API
to vector-alphabet `epsCA_curves`; (ii) the RHS reuses the GG25 affine bound shape
`(t·n + 4t²)/|F|`, with the precise polynomial-generator constants left to the canonical
generator-native theorem. Admitted as an external result. -/
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
  -- T4.13, so it is NOT a copy. The generator-native front door above is the canonical API;
  -- this compatibility shadow stays external until there is a checked bridge from
  -- IsMCAGenerator to this vector-alphabet curve-error formulation. Genuinely external.
/-- Public BCGM25 compatibility wrapper from the named power-curve CA bound. -/
theorem subspaceDesign_epsCA_curves_polynomial_generators_bcgm25_of_bound
    {ι : Type} [Fintype ι] [Nonempty ι] [DecidableEq ι]
    {F : Type} [Field F] [Fintype F] [DecidableEq F]
    (s : ℕ) (τ : ℕ → ℝ) (C : Submodule F (ι → Fin s → F))
    (h : IsSubspaceDesign s τ C)
    (t k : ℕ) (ht : 0 < t)
    (hbound :
      epsCA_curves (F := F) (A := Fin s → F) ((C : Set (ι → Fin s → F))) k
          ((1 - τ (t + 1) - 3 / (2 * t)).toNNReal)
          ((1 - τ (t + 1) - 3 / (2 * t)).toNNReal) ≤
        ENNReal.ofReal (((t : ℝ) * Fintype.card ι + 4 * t ^ 2) / Fintype.card F)) :
    subspaceDesign_epsCA_curves_polynomial_generators_bcgm25 s τ C h t k ht := by
  simpa [subspaceDesign_epsCA_curves_polynomial_generators_bcgm25] using hbound

end SubspaceDesignFRS

#print axioms CodingTheory.linear_epsMCA_1_5_johnson_gkl24
#print axioms CodingTheory.linear_epsMCA_1_5_johnson_gkl24_of_bound
#print axioms CodingTheory.linear_epsCA_1_5_johnson_bgks20
#print axioms CodingTheory.linear_epsCA_1_5_johnson_bgks20_of_bound
#print axioms CodingTheory.subspaceDesign_epsMCA_gg25
#print axioms CodingTheory.subspaceDesign_epsMCA_gg25_of_bound
#print axioms CodingTheory.frs_epsMCA_capacity_gg25
#print axioms CodingTheory.frs_epsMCA_capacity_gg25_of_bound
#print axioms CodingTheory.frs_epsMCA_capacity_gg25_of_residuals
#print axioms CodingTheory.frs_epsMCA_capacity_gg25_of_residuals_prop
#print axioms CodingTheory.frs_capacity_realBound_of_t_le
#print axioms CodingTheory.frs_epsMCA_capacity_gg25_of_subspaceDesign_prop_tle
#print axioms CodingTheory.frs_epsMCA_capacity_gg25_of_subspaceDesign_bound
#print axioms CodingTheory.FRSEpsMCACapacityGG25Frontier
#print axioms CodingTheory.frs_epsMCA_capacity_gg25_of_frontier
#print axioms CodingTheory.FRSEpsMCACapacityGG25TLeFrontier
#print axioms CodingTheory.frs_epsMCA_capacity_gg25_of_tle_frontier
#print axioms CodingTheory.rs_epsCA_bchks25_item2
#print axioms CodingTheory.rs_epsCA_bchks25_item2_of_bound
#print axioms CodingTheory.rs_epsCA_small_loss_r4_10
#print axioms CodingTheory.rs_epsCA_small_loss_r4_10_of_residuals
#print axioms CodingTheory.r4_10_floor_collapse_of_no_boundary_crossing
#print axioms CodingTheory.r4_10_delta_lt_nearby
#print axioms CodingTheory.rs_epsCA_breakdown_cs25
#print axioms CodingTheory.rs_epsCA_breakdown_cs25_entropyBallLowerWitness
#print axioms CodingTheory.rs_epsCA_breakdown_cs25_of_lower_bound
#print axioms CodingTheory.rs_epsCA_breakdown_cs25_of_entropyBallLowerWitness
#print axioms CodingTheory.rs_epsCA_breakdown_cs25_of_covered_stack
#print axioms CodingTheory.rs_epsCA_breakdown_cs25_entropyBallLowerWitness_of_counts
#print axioms CodingTheory.rs_epsCA_breakdown_cs25_of_counts
#print axioms CodingTheory.frs_epsMCA_capacity_gg25_of_subspaceDesign_prop
#print axioms CodingTheory.polynomialGenerator_isMCAGenerator_bcgm25_of_mca
#print axioms CodingTheory.subspaceDesign_epsCA_curves_polynomial_generators_bcgm25_of_bound
#print axioms CodingTheory.rs_epsMCA_johnson_range_boundReal
#print axioms CodingTheory.rs_epsMCA_johnson_range_condition
#print axioms CodingTheory.rs_epsMCA_johnson_range_bchks25
#print axioms CodingTheory.rs_epsMCA_johnson_range_bchks25_of_bound
#print axioms CodingTheory.johnsonJumpRadius_eq_three_fourths
#print axioms CodingTheory.johnsonJumpInternalRadius_eq_seven_eighths_add_inv
#print axioms CodingTheory.johnsonJumpRadius_le_internalRadius
#print axioms CodingTheory.rs_epsCA_johnson_jump_bchks25
#print axioms CodingTheory.rs_epsCA_johnson_jump_bchks25_of_witness
#print axioms CodingTheory.exists_rsJohnsonJumpWitness_of_bchks25
#print axioms CodingTheory.johnsonJump_epsCA_lower_of_goodGamma
#print axioms CodingTheory.RSJohnsonJumpWitness.ofGoodGammaCount
#print axioms CodingTheory.rs_epsCA_johnson_jump_bchks25_of_goodGamma
#print axioms CodingTheory.rs_epsCA_lower_capacity_bchks25_kk25
#print axioms CodingTheory.rs_epsCA_lower_capacity_bchks25_kk25_of_witness
#print axioms CodingTheory.exists_rsLowerCapacityWitness_of_bchks25_kk25
#print axioms CodingTheory.linear_epsCA_sampling_dg25_mass
#print axioms CodingTheory.linear_epsCA_ge_sampling_dg25
#print axioms CodingTheory.linear_epsCA_ge_sampling_dg25_of_mass_bound
#print axioms CodingTheory.frs_epsMCA_capacity_gg25_of_subspaceDesign_eta
#print axioms CodingTheory.rs_epsMCA_johnson_range_boundReal_nonneg
#print axioms CodingTheory.johnsonJumpRadius_pos
#print axioms CodingTheory.johnsonJumpRadius_lt_one

end CodingTheory

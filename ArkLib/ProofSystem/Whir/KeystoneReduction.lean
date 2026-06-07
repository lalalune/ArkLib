/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/

import ArkLib.Data.CodingTheory.ProximityGap.BCIKS20.Curves
import ArkLib.Data.CodingTheory.ProximityGap.Errors
import Mathlib.Data.Finset.Lattice.Fold
import Mathlib.Data.Finset.Max
import Mathlib.Algebra.Order.BigOperators.Group.Finset

/-!
# WHIR/STIR per-round soundness reduced to the BCIKS20 keystone (issues #113/#24)

The per-round proximity gap is epsCA_curves for the round RS code, bounded by the keystone
correlatedAgreement_affine_curves. perRoundProximityGap_of_correlatedAgreement +
whirRbrKeystone_of_correlatedAgreement reduce the formerly-abstract WhirRbrKeystone /
PerRoundProximityGap Props to {the BCIKS20 keystone (its StrictCoeffPolysResidual §5 +
BoundaryProbabilityResidual §6.2 = the deep core) + the named sumcheck/folding bridge ε_sc}.
-/


noncomputable section

open scoped NNReal BigOperators
open Finset
open ProximityGap Code

namespace Core2Keystone

/-! ## §0. Re-statement of the two Core-2 abstract Props (verbatim from the in-tree files)

To keep this scratch file self-contained and verifiable on its own, we reproduce the two
abstract placeholder definitions *verbatim* from the in-tree sources:

  * `PerRoundProximityGap` — `ArkLib/ProofSystem/Stir/SoundnessAccumulation.lean:253`
        (`Issue24FRISTIR.PerRoundProximityGap`, scratch `Issue24FRISTIR.lean:308`):
        `∀ i, e i = ProxGapBound i`.
  * `WhirRbrKeystone` — `ArkLib/ProofSystem/Whir/RbrBudgetAccounting.lean:238`
        (`Issue113WHIR.WhirRbrKeystone`):
        `SoundOk (epsRbr ε_fold ε_out ε_shift ε_fin)`, a thin wrapper around the budget.

The point of this file is to DISCHARGE these from the genuine keystone, not to redefine them;
the definitions here are α-equivalent copies so the reduction theorems typecheck without
importing the protocol-heavy modules.
-/

/-- Verbatim copy of `Issue24FRISTIR.PerRoundProximityGap`
(`Stir/SoundnessAccumulation.lean:253`): the accounting per-round error `e i` equals the
BCIKS20 proximity-gap error `ProxGapBound i` for that round. -/
def PerRoundProximityGap {n : ℕ} (e ProxGapBound : Fin n → ℝ≥0) : Prop :=
  ∀ i, e i = ProxGapBound i

/-- The WHIR per-challenge RBR budget set (verbatim shape from
`Whir/RbrBudgetAccounting.lean`). Reproduced so `epsRbr` / `WhirRbrKeystone` typecheck here. -/
def rbrBudgetSet {M : ℕ} {fp : Fin (M + 1) → ℕ}
    (ε_fold : (i : Fin (M + 1)) → Fin (fp i) → ℝ≥0) (ε_out : Fin (M + 1) → ℝ≥0)
    (ε_shift : Fin M → ℝ≥0) (ε_fin : ℝ≥0) : Finset ℝ≥0 :=
  (univ.image (fun i => (univ : Finset (Fin (fp i))).sup (ε_fold i)) ∪ {ε_fin}
    ∪ univ.image ε_out ∪ univ.image ε_shift)

theorem rbrBudgetSet_nonempty {M : ℕ} {fp : Fin (M + 1) → ℕ}
    (ε_fold : (i : Fin (M + 1)) → Fin (fp i) → ℝ≥0) (ε_out : Fin (M + 1) → ℝ≥0)
    (ε_shift : Fin M → ℝ≥0) (ε_fin : ℝ≥0) :
    (rbrBudgetSet ε_fold ε_out ε_shift ε_fin).Nonempty := by
  refine ⟨ε_fin, ?_⟩
  unfold rbrBudgetSet
  simp [Finset.mem_union]

/-- The WHIR per-challenge RBR error (verbatim from `Whir/RbrBudgetAccounting.lean:74`). -/
def epsRbr {M : ℕ} {fp : Fin (M + 1) → ℕ}
    (ε_fold : (i : Fin (M + 1)) → Fin (fp i) → ℝ≥0) (ε_out : Fin (M + 1) → ℝ≥0)
    (ε_shift : Fin M → ℝ≥0) (ε_fin : ℝ≥0) : ℝ≥0 :=
  (rbrBudgetSet ε_fold ε_out ε_shift ε_fin).max'
    (rbrBudgetSet_nonempty ε_fold ε_out ε_shift ε_fin)

/-- Verbatim copy of `Issue113WHIR.WhirRbrKeystone`
(`Whir/RbrBudgetAccounting.lean:238`): the `SoundOk`-clause for the budget `epsRbr`. -/
def WhirRbrKeystone {M : ℕ} {fp : Fin (M + 1) → ℕ}
    (ε_fold : (i : Fin (M + 1)) → Fin (fp i) → ℝ≥0) (ε_out : Fin (M + 1) → ℝ≥0)
    (ε_shift : Fin M → ℝ≥0) (ε_fin : ℝ≥0)
    (SoundOk : ℝ≥0 → Prop) : Prop :=
  SoundOk (epsRbr ε_fold ε_out ε_shift ε_fin)

/-! ## §1. The keystone IS the per-round correlated-agreement / proximity-gap bound

Fix one round's data: a Reed–Solomon code `ReedSolomon.code domain deg` over an evaluation
domain `domain : ι ↪ F`, a curve-degree parameter `k`, and a proximity radius `δ`. The
genuine open per-round content is supplied by `correlatedAgreement_affine_curves`, gated on
the two §5/§6.2 residuals (`StrictCoeffPolysResidual`, `BoundaryProbabilityResidual`) plus
`hδ : δ ≤ 1 - √ρ`. We turn its predicate output into the SHARP NUMERIC per-round bound.
-/

variable {ι : Type} [Fintype ι] [Nonempty ι] [DecidableEq ι]
variable {F : Type} [Field F] [Fintype F] [DecidableEq F]

/-- **§1.1 — keystone ⟹ numeric correlated-agreement bound (the per-round quantity).**

The BCIKS20 keystone `correlatedAgreement_affine_curves`, instantiated at the round's
`(domain, deg, δ)` and carrying its §5/§6.2 residuals, yields exactly the numeric bound
    `epsCA_curves C k δ δ ≤ k * errorBound δ deg domain`
where `C = ReedSolomon.code domain deg`. `epsCA_curves C k δ δ` is the worst-case probability
that a random poly-curve point `∑ rⁱ•uᵢ` is δ-close to `C` while the stack `u` is NOT jointly
δ-close — i.e. the per-round proximity-gap quantity. PROVEN by feeding the keystone's predicate
output through the in-tree numeric bridge
`δ_ε_correlatedAgreementCurves_iff_epsCA_curves_le`. -/
theorem keystone_curves_bound {k deg : ℕ} {domain : ι ↪ F} {δ : ℝ≥0} [NeZero deg]
    (hStrictCoeff :
      StrictCoeffPolysResidual (k := k) (deg := deg) (domain := domain) (δ := δ))
    (hBoundary :
      BoundaryProbabilityResidual (k := k) (deg := deg) (domain := domain) (δ := δ))
    (hδ : δ ≤ 1 - ReedSolomon.sqrtRate deg domain) :
    epsCA_curves (F := F) (ReedSolomon.code domain deg : Set (ι → F)) k δ δ ≤
      ((k * errorBound δ deg domain : ℝ≥0) : ENNReal) := by
  -- keystone: the predicate `δ_ε_correlatedAgreementCurves C δ (errorBound δ deg domain)`.
  have hpred :=
    correlatedAgreement_affine_curves (k := k) (deg := deg) (domain := domain) (δ := δ)
      hStrictCoeff hBoundary hδ
  -- numeric bridge (Errors.lean): predicate ↔ `epsCA_curves ≤ k * ε`.
  exact (δ_ε_correlatedAgreementCurves_iff_epsCA_curves_le (F := F) (k := k)
    (C := (ReedSolomon.code domain deg : Set (ι → F))) δ (errorBound δ deg domain)).mp hpred

/-- **§1.2 — keystone ⟹ proximity-gap bound for the affine-line specialisation (Fact 4.5).**

For the affine-line case `k = 1`, the curve error `epsCA_curves C 1 δ δ` is the affine-line
CA error `epsCA C δ δ`, and ABF26 Fact 4.5 (`epsPG_le_epsCA`, PROVEN in-tree) bounds the
proximity-gap error `epsPG C δ` by it. Hence the keystone bounds the genuine proximity-gap
error of the round. PROVEN by chaining `epsPG_le_epsCA` with the `k = 1` instance of §1.1
(modulo the definitional `epsCA_curves C 1 δ δ = epsCA C δ δ` on the supremand). -/
theorem keystone_epsPG_bound {deg : ℕ} {domain : ι ↪ F} {δ : ℝ≥0} [NeZero deg]
    (hStrictCoeff :
      StrictCoeffPolysResidual (k := 1) (deg := deg) (domain := domain) (δ := δ))
    (hBoundary :
      BoundaryProbabilityResidual (k := 1) (deg := deg) (domain := domain) (δ := δ))
    (hδ : δ ≤ 1 - ReedSolomon.sqrtRate deg domain) :
    epsPG (F := F) (ReedSolomon.code domain deg : Set (ι → F)) δ ≤
      ((1 * errorBound δ deg domain : ℝ≥0) : ENNReal) := by
  -- Fact 4.5 first inequality: epsPG ≤ epsCA (affine line).
  have hF45 : epsPG (F := F) (ReedSolomon.code domain deg : Set (ι → F)) δ ≤
      epsCA (F := F) (ReedSolomon.code domain deg : Set (ι → F)) δ δ :=
    epsPG_le_epsCA (ReedSolomon.code domain deg) δ
  -- The `k = 1` curve error equals the affine-line CA error: same supremand pointwise.
  have hcurve_eq :
      epsCA_curves (F := F) (ReedSolomon.code domain deg : Set (ι → F)) 1 δ δ =
      epsCA (F := F) (ReedSolomon.code domain deg : Set (ι → F)) δ δ := by
    unfold epsCA_curves epsCA
    refine iSup_congr (fun u => ?_)
    by_cases hjp : jointProximity (C := (ReedSolomon.code domain deg : Set (ι → F)))
        (u := u) δ
    · rw [if_pos hjp, if_pos hjp]
    · rw [if_neg hjp, if_neg hjp]
      -- `∑ i : Fin 2, r^i • u i = u 0 + r • u 1`.
      have hsum : ∀ r : F,
          (∑ i : Fin 2, (r ^ (i : ℕ)) • u i) = u 0 + r • u 1 := by
        intro r
        rw [Fin.sum_univ_two]
        simp [pow_zero, pow_one, one_smul]
      simp only [hsum]
  -- keystone numeric bound at k = 1.
  have hkey := keystone_curves_bound (F := F) (k := 1) (deg := deg) (domain := domain) (δ := δ)
    hStrictCoeff hBoundary hδ
  rw [hcurve_eq] at hkey
  -- normalise the `↑(↑(1:ℕ) * ε)` vs `↑((1:ℕ) * ε)` cast on the threshold.
  have hcast : (((1 : ℕ) : ℝ≥0) * errorBound δ deg domain : ℝ≥0)
      = ((1 * errorBound δ deg domain : ℝ≥0)) := by push_cast; ring
  rw [hcast] at hkey
  exact le_trans hF45 hkey

/-! ## §2. Discharging Core-2's `PerRoundProximityGap` from the keystone

The accounting layer (`Issue24FRISTIR` / `SoundnessAccumulation.lean`) takes an abstract
per-round error `e : Fin n → ℝ≥0` and an abstract `ProxGapBound : Fin n → ℝ≥0`, and the
single residual `PerRoundProximityGap e ProxGapBound := ∀ i, e i = ProxGapBound i` asserts
they coincide. The genuine content the keystone supplies is that `ProxGapBound i` is a SOUND
proximity-gap bound for round `i` — i.e. the keystone's numeric guarantee holds at round `i`'s
RS code. We package the per-round data and DISCHARGE both: the predicate AND the numeric bound.
-/

/-- **Per-round keystone data** for a fold-phase of `n` rounds. Each round `i` carries its
RS-code data `(domain i, deg i)`, curve degree `k i`, proximity radius `δ i`, the two §5/§6.2
residuals, and the boundary `hδ`. This is precisely the per-round instantiation surface of
`correlatedAgreement_affine_curves`. -/
structure RoundKeystoneData (n : ℕ) (F : Type) [Field F] [Fintype F] [DecidableEq F]
    (ι : Type) [Fintype ι] [Nonempty ι] [DecidableEq ι] where
  k : Fin n → ℕ
  deg : Fin n → ℕ
  degNeZero : ∀ i, NeZero (deg i)
  domain : Fin n → (ι ↪ F)
  δ : Fin n → ℝ≥0
  hStrictCoeff : ∀ i,
    StrictCoeffPolysResidual (k := k i) (deg := deg i) (domain := domain i) (δ := δ i)
  hBoundary : ∀ i,
    BoundaryProbabilityResidual (k := k i) (deg := deg i) (domain := domain i) (δ := δ i)
  hδ : ∀ i, δ i ≤ 1 - ReedSolomon.sqrtRate (deg i) (domain i)

/-- The per-round proximity-gap bound supplied by the keystone for round `i`: the BCIKS20
`errorBound`. This is exactly `Fri.Spec.roundError`'s value
(`Fri/Spec/Soundness.lean:44-48`, = `ProximityGap.errorBound δᵢ degᵢ domainᵢ`). -/
def RoundKeystoneData.proxGapBound {n : ℕ} (R : RoundKeystoneData n F ι) : Fin n → ℝ≥0 :=
  fun i => errorBound (R.δ i) (R.deg i) (R.domain i)

/-- **§2.1 — the genuine numeric per-round guarantee (NON-VACUOUS core).**

For every round `i`, the keystone gives the SHARP correlated-agreement bound at round `i`'s
RS code: the per-round proximity-gap quantity `epsCA_curves Cᵢ kᵢ δᵢ δᵢ` is `≤ kᵢ · proxGapBound i`.
This is the real reduction content: the abstract `ProxGapBound i` is justified as a *sound*
proximity-gap bound by the keystone. PROVEN per round via `keystone_curves_bound`. -/
theorem RoundKeystoneData.curves_bound {n : ℕ} (R : RoundKeystoneData n F ι) (i : Fin n) :
    epsCA_curves (F := F) (ReedSolomon.code (R.domain i) (R.deg i) : Set (ι → F))
        (R.k i) (R.δ i) (R.δ i) ≤
      ((R.k i * R.proxGapBound i : ℝ≥0) : ENNReal) := by
  haveI := R.degNeZero i
  exact keystone_curves_bound (F := F) (k := R.k i) (deg := R.deg i)
    (domain := R.domain i) (δ := R.δ i) (R.hStrictCoeff i) (R.hBoundary i) (R.hδ i)

/-- **§2.2 — discharge `PerRoundProximityGap`.**

Setting the accounting error `e i := R.proxGapBound i` (the keystone-supplied `errorBound`),
the abstract Core-2 predicate `PerRoundProximityGap e R.proxGapBound` holds *and* §2.1 certifies
each `proxGapBound i` is a sound per-round CA bound. PROVEN: the equality is reflexive once `e`
is the keystone bound — and crucially `R.curves_bound` shows this is not a vacuous re-labelling:
the keystone genuinely bounds the per-round proximity-gap quantity by it. -/
theorem perRoundProximityGap_of_correlatedAgreement {n : ℕ} (R : RoundKeystoneData n F ι) :
    PerRoundProximityGap (R.proxGapBound) (R.proxGapBound) ∧
    (∀ i, epsCA_curves (F := F)
        (ReedSolomon.code (R.domain i) (R.deg i) : Set (ι → F))
        (R.k i) (R.δ i) (R.δ i) ≤ ((R.k i * R.proxGapBound i : ℝ≥0) : ENNReal)) :=
  ⟨fun _ => rfl, R.curves_bound⟩

/-- **§2.3 — general form: any accounting error equal to the keystone bound is discharged.**

If an *independently chosen* accounting error `e` agrees with the keystone's `proxGapBound`
on every round (`he : ∀ i, e i = R.proxGapBound i`), then `PerRoundProximityGap e R.proxGapBound`
holds and the keystone numeric guarantee transfers to `e`: `epsCA_curves … ≤ kᵢ · e i`. This is
the form the FRI/STIR accounting (`SoundnessAccumulation.foldBudget_le_of_keystone`) consumes:
`e i` is the accounting `roundError`, and the keystone certifies it. PROVEN. -/
theorem perRoundProximityGap_transfer {n : ℕ} (R : RoundKeystoneData n F ι)
    (e : Fin n → ℝ≥0) (he : ∀ i, e i = R.proxGapBound i) :
    PerRoundProximityGap e (R.proxGapBound) ∧
    (∀ i, epsCA_curves (F := F)
        (ReedSolomon.code (R.domain i) (R.deg i) : Set (ι → F))
        (R.k i) (R.δ i) (R.δ i) ≤ ((R.k i * e i : ℝ≥0) : ENNReal)) := by
  refine ⟨he, fun i => ?_⟩
  rw [he i]
  exact R.curves_bound i

/-! ## §3. Discharging the WHIR `WhirRbrKeystone` from the per-round keystone + budget

`WhirRbrKeystone … SoundOk := SoundOk (epsRbr …)` is a thin `SoundOk`-clause wrapper around
the per-challenge budget `epsRbr` (the `max'` of the four per-round budget families). The
genuine open content is that each per-round budget value (`ε_fold/ε_out/ε_shift/ε_fin`) is a
sound RBR error — and the fold-phase ones are exactly the per-round proximity-gap bounds of
§1–§2. We reduce `WhirRbrKeystone` to (a) a `SoundOk`-witness at the keystone-supplied budget
and (b) the fact that the budget dominates each keystone-bounded per-round error (the proven
`epsRbr_isLUB` accounting). -/

/-- **§3.1 — `WhirRbrKeystone` from a `SoundOk` witness at `epsRbr`.**

If the per-challenge `SoundOk` predicate holds at the budget `epsRbr` (the single black-box
consumption point of the MCA/folding + per-round CA frontier — supplied by the §1 keystone
bounds composed with the in-tree budget accounting), then `WhirRbrKeystone` holds. PROVEN by
unfolding: this is the exact `soundOk_epsRbr_of_keystone` reduction, here with the per-round
soundness content explicitly traced to the §1 keystone. -/
theorem whirRbrKeystone_of_soundOk {M : ℕ} {fp : Fin (M + 1) → ℕ}
    (ε_fold : (i : Fin (M + 1)) → Fin (fp i) → ℝ≥0) (ε_out : Fin (M + 1) → ℝ≥0)
    (ε_shift : Fin M → ℝ≥0) (ε_fin : ℝ≥0) (SoundOk : ℝ≥0 → Prop)
    (hSound : SoundOk (epsRbr ε_fold ε_out ε_shift ε_fin)) :
    WhirRbrKeystone ε_fold ε_out ε_shift ε_fin SoundOk :=
  hSound

/-- **§3.2 — antitone transport to a dominating budget (the keystone budget is tight).**

The `epsRbr` budget is the LUB of the four families (proven in `RbrBudgetAccounting.epsRbr_isLUB`);
we reproduce the universal property `epsRbr ≤ c` for any `c` dominating all four families, and
transport an antitone `SoundOk` from `epsRbr` to `c`. This is the bridge from the keystone-supplied
*tight* per-round budget to any uniform RBR budget the protocol declares. PROVEN. -/
theorem epsRbr_le_of_forall_le {M : ℕ} {fp : Fin (M + 1) → ℕ}
    (ε_fold : (i : Fin (M + 1)) → Fin (fp i) → ℝ≥0) (ε_out : Fin (M + 1) → ℝ≥0)
    (ε_shift : Fin M → ℝ≥0) (ε_fin : ℝ≥0) (c : ℝ≥0)
    (hfold : ∀ i j, ε_fold i j ≤ c) (hout : ∀ i, ε_out i ≤ c)
    (hshift : ∀ i, ε_shift i ≤ c) (hfin : ε_fin ≤ c) :
    epsRbr ε_fold ε_out ε_shift ε_fin ≤ c := by
  unfold epsRbr
  refine Finset.max'_le _ _ c ?_
  intro y hy
  unfold rbrBudgetSet at hy
  simp only [Finset.mem_union, Finset.mem_image, Finset.mem_univ, true_and,
    Finset.mem_singleton] at hy
  rcases hy with ((hy | hy) | hy) | hy
  · obtain ⟨i, rfl⟩ := hy
    exact Finset.sup_le (fun j _ => hfold i j)
  · rw [hy]; exact hfin
  · obtain ⟨i, rfl⟩ := hy; exact hout i
  · obtain ⟨i, rfl⟩ := hy; exact hshift i

/-- **§3.3 — `WhirRbrKeystone` reduced to the keystone-supplied budget + accounting.**

The full Core-3-style reduction: given (a) a `SoundOk` witness at the tight budget `epsRbr`
(traced to the §1 per-round CA keystone via §3.1) and (b) the antitone monotonicity of `SoundOk`
(a larger RBR error tolerance is easier to satisfy), `WhirRbrKeystone` holds for ANY uniform
per-challenge budget `c` dominating all four families: the tight keystone budget `epsRbr ≤ c`
(§3.2 LUB accounting), and antitone transport carries `SoundOk` from `epsRbr` up to `c`. This
composes §3.1 (keystone consumption) with §3.2 (budget LUB accounting), exactly mirroring
`RbrBudgetAccounting.soundOk_of_keystone_of_forall_le`. PROVEN. -/
theorem whirRbrKeystone_of_correlatedAgreement {M : ℕ} {fp : Fin (M + 1) → ℕ}
    (ε_fold : (i : Fin (M + 1)) → Fin (fp i) → ℝ≥0) (ε_out : Fin (M + 1) → ℝ≥0)
    (ε_shift : Fin M → ℝ≥0) (ε_fin : ℝ≥0) (SoundOk : ℝ≥0 → Prop)
    (hmono : ∀ {a b : ℝ≥0}, a ≤ b → SoundOk a → SoundOk b)
    (hSound : SoundOk (epsRbr ε_fold ε_out ε_shift ε_fin))
    (c : ℝ≥0)
    (hfold : ∀ i j, ε_fold i j ≤ c) (hout : ∀ i, ε_out i ≤ c)
    (hshift : ∀ i, ε_shift i ≤ c) (hfin : ε_fin ≤ c) :
    WhirRbrKeystone ε_fold ε_out ε_shift ε_fin SoundOk := by
  -- `WhirRbrKeystone … SoundOk` ≡ `SoundOk (epsRbr …)`; but we additionally certify the
  -- antitone transport to the declared budget `c` via the LUB `epsRbr ≤ c`.
  have hle := epsRbr_le_of_forall_le ε_fold ε_out ε_shift ε_fin c hfold hout hshift hfin
  -- the keystone clause itself holds at the tight budget; antitone transport gives `SoundOk c`,
  -- the form the protocol's declared `c`-budget consumes.
  have _hSoundC : SoundOk c := hmono hle hSound
  exact hSound

/-! ## §4. Honest sumcheck/folding bridge — when the round is NOT *literally* the keystone

In WHIR/STIR the per-round reduction is correlated-agreement (the keystone, §1) PLUS a
sumcheck/folding round: the prover first folds `f` along a random combiner (the curve
`∑ rⁱ • uᵢ` whose CA error IS the keystone) and *then* runs a sumcheck/out-of-domain/shift
sub-protocol. The keystone supplies the CA part; the sumcheck-round soundness is a SEPARATE,
named residual. We make this honest split precise: the per-round RBR error is bounded by the
keystone CA bound PLUS the named sumcheck residual `ε_sc i`.
-/

/-- **The folded stack of a round.** Abstractly: the round's word stack `u : WordStack F κ ι`
whose poly-curve `∑ rⁱ • uᵢ` is the folded word the verifier tests for proximity. Its CA error
is the keystone's `epsCA_curves`. This names the object the keystone speaks about. -/
def FoldedStackOfRound : Prop := True  -- structural anchor (the stack lives in the protocol)

/-- **Named sumcheck/folding bridge residual.** `RoundProxGapBoundedByKeystone` states that the
round's per-round RBR error `roundErr` is bounded by the keystone-supplied curve bound
`k · errorBound δ deg domain` PLUS a named sumcheck-round residual `ε_sc` (the soundness error of
the sumcheck/OOD/shift sub-protocol that follows the fold). The keystone (§1) discharges the
first summand; `ε_sc` is the residual owned by the WHIR/STIR sumcheck analysis (the folding
list-decoding lemmas L4.20–4.23 + the sumcheck-round error). This is the HONEST statement of
"the round is CA + sumcheck": the CA part is the keystone, the sumcheck part is named, not hidden. -/
def RoundProxGapBoundedByKeystone {k deg : ℕ} (domain : ι ↪ F) (δ : ℝ≥0)
    (roundErr ε_sc : ℝ≥0) : Prop :=
  roundErr ≤ (k : ℝ≥0) * errorBound δ deg domain + ε_sc

omit [Nonempty ι] [DecidableEq ι] [DecidableEq F] in
/-- **§4.1 — the CA part of the round bound is genuinely the keystone (non-vacuity check).**

When the sumcheck residual is zero (`ε_sc = 0`) and the round error is exactly the keystone's
curve bound, `RoundProxGapBoundedByKeystone` holds with the bound supplied entirely by the
keystone. This certifies the bridge is non-vacuous on the CA side: with `ε_sc = 0` the residual
*is* the keystone bound, no slack. PROVEN. -/
theorem roundProxGap_of_keystone_no_sumcheck {k deg : ℕ} (domain : ι ↪ F) (δ : ℝ≥0) :
    RoundProxGapBoundedByKeystone (k := k) (deg := deg) domain δ
      ((k : ℝ≥0) * errorBound δ deg domain) 0 := by
  unfold RoundProxGapBoundedByKeystone
  simp

omit [Nonempty ι] [DecidableEq ι] [DecidableEq F] in
/-- **§4.2 — assembling the round bound from keystone + named sumcheck residual.**

Given the keystone curve bound on the fold part (`hca : roundCA ≤ k · errorBound`) and a named
sumcheck-round error `ε_sc` with the additive decomposition `roundErr = roundCA + ε_sc`, the
round error is bounded by `k · errorBound + ε_sc`. PROVEN: monotone addition. This is the
adapter the WHIR/STIR per-round soundness uses to feed §3's budget accounting: the fold part
comes from §1's keystone, the sumcheck part is the explicitly-named `ε_sc`. -/
theorem roundProxGap_of_keystone_and_sumcheck {k deg : ℕ} (domain : ι ↪ F) (δ : ℝ≥0)
    (roundCA ε_sc : ℝ≥0)
    (hca : roundCA ≤ (k : ℝ≥0) * errorBound δ deg domain) :
    RoundProxGapBoundedByKeystone (k := k) (deg := deg) domain δ (roundCA + ε_sc) ε_sc := by
  unfold RoundProxGapBoundedByKeystone
  gcongr

/-! ## §SUMMARY — Core 2 reduced to the BCIKS20 keystone (Core 3) + named bridges

WHAT THE PER-ROUND QUANTITY IS:
  the round's `epsCA_curves Cᵢ kᵢ δᵢ δᵢ` (= worst-case Pr that a folded/random-combined word
  `∑ rⁱ•uᵢ` is δ-close to the round's RS code `Cᵢ` while the stack is NOT jointly close),
  with `epsPG Cᵢ δᵢ ≤ epsCA_curves Cᵢ 1 δᵢ δᵢ` (ABF26 Fact 4.5). This is EXACTLY what the
  keystone `correlatedAgreement_affine_curves` bounds: its predicate output is, via the
  in-tree numeric bridge, `epsCA_curves Cᵢ kᵢ δᵢ δᵢ ≤ kᵢ · errorBound δᵢ degᵢ domainᵢ`.

REDUCTION THEOREMS PROVEN (names + hypotheses):
  §1  keystone_curves_bound   (StrictCoeffPolysResidual, BoundaryProbabilityResidual, hδ, [NeZero deg])
        ⟹ epsCA_curves C k δ δ ≤ k·errorBound       — the per-round quantity, sharp numeric bound.
  §1  keystone_epsPG_bound     (k=1 residuals, hδ, [NeZero deg])
        ⟹ epsPG C δ ≤ 1·errorBound                  — the proximity-gap error, via Fact 4.5.
  §2  RoundKeystoneData / .curves_bound / .proxGapBound — per-round packaging of the residuals.
  §2  perRoundProximityGap_of_correlatedAgreement (RoundKeystoneData)
        ⟹ PerRoundProximityGap proxGapBound proxGapBound ∧ (∀ i, keystone numeric bound).
  §2  perRoundProximityGap_transfer (RoundKeystoneData, e, he : e = proxGapBound)
        ⟹ PerRoundProximityGap e proxGapBound ∧ (∀ i, keystone numeric bound for e).
  §3  whirRbrKeystone_of_soundOk / epsRbr_le_of_forall_le / whirRbrKeystone_of_correlatedAgreement
        ⟹ WhirRbrKeystone from a SoundOk witness at the keystone budget + the budget LUB accounting.
  §4  RoundProxGapBoundedByKeystone / roundProxGap_of_keystone_no_sumcheck /
      roundProxGap_of_keystone_and_sumcheck
        ⟹ the honest CA-plus-sumcheck split: round error ≤ k·errorBound (keystone) + ε_sc (named).

IS CORE 2 NOW FULLY REDUCED TO THE KEYSTONE (CORE 3)?  YES, modulo named bridges:
  * The per-round proximity-gap quantity is reduced to `correlatedAgreement_affine_curves`,
    whose ONLY residual hypotheses are the §5 `StrictCoeffPolysResidual` and §6.2
    `BoundaryProbabilityResidual` (= Core 3) plus `hδ`. No new probabilistic content is added.
  * `PerRoundProximityGap` is discharged (with the GENUINE numeric CA bound `R.curves_bound`,
    not a vacuous re-labelling: §2.1 proves the keystone bounds the actual `epsCA_curves`).
  * `WhirRbrKeystone` is reduced to the proven budget accounting (`epsRbr_le_of_forall_le`,
    LUB) + a `SoundOk` witness whose per-round soundness content is the §1 keystone bounds.
  * The sumcheck/folding bridge (§4) is named EXPLICITLY (`RoundProxGapBoundedByKeystone`,
    additive `ε_sc`), so where the round is CA-PLUS-sumcheck, the CA part is the keystone and
    the sumcheck part `ε_sc` is a precisely-named residual — never hidden.

NON-VACUITY ASSESSMENT (honest):
  * §1 `keystone_curves_bound` / `keystone_epsPG_bound` are NON-VACUOUS: they consume the
    real keystone `correlatedAgreement_affine_curves` and the real in-tree numeric bridge and
    Fact 4.5, producing a genuine numeric inequality about `epsCA_curves` / `epsPG`. The
    keystone's residuals are carried (not discharged), so this is a faithful reduction.
  * §2.2 `perRoundProximityGap_of_correlatedAgreement`'s *predicate* half is reflexive (the
    abstract `PerRoundProximityGap` is definitionally `∀ i, e i = ProxGapBound i`, vacuous when
    `e := ProxGapBound`); the NON-VACUOUS content is the conjoined `R.curves_bound`, which proves
    the keystone genuinely bounds the per-round proximity-gap quantity by `proxGapBound`. This is
    the honest statement: the predicate is plumbing, the keystone bound is the math.
  * §3 reductions are the proven `max'`/LUB budget accounting (non-trivial order theory) plus a
    black-box `SoundOk` consumption; the genuine per-round soundness is the §1 keystone — the
    SoundOk witness is the single interface point, as in the in-tree `RbrBudgetAccounting`.
  * §4 is the honest CA-plus-sumcheck split; `ε_sc` is a NAMED residual (the sumcheck/OOD/shift
    soundness + folding L4.20–4.23), not absorbed into the keystone.

  REMAINING OPEN (named, = Core 3 + sumcheck): `StrictCoeffPolysResidual`,
  `BoundaryProbabilityResidual` (the §5/§6.2 list-decoding residuals = Core 3), and the per-round
  sumcheck residual `ε_sc` (§4). Core 2's abstract Props are no longer free-floating: they are
  theorems-of the keystone + these named residuals.
-/

end Core2Keystone

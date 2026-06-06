/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexander Hicks
-/

import ArkLib.Data.CodingTheory.ProximityGap.Errors
import ArkLib.Data.CodingTheory.ListDecodability
import ArkLib.Data.CodingTheory.ReedSolomon
import ArkLib.ToMathlib.BridgeListDecodingCA
import ArkLib.ToMathlib.Bridge2BCHKS25
import ArkLib.ToMathlib.Bridge2BGKS20
import ArkLib.Data.CodingTheory.Connections.EpsMCABadGlue
import ArkLib.Data.CodingTheory.Connections.GKL24FirstMoment
import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# Connections between list decoding and correlated agreement (ABF26 §5)

External *proposition statements* for the §5 results that link list-size bounds to
correlated-agreement error bounds and vice versa. From ABF26 (Arnon-Boneh-Fenzi,
*Open Problems in List Decoding and Correlated Agreement*, 2026), §5.

These four propositions directly bridge the Grand List Decoding Challenge and the
Grand MCA Challenge of §1. T5.1 turns a list-size bound into an MCA bound;
T5.2 / T5.3 turn CA bounds into list-size bounds; T5.4 demonstrates that the
implication "list-decoding ⇒ CA" cannot be tight in general.

## Main statements (external admits)

- `linear_listSize_to_epsMCA_gcxk25` — ABF26 T5.1 [GCXK25 Thm 3]: list decoding at
  `δ` with list size `L` implies `ε_mca(C, 1 - √(1-δ+η)) ≤ (L²·δ·n + 1/η)/|F|`.
- `rs_epsCA_small_implies_lambda_lt_F_bchks25` — ABF26 T5.2 [BCHKS25 Thm 1.9]:
  `ε_ca < 1/(2n)` (with explicit proximity loss) implies `|Λ(C, δ)| < |F|`.
- `rs_epsCA_implies_lambda_extended_cs25` — ABF26 T5.3 [CS25 Thm 2]: small `ε_ca` for
  `RS[F, L, k]` implies a quantitative list-size bound for the related code
  `RS[F, L, k+1]`.
- `rs_epsCA_separation_bgks20` — ABF26 T5.4 [BGKS20 Lem 3.3]: characteristic-2 RS
  codes with rate `1/8` have `ε_ca(C, 1 - ρ^{1/3}) ≥ 1 - 1/|F|`, separating list
  decoding from CA.

## Coercion conventions

Each statement bounds an `ENNReal`-valued `ε_ca` or `ε_mca` (or `Lambda`) in terms of a
real-valued numeric expression. To wire real expressions into the `ENNReal` and `ℝ≥0`
worlds we use:

- `ENNReal.ofReal x` when `x : ℝ` is the RHS of a `≤` / `<` / `=`. This truncates
  negative `x` to `0`, which only matters in degenerate parameter regimes where the
  paper's bound is vacuous anyway.
- `x.toNNReal` when `x : ℝ` is the proximity radius (argument to `ε_mca` / `ε_ca`).
  Each occurrence is either provably non-negative under the theorem's hypotheses (most
  cases), or the truncation aligns with the paper-stated regime (e.g. T5.1 uses
  `η ≤ δ` to keep `1 − √(1−δ+η)` in `[0, 1]`).

## References

- [ABF26] Arnon, Boneh, Fenzi. *Open Problems in List Decoding and Correlated Agreement*.
  2026.
- [GCXK25] Theorem 3 in their paper.
- [BCHKS25] Theorem 1.9.
- [CS25] Theorem 2.
- [BGKS20] Lemma 3.3.
-/

set_option linter.unusedFintypeInType false
set_option linter.unusedDecidableInType false
set_option linter.unusedSectionVars false

namespace CodingTheory

open scoped NNReal
open scoped ProbabilityTheory BigOperators
open ListDecodable ProximityGap

section ListImpliesMCA

variable {ι : Type} [Fintype ι] [Nonempty ι] [DecidableEq ι]
variable {F : Type} [Field F] [Fintype F] [DecidableEq F]

/-- **ABF26 Theorem 5.1 [GCXK25 Theorem 3].** List decoding implies MCA.

Let `C ⊆ F^n` be a linear code and let `δ, η ∈ (0, 1)`. If `|Λ(C, δ)| ≤ L`, then

  `ε_mca(C, 1 - √(1 - δ + η)) ≤ (L²·δ·n + 1/η) / |F|`

The conclusion's proximity radius `1 - √(1 - δ + η)` is the "Johnson lift" of `δ`
(plus the `η` slack). For Reed-Solomon codes this implies MCA up to the "2 Johnson"
regime via Corollary 3.3; for random RS codes (which list-decode to capacity by
Theorem 3.6) it implies MCA for random RS up to the Johnson bound.

**Paper divergence — added hypothesis `η ≤ δ`.** Paper T5.1 only
requires `δ, η ∈ (0, 1)`. We strengthen this to `η ≤ δ` so that the
conclusion's proximity radius `1 - √(1 - δ + η)` stays in `[0, 1]`
(without it, `(1 - √…).toNNReal` silently truncates to `0` and the
statement becomes vacuous — almost certainly not the paper's intent in
the `η > δ` regime, which is the "list-decoding capacity overshoot"
case the paper itself doesn't analyse). The added hypothesis matches
the way every existing application of the bound uses it.

If a downstream caller genuinely needs the `0 < η < 1` regime without
the `η ≤ δ` bound, the right move is to add a paper-faithful variant
of this theorem with the truncation made explicit (and the bound made
vacuous), rather than dropping the hypothesis here.

**HONEST REDUCTION AVAILABLE.** The supremum-packaging glue is fully proven, `sorry`-free
and axiom-clean, in `linear_listSize_to_epsMCA_gcxk25_of_residuals`, which derives this exact
bound from the GCXK25 *per-stack* amplification bound (`hPerStack` — the genuine external
content: for *each* word stack `u`, the probability of the MCA bad-event is at most the
`(L²δn + 1/η)/|F|` bound) by `iSup_le`.  The external statement below isolates exactly
`hPerStack`, which the *unhypothesized* in-tree statement cannot supply: that needs GCXK25's
`Bad¹ ≤ pn` count (the GKL24 maximal-correlated-agree-domain machinery, not connected to
`epsMCA`/`Lambda` in-tree) together with the in-tree `Bad² < 1/ε` second-moment count
(`Connections/GCXK25SecondMoment.lean`) and the §5 reduction from `epsMCA`'s arbitrary-stack
supremum to GCXK25's per-codeword-pair `Bad(π₁,π₂,δ)` count.

Admitted as an external result. -/
theorem linear_listSize_to_epsMCA_gcxk25_of_residuals
    (C : LinearCode ι F) (L : ℕ) (δ η : ℝ)
    (_hδ_pos : 0 < δ) (_hδ_lt : δ < 1)
    (_hη_pos : 0 < η) (_hη_lt : η < 1) (_hη_le_δ : η ≤ δ)
    (_hΛ : Lambda ((C : Set (ι → F))) δ ≤ (L : ℕ∞))
    -- GCXK25 Theorem 3 per-stack amplification bound (the genuine external content):
    (hPerStack :
        ∀ u : Code.WordStack F (Fin 2) ι,
          Pr_{let γ ← $ᵖ F}[mcaEvent (F := F)
              ((C : Set (ι → F)))
              ((1 - (1 - δ + η) ^ ((1 : ℝ) / 2)).toNNReal) (u 0) (u 1) γ] ≤
            ENNReal.ofReal
              (((L : ℝ) ^ 2 * δ * Fintype.card ι + 1 / η) / Fintype.card F)) :
    epsMCA (F := F) (A := F) ((C : Set (ι → F)))
        ((1 - (1 - δ + η) ^ ((1 : ℝ) / 2)).toNNReal) ≤
      ENNReal.ofReal
        (((L : ℝ) ^ 2 * δ * Fintype.card ι + 1 / η) / Fintype.card F) := by
  unfold epsMCA
  exact iSup_le hPerStack

/-- **ABF26 Theorem 5.1 [GCXK25 Theorem 3] — sharpened honest reduction via the bad-`γ`
count.** This derives the exact T5.1 bound from the GCXK25 *per-stack bad-combining-point
count* (`hBadCount`: for every stack `u`, the number of scalars `γ` for which the MCA bad
event fires is at most `L²·δ·n + 1/η`), rather than from the raw per-stack *probability*
bound used in `linear_listSize_to_epsMCA_gcxk25_of_residuals`.

The residual `hBadCount` is *strictly closer* to GCXK25's actual combinatorial content: it is
literally `|Bad(π₁,π₂,δ)| ≤ pn·L² + 1/ε`, i.e. the sum of GCXK25's first-moment count
`|Bad¹| ≤ pn` (the GKL24 agree-domain machinery, the named external residual) and the in-tree
second-moment count `|Bad²| < 1/ε` (`GCXK25SecondMoment.card_lt_one_div_of_second_moment_rs`),
times the `L²` list-size factor. The entire supremum-to-count plumbing of ABF26 §5 — going
from `ε_mca`'s arbitrary-stack supremum to a uniform per-stack count of bad `γ` — is now
*proven* in-tree via `ProximityGap.epsMCA_le_ofReal_of_forall_mcaBad_card_le`. -/
theorem linear_listSize_to_epsMCA_gcxk25_of_bad_count
    (C : LinearCode ι F) (L : ℕ) (δ η : ℝ)
    (_hδ_pos : 0 < δ) (_hδ_lt : δ < 1)
    (_hη_pos : 0 < η) (_hη_lt : η < 1) (_hη_le_δ : η ≤ δ)
    (_hΛ : Lambda ((C : Set (ι → F))) δ ≤ (L : ℕ∞))
    -- GCXK25 Theorem 3 per-stack bad-combining-point count (the genuine external content):
    (hBadCount :
        ∀ u : Code.WordStack F (Fin 2) ι,
          ((ProximityGap.mcaBad (F := F) ((C : Set (ι → F)))
              ((1 - (1 - δ + η) ^ ((1 : ℝ) / 2)).toNNReal) (u 0) (u 1)).card : ℝ) ≤
            (L : ℝ) ^ 2 * δ * Fintype.card ι + 1 / η) :
    epsMCA (F := F) (A := F) ((C : Set (ι → F)))
        ((1 - (1 - δ + η) ^ ((1 : ℝ) / 2)).toNNReal) ≤
      ENNReal.ofReal
        (((L : ℝ) ^ 2 * δ * Fintype.card ι + 1 / η) / Fintype.card F) :=
  ProximityGap.epsMCA_le_ofReal_of_forall_mcaBad_card_le
    ((C : Set (ι → F)))
    ((1 - (1 - δ + η) ^ ((1 : ℝ) / 2)).toNNReal)
    hBadCount

/-- **ABF26 Theorem 5.1 [GCXK25 Theorem 3] — first-moment summand from the in-tree GKL24
brick.** This derives the *first-moment* part of T5.1,

  `ε_mca(C, 1 − √(1 − δ + η)) ≤ ENNReal.ofReal ((L²·δ·n) / |F|)`,

from the single named residual `ProximityGap.GKL24FirstMomentResidual` (the GKL24
agree-domain / `|Bad¹| ≤ p·n` first-moment count, uniformly over a size-`L²` close-codeword
carrier), via the *fully in-tree* per-codeword determinacy brick proven in
`Connections/GKL24FirstMoment.lean` (`epsMCA_le_ofReal_of_gkl24_residual`).

This is strictly sharper plumbing than `linear_listSize_to_epsMCA_gcxk25_of_bad_count`: there the
whole per-stack count `L²·δ·n + 1/η` was a single opaque residual, whereas here the per-codeword
*first-moment* count is reduced to its honest GKL24 core — the combining point of any single
witness codeword is determined by the support of `u₁` (proven in-tree), so the only external input
left in this summand is GKL24's sharpening of that support count to `δ·n`. The `1/η` second-moment
summand is supplied separately by `GCXK25SecondMoment.card_lt_one_div_of_second_moment_rs`. -/
theorem linear_listSize_to_epsMCA_gcxk25_firstMoment_of_gkl24_residual
    (C : LinearCode ι F) (L : ℕ) (δ η : ℝ)
    (hδ_pos : 0 < δ) (_hδ_lt : δ < 1)
    (_hη_pos : 0 < η) (_hη_lt : η < 1) (_hη_le_δ : η ≤ δ)
    (_hΛ : Lambda ((C : Set (ι → F))) δ ≤ (L : ℕ∞))
    -- The GKL24 first-moment agree-domain residual (the genuine external content): at the
    -- Johnson-lifted MCA radius, with list-size factor `B_T = L²` and per-codeword count
    -- `b = δ·n` (`δ` the *list-decoding* radius, GCXK25's `|Bad¹| ≤ p·n`):
    (hres :
        ProximityGap.GKL24FirstMomentResidual C
          ((1 - (1 - δ + η) ^ ((1 : ℝ) / 2)).toNNReal)
          ((L : ℝ) ^ 2) (δ * Fintype.card ι)) :
    epsMCA (F := F) (A := F) ((C : Set (ι → F)))
        ((1 - (1 - δ + η) ^ ((1 : ℝ) / 2)).toNNReal) ≤
      ENNReal.ofReal
        (((L : ℝ) ^ 2 * (δ * Fintype.card ι)) / Fintype.card F) :=
  ProximityGap.epsMCA_le_ofReal_of_gkl24_residual C
    ((1 - (1 - δ + η) ^ ((1 : ℝ) / 2)).toNNReal)
    (by positivity) hres

/-- **ABF26 Theorem 5.1 [GCXK25 Theorem 3] — unconditional in-tree first-moment
relaxation.**  This is the same first-moment plumbing as
`linear_listSize_to_epsMCA_gcxk25_firstMoment_of_gkl24_residual`, but with the genuinely proven
per-codeword determinacy bound `|Bad_w| ≤ n` in place of the external GKL24 sharpening
`|Bad_w| ≤ δ·n`.

Thus a carrier `T` of codewords with `(T.card : ℝ) ≤ B_T` gives

  `ε_mca(C, 1 − √(1 − δ + η)) ≤ ENNReal.ofReal ((B_T·n)/|F|)`.

The proof contains no paper residual: it is exactly
`ProximityGap.epsMCA_le_ofReal_of_listFactor`, whose per-codeword count is proved in
`Connections/GKL24FirstMoment.lean`. -/
theorem linear_listSize_to_epsMCA_gcxk25_firstMoment_inTree_card
    (C : LinearCode ι F) (δ η : ℝ)
    (T : Finset (ι → F)) {B_T : ℝ}
    (hT : ∀ w ∈ (C : Set (ι → F)), w ∈ T)
    (hTsub : ∀ w ∈ T, w ∈ (C : Set (ι → F)))
    (hcard : (T.card : ℝ) ≤ B_T) :
    epsMCA (F := F) (A := F) ((C : Set (ι → F)))
        ((1 - (1 - δ + η) ^ ((1 : ℝ) / 2)).toNNReal) ≤
      ENNReal.ofReal ((B_T * (Fintype.card ι : ℝ)) / Fintype.card F) :=
  ProximityGap.epsMCA_le_ofReal_of_listFactor C
    ((1 - (1 - δ + η) ^ ((1 : ℝ) / 2)).toNNReal)
    T hT hTsub hcard

/-- **ABF26 Theorem 5.1 [GCXK25 Theorem 3] — canonical in-tree first-moment relaxation.**
This is the no-carrier version of `linear_listSize_to_epsMCA_gcxk25_firstMoment_inTree_card`.
Taking the carrier to be all codewords and using the proven single-codeword determinacy count gives

  `ε_mca(C, 1 − √(1 − δ + η)) ≤ ENNReal.ofReal ((|F|^n · n)/|F|)`.

It is intentionally much weaker than the GCXK25/GKL24 `L²·δ·n` first-moment term, but it closes
the first-moment residual interface without any external hypothesis. -/
theorem linear_listSize_to_epsMCA_gcxk25_firstMoment_inTree_univ
    (C : LinearCode ι F) (δ η : ℝ) :
    epsMCA (F := F) (A := F) ((C : Set (ι → F)))
        ((1 - (1 - δ + η) ^ ((1 : ℝ) / 2)).toNNReal) ≤
      ENNReal.ofReal
        (((Fintype.card (ι → F) : ℝ) * (Fintype.card ι : ℝ)) / Fintype.card F) :=
  ProximityGap.epsMCA_le_ofReal_inTree_firstMoment_card C
    ((1 - (1 - δ + η) ^ ((1 : ℝ) / 2)).toNNReal)

/-- **ABF26 Theorem 5.1 [GCXK25 Theorem 3].** List decoding implies MCA.

Let `C ⊆ F^n` be a linear code and let `δ, η ∈ (0, 1)`. If `|Λ(C, δ)| ≤ L`, then

  `ε_mca(C, 1 - √(1 - δ + η)) ≤ (L²·δ·n + 1/η) / |F|`

See `linear_listSize_to_epsMCA_gcxk25_of_residuals` for the honest reduction (this external
statement isolates the genuinely external GCXK25 per-stack amplification bound), or
`linear_listSize_to_epsMCA_gcxk25_of_bad_count` for the sharpened reduction that isolates the
genuinely external content as a per-stack *bad-`γ` count* (closest to GCXK25's `Bad` count).
Admitted as an external result. -/
def linear_listSize_to_epsMCA_gcxk25
    (C : LinearCode ι F) (L : ℕ) (δ η : ℝ)
    (_hδ_pos : 0 < δ) (_hδ_lt : δ < 1)
    (_hη_pos : 0 < η) (_hη_lt : η < 1) (_hη_le_δ : η ≤ δ)
    (_hΛ : Lambda ((C : Set (ι → F))) δ ≤ (L : ℕ∞)) : Prop :=
    epsMCA (F := F) (A := F) ((C : Set (ι → F)))
        ((1 - (1 - δ + η) ^ ((1 : ℝ) / 2)).toNNReal) ≤
      ENNReal.ofReal
        (((L : ℝ) ^ 2 * δ * Fintype.card ι + 1 / η) / Fintype.card F)
  -- ABF26-T5.1; external statement [GCXK25 Thm 3].
  -- Missing ingredient: the GCXK25 list-decoding→MCA amplification. GCXK25 (eprint 2025/870)
  -- partition the bad combining points into `Bad¹` (count `≤ p·n`, their Cor 2 via the GKL24
  -- agree-domain intersection Lemma 1/Cor 1) and `Bad²` (count `< 1/ε`, their Lemma 3, a
  -- second-moment Cauchy–Schwarz count over the δ-agreement domains); together with the
  -- `l ≤ L²` list-size factor this gives the `L²·δ·n + 1/η` shape, divided by |F|.
  --
  -- VERIFIED BACKBONE: the GCXK25 Lemma 3 `Bad² < 1/ε` second-moment count is now formalized
  -- kernel-clean in `Connections/GCXK25SecondMoment.lean`
  -- (`GCXK25SecondMoment.card_lt_inv_of_second_moment_rs`, with the abstract master inequality
  -- `card_le_of_second_moment` and the Cauchy–Schwarz step
  -- `sq_sum_card_le_card_mul_sum_sum_card_inter`). Its `ε ≤ p` hypothesis is exactly the
  -- `η ≤ δ` constraint imposed above.
  --
  -- STRUCTURAL GLUE NOW IN-TREE: the supremum-to-count reduction of ABF26 §5 — going from
  -- `epsMCA`'s ARBITRARY-stack supremum to a uniform per-stack count of bad scalars `γ` — is
  -- proven `sorry`-free / axiom-clean in `Connections/EpsMCABadGlue.lean`
  -- (`ProximityGap.epsMCA_le_ofReal_of_forall_mcaBad_card_le`, via the per-stack counting
  -- bound `mcaEvent_prob_le_of_mcaBad_card_le`). It is wired into the sharpened reduction
  -- `linear_listSize_to_epsMCA_gcxk25_of_bad_count` above, whose residual `hBadCount` is the
  -- per-stack bad-`γ` count `|mcaBad u| ≤ L²·δ·n + 1/η` (i.e. GCXK25's `|Bad(π₁,π₂,δ)|`).
  --
  -- STILL EXTERNAL (not in-tree): the per-stack count `|mcaBad u| ≤ L²·δ·n + 1/η` itself, i.e.
  -- GCXK25's amplification = the GKL24 maximal-correlated-agree-domain machinery and the
  -- `Bad¹ ≤ pn` first-moment count (the `A_{δ,{π₁,π₂},C}` agree-domain structure, not connected
  -- to `Lambda`/`epsMCA` in-tree) plus the connection of GCXK25's per-CODEWORD-PAIR
  -- `Bad(π₁,π₂,δ)` count to the arbitrary stack's `mcaBad`. The in-tree second-moment count
  -- `|Bad²| < 1/ε` (`GCXK25SecondMoment`) supplies the `1/η` summand of that residual.
  -- Genuinely external pending the first-moment / agree-domain piece.

/-- Prop-level wrapper for T5.1 from the per-stack probability residual. -/
theorem linear_listSize_to_epsMCA_gcxk25_of_residuals_prop
    (C : LinearCode ι F) (L : ℕ) (δ η : ℝ)
    (hδ_pos : 0 < δ) (hδ_lt : δ < 1)
    (hη_pos : 0 < η) (hη_lt : η < 1) (hη_le_δ : η ≤ δ)
    (hΛ : Lambda ((C : Set (ι → F))) δ ≤ (L : ℕ∞))
    (hPerStack :
        ∀ u : Code.WordStack F (Fin 2) ι,
          Pr_{let γ ← $ᵖ F}[mcaEvent (F := F)
              ((C : Set (ι → F)))
              ((1 - (1 - δ + η) ^ ((1 : ℝ) / 2)).toNNReal) (u 0) (u 1) γ] ≤
            ENNReal.ofReal
              (((L : ℝ) ^ 2 * δ * Fintype.card ι + 1 / η) / Fintype.card F)) :
    linear_listSize_to_epsMCA_gcxk25 C L δ η
      hδ_pos hδ_lt hη_pos hη_lt hη_le_δ hΛ :=
  linear_listSize_to_epsMCA_gcxk25_of_residuals C L δ η
    hδ_pos hδ_lt hη_pos hη_lt hη_le_δ hΛ hPerStack

/-- Prop-level wrapper for T5.1 from the sharper bad-`γ` count residual. -/
theorem linear_listSize_to_epsMCA_gcxk25_of_bad_count_prop
    (C : LinearCode ι F) (L : ℕ) (δ η : ℝ)
    (hδ_pos : 0 < δ) (hδ_lt : δ < 1)
    (hη_pos : 0 < η) (hη_lt : η < 1) (hη_le_δ : η ≤ δ)
    (hΛ : Lambda ((C : Set (ι → F))) δ ≤ (L : ℕ∞))
    (hBadCount :
        ∀ u : Code.WordStack F (Fin 2) ι,
          ((ProximityGap.mcaBad (F := F) ((C : Set (ι → F)))
              ((1 - (1 - δ + η) ^ ((1 : ℝ) / 2)).toNNReal) (u 0) (u 1)).card : ℝ) ≤
            (L : ℝ) ^ 2 * δ * Fintype.card ι + 1 / η) :
    linear_listSize_to_epsMCA_gcxk25 C L δ η
      hδ_pos hδ_lt hη_pos hη_lt hη_le_δ hΛ :=
  linear_listSize_to_epsMCA_gcxk25_of_bad_count C L δ η
    hδ_pos hδ_lt hη_pos hη_lt hη_le_δ hΛ hBadCount

end ListImpliesMCA

section CAImpliesList

variable {ι : Type} [Fintype ι] [Nonempty ι] [DecidableEq ι]
variable {F : Type} [Field F] [Fintype F] [DecidableEq F]

/-- **ABF26 Theorem 5.2 [BCHKS25 Theorem 1.9].** Small CA error implies small list size.

Let `C := RS[F, L, k]` be a Reed-Solomon code with rate `ρ` and let `δ ∈ (0, 1-ρ)`.
If

  `ε_ca(C, δ_fld = δ + 2/n, δ_int = 1 - ρ - 1/n) < 1/(2n)`

then

  `|Λ(C, δ)| < |F|` .

Reading: CA at `δ + 2/n` with proximity loss to `1 - ρ - 1/n` having very small error
forces the list size at `δ` to be strictly below the field size. Admitted as an
external result.

**HONEST REDUCTION AVAILABLE.** The contrapositive packaging is fully proven, `sorry`-free
and axiom-clean, in `rs_epsCA_small_implies_lambda_lt_F_bchks25_of_residuals`, which derives
the bound from BCHKS25's bad-line count (`hBadLine` — the genuine external content: a list of
`≥ |F|` close codewords forces `ε_ca ≥ 1/(2n)` via the affine-shift interpolation argument)
as an explicit hypothesis.  The bare external statement isolates exactly `hBadLine`, which
needs the RS interpolation lemma "|F|-codewords ⟹ bad line" not connected to `epsCA`/`Lambda`
in-tree. -/
theorem rs_epsCA_small_implies_lambda_lt_F_bchks25_of_residuals
    (domain : ι ↪ F) (k : ℕ) (δ : ℝ)
    (_hδ_pos : 0 < δ)
    (_hδ_lt : (δ : ℝ) < 1 - (k : ℝ) / Fintype.card ι)
    (_hε_ca :
        epsCA (F := F) (A := F)
            ((ReedSolomon.code domain k : Set (ι → F)))
            ((δ + 2 / Fintype.card ι).toNNReal)
            ((1 - (k : ℝ) / Fintype.card ι - 1 / Fintype.card ι).toNNReal) <
          ENNReal.ofReal (1 / (2 * Fintype.card ι)))
    -- BCHKS25 Theorem 1.9 bad-line count (the genuine external content): if the list size at
    -- `δ` is *not* below `|F|`, the affine-shift interpolation produces a CA failure of
    -- probability `≥ 1/(2n)`.
    (hBadLine :
        ¬ (Lambda ((ReedSolomon.code domain k : Set (ι → F))) δ < (Fintype.card F : ℕ∞)) →
          ENNReal.ofReal (1 / (2 * Fintype.card ι)) ≤
            epsCA (F := F) (A := F)
              ((ReedSolomon.code domain k : Set (ι → F)))
              ((δ + 2 / Fintype.card ι).toNNReal)
              ((1 - (k : ℝ) / Fintype.card ι - 1 / Fintype.card ι).toNNReal)) :
    Lambda ((ReedSolomon.code domain k : Set (ι → F))) δ < (Fintype.card F : ℕ∞) := by
  by_contra hcon
  exact absurd (hBadLine hcon) (not_le.mpr _hε_ca)

/-- **ABF26 Theorem 5.2 [BCHKS25 Theorem 1.9].** Small CA error implies small list size.
(External statement — see `rs_epsCA_small_implies_lambda_lt_F_bchks25_of_residuals` for the
fully-proven honest reduction.) -/
def rs_epsCA_small_implies_lambda_lt_F_bchks25
    (domain : ι ↪ F) (k : ℕ) (δ : ℝ)
    (_hδ_pos : 0 < δ)
    (_hδ_lt : (δ : ℝ) < 1 - (k : ℝ) / Fintype.card ι)
    (_hε_ca :
        epsCA (F := F) (A := F)
            ((ReedSolomon.code domain k : Set (ι → F)))
            ((δ + 2 / Fintype.card ι).toNNReal)
            ((1 - (k : ℝ) / Fintype.card ι - 1 / Fintype.card ι).toNNReal) <
          ENNReal.ofReal (1 / (2 * Fintype.card ι))) : Prop :=
    Lambda ((ReedSolomon.code domain k : Set (ι → F))) δ < (Fintype.card F : ℕ∞)
  -- ABF26-T5.2; external statement [BCHKS25 Thm 1.9].
  -- Missing ingredient: BCHKS25's CA→list contrapositive for RS. The proof negates
  -- `|Λ(C,δ)| ≥ |F|`: if ≥|F| codewords are δ-close to some `w`, an averaging/interpolation
  -- argument over the |F| affine shifts produces a line `w + γ·v` that is δ_fld-close on a
  -- (1-δ_fld)-fraction for ≥ 1/(2n)·|F| values of γ while the pair fails δ_int-joint-proximity,
  -- forcing `epsCA(δ_fld=δ+2/n, δ_int=1-ρ-1/n) ≥ 1/(2n)`. This requires the RS-specific
  -- interpolation lemma (BCKHS25/Interpolation.lean has the collinear-proximates engine but
  -- not the |F|-codewords⇒bad-line counting). Genuinely external.

/-- Prop-level wrapper for T5.2. -/
theorem rs_epsCA_small_implies_lambda_lt_F_bchks25_of_residuals_prop
    (domain : ι ↪ F) (k : ℕ) (δ : ℝ)
    (hδ_pos : 0 < δ)
    (hδ_lt : (δ : ℝ) < 1 - (k : ℝ) / Fintype.card ι)
    (hε_ca :
        epsCA (F := F) (A := F)
            ((ReedSolomon.code domain k : Set (ι → F)))
            ((δ + 2 / Fintype.card ι).toNNReal)
            ((1 - (k : ℝ) / Fintype.card ι - 1 / Fintype.card ι).toNNReal) <
          ENNReal.ofReal (1 / (2 * Fintype.card ι)))
    (hBadLine :
        ¬ (Lambda ((ReedSolomon.code domain k : Set (ι → F))) δ < (Fintype.card F : ℕ∞)) →
          ENNReal.ofReal (1 / (2 * Fintype.card ι)) ≤
            epsCA (F := F) (A := F)
              ((ReedSolomon.code domain k : Set (ι → F)))
              ((δ + 2 / Fintype.card ι).toNNReal)
              ((1 - (k : ℝ) / Fintype.card ι - 1 / Fintype.card ι).toNNReal)) :
    rs_epsCA_small_implies_lambda_lt_F_bchks25 domain k δ hδ_pos hδ_lt hε_ca :=
  rs_epsCA_small_implies_lambda_lt_F_bchks25_of_residuals
    domain k δ hδ_pos hδ_lt hε_ca hBadLine

/-- **BCHKS25 named-witness connector.**  This is the exact ABF26 T5.2 reduction with the
opaque `hBadLine` hypothesis replaced by the strictly smaller `BadLineWitness` producer from
`ArkLib.ToMathlib.Bridge2BCHKS25`.

The remaining obligation is the genuine BCHKS25 construction: from the negated list-size bound,
produce the bad combining line.  Once supplied, the in-tree bridge arithmetic converts it to the
`hBadLine` shape consumed by `rs_epsCA_small_implies_lambda_lt_F_bchks25_of_residuals`. -/
theorem rs_epsCA_small_implies_lambda_lt_F_bchks25_of_badLineWitness
    (domain : ι ↪ F) (k : ℕ) (δ : ℝ)
    (hδ_pos : 0 < δ)
    (hδ_lt : (δ : ℝ) < 1 - (k : ℝ) / Fintype.card ι)
    (hε_ca :
        epsCA (F := F) (A := F)
            ((ReedSolomon.code domain k : Set (ι → F)))
            ((δ + 2 / Fintype.card ι).toNNReal)
            ((1 - (k : ℝ) / Fintype.card ι - 1 / Fintype.card ι).toNNReal) <
          ENNReal.ofReal (1 / (2 * Fintype.card ι)))
    (provBadLine :
        ¬ (Lambda ((ReedSolomon.code domain k : Set (ι → F))) δ < (Fintype.card F : ℕ∞)) →
          Bridge.BadLineWitness (F := F)
            ((ReedSolomon.code domain k : Set (ι → F)))
            ((δ + 2 / Fintype.card ι).toNNReal)
            ((1 - (k : ℝ) / Fintype.card ι - 1 / Fintype.card ι).toNNReal)) :
    Lambda ((ReedSolomon.code domain k : Set (ι → F))) δ < (Fintype.card F : ℕ∞) :=
  rs_epsCA_small_implies_lambda_lt_F_bchks25_of_residuals
    domain k δ hδ_pos hδ_lt hε_ca
    (Bridge.hBadLine_of_provBadLine
      ((ReedSolomon.code domain k : Set (ι → F)))
      ((δ + 2 / Fintype.card ι).toNNReal)
      ((1 - (k : ℝ) / Fintype.card ι - 1 / Fintype.card ι).toNNReal)
      provBadLine)

/-- Prop-level wrapper for T5.2 from a `BadLineWitness` producer. -/
theorem rs_epsCA_small_implies_lambda_lt_F_bchks25_of_badLineWitness_prop
    (domain : ι ↪ F) (k : ℕ) (δ : ℝ)
    (hδ_pos : 0 < δ)
    (hδ_lt : (δ : ℝ) < 1 - (k : ℝ) / Fintype.card ι)
    (hε_ca :
        epsCA (F := F) (A := F)
            ((ReedSolomon.code domain k : Set (ι → F)))
            ((δ + 2 / Fintype.card ι).toNNReal)
            ((1 - (k : ℝ) / Fintype.card ι - 1 / Fintype.card ι).toNNReal) <
          ENNReal.ofReal (1 / (2 * Fintype.card ι)))
    (provBadLine :
        ¬ (Lambda ((ReedSolomon.code domain k : Set (ι → F))) δ < (Fintype.card F : ℕ∞)) →
          Bridge.BadLineWitness (F := F)
            ((ReedSolomon.code domain k : Set (ι → F)))
            ((δ + 2 / Fintype.card ι).toNNReal)
            ((1 - (k : ℝ) / Fintype.card ι - 1 / Fintype.card ι).toNNReal)) :
    rs_epsCA_small_implies_lambda_lt_F_bchks25 domain k δ hδ_pos hδ_lt hε_ca :=
  rs_epsCA_small_implies_lambda_lt_F_bchks25_of_badLineWitness
    domain k δ hδ_pos hδ_lt hε_ca provBadLine

/-- **ABF26 Theorem 5.3 [CS25 Theorem 2] — honest reduction form.**

The fully-proven, `sorry`-free, axiom-clean *contradiction core* of CS25 Theorem 2, with the
single genuinely-external ingredient (CS25's "Claim 3" deep-hole + Schwartz–Zippel count,
which manufactures the bad correlated-agreement stack from a large `C⁺`-list) surfaced as an
explicit hypothesis `hClaim3`.

Write `q := |F|`, `n := |ι|`, `s := q - n`, `ε := ε_ca(C, δ).toReal`, and
`L0 := ⌈q/(1-η)·ε⌉`.  CS25's Claim 3 says: if the degree-`(k+1)` code has *more than* `L0`
codewords within relative distance `δ` of some word, then evaluating the deep-hole
construction at `L = L0+1` produces **strictly more than** `E(L0) := L0·s/(L0·k + s)`
bad combining points (strict because `E` is increasing in the list size `L` and the list has
size `≥ L0+1`), forcing `ε_ca·q > E(L0)`.  This is exactly `hClaim3`.

The arithmetic glue (`Bridge.cs25_qeps_le_E`: the two numeric hypotheses force
`ε_ca·q ≤ E(L0)`) then contradicts `hClaim3`, closing the bound.  This matches the paper's
"substituting `E = εq` gives the contradiction".

Faithfulness of the *statement*: under `η = k·ε·q/s` (the tightest admissible slack) the
threshold `L0 = ⌈q·ε·s/(s − k·ε·q)⌉` coincides with CS25 Theorem 2's published list size
`L = ⌈εq(q−n)/(q−n−kεq)⌉`; for larger admissible `η` the in-tree `L0` is *weaker* (larger),
so the in-tree statement is valid.  The strict comparison `ε_ca·q > E(L0)` (rather than `≥`)
is the in-tree analogue of CS25's *strict* hypothesis `ε < (q−n)/(kq)`, which the in-tree
`η < 1` already supplies (`ε ≤ η(q−n)/(kq) < (q−n)/(kq)`); it is needed because at the
measure-zero boundary `E(L0) = εq` the non-strict count is vacuous. -/
theorem rs_epsCA_implies_lambda_extended_cs25_of_residuals
    (domain : ι ↪ F) (k : ℕ) (δ : ℝ) (η : ℝ)
    (_hk_pos : 0 < k)
    (_hη_lo : 0 ≤ η) (_hη_lt : η < 1)
    (hs_pos : (0 : ℝ) < Fintype.card F - Fintype.card ι)
    (_hε_ca :
        (epsCA (F := F) (A := F)
            ((ReedSolomon.code domain k : Set (ι → F)))
            δ.toNNReal δ.toNNReal).toReal ≤
          η * (1 / k - Fintype.card ι / (k * Fintype.card F)))
    -- CS25 "Claim 3" (the genuine external content): a `C⁺`-list strictly larger than the
    -- claimed bound forces, via the deep-hole/Schwartz–Zippel construction, strictly more
    -- bad combining points than `E(L0)`, i.e. `ε_ca·q > E(L0)`.
    (hClaim3 :
        let ε := (epsCA (F := F) (A := F)
                    ((ReedSolomon.code domain k : Set (ι → F)))
                    δ.toNNReal δ.toNNReal).toReal
        let L0 : ℕ := Nat.ceil ((Fintype.card F : ℝ) / (1 - η) * ε)
        let s : ℝ := Fintype.card F - Fintype.card ι
        ¬ (Lambda ((ReedSolomon.code domain (k + 1) : Set (ι → F))) δ ≤ (L0 : ℕ∞)) →
          (L0 : ℝ) * s / ((L0 : ℝ) * k + s) < ε * Fintype.card F) :
    Lambda ((ReedSolomon.code domain (k + 1) : Set (ι → F))) δ ≤
      (Nat.ceil
        ((Fintype.card F : ℝ) / (1 - η)
          * (epsCA (F := F) (A := F)
                ((ReedSolomon.code domain k : Set (ι → F)))
                δ.toNNReal δ.toNNReal).toReal) : ℕ∞) := by
  classical
  -- Abbreviations.
  set ε := (epsCA (F := F) (A := F)
              ((ReedSolomon.code domain k : Set (ι → F)))
              δ.toNNReal δ.toNNReal).toReal with hεdef
  set q : ℝ := (Fintype.card F : ℝ) with hqdef
  set s : ℝ := (Fintype.card F : ℝ) - (Fintype.card ι : ℝ) with hsdef
  set L0 : ℕ := Nat.ceil (q / (1 - η) * ε) with hL0def
  -- Numerics.
  have hkpos : (1 : ℝ) ≤ (k : ℝ) := by exact_mod_cast _hk_pos
  have hqpos : (0 : ℝ) < q := by
    rw [hqdef]; exact_mod_cast Fintype.card_pos
  have hηlt : η < 1 := _hη_lt
  have h1η : (0 : ℝ) < 1 - η := by linarith
  -- `ε ≥ 0`.
  have hε0 : 0 ≤ ε := by
    rw [hεdef]; exact ENNReal.toReal_nonneg
  -- Rewrite the CA-cap hypothesis as `q·ε ≤ η·s/k`.
  have hcap1 : q * ε ≤ η * s / (k : ℝ) := by
    have hrw : η * (1 / (k : ℝ) - (Fintype.card ι : ℝ) / ((k : ℝ) * (Fintype.card F : ℝ)))
        = η * s / (k : ℝ) / q := by
      rw [hsdef, hqdef]
      have hkne : (k : ℝ) ≠ 0 := by
        have : (0 : ℝ) < k := by exact_mod_cast _hk_pos
        exact ne_of_gt this
      have hqne : (Fintype.card F : ℝ) ≠ 0 := ne_of_gt (by exact_mod_cast Fintype.card_pos)
      field_simp
    have := _hε_ca
    rw [hrw] at this
    -- this : ε ≤ η*s/k / q
    have hq' : ε * q ≤ η * s / (k : ℝ) := by
      rw [le_div_iff₀ hqpos] at this; linarith [this]
    linarith [hq']
  by_contra hcon
  -- From the residual, `E(L0) < ε·q`.
  have hstrict : (L0 : ℝ) * s / ((L0 : ℝ) * k + s) < ε * q := by
    simpa [hεdef, hL0def, hsdef, hqdef] using hClaim3 hcon
  -- `L0 ≥ 1`: else `Lambda ≤ 0` would need to fail, but `hcon` says `¬ ≤ L0`.
  -- We get `1 ≤ L0` from the residual's strict inequality forcing a positive count.
  have hL0pos : 1 ≤ (L0 : ℝ) := by
    by_contra hlt
    push_neg at hlt
    -- L0 = 0, so the LHS of hstrict is 0; but then 0 < ε·q.
    have hL0z : L0 = 0 := by
      have : (L0 : ℝ) < 1 := hlt
      exact_mod_cast Nat.lt_one_iff.mp (by exact_mod_cast this)
    rw [hL0z] at hstrict
    simp at hstrict
    -- hstrict : 0 < ε * q (after simp); combine with hcap1 and η<1.
    -- Actually with L0=0, ⌈q/(1-η)·ε⌉ = 0 ⇒ q/(1-η)·ε ≤ 0 ⇒ ε ≤ 0 ⇒ ε = 0 ⇒ contradiction.
    have hceil : q / (1 - η) * ε ≤ 0 := by
      have : Nat.ceil (q / (1 - η) * ε) = 0 := hL0z
      exact_mod_cast Nat.ceil_eq_zero.mp this
    have hεz : ε ≤ 0 := by
      by_contra hpos
      push_neg at hpos
      have : 0 < q / (1 - η) * ε := by positivity
      linarith
    have : ε * q ≤ 0 := by nlinarith [hε0, hqpos.le]
    nlinarith [hstrict, this]
  -- Arithmetic: the two caps force `q·ε ≤ E(L0)`.
  have hcap2 : q * ε ≤ (1 - η) * (L0 : ℝ) := by
    have hceil_ge : q / (1 - η) * ε ≤ (L0 : ℝ) := by
      rw [hL0def]; exact_mod_cast Nat.le_ceil _
    -- multiply both sides by (1-η) > 0
    have hmul := mul_le_mul_of_nonneg_left hceil_ge (le_of_lt h1η)
    have heq : (1 - η) * (q / (1 - η) * ε) = q * ε := by
      field_simp
    rw [heq] at hmul
    exact hmul
  have hEle : q * ε ≤ (L0 : ℝ) * s / ((L0 : ℝ) * k + s) := by
    exact Bridge.cs25_qeps_le_E (s := s) (m := (L0 : ℝ)) (k := (k : ℝ)) (η := η)
      (qε := q * ε) hs_pos hkpos hL0pos _hη_lo _hη_lt hcap1 hcap2
  -- Contradiction: E(L0) < ε·q = q·ε ≤ E(L0).
  have : (L0 : ℝ) * s / ((L0 : ℝ) * k + s) < (L0 : ℝ) * s / ((L0 : ℝ) * k + s) := by
    calc (L0 : ℝ) * s / ((L0 : ℝ) * k + s) < ε * q := hstrict
      _ = q * ε := by ring
      _ ≤ (L0 : ℝ) * s / ((L0 : ℝ) * k + s) := hEle
  exact lt_irrefl _ this

/-- **ABF26 Theorem 5.3 [CS25 Theorem 2].** CA error converts to list size for related RS.

Let `C := RS[F, L, k]` and `C⁺ := RS[F, L, k+1]` be Reed-Solomon codes with `|L| = n`.
For `δ ∈ (0, δ_min(C))` and `η ∈ [0, 1)`, if

  `ε_ca(C, δ) ≤ η · (1/k - n/(k·|F|))`

then

  `|Λ(C⁺, δ)| ≤ ⌈|F|/(1-η) · ε_ca(C, δ)⌉`

Pivots CA on `C` to a list-size bound on the extended code `C⁺`. This is *the* key bridge
from the in-tree CA chain to the Grand List-Decoding Challenge.

**HONEST REDUCTION AVAILABLE.** The contradiction core is fully proven, `sorry`-free and
axiom-clean, in `rs_epsCA_implies_lambda_extended_cs25_of_residuals`, which derives this exact
bound from CS25's "Claim 3" deep-hole/Schwartz–Zippel count (`hClaim3`) and the standard-regime
side condition `0 < |F| − |ι|` as explicit hypotheses, together with the arithmetic glue
`Bridge.cs25_qeps_le_E`.  The external statement below isolates exactly `hClaim3`, which the
*unhypothesized* in-tree statement cannot manufacture: that needs the deep-hole construction
`u⁽¹⁾ = 1/(x−a)`, pointwise scaling, the polynomial-remainder lift `RS[k] ⊂ RS[k+1]`, and the
Schwartz–Zippel collision count over the list of degree-`k` polynomials, none of which is
connected to `epsCA`/`Lambda` in-tree.  Admitted as an external result. -/
def rs_epsCA_implies_lambda_extended_cs25
    (domain : ι ↪ F) (k : ℕ) (δ : ℝ) (η : ℝ)
    (_hk_pos : 0 < k)
    (_hδ_pos : 0 < δ)
    (_hδ_min :
        (δ : ℝ) < Code.minDist ((ReedSolomon.code domain k : Set (ι → F)))
                    / Fintype.card ι)
    (_hη_lo : 0 ≤ η) (_hη_lt : η < 1)
    (_hε_ca :
        (epsCA (F := F) (A := F)
            ((ReedSolomon.code domain k : Set (ι → F)))
            δ.toNNReal δ.toNNReal).toReal ≤
          η * (1 / k - Fintype.card ι / (k * Fintype.card F))) : Prop :=
    Lambda ((ReedSolomon.code domain (k + 1) : Set (ι → F))) δ ≤
      (Nat.ceil
        ((Fintype.card F : ℝ) / (1 - η)
          * (epsCA (F := F) (A := F)
                ((ReedSolomon.code domain k : Set (ι → F)))
                δ.toNNReal δ.toNNReal).toReal) : ℕ∞)
  -- ABF26-T5.3; external statement [CS25 Thm 2].
  -- Missing ingredient: CS25's degree-lift list-size formula. The bound on Λ(C⁺,δ) for
  -- C⁺ = RS[F,L,k+1] in terms of ε_ca(C,δ) uses that a codeword of C⁺ δ-close to `w`
  -- restricts (mod the degree-k subcode C) to a near-codeword whose multiplicity is
  -- controlled by the CA error of C; the ⌈|F|/(1-η)·ε_ca⌉ count is the number of degree-(k+1)
  -- extensions surviving the η-margin. Needs: the RS degree-filtration C ⊂ C⁺ list map and
  -- the CS25 multiplicity bound (not in-tree; ReedSolomon.lean has the code but not the
  -- degree-lift list correspondence). Genuinely external.

/-- Prop-level wrapper for T5.3. -/
theorem rs_epsCA_implies_lambda_extended_cs25_of_residuals_prop
    (domain : ι ↪ F) (k : ℕ) (δ : ℝ) (η : ℝ)
    (hk_pos : 0 < k)
    (hδ_pos : 0 < δ)
    (hδ_min :
        (δ : ℝ) < Code.minDist ((ReedSolomon.code domain k : Set (ι → F)))
                    / Fintype.card ι)
    (hη_lo : 0 ≤ η) (hη_lt : η < 1)
    (hε_ca :
        (epsCA (F := F) (A := F)
            ((ReedSolomon.code domain k : Set (ι → F)))
            δ.toNNReal δ.toNNReal).toReal ≤
          η * (1 / k - Fintype.card ι / (k * Fintype.card F)))
    (hs_pos : (0 : ℝ) < Fintype.card F - Fintype.card ι)
    (hClaim3 :
        let ε := (epsCA (F := F) (A := F)
                    ((ReedSolomon.code domain k : Set (ι → F)))
                    δ.toNNReal δ.toNNReal).toReal
        let L0 : ℕ := Nat.ceil ((Fintype.card F : ℝ) / (1 - η) * ε)
        let s : ℝ := Fintype.card F - Fintype.card ι
        ¬ (Lambda ((ReedSolomon.code domain (k + 1) : Set (ι → F))) δ ≤ (L0 : ℕ∞)) →
          (L0 : ℝ) * s / ((L0 : ℝ) * k + s) < ε * Fintype.card F) :
    rs_epsCA_implies_lambda_extended_cs25 domain k δ η
      hk_pos hδ_pos hδ_min hη_lo hη_lt hε_ca :=
  rs_epsCA_implies_lambda_extended_cs25_of_residuals
    domain k δ η hk_pos hη_lo hη_lt hs_pos hε_ca hClaim3

end CAImpliesList

section ListVsCAseparation

/-- **ABF26 Theorem 5.4 [BGKS20 Lemma 3.3].** List decoding does **not** tightly imply CA.

For all fields `F` of characteristic 2, the Reed-Solomon code `C := RS[F, F, |F|/8]`
of rate `ρ = 1/8` (using `F` itself as the evaluation domain — a "full-domain" RS)
satisfies

  `ε_ca(C, 1 - ρ^{1/3}) ≥ 1 - 1/|F|` .

In particular `1 - ρ^{1/3} = 1 - (1/8)^{1/3} = 0.5`; the Johnson bound for the same
code sits at `1 - √ρ - η ≈ 0.55`, where the list size is `≈ 40` (constant in `|F|`).
This witnesses a code that is list-decodable at the Johnson radius yet has CA error
≈ 1 at a smaller radius — separating list decoding from CA in general.

The paper notes the also-true proximity-loss version: `ε_ca(C, δ_fld = 1 - ρ^{1/3},
δ_int = 1 - ρ^{2/3}) ≥ 1 - 1/|F|`. We state both. Admitted as an external result.

**HONEST REDUCTION AVAILABLE.** The conjunction packaging is fully proven, `sorry`-free and
axiom-clean, in `rs_epsCA_separation_bgks20_of_residuals`, which assembles the two BGKS20
lower bounds (`hMain`, `hLoss` — the genuine external content: the char-2 full-domain RS
bad-stack construction yielding `ε_ca ≥ 1 - 1/|F|` at radius `1 - ρ^{1/3}`).  These are
*lower* bounds on `ε_ca`; the trivial in-tree fact `ε_ca ≤ 1` (`Bridge.epsCA_le_one`) is the
wrong direction, so no in-tree machinery manufactures the bad stack — that needs BGKS20's
Frobenius/subfield construction. -/
theorem rs_epsCA_separation_bgks20_of_residuals
    {ι : Type} [Fintype ι] [Nonempty ι] [DecidableEq ι]
    {F : Type} [Field F] [Fintype F] [DecidableEq F] [CharP F 2]
    (_hF_eq_ι : Fintype.card F = Fintype.card ι)
    (_hF_ge : 8 ≤ Fintype.card F)
    (domain : ι ↪ F)
    -- BGKS20 Lemma 3.3 construction (the genuine external content): the two char-2
    -- full-domain RS lower bounds on `ε_ca`.
    (hMain :
        let k : ℕ := Fintype.card F / 8
        let ρ : ℝ := 1 / 8
        let C := ReedSolomon.code domain k
        (epsCA (F := F) (A := F) ((C : Set (ι → F)))
            ((1 - ρ ^ ((1 : ℝ) / 3)).toNNReal)
            ((1 - ρ ^ ((1 : ℝ) / 3)).toNNReal)) ≥
          ENNReal.ofReal (1 - 1 / Fintype.card F))
    (hLoss :
        let k : ℕ := Fintype.card F / 8
        let ρ : ℝ := 1 / 8
        let C := ReedSolomon.code domain k
        (epsCA (F := F) (A := F) ((C : Set (ι → F)))
            ((1 - ρ ^ ((1 : ℝ) / 3)).toNNReal)
            ((1 - ρ ^ ((2 : ℝ) / 3)).toNNReal)) ≥
          ENNReal.ofReal (1 - 1 / Fintype.card F)) :
    let k : ℕ := Fintype.card F / 8
    let ρ : ℝ := 1 / 8
    let C := ReedSolomon.code domain k
    (epsCA (F := F) (A := F) ((C : Set (ι → F)))
        ((1 - ρ ^ ((1 : ℝ) / 3)).toNNReal)
        ((1 - ρ ^ ((1 : ℝ) / 3)).toNNReal)) ≥
      ENNReal.ofReal (1 - 1 / Fintype.card F) ∧
    (epsCA (F := F) (A := F) ((C : Set (ι → F)))
        ((1 - ρ ^ ((1 : ℝ) / 3)).toNNReal)
        ((1 - ρ ^ ((2 : ℝ) / 3)).toNNReal)) ≥
      ENNReal.ofReal (1 - 1 / Fintype.card F) :=
  ⟨hMain, hLoss⟩

/-- **ABF26 Theorem 5.4 [BGKS20 Lemma 3.3].** List decoding does **not** tightly imply CA.
(External statement — see `rs_epsCA_separation_bgks20_of_residuals` for the fully-proven
honest reduction.) -/
def rs_epsCA_separation_bgks20
    {ι : Type} [Fintype ι] [Nonempty ι] [DecidableEq ι]
    {F : Type} [Field F] [Fintype F] [DecidableEq F] [CharP F 2]
    (_hF_eq_ι : Fintype.card F = Fintype.card ι)
    -- Without `|F| ≥ 8` the dimension `k = ⌊|F| / 8⌋` truncates to 0,
    -- giving the trivial code `{0}` for which the conclusion's
    -- `ε_ca(C, _) ≥ 1 - 1/|F|` is not the intended separation result.
    -- The paper implicitly assumes `|F|` large enough for a meaningful
    -- rate-`1/8` code; we surface that hypothesis explicitly.
    (_hF_ge : 8 ≤ Fintype.card F)
    (domain : ι ↪ F) : Prop :=
    let k : ℕ := Fintype.card F / 8
    let ρ : ℝ := 1 / 8
    let C := ReedSolomon.code domain k
    -- main statement
    (epsCA (F := F) (A := F) ((C : Set (ι → F)))
        ((1 - ρ ^ ((1 : ℝ) / 3)).toNNReal)
        ((1 - ρ ^ ((1 : ℝ) / 3)).toNNReal)) ≥
      ENNReal.ofReal (1 - 1 / Fintype.card F) ∧
    -- with proximity loss
    (epsCA (F := F) (A := F) ((C : Set (ι → F)))
        ((1 - ρ ^ ((1 : ℝ) / 3)).toNNReal)
        ((1 - ρ ^ ((2 : ℝ) / 3)).toNNReal)) ≥
      ENNReal.ofReal (1 - 1 / Fintype.card F)
  -- ABF26-T5.4; external statement [BGKS20 Lem 3.3].
  -- Missing ingredient: BGKS20's char-2 full-domain RS separation construction. The
  -- ε_ca ≥ 1-1/|F| LOWER bound at radius 1-ρ^{1/3} (ρ=1/8) requires exhibiting a stack
  -- (f₀,f₁) such that for all but one γ∈F the line f₀+γ·f₁ is (1-ρ^{1/3})-close to RS while
  -- (f₀,f₁) is NOT jointly close — i.e. a near-certain proximity-gap failure. The witness
  -- uses the char-2 Frobenius/subfield structure of RS[F,F,|F|/8] (BGKS20 §3.3). This is a
  -- code-CONSTRUCTION lower bound (the trivial `epsCA ≤ 1` gives the wrong direction); no
  -- in-tree machinery manufactures the bad stack. Genuinely external.

/-- Prop-level wrapper for T5.4. -/
theorem rs_epsCA_separation_bgks20_of_residuals_prop
    {ι : Type} [Fintype ι] [Nonempty ι] [DecidableEq ι]
    {F : Type} [Field F] [Fintype F] [DecidableEq F] [CharP F 2]
    (hF_eq_ι : Fintype.card F = Fintype.card ι)
    (hF_ge : 8 ≤ Fintype.card F)
    (domain : ι ↪ F)
    (hMain :
        let k : ℕ := Fintype.card F / 8
        let ρ : ℝ := 1 / 8
        let C := ReedSolomon.code domain k
        (epsCA (F := F) (A := F) ((C : Set (ι → F)))
            ((1 - ρ ^ ((1 : ℝ) / 3)).toNNReal)
            ((1 - ρ ^ ((1 : ℝ) / 3)).toNNReal)) ≥
          ENNReal.ofReal (1 - 1 / Fintype.card F))
    (hLoss :
        let k : ℕ := Fintype.card F / 8
        let ρ : ℝ := 1 / 8
        let C := ReedSolomon.code domain k
        (epsCA (F := F) (A := F) ((C : Set (ι → F)))
            ((1 - ρ ^ ((1 : ℝ) / 3)).toNNReal)
            ((1 - ρ ^ ((2 : ℝ) / 3)).toNNReal)) ≥
          ENNReal.ofReal (1 - 1 / Fintype.card F)) :
    rs_epsCA_separation_bgks20 hF_eq_ι hF_ge domain :=
  rs_epsCA_separation_bgks20_of_residuals hF_eq_ι hF_ge domain hMain hLoss

/-- **BGKS20 named-witness connector.**  This packages ABF26 T5.4 from the geometric
`NearCertainBadLine` residuals isolated in `ArkLib.ToMathlib.Bridge2BGKS20`.

The two remaining inputs are exactly the BGKS20 characteristic-2 constructions: one bad stack at
the main radius and one at the proximity-loss radius.  The bridge file proves the conversion from
each witness to the corresponding `ε_ca ≥ 1 - 1/|F|` lower bound. -/
theorem rs_epsCA_separation_bgks20_of_nearCertainBadLines
    {ι : Type} [Fintype ι] [Nonempty ι] [DecidableEq ι]
    {F : Type} [Field F] [Fintype F] [DecidableEq F] [CharP F 2]
    (hF_eq_ι : Fintype.card F = Fintype.card ι)
    (hF_ge : 8 ≤ Fintype.card F)
    (domain : ι ↪ F)
    (hMainWitness :
        let k : ℕ := Fintype.card F / 8
        let ρ : ℝ := 1 / 8
        let C := ReedSolomon.code domain k
        Bridge.NearCertainBadLine (F := F) ((C : Set (ι → F)))
          ((1 - ρ ^ ((1 : ℝ) / 3)).toNNReal)
          ((1 - ρ ^ ((1 : ℝ) / 3)).toNNReal))
    (hLossWitness :
        let k : ℕ := Fintype.card F / 8
        let ρ : ℝ := 1 / 8
        let C := ReedSolomon.code domain k
        Bridge.NearCertainBadLine (F := F) ((C : Set (ι → F)))
          ((1 - ρ ^ ((1 : ℝ) / 3)).toNNReal)
          ((1 - ρ ^ ((2 : ℝ) / 3)).toNNReal)) :
    rs_epsCA_separation_bgks20 hF_eq_ι hF_ge domain :=
  rs_epsCA_separation_bgks20_of_residuals hF_eq_ι hF_ge domain
    (Bridge.epsCA_separation_bridge_of_residual
      (F := F) ((ReedSolomon.code domain (Fintype.card F / 8) : Set (ι → F)))
      ((1 - ((1 : ℝ) / 8) ^ ((1 : ℝ) / 3)).toNNReal)
      ((1 - ((1 : ℝ) / 8) ^ ((1 : ℝ) / 3)).toNNReal)
      hMainWitness)
    (Bridge.epsCA_separation_bridge_of_residual
      (F := F) ((ReedSolomon.code domain (Fintype.card F / 8) : Set (ι → F)))
      ((1 - ((1 : ℝ) / 8) ^ ((1 : ℝ) / 3)).toNNReal)
      ((1 - ((1 : ℝ) / 8) ^ ((2 : ℝ) / 3)).toNNReal)
      hLossWitness)

end ListVsCAseparation

end CodingTheory

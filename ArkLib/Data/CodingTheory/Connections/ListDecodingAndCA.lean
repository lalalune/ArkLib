/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexander Hicks
-/

import ArkLib.Data.CodingTheory.ProximityGap.Errors
import ArkLib.Data.CodingTheory.ListDecodability
import ArkLib.Data.CodingTheory.ReedSolomon
import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# Connections between list decoding and correlated agreement (ABF26 §5)

External-admit *statements* for the §5 theorems that link list-size bounds to
correlated-agreement error bounds and vice versa. From ABF26 (Arnon-Boneh-Fenzi,
*Open Problems in List Decoding and Correlated Agreement*, 2026), §5.

These four theorems directly bridge the Grand List Decoding Challenge and the
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

Admitted as an external result. -/
theorem linear_listSize_to_epsMCA_gcxk25
    (C : LinearCode ι F) (L : ℕ) (δ η : ℝ)
    (_hδ_pos : 0 < δ) (_hδ_lt : δ < 1)
    (_hη_pos : 0 < η) (_hη_lt : η < 1) (_hη_le_δ : η ≤ δ)
    (_hΛ : Lambda ((C : Set (ι → F))) δ ≤ (L : ℕ∞)) :
    epsMCA (F := F) (A := F) ((C : Set (ι → F)))
        ((1 - (1 - δ + η) ^ ((1 : ℝ) / 2)).toNNReal) ≤
      ENNReal.ofReal
        (((L : ℝ) ^ 2 * δ * Fintype.card ι + 1 / η) / Fintype.card F) := by
  sorry -- ABF26-T5.1; external admit [GCXK25 Thm 3].
  -- Missing ingredient: the GCXK25 list-decoding→MCA amplification. GCXK25 (eprint 2025/870)
  -- partition the bad combining points into `Bad¹` (count `≤ p·n`, their Cor 2 via the GKL24
  -- agree-domain intersection Lemma 1/Cor 1) and `Bad²` (count `< 1/ε`, their Lemma 3, a
  -- second-moment Cauchy–Schwarz count over the δ-agreement domains); together with the
  -- `l ≤ L²` list-size factor this gives the `L²·δ·n + 1/η` shape, divided by |F|.
  --
  -- VERIFIED BACKBONE: the GCXK25 Lemma 3 `Bad² < 1/ε` second-moment count is now formalized
  -- kernel-clean in `ProximityGap/GCXK25SecondMoment.lean`
  -- (`GCXK25SecondMoment.card_lt_inv_of_second_moment_rs`, with the abstract master inequality
  -- `card_le_of_second_moment` and the Cauchy–Schwarz step
  -- `sq_sum_card_le_card_mul_sum_sum_card_inter`). Its `ε ≤ p` hypothesis is exactly the
  -- `η ≤ δ` constraint imposed above.
  --
  -- STILL EXTERNAL (not in-tree): (i) the GKL24 maximal-correlated-agree-domain machinery
  -- and the `Bad¹ ≤ pn` per-domain count (the `Bad`-set / `A_{δ,{π₁,π₂},C}` structure is not
  -- connected to `Lambda`/`epsMCA`); and (ii) the reduction from `epsMCA` — a supremum over
  -- ARBITRARY word stacks `u` with the single-witness-set `mcaEvent` (ABF26 Def 4.3) — to
  -- GCXK25's per-CODEWORD-PAIR `Bad(π₁,π₂,δ)` count (the content of ABF26 §5). Genuinely
  -- external pending those two pieces.

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
external result. -/
theorem rs_epsCA_small_implies_lambda_lt_F_bchks25
    (domain : ι ↪ F) (k : ℕ) (δ : ℝ)
    (_hδ_pos : 0 < δ)
    (_hδ_lt : (δ : ℝ) < 1 - (k : ℝ) / Fintype.card ι)
    (_hε_ca :
        epsCA (F := F) (A := F)
            ((ReedSolomon.code domain k : Set (ι → F)))
            ((δ + 2 / Fintype.card ι).toNNReal)
            ((1 - (k : ℝ) / Fintype.card ι - 1 / Fintype.card ι).toNNReal) <
          ENNReal.ofReal (1 / (2 * Fintype.card ι))) :
    Lambda ((ReedSolomon.code domain k : Set (ι → F))) δ < (Fintype.card F : ℕ∞) := by
  sorry -- ABF26-T5.2; external admit [BCHKS25 Thm 1.9].
  -- Missing ingredient: BCHKS25's CA→list contrapositive for RS. The proof negates
  -- `|Λ(C,δ)| ≥ |F|`: if ≥|F| codewords are δ-close to some `w`, an averaging/interpolation
  -- argument over the |F| affine shifts produces a line `w + γ·v` that is δ_fld-close on a
  -- (1-δ_fld)-fraction for ≥ 1/(2n)·|F| values of γ while the pair fails δ_int-joint-proximity,
  -- forcing `epsCA(δ_fld=δ+2/n, δ_int=1-ρ-1/n) ≥ 1/(2n)`. This requires the RS-specific
  -- interpolation lemma (BCKHS25/Interpolation.lean has the collinear-proximates engine but
  -- not the |F|-codewords⇒bad-line counting). Genuinely external.

/-- **ABF26 Theorem 5.3 [CS25 Theorem 2].** CA error converts to list size for related RS.

Let `C := RS[F, L, k]` and `C⁺ := RS[F, L, k+1]` be Reed-Solomon codes with `|L| = n`.
For `δ ∈ (0, δ_min(C))` and `η ∈ [0, 1)`, if

  `ε_ca(C, δ) ≤ η · (1/k - n/(k·|F|))`

then

  `|Λ(C⁺, δ)| ≤ ⌈|F|/(1-η) · ε_ca(C, δ)⌉`

Pivots CA on `C` to a list-size bound on the extended code `C⁺`. Admitted as an
external result. -/
theorem rs_epsCA_implies_lambda_extended_cs25
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
          η * (1 / k - Fintype.card ι / (k * Fintype.card F))) :
    Lambda ((ReedSolomon.code domain (k + 1) : Set (ι → F))) δ ≤
      (Nat.ceil
        ((Fintype.card F : ℝ) / (1 - η)
          * (epsCA (F := F) (A := F)
                ((ReedSolomon.code domain k : Set (ι → F)))
                δ.toNNReal δ.toNNReal).toReal) : ℕ∞) := by
  sorry -- ABF26-T5.3; external admit [CS25 Thm 2].
  -- Missing ingredient: CS25's degree-lift list-size formula. The bound on Λ(C⁺,δ) for
  -- C⁺ = RS[F,L,k+1] in terms of ε_ca(C,δ) uses that a codeword of C⁺ δ-close to `w`
  -- restricts (mod the degree-k subcode C) to a near-codeword whose multiplicity is
  -- controlled by the CA error of C; the ⌈|F|/(1-η)·ε_ca⌉ count is the number of degree-(k+1)
  -- extensions surviving the η-margin. Needs: the RS degree-filtration C ⊂ C⁺ list map and
  -- the CS25 multiplicity bound (not in-tree; ReedSolomon.lean has the code but not the
  -- degree-lift list correspondence). Genuinely external.

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
δ_int = 1 - ρ^{2/3}) ≥ 1 - 1/|F|`. We state both. Admitted as an external result. -/
theorem rs_epsCA_separation_bgks20
    {ι : Type} [Fintype ι] [Nonempty ι] [DecidableEq ι]
    {F : Type} [Field F] [Fintype F] [DecidableEq F] [CharP F 2]
    (_hF_eq_ι : Fintype.card F = Fintype.card ι)
    -- Without `|F| ≥ 8` the dimension `k = ⌊|F| / 8⌋` truncates to 0,
    -- giving the trivial code `{0}` for which the conclusion's
    -- `ε_ca(C, _) ≥ 1 - 1/|F|` is not the intended separation result.
    -- The paper implicitly assumes `|F|` large enough for a meaningful
    -- rate-`1/8` code; we surface that hypothesis explicitly.
    (_hF_ge : 8 ≤ Fintype.card F)
    (domain : ι ↪ F) :
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
      ENNReal.ofReal (1 - 1 / Fintype.card F) := by
  sorry -- ABF26-T5.4; external admit [BGKS20 Lem 3.3].
  -- Missing ingredient: BGKS20's char-2 full-domain RS separation construction. The
  -- ε_ca ≥ 1-1/|F| LOWER bound at radius 1-ρ^{1/3} (ρ=1/8) requires exhibiting a stack
  -- (f₀,f₁) such that for all but one γ∈F the line f₀+γ·f₁ is (1-ρ^{1/3})-close to RS while
  -- (f₀,f₁) is NOT jointly close — i.e. a near-certain proximity-gap failure. The witness
  -- uses the char-2 Frobenius/subfield structure of RS[F,F,|F|/8] (BGKS20 §3.3). This is a
  -- code-CONSTRUCTION lower bound (the trivial `epsCA ≤ 1` gives the wrong direction); no
  -- in-tree machinery manufactures the bad stack. Genuinely external.

end ListVsCAseparation

end CodingTheory

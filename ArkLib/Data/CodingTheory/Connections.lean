/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexander Hicks
-/

import ArkLib.Data.CodingTheory.ProximityGap.EpsilonErrors
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

**Implicit hypothesis `η ≤ δ`.** For the conclusion's proximity radius
`1 - √(1 - δ + η)` to be a valid relative distance in `[0, 1]` we need
`1 - δ + η ≤ 1`, i.e. `η ≤ δ`. The paper's `δ, η ∈ (0, 1)` regime does not force
this; without it `(1 - √…).toNNReal` would silently truncate to `0` and the
statement would collapse. We add `η ≤ δ` explicitly to match the paper's intent.

Admitted as an external result. -/
theorem linear_listSize_to_epsMCA_gcxk25
    (C : Submodule F (ι → F)) (L : ℕ) (δ η : ℝ)
    (_hδ_pos : 0 < δ) (_hδ_lt : δ < 1)
    (_hη_pos : 0 < η) (_hη_lt : η < 1) (_hη_le_δ : η ≤ δ)
    (_hΛ : Lambda ((C : Set (ι → F))) δ ≤ (L : ℕ∞)) :
    epsMCA (F := F) (A := F) ((C : Set (ι → F)))
        ((1 - (1 - δ + η) ^ ((1 : ℝ) / 2)).toNNReal) ≤
      ENNReal.ofReal
        (((L : ℝ) ^ 2 * δ * Fintype.card ι + 1 / η) / Fintype.card F) := by
  sorry -- ABF26-T5.1; external admit [GCXK25 Thm 3].

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

end ListVsCAseparation

end CodingTheory

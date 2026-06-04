/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexander Hicks
-/

import ArkLib.Data.CodingTheory.ProximityGap.Errors

/-!
# Line decoding (ABF26 §4.4)

Line decoding is a structural strengthening of list decoding that lifts a fiberwise
"line is close to *some* codeword" statement into an aligned "line is close to a *single*
affine pair `u₁ + γ·u₂`". Definition 4.20 of *Open Problems in List Decoding and Correlated
Agreement* (Arnon, Boneh, Fenzi; April 8, 2026) formalises this; the immediate downstream
fact is Theorem 4.21, which converts a line-decoding bound into a mutual correlated
agreement (MCA) bound.

## Main definitions

- `CodingTheory.LineDecodable` — ABF26 Definition 4.20: `(δ, a, b)`-line-decodability of
  an `F`-additive code `C`.

## Main statements

- `CodingTheory.lineDecodable_imp_epsMCA_le` — ABF26 Theorem 4.21 [GG25 Thm 3.5]:
  `(δ, a, n+1)`-line-decodability gives an MCA bound `ε_mca(C, δ) ≤ a / |F|`.
  Admitted as an external result; the proof in GG25 routes through the line-decoder's
  alignment guarantee and a `Δ_S = 0`-witness argument.

## References

- [ABF26] Arnon, Boneh, Fenzi. *Open Problems in List Decoding and Correlated Agreement*.
  2026. §4.4.
- [GG25] Guo, Gerbush. Definition 3.1 / Theorem 3.5 (original source).
-/

set_option linter.unusedFintypeInType false
set_option linter.unusedDecidableInType false
set_option linter.unusedSectionVars false

namespace CodingTheory

open scoped NNReal ProbabilityTheory
open ProximityGap

section

variable {ι : Type} [Fintype ι] [Nonempty ι] [DecidableEq ι]
variable {F : Type} [Field F] [Fintype F] [DecidableEq F]
variable {A : Type} [Fintype A] [DecidableEq A] [AddCommGroup A] [Module F A]

open Classical in
/-- **ABF26 Definition 4.20 [GG25 Def 3.1].** A code `C ⊆ A^ι` is `(δ, a, b)`-**line-decodable**
when every `γ`-indexed family of codewords that aligns with a random line `f₁ + γ·f₂` on at
least an `a/|F|` fraction of `γ`'s is itself induced (on at least a `b/|F|` fraction of `γ`'s)
by a single affine pair `(u₁, u₂)` of codewords.

In formula:

  `∀ f₁ f₂ : ι → A, ∀ U : F → ι → A, (∀ γ, U γ ∈ C) →`
  `  Pr_γ [δᵣ(f₁ + γ • f₂, U γ) ≤ δ] ≥ a / |F| →`
  `  ∃ u₁ u₂ ∈ C, Pr_γ [U γ = u₁ + γ • u₂] ≥ b / |F|`

The hypothesis pins each `U γ` inside `C`; ABF26 writes this as `U : F → C` but Lean is
cleaner with a function into the ambient space plus a side condition. The probabilities
are read in `ENNReal`, matching the convention in
[`ProximityGap.Errors`](ProximityGap.Errors.lean). -/
def LineDecodable (C : Set (ι → A)) (δ : ℝ≥0) (a b : ℝ≥0) : Prop :=
  ∀ f₁ f₂ : ι → A, ∀ U : F → ι → A, (∀ γ : F, U γ ∈ C) →
    (a : ENNReal) / (Fintype.card F : ENNReal)
        ≤ Pr_{let γ ← $ᵖ F}[δᵣ(f₁ + γ • f₂, U γ) ≤ δ] →
    ∃ u₁ ∈ C, ∃ u₂ ∈ C,
      (b : ENNReal) / (Fintype.card F : ENNReal)
          ≤ Pr_{let γ ← $ᵖ F}[U γ = u₁ + γ • u₂]

/-- **ABF26 Theorem 4.21 [GG25 Thm 3.5].** If `C` is `(δ, a, n+1)`-line-decodable, then its
mutual correlated agreement error is bounded by `a / |F|`:

  `LineDecodable (F := F) C δ a (n+1) → ε_mca(C, δ) ≤ a / |F|`

where `n = |ι|`. The proof in [GG25] proceeds by taking the line-decoder's witness
pair `(u₁, u₂)` and showing that the `Δ_S = 0` witness set of the MCA event must coincide
with the `γ`-set on which `U γ = u₁ + γ • u₂`, which has measure `≥ (n+1)/|F|`. Because
that pair has at most `n` exceptional positions on every fold, the alignment lifts to a
joint-pair witness, contradicting the `¬ pairJointAgreesOn` clause of `mcaEvent` when the
fraction of γ-aligned points exceeds `n/|F|`.

The statement is reduced here, via `iSup_le`, to the **per-stack** bound
`Pr_γ[mcaEvent C δ (u 0) (u 1) γ] ≤ a / |F|` for every word stack `u`. This is exactly the
core of [GG25 Thm 3.5]: fix `f₁ := u 0`, `f₂ := u 1` and, on the `γ`-set where `mcaEvent`
fires, let `U γ` be the codeword `w_γ` that the event provides agreeing with the line on a
size-`≥(1-δ)n` set (so `δᵣ(f₁ + γ·f₂, U γ) ≤ δ` there; cf.
`ProximityGap.mcaEvent_imp_relCloseToCode`). If `Pr_γ[mcaEvent] > a/|F|` then the line-close
probability exceeds `a/|F|`, so line-decodability yields a single affine pair `(u₁, u₂)` with
`Pr_γ[U γ = u₁ + γ·u₂] ≥ (n+1)/|F|`; picking two distinct aligned `γ` whose witness sets
overlap in `> n` positions forces `u₁`/`u₂` to agree with `f₁`/`f₂` on that overlap, a
`pairJointAgreesOn` witness contradicting `mcaEvent`'s `¬ pairJointAgreesOn` clause. This
counting/extraction step is the external [GG25] content.

Admitted as an external result; formalising the GG25 per-stack argument is tracked separately. -/
theorem lineDecodable_imp_epsMCA_le
    (C : ModuleCode ι F A) (δ : ℝ≥0) (a : ℝ≥0)
    (_h : LineDecodable (F := F) ((C : Set (ι → A))) δ a
            ((Fintype.card ι : ℝ≥0) + 1)) :
    epsMCA (F := F) (A := A) ((C : Set (ι → A))) δ
        ≤ (a : ENNReal) / (Fintype.card F : ENNReal) := by
  -- Reduce to the per-stack bound `Pr_γ[mcaEvent] ≤ a/|F|` (the GG25 core).
  unfold epsMCA
  refine iSup_le fun u ↦ ?_
  -- Per-stack `γ`-probability bound from line-decodability (external [GG25 Thm 3.5]).
  sorry -- ABF26-T4.21 (per-stack `Pr_γ[mcaEvent] ≤ a/|F|`); external admit [GG25 Thm 3.5].

end

end CodingTheory

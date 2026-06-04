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

## Status (2026-06): U-construction realised in-tree; residual is the multi-γ coverage count

The statement is reduced here, via `iSup_le`, to the **per-stack** bound
`Pr_γ[mcaEvent C δ (u 0) (u 1) γ] ≤ a / |F|` for every word stack `u`, then attacked by
contradiction. The **GG25 U-construction is now fully formalised in-tree** (no longer a
black-box): fixing `f₁ := u 0`, `f₂ := u 1`, the proof builds
`U : F → ι → A`, `U γ := if mcaEvent fires then the event's witness codeword `w_γ` else `0``
(`0 ∈ C` as `C` is a submodule), proves `∀ γ, U γ ∈ C` (`hU_mem`) and that on the
`mcaEvent`-set the line is `δ`-close to `U γ` (`hU_close`, agreement on the size-`≥(1-δ)n`
witness set `S_γ`; cf. `ProximityGap.mcaEvent_imp_relCloseToCode`). Under the negated goal
`Pr_γ[mcaEvent] > a/|F|`, event-domination (`Pr_le_Pr_of_implies`) lifts this to
`a/|F| ≤ Pr_γ[δᵣ(f₁+γ·f₂, U γ) ≤ δ]`, so **line-decodability fires in-tree** and yields a
single affine pair `(u₁, u₂) ∈ C` with `Pr_γ[U γ = u₁ + γ·u₂] ≥ (n+1)/|F|`.

**Residual (the only remaining `sorry`): the GG25 multi-γ overlap/coverage extraction.**
The aligned set `G := {γ : U γ = u₁ + γ·u₂}` has `> n` elements. For `γ ∈ G` with `mcaEvent`
firing, `U γ = w_γ` agrees with the line on `S_γ`, so the affine-in-γ word
`D(γ) := (u₁ - f₁) + γ·(u₂ - f₂)` vanishes on `S_γ`. To contradict `¬ pairJointAgreesOn C
S_{γ₀} f₁ f₂` for a fixed bad `γ₀` one must show `(u₁, u₂)` agrees with `(f₁, f₂)` on **all**
of `S_{γ₀}`, i.e. for **every** `i ∈ S_{γ₀}` a *second* aligned-mcaEvent `γ ≠ γ₀` with
`i ∈ S_γ` (two zeros of the affine `g_i(γ) := (u₁-f₁) i + γ·(u₂-f₂) i` pin `u₁ i = f₁ i`,
`u₂ i = f₂ i`). Note `pairJointAgreesOn` is **antitone** in `S`, so the easy 2-γ argument —
which only yields agreement on the *intersection* `S_γ ∩ S_{γ'} ⊆ S_{γ₀}` — does **not**
contradict `¬ pairJointAgreesOn` on the larger `S_{γ₀}` (wrong direction). The genuine GG25
content is the counting that `> n` aligned points force per-position double-coverage of
`S_{γ₀}` (each `S_γ` misses `≤ δn` positions; the `n+1`-point budget closes the cover). This
coupling of the line-decode alignment set `G` with the per-γ `mcaEvent` witness sets is the
external [GG25 Thm 3.5] combinatorics and is the sole residual admit (the unique-decoding
restriction does not shortcut it: under UDR the close codeword is unique, forcing
`u₁+γ·u₂ = w_γ`, but the antitone-`S` obstruction above is unchanged).

Admitted residual: the GG25 multi-γ coverage count; the U-construction reduction above is
machine-checked. -/
theorem lineDecodable_imp_epsMCA_le
    (C : ModuleCode ι F A) (δ : ℝ≥0) (a : ℝ≥0)
    (h : LineDecodable (F := F) ((C : Set (ι → A))) δ a
            ((Fintype.card ι : ℝ≥0) + 1)) :
    epsMCA (F := F) (A := A) ((C : Set (ι → A))) δ
        ≤ (a : ENNReal) / (Fintype.card F : ENNReal) := by
  classical
  -- Reduce to the per-stack bound `Pr_γ[mcaEvent] ≤ a/|F|` (the GG25 core).
  unfold epsMCA
  refine iSup_le fun u ↦ ?_
  -- Per-stack: contrapositive. Suppose `Pr_γ[mcaEvent] > a/|F|` and derive a contradiction
  -- by feeding the `mcaEvent`-witness codewords into line-decodability (the GG25 U-construction).
  by_contra hgt
  push Not at hgt
  -- `f₁ := u 0`, `f₂ := u 1`.
  set f₁ := u 0 with hf₁
  set f₂ := u 1 with hf₂
  -- The U-construction: for each `γ`, pick the `mcaEvent`-witness codeword if the event fires,
  -- else the zero codeword (`0 ∈ C` as `C` is a submodule).
  have hzeroC : (0 : ι → A) ∈ (C : Set (ι → A)) := C.zero_mem
  set U : F → ι → A := fun γ =>
    if hev : mcaEvent (F := F) ((C : Set (ι → A))) δ f₁ f₂ γ
      then hev.choose_spec.2.1.choose
      else 0 with hU_def
  -- Every `U γ` is a codeword.
  have hU_mem : ∀ γ : F, U γ ∈ (C : Set (ι → A)) := by
    intro γ
    by_cases hev : mcaEvent (F := F) ((C : Set (ι → A))) δ f₁ f₂ γ
    · simp only [hU_def, dif_pos hev]
      exact hev.choose_spec.2.1.choose_spec.1
    · simp only [hU_def, dif_neg hev]; exact hzeroC
  -- On the `mcaEvent`-set, the line is `δ`-close to `U γ` (the chosen witness codeword agrees
  -- with the line on the size-`≥(1-δ)n` set `S_γ`).
  have hU_close : ∀ γ : F, mcaEvent (F := F) ((C : Set (ι → A))) δ f₁ f₂ γ →
      δᵣ(f₁ + γ • f₂, U γ) ≤ δ := by
    intro γ hev
    -- `U γ = (hev.choose_spec.2.1).choose`, the event's witness codeword.
    have hUγ : U γ = hev.choose_spec.2.1.choose := by
      simp only [hU_def, dif_pos hev]
    -- The event's witness set `S = hev.choose` carries this codeword agreeing with the line.
    obtain ⟨hS_card, hw, _hpair⟩ := hev.choose_spec
    obtain ⟨_hwC, hw_eq⟩ := hw.choose_spec
    rw [hUγ, Code.relCloseToWord_iff_exists_agreementCols]
    refine ⟨hev.choose,
      (Code.relDist_floor_bound_iff_complement_bound _ _ _).mpr hev.choose_spec.1, ?_⟩
    intro j
    refine ⟨fun hj ↦ ?_, fun hne hj ↦ ?_⟩
    · simpa [Pi.add_apply, Pi.smul_apply] using (hw_eq j hj).symm
    · exact hne (by simpa [Pi.add_apply, Pi.smul_apply] using (hw_eq j hj).symm)
  -- The line-close event dominates the `mcaEvent` event, so its probability exceeds `a/|F|`.
  have hPr_close : (a : ENNReal) / (Fintype.card F : ENNReal)
      ≤ Pr_{let γ ← $ᵖ F}[δᵣ(f₁ + γ • f₂, U γ) ≤ δ] := by
    refine le_trans (le_of_lt hgt) ?_
    refine Pr_le_Pr_of_implies ($ᵖ F) _ _ ?_
    intro γ hev; exact hU_close γ hev
  -- Apply line-decodability: get the aligned affine pair `(u₁, u₂)`.
  obtain ⟨u₁, hu₁C, u₂, hu₂C, hPr_align⟩ := h f₁ f₂ U hU_mem hPr_close
  -- `Pr_γ[U γ = u₁ + γ • u₂] ≥ (n+1)/|F|`, so the aligned set has `> n` elements.
  -- The GG25 two-γ / multi-γ overlap extraction: among the `≥ n+1` aligned `γ`'s, two whose
  -- `mcaEvent` witness sets jointly cover some `S_γ₀` force `pairJointAgreesOn C S_γ₀ f₁ f₂`,
  -- contradicting the `¬ pairJointAgreesOn` clause of `mcaEvent`.
  sorry -- ABF26-T4.21 (GG25 multi-γ overlap extraction); residual after the U-construction.

end

end CodingTheory

/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/

import Mathlib.LinearAlgebra.Span.Basic
import Mathlib.Algebra.Module.Submodule.Basic
import Mathlib.Algebra.Module.Pi
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring
import Mathlib.Tactic.LinearCombination
import ArkLib.Data.CodingTheory.InterleavedCode

/-!
# Two-line correlated-agreement extraction (proximity gap, linear codes)

The genuinely-linear-algebraic core of the affine-line correlated-agreement / proximity-gap
argument for **linear** codes: if two distinct scalars `z ≠ z'` both make the affine-line word
`u₀ + z • u₁` agree with a codeword (`w` on `S`, `w'` on `S'`), then `u₀` and `u₁` *themselves*
agree with codewords on the common set `S ∩ S'`.

Concretely, on `S ∩ S'` the difference `w − w' = (z − z') • u₁`, so

  `v₁ := (z − z')⁻¹ • (w − w') ∈ C`   and   `v₀ := w − z • v₁ ∈ C`

are codewords (by `Submodule` closure) with `v₁ = u₁` and `v₀ = u₀` on `S ∩ S'`.

This is the step that turns "many points of the line are close to the code" into "the pair is
jointly close": at radius `δ` each `w, w'` agrees on `≥ (1−δ)n` coordinates, so `S ∩ S'` has size
`≥ (1−2δ)n` and the pair is jointly `2δ`-close.  (Closing the factor-2 gap to the genuine radius `δ`
is the BCIKS20 *curve* argument — the codewords must be shown affine-linear in `z` — and is left to
that development; this lemma supplies the linear-extraction half unconditionally.)
-/

namespace ProximityGap

open Finset Code
open scoped NNReal

variable {ι : Type*} [DecidableEq ι] {F : Type*} [Field F]

/-- **Two-line linear extraction.**  For a linear code `C` (a submodule), if codewords `w, w'`
agree with the affine-line words `u₀ + z • u₁` and `u₀ + z' • u₁` on `S` and `S'` respectively
(with `z ≠ z'`), then there are codewords `v₀, v₁ ∈ C` agreeing with `u₀` and `u₁` on `S ∩ S'`. -/
theorem exists_joint_codewords_of_two_lines
    (C : Submodule F (ι → F)) {u₀ u₁ : ι → F} {z z' : F} (hzz' : z ≠ z')
    {w w' : ι → F} (hw : w ∈ C) (hw' : w' ∈ C) {S S' : Finset ι}
    (hwS : ∀ i ∈ S, w i = u₀ i + z • u₁ i)
    (hw'S : ∀ i ∈ S', w' i = u₀ i + z' • u₁ i) :
    ∃ v₀ ∈ C, ∃ v₁ ∈ C, ∀ i ∈ S ∩ S', v₀ i = u₀ i ∧ v₁ i = u₁ i := by
  set v₁ : ι → F := (z - z')⁻¹ • (w - w') with hv₁def
  set v₀ : ι → F := w - z • v₁ with hv₀def
  have hsub : z - z' ≠ 0 := sub_ne_zero.mpr hzz'
  have hv₁mem : v₁ ∈ C := C.smul_mem _ (C.sub_mem hw hw')
  have hv₀mem : v₀ ∈ C := C.sub_mem hw (C.smul_mem z hv₁mem)
  refine ⟨v₀, hv₀mem, v₁, hv₁mem, ?_⟩
  intro i hi
  rw [Finset.mem_inter] at hi
  have e1 : w i = u₀ i + z * u₁ i := by simpa [smul_eq_mul] using hwS i hi.1
  have e2 : w' i = u₀ i + z' * u₁ i := by simpa [smul_eq_mul] using hw'S i hi.2
  -- on `S ∩ S'`, `w i - w' i = (z - z') u₁ i`
  have hwdiff : w i - w' i = (z - z') * u₁ i := by rw [e1, e2]; ring
  -- v₁ i = (z - z')⁻¹ (w i - w' i) = (z - z')⁻¹ (z - z') u₁ i = u₁ i
  have hv₁i : v₁ i = u₁ i := by
    simp only [hv₁def, Pi.smul_apply, Pi.sub_apply, smul_eq_mul]
    rw [hwdiff, inv_mul_cancel_left₀ hsub]
  -- v₀ i = w i - z · v₁ i = (u₀ i + z u₁ i) - z u₁ i = u₀ i
  have hv₀i : v₀ i = u₀ i := by
    simp only [hv₀def, Pi.sub_apply, Pi.smul_apply, smul_eq_mul, hv₁i, e1]
    ring
  exact ⟨hv₀i, hv₁i⟩

section JointAgreement

variable [Fintype ι] [DecidableEq F]

/-- **Two-line radius-`2δ` correlated agreement (complete proof chain).**  If two distinct scalars
`z ≠ z'` each make the affine-line word agree with a codeword on a set of size `≥ (1-δ)·n`, then the
pair `(u₀, u₁)` is jointly `2δ`-close to the linear code `C`: there are codewords matching `u₀` and
`u₁` on the common set, of size `≥ (1-2δ)·n`.  Combines the linear extraction with the
inclusion–exclusion overlap bound. -/
theorem jointAgreement_two_delta_of_two_lines
    (C : Submodule F (ι → F)) (δ : ℝ≥0) {u₀ u₁ : ι → F} {z z' : F} (hzz' : z ≠ z')
    {w w' : ι → F} (hw : w ∈ C) (hw' : w' ∈ C) {S S' : Finset ι}
    (hwS : ∀ i ∈ S, w i = u₀ i + z • u₁ i)
    (hw'S : ∀ i ∈ S', w' i = u₀ i + z' • u₁ i)
    (hScard : ((1 : ℝ) - δ) * Fintype.card ι ≤ (S.card : ℝ))
    (hS'card : ((1 : ℝ) - δ) * Fintype.card ι ≤ (S'.card : ℝ)) :
    Code.jointAgreement (↑C : Set (ι → F)) (2 * δ) (![u₀, u₁] : Fin 2 → ι → F) := by
  classical
  obtain ⟨v₀, hv₀C, v₁, hv₁C, hagree⟩ :=
    exists_joint_codewords_of_two_lines C hzz' hw hw' hwS hw'S
  refine ⟨S ∩ S', ?_, ![v₀, v₁], ?_⟩
  · -- |S ∩ S'| ≥ (1 - 2δ)·n  from inclusion–exclusion and |S∪S'| ≤ n
    have hie : (S ∩ S').card + (S ∪ S').card = S.card + S'.card :=
      Finset.card_inter_add_card_union S S'
    have hunion : (S ∪ S').card ≤ Fintype.card ι := Finset.card_le_univ _
    have hieR : ((S ∩ S').card : ℝ) + (S ∪ S').card = S.card + S'.card := by exact_mod_cast hie
    have hunionR : ((S ∪ S').card : ℝ) ≤ Fintype.card ι := by exact_mod_cast hunion
    -- real lower bound `(1 - 2δ)·n ≤ |S ∩ S'|`
    have hreal : ((1 : ℝ) - 2 * δ) * Fintype.card ι ≤ ((S ∩ S').card : ℝ) := by nlinarith
    -- cast the `jointAgreement` NNReal goal `(1 - 2δ)·n ≤ |S ∩ S'|` through ℝ
    have hgoal : ((1 - 2 * δ : ℝ≥0) : ℝ) * Fintype.card ι ≤ ((S ∩ S').card : ℝ) := by
      rcases le_total (2 * δ) 1 with hle | hge
      · have : ((1 - 2 * δ : ℝ≥0) : ℝ) = 1 - 2 * (δ : ℝ) := by
          rw [NNReal.coe_sub hle]; push_cast; ring
        rw [this]; exact hreal
      · have : ((1 - 2 * δ : ℝ≥0) : ℝ) = 0 := by
          rw [NNReal.coe_eq_zero]; exact tsub_eq_zero_of_le hge
        rw [this, zero_mul]; positivity
    have : ((1 - 2 * δ : ℝ≥0) * Fintype.card ι : ℝ≥0) ≤ ((S ∩ S').card : ℝ≥0) := by
      rw [← NNReal.coe_le_coe]; push_cast; exact hgoal
    exact_mod_cast this
  · -- the two codewords match `u₀`, `u₁` on `S ∩ S'`
    intro k
    fin_cases k
    · refine ⟨hv₀C, ?_⟩
      intro j hj
      simpa using (hagree j hj).1
    · refine ⟨hv₁C, ?_⟩
      intro j hj
      simpa using (hagree j hj).2

end JointAgreement

/-! ### Toward the genuine radius `δ`: the many-points linearity argument

The factor-2 loss above comes from intersecting just two agreement sets.  If instead the affine-line
words agree with a *fixed* codeword pair `(v₀, v₁)` — the BCIKS20 "curve" hypothesis, available in
the unique-decoding regime where the close codeword is unique and hence affine-linear in the
combining scalar — then agreement can be read off **coordinate by coordinate**, and a single
coordinate seen by two distinct scalars already pins both `u₀` and `u₁` there.  Aggregating over many
close scalars drives the joint-agreement radius from `2δ` back toward `δ`. -/

/-- **Per-coordinate linearity.**  If at coordinate `i` the affine-line word agrees with the fixed
codeword line `v₀ + z • v₁` for two distinct scalars `z ≠ z'`, then `u₀` and `u₁` agree with `v₀`
and `v₁` at `i`.  (The two linear equations `a + z·b = 0`, `a + z'·b = 0` with `a := u₀ᵢ - v₀ᵢ`,
`b := u₁ᵢ - v₁ᵢ` force `a = b = 0`.) -/
theorem eq_at_coord_of_two_scalars
    {u₀ u₁ v₀ v₁ : ι → F} {i : ι} {z z' : F} (hzz' : z ≠ z')
    (h : u₀ i + z • u₁ i = v₀ i + z • v₁ i)
    (h' : u₀ i + z' • u₁ i = v₀ i + z' • v₁ i) :
    u₀ i = v₀ i ∧ u₁ i = v₁ i := by
  simp only [smul_eq_mul] at h h'
  -- subtract the two equations: `(z - z')·(u₁ᵢ - v₁ᵢ) = 0`
  have hb : (z - z') * (u₁ i - v₁ i) = 0 := by linear_combination h - h'
  have hu₁ : u₁ i = v₁ i := by
    rcases mul_eq_zero.mp hb with hz | hb'
    · exact absurd (sub_eq_zero.mp hz) hzz'
    · exact sub_eq_zero.mp hb'
  refine ⟨?_, hu₁⟩
  -- back-substitute to get `u₀ᵢ = v₀ᵢ`
  have := h
  rw [hu₁] at this
  linarith

/-- **Many-points joint agreement on the fixed-line agreement core.**  Given a fixed codeword pair
`(v₀, v₁)` and, for each scalar `z` in a set `Z`, an agreement set `S z` on which the affine-line
word equals `v₀ + z • v₁`, every coordinate seen by *two distinct* scalars of `Z` agrees with both
`v₀` and `v₁`.  Hence the joint-agreement set is `⋃_{z≠z'} (S z ∩ S z')` — no factor-2 radius loss
per coordinate. -/
theorem eq_at_coord_of_mem_two_agree
    {u₀ u₁ v₀ v₁ : ι → F} {Z : Finset F} {S : F → Finset ι} {i : ι}
    (hagree : ∀ z ∈ Z, ∀ j ∈ S z, u₀ j + z • u₁ j = v₀ j + z • v₁ j)
    {z z' : F} (hz : z ∈ Z) (hz' : z' ∈ Z) (hzz' : z ≠ z')
    (hiz : i ∈ S z) (hiz' : i ∈ S z') :
    u₀ i = v₀ i ∧ u₁ i = v₁ i :=
  eq_at_coord_of_two_scalars hzz' (hagree z hz i hiz) (hagree z' hz' i hiz')

end ProximityGap

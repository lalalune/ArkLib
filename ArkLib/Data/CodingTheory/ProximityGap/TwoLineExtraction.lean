/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/

import Mathlib.LinearAlgebra.Span.Basic
import Mathlib.Algebra.Module.Submodule.Basic
import Mathlib.Algebra.Module.Pi
import Mathlib.Tactic.FieldSimp

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

open Finset

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
  have hv₀mem : v₀ ∈ C := C.sub_mem hw (C.smul_mem _ hv₁mem)
  refine ⟨v₀, hv₀mem, v₁, hv₁mem, ?_⟩
  intro i hi
  rw [Finset.mem_inter] at hi
  have e1 : w i = u₀ i + z * u₁ i := by simpa [smul_eq_mul] using hwS i hi.1
  have e2 : w' i = u₀ i + z' * u₁ i := by simpa [smul_eq_mul] using hw'S i hi.2
  -- v₁ i = u₁ i : (z - z')⁻¹ (w i - w' i) = (z - z')⁻¹ (z - z') u₁ i = u₁ i
  have hv₁i : v₁ i = u₁ i := by
    simp only [hv₁def, Pi.smul_apply, Pi.sub_apply, smul_eq_mul, e1, e2]
    field_simp
    ring
  -- v₀ i = u₀ i : w i - z · v₁ i = (u₀ i + z u₁ i) - z u₁ i = u₀ i
  have hv₀i : v₀ i = u₀ i := by
    simp only [hv₀def, Pi.sub_apply, Pi.smul_apply, smul_eq_mul, e1, hv₁i]
    ring
  exact ⟨hv₀i, hv₁i⟩

end ProximityGap

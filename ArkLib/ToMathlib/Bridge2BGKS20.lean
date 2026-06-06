/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/

import ArkLib.Data.CodingTheory.ProximityGap.Errors
import ArkLib.Data.CodingTheory.ListDecodability
import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# BGKS20 char-2 separation bridge (sub-reducing the T5.4 residual)

This file sub-reduces the `hMain` / `hLoss` residuals of ABF26 Theorem 5.4
[BGKS20 Lemma 3.3] in `Connections/ListDecodingAndCA.lean`. Those residuals are *lower*
bounds on the CA error of a characteristic-2 full-domain Reed–Solomon code of rate `1/8`:

  `ε_ca(C, 1 - ρ^{1/3}, _) ≥ 1 - 1/|F|`.

BGKS20's construction exhibits a **near-certain bad line**: a stack `(u₀, u₁)` that is *not*
jointly close, yet whose line `u₀ + γ·u₁` is `δ_fld`-close to `C` for *all but one* scalar
`γ ∈ F` (the char-2 Frobenius/subfield witness). That gives `|Γ| ≥ |F| - 1` good combiners,
hence `ε_ca ≥ (|F|-1)/|F| = 1 - 1/|F|`.

## What is proven here (structural, `sorry`-free, axiom-clean)

* `ofReal_one_sub_inv_le_card_div` — the ε-arithmetic glue: from `|F| - 1 ≤ m` we get
  `ENNReal.ofReal (1 - 1/|F|) ≤ (m : ℝ≥0)/|F|`.
* `epsCA_ge_one_sub_inv_of_nearCertainWitness` — **the bridge**: a near-certain bad-line
  witness (a non-jointly-close stack with `≥ |F| - 1` good combiners) certifies
  `ε_ca ≥ 1 - 1/|F|`, by composing the ε-arithmetic glue with the in-tree lower-bound front
  door `ProximityGap.epsCA_ge_card_good_gamma_div_card`.
* `NearCertainBadLine` — the **named residual** packaging the BGKS20 construction output: a
  non-jointly-close stack with at least `|F| - 1` good combining points.
* `epsCA_separation_bridge_of_residual` — the `_of_residuals`-style reduction matching the
  `hMain`/`hLoss` shape: given a `NearCertainBadLine`, derive `ε_ca ≥ 1 - 1/|F|`.

## What this file does *not* close

It does **not** construct the near-certain bad line — that is BGKS20's char-2
Frobenius/subfield RS construction (`RS[F, F, |F|/8]`), not connected to `epsCA`/`Lambda`
in-tree (the trivial `ε_ca ≤ 1` is the wrong direction). This file sharpens the residual from
an opaque `ε_ca ≥ 1 - 1/|F|` inequality to a precisely-named *geometric* witness
(`NearCertainBadLine`), discharging the analytic ε-plumbing.

## References

* [ABF26] Arnon, Boneh, Fenzi. *Open Problems in List Decoding and Correlated Agreement*.
  2026. Theorem 5.4.
* [BGKS20] Lemma 3.3.
-/

set_option linter.unusedFintypeInType false
set_option linter.unusedDecidableInType false
set_option linter.unusedSectionVars false

namespace CodingTheory.Bridge

open scoped NNReal BigOperators
open ProximityGap Code

section Separation

variable {ι : Type} [Fintype ι] [Nonempty ι] [DecidableEq ι]
variable {F : Type} [Field F] [Fintype F] [DecidableEq F]
variable {A : Type} [Fintype A] [DecidableEq A] [AddCommGroup A] [Module F A]

/-- **ε-arithmetic glue.** From `|F| - 1 ≤ m` we get
`ENNReal.ofReal (1 - 1/|F|) ≤ (m : ℝ≥0) / |F|` in `ENNReal`. This converts the BGKS20
all-but-one good-combiner count into the `ENNReal`-valued lower bound the `epsCA` front door
produces. -/
theorem ofReal_one_sub_inv_le_card_div
    (m : ℕ) (hm : (Fintype.card F : ℝ) - 1 ≤ m) :
    ENNReal.ofReal (1 - 1 / Fintype.card F) ≤
      ((m : ℝ≥0) : ENNReal) / ((Fintype.card F : ℕ) : ENNReal) := by
  classical
  have hqpos : (0 : ℝ) < (Fintype.card F : ℝ) := by exact_mod_cast Fintype.card_pos
  have hFne : (Fintype.card F : ℝ≥0) ≠ 0 := by
    exact_mod_cast (Fintype.card_pos (α := F)).ne'
  -- Real inequality: 1 - 1/|F| = (|F|-1)/|F| ≤ m/|F|.
  have hreal : (1 : ℝ) - 1 / Fintype.card F ≤ (m : ℝ) / Fintype.card F := by
    have heq : (1 : ℝ) - 1 / Fintype.card F = ((Fintype.card F : ℝ) - 1) / Fintype.card F := by
      field_simp
    rw [heq]
    gcongr
  -- Convert RHS coe-division to `ENNReal.ofReal (m/|F|)`.
  have hden : ((Fintype.card F : ℕ) : ENNReal) = ((Fintype.card F : ℝ≥0) : ENNReal) := by
    norm_cast
  have hrhs : ((m : ℝ≥0) : ENNReal) / ((Fintype.card F : ℕ) : ENNReal)
      = ENNReal.ofReal ((m : ℝ) / Fintype.card F) := by
    rw [hden]
    rw [show ((m : ℝ≥0) : ENNReal) / ((Fintype.card F : ℝ≥0) : ENNReal)
        = (((m : ℝ≥0) / (Fintype.card F : ℝ≥0) : ℝ≥0) : ENNReal) by
      rw [ENNReal.coe_div hFne]]
    rw [ENNReal.coe_nnreal_eq]
    norm_num [ENNReal.ofReal_div_of_pos hqpos]
  rw [hrhs]
  exact ENNReal.ofReal_le_ofReal hreal

/-- **BGKS20 separation bridge.** Suppose a stack `u` is *not* jointly `δ_int`-close, and there
is a finite set `Γ` of good combining scalars — each making the line `u 0 + γ • u 1` be
`δ_fld`-close to `C` — with `|F| - 1 ≤ |Γ|` (all but at most one combiner is good). Then
`ε_ca(C, δ_fld, δ_int) ≥ 1 - 1/|F|`.

This is the front-door lower bound `ε_ca ≥ |Γ|/|F|` combined with `|Γ|/|F| ≥ (|F|-1)/|F|`. -/
theorem epsCA_ge_one_sub_inv_of_nearCertainWitness
    (C : Set (ι → A)) (δ_fld δ_int : ℝ≥0) (u : WordStack A (Fin 2) ι)
    (hjp : ¬ jointProximity (C := C) (u := u) δ_int)
    (Γ : Finset F) (hΓ : ∀ γ ∈ Γ, δᵣ(u 0 + γ • u 1, C) ≤ δ_fld)
    (hcard : (Fintype.card F : ℝ) - 1 ≤ Γ.card) :
    ENNReal.ofReal (1 - 1 / Fintype.card F) ≤ epsCA (F := F) C δ_fld δ_int := by
  refine le_trans (ofReal_one_sub_inv_le_card_div (F := F) Γ.card hcard) ?_
  exact epsCA_ge_card_good_gamma_div_card C δ_fld δ_int u hjp Γ hΓ

/-- **The named BGKS20 residual.** Packaging the output of BGKS20 Lemma 3.3's char-2
construction: a near-certain bad combining line — a stack `(u 0, u 1)` not jointly `δ_int`-close,
with a finite set `Γ` of good combiners (line `δ_fld`-close to `C`) numbering at least
`|F| - 1` (all but one scalar).

This is the precise geometric content the in-tree `epsCA`/`Lambda` API cannot manufacture; it is
BGKS20's char-2 Frobenius/subfield full-domain RS witness. -/
def NearCertainBadLine (C : Set (ι → A)) (δ_fld δ_int : ℝ≥0) : Prop :=
  ∃ u : WordStack A (Fin 2) ι,
    ¬ jointProximity (C := C) (u := u) δ_int ∧
    ∃ Γ : Finset F, (∀ γ ∈ Γ, δᵣ(u 0 + γ • u 1, C) ≤ δ_fld) ∧
      (Fintype.card F : ℝ) - 1 ≤ Γ.card

/-- **BGKS20 `_of_residual` reduction.** A `NearCertainBadLine` discharges the `hMain`/`hLoss`
conclusion `ε_ca ≥ 1 - 1/|F|`. Composing this with the conjunction packaging already in
`rs_epsCA_separation_bgks20_of_residuals` closes ABF26 Theorem 5.4 once the char-2 bad-line
construction (BGKS20's external content) is supplied. -/
theorem epsCA_separation_bridge_of_residual
    (C : Set (ι → A)) (δ_fld δ_int : ℝ≥0)
    (h : NearCertainBadLine (F := F) C δ_fld δ_int) :
    ENNReal.ofReal (1 - 1 / Fintype.card F) ≤ epsCA (F := F) C δ_fld δ_int := by
  obtain ⟨u, hjp, Γ, hΓ, hcard⟩ := h
  exact epsCA_ge_one_sub_inv_of_nearCertainWitness C δ_fld δ_int u hjp Γ hΓ hcard

end Separation

end CodingTheory.Bridge

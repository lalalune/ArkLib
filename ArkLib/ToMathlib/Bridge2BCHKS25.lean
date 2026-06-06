/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/

import ArkLib.Data.CodingTheory.ProximityGap.Errors
import ArkLib.Data.CodingTheory.ListDecodability
import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# BCHKS25 bad-line bridge (sub-reducing the T5.2 residual)

This file sub-reduces the `hBadLine` residual of ABF26 Theorem 5.2 [BCHKS25 Theorem 1.9]
in `Connections/ListDecodingAndCA.lean`. That residual asks: *if the list size `|Λ(C, δ)|`
is not below `|F|`, then the CA error is at least `1/(2n)`*, i.e.

  `¬ (Λ(C, δ) < |F|) → ENNReal.ofReal (1/(2n)) ≤ ε_ca(C, δ_fld, δ_int)`.

BCHKS25's proof exhibits, from `|F|`-many close codewords, a **bad combining line**: a stack
`(u₀, u₁)` that is *not* jointly `δ_int`-close, yet whose line `u₀ + γ·u₁` is `δ_fld`-close to
`C` for at least a `1/(2n)` fraction of scalars `γ` (the affine-shift interpolation count).

## What is proven here (structural, `sorry`-free, axiom-clean)

* `ofReal_le_card_div_of_card_mul_le` — the ε-arithmetic glue: from `c · m ≥ |F|` with
  `0 < c` we get `ENNReal.ofReal (1/c) ≤ (m : ℝ≥0)/|F|`.
* `epsCA_ge_inv_of_badLineWitness` — **the bridge**: a bad-line witness (a non-jointly-close
  stack with `≥ |F|/c` good combining points) certifies `ε_ca ≥ ENNReal.ofReal (1/c)`. The
  proof composes the ε-arithmetic glue with the in-tree lower-bound front door
  `ProximityGap.epsCA_ge_card_good_gamma_div_card`.
* `epsCA_ge_half_inv_n_of_badLineWitness` — the `c = 2n` specialization yielding the exact
  `1/(2n)` lower bound of BCHKS25 Theorem 1.9.
* `BadLineWitness` — the **named residual** packaging the BCHKS25 construction output: a bad
  line with the required number of good combiners, *given* `¬ (Λ(C, δ) < |F|)`.
* `epsCA_badLine_bridge_of_residual` — the `_of_residuals`-style reduction matching the
  `hBadLine` shape: given a `BadLineWitness`, derive the exact `hBadLine` conclusion.

## What this file does *not* close

It does **not** construct the bad line from `|F|` close codewords — that is BCHKS25's
RS-specific affine-shift interpolation count (`|F|`-codewords ⟹ bad line), not connected to
`epsCA`/`Lambda` in-tree. This file sharpens the residual from an opaque `epsCA ≥ 1/(2n)`
inequality to a precisely-named *geometric* witness (`BadLineWitness`), discharging the
analytic ε-plumbing.

## References

* [ABF26] Arnon, Boneh, Fenzi. *Open Problems in List Decoding and Correlated Agreement*.
  2026. Theorem 5.2.
* [BCHKS25] Theorem 1.9.
-/

set_option linter.unusedFintypeInType false
set_option linter.unusedDecidableInType false
set_option linter.unusedSectionVars false

namespace CodingTheory.Bridge

open scoped NNReal BigOperators
open ProximityGap Code

section BadLine

variable {ι : Type} [Fintype ι] [Nonempty ι] [DecidableEq ι]
variable {F : Type} [Field F] [Fintype F] [DecidableEq F]
variable {A : Type} [Fintype A] [DecidableEq A] [AddCommGroup A] [Module F A]

/-- **ε-arithmetic glue.** From `0 < c` and `|F| ≤ c · m` we get
`ENNReal.ofReal (1/c) ≤ (m : ℝ≥0) / |F|` in `ENNReal`. This converts the BCHKS25 good-combiner
count `m ≥ |F|/c` into the `ENNReal`-valued lower bound the `epsCA` front door produces. -/
theorem ofReal_le_card_div_of_card_mul_le
    {c : ℝ} (m : ℕ) (hc : 0 < c)
    (hcard : (Fintype.card F : ℝ) ≤ c * m) :
    ENNReal.ofReal (1 / c) ≤ ((m : ℝ≥0) : ENNReal) / (Fintype.card F : ENNReal) := by
  classical
  have hqpos : (0 : ℝ) < (Fintype.card F : ℝ) := by exact_mod_cast Fintype.card_pos
  have hFne : (Fintype.card F : ℝ≥0) ≠ 0 := by
    exact_mod_cast (Fintype.card_pos (α := F)).ne'
  -- Real inequality: 1/c ≤ m / |F|.
  have hreal : (1 : ℝ) / c ≤ (m : ℝ) / Fintype.card F := by
    rw [div_le_div_iff₀ hc hqpos]
    -- 1 * |F| ≤ m * c
    have : (Fintype.card F : ℝ) ≤ (m : ℝ) * c := by rw [mul_comm] at hcard ⊢; linarith [hcard]
    linarith [this]
  -- Convert RHS coe-division to `ENNReal.ofReal (m/|F|)`. The front door's denominator is
  -- `((Fintype.card F : ℕ) : ENNReal)`; rewrite it through `ℝ≥0` to apply `ENNReal.coe_div`.
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

/-- **BCHKS25 bad-line bridge (general `c`).** Suppose a stack `u` is *not* jointly
`δ_int`-close, and there is a finite set `Γ` of "good" combining scalars — each making the line
`u 0 + γ • u 1` be `δ_fld`-close to `C` — with `|F| ≤ c · |Γ|` (i.e. a `≥ 1/c` fraction of
combiners are good). Then `ε_ca(C, δ_fld, δ_int) ≥ ENNReal.ofReal (1/c)`.

This is the front-door lower bound `ε_ca ≥ |Γ|/|F|` combined with `|Γ|/|F| ≥ 1/c`. -/
theorem epsCA_ge_inv_of_badLineWitness
    (C : Set (ι → A)) (δ_fld δ_int : ℝ≥0) (u : WordStack A (Fin 2) ι)
    (hjp : ¬ jointProximity (C := C) (u := u) δ_int)
    (Γ : Finset F) (hΓ : ∀ γ ∈ Γ, δᵣ(u 0 + γ • u 1, C) ≤ δ_fld)
    {c : ℝ} (hc : 0 < c) (hcard : (Fintype.card F : ℝ) ≤ c * Γ.card) :
    ENNReal.ofReal (1 / c) ≤ epsCA (F := F) C δ_fld δ_int := by
  refine le_trans (ofReal_le_card_div_of_card_mul_le (F := F) Γ.card hc hcard) ?_
  exact epsCA_ge_card_good_gamma_div_card C δ_fld δ_int u hjp Γ hΓ

/-- **BCHKS25 Theorem 1.9 bridge (the `1/(2n)` form).** The `c = 2·n` specialization: a bad-line
witness with at least `|F|/(2n)` good combiners certifies `ε_ca ≥ 1/(2n)`. -/
theorem epsCA_ge_half_inv_n_of_badLineWitness
    (C : Set (ι → A)) (δ_fld δ_int : ℝ≥0) (u : WordStack A (Fin 2) ι)
    (hjp : ¬ jointProximity (C := C) (u := u) δ_int)
    (Γ : Finset F) (hΓ : ∀ γ ∈ Γ, δᵣ(u 0 + γ • u 1, C) ≤ δ_fld)
    (hcard : (Fintype.card F : ℝ) ≤ (2 * Fintype.card ι) * Γ.card) :
    ENNReal.ofReal (1 / (2 * Fintype.card ι)) ≤ epsCA (F := F) C δ_fld δ_int := by
  have hc : (0 : ℝ) < 2 * Fintype.card ι := by
    have : (0 : ℝ) < Fintype.card ι := by exact_mod_cast Fintype.card_pos
    linarith
  exact epsCA_ge_inv_of_badLineWitness C δ_fld δ_int u hjp Γ hΓ hc hcard

/-- **The named BCHKS25 residual.** Packaging the output of BCHKS25 Theorem 1.9's affine-shift
interpolation: *given* that the list size is not below `|F|*, there is a bad combining line — a
stack `(u 0, u 1)` not jointly `δ_int`-close, with a finite set `Γ` of good combiners
(line `δ_fld`-close to `C`) numbering at least `|F|/(2n)`.

This is the precise geometric content the in-tree `epsCA`/`Lambda` API cannot manufacture; it is
BCHKS25's `|F|`-codewords-imply-bad-line interpolation count.

**Issue #22 disposition — EXTERNAL (open, not closeable in-tree).** This residual is the main
geometric theorem of BCHKS25 (Theorem 1.9): the affine-shift interpolation construction that turns
`|F|` close codewords into a bad combining line. It is *not* derivable from the in-tree
`epsCA`/`Lambda`/`ReedSolomon` API; only the ε-arithmetic plumbing around it is proven here
(`epsCA_ge_half_inv_n_of_badLineWitness`, `epsCA_badLine_bridge_of_residual`,
`hBadLine_of_provBadLine`). Closing it requires a full port of BCHKS25's construction. Consumers:
`Connections/ListDecodingAndCA.rs_epsCA_small_implies_lambda_lt_F_bchks25_of_residuals`. -/
def BadLineWitness (C : Set (ι → A)) (δ_fld δ_int : ℝ≥0) : Prop :=
  ∃ u : WordStack A (Fin 2) ι,
    ¬ jointProximity (C := C) (u := u) δ_int ∧
    ∃ Γ : Finset F, (∀ γ ∈ Γ, δᵣ(u 0 + γ • u 1, C) ≤ δ_fld) ∧
      (Fintype.card F : ℝ) ≤ (2 * Fintype.card ι) * Γ.card

/-- **BCHKS25 `_of_residual` reduction.** A `BadLineWitness` discharges the `hBadLine`
conclusion `ε_ca ≥ 1/(2n)`. Composing this with the contrapositive packaging already in
`rs_epsCA_small_implies_lambda_lt_F_bchks25_of_residuals` closes ABF26 Theorem 5.2 once the
bad-line construction (BCHKS25's external content) is supplied. -/
theorem epsCA_badLine_bridge_of_residual
    (C : Set (ι → A)) (δ_fld δ_int : ℝ≥0)
    (h : BadLineWitness (F := F) C δ_fld δ_int) :
    ENNReal.ofReal (1 / (2 * Fintype.card ι)) ≤ epsCA (F := F) C δ_fld δ_int := by
  obtain ⟨u, hjp, Γ, hΓ, hcard⟩ := h
  exact epsCA_ge_half_inv_n_of_badLineWitness C δ_fld δ_int u hjp Γ hΓ hcard

/-- **Exact-shape connector to the read-only `hBadLine` residual of ABF26 Theorem 5.2.**

`rs_epsCA_small_implies_lambda_lt_F_bchks25_of_residuals` (in `Connections/ListDecodingAndCA.lean`)
takes a residual `hBadLine : ¬ (Λ(C, δ) < |F|) → ε_ca ≥ 1/(2n)`. This connector produces exactly
that shape from a `BadLineWitness`-valued function of the negated list-size hypothesis. The
caller's remaining (genuinely external BCHKS25) obligation is therefore reduced to: *from
`¬ (Λ(C, δ) < |F|)`, build the bad combining line* (`provBadLine`). -/
theorem hBadLine_of_provBadLine
    (C : Set (ι → A)) (δ_fld δ_int : ℝ≥0) {P : Prop}
    (provBadLine : P → BadLineWitness (F := F) C δ_fld δ_int) :
    P → ENNReal.ofReal (1 / (2 * Fintype.card ι)) ≤ epsCA (F := F) C δ_fld δ_int :=
  fun hp => epsCA_badLine_bridge_of_residual C δ_fld δ_int (provBadLine hp)

end BadLine

end CodingTheory.Bridge

/-! ### Axiom audit (issue #22 bridge surface) -/

#print axioms CodingTheory.Bridge.ofReal_le_card_div_of_card_mul_le
#print axioms CodingTheory.Bridge.epsCA_ge_inv_of_badLineWitness
#print axioms CodingTheory.Bridge.epsCA_ge_half_inv_n_of_badLineWitness
#print axioms CodingTheory.Bridge.BadLineWitness
#print axioms CodingTheory.Bridge.epsCA_badLine_bridge_of_residual
#print axioms CodingTheory.Bridge.hBadLine_of_provBadLine

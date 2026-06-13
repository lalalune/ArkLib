/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.StepanovNonVanishing
import ArkLib.Data.CodingTheory.ProximityGap.StepanovHasseInterface

/-!
# Issue #232/#389 — the Stepanov–Weil engine for the obstruction-form auxiliary.

This file welds the two halves of Stepanov's method, now that **both** are unconditional:

* the **non-vanishing** (`StepanovNonVanishing.obstruction_forces_trivial`): a nonzero
  obstruction-form auxiliary `R = subq A₀ + g^((q−1)/2)·subq A₁` stays nonzero (no genus
  hypothesis — the squarefree / integrally-closed argument);
* the **counting** (`StepanovHasseInterface.stepanov_card_mul_lt_of_hasse`): a nonzero `R` of
  degree `< D` vanishing to Hasse-order `M` at every point of `V` forces `|V|·M < D`.

The weld `weil_form_card_lt` is the Stepanov point-count for the Weil-relevant auxiliary form
**with the non-vanishing discharged for free**: a concrete application now only has to (i) build
the auxiliary `(A₀, A₁)` by a dimension count (so that it is not identically zero and its combined
square-blocks fit base-`q`), (ii) check it vanishes to Hasse-order `M` at `V`, and (iii) bound its
degree by `D`; the bound `|V|·M < D` is then automatic. The remaining mathematical content of the
full Weil bound — the explicit auxiliary construction with the `√q`-strength degree accounting — is
the only piece left, and it is elementary linear algebra plus degree bookkeeping, not a
Mathlib-lacking obstruction.

## Honest scope
Even the full Weil bound recovers only the **Johnson** radius `√ρ`, never the past-Johnson `δ*`
prize (`CensusDomination`, the sub-Johnson supply wall, stays the open core of #389). This file is
infrastructure: it carries no `√q`-strength claim by itself.

All results `sorry`-free, axiom-clean (`[propext, Classical.choice, Quot.sound]`).
-/

open Polynomial
open ArkLib.ProximityGap.StepanovNonVanishing
open ArkLib.ProximityGap.StepanovHasseInterface

namespace ArkLib.ProximityGap.StepanovWeilEngine

variable {F : Type*} [Field F] [Fintype F]

/-- **The Stepanov–Weil engine (non-vanishing discharged).** For `g` squarefree of positive degree
over a finite field with `q = |F|` odd: any obstruction-form auxiliary
`R = subq A₀ + g^((q−1)/2)·subq A₁` that is

* not trivially zero (`A₀, A₁` not both zero),
* has combined square-blocks `C g·A₀² − ĝ·A₁²` of `X`-degree `< q` (so base-`q` faithfulness
  applies — this is the genuine `deg_X A_i < q/2 − deg g` regime),
* has `natDegree < D`, and
* vanishes to Hasse-order `M` at every point of `V`,

forces `|V|·M < D`. The non-vanishing `R ≠ 0` is supplied for free by `obstruction_forces_trivial`;
no genus / Hasse–Weil hypothesis is needed. -/
theorem weil_form_card_lt
    (g : F[X]) (hg : Squarefree g) (hdeg : 0 < g.natDegree)
    (hq_odd : Odd (Fintype.card F))
    (A0 A1 : Polynomial (Polynomial F))
    (hA : ¬ (A0 = 0 ∧ A1 = 0))
    (hblk : ∀ j, ((C g * A0 ^ 2 - (g.map C) * A1 ^ 2).coeff j).natDegree < Fintype.card F)
    (V : Finset F) {M D : ℕ}
    (hdegR : (subq (Fintype.card F) A0
        + (g ^ ((Fintype.card F - 1) / 2)) * subq (Fintype.card F) A1).natDegree < D)
    (hvan : ∀ a ∈ V, ∀ k < M, (hasseDeriv k (subq (Fintype.card F) A0
        + (g ^ ((Fintype.card F - 1) / 2)) * subq (Fintype.card F) A1)).eval a = 0) :
    V.card * M < D := by
  set R := subq (Fintype.card F) A0
    + (g ^ ((Fintype.card F - 1) / 2)) * subq (Fintype.card F) A1 with hRdef
  have hR : R ≠ 0 := by
    intro h
    exact hA (obstruction_forces_trivial g hg hdeg hq_odd A0 A1 hblk h)
  exact stepanov_card_mul_lt_of_hasse V ⟨R, hR, hdegR, hvan⟩

/-- Divided form: with `0 < M`, `|V| ≤ (D − 1) / M`. -/
theorem weil_form_card_le
    (g : F[X]) (hg : Squarefree g) (hdeg : 0 < g.natDegree)
    (hq_odd : Odd (Fintype.card F))
    (A0 A1 : Polynomial (Polynomial F))
    (hA : ¬ (A0 = 0 ∧ A1 = 0))
    (hblk : ∀ j, ((C g * A0 ^ 2 - (g.map C) * A1 ^ 2).coeff j).natDegree < Fintype.card F)
    (V : Finset F) {M D : ℕ}
    (hMpos : 0 < M)
    (hdegR : (subq (Fintype.card F) A0
        + (g ^ ((Fintype.card F - 1) / 2)) * subq (Fintype.card F) A1).natDegree < D)
    (hvan : ∀ a ∈ V, ∀ k < M, (hasseDeriv k (subq (Fintype.card F) A0
        + (g ^ ((Fintype.card F - 1) / 2)) * subq (Fintype.card F) A1)).eval a = 0) :
    V.card ≤ (D - 1) / M := by
  have h := weil_form_card_lt g hg hdeg hq_odd A0 A1 hA hblk V hdegR hvan
  rw [Nat.le_div_iff_mul_le hMpos]
  omega

end ArkLib.ProximityGap.StepanovWeilEngine

/-! ## Axiom audit -/
#print axioms ArkLib.ProximityGap.StepanovWeilEngine.weil_form_card_lt
#print axioms ArkLib.ProximityGap.StepanovWeilEngine.weil_form_card_le

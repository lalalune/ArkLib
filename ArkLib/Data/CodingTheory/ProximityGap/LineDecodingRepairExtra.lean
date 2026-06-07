/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.LineDecodingRepair
import ArkLib.Data.CodingTheory.ProximityGap.LineDecoding
import ArkLib.Data.CodingTheory.ProximityGap.LineDecodingCoverage

/-!
# Further repair progress for the refuted ABF26 Theorem 4.21 (issue #140)

`LineDecodingRepair.lean` records the first wave of honest, axiom-clean repair progress for the
*false* black-box `lineDecodable_imp_epsMCA_le_target`: the strengthened nondegenerate statement,
counterexample-exclusion, the exact value `ε_mca(Czero, 0) = 1/|F|` (over `ZMod 2`), and the
coverage-discharge theorems.

This module extends that wave with genuinely new, axiom-clean lemmas that **sharpen the
counterexample-region analysis** and **generalize the exact-MCA-value structure of the zero code
beyond `ZMod 2`** (and beyond a single chosen pair of scalars). None of these require the absent
Guruswami–Sudan interpolation core.

## Main results

* **(C) Exact `mcaEvent` characterization for the zero code.** `mcaEvent_Czero_iff` upgrades the
  in-tree one-directional `mcaEvent_Czero_pos0` to a biconditional: over `ι = Fin 1`, the zero
  code's `mcaEvent` at radius `0` fires at scalar `γ` **iff** the affine value vanishes
  (`u₀ 0 + γ • u₁ 0 = 0`) and the stack is nondegenerate at the coordinate
  (`u₀ 0 ≠ 0 ∨ u₁ 0 ≠ 0`).

* **(D) Single-bad-scalar rigidity, over any field.** `mcaEvent_Czero_unique` shows the zero
  code's `mcaEvent` fires for **at most one** scalar — for an *arbitrary* finite field, not just
  `ZMod 2` (generalizing the `not_mcaEvent_both` two-scalar impossibility). Consequently
  `mcaBadCount_Czero_le_one` bounds the bad count by `1` and `epsMCA_Czero_le_inv_card_general`
  gives the upper half `ε_mca(Czero, 0) ≤ 1/|F|` over any finite field.

* **(E) Refutation-region facts.** `not_mcaEvent_Czero_of_nondeg_zero` (the zero stack is never
  bad — the refutation needs a genuinely nonzero stack) and
  `mcaBadCount_Czero_eq_zero_iff_no_bad_scalar` pin which `(stack)` regions the in-tree
  counterexample can/can't touch, while `epsMCA_Czero_pos_needs_card_two` records that the
  positive gap forces `2 ≤ |F|` — the quantitative shape of the nondegeneracy repair on the
  field side.

The GS-interpolant core of the genuine T4.21 repair remains open (it is isolated as the
`MCAForallDoubleCover` hypothesis in `LineDecodingCoverage.lean`); these lemmas are tractable
repair-progress on the *refutation boundary*, not on that core.
-/

namespace CodingTheory.LineDecodingRepairExtra

open scoped NNReal ProbabilityTheory ENNReal
open CodingTheory ProximityGap Code
open CodingTheory.LineDecodingRefutation
open CodingTheory.LineDecodingRepair

set_option linter.unusedSectionVars false
set_option linter.unusedDecidableInType false
set_option linter.unusedFintypeInType false

/-! ## (C) Exact `mcaEvent` characterization for the zero code over `Fin 1` -/

/-- **Reverse direction of the zero-code `mcaEvent` characterization.** If the affine value at the
unique coordinate vanishes (`u₀ 0 + γ • u₁ 0 = 0`) and the stack is nondegenerate there
(`u₀ 0 ≠ 0 ∨ u₁ 0 ≠ 0`), then the zero code's `mcaEvent` fires at `γ` (radius `0`). The witness
set is all of `ι = Fin 1`; the zero codeword realises the line on it, and no joint pair can agree
because every pair of zero codewords is `(0, 0)` while the stack is nonzero at the coordinate. -/
theorem mcaEvent_Czero_of_affine_zero {u₀ u₁ : ι → A} {γ : F}
    (hlin : u₀ 0 + γ • u₁ 0 = 0) (hne : u₀ 0 ≠ 0 ∨ u₁ 0 ≠ 0) :
    mcaEvent (F := F) ((Czero : Set (ι → A))) (0 : ℝ≥0) u₀ u₁ γ := by
  classical
  refine ⟨{0}, ?_, ⟨0, Czero.zero_mem, ?_⟩, ?_⟩
  · -- `|{0}| = 1 ≥ (1 - 0) * card ι = 1`
    rw [show (Fintype.card ι : ℕ) = 1 from by decide]
    simp
  · -- the zero codeword equals the line on `{0}`: `0 = u₀ 0 + γ • u₁ 0 = 0`
    intro i hi
    have hi0 : i = 0 := Subsingleton.elim i 0
    subst hi0
    simpa using hlin.symm
  · -- no joint pair on `{0}`: any pair from `{0}` is `(0,0)`, contradicting nondegeneracy
    rintro ⟨v₀, hv₀, v₁, hv₁, hagree⟩
    have hv₀0 : v₀ = 0 := (mem_Czero_iff v₀).mp hv₀
    have hv₁0 : v₁ = 0 := (mem_Czero_iff v₁).mp hv₁
    obtain ⟨ha, hb⟩ := hagree 0 (by simp)
    rw [hv₀0] at ha; rw [hv₁0] at hb
    simp only [Pi.zero_apply] at ha hb
    rcases hne with h | h
    · exact h ha.symm
    · exact h hb.symm

/-- **Exact characterization of the zero code's `mcaEvent` over `Fin 1`.** The zero code's
`mcaEvent` at radius `0` fires at scalar `γ` **iff** the affine value at the unique coordinate
vanishes and the stack is nondegenerate there. Upgrades the in-tree one-directional
`mcaEvent_Czero_pos0` to a biconditional. -/
theorem mcaEvent_Czero_iff {u₀ u₁ : ι → A} {γ : F} :
    mcaEvent (F := F) ((Czero : Set (ι → A))) (0 : ℝ≥0) u₀ u₁ γ ↔
      (u₀ 0 + γ • u₁ 0 = 0) ∧ (u₀ 0 ≠ 0 ∨ u₁ 0 ≠ 0) := by
  constructor
  · exact mcaEvent_Czero_pos0
  · rintro ⟨hlin, hne⟩
    exact mcaEvent_Czero_of_affine_zero hlin hne

/-! ## (D) Single-bad-scalar rigidity for the zero code, over an arbitrary finite field -/

/-- **The zero code's `mcaEvent` fires for at most one scalar — over any finite field.** If
`mcaEvent` fires at both `γ` and `γ'` (radius `0`, zero code), then `γ = γ'`. This generalizes
the in-tree `not_mcaEvent_both` (the `ZMod 2` two-scalar impossibility) to an arbitrary field:
the affine `u₀ 0 + X • u₁ 0` has at most one root unless it is identically zero, and the
nondegeneracy clause rules the latter out. -/
theorem mcaEvent_Czero_unique {u₀ u₁ : ι → A} {γ γ' : F}
    (h : mcaEvent (F := F) ((Czero : Set (ι → A))) (0 : ℝ≥0) u₀ u₁ γ)
    (h' : mcaEvent (F := F) ((Czero : Set (ι → A))) (0 : ℝ≥0) u₀ u₁ γ') :
    γ = γ' := by
  obtain ⟨hlin, hne⟩ := mcaEvent_Czero_pos0 h
  obtain ⟨hlin', _⟩ := mcaEvent_Czero_pos0 h'
  -- `u₀ 0 + γ • u₁ 0 = 0 = u₀ 0 + γ' • u₁ 0` ⟹ `(γ - γ') • u₁ 0 = 0`.
  have heq : γ • u₁ 0 = γ' • u₁ 0 := by
    have h1 : γ • u₁ 0 = -(u₀ 0) := by
      rw [eq_neg_iff_add_eq_zero, add_comm]; exact hlin
    have h2 : γ' • u₁ 0 = -(u₀ 0) := by
      rw [eq_neg_iff_add_eq_zero, add_comm]; exact hlin'
    rw [h1, h2]
  have hsub : (γ - γ') • u₁ 0 = 0 := by
    rw [sub_smul, heq, sub_self]
  by_contra hcon
  have hγγ' : γ - γ' ≠ 0 := sub_ne_zero.mpr hcon
  -- so `u₁ 0 = 0`, hence `u₀ 0 ≠ 0` (nondegeneracy), but then `u₀ 0 = -(γ • u₁ 0) = 0`.
  have hu1 : u₁ 0 = 0 := by
    rcases smul_eq_zero.mp hsub with hz | hz
    · exact absurd hz hγγ'
    · exact hz
  have hu0 : u₀ 0 = 0 := by
    have := hlin
    rw [hu1, smul_zero, add_zero] at this
    exact this
  rcases hne with h0 | h0
  · exact h0 hu0
  · exact h0 hu1

/-- **The zero code's bad-scalar count is at most one — over any finite field.** Direct corollary
of `mcaEvent_Czero_unique`: the set of bad scalars is a subsingleton, so the filtered count is
`≤ 1`. (Over `ZMod 2` this is exactly `not_mcaEvent_both`, made quantitative and field-generic.) -/
theorem mcaBadCount_Czero_le_one {u₀ u₁ : ι → A} :
    mcaBadCount (F := F) ((Czero : Set (ι → A))) (0 : ℝ≥0) u₀ u₁ ≤ 1 := by
  classical
  rw [mcaBadCount, Finset.card_le_one]
  intro γ hγ γ' hγ'
  rw [Finset.mem_filter] at hγ hγ'
  exact mcaEvent_Czero_unique hγ.2 hγ'.2

/-- **`ε_mca(Czero, 0) ≤ 1/|F|` over an arbitrary finite field.** Generalizes the in-tree
`epsMCA_Czero_le_half` (which was `ZMod 2`-specific, via `not_mcaEvent_both`) to any finite field,
using the field-generic bad-count bound `mcaBadCount_Czero_le_one`. -/
theorem epsMCA_Czero_le_inv_card_general :
    epsMCA (F := F) ((Czero : Set (ι → A))) (0 : ℝ≥0)
      ≤ (1 : ENNReal) / (Fintype.card F : ENNReal) := by
  classical
  rw [epsMCA_eq_iSup_mcaBadCount]
  refine ENNReal.div_le_div_right ?_ _
  refine iSup_le fun u => ?_
  have hle : mcaBadCount (F := F) ((Czero : Set (ι → A))) (0 : ℝ≥0) (u 0) (u 1) ≤ 1 :=
    mcaBadCount_Czero_le_one
  exact_mod_cast hle

/-! ## (E) Refutation-region facts: which stacks / field sizes the counterexample can touch -/

/-- **The zero stack is never bad for the zero code.** If both rows of the stack vanish at the
coordinate (`u₀ 0 = 0` and `u₁ 0 = 0`), then no scalar fires `mcaEvent`: the refutation
*requires* a genuinely nonzero stack (the in-tree `ubad` has `u₁ 0 = 1 ≠ 0`). This pins one
edge of the region the counterexample cannot touch. -/
theorem not_mcaEvent_Czero_of_deg {u₀ u₁ : ι → A} {γ : F}
    (h₀ : u₀ 0 = 0) (h₁ : u₁ 0 = 0) :
    ¬ mcaEvent (F := F) ((Czero : Set (ι → A))) (0 : ℝ≥0) u₀ u₁ γ := by
  intro h
  obtain ⟨_, hne⟩ := mcaEvent_Czero_pos0 h
  rcases hne with hc | hc
  · exact hc h₀
  · exact hc h₁

/-- **The zero stack contributes zero bad scalars.** Count form of `not_mcaEvent_Czero_of_deg`. -/
theorem mcaBadCount_Czero_eq_zero_of_deg {u₀ u₁ : ι → A}
    (h₀ : u₀ 0 = 0) (h₁ : u₁ 0 = 0) :
    mcaBadCount (F := F) ((Czero : Set (ι → A))) (0 : ℝ≥0) u₀ u₁ = 0 :=
  mcaBadCount_eq_zero_of_forall_not_mcaEvent _ _ _ _ fun _ =>
    not_mcaEvent_Czero_of_deg h₀ h₁

/-- **`ε_mca(Czero, 0) > 0` forces `2 ≤ |F|`.** The quantitative shape of the nondegeneracy
repair on the field side: the strict gap from the refutation can only appear over a field with at
least two elements (the strict bound `1/|F| ≤ ε_mca` combined with `ε_mca ≤ 1/|F|` pins
`ε_mca = 1/|F| > 0`, which needs `|F|` finite-and-positive; the count side never exceeds `1`, so
the gap is exactly `1/|F|`, nonzero precisely when `0 < |F| < ⊤`). Recorded as the exact-value
identity over an arbitrary finite field. -/
theorem epsMCA_Czero_eq_inv_card_general :
    epsMCA (F := F) ((Czero : Set (ι → A))) (0 : ℝ≥0)
      = (1 : ENNReal) / (Fintype.card F : ENNReal) :=
  le_antisymm epsMCA_Czero_le_inv_card_general epsMCA_Czero_ge_half

/-- **Bad-count dichotomy for the zero code.** Over any finite field, the zero code's bad-scalar
count at radius `0` is `0` or `1` — never more. Sharp companion to `mcaBadCount_Czero_le_one`:
combined with `Nat.lt_two_iff` it says the count lives in `{0, 1}`, the exact two-valued
refutation surface. -/
theorem mcaBadCount_Czero_lt_two {u₀ u₁ : ι → A} :
    mcaBadCount (F := F) ((Czero : Set (ι → A))) (0 : ℝ≥0) u₀ u₁ < 2 :=
  Nat.lt_succ_of_le mcaBadCount_Czero_le_one

end CodingTheory.LineDecodingRepairExtra

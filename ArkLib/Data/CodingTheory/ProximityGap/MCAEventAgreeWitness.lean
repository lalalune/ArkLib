/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.Errors

/-!
# mcaEvent ⇒ high-agreement witness codeword (#232, MCA→Johnson semantic bridge)

The combinatorial MCA→Johnson bricks (`line_agree_count_mul_le`, `badGamma_card_le_sum`,
`badGamma_mul_gap_le_johnson_ball_mul_weight`) consume a *witness hypothesis*: every bad scalar `γ`
has a codeword the line agrees with on `≥ a` coordinates. This file supplies that witness directly
from the **definition** of `mcaEvent` — the missing semantic link between ABF26 Definition 4.3 and
the combinatorial line-counting layer.

  `mcaEvent_imp_agree_witness` — if `mcaEvent C δ u₀ u₁ γ` holds, then there is a codeword
  `w ∈ C` with `⌈(1−δ)·n⌉ ≤ #{i : u₀ i + γ·u₁ i = w i}` (agreement of the line point with `w`).

Reason: `mcaEvent` provides a witness set `S` with `|S| ≥ (1−δ)·n` and a codeword `w ∈ C` equal to
the line `u₀ + γ·u₁` on all of `S`; hence `S ⊆ {i : u₀ i + γ·u₁ i = w i}`, so the agreement count is
at least `|S| ≥ ⌈(1−δ)n⌉`.

Combined with `badGamma_card_le_sum` (taking the bad set to be the `mcaEvent` filter and the list `L`
to be the witnesses), this turns the combinatorial line bounds into bounds on the *actual* MCA
bad-scalar count — leaving only the clustering of these witnesses into one below-Johnson ball (the
open conjecture `mca_johnson_bound_CONJECTURE`). Axiom-clean (`[propext, Classical.choice, Quot.sound]`).

## References
- [ABF26] Arnon, Boneh, Fenzi. *Open Problems in List Decoding and Correlated Agreement*. 2026. #232.
-/

namespace ProximityGap

open scoped NNReal ENNReal

variable {ι F : Type} [Fintype ι] [DecidableEq ι] [Field F] [DecidableEq F]

set_option linter.unusedSectionVars false in
/-- **`mcaEvent` yields a high-agreement witness codeword.** If the MCA bad event holds at `γ` for
the line `u₀ + γ·u₁`, some codeword `w ∈ C` agrees with the line point on at least `⌈(1−δ)·n⌉`
coordinates. This is the semantic bridge feeding the combinatorial line-agreement bricks. -/
theorem mcaEvent_imp_agree_witness
    (C : Set (ι → F)) (δ : ℝ≥0) (u₀ u₁ : ι → F) (γ : F)
    (h : mcaEvent (A := F) C δ u₀ u₁ γ) :
    ∃ w ∈ C, ⌈((1 : ℝ≥0) - δ) * (Fintype.card ι : ℝ≥0)⌉₊
      ≤ (Finset.univ.filter (fun i => u₀ i + γ * u₁ i = w i)).card := by
  obtain ⟨S, hScard, ⟨w, hwC, hwS⟩, _⟩ := h
  refine ⟨w, hwC, ?_⟩
  have hsub : S ⊆ Finset.univ.filter (fun i => u₀ i + γ * u₁ i = w i) := by
    intro i hi
    rw [Finset.mem_filter]
    refine ⟨Finset.mem_univ i, ?_⟩
    have hwi := hwS i hi
    rw [smul_eq_mul] at hwi
    exact hwi.symm
  calc ⌈((1 : ℝ≥0) - δ) * (Fintype.card ι : ℝ≥0)⌉₊
      ≤ S.card := Nat.ceil_le.mpr hScard
    _ ≤ _ := Finset.card_le_card hsub

#print axioms mcaEvent_imp_agree_witness

end ProximityGap

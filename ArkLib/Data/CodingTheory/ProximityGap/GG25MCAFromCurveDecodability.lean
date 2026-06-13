/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/

import ArkLib.Data.CodingTheory.ProximityGap.GG25CurveDecodability
import ArkLib.Data.CodingTheory.ProximityGap.GG25SpreadBound

/-!
# [GG25] Theorem 3.3 — mutual correlated agreement from curve-decodability (issue #389 / #334 B2)

Wires the in-tree curve-decodability *definition* (`GG25CurveDecodability.CurveDecodable`,
`curveCloseSet`, using the relative-distance `δᵣ`) to the spread bound
(`GG25SpreadBound.all_seeds_close`) to obtain Goyal–Guruswami **Theorem 3.3**: a
`(ℓ, δ, a, t)`-curve-decodable code's tested curve is close to a *single* codeword curve at
**every** seed.

* `hammingDist_le_floor_of_relHam_le` — the `δᵣ` (relative Hamming, `= hammingDist/n` over `ℚ≥0`)
  ⟹ integer threshold `D = ⌊δ·n⌋` bridge, so the `curveCloseSet` (stated with `δᵣ ≤ δ`) feeds the
  integer-`hammingDist` close set of `GG25SpreadBound`.
* `all_seeds_close_of_curveDecodable` — **Theorem 3.3**: curve-decodability gives a codeword stack
  `cs` whose curve is within `(t − ℓ)·dist ≤ t·⌊δ·n⌋` of the tested curve at *every* seed `β` —
  the mutual-correlated-agreement conclusion.

The argument is exactly the paper's: `CurveDecodable.exists_curve_of_close` produces a codeword
curve agreeing with `f` on `≥ t` close seeds; on those seeds the tested curve is `δᵣ ≤ δ`-close to
the codeword curve, i.e. integer-close (`≤ ⌊δ·n⌋`); `all_seeds_close` then spreads that to every
seed via the degree-`ℓ` root bound. Axiom-clean `[propext, Classical.choice, Quot.sound]`.

**Scope.** This is the general curve-decodability ⟹ MCA mechanism (class-B2). GG25 supplies
curve-decodability for folded-RS / multiplicity / random-RS / subspace-design codes (not explicit
plain smooth-domain RS); the `δ*` open core is unaffected.
-/

open Finset Code
open scoped NNReal

namespace ProximityGap.GG25Lemma32

variable {ι : Type} [Fintype ι] [Nonempty ι] [DecidableEq ι]
variable {F : Type} [Field F] [Fintype F] [DecidableEq F]
variable {A : Type} [Fintype A] [DecidableEq A] [AddCommGroup A] [Module F A]

/-- **The `δᵣ` → integer-`D` bridge.** Relative-Hamming closeness `δᵣ(u,v) ≤ δ` (cast to `ℝ≥0`)
forces the integer Hamming distance below the floor `⌊δ·n⌋` — the clean threshold consumed by
`GG25SpreadBound.all_seeds_close`. -/
theorem hammingDist_le_floor_of_relHam_le {u v : ι → A} {δ : ℝ≥0}
    (h : ((relHammingDist u v : ℚ≥0) : ℝ≥0) ≤ δ) :
    hammingDist u v ≤ ⌊δ * (Fintype.card ι : ℝ≥0)⌋₊ := by
  have hcard : (0 : ℝ≥0) < (Fintype.card ι : ℝ≥0) := by exact_mod_cast Fintype.card_pos
  have hcast : ((relHammingDist u v : ℚ≥0) : ℝ≥0)
      = (hammingDist u v : ℝ≥0) / (Fintype.card ι : ℝ≥0) := by
    simp only [relHammingDist, NNRat.cast_div, NNRat.cast_natCast]
  rw [hcast, div_le_iff₀ hcard] at h
  exact Nat.le_floor h

/-- **[GG25] Theorem 3.3 (mutual correlated agreement from curve-decodability).** If `C` is
`(ℓ, δ, a, t)`-curve-decodable with `ℓ < t`, then for every tested stack `u` and codeword-curve
`f` whose close set reaches the threshold `a`, there is a single codeword stack `cs` whose curve
agrees with the tested curve at *every* seed up to `(t − ℓ)·dist ≤ t·⌊δ·n⌋`. -/
theorem all_seeds_close_of_curveDecodable
    {C : Set (ι → A)} {ℓ : ℕ} {δ : ℝ≥0} {a t : ℕ} (hlt : ℓ < t)
    (h : CurveDecodable (F := F) C ℓ δ a t)
    {u : Fin (ℓ + 1) → ι → A} {f : F → ι → A} (hf : ∀ α, f α ∈ C)
    (hclose : a ≤ (curveCloseSet δ u f).card) :
    ∃ cs : Fin (ℓ + 1) → ι → A, (∀ j, cs j ∈ C) ∧
      ∀ β : F, (t - ℓ) * hammingDist (comb u β) (comb cs β)
            ≤ t * ⌊δ * (Fintype.card ι : ℝ≥0)⌋₊ := by
  classical
  obtain ⟨cs, hcs, hcount⟩ := h.exists_curve_of_close hf hclose
  refine ⟨cs, hcs, fun β => ?_⟩
  set D := ⌊δ * (Fintype.card ι : ℝ≥0)⌋₊ with hD
  -- the explained close seeds inject into the integer close set of the tested vs codeword curve
  have hsub : ((curveCloseSet δ u f).filter
        (fun α => f α = fun i => ∑ j : Fin (ℓ + 1), α ^ (j : ℕ) • cs j i))
      ⊆ univ.filter (fun α : F => hammingDist (comb u α) (comb cs α) ≤ D) := by
    intro α hα
    rw [mem_filter] at hα
    obtain ⟨hαC, hαeq⟩ := hα
    simp only [curveCloseSet, mem_filter, mem_univ, true_and] at hαC
    simp only [mem_filter, mem_univ, true_and]
    have hcomb_cs : f α = comb cs α := hαeq
    rw [hcomb_cs] at hαC
    exact hammingDist_le_floor_of_relHam_le hαC
  have ht : t ≤ (univ.filter (fun α : F => hammingDist (comb u α) (comb cs α) ≤ D)).card :=
    le_trans hcount (Finset.card_le_card hsub)
  exact all_seeds_close hlt u cs ht β

end ProximityGap.GG25Lemma32

-- Axiom audit: must report only `[propext, Classical.choice, Quot.sound]` (no `sorryAx`).
#print axioms ProximityGap.GG25Lemma32.all_seeds_close_of_curveDecodable

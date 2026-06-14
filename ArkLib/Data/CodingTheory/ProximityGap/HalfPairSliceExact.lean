/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.GeneralGapCensusLaw

/-!
# The first exact monomial-slice census: the half-pair at the unique-decoding radius

The gap census law characterizes each monomial pair's bad set; the splitting ladder
lower-bounds the half-pair's by `−μ_n`, with its deepest rung at the unique-decoding
radius. This file closes that deepest rung **exactly**, at the first kernel-checkable
smooth instance:

For `F₁₇`, the smooth domain `μ₈ = ⟨2⟩` (`n = 8 = 2³`, rate `ρ = 1/4`), the half-order
pair `(X⁵, X⁴)` at agreement `a = 5 = m + 1` — the deepest reach of the `g = 1` ladder
rung, at radius `δ = 3/8 = (1 − ρ)/2`, **the unique-decoding radius exactly**:

* `bad_iff_core` — the law-badness (a degree-`< 2` explanation on `≥ 5` points) is
  equivalent to an affine-function core (`exists_eq_X_add_C_of_natDegree_le_one`),
  making the census kernel-decidable.
* `core_set_eq` — the bad set is **exactly `μ₈ = {1,2,4,8,16,15,13,9}`**, by `decide`.
* `halfPair_badSet_eq` / `halfPair_badCount` — the law-bad set equals the domain and
  the count is **exactly `8 = n`**: the splitting-ladder lower bound `n/gcd(1,n) = n`
  is **tight at its deepest rung** — the first machine-checked exact monomial-slice
  census for any smooth-domain code, sitting exactly on the unique-decoding boundary.

The flat-`n` law for half-pairs (measured at `(16,4)` by the take-over probes, predicted
by the ladder) is hereby a theorem at this instance, in its exact two-sided form. Note
`−μ₈ = μ₈` (`−1 = 2⁴ ∈ μ₈`), so the bad set is literally the domain orbit. The same
two-sided question one radius higher (`a = 4`, inside `(UDR, Johnson]`) requires the
no-joint clause (the pure-agreement census saturates at this field size: every scalar
admits a 4-point affine agreement) — the registered next rung.

All results are `sorry`-free and axiom-clean (`[propext, Classical.choice, Quot.sound]`).

## References

- Issue #357 (the ladder/census arc); `GeneralGapCensusLaw.lean` (the law),
  `SmoothLadderInstance.lean` (the lower half made tight here).
-/

set_option linter.unusedSectionVars false
set_option maxRecDepth 40000

namespace ProximityGap.HalfPairSliceExact

open Polynomial Finset
open ArkLib.ProximityGap.GeneralGapCensus

instance : Fact (Nat.Prime 17) := ⟨by norm_num⟩

abbrev F17 := ZMod 17

/-- The smooth domain `μ₈ = ⟨2⟩ ⊆ F₁₇ˣ`. -/
def H8 : Finset F17 := {1, 2, 4, 8, 16, 15, 13, 9}

/-- The decidable core: an affine explanation with `≥ 5` agreements. -/
def core (lam : F17) : Prop :=
  ∃ c₁ c₀ : F17, 5 ≤ (H8.filter (fun x => x ^ 5 + lam * x ^ 4 = c₁ * x + c₀)).card

instance (lam : F17) : Decidable (core lam) := by
  unfold core
  infer_instance

/-- The law-badness ↔ decidable-core bridge: a `natDegree ≤ 1` polynomial is an affine
function, and conversely. -/
theorem bad_iff_core (lam : F17) :
    (∃ q : Polynomial F17, q.natDegree ≤ 2 - 1 ∧
      5 ≤ (gapAgreeSet H8 5 4 lam q).card) ↔ core lam := by
  constructor
  · rintro ⟨q, hq, hcard⟩
    have hq1 : q.natDegree ≤ 1 := hq
    obtain ⟨c₁, c₀, hq_eq⟩ := exists_eq_X_add_C_of_natDegree_le_one hq1
    refine ⟨c₁, c₀, le_trans hcard (Finset.card_le_card ?_)⟩
    intro x hx
    rw [gapAgreeSet, Finset.mem_filter] at hx
    rw [Finset.mem_filter]
    refine ⟨hx.1, ?_⟩
    have heval : (C c₁ * X + C c₀ : Polynomial F17).eval x = c₁ * x + c₀ := by
      simp [eval_add, eval_mul, eval_C, eval_X]
    rw [hx.2, hq_eq, heval]
  · rintro ⟨c₁, c₀, hcard⟩
    refine ⟨C c₁ * X + C c₀, ?_, le_trans hcard (Finset.card_le_card ?_)⟩
    · show (C c₁ * X + C c₀).natDegree ≤ 1
      refine le_trans (natDegree_add_le _ _) (max_le ?_ ?_)
      · refine le_trans natDegree_mul_le ?_
        simp [natDegree_C, natDegree_X]
      · simp [natDegree_C]
    · intro x hx
      rw [Finset.mem_filter] at hx
      rw [gapAgreeSet, Finset.mem_filter]
      refine ⟨hx.1, ?_⟩
      have heval : (C c₁ * X + C c₀ : Polynomial F17).eval x = c₁ * x + c₀ := by
        simp [eval_add, eval_mul, eval_C, eval_X]
      rw [hx.2, heval]

/-- **The exact slice census, kernel-checked:** the core-bad set is exactly `μ₈`. -/
theorem core_set_eq : (Finset.univ.filter core) = H8 := by decide

open Classical in
/-- **The first exact monomial-slice census.** At the unique-decoding radius of the
rate-1/4 smooth code on `μ₈ ⊆ F₁₇`, the law-bad set of the half-order pair `(X⁵, X⁴)`
at agreement 5 is exactly the domain `μ₈`. -/
theorem halfPair_badSet_eq :
    (Finset.univ.filter (fun lam : F17 =>
      ∃ q : Polynomial F17, q.natDegree ≤ 2 - 1 ∧
        5 ≤ (gapAgreeSet H8 5 4 lam q).card)) = H8 := by
  ext lam
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  rw [bad_iff_core lam]
  constructor
  · intro h
    have hmem : lam ∈ Finset.univ.filter core :=
      Finset.mem_filter.mpr ⟨Finset.mem_univ _, h⟩
    rw [core_set_eq] at hmem
    exact hmem
  · intro h
    have hmem : lam ∈ Finset.univ.filter core := by
      rw [core_set_eq]
      exact h
    exact (Finset.mem_filter.mp hmem).2

open Classical in
/-- The count is exactly `n = 8`: the splitting-ladder lower bound is **tight at its
deepest rung**. -/
theorem halfPair_badCount :
    (Finset.univ.filter (fun lam : F17 =>
      ∃ q : Polynomial F17, q.natDegree ≤ 2 - 1 ∧
        5 ≤ (gapAgreeSet H8 5 4 lam q).card)).card = 8 := by
  rw [halfPair_badSet_eq]
  decide

/-! ## Source audit -/

#print axioms core_set_eq
#print axioms halfPair_badSet_eq
#print axioms halfPair_badCount

end ProximityGap.HalfPairSliceExact

/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.MCAGSWitness

/-!
# Issue #141 — the field-universal GS prize, reduced to a single combinatorial input

This file states the **genuine** ABF26 Grand Challenge 1 prize in its honest field-universal
`∃`-faithful-`L` form (`epsMCAgsPrizeUniversalConjecture`) and reduces it, **axiom-clean**, to one
crisp combinatorial hypothesis (`CapacityListCoveringBound`): a uniform-polynomial Guruswami–Sudan
list-size bound together with the pivot-covering and faithfulness data, valid up to capacity
`δ ≤ 1 − ρ − η`.

## Why this is the right surface (and the open core, isolated)

The prize is field-universal: the constants `c₁,c₂,c₃` are quantified **before** the field, so the
bound `(1/q)·(2^m)^{c₁}/(ρ^{c₂}·η^{c₃})` vanishes as `q → ∞`. The "inflate past 1" argument that
legitimately proves the *fixed-field* surface (`epsMCAgs_prizeBound_conjecture`) is therefore
unavailable here, and an unconstrained `∀ L` strengthening is *false* (an adversarial large list
keeps `epsMCAgs = Ω(1)`). So the honest statement is the **existence of a faithful family** meeting
the bound.

The reduction below shows that this prize follows from a single, purely combinatorial fact:

* a family `L` whose Guruswami–Sudan list size is **uniformly polynomial** (`(L u).card ≤ ℓ` with
  `ℓ/q` below the prize bound),
* which is **pivot-covering** (`PivotCovering`), and
* which is **faithful** (`epsMCA ≤ epsMCAgs`, ruling out the trivial empty family),

all valid up to the capacity radius `δ ≤ 1 − ρ − η`. Given that, the probabilistic prize bound is a
*theorem* via the proven GS error bridge `epsMCAgs_le_listSize_div_of_pivotCovering`
(`epsMCAgs ≤ ℓ/q`). The genuinely-open content is thereby pinned to exactly the *combinatorial*
statement `CapacityListCoveringBound` — the beyond-Johnson Reed–Solomon list-decoding mass bound up
to capacity, which is the open research input (no in-tree or mathlib proof exists). Nothing here
asserts that input; it is the explicit hypothesis of the reduction.

## References
- [ABF26] §1 Grand MCA Challenge; §4.5 `conj:mca-conjecture`. Tracking: Issue #141.
-/

namespace ProximityGap

open NNReal Code
open scoped ProbabilityTheory BigOperators NNReal

namespace MCAGS

variable {ι : Type} [Fintype ι] [Nonempty ι] [DecidableEq ι]
variable {F : Type} [Field F] [Fintype F] [DecidableEq F]

/-- The Reed–Solomon code at ABF26 prize rate `ρ = prizeRates j` over the evaluation `domain`. -/
noncomputable def prizeCode (domain : ι ↪ F) (j : Fin 4) : Set (ι → F) :=
  (ReedSolomon.code (domain := domain)
      ⌊(ProximityGap.prizeRates j : ℝ≥0) * (Fintype.card ι : ℝ≥0)⌋₊ : Set (ι → F))

/-- **The genuine field-universal ABF26 Grand Challenge 1 prize (`∃`-faithful-`L` form).**

One universal constant triple, quantified *before the field*, such that for every finite field `F`,
domain, prize rate `j`, gap `η > 0`, and radius `δ ≤ 1 − ρ − η` (up to capacity), there **exists a
faithful** GS family `L` (`FaithfulGSFamily`, i.e. `epsMCA ≤ epsMCAgs`, which rules out the trivial
empty family) whose GS-exposed error meets the polynomial mass bound. The constants precede the
field, so they cannot absorb `q = |F|`. Deliberately **unproved**: its proof is the beyond-Johnson
Guruswami–Sudan list-decoder mass bound up to capacity (the open prize). -/
def epsMCAgsPrizeUniversalConjecture (m : ℕ) : Prop :=
  ∃ c₁ c₂ c₃ : ℝ,
    ∀ {ι : Type} [Fintype ι] [Nonempty ι] [DecidableEq ι]
      {F : Type} [Field F] [Fintype F] [DecidableEq F]
      (domain : ι ↪ F) (j : Fin 4) (η δ : ℝ≥0),
      0 < η → (δ : ℝ) ≤ 1 - (ProximityGap.prizeRates j : ℝ) - (η : ℝ) →
      ∃ L : WordStack F (Fin 2) ι → Finset (ι → F),
        FaithfulGSFamily (F := F) (prizeCode domain j) δ L ∧
        epsMCAgs (F := F) (prizeCode domain j) δ L
          ≤ ENNReal.ofReal
              (epsMCAgsPrizeBound (Fintype.card F) m (ProximityGap.prizeRates j) η c₁ c₂ c₃)

/-- **The clean combinatorial open input.** A *uniformly polynomial* Guruswami–Sudan list size
(`(L u).card ≤ ℓ` with `ℓ/q` below the prize bound), together with the pivot-covering and
faithfulness data, valid up to capacity `δ ≤ 1 − ρ − η`. This is the beyond-Johnson Reed–Solomon
list-decoding mass bound, isolated as a single combinatorial statement. It is the genuinely open
research input (no in-tree or mathlib proof exists); it is *not asserted* here — it is the explicit
hypothesis of `epsMCAgsPrizeUniversal_of_capacityListCovering`. -/
def CapacityListCoveringBound (m : ℕ) : Prop :=
  ∃ c₁ c₂ c₃ : ℝ,
    ∀ {ι : Type} [Fintype ι] [Nonempty ι] [DecidableEq ι]
      {F : Type} [Field F] [Fintype F] [DecidableEq F]
      (domain : ι ↪ F) (j : Fin 4) (η δ : ℝ≥0),
      0 < η → (δ : ℝ) ≤ 1 - (ProximityGap.prizeRates j : ℝ) - (η : ℝ) →
      ∃ (L : WordStack F (Fin 2) ι → Finset (ι → F)) (ℓ : ℕ),
        FaithfulGSFamily (F := F) (prizeCode domain j) δ L ∧
        (∀ u, PivotCovering (F := F) (prizeCode domain j) δ L u) ∧
        (∀ u, (L u).card ≤ ℓ) ∧
        ((ℓ : ENNReal) / (Fintype.card F : ENNReal)
          ≤ ENNReal.ofReal
              (epsMCAgsPrizeBound (Fintype.card F) m (ProximityGap.prizeRates j) η c₁ c₂ c₃))

/-- **The reduction (axiom-clean): the field-universal prize follows from the combinatorial bound.**

From a faithful, pivot-covering family of uniformly-polynomial GS list size up to capacity, the
GS-exposed error meets the prize bound by the proven bridge
`epsMCAgs_le_listSize_div_of_pivotCovering` (`epsMCAgs ≤ ℓ/q`), and faithfulness is carried through
directly. This pins the open ABF26 prize to exactly `CapacityListCoveringBound` — the beyond-Johnson
list-decoding mass bound — with no `axiom` and no `sorry`. -/
theorem epsMCAgsPrizeUniversal_of_capacityListCovering (m : ℕ)
    (h : CapacityListCoveringBound m) :
    epsMCAgsPrizeUniversalConjecture m := by
  obtain ⟨c₁, c₂, c₃, hh⟩ := h
  refine ⟨c₁, c₂, c₃, ?_⟩
  intro ι _ _ _ F _ _ _ domain j η δ hη hδ
  obtain ⟨L, ℓ, hfaith, hcov, hsize, hnum⟩ := hh domain j η δ hη hδ
  refine ⟨L, hfaith, ?_⟩
  exact le_trans
    (epsMCAgs_le_listSize_div_of_pivotCovering (F := F) (prizeCode domain j) δ L ℓ hcov hsize)
    hnum

/-! ## Source audit -/

#print axioms ProximityGap.MCAGS.epsMCAgsPrizeUniversal_of_capacityListCovering

end MCAGS

end ProximityGap

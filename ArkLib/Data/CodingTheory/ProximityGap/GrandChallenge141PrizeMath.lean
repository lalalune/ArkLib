/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/

import ArkLib.Data.CodingTheory.ProximityGap.MCAGSWitness

/-!
# Genuine mathematics around the Grand Challenge 1 prize surfaces (Issue #141)

Issue #141 tracks the two open ABF26 Grand Challenge 1 conjecture surfaces:
`ProximityGap.GrandChallenges.mcaConjecture` (abstract `ε_mca`) and
`ProximityGap.MCAGS.epsMCAgs_prizeBound_conjecture` (GS-exposed). Their *uniform* form — one
universal constant triple `(c₁, c₂, c₃)` working for **all** Reed–Solomon codes at the prize
rates — is the genuinely open beyond-UDR Guruswami–Sudan list-decoder mass bound, the research
prize, and is **not** proved here (proving it would need classical GS list decoding that is not
in mathlib; cf. the in-tree §6 / list-decoding blockers).

This file writes the surrounding mathematics that *is* genuinely provable, sorry-free and
axiom-clean, so that the prize is correctly delineated rather than merely asserted:

1. **Soft probability ceilings.** `epsMCAgs_le_one` / `epsMCA_le_one`: both MCA errors are
   suprema of probabilities, hence `≤ 1`. (Used below and independently useful.)

2. **The per-input vs. uniform quantifier distinction — the heart of the prize.**
   `epsMCAgs_prizeBound_conjecture` packages its constants *inside* the per-input `Prop`
   (`∃ c₁ c₂ c₃, …` for fixed code/rate/radius), whereas `mcaConjecture` correctly places them
   *outside* the `∀` (one triple for every code). We prove
   `epsMCAgs_prizeBound_conjecture_holds`: the **per-input** GS form is a theorem — for any
   single instance one may inflate the bound past `1` by taking the `η`-exponent large (`η < 1`
   in the prize regime), and `epsMCAgs ≤ 1`. Hence the per-input surface does **not** capture the
   prize; the open content lives entirely in the *uniformity* of the constants. We record the
   honest uniform GS surface as `epsMCAgsPrizeUniformConjecture` (a named `Prop`, **unproved** —
   the actual #141 prize), mirroring `mcaConjecture`'s outside-the-`∀` quantification.

3. **An explicit-constant conditional reduction.** `epsMCAgs_prizeBound_of_listSize_clears`
   derives the per-input conjecture from the proven `epsMCAgs ≤ ℓ/q` pivot-covering bound plus a
   single numeric clearance hypothesis, with the open beyond-UDR content isolated into the named
   list-size + covering inputs (no laundering).

None of this proves either tracked conjecture; it sharpens *which* statement is the open prize.

## References

- [ABF26] §1 Grand MCA Challenge; §4.5 `conj:mca-conjecture`.
- Tracking: Issue #141.
-/

set_option linter.unusedFintypeInType false
set_option linter.unusedDecidableInType false
set_option linter.unusedSectionVars false

namespace ProximityGap

open NNReal Code
open scoped ProbabilityTheory BigOperators

namespace MCAGS

/-! ## 1. Soft probability ceilings -/

section Ceilings

variable {ι : Type} [Fintype ι] [Nonempty ι] [DecidableEq ι]
variable {F : Type} [Field F] [Fintype F] [DecidableEq F]
variable {A : Type} [Fintype A] [DecidableEq A] [AddCommGroup A] [Module F A]

open Classical in
/-- **The GS-exposed MCA error is a probability ceiling: `epsMCAgs ≤ 1`.** It is a supremum of
`γ`-probabilities of `mcaEventGSrow`, each `≤ 1`. (Issue #141: a soft universal ceiling on the
prize surface, independent of any list-size estimate.) -/
theorem epsMCAgs_le_one (C : Set (ι → A)) (δ : ℝ≥0)
    (L : WordStack A (Fin 2) ι → Finset (ι → A)) :
    epsMCAgs (F := F) C δ L ≤ 1 := by
  unfold epsMCAgs
  exact iSup_le fun u => Pr_le_one _ _

end Ceilings

section CeilingAbstract

variable {ι : Type} [Fintype ι] [Nonempty ι] [DecidableEq ι]
variable {F : Type} [Field F] [Fintype F] [DecidableEq F]
variable {A : Type} [Fintype A] [DecidableEq A] [AddCommGroup A] [Module F A]

open Classical in
/-- **The abstract MCA error is a probability ceiling: `ε_mca ≤ 1`.** (Companion to
`epsMCAgs_le_one`; the abstract prize surface is likewise bounded by `1`.) -/
theorem epsMCA_le_one (C : Set (ι → A)) (δ : ℝ≥0) :
    epsMCA (F := F) (A := A) C δ ≤ 1 := by
  unfold epsMCA
  exact iSup_le fun u => Pr_le_one _ _

end CeilingAbstract

/-! ## 2. The per-input GS prize form is a theorem; the uniform form is the open prize -/

section PerInput

variable {ι : Type} [Fintype ι] [Nonempty ι] [DecidableEq ι]
variable {F : Type} [Field F] [Fintype F] [DecidableEq F]

open scoped NNReal

/-- A prize rate is strictly positive: `prizeRates j = 1 / 2^(j+1) > 0`. -/
theorem prizeRates_pos (j : Fin 4) : 0 < ProximityGap.prizeRates j := by
  unfold ProximityGap.prizeRates
  positivity

/-- In the prize regime the gap `η` is strictly below `1`: the radius constraint
`δ ≤ 1 - ρ - η` with `δ ≥ 0` and `ρ > 0` forces `η < 1`. -/
theorem eta_lt_one_of_prize (j : Fin 4) (η δ : ℝ≥0)
    (hδ : (δ : ℝ) ≤ 1 - (ProximityGap.prizeRates j : ℝ) - (η : ℝ)) :
    (η : ℝ) < 1 := by
  have hρpos : (0 : ℝ) < (ProximityGap.prizeRates j : ℝ) := by
    exact_mod_cast prizeRates_pos j
  have hδ0 : (0 : ℝ) ≤ (δ : ℝ) := (δ : ℝ≥0).coe_nonneg
  linarith

open Classical in
/-- **The per-input GS-exposed prize conjecture is a theorem.**

`epsMCAgs_prizeBound_conjecture` quantifies its constants *inside* the per-input `Prop`. For any
single instance the bound `(1/q)·(2^m)^{c₁}/(ρ^{c₂}·η^{c₃})` can be inflated past `1` by taking
`c₃` large — `η < 1` in the prize regime, so `η^{c₃} → 0` — while `epsMCAgs ≤ 1`. Hence the
per-input form holds with explicit constants `c₁ = c₂ = 0`, `c₃ = n` for a suitable `n`.

This is **not** a proof of the prize: it shows the per-input packaging does not capture it. The
open prize is the *uniform* form `epsMCAgsPrizeUniformConjecture` (one constant triple for all
inputs), mirroring `mcaConjecture`. Tracking: Issue #141. -/
theorem epsMCAgs_prizeBound_conjecture_holds
    (domain : ι ↪ F) (j : Fin 4) (m : ℕ) (η δ : ℝ≥0) (hη : 0 < η)
    (L : WordStack F (Fin 2) ι → Finset (ι → F))
    (hδ : (δ : ℝ) ≤ 1 - (ProximityGap.prizeRates j : ℝ) - (η : ℝ)) :
    epsMCAgs_prizeBound_conjecture domain j m η δ hη L hδ := by
  have hηlt1 : (η : ℝ) < 1 := eta_lt_one_of_prize j η δ hδ
  have hqpos : (0 : ℝ) < (Fintype.card F : ℝ) := by exact_mod_cast Fintype.card_pos
  -- pick `n` with `η^n < 1/q`
  obtain ⟨n, hn⟩ := exists_pow_lt_of_lt_one (by positivity : (0 : ℝ) < 1 / (Fintype.card F : ℝ)) hηlt1
  have hηpow_pos : (0 : ℝ) < (η : ℝ) ^ n := by
    have : (0 : ℝ) < (η : ℝ) := by exact_mod_cast hη
    positivity
  refine ⟨0, 0, (n : ℝ), ?_⟩
  -- the bound is `≥ 1`
  have hbound : (1 : ℝ) ≤
      epsMCAgsPrizeBound (Fintype.card F) m (ProximityGap.prizeRates j) η 0 0 (n : ℝ) := by
    unfold epsMCAgsPrizeBound
    rw [Real.rpow_zero, Real.rpow_zero, Real.rpow_natCast, mul_one, one_mul]
    rw [le_div_iff₀ hηpow_pos, one_mul]
    exact hn.le
  have hofr : (1 : ENNReal) ≤ ENNReal.ofReal
      (epsMCAgsPrizeBound (Fintype.card F) m (ProximityGap.prizeRates j) η 0 0 (n : ℝ)) := by
    rw [← ENNReal.ofReal_one]
    exact ENNReal.ofReal_le_ofReal hbound
  exact le_trans (epsMCAgs_le_one _ _ _) hofr

/-- **The honest open GS-exposed prize (Issue #141).** The *uniform* GS-exposed Grand Challenge 1
bound: one universal constant triple `(c₁, c₂, c₃)` such that for **every** prize rate `j`, gap
`η`, radius `δ ≤ 1 - ρ - η`, interleaving exponent `m`, evaluation domain, and GS list family,
the GS-exposed MCA error is within `epsMCAgsPrizeBound`. The constants are quantified *before* the
data, exactly as `mcaConjecture` does for the abstract error — this is the quantifier order that
makes the statement the open prize rather than the per-input theorem
`epsMCAgs_prizeBound_conjecture_holds`.

This is a named `Prop`, deliberately **unproved**: its proof is the beyond-UDR Guruswami–Sudan
list-decoder mass bound. Downstream developments must take it as an explicit hypothesis. Do not
launder it into a theorem by assuming an equivalent packaged form. Tracking: Issue #141. -/
def epsMCAgsPrizeUniformConjecture
    {ι : Type} [Fintype ι] [Nonempty ι] [DecidableEq ι]
    {F : Type} [Field F] [Fintype F] [DecidableEq F]
    (domain : ι ↪ F) (m : ℕ) : Prop :=
  ∃ c₁ c₂ c₃ : ℝ,
    ∀ (j : Fin 4) (η δ : ℝ≥0),
      0 < η →
      (δ : ℝ) ≤ 1 - (ProximityGap.prizeRates j : ℝ) - (η : ℝ) →
      ∀ L : WordStack F (Fin 2) ι → Finset (ι → F),
        epsMCAgs (F := F)
          ((ReedSolomon.code (domain := domain)
            ⌊(ProximityGap.prizeRates j : ℝ≥0) * (Fintype.card ι : ℝ≥0)⌋₊ : Set (ι → F))) δ L
        ≤ ENNReal.ofReal
            (epsMCAgsPrizeBound (Fintype.card F) m (ProximityGap.prizeRates j) η c₁ c₂ c₃)

/-- The honest uniform GS-exposed prize immediately supplies the legacy per-input
`epsMCAgs_prizeBound_conjecture` surface, with the same constant triple. This is only an adapter:
the uniform conjecture remains an explicit hypothesis. -/
theorem epsMCAgs_prizeBound_conjecture_of_uniformConjecture
    (domain : ι ↪ F) (m : ℕ)
    (hUniform : epsMCAgsPrizeUniformConjecture domain m)
    (j : Fin 4) (η δ : ℝ≥0) (hη : 0 < η)
    (L : WordStack F (Fin 2) ι → Finset (ι → F))
    (hδ : (δ : ℝ) ≤ 1 - (ProximityGap.prizeRates j : ℝ) - (η : ℝ)) :
    epsMCAgs_prizeBound_conjecture domain j m η δ hη L hδ := by
  rcases hUniform with ⟨c₁, c₂, c₃, hbound⟩
  exact ⟨c₁, c₂, c₃, hbound j η δ hη hδ L⟩

/-- The honest uniform GS-exposed prize supplies the existing mass-bound API uniformly in the
prize parameters: the same constant triple works for every rate, gap, radius, and list family.
This keeps the uniform conjecture as an explicit hypothesis while routing it into
`epsMCAgsMassBound`. -/
theorem exists_uniform_epsMCAgsMassBound_of_uniformConjecture
    (domain : ι ↪ F) (m : ℕ)
    (hUniform : epsMCAgsPrizeUniformConjecture domain m) :
    ∃ c₁ c₂ c₃ : ℝ,
      ∀ (j : Fin 4) (η δ : ℝ≥0),
        0 < η →
        (δ : ℝ) ≤ 1 - (ProximityGap.prizeRates j : ℝ) - (η : ℝ) →
        ∀ L : WordStack F (Fin 2) ι → Finset (ι → F),
          epsMCAgsMassBound (F := F)
            ((ReedSolomon.code (domain := domain)
              ⌊(ProximityGap.prizeRates j : ℝ≥0) * (Fintype.card ι : ℝ≥0)⌋₊ :
                Set (ι → F))) δ L
            (ENNReal.ofReal
              (epsMCAgsPrizeBound (Fintype.card F) m (ProximityGap.prizeRates j) η c₁ c₂ c₃)) := by
  rcases hUniform with ⟨c₁, c₂, c₃, hbound⟩
  refine ⟨c₁, c₂, c₃, ?_⟩
  intro j η δ hη hδ L
  exact epsMCAgsMassBound_of_epsMCAgs_le
    ((ReedSolomon.code (domain := domain)
      ⌊(ProximityGap.prizeRates j : ℝ≥0) * (Fintype.card ι : ℝ≥0)⌋₊ :
        Set (ι → F))) δ L
    (hbound j η δ hη hδ L)

/-- A uniform `epsMCAgsMassBound` constant triple supplies the honest uniform GS-exposed prize
surface with the same constants. This is the reverse adapter to
`exists_uniform_epsMCAgsMassBound_of_uniformConjecture`; it does not prove the mass bound. -/
theorem epsMCAgsPrizeUniformConjecture_of_uniform_epsMCAgsMassBound
    (domain : ι ↪ F) (m : ℕ)
    (hMass : ∃ c₁ c₂ c₃ : ℝ,
      ∀ (j : Fin 4) (η δ : ℝ≥0),
        0 < η →
        (δ : ℝ) ≤ 1 - (ProximityGap.prizeRates j : ℝ) - (η : ℝ) →
        ∀ L : WordStack F (Fin 2) ι → Finset (ι → F),
          epsMCAgsMassBound (F := F)
            ((ReedSolomon.code (domain := domain)
              ⌊(ProximityGap.prizeRates j : ℝ≥0) * (Fintype.card ι : ℝ≥0)⌋₊ :
                Set (ι → F))) δ L
            (ENNReal.ofReal
              (epsMCAgsPrizeBound (Fintype.card F) m (ProximityGap.prizeRates j) η c₁ c₂ c₃))) :
    epsMCAgsPrizeUniformConjecture domain m := by
  rcases hMass with ⟨c₁, c₂, c₃, hbound⟩
  refine ⟨c₁, c₂, c₃, ?_⟩
  intro j η δ hη hδ L
  exact epsMCAgs_le_of_massBound
    ((ReedSolomon.code (domain := domain)
      ⌊(ProximityGap.prizeRates j : ℝ≥0) * (Fintype.card ι : ℝ≥0)⌋₊ :
        Set (ι → F))) δ L
    (hbound j η δ hη hδ L)

/-- The honest uniform GS-exposed prize is equivalent to the uniform per-stack GS-row mass-bound
API, with the constant triple quantified before all prize inputs on both sides. This is a pure
API equivalence; the uniform prize remains an explicit hypothesis. -/
theorem epsMCAgsPrizeUniformConjecture_iff_uniform_epsMCAgsMassBound
    (domain : ι ↪ F) (m : ℕ) :
    epsMCAgsPrizeUniformConjecture domain m ↔
      ∃ c₁ c₂ c₃ : ℝ,
        ∀ (j : Fin 4) (η δ : ℝ≥0),
          0 < η →
          (δ : ℝ) ≤ 1 - (ProximityGap.prizeRates j : ℝ) - (η : ℝ) →
          ∀ L : WordStack F (Fin 2) ι → Finset (ι → F),
            epsMCAgsMassBound (F := F)
              ((ReedSolomon.code (domain := domain)
                ⌊(ProximityGap.prizeRates j : ℝ≥0) * (Fintype.card ι : ℝ≥0)⌋₊ :
                  Set (ι → F))) δ L
              (ENNReal.ofReal
                (epsMCAgsPrizeBound (Fintype.card F) m (ProximityGap.prizeRates j)
                  η c₁ c₂ c₃)) := by
  constructor
  · intro hUniform
    exact exists_uniform_epsMCAgsMassBound_of_uniformConjecture domain m hUniform
  · intro hMass
    exact epsMCAgsPrizeUniformConjecture_of_uniform_epsMCAgsMassBound domain m hMass

end PerInput

/-! ## 3. Explicit-constant conditional reduction (open content named, no laundering) -/

section Reduction

variable {ι : Type} [Fintype ι] [Nonempty ι] [DecidableEq ι]
variable {F : Type} [Field F] [Fintype F] [DecidableEq F]

open scoped NNReal

/-- **Per-input prize from the proven pivot-covering bound plus a numeric clearance.**

Under the (open, beyond-UDR) inputs — a uniform GS list size `ℓ`, per-stack pivot covering, and
the single numeric clearance `ℓ/q ≤ epsMCAgsPrizeBound … c₁ c₂ c₃` for explicit constants — the
per-input GS prize conjecture follows from the **proved** `epsMCAgs_le_listSize_div_of_pivotCovering`
(`MCAGSWitness`). The genuinely open content is isolated into the named list-size/covering
hypotheses; the assembly is sorry-free `le_trans`. No laundering: the conjecture's existential is
discharged only relative to these explicit external inputs. Tracking: Issue #141. -/
theorem epsMCAgs_prizeBound_of_listSize_clears
    (domain : ι ↪ F) (j : Fin 4) (m : ℕ) (η δ : ℝ≥0) (hη : 0 < η)
    (L : WordStack F (Fin 2) ι → Finset (ι → F))
    (hδ : (δ : ℝ) ≤ 1 - (ProximityGap.prizeRates j : ℝ) - (η : ℝ))
    (ℓ : ℕ) (c₁ c₂ c₃ : ℝ)
    (hcov : ∀ u, PivotCovering (F := F)
      ((ReedSolomon.code (domain := domain)
        ⌊(ProximityGap.prizeRates j : ℝ≥0) * (Fintype.card ι : ℝ≥0)⌋₊ : Set (ι → F))) δ L u)
    (hsize : ∀ u, (L u).card ≤ ℓ)
    (hclear : ((ℓ : ENNReal) / (Fintype.card F : ENNReal)) ≤
      ENNReal.ofReal
        (epsMCAgsPrizeBound (Fintype.card F) m (ProximityGap.prizeRates j) η c₁ c₂ c₃)) :
    epsMCAgs_prizeBound_conjecture domain j m η δ hη L hδ :=
  ⟨c₁, c₂, c₃,
    le_trans
      (epsMCAgs_le_listSize_div_of_pivotCovering
        (F := F) _ δ L ℓ hcov hsize)
      hclear⟩

end Reduction

/-! ## Source audit -/

#print axioms epsMCAgs_le_one
#print axioms epsMCA_le_one
#print axioms epsMCAgs_prizeBound_conjecture_holds
#print axioms epsMCAgs_prizeBound_conjecture_of_uniformConjecture
#print axioms exists_uniform_epsMCAgsMassBound_of_uniformConjecture
#print axioms epsMCAgsPrizeUniformConjecture_of_uniform_epsMCAgsMassBound
#print axioms epsMCAgsPrizeUniformConjecture_iff_uniform_epsMCAgsMassBound
#print axioms epsMCAgs_prizeBound_of_listSize_clears

end MCAGS

end ProximityGap

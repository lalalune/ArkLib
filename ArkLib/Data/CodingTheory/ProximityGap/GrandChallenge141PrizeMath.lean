/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/

import ArkLib.Data.CodingTheory.ProximityGap.GrandChallengesLatticePrizeSpec
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
  obtain ⟨n, hn⟩ :=
    exists_pow_lt_of_lt_one
      (by positivity : (0 : ℝ) < 1 / (Fintype.card F : ℝ)) hηlt1
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

/-- The honest uniform GS-exposed prize, plus the still-explicit GS faithfulness and numeric
clearance hypotheses, produces a one-sided lower witness at the ABF26 prize-rate radius.

This is the lower-witness-facing specialization of
`exists_uniform_epsMCAgsMassBound_of_uniformConjecture`: the uniform conjecture supplies the
GS-exposed mass bound with one constant triple, `hclear` routes that bound to `epsStar`, and
`hfaithful` transfers the GS-exposed error back to the abstract MCA error. No open content is
hidden: uniformity, faithfulness, and numeric clearance are all explicit inputs. -/
theorem exists_prize_mcaLowerWitness_of_uniformConjecture
    (domain : ι ↪ F) (m : ℕ)
    (hUniform : epsMCAgsPrizeUniformConjecture domain m) :
    ∃ c₁ c₂ c₃ : ℝ,
      ∀ (j : Fin 4) (η δ : ℝ≥0),
        0 < η →
        (δ : ℝ) ≤ 1 - (ProximityGap.prizeRates j : ℝ) - (η : ℝ) →
        δ ≤ 1 →
        ∀ L : WordStack F (Fin 2) ι → Finset (ι → F),
          FaithfulGSFamily (F := F)
            ((ReedSolomon.code (domain := domain)
              ⌊(ProximityGap.prizeRates j : ℝ≥0) * (Fintype.card ι : ℝ≥0)⌋₊ :
                Set (ι → F))) δ L →
          ENNReal.ofReal
              (epsMCAgsPrizeBound (Fintype.card F) m (ProximityGap.prizeRates j)
                η c₁ c₂ c₃)
            ≤ (epsStar : ENNReal) →
          ∃ w : GrandChallenges.MCALowerWitness
            ((ReedSolomon.code (domain := domain)
              ⌊(ProximityGap.prizeRates j : ℝ≥0) * (Fintype.card ι : ℝ≥0)⌋₊ :
                Set (ι → F))) epsStar,
            w.δ = δ := by
  rcases hUniform with ⟨c₁, c₂, c₃, hbound⟩
  refine ⟨c₁, c₂, c₃, ?_⟩
  intro j η δ hη hδ hδ_le_one L hfaithful hclear
  let C : Set (ι → F) :=
    (ReedSolomon.code (domain := domain)
      ⌊(ProximityGap.prizeRates j : ℝ≥0) * (Fintype.card ι : ℝ≥0)⌋₊ : Set (ι → F))
  have hMassUniform : epsMCAgsMassBound (F := F) C δ L
      (ENNReal.ofReal
        (epsMCAgsPrizeBound (Fintype.card F) m (ProximityGap.prizeRates j)
          η c₁ c₂ c₃)) :=
    epsMCAgsMassBound_of_epsMCAgs_le C δ L (hbound j η δ hη hδ L)
  have hMassStar : epsMCAgsMassBound (F := F) C δ L (epsStar : ENNReal) :=
    epsMCAgsMassBound.mono hMassUniform hclear
  refine ⟨GrandChallenges.MCALowerWitness.ofLe (C := C) (ε_star := epsStar) (δ := δ)
    hδ_le_one ?_, rfl⟩
  exact epsMCA_le_of_faithful_mass (F := F) C δ L hfaithful hMassStar

/-- The honest uniform GS-exposed prize supplies a four-rate family of lower witnesses with one
shared constant triple. This is the all-prize-rate packaging of
`exists_prize_mcaLowerWitness_of_uniformConjecture`: every open input remains explicit, but
downstream lattice-prize code can consume the resulting `∀ j` witness family directly. -/
theorem exists_prize_mcaLowerWitnesses_allRates_of_uniformConjecture
    (domain : ι ↪ F) (m : ℕ)
    (hUniform : epsMCAgsPrizeUniformConjecture domain m) :
    ∃ c₁ c₂ c₃ : ℝ,
      ∀ (η δ : Fin 4 → ℝ≥0),
        (∀ j : Fin 4, 0 < η j) →
        (∀ j : Fin 4,
          (δ j : ℝ) ≤ 1 - (ProximityGap.prizeRates j : ℝ) - (η j : ℝ)) →
        (∀ j : Fin 4, δ j ≤ 1) →
        ∀ L : ∀ _ : Fin 4, WordStack F (Fin 2) ι → Finset (ι → F),
          (∀ j : Fin 4,
            FaithfulGSFamily (F := F)
              ((ReedSolomon.code (domain := domain)
                ⌊(ProximityGap.prizeRates j : ℝ≥0) * (Fintype.card ι : ℝ≥0)⌋₊ :
                  Set (ι → F))) (δ j) (L j)) →
          (∀ j : Fin 4,
            ENNReal.ofReal
                (epsMCAgsPrizeBound (Fintype.card F) m (ProximityGap.prizeRates j)
                  (η j) c₁ c₂ c₃)
              ≤ (epsStar : ENNReal)) →
          ∀ j : Fin 4,
            ∃ w : GrandChallenges.MCALowerWitness
              ((ReedSolomon.code (domain := domain)
                ⌊(ProximityGap.prizeRates j : ℝ≥0) * (Fintype.card ι : ℝ≥0)⌋₊ :
                  Set (ι → F))) epsStar,
              w.δ = δ j := by
  rcases exists_prize_mcaLowerWitness_of_uniformConjecture domain m hUniform with
    ⟨c₁, c₂, c₃, hlower⟩
  refine ⟨c₁, c₂, c₃, ?_⟩
  intro η δ hη hδ hδ_le_one L hfaithful hclear j
  exact hlower j (η j) (δ j) (hη j) (hδ j) (hδ_le_one j) (L j)
    (hfaithful j) (hclear j)

/-- The honest uniform GS-exposed prize, plus explicit GS faithfulness and numeric clearance
hypotheses at all four prize rates, supplies a faithful MCA prize-lattice resolution together with
the satisfy/maximality specification for the selected thresholds.

This is the lattice/spec aggregation of
`exists_prize_mcaLowerWitnesses_allRates_of_uniformConjecture`: it chooses the all-rate lower
witnesses and feeds them through the generic faithful lattice-prize spec API. The uniform GS prize,
faithfulness, and numeric clearance remain explicit hypotheses. -/
theorem exists_mcaPrizeLatticeResolved_with_spec_of_uniformConjecture
    (domain : ι ↪ F) (m : ℕ)
    (hUniform : epsMCAgsPrizeUniformConjecture domain m) :
    ∃ c₁ c₂ c₃ : ℝ,
      ∀ (η δ : Fin 4 → ℝ≥0),
        (∀ j : Fin 4, 0 < η j) →
        (∀ j : Fin 4,
          (δ j : ℝ) ≤ 1 - (ProximityGap.prizeRates j : ℝ) - (η j : ℝ)) →
        (∀ j : Fin 4, δ j ≤ 1) →
        ∀ L : ∀ _ : Fin 4, WordStack F (Fin 2) ι → Finset (ι → F),
          (∀ j : Fin 4,
            FaithfulGSFamily (F := F)
              ((ReedSolomon.code (domain := domain)
                ⌊(ProximityGap.prizeRates j : ℝ≥0) * (Fintype.card ι : ℝ≥0)⌋₊ :
                  Set (ι → F))) (δ j) (L j)) →
          (∀ j : Fin 4,
            ENNReal.ofReal
                (epsMCAgsPrizeBound (Fintype.card F) m (ProximityGap.prizeRates j)
                  (η j) c₁ c₂ c₃)
              ≤ (epsStar : ENNReal)) →
          ∃ τ : Fin 4 → Fin (Fintype.card ι + 1),
            GrandChallengesLattice.mcaPrizeLatticeResolved domain τ ∧
              ∀ j : Fin 4,
                let C : Set (ι → F) :=
                  ReedSolomon.code domain
                    ⌊ProximityGap.prizeRates j * (Fintype.card ι : ℝ≥0)⌋₊
                ∃ _ : GrandChallengesLattice.mcaThresholdExists C epsStar,
                  GrandChallengesLattice.mcaSatisfies C epsStar (τ j) ∧
                    ∀ i : Fin (Fintype.card ι + 1),
                      GrandChallengesLattice.mcaSatisfies C epsStar i → i ≤ τ j := by
  rcases exists_prize_mcaLowerWitnesses_allRates_of_uniformConjecture domain m hUniform with
    ⟨c₁, c₂, c₃, hlower⟩
  refine ⟨c₁, c₂, c₃, ?_⟩
  intro η δ hη hδ hδ_le_one L hfaithful hclear
  have hw : ∀ j : Fin 4,
      ∃ w : GrandChallenges.MCALowerWitness
        ((ReedSolomon.code (domain := domain)
          ⌊(ProximityGap.prizeRates j : ℝ≥0) * (Fintype.card ι : ℝ≥0)⌋₊ :
            Set (ι → F))) epsStar,
        w.δ = δ j :=
    hlower η δ hη hδ hδ_le_one L hfaithful hclear
  let w : ∀ j : Fin 4,
      GrandChallenges.MCALowerWitness
        ((ReedSolomon.code (domain := domain)
          ⌊(ProximityGap.prizeRates j : ℝ≥0) * (Fintype.card ι : ℝ≥0)⌋₊ :
            Set (ι → F))) epsStar :=
    fun j => Classical.choose (hw j)
  exact GrandChallengesLattice.exists_mcaPrizeLatticeResolved_with_spec_of_lowerWitnesses
    domain w

/-- The honest uniform GS-exposed prize, plus explicit GS faithfulness and numeric clearance
hypotheses at all four prize rates, supplies a faithful MCA prize-lattice resolution.

This is the plain-existential projection of
`exists_mcaPrizeLatticeResolved_with_spec_of_uniformConjecture`: consumers that do not need the
selected-threshold satisfy/maximality specification can target only
`mcaPrizeLatticeResolved`, while the uniform GS prize, faithfulness, and clearance hypotheses
remain explicit. -/
theorem exists_mcaPrizeLatticeResolved_of_uniformConjecture
    (domain : ι ↪ F) (m : ℕ)
    (hUniform : epsMCAgsPrizeUniformConjecture domain m) :
    ∃ c₁ c₂ c₃ : ℝ,
      ∀ (η δ : Fin 4 → ℝ≥0),
        (∀ j : Fin 4, 0 < η j) →
        (∀ j : Fin 4,
          (δ j : ℝ) ≤ 1 - (ProximityGap.prizeRates j : ℝ) - (η j : ℝ)) →
        (∀ j : Fin 4, δ j ≤ 1) →
        ∀ L : ∀ _ : Fin 4, WordStack F (Fin 2) ι → Finset (ι → F),
          (∀ j : Fin 4,
            FaithfulGSFamily (F := F)
              ((ReedSolomon.code (domain := domain)
                ⌊(ProximityGap.prizeRates j : ℝ≥0) * (Fintype.card ι : ℝ≥0)⌋₊ :
                  Set (ι → F))) (δ j) (L j)) →
          (∀ j : Fin 4,
            ENNReal.ofReal
                (epsMCAgsPrizeBound (Fintype.card F) m (ProximityGap.prizeRates j)
                  (η j) c₁ c₂ c₃)
              ≤ (epsStar : ENNReal)) →
          ∃ τ : Fin 4 → Fin (Fintype.card ι + 1),
            GrandChallengesLattice.mcaPrizeLatticeResolved domain τ := by
  rcases exists_mcaPrizeLatticeResolved_with_spec_of_uniformConjecture domain m hUniform with
    ⟨c₁, c₂, c₃, hresolved⟩
  refine ⟨c₁, c₂, c₃, ?_⟩
  intro η δ hη hδ hδ_le_one L hfaithful hclear
  rcases hresolved η δ hη hδ hδ_le_one L hfaithful hclear with ⟨τ, hτ, _⟩
  exact ⟨τ, hτ⟩

/-- The honest uniform GS-exposed prize, plus explicit GS faithfulness and numeric clearance
hypotheses at all four prize rates, supplies the per-rate threshold satisfy/maximality
specification for the selected MCA prize-lattice thresholds.

This is the spec-only projection of
`exists_mcaPrizeLatticeResolved_with_spec_of_uniformConjecture`: consumers that already obtain or
do not need the faithful lattice-resolution predicate can use only the selected-threshold
specification under the same explicit uniform GS prize, faithfulness, and clearance hypotheses. -/
theorem exists_mcaPrizeLatticeSpec_of_uniformConjecture
    (domain : ι ↪ F) (m : ℕ)
    (hUniform : epsMCAgsPrizeUniformConjecture domain m) :
    ∃ c₁ c₂ c₃ : ℝ,
      ∀ (η δ : Fin 4 → ℝ≥0),
        (∀ j : Fin 4, 0 < η j) →
        (∀ j : Fin 4,
          (δ j : ℝ) ≤ 1 - (ProximityGap.prizeRates j : ℝ) - (η j : ℝ)) →
        (∀ j : Fin 4, δ j ≤ 1) →
        ∀ L : ∀ _ : Fin 4, WordStack F (Fin 2) ι → Finset (ι → F),
          (∀ j : Fin 4,
            FaithfulGSFamily (F := F)
              ((ReedSolomon.code (domain := domain)
                ⌊(ProximityGap.prizeRates j : ℝ≥0) * (Fintype.card ι : ℝ≥0)⌋₊ :
                  Set (ι → F))) (δ j) (L j)) →
          (∀ j : Fin 4,
            ENNReal.ofReal
                (epsMCAgsPrizeBound (Fintype.card F) m (ProximityGap.prizeRates j)
                  (η j) c₁ c₂ c₃)
              ≤ (epsStar : ENNReal)) →
          ∃ τ : Fin 4 → Fin (Fintype.card ι + 1),
            ∀ j : Fin 4,
              let C : Set (ι → F) :=
                ReedSolomon.code domain
                  ⌊ProximityGap.prizeRates j * (Fintype.card ι : ℝ≥0)⌋₊
              ∃ _ : GrandChallengesLattice.mcaThresholdExists C epsStar,
                GrandChallengesLattice.mcaSatisfies C epsStar (τ j) ∧
                  ∀ i : Fin (Fintype.card ι + 1),
                    GrandChallengesLattice.mcaSatisfies C epsStar i → i ≤ τ j := by
  rcases exists_mcaPrizeLatticeResolved_with_spec_of_uniformConjecture domain m hUniform with
    ⟨c₁, c₂, c₃, hresolved⟩
  refine ⟨c₁, c₂, c₃, ?_⟩
  intro η δ hη hδ hδ_le_one L hfaithful hclear
  rcases hresolved η δ hη hδ hδ_le_one L hfaithful hclear with ⟨τ, _, hspec⟩
  exact ⟨τ, hspec⟩

/-- The honest uniform GS-exposed prize, plus explicit GS faithfulness and numeric clearance,
supplies the all-rate selected-threshold specification together with the lower lattice brackets
`latticeIndexOf (δ j) ≤ τ j`.

This strengthens the spec-only projection by keeping the lower witnesses used in the aggregation
visible long enough to derive the per-rate lower bracket from threshold maximality. The uniform GS
prize, faithfulness, and clearance hypotheses remain explicit. -/
theorem exists_mcaPrizeLatticeSpec_and_lower_brackets_of_uniformConjecture
    (domain : ι ↪ F) (m : ℕ)
    (hUniform : epsMCAgsPrizeUniformConjecture domain m) :
    ∃ c₁ c₂ c₃ : ℝ,
      ∀ (η δ : Fin 4 → ℝ≥0),
        (∀ j : Fin 4, 0 < η j) →
        (∀ j : Fin 4,
          (δ j : ℝ) ≤ 1 - (ProximityGap.prizeRates j : ℝ) - (η j : ℝ)) →
        (hδ_le_one : ∀ j : Fin 4, δ j ≤ 1) →
        ∀ L : ∀ _ : Fin 4, WordStack F (Fin 2) ι → Finset (ι → F),
          (∀ j : Fin 4,
            FaithfulGSFamily (F := F)
              ((ReedSolomon.code (domain := domain)
                ⌊(ProximityGap.prizeRates j : ℝ≥0) * (Fintype.card ι : ℝ≥0)⌋₊ :
                  Set (ι → F))) (δ j) (L j)) →
          (∀ j : Fin 4,
            ENNReal.ofReal
                (epsMCAgsPrizeBound (Fintype.card F) m (ProximityGap.prizeRates j)
                  (η j) c₁ c₂ c₃)
              ≤ (epsStar : ENNReal)) →
          ∃ τ : Fin 4 → Fin (Fintype.card ι + 1),
            (∀ j : Fin 4,
              let C : Set (ι → F) :=
                ReedSolomon.code domain
                  ⌊ProximityGap.prizeRates j * (Fintype.card ι : ℝ≥0)⌋₊
              ∃ _ : GrandChallengesLattice.mcaThresholdExists C epsStar,
                GrandChallengesLattice.mcaSatisfies C epsStar (τ j) ∧
                  ∀ i : Fin (Fintype.card ι + 1),
                    GrandChallengesLattice.mcaSatisfies C epsStar i → i ≤ τ j) ∧
              ∀ j : Fin 4,
                GrandChallengesLattice.latticeIndexOf (ι := ι) (δ j) (hδ_le_one j) ≤
                  τ j := by
  rcases exists_prize_mcaLowerWitnesses_allRates_of_uniformConjecture domain m hUniform with
    ⟨c₁, c₂, c₃, hlower⟩
  refine ⟨c₁, c₂, c₃, ?_⟩
  intro η δ hη hδ hδ_le_one L hfaithful hclear
  have hw : ∀ j : Fin 4,
      ∃ w : GrandChallenges.MCALowerWitness
        ((ReedSolomon.code (domain := domain)
          ⌊(ProximityGap.prizeRates j : ℝ≥0) * (Fintype.card ι : ℝ≥0)⌋₊ :
            Set (ι → F))) epsStar,
        w.δ = δ j :=
    hlower η δ hη hδ hδ_le_one L hfaithful hclear
  let w : ∀ j : Fin 4,
      GrandChallenges.MCALowerWitness
        ((ReedSolomon.code (domain := domain)
          ⌊(ProximityGap.prizeRates j : ℝ≥0) * (Fintype.card ι : ℝ≥0)⌋₊ :
            Set (ι → F))) epsStar :=
    fun j => Classical.choose (hw j)
  have hδw : ∀ j : Fin 4, (w j).δ = δ j :=
    fun j => Classical.choose_spec (hw j)
  rcases GrandChallengesLattice.exists_mcaPrizeLatticeResolved_with_spec_of_lowerWitnesses
      domain w with ⟨τ, _hτ, hspec⟩
  refine ⟨τ, hspec, ?_⟩
  intro j
  let C : Set (ι → F) :=
    ReedSolomon.code domain ⌊ProximityGap.prizeRates j * (Fintype.card ι : ℝ≥0)⌋₊
  rcases hspec j with ⟨hne, _hsat, hmax⟩
  have hle_lower :
      GrandChallengesLattice.latticeIndexOf (ι := ι) (w j).δ (w j).le_one ≤
        GrandChallengesLattice.mcaThreshold C epsStar hne := by
    exact GrandChallengesLattice.MCALowerWitness_le_mcaThreshold C epsStar hne (w j)
  have hle_threshold :
      GrandChallengesLattice.mcaThreshold C epsStar hne ≤ τ j := by
    exact hmax _ (GrandChallengesLattice.mcaThreshold_spec C epsStar hne)
  have hidx :
      GrandChallengesLattice.latticeIndexOf (ι := ι) (w j).δ (w j).le_one =
        GrandChallengesLattice.latticeIndexOf (ι := ι) (δ j) (hδ_le_one j) := by
    apply Fin.ext
    simp [GrandChallengesLattice.latticeIndexOf_val, hδw j]
  exact hidx ▸ le_trans hle_lower hle_threshold

/-- The honest uniform GS-exposed prize, with explicit GS faithfulness, numeric clearance, and
per-rate upper witnesses, supplies the all-rate selected-threshold specification together with
both lower and upper lattice brackets for every ABF26 prize rate. -/
theorem exists_mcaPrizeLatticeSpec_and_brackets_of_uniformConjecture
    (domain : ι ↪ F) (m : ℕ)
    (hUniform : epsMCAgsPrizeUniformConjecture domain m) :
    ∃ c₁ c₂ c₃ : ℝ,
      ∀ (η δ : Fin 4 → ℝ≥0),
        (∀ j : Fin 4, 0 < η j) →
        (∀ j : Fin 4,
          (δ j : ℝ) ≤ 1 - (ProximityGap.prizeRates j : ℝ) - (η j : ℝ)) →
        (hδ_le_one : ∀ j : Fin 4, δ j ≤ 1) →
        ∀ L : ∀ _ : Fin 4, WordStack F (Fin 2) ι → Finset (ι → F),
          (∀ j : Fin 4,
            FaithfulGSFamily (F := F)
              ((ReedSolomon.code (domain := domain)
                ⌊(ProximityGap.prizeRates j : ℝ≥0) * (Fintype.card ι : ℝ≥0)⌋₊ :
                  Set (ι → F))) (δ j) (L j)) →
          (∀ j : Fin 4,
            ENNReal.ofReal
                (epsMCAgsPrizeBound (Fintype.card F) m (ProximityGap.prizeRates j)
                  (η j) c₁ c₂ c₃)
              ≤ (epsStar : ENNReal)) →
          (whi : ∀ j : Fin 4,
            GrandChallenges.MCAUpperWitness
              ((ReedSolomon.code (domain := domain)
                ⌊(ProximityGap.prizeRates j : ℝ≥0) * (Fintype.card ι : ℝ≥0)⌋₊ :
                  Set (ι → F))) epsStar) →
          (hδhi : ∀ j : Fin 4, (whi j).δ ≤ 1) →
          ∃ τ : Fin 4 → Fin (Fintype.card ι + 1),
            (∀ j : Fin 4,
              let C : Set (ι → F) :=
                ReedSolomon.code domain
                  ⌊ProximityGap.prizeRates j * (Fintype.card ι : ℝ≥0)⌋₊
              ∃ _ : GrandChallengesLattice.mcaThresholdExists C epsStar,
                GrandChallengesLattice.mcaSatisfies C epsStar (τ j) ∧
                  ∀ i : Fin (Fintype.card ι + 1),
                    GrandChallengesLattice.mcaSatisfies C epsStar i → i ≤ τ j) ∧
              (∀ j : Fin 4,
                GrandChallengesLattice.latticeIndexOf (ι := ι) (δ j) (hδ_le_one j) ≤
                  τ j) ∧
                ∀ j : Fin 4,
                  τ j <
                    GrandChallengesLattice.latticeIndexOf (ι := ι) (whi j).δ (hδhi j) := by
  rcases exists_prize_mcaLowerWitnesses_allRates_of_uniformConjecture domain m hUniform with
    ⟨c₁, c₂, c₃, hlower⟩
  refine ⟨c₁, c₂, c₃, ?_⟩
  intro η δ hη hδ hδ_le_one L hfaithful hclear whi hδhi
  have hw : ∀ j : Fin 4,
      ∃ w : GrandChallenges.MCALowerWitness
        ((ReedSolomon.code (domain := domain)
          ⌊(ProximityGap.prizeRates j : ℝ≥0) * (Fintype.card ι : ℝ≥0)⌋₊ :
            Set (ι → F))) epsStar,
        w.δ = δ j :=
    hlower η δ hη hδ hδ_le_one L hfaithful hclear
  let w : ∀ j : Fin 4,
      GrandChallenges.MCALowerWitness
        ((ReedSolomon.code (domain := domain)
          ⌊(ProximityGap.prizeRates j : ℝ≥0) * (Fintype.card ι : ℝ≥0)⌋₊ :
            Set (ι → F))) epsStar :=
    fun j => Classical.choose (hw j)
  have hδw : ∀ j : Fin 4, (w j).δ = δ j :=
    fun j => Classical.choose_spec (hw j)
  rcases GrandChallengesLattice.exists_mcaPrizeLatticeResolved_with_spec_of_lowerWitnesses
      domain w with ⟨τ, _hτ, hspec⟩
  refine ⟨τ, hspec, ?_, ?_⟩
  · intro j
    let C : Set (ι → F) :=
      ReedSolomon.code domain ⌊ProximityGap.prizeRates j * (Fintype.card ι : ℝ≥0)⌋₊
    rcases hspec j with ⟨hne, _hsat, hmax⟩
    have hle_lower :
        GrandChallengesLattice.latticeIndexOf (ι := ι) (w j).δ (w j).le_one ≤
          GrandChallengesLattice.mcaThreshold C epsStar hne := by
      exact GrandChallengesLattice.MCALowerWitness_le_mcaThreshold C epsStar hne (w j)
    have hle_threshold :
        GrandChallengesLattice.mcaThreshold C epsStar hne ≤ τ j := by
      exact hmax _ (GrandChallengesLattice.mcaThreshold_spec C epsStar hne)
    have hidx :
        GrandChallengesLattice.latticeIndexOf (ι := ι) (w j).δ (w j).le_one =
          GrandChallengesLattice.latticeIndexOf (ι := ι) (δ j) (hδ_le_one j) := by
      apply Fin.ext
      simp [GrandChallengesLattice.latticeIndexOf_val, hδw j]
    exact hidx ▸ le_trans hle_lower hle_threshold
  · intro j
    let C : Set (ι → F) :=
      ReedSolomon.code domain ⌊ProximityGap.prizeRates j * (Fintype.card ι : ℝ≥0)⌋₊
    rcases hspec j with ⟨hne, hsat, _hmax⟩
    have hτ_le_threshold :
        τ j ≤ GrandChallengesLattice.mcaThreshold C epsStar hne :=
      GrandChallengesLattice.le_mcaThreshold C epsStar hne hsat
    have hthreshold_lt_upper :
        GrandChallengesLattice.mcaThreshold C epsStar hne <
          GrandChallengesLattice.latticeIndexOf (ι := ι) (whi j).δ (hδhi j) :=
      GrandChallengesLattice.mcaThreshold_lt_MCAUpperWitness C epsStar hne (whi j) (hδhi j)
    exact lt_of_le_of_lt hτ_le_threshold hthreshold_lt_upper

/-- The honest uniform GS-exposed prize supplies a selected-threshold lattice resolution together
with the exact threshold specification and lower lattice brackets.

This is the resolved companion to
`exists_mcaPrizeLatticeSpec_and_lower_brackets_of_uniformConjecture`: the existing
selected-threshold spec is routed through `mcaPrizeLatticeResolved_iff`, while the uniform GS prize,
faithfulness, and numeric clearance hypotheses remain explicit. -/
theorem exists_mcaPrizeLatticeResolved_with_spec_and_lower_brackets_of_uniformConjecture
    (domain : ι ↪ F) (m : ℕ)
    (hUniform : epsMCAgsPrizeUniformConjecture domain m) :
    ∃ c₁ c₂ c₃ : ℝ,
      ∀ (η δ : Fin 4 → ℝ≥0),
        (∀ j : Fin 4, 0 < η j) →
        (∀ j : Fin 4,
          (δ j : ℝ) ≤ 1 - (ProximityGap.prizeRates j : ℝ) - (η j : ℝ)) →
        (hδ_le_one : ∀ j : Fin 4, δ j ≤ 1) →
        ∀ L : ∀ _ : Fin 4, WordStack F (Fin 2) ι → Finset (ι → F),
          (∀ j : Fin 4,
            FaithfulGSFamily (F := F)
              ((ReedSolomon.code (domain := domain)
                ⌊(ProximityGap.prizeRates j : ℝ≥0) * (Fintype.card ι : ℝ≥0)⌋₊ :
                  Set (ι → F))) (δ j) (L j)) →
          (∀ j : Fin 4,
            ENNReal.ofReal
                (epsMCAgsPrizeBound (Fintype.card F) m (ProximityGap.prizeRates j)
                  (η j) c₁ c₂ c₃)
              ≤ (epsStar : ENNReal)) →
          ∃ τ : Fin 4 → Fin (Fintype.card ι + 1),
            GrandChallengesLattice.mcaPrizeLatticeResolved domain τ ∧
              (∀ j : Fin 4,
                let C : Set (ι → F) :=
                  ReedSolomon.code domain
                    ⌊ProximityGap.prizeRates j * (Fintype.card ι : ℝ≥0)⌋₊
                ∃ _ : GrandChallengesLattice.mcaThresholdExists C epsStar,
                  GrandChallengesLattice.mcaSatisfies C epsStar (τ j) ∧
                    ∀ i : Fin (Fintype.card ι + 1),
                      GrandChallengesLattice.mcaSatisfies C epsStar i → i ≤ τ j) ∧
                ∀ j : Fin 4,
                  GrandChallengesLattice.latticeIndexOf (ι := ι) (δ j) (hδ_le_one j) ≤
                    τ j := by
  rcases exists_mcaPrizeLatticeSpec_and_lower_brackets_of_uniformConjecture
      domain m hUniform with ⟨c₁, c₂, c₃, hbracket⟩
  refine ⟨c₁, c₂, c₃, ?_⟩
  intro η δ hη hδ hδ_le_one L hfaithful hclear
  rcases hbracket η δ hη hδ hδ_le_one L hfaithful hclear with
    ⟨τ, hspec, hlower⟩
  exact ⟨τ, (GrandChallengesLattice.mcaPrizeLatticeResolved_iff domain τ).mpr hspec,
    hspec, hlower⟩

/-- The honest uniform GS-exposed prize supplies a selected-threshold lattice resolution together
with the exact threshold specification and both lower and upper lattice brackets.

This is the resolved companion to `exists_mcaPrizeLatticeSpec_and_brackets_of_uniformConjecture`:
the existing selected-threshold two-bracket spec is routed through
`mcaPrizeLatticeResolved_iff`, while all uniform GS and upper-witness inputs remain explicit. -/
theorem exists_mcaPrizeLatticeResolved_with_spec_and_brackets_of_uniformConjecture
    (domain : ι ↪ F) (m : ℕ)
    (hUniform : epsMCAgsPrizeUniformConjecture domain m) :
    ∃ c₁ c₂ c₃ : ℝ,
      ∀ (η δ : Fin 4 → ℝ≥0),
        (∀ j : Fin 4, 0 < η j) →
        (∀ j : Fin 4,
          (δ j : ℝ) ≤ 1 - (ProximityGap.prizeRates j : ℝ) - (η j : ℝ)) →
        (hδ_le_one : ∀ j : Fin 4, δ j ≤ 1) →
        ∀ L : ∀ _ : Fin 4, WordStack F (Fin 2) ι → Finset (ι → F),
          (∀ j : Fin 4,
            FaithfulGSFamily (F := F)
              ((ReedSolomon.code (domain := domain)
                ⌊(ProximityGap.prizeRates j : ℝ≥0) * (Fintype.card ι : ℝ≥0)⌋₊ :
                  Set (ι → F))) (δ j) (L j)) →
          (∀ j : Fin 4,
            ENNReal.ofReal
                (epsMCAgsPrizeBound (Fintype.card F) m (ProximityGap.prizeRates j)
                  (η j) c₁ c₂ c₃)
              ≤ (epsStar : ENNReal)) →
          (whi : ∀ j : Fin 4,
            GrandChallenges.MCAUpperWitness
              ((ReedSolomon.code (domain := domain)
                ⌊(ProximityGap.prizeRates j : ℝ≥0) * (Fintype.card ι : ℝ≥0)⌋₊ :
                  Set (ι → F))) epsStar) →
          (hδhi : ∀ j : Fin 4, (whi j).δ ≤ 1) →
          ∃ τ : Fin 4 → Fin (Fintype.card ι + 1),
            GrandChallengesLattice.mcaPrizeLatticeResolved domain τ ∧
              (∀ j : Fin 4,
                let C : Set (ι → F) :=
                  ReedSolomon.code domain
                    ⌊ProximityGap.prizeRates j * (Fintype.card ι : ℝ≥0)⌋₊
                ∃ _ : GrandChallengesLattice.mcaThresholdExists C epsStar,
                  GrandChallengesLattice.mcaSatisfies C epsStar (τ j) ∧
                    ∀ i : Fin (Fintype.card ι + 1),
                      GrandChallengesLattice.mcaSatisfies C epsStar i → i ≤ τ j) ∧
                (∀ j : Fin 4,
                  GrandChallengesLattice.latticeIndexOf (ι := ι) (δ j) (hδ_le_one j) ≤
                    τ j) ∧
                  ∀ j : Fin 4,
                    τ j <
                      GrandChallengesLattice.latticeIndexOf (ι := ι) (whi j).δ (hδhi j) := by
  rcases exists_mcaPrizeLatticeSpec_and_brackets_of_uniformConjecture
      domain m hUniform with ⟨c₁, c₂, c₃, hbracket⟩
  refine ⟨c₁, c₂, c₃, ?_⟩
  intro η δ hη hδ hδ_le_one L hfaithful hclear whi hδhi
  rcases hbracket η δ hη hδ hδ_le_one L hfaithful hclear whi hδhi with
    ⟨τ, hspec, hlower, hupper⟩
  exact ⟨τ, (GrandChallengesLattice.mcaPrizeLatticeResolved_iff domain τ).mpr hspec,
    hspec, hlower, hupper⟩

/-- The honest uniform GS-exposed prize, with explicit GS faithfulness and numeric clearance,
produces a faithful MCA threshold-existence witness for a single ABF26 prize-rate code. -/
theorem mcaThresholdExists_prize_of_uniformConjecture
    (domain : ι ↪ F) (m : ℕ)
    (hUniform : epsMCAgsPrizeUniformConjecture domain m) :
    ∃ c₁ c₂ c₃ : ℝ,
      ∀ (j : Fin 4) (η δ : ℝ≥0),
        0 < η →
        (δ : ℝ) ≤ 1 - (ProximityGap.prizeRates j : ℝ) - (η : ℝ) →
        δ ≤ 1 →
        ∀ L : WordStack F (Fin 2) ι → Finset (ι → F),
          FaithfulGSFamily (F := F)
            ((ReedSolomon.code (domain := domain)
              ⌊(ProximityGap.prizeRates j : ℝ≥0) * (Fintype.card ι : ℝ≥0)⌋₊ :
                Set (ι → F))) δ L →
          ENNReal.ofReal
              (epsMCAgsPrizeBound (Fintype.card F) m (ProximityGap.prizeRates j)
                η c₁ c₂ c₃)
            ≤ (epsStar : ENNReal) →
          GrandChallengesLattice.mcaThresholdExists
            ((ReedSolomon.code (domain := domain)
              ⌊(ProximityGap.prizeRates j : ℝ≥0) * (Fintype.card ι : ℝ≥0)⌋₊ :
                Set (ι → F))) epsStar := by
  rcases exists_prize_mcaLowerWitness_of_uniformConjecture domain m hUniform with
    ⟨c₁, c₂, c₃, hlower⟩
  refine ⟨c₁, c₂, c₃, ?_⟩
  intro j η δ hη hδ hδ_le_one L hfaithful hclear
  let C : Set (ι → F) :=
    (ReedSolomon.code (domain := domain)
      ⌊(ProximityGap.prizeRates j : ℝ≥0) * (Fintype.card ι : ℝ≥0)⌋₊ : Set (ι → F))
  rcases hlower j η δ hη hδ hδ_le_one L hfaithful hclear with ⟨w, _⟩
  exact GrandChallengesLattice.mcaThresholdExists_of_MCALowerWitness C epsStar w

/-- The honest uniform GS-exposed prize, with explicit all-rate GS faithfulness and numeric
clearance, produces MCA threshold-existence witnesses at all four ABF26 prize-rate codes.

This is the all-rate threshold-existence projection of
`mcaThresholdExists_prize_of_uniformConjecture`: it deliberately exposes only the nonemptiness
needed to form `mcaThreshold`, leaving satisfy/maximality and bracket data to the stronger
wrappers below. -/
theorem mcaThresholdExists_prize_allRates_of_uniformConjecture
    (domain : ι ↪ F) (m : ℕ)
    (hUniform : epsMCAgsPrizeUniformConjecture domain m) :
    ∃ c₁ c₂ c₃ : ℝ,
      ∀ (η δ : Fin 4 → ℝ≥0),
        (∀ j : Fin 4, 0 < η j) →
        (∀ j : Fin 4,
          (δ j : ℝ) ≤ 1 - (ProximityGap.prizeRates j : ℝ) - (η j : ℝ)) →
        (∀ j : Fin 4, δ j ≤ 1) →
        ∀ L : ∀ _ : Fin 4, WordStack F (Fin 2) ι → Finset (ι → F),
          (∀ j : Fin 4,
            FaithfulGSFamily (F := F)
              ((ReedSolomon.code (domain := domain)
                ⌊(ProximityGap.prizeRates j : ℝ≥0) * (Fintype.card ι : ℝ≥0)⌋₊ :
                  Set (ι → F))) (δ j) (L j)) →
          (∀ j : Fin 4,
            ENNReal.ofReal
                (epsMCAgsPrizeBound (Fintype.card F) m (ProximityGap.prizeRates j)
                  (η j) c₁ c₂ c₃)
              ≤ (epsStar : ENNReal)) →
          ∀ j : Fin 4,
            GrandChallengesLattice.mcaThresholdExists
              ((ReedSolomon.code (domain := domain)
                ⌊(ProximityGap.prizeRates j : ℝ≥0) * (Fintype.card ι : ℝ≥0)⌋₊ :
                  Set (ι → F))) epsStar := by
  rcases mcaThresholdExists_prize_of_uniformConjecture domain m hUniform with
    ⟨c₁, c₂, c₃, hexists⟩
  refine ⟨c₁, c₂, c₃, ?_⟩
  intro η δ hη hδ hδ_le_one L hfaithful hclear j
  exact hexists j (η j) (δ j) (hη j) (hδ j) (hδ_le_one j) (L j)
    (hfaithful j) (hclear j)

/-- The honest uniform GS-exposed prize, with explicit GS faithfulness and numeric clearance,
packages only the single-rate selected threshold satisfy fact.

This is the low-output threshold-spec projection between
`mcaThresholdExists_prize_of_uniformConjecture` and the stronger lower/two-bracket wrappers:
callers that only need to form `mcaThreshold` and use its satisfy fact do not have to unpack
bracket data. -/
theorem mcaThreshold_spec_prize_of_uniformConjecture
    (domain : ι ↪ F) (m : ℕ)
    (hUniform : epsMCAgsPrizeUniformConjecture domain m) :
    ∃ c₁ c₂ c₃ : ℝ,
      ∀ (j : Fin 4) (η δ : ℝ≥0),
        0 < η →
        (δ : ℝ) ≤ 1 - (ProximityGap.prizeRates j : ℝ) - (η : ℝ) →
        δ ≤ 1 →
        ∀ L : WordStack F (Fin 2) ι → Finset (ι → F),
          FaithfulGSFamily (F := F)
            ((ReedSolomon.code (domain := domain)
              ⌊(ProximityGap.prizeRates j : ℝ≥0) * (Fintype.card ι : ℝ≥0)⌋₊ :
                Set (ι → F))) δ L →
          ENNReal.ofReal
              (epsMCAgsPrizeBound (Fintype.card F) m (ProximityGap.prizeRates j)
                η c₁ c₂ c₃)
            ≤ (epsStar : ENNReal) →
          let C : Set (ι → F) :=
            ReedSolomon.code domain
              ⌊ProximityGap.prizeRates j * (Fintype.card ι : ℝ≥0)⌋₊
          ∃ hne : GrandChallengesLattice.mcaThresholdExists C epsStar,
            GrandChallengesLattice.mcaSatisfies C epsStar
              (GrandChallengesLattice.mcaThreshold C epsStar hne) := by
  rcases mcaThresholdExists_prize_of_uniformConjecture domain m hUniform with
    ⟨c₁, c₂, c₃, hexists⟩
  refine ⟨c₁, c₂, c₃, ?_⟩
  intro j η δ hη hδ hδ_le_one L hfaithful hclear
  let C : Set (ι → F) :=
    (ReedSolomon.code (domain := domain)
      ⌊(ProximityGap.prizeRates j : ℝ≥0) * (Fintype.card ι : ℝ≥0)⌋₊ : Set (ι → F))
  let hne : GrandChallengesLattice.mcaThresholdExists C epsStar :=
    hexists j η δ hη hδ hδ_le_one L hfaithful hclear
  exact ⟨hne, GrandChallengesLattice.mcaThreshold_spec C epsStar hne⟩

/-- The honest uniform GS-exposed prize, with explicit all-rate GS faithfulness and numeric
clearance, packages only the selected threshold satisfy facts at all four ABF26 prize-rate codes.

This is the all-rate threshold-spec projection of
`mcaThreshold_spec_prize_of_uniformConjecture`: it is intentionally weaker than the lower-bracket,
two-bracket, and resolved-`τ` APIs below. -/
theorem mcaThreshold_spec_prize_allRates_of_uniformConjecture
    (domain : ι ↪ F) (m : ℕ)
    (hUniform : epsMCAgsPrizeUniformConjecture domain m) :
    ∃ c₁ c₂ c₃ : ℝ,
      ∀ (η δ : Fin 4 → ℝ≥0),
        (∀ j : Fin 4, 0 < η j) →
        (∀ j : Fin 4,
          (δ j : ℝ) ≤ 1 - (ProximityGap.prizeRates j : ℝ) - (η j : ℝ)) →
        (∀ j : Fin 4, δ j ≤ 1) →
        ∀ L : ∀ _ : Fin 4, WordStack F (Fin 2) ι → Finset (ι → F),
          (∀ j : Fin 4,
            FaithfulGSFamily (F := F)
              ((ReedSolomon.code (domain := domain)
                ⌊(ProximityGap.prizeRates j : ℝ≥0) * (Fintype.card ι : ℝ≥0)⌋₊ :
                  Set (ι → F))) (δ j) (L j)) →
          (∀ j : Fin 4,
            ENNReal.ofReal
                (epsMCAgsPrizeBound (Fintype.card F) m (ProximityGap.prizeRates j)
                  (η j) c₁ c₂ c₃)
              ≤ (epsStar : ENNReal)) →
          ∀ j : Fin 4,
            let C : Set (ι → F) :=
              ReedSolomon.code domain
                ⌊ProximityGap.prizeRates j * (Fintype.card ι : ℝ≥0)⌋₊
            ∃ hne : GrandChallengesLattice.mcaThresholdExists C epsStar,
              GrandChallengesLattice.mcaSatisfies C epsStar
                (GrandChallengesLattice.mcaThreshold C epsStar hne) := by
  rcases mcaThreshold_spec_prize_of_uniformConjecture domain m hUniform with
    ⟨c₁, c₂, c₃, hsingle⟩
  refine ⟨c₁, c₂, c₃, ?_⟩
  intro η δ hη hδ hδ_le_one L hfaithful hclear j
  exact hsingle j (η j) (δ j) (hη j) (hδ j) (hδ_le_one j) (L j)
    (hfaithful j) (hclear j)

/-- The honest uniform GS-exposed prize, with explicit GS faithfulness and numeric clearance,
packages the single-rate threshold satisfy fact together with the lower lattice bracket
`latticeIndexOf δ ≤ mcaThreshold`. -/
theorem mcaThreshold_spec_and_lower_bracket_prize_of_uniformConjecture
    (domain : ι ↪ F) (m : ℕ)
    (hUniform : epsMCAgsPrizeUniformConjecture domain m) :
    ∃ c₁ c₂ c₃ : ℝ,
      ∀ (j : Fin 4) (η δ : ℝ≥0),
        0 < η →
        (δ : ℝ) ≤ 1 - (ProximityGap.prizeRates j : ℝ) - (η : ℝ) →
        (hδ_le_one : δ ≤ 1) →
        ∀ L : WordStack F (Fin 2) ι → Finset (ι → F),
          FaithfulGSFamily (F := F)
            ((ReedSolomon.code (domain := domain)
              ⌊(ProximityGap.prizeRates j : ℝ≥0) * (Fintype.card ι : ℝ≥0)⌋₊ :
                Set (ι → F))) δ L →
          ENNReal.ofReal
              (epsMCAgsPrizeBound (Fintype.card F) m (ProximityGap.prizeRates j)
                η c₁ c₂ c₃)
            ≤ (epsStar : ENNReal) →
          let C : Set (ι → F) :=
            ReedSolomon.code domain
              ⌊ProximityGap.prizeRates j * (Fintype.card ι : ℝ≥0)⌋₊
          ∃ hne : GrandChallengesLattice.mcaThresholdExists C epsStar,
            GrandChallengesLattice.mcaSatisfies C epsStar
              (GrandChallengesLattice.mcaThreshold C epsStar hne) ∧
              GrandChallengesLattice.latticeIndexOf (ι := ι) δ hδ_le_one ≤
                GrandChallengesLattice.mcaThreshold C epsStar hne := by
  rcases exists_prize_mcaLowerWitness_of_uniformConjecture domain m hUniform with
    ⟨c₁, c₂, c₃, hlower⟩
  refine ⟨c₁, c₂, c₃, ?_⟩
  intro j η δ hη hδ hδ_le_one L hfaithful hclear
  let C : Set (ι → F) :=
    (ReedSolomon.code (domain := domain)
      ⌊(ProximityGap.prizeRates j : ℝ≥0) * (Fintype.card ι : ℝ≥0)⌋₊ : Set (ι → F))
  rcases hlower j η δ hη hδ hδ_le_one L hfaithful hclear with ⟨w, hwδ⟩
  let hne : GrandChallengesLattice.mcaThresholdExists C epsStar :=
    GrandChallengesLattice.mcaThresholdExists_of_MCALowerWitness C epsStar w
  refine ⟨hne, GrandChallengesLattice.mcaThreshold_spec C epsStar hne, ?_⟩
  have hle := GrandChallengesLattice.MCALowerWitness_le_mcaThreshold C epsStar hne w
  subst δ
  simpa using hle

/-- The honest uniform GS-exposed prize, with explicit GS faithfulness, numeric clearance, and
an explicit upper witness, packages the single-rate threshold satisfy fact together with both
lattice brackets. -/
theorem mcaThreshold_spec_and_bracket_prize_of_uniformConjecture
    (domain : ι ↪ F) (m : ℕ)
    (hUniform : epsMCAgsPrizeUniformConjecture domain m) :
    ∃ c₁ c₂ c₃ : ℝ,
      ∀ (j : Fin 4) (η δ : ℝ≥0),
        0 < η →
        (δ : ℝ) ≤ 1 - (ProximityGap.prizeRates j : ℝ) - (η : ℝ) →
        (hδ_le_one : δ ≤ 1) →
        ∀ L : WordStack F (Fin 2) ι → Finset (ι → F),
          FaithfulGSFamily (F := F)
            ((ReedSolomon.code (domain := domain)
              ⌊(ProximityGap.prizeRates j : ℝ≥0) * (Fintype.card ι : ℝ≥0)⌋₊ :
                Set (ι → F))) δ L →
          ENNReal.ofReal
              (epsMCAgsPrizeBound (Fintype.card F) m (ProximityGap.prizeRates j)
                η c₁ c₂ c₃)
            ≤ (epsStar : ENNReal) →
          (whi : GrandChallenges.MCAUpperWitness
            ((ReedSolomon.code (domain := domain)
              ⌊(ProximityGap.prizeRates j : ℝ≥0) * (Fintype.card ι : ℝ≥0)⌋₊ :
                Set (ι → F))) epsStar) →
          (hδhi : whi.δ ≤ 1) →
          let C : Set (ι → F) :=
            ReedSolomon.code domain
              ⌊ProximityGap.prizeRates j * (Fintype.card ι : ℝ≥0)⌋₊
          ∃ hne : GrandChallengesLattice.mcaThresholdExists C epsStar,
            GrandChallengesLattice.mcaSatisfies C epsStar
              (GrandChallengesLattice.mcaThreshold C epsStar hne) ∧
              GrandChallengesLattice.latticeIndexOf (ι := ι) δ hδ_le_one ≤
                GrandChallengesLattice.mcaThreshold C epsStar hne ∧
                GrandChallengesLattice.mcaThreshold C epsStar hne <
                  GrandChallengesLattice.latticeIndexOf (ι := ι) whi.δ hδhi := by
  rcases exists_prize_mcaLowerWitness_of_uniformConjecture domain m hUniform with
    ⟨c₁, c₂, c₃, hlower⟩
  refine ⟨c₁, c₂, c₃, ?_⟩
  intro j η δ hη hδ hδ_le_one L hfaithful hclear whi hδhi
  let C : Set (ι → F) :=
    (ReedSolomon.code (domain := domain)
      ⌊(ProximityGap.prizeRates j : ℝ≥0) * (Fintype.card ι : ℝ≥0)⌋₊ : Set (ι → F))
  rcases hlower j η δ hη hδ hδ_le_one L hfaithful hclear with ⟨w, hwδ⟩
  let hne : GrandChallengesLattice.mcaThresholdExists C epsStar :=
    GrandChallengesLattice.mcaThresholdExists_of_MCALowerWitness C epsStar w
  refine ⟨hne, GrandChallengesLattice.mcaThreshold_spec C epsStar hne, ?_, ?_⟩
  · have hle := GrandChallengesLattice.MCALowerWitness_le_mcaThreshold C epsStar hne w
    subst δ
    simpa using hle
  · exact GrandChallengesLattice.mcaThreshold_lt_MCAUpperWitness C epsStar hne whi hδhi

/-- The honest uniform GS-exposed prize, with explicit all-rate GS faithfulness and numeric
clearance, packages threshold satisfy facts together with lower lattice brackets at all four
ABF26 prize rates. -/
theorem mcaThreshold_spec_and_lower_bracket_prize_allRates_of_uniformConjecture
    (domain : ι ↪ F) (m : ℕ)
    (hUniform : epsMCAgsPrizeUniformConjecture domain m) :
    ∃ c₁ c₂ c₃ : ℝ,
      ∀ (η δ : Fin 4 → ℝ≥0),
        (∀ j : Fin 4, 0 < η j) →
        (∀ j : Fin 4,
          (δ j : ℝ) ≤ 1 - (ProximityGap.prizeRates j : ℝ) - (η j : ℝ)) →
        (hδ_le_one : ∀ j : Fin 4, δ j ≤ 1) →
        ∀ L : ∀ _ : Fin 4, WordStack F (Fin 2) ι → Finset (ι → F),
          (∀ j : Fin 4,
            FaithfulGSFamily (F := F)
              ((ReedSolomon.code (domain := domain)
                ⌊(ProximityGap.prizeRates j : ℝ≥0) * (Fintype.card ι : ℝ≥0)⌋₊ :
                  Set (ι → F))) (δ j) (L j)) →
          (∀ j : Fin 4,
            ENNReal.ofReal
                (epsMCAgsPrizeBound (Fintype.card F) m (ProximityGap.prizeRates j)
                  (η j) c₁ c₂ c₃)
              ≤ (epsStar : ENNReal)) →
          ∀ j : Fin 4,
            let C : Set (ι → F) :=
              ReedSolomon.code domain
                ⌊ProximityGap.prizeRates j * (Fintype.card ι : ℝ≥0)⌋₊
            ∃ hne : GrandChallengesLattice.mcaThresholdExists C epsStar,
              GrandChallengesLattice.mcaSatisfies C epsStar
                (GrandChallengesLattice.mcaThreshold C epsStar hne) ∧
                GrandChallengesLattice.latticeIndexOf (ι := ι) (δ j) (hδ_le_one j) ≤
                  GrandChallengesLattice.mcaThreshold C epsStar hne := by
  rcases mcaThreshold_spec_and_lower_bracket_prize_of_uniformConjecture domain m hUniform with
    ⟨c₁, c₂, c₃, hsingle⟩
  refine ⟨c₁, c₂, c₃, ?_⟩
  intro η δ hη hδ hδ_le_one L hfaithful hclear j
  exact hsingle j (η j) (δ j) (hη j) (hδ j) (hδ_le_one j) (L j)
    (hfaithful j) (hclear j)

/-- The honest uniform GS-exposed prize, with explicit all-rate GS faithfulness, numeric clearance,
and upper witnesses, packages threshold satisfy facts together with both lattice brackets at all
four ABF26 prize rates. -/
theorem mcaThreshold_spec_and_bracket_prize_allRates_of_uniformConjecture
    (domain : ι ↪ F) (m : ℕ)
    (hUniform : epsMCAgsPrizeUniformConjecture domain m) :
    ∃ c₁ c₂ c₃ : ℝ,
      ∀ (η δ : Fin 4 → ℝ≥0),
        (∀ j : Fin 4, 0 < η j) →
        (∀ j : Fin 4,
          (δ j : ℝ) ≤ 1 - (ProximityGap.prizeRates j : ℝ) - (η j : ℝ)) →
        (hδ_le_one : ∀ j : Fin 4, δ j ≤ 1) →
        ∀ L : ∀ _ : Fin 4, WordStack F (Fin 2) ι → Finset (ι → F),
          (∀ j : Fin 4,
            FaithfulGSFamily (F := F)
              ((ReedSolomon.code (domain := domain)
                ⌊(ProximityGap.prizeRates j : ℝ≥0) * (Fintype.card ι : ℝ≥0)⌋₊ :
                  Set (ι → F))) (δ j) (L j)) →
          (∀ j : Fin 4,
            ENNReal.ofReal
                (epsMCAgsPrizeBound (Fintype.card F) m (ProximityGap.prizeRates j)
                  (η j) c₁ c₂ c₃)
              ≤ (epsStar : ENNReal)) →
          (whi : ∀ j : Fin 4,
            GrandChallenges.MCAUpperWitness
              ((ReedSolomon.code (domain := domain)
                ⌊(ProximityGap.prizeRates j : ℝ≥0) * (Fintype.card ι : ℝ≥0)⌋₊ :
                  Set (ι → F))) epsStar) →
          (hδhi : ∀ j : Fin 4, (whi j).δ ≤ 1) →
          ∀ j : Fin 4,
            let C : Set (ι → F) :=
              ReedSolomon.code domain
                ⌊ProximityGap.prizeRates j * (Fintype.card ι : ℝ≥0)⌋₊
            ∃ hne : GrandChallengesLattice.mcaThresholdExists C epsStar,
              GrandChallengesLattice.mcaSatisfies C epsStar
                (GrandChallengesLattice.mcaThreshold C epsStar hne) ∧
                GrandChallengesLattice.latticeIndexOf (ι := ι) (δ j) (hδ_le_one j) ≤
                  GrandChallengesLattice.mcaThreshold C epsStar hne ∧
                  GrandChallengesLattice.mcaThreshold C epsStar hne <
                    GrandChallengesLattice.latticeIndexOf (ι := ι) (whi j).δ (hδhi j) := by
  rcases mcaThreshold_spec_and_bracket_prize_of_uniformConjecture domain m hUniform with
    ⟨c₁, c₂, c₃, hsingle⟩
  refine ⟨c₁, c₂, c₃, ?_⟩
  intro η δ hη hδ hδ_le_one L hfaithful hclear whi hδhi j
  exact hsingle j (η j) (δ j) (hη j) (hδ j) (hδ_le_one j) (L j)
    (hfaithful j) (hclear j) (whi j) (hδhi j)

set_option linter.style.longLine false

/-- The all-rate uniform GS threshold-spec package resolves the faithful prize lattice at the
concrete `mcaThreshold` indices and preserves only the selected-threshold spec.

This is the spec-only concrete-threshold companion to
`mcaThreshold_spec_prize_allRates_of_uniformConjecture`: it exposes the chosen thresholds as a
`τ` solving `mcaPrizeLatticeResolved`, without requiring or returning lower/upper bracket data. -/
theorem mcaPrizeLatticeResolved_with_threshold_spec_prize_allRates_of_uniformConjecture
    (domain : ι ↪ F) (m : ℕ)
    (hUniform : epsMCAgsPrizeUniformConjecture domain m) :
    ∃ c₁ c₂ c₃ : ℝ,
      ∀ (η δ : Fin 4 → ℝ≥0),
        (∀ j : Fin 4, 0 < η j) →
        (∀ j : Fin 4,
          (δ j : ℝ) ≤ 1 - (ProximityGap.prizeRates j : ℝ) - (η j : ℝ)) →
        (∀ j : Fin 4, δ j ≤ 1) →
        ∀ L : ∀ _ : Fin 4, WordStack F (Fin 2) ι → Finset (ι → F),
          (∀ j : Fin 4,
            FaithfulGSFamily (F := F)
              ((ReedSolomon.code (domain := domain)
                ⌊(ProximityGap.prizeRates j : ℝ≥0) * (Fintype.card ι : ℝ≥0)⌋₊ :
                  Set (ι → F))) (δ j) (L j)) →
          (∀ j : Fin 4,
            ENNReal.ofReal
                (epsMCAgsPrizeBound (Fintype.card F) m (ProximityGap.prizeRates j)
                  (η j) c₁ c₂ c₃)
              ≤ (epsStar : ENNReal)) →
          let C : Fin 4 → Set (ι → F) := fun j =>
            ReedSolomon.code domain
              ⌊ProximityGap.prizeRates j * (Fintype.card ι : ℝ≥0)⌋₊
          ∃ τ : Fin 4 → Fin (Fintype.card ι + 1),
            GrandChallengesLattice.mcaPrizeLatticeResolved domain τ ∧
              ∀ j : Fin 4,
                ∃ hne : GrandChallengesLattice.mcaThresholdExists (C j) epsStar,
                  τ j = GrandChallengesLattice.mcaThreshold (C j) epsStar hne ∧
                    GrandChallengesLattice.mcaSatisfies (C j) epsStar (τ j) ∧
                      ∀ i : Fin (Fintype.card ι + 1),
                        GrandChallengesLattice.mcaSatisfies (C j) epsStar i → i ≤ τ j := by
  rcases mcaThreshold_spec_prize_allRates_of_uniformConjecture
      domain m hUniform with ⟨c₁, c₂, c₃, hall⟩
  refine ⟨c₁, c₂, c₃, ?_⟩
  intro η δ hη hδ hδ_le_one L hfaithful hclear
  let C : Fin 4 → Set (ι → F) := fun j =>
    (ReedSolomon.code (domain := domain)
      ⌊(ProximityGap.prizeRates j : ℝ≥0) * (Fintype.card ι : ℝ≥0)⌋₊ : Set (ι → F))
  have hdata :
      ∀ j : Fin 4,
        ∃ hne : GrandChallengesLattice.mcaThresholdExists (C j) epsStar,
          GrandChallengesLattice.mcaSatisfies (C j) epsStar
            (GrandChallengesLattice.mcaThreshold (C j) epsStar hne) := by
    intro j
    simpa [C] using hall η δ hη hδ hδ_le_one L hfaithful hclear j
  choose hne hsat using hdata
  let τ : Fin 4 → Fin (Fintype.card ι + 1) := fun j =>
    GrandChallengesLattice.mcaThreshold (C j) epsStar (hne j)
  refine ⟨τ, ?_, ?_⟩
  · refine (GrandChallengesLattice.mcaPrizeLatticeResolved_iff domain τ).mpr ?_
    intro j
    refine ⟨hne j, ?_, ?_⟩
    · simpa [τ, C] using hsat j
    · intro i hi
      simpa [τ, C] using GrandChallengesLattice.le_mcaThreshold (C j) epsStar (hne j) hi
  · intro j
    refine ⟨hne j, ?_, ?_, ?_⟩
    · simp [τ, C]
    · simpa [τ] using hsat j
    · intro i hi
      simpa [τ, C] using GrandChallengesLattice.le_mcaThreshold (C j) epsStar (hne j) hi

/-- The all-rate uniform GS threshold-spec package resolves the faithful prize lattice at the
concrete `mcaThreshold` indices and preserves only the threshold equality witnesses. -/
theorem mcaPrizeLatticeResolved_with_threshold_prize_allRates_of_uniformConjecture
    (domain : ι ↪ F) (m : ℕ)
    (hUniform : epsMCAgsPrizeUniformConjecture domain m) :
    ∃ c₁ c₂ c₃ : ℝ,
      ∀ (η δ : Fin 4 → ℝ≥0),
        (∀ j : Fin 4, 0 < η j) →
        (∀ j : Fin 4,
          (δ j : ℝ) ≤ 1 - (ProximityGap.prizeRates j : ℝ) - (η j : ℝ)) →
        (∀ j : Fin 4, δ j ≤ 1) →
        ∀ L : ∀ _ : Fin 4, WordStack F (Fin 2) ι → Finset (ι → F),
          (∀ j : Fin 4,
            FaithfulGSFamily (F := F)
              ((ReedSolomon.code (domain := domain)
                ⌊(ProximityGap.prizeRates j : ℝ≥0) * (Fintype.card ι : ℝ≥0)⌋₊ :
                  Set (ι → F))) (δ j) (L j)) →
          (∀ j : Fin 4,
            ENNReal.ofReal
                (epsMCAgsPrizeBound (Fintype.card F) m (ProximityGap.prizeRates j)
                  (η j) c₁ c₂ c₃)
              ≤ (epsStar : ENNReal)) →
          let C : Fin 4 → Set (ι → F) := fun j =>
            ReedSolomon.code domain
              ⌊ProximityGap.prizeRates j * (Fintype.card ι : ℝ≥0)⌋₊
          ∃ τ : Fin 4 → Fin (Fintype.card ι + 1),
            GrandChallengesLattice.mcaPrizeLatticeResolved domain τ ∧
              ∀ j : Fin 4,
                ∃ hne : GrandChallengesLattice.mcaThresholdExists (C j) epsStar,
                  τ j = GrandChallengesLattice.mcaThreshold (C j) epsStar hne := by
  rcases mcaPrizeLatticeResolved_with_threshold_spec_prize_allRates_of_uniformConjecture
      domain m hUniform with ⟨c₁, c₂, c₃, hresolved⟩
  refine ⟨c₁, c₂, c₃, ?_⟩
  intro η δ hη hδ hδ_le_one L hfaithful hclear
  rcases hresolved η δ hη hδ hδ_le_one L hfaithful hclear with ⟨τ, hτ, hspec⟩
  refine ⟨τ, hτ, ?_⟩
  intro j
  rcases hspec j with ⟨hne, hτeq, _hsat, _hmax⟩
  exact ⟨hne, hτeq⟩

/-- The all-rate uniform GS threshold package also resolves the faithful prize lattice at the
concrete `mcaThreshold` indices and preserves the lower lattice brackets.

This is a concrete-threshold companion to
`mcaThreshold_spec_and_lower_bracket_prize_allRates_of_uniformConjecture`: it exposes the chosen
thresholds as a `τ` solving `mcaPrizeLatticeResolved`, so downstream code does not have to rebuild
the `mcaPrizeLatticeResolved_iff` projection. -/
theorem mcaPrizeLatticeResolved_with_threshold_spec_and_lower_brackets_prize_allRates_of_uniformConjecture
    (domain : ι ↪ F) (m : ℕ)
    (hUniform : epsMCAgsPrizeUniformConjecture domain m) :
    ∃ c₁ c₂ c₃ : ℝ,
      ∀ (η δ : Fin 4 → ℝ≥0),
        (∀ j : Fin 4, 0 < η j) →
        (∀ j : Fin 4,
          (δ j : ℝ) ≤ 1 - (ProximityGap.prizeRates j : ℝ) - (η j : ℝ)) →
        (hδ_le_one : ∀ j : Fin 4, δ j ≤ 1) →
        ∀ L : ∀ _ : Fin 4, WordStack F (Fin 2) ι → Finset (ι → F),
          (∀ j : Fin 4,
            FaithfulGSFamily (F := F)
              ((ReedSolomon.code (domain := domain)
                ⌊(ProximityGap.prizeRates j : ℝ≥0) * (Fintype.card ι : ℝ≥0)⌋₊ :
                  Set (ι → F))) (δ j) (L j)) →
          (∀ j : Fin 4,
            ENNReal.ofReal
                (epsMCAgsPrizeBound (Fintype.card F) m (ProximityGap.prizeRates j)
                  (η j) c₁ c₂ c₃)
              ≤ (epsStar : ENNReal)) →
          let C : Fin 4 → Set (ι → F) := fun j =>
            ReedSolomon.code domain
              ⌊ProximityGap.prizeRates j * (Fintype.card ι : ℝ≥0)⌋₊
          ∃ τ : Fin 4 → Fin (Fintype.card ι + 1),
            GrandChallengesLattice.mcaPrizeLatticeResolved domain τ ∧
              ∀ j : Fin 4,
                ∃ hne : GrandChallengesLattice.mcaThresholdExists (C j) epsStar,
                  τ j = GrandChallengesLattice.mcaThreshold (C j) epsStar hne ∧
                    GrandChallengesLattice.mcaSatisfies (C j) epsStar (τ j) ∧
                      GrandChallengesLattice.latticeIndexOf (ι := ι) (δ j) (hδ_le_one j) ≤
                        τ j := by
  rcases mcaThreshold_spec_and_lower_bracket_prize_allRates_of_uniformConjecture
      domain m hUniform with ⟨c₁, c₂, c₃, hall⟩
  refine ⟨c₁, c₂, c₃, ?_⟩
  intro η δ hη hδ hδ_le_one L hfaithful hclear
  let C : Fin 4 → Set (ι → F) := fun j =>
    (ReedSolomon.code (domain := domain)
      ⌊(ProximityGap.prizeRates j : ℝ≥0) * (Fintype.card ι : ℝ≥0)⌋₊ : Set (ι → F))
  have hdata :
      ∀ j : Fin 4,
        ∃ hne : GrandChallengesLattice.mcaThresholdExists (C j) epsStar,
          GrandChallengesLattice.mcaSatisfies (C j) epsStar
            (GrandChallengesLattice.mcaThreshold (C j) epsStar hne) ∧
            GrandChallengesLattice.latticeIndexOf (ι := ι) (δ j) (hδ_le_one j) ≤
              GrandChallengesLattice.mcaThreshold (C j) epsStar hne := by
    intro j
    simpa [C] using hall η δ hη hδ hδ_le_one L hfaithful hclear j
  choose hne hspec using hdata
  let τ : Fin 4 → Fin (Fintype.card ι + 1) := fun j =>
    GrandChallengesLattice.mcaThreshold (C j) epsStar (hne j)
  refine ⟨τ, ?_, ?_⟩
  · refine (GrandChallengesLattice.mcaPrizeLatticeResolved_iff domain τ).mpr ?_
    intro j
    refine ⟨hne j, ?_, ?_⟩
    · simpa [τ, C] using (hspec j).1
    · intro i hi
      simpa [τ, C] using GrandChallengesLattice.le_mcaThreshold (C j) epsStar (hne j) hi
  · intro j
    refine ⟨hne j, ?_, ?_, ?_⟩
    · simp [τ, C]
    · simpa [τ] using (hspec j).1
    · simpa [τ] using (hspec j).2

/-- The all-rate uniform GS two-bracket threshold package also resolves the faithful prize lattice
at the concrete `mcaThreshold` indices and preserves both lower and upper lattice brackets. -/
theorem mcaPrizeLatticeResolved_with_threshold_spec_and_brackets_prize_allRates_of_uniformConjecture
    (domain : ι ↪ F) (m : ℕ)
    (hUniform : epsMCAgsPrizeUniformConjecture domain m) :
    ∃ c₁ c₂ c₃ : ℝ,
      ∀ (η δ : Fin 4 → ℝ≥0),
        (∀ j : Fin 4, 0 < η j) →
        (∀ j : Fin 4,
          (δ j : ℝ) ≤ 1 - (ProximityGap.prizeRates j : ℝ) - (η j : ℝ)) →
        (hδ_le_one : ∀ j : Fin 4, δ j ≤ 1) →
        ∀ L : ∀ _ : Fin 4, WordStack F (Fin 2) ι → Finset (ι → F),
          (∀ j : Fin 4,
            FaithfulGSFamily (F := F)
              ((ReedSolomon.code (domain := domain)
                ⌊(ProximityGap.prizeRates j : ℝ≥0) * (Fintype.card ι : ℝ≥0)⌋₊ :
                  Set (ι → F))) (δ j) (L j)) →
          (∀ j : Fin 4,
            ENNReal.ofReal
                (epsMCAgsPrizeBound (Fintype.card F) m (ProximityGap.prizeRates j)
                  (η j) c₁ c₂ c₃)
              ≤ (epsStar : ENNReal)) →
          (whi : ∀ j : Fin 4,
            GrandChallenges.MCAUpperWitness
              ((ReedSolomon.code (domain := domain)
                ⌊(ProximityGap.prizeRates j : ℝ≥0) * (Fintype.card ι : ℝ≥0)⌋₊ :
                  Set (ι → F))) epsStar) →
          (hδhi : ∀ j : Fin 4, (whi j).δ ≤ 1) →
          let C : Fin 4 → Set (ι → F) := fun j =>
            ReedSolomon.code domain
              ⌊ProximityGap.prizeRates j * (Fintype.card ι : ℝ≥0)⌋₊
          ∃ τ : Fin 4 → Fin (Fintype.card ι + 1),
            GrandChallengesLattice.mcaPrizeLatticeResolved domain τ ∧
              ∀ j : Fin 4,
                ∃ hne : GrandChallengesLattice.mcaThresholdExists (C j) epsStar,
                  τ j = GrandChallengesLattice.mcaThreshold (C j) epsStar hne ∧
                    GrandChallengesLattice.mcaSatisfies (C j) epsStar (τ j) ∧
                      GrandChallengesLattice.latticeIndexOf (ι := ι) (δ j) (hδ_le_one j) ≤
                        τ j ∧
                        τ j <
                          GrandChallengesLattice.latticeIndexOf (ι := ι) (whi j).δ (hδhi j) := by
  rcases mcaThreshold_spec_and_bracket_prize_allRates_of_uniformConjecture
      domain m hUniform with ⟨c₁, c₂, c₃, hall⟩
  refine ⟨c₁, c₂, c₃, ?_⟩
  intro η δ hη hδ hδ_le_one L hfaithful hclear whi hδhi
  let C : Fin 4 → Set (ι → F) := fun j =>
    (ReedSolomon.code (domain := domain)
      ⌊(ProximityGap.prizeRates j : ℝ≥0) * (Fintype.card ι : ℝ≥0)⌋₊ : Set (ι → F))
  have hdata :
      ∀ j : Fin 4,
        ∃ hne : GrandChallengesLattice.mcaThresholdExists (C j) epsStar,
          GrandChallengesLattice.mcaSatisfies (C j) epsStar
            (GrandChallengesLattice.mcaThreshold (C j) epsStar hne) ∧
            GrandChallengesLattice.latticeIndexOf (ι := ι) (δ j) (hδ_le_one j) ≤
              GrandChallengesLattice.mcaThreshold (C j) epsStar hne ∧
              GrandChallengesLattice.mcaThreshold (C j) epsStar hne <
                GrandChallengesLattice.latticeIndexOf (ι := ι) (whi j).δ (hδhi j) := by
    intro j
    simpa [C] using hall η δ hη hδ hδ_le_one L hfaithful hclear whi hδhi j
  choose hne hspec using hdata
  let τ : Fin 4 → Fin (Fintype.card ι + 1) := fun j =>
    GrandChallengesLattice.mcaThreshold (C j) epsStar (hne j)
  refine ⟨τ, ?_, ?_⟩
  · refine (GrandChallengesLattice.mcaPrizeLatticeResolved_iff domain τ).mpr ?_
    intro j
    refine ⟨hne j, ?_, ?_⟩
    · simpa [τ, C] using (hspec j).1
    · intro i hi
      simpa [τ, C] using GrandChallengesLattice.le_mcaThreshold (C j) epsStar (hne j) hi
  · intro j
    refine ⟨hne j, ?_, ?_, ?_, ?_⟩
    · simp [τ, C]
    · simpa [τ] using (hspec j).1
    · simpa [τ] using (hspec j).2.1
    · simpa [τ] using (hspec j).2.2

set_option linter.style.longLine true

end PerInput

/-! ## 3. Explicit-constant conditional reduction (open content named, no laundering) -/

section Reduction

variable {ι : Type} [Fintype ι] [Nonempty ι] [DecidableEq ι]
variable {F : Type} [Field F] [Fintype F] [DecidableEq F]

open scoped NNReal

/-- **Per-input prize from the proven pivot-covering bound plus a numeric clearance.**

Under the (open, beyond-UDR) inputs — a uniform GS list size `ℓ`, per-stack pivot covering, and
the single numeric clearance `ℓ/q ≤ epsMCAgsPrizeBound … c₁ c₂ c₃` for explicit constants — the
per-input GS prize conjecture follows from the **proved** GS list-size bound
`epsMCAgs_le_listSize_div_of_pivotCovering` (`MCAGSWitness`). The genuinely open content is
isolated into the named list-size/covering hypotheses; the assembly is sorry-free `le_trans`.
No laundering: the conjecture's existential is discharged only relative to these explicit external
inputs. Tracking: Issue #141. -/
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
#print axioms exists_prize_mcaLowerWitness_of_uniformConjecture
#print axioms exists_prize_mcaLowerWitnesses_allRates_of_uniformConjecture
#print axioms exists_mcaPrizeLatticeResolved_with_spec_of_uniformConjecture
#print axioms exists_mcaPrizeLatticeResolved_of_uniformConjecture
#print axioms exists_mcaPrizeLatticeSpec_of_uniformConjecture
#print axioms exists_mcaPrizeLatticeSpec_and_lower_brackets_of_uniformConjecture
#print axioms exists_mcaPrizeLatticeSpec_and_brackets_of_uniformConjecture
#print axioms exists_mcaPrizeLatticeResolved_with_spec_and_lower_brackets_of_uniformConjecture
#print axioms exists_mcaPrizeLatticeResolved_with_spec_and_brackets_of_uniformConjecture
#print axioms mcaThresholdExists_prize_of_uniformConjecture
#print axioms mcaThresholdExists_prize_allRates_of_uniformConjecture
#print axioms mcaThreshold_spec_prize_of_uniformConjecture
#print axioms mcaThreshold_spec_prize_allRates_of_uniformConjecture
#print axioms mcaThreshold_spec_and_lower_bracket_prize_of_uniformConjecture
#print axioms mcaThreshold_spec_and_bracket_prize_of_uniformConjecture
set_option linter.style.longLine false in
#print axioms mcaThreshold_spec_and_lower_bracket_prize_allRates_of_uniformConjecture
set_option linter.style.longLine false in
#print axioms mcaThreshold_spec_and_bracket_prize_allRates_of_uniformConjecture
set_option linter.style.longLine false in
#print axioms mcaPrizeLatticeResolved_with_threshold_spec_prize_allRates_of_uniformConjecture
set_option linter.style.longLine false in
#print axioms mcaPrizeLatticeResolved_with_threshold_prize_allRates_of_uniformConjecture
set_option linter.style.longLine false in
#print axioms mcaPrizeLatticeResolved_with_threshold_spec_and_lower_brackets_prize_allRates_of_uniformConjecture
set_option linter.style.longLine false in
#print axioms mcaPrizeLatticeResolved_with_threshold_spec_and_brackets_prize_allRates_of_uniformConjecture
#print axioms epsMCAgs_prizeBound_of_listSize_clears

end MCAGS

end ProximityGap

/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.MCAGSWitness

/-!
# Issue #141: the fixed-field uniform GS prize is a theorem; the open prize is field-universal

Issue #141 tracks the ABF26 Grand Challenge 1 prize surfaces. The GS-exposed surface
`ProximityGap.MCAGS.epsMCAgs_prizeBound_conjecture domain m` fixes the field `F` (hence
`q = |F|`), the evaluation `domain`, and the interleaving exponent `m`, quantifying the universal
constant triple *before* `∀ j η δ L`. This file proves that surface is a **theorem**
(`epsMCAgs_prizeBound_conjecture_holds`), and states the genuinely open ABF26 prize correctly as a
*field-universal* existence statement.

## Why the fixed-field surface is provable (and is **not** the open prize)

The bound is `epsMCAgsPrizeBound q m ρ η c₁ c₂ c₃ = (1/q)·(2^m)^{c₁}/(ρ^{c₂}·η^{c₃})`. Take
`c₁ = c₂ = 0` and `c₃ = n` with `(15/16)^n ≤ 1/q` (such `n` exists because `15/16 < 1`). Every prize
rate satisfies `ρ = prizeRates j = 1/2^{j+1} ≥ 1/16`, so the radius constraint `δ ≤ 1 - ρ - η` with
`δ ≥ 0` forces `η ≤ 1 - ρ ≤ 15/16` **uniformly** over the four rates. Hence
`η^n ≤ (15/16)^n ≤ 1/q`, so `epsMCAgsPrizeBound q m ρ η 0 0 n = (1/q)/η^n ≥ 1 ≥ epsMCAgs`.

The key point the earlier "open prize" reading missed: `η` is bounded *away from `1`* by the
uniform gap `15/16` (because the smallest prize rate `1/16` is bounded away from `0`), not merely
`η < 1`. One fixed exponent therefore inflates the bound past `1` for **every** valid `(j, η)` at
once — no per-input choice of `n` is needed, so the constants really are uniform.

## The genuinely open prize is *field-universal*

`epsMCAgsPrizeUniversalConjecture` quantifies the constants **before the field**, so they cannot
absorb `q = |F|`; along a family with `q → ∞` the bound `→ 0` for fixed `η` and the inflation above
fails. It is an **existence** statement: there is a *faithful* GS list family (`epsMCA ≤ epsMCAgs`,
which rules out the trivial empty family) meeting the bound. A `∀ L` field-universal form would be
*false* — an adversarial large `L` keeps `epsMCAgs = Ω(1)` while the bound vanishes — so it is the
existence of the genuine Guruswami–Sudan decoder family that is the open content (the beyond-UDR
list-decoder mass bound, absent from mathlib). `epsMCA_le_of_universalGSConjecture` bridges it to a
polynomial bound on the abstract `epsMCA`, the GS-exposed analogue of
`GrandChallenges.mcaConjecture`.

## References
- [ABF26] §1 Grand MCA Challenge; §4.5 `conj:mca-conjecture`.
- Tracking: Issue #141.
-/

namespace ProximityGap

open NNReal Code
open scoped ProbabilityTheory BigOperators NNReal

namespace MCAGS

section Resolved

variable {ι : Type} [Fintype ι] [Nonempty ι] [DecidableEq ι]
variable {F : Type} [Field F] [Fintype F] [DecidableEq F]

/-- Every prize rate is at least `1/16`: `prizeRates j = 1/2^(j+1)` with `j+1 ≤ 4`. -/
theorem prizeRates_ge_inv_sixteen (j : Fin 4) :
    (1 / 16 : ℝ) ≤ (ProximityGap.prizeRates j : ℝ) := by
  have hj : j.val + 1 ≤ 4 := by omega
  have h2 : (2 : ℝ) ^ (j.val + 1) ≤ 16 := by
    calc (2 : ℝ) ^ (j.val + 1) ≤ (2 : ℝ) ^ 4 := pow_le_pow_right₀ (by norm_num) hj
      _ = 16 := by norm_num
  have hpos : (0 : ℝ) < 2 ^ (j.val + 1) := by positivity
  unfold ProximityGap.prizeRates
  push_cast
  exact one_div_le_one_div_of_le hpos h2

open Classical in
/-- **The fixed-field uniform GS-exposed prize conjecture is a theorem.**

Take `c₁ = c₂ = 0` and `c₃ = n` with `(15/16)^n ≤ 1/q`. Since `prizeRates j ≥ 1/16`, the radius
constraint forces `η ≤ 1 - ρ - δ ≤ 15/16` uniformly, so `η^n ≤ (15/16)^n ≤ 1/q` and
`epsMCAgsPrizeBound q m ρ η 0 0 n = (1/q)/η^n ≥ 1 ≥ epsMCAgs`. See the module docstring. -/
theorem epsMCAgs_prizeBound_conjecture_holds (domain : ι ↪ F) (m : ℕ) :
    epsMCAgs_prizeBound_conjecture domain m := by
  have hqpos : (0 : ℝ) < (Fintype.card F : ℝ) := by exact_mod_cast Fintype.card_pos
  obtain ⟨n, hn⟩ :=
    exists_pow_lt_of_lt_one
      (show (0 : ℝ) < 1 / (Fintype.card F : ℝ) by positivity)
      (show (15 / 16 : ℝ) < 1 by norm_num)
  refine ⟨0, 0, (n : ℝ), ?_⟩
  intro j η δ hη hδ L
  have hηpos : (0 : ℝ) < (η : ℝ) := by exact_mod_cast hη
  have hη0 : (0 : ℝ) ≤ (η : ℝ) := le_of_lt hηpos
  have hδ0 : (0 : ℝ) ≤ (δ : ℝ) := (δ : ℝ≥0).coe_nonneg
  have hρ : (1 / 16 : ℝ) ≤ (ProximityGap.prizeRates j : ℝ) := prizeRates_ge_inv_sixteen j
  have hηle : (η : ℝ) ≤ 15 / 16 := by linarith
  have hηpow_le : (η : ℝ) ^ n ≤ (15 / 16 : ℝ) ^ n := by gcongr
  have hclear : (η : ℝ) ^ n ≤ 1 / (Fintype.card F : ℝ) := le_trans hηpow_le hn.le
  have hηpow_pos : (0 : ℝ) < (η : ℝ) ^ n := by positivity
  have hbound : (1 : ℝ) ≤
      epsMCAgsPrizeBound (Fintype.card F) m (ProximityGap.prizeRates j) η 0 0 (n : ℝ) := by
    unfold epsMCAgsPrizeBound
    rw [Real.rpow_zero, Real.rpow_zero, Real.rpow_natCast, mul_one, one_mul]
    rw [le_div_iff₀ hηpow_pos, one_mul]
    exact hclear
  have hofr : (1 : ENNReal) ≤ ENNReal.ofReal
      (epsMCAgsPrizeBound (Fintype.card F) m (ProximityGap.prizeRates j) η 0 0 (n : ℝ)) := by
    rw [← ENNReal.ofReal_one]; exact ENNReal.ofReal_le_ofReal hbound
  have hle1 : epsMCAgs (F := F)
      ((ReedSolomon.code (domain := domain)
        ⌊(ProximityGap.prizeRates j : ℝ≥0) * (Fintype.card ι : ℝ≥0)⌋₊ : Set (ι → F))) δ L ≤ 1 := by
    unfold epsMCAgs; exact iSup_le fun u => Pr_le_one _ _
  exact le_trans hle1 hofr

end Resolved

/-! ## The genuinely open prize: the field-universal Guruswami–Sudan form -/

/-- **The genuine open ABF26 Grand Challenge 1 prize, GS-exposed (field-universal form).**

One universal constant triple, quantified *before the field*, such that for **every** finite field
`F`, domain, prize rate `j`, gap `η > 0`, and radius `δ ≤ 1 - ρ - η`, there **exists a faithful GS
list family** `L` — faithful in the sense `epsMCA ≤ epsMCAgs … L`, which rules out the trivial
empty family — whose GS-exposed error meets the polynomial mass bound.

The constants precede the field, so they cannot absorb `q = |F|`: along a family with `q → ∞` the
bound `→ 0` for fixed `η`, so the fixed-field inflation of `epsMCAgs_prizeBound_conjecture_holds`
cannot apply. A `∀ L` strengthening would be *false*; it is the *existence* of the genuine
Guruswami–Sudan decoder family that is open. Deliberately **unproved**: its proof is the beyond-UDR
Guruswami–Sudan list-decoder mass bound. Tracking: Issue #141. -/
def epsMCAgsPrizeUniversalConjecture (m : ℕ) : Prop :=
  ∃ c₁ c₂ c₃ : ℝ,
    ∀ {ι : Type} [Fintype ι] [Nonempty ι] [DecidableEq ι]
      {F : Type} [Field F] [Fintype F] [DecidableEq F]
      (domain : ι ↪ F) (j : Fin 4) (η δ : ℝ≥0),
      0 < η →
      (δ : ℝ) ≤ 1 - (ProximityGap.prizeRates j : ℝ) - (η : ℝ) →
      ∃ L : WordStack F (Fin 2) ι → Finset (ι → F),
        epsMCA (F := F) (A := F)
            ((ReedSolomon.code (domain := domain)
              ⌊(ProximityGap.prizeRates j : ℝ≥0) * (Fintype.card ι : ℝ≥0)⌋₊ : Set (ι → F))) δ
          ≤ epsMCAgs (F := F)
            ((ReedSolomon.code (domain := domain)
              ⌊(ProximityGap.prizeRates j : ℝ≥0) * (Fintype.card ι : ℝ≥0)⌋₊ : Set (ι → F))) δ L ∧
        epsMCAgs (F := F)
          ((ReedSolomon.code (domain := domain)
            ⌊(ProximityGap.prizeRates j : ℝ≥0) * (Fintype.card ι : ℝ≥0)⌋₊ : Set (ι → F))) δ L
        ≤ ENNReal.ofReal
            (epsMCAgsPrizeBound (Fintype.card F) m (ProximityGap.prizeRates j) η c₁ c₂ c₃)

/-- **The genuine GS prize transfers to the abstract `epsMCA` prize.** From a faithful GS family
meeting the GS-exposed mass bound, `epsMCA ≤ epsMCAgs ≤ bound`, with the same field-universal
constant triple — the honest bridge from the GS-exposed open prize to a
`GrandChallenges.mcaConjecture`-style polynomial bound on the abstract `epsMCA`. -/
theorem epsMCA_le_of_universalGSConjecture (m : ℕ)
    (hUniv : epsMCAgsPrizeUniversalConjecture m) :
    ∃ c₁ c₂ c₃ : ℝ,
      ∀ {ι : Type} [Fintype ι] [Nonempty ι] [DecidableEq ι]
        {F : Type} [Field F] [Fintype F] [DecidableEq F]
        (domain : ι ↪ F) (j : Fin 4) (η δ : ℝ≥0),
        0 < η →
        (δ : ℝ) ≤ 1 - (ProximityGap.prizeRates j : ℝ) - (η : ℝ) →
        epsMCA (F := F) (A := F)
          ((ReedSolomon.code (domain := domain)
            ⌊(ProximityGap.prizeRates j : ℝ≥0) * (Fintype.card ι : ℝ≥0)⌋₊ : Set (ι → F))) δ
        ≤ ENNReal.ofReal
            (epsMCAgsPrizeBound (Fintype.card F) m (ProximityGap.prizeRates j) η c₁ c₂ c₃) := by
  obtain ⟨c₁, c₂, c₃, hbound⟩ := hUniv
  refine ⟨c₁, c₂, c₃, ?_⟩
  intro ι _ _ _ F _ _ _ domain j η δ hη hδ
  obtain ⟨L, hfaithful, hle⟩ := hbound domain j η δ hη hδ
  exact le_trans hfaithful hle

/-! ## The honest open core, isolated (no laundering)

`epsMCAgsPrizeUniversalConjecture` reduces — with no other assumption — to a *single* named
hypothesis: a field-universal beyond-UDR Guruswami–Sudan list-mass bound. The reduction routes
through the already-**proved** `epsMCAgs_le_listSize_div_of_pivotCovering` (`epsMCAgs ≤ ℓ/q` under
pivot covering and list size `≤ ℓ`), so the only open content is the *existence* of the uniform GS
list family with a polynomial size clearing the bound — exactly the classical Guruswami–Sudan mass
bound at radius `δ ≤ 1 - ρ - η`, which is absent from mathlib. This is not laundering: the open
content stays an explicit named hypothesis, and everything else is unconditional. -/

/-- **The field-universal beyond-UDR Guruswami–Sudan list-mass hypothesis** — the isolated open
core of the universal prize. One constant triple and, for every field/domain/prize-rate/gap/radius,
a GS list family `L` that is faithful (`epsMCA ≤ epsMCAgs`), pivot-covering, of list size `≤ ℓ`,
with `ℓ/q` clearing the polynomial mass bound. -/
def UniversalGSListMassBound (m : ℕ) : Prop :=
  ∃ c₁ c₂ c₃ : ℝ,
    ∀ {ι : Type} [Fintype ι] [Nonempty ι] [DecidableEq ι]
      {F : Type} [Field F] [Fintype F] [DecidableEq F]
      (domain : ι ↪ F) (j : Fin 4) (η δ : ℝ≥0),
      0 < η →
      (δ : ℝ) ≤ 1 - (ProximityGap.prizeRates j : ℝ) - (η : ℝ) →
      ∃ (L : WordStack F (Fin 2) ι → Finset (ι → F)) (ℓ : ℕ),
        FaithfulGSFamily (F := F)
            ((ReedSolomon.code (domain := domain)
              ⌊(ProximityGap.prizeRates j : ℝ≥0) * (Fintype.card ι : ℝ≥0)⌋₊ : Set (ι → F))) δ L ∧
          (∀ u, PivotCovering (F := F)
            ((ReedSolomon.code (domain := domain)
              ⌊(ProximityGap.prizeRates j : ℝ≥0) * (Fintype.card ι : ℝ≥0)⌋₊ : Set (ι → F))) δ L u) ∧
          (∀ u, (L u).card ≤ ℓ) ∧
          ((ℓ : ENNReal) / (Fintype.card F : ENNReal)
            ≤ ENNReal.ofReal
                (epsMCAgsPrizeBound (Fintype.card F) m (ProximityGap.prizeRates j) η c₁ c₂ c₃))

/-- **The universal prize reduces to the beyond-UDR GS list-mass bound, with nothing else.**
The proof uses only the proved pivot-covering bound and `le_trans`; the entire open content lives in
the named hypothesis `UniversalGSListMassBound`. -/
theorem epsMCAgsPrizeUniversalConjecture_of_UniversalGSListMassBound (m : ℕ)
    (h : UniversalGSListMassBound m) :
    epsMCAgsPrizeUniversalConjecture m := by
  obtain ⟨c₁, c₂, c₃, H⟩ := h
  refine ⟨c₁, c₂, c₃, ?_⟩
  intro ι _ _ _ F _ _ _ domain j η δ hη hδ
  obtain ⟨L, ℓ, hfaithful, hcov, hsize, hclear⟩ := H domain j η δ hη hδ
  refine ⟨L, hfaithful, ?_⟩
  exact le_trans (epsMCAgs_le_listSize_div_of_pivotCovering _ δ L ℓ hcov hsize) hclear

/-! ## Closing out the consumers: the proven conjecture discharges its downstream adapters -/

section Consumers

variable {ι : Type} [Fintype ι] [Nonempty ι] [DecidableEq ι]
variable {F : Type} [Field F] [Fintype F] [DecidableEq F]

/-- **Unconditional prize lower-witness existence.** The `_of_uniformConjecture` adapters in
`GrandChallenge141PrizeMath` take `epsMCAgs_prizeBound_conjecture domain m` as a hypothesis; since
that surface is now the theorem `epsMCAgs_prizeBound_conjecture_holds`, the flagship consumer holds
**unconditionally** in the conjecture: one constant triple such that, given only the still-explicit
GS faithfulness and the numeric clearance `bound ≤ ε*`, every ABF26 prize rate admits an
`MCALowerWitness` at radius `δ`. (Faithfulness and clearance remain genuine explicit inputs; only
the conjecture hypothesis is discharged.) -/
theorem exists_prize_mcaLowerWitness_unconditional (domain : ι ↪ F) (m : ℕ) :
    ∃ c₁ c₂ c₃ : ℝ,
      ∀ (j : Fin 4) (η δ : ℝ≥0),
        0 < η →
        (δ : ℝ) ≤ 1 - (ProximityGap.prizeRates j : ℝ) - (η : ℝ) →
        δ ≤ 1 →
        ∀ L : WordStack F (Fin 2) ι → Finset (ι → F),
          FaithfulGSFamily (F := F)
            ((ReedSolomon.code (domain := domain)
              ⌊(ProximityGap.prizeRates j : ℝ≥0) * (Fintype.card ι : ℝ≥0)⌋₊ : Set (ι → F))) δ L →
          ENNReal.ofReal
              (epsMCAgsPrizeBound (Fintype.card F) m (ProximityGap.prizeRates j) η c₁ c₂ c₃)
            ≤ (epsStar : ENNReal) →
          ∃ w : GrandChallenges.MCALowerWitness
            ((ReedSolomon.code (domain := domain)
              ⌊(ProximityGap.prizeRates j : ℝ≥0) * (Fintype.card ι : ℝ≥0)⌋₊ :
                Set (ι → F))) epsStar,
            w.δ = δ := by
  obtain ⟨c₁, c₂, c₃, hbound⟩ := epsMCAgs_prizeBound_conjecture_holds domain m
  refine ⟨c₁, c₂, c₃, ?_⟩
  intro j η δ hη hδ hδ_le_one L hfaithful hclear
  let C : Set (ι → F) :=
    (ReedSolomon.code (domain := domain)
      ⌊(ProximityGap.prizeRates j : ℝ≥0) * (Fintype.card ι : ℝ≥0)⌋₊ : Set (ι → F))
  have hMass : epsMCAgsMassBound (F := F) C δ L
      (ENNReal.ofReal
        (epsMCAgsPrizeBound (Fintype.card F) m (ProximityGap.prizeRates j) η c₁ c₂ c₃)) :=
    epsMCAgsMassBound_of_epsMCAgs_le C δ L (hbound j η δ hη hδ L)
  have hMassStar : epsMCAgsMassBound (F := F) C δ L (epsStar : ENNReal) :=
    epsMCAgsMassBound.mono hMass hclear
  exact ⟨GrandChallenges.MCALowerWitness.ofLe (C := C) (ε_star := epsStar) (δ := δ) hδ_le_one
    (epsMCA_le_of_faithful_mass (F := F) C δ L hfaithful hMassStar), rfl⟩

end Consumers

/-! ## Source audit -/

#print axioms epsMCAgs_prizeBound_conjecture_holds
#print axioms epsMCAgsPrizeUniversalConjecture
#print axioms epsMCA_le_of_universalGSConjecture
#print axioms epsMCAgsPrizeUniversalConjecture_of_UniversalGSListMassBound
#print axioms exists_prize_mcaLowerWitness_unconditional

end MCAGS

end ProximityGap

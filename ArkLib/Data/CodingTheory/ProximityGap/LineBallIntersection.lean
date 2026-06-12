/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import Mathlib.InformationTheory.Hamming
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.Data.Fintype.BigOperators

set_option linter.style.longLine false

/-!
# Line–ball intersection: the `1/q` mechanism for the MCA grand challenge

This is a foundational, self-contained combinatorial lemma toward the ABF26 §4.5 MCA conjecture
(`ProximityGap.mcaConjecture`): a *fixed* codeword `w` is `δ`-close to a **non-degenerate** affine
line `γ ↦ u₀ + γ•u₁` for only very few `γ`.

  `#{γ : Δ₀(u₀+γ•u₁, w) ≤ R} · (|supp u₁| − R) ≤ |supp u₁|`.

This is the source of the conjecture's `1/q` factor: averaging over `γ ← $ᵖ F`, the per-codeword
closeness probability is `≤ |supp u₁| / (q·(|supp u₁| − R))`.  Coordinate-wise, on `T = supp(u₁)`
each `i` forces line-agreement with `w` at a *unique* `γ_i = (w i − u₀ i)/u₁ i`, so the agreement
sets `{i ∈ T : (u₀+γ•u₁) i = w i}` are pairwise disjoint across `γ`; a `γ` within radius `R` has
agreement `≥ |T| − R`, and disjoint sets that large number at most `|T| / (|T| − R)`.

## Strategy (MCA grand challenge)

`ε_mca(C,δ) = sup_u Pr_γ[mcaEvent]`, and the bad event implies *some* `w ∈ C` is `δ`-close to the
line `u₀+γ•u₁`.  A union bound over codewords plus this lemma gives

  `ε_mca(C,δ) ≤ (1/q) · N_line · M`,   `M = |supp u₁|/(|supp u₁| − R)`,

where `N_line = #{w ∈ C : w is δ-close to some point of the line}`.  Since `M = O(1/ρ)` below
capacity, the conjecture **reduces to** the list-decoding count `N_line ≤ poly(n)` — Johnson gives it
up to `1 − √ρ`, and capacity `1 − ρ` is the open core.

## Main result

* `card_close_gamma_le` — the line–ball intersection bound (multiplicative, lossless form).
* `card_close_gamma_le_div` — its `Nat`-division form `#{close γ} ≤ |supp u₁| / (|supp u₁| − R)`.
-/

open scoped BigOperators
open Polynomial Finset

namespace ProximityGap

set_option linter.unusedSectionVars false
set_option linter.unusedFintypeInType false
set_option linter.unusedDecidableInType false

variable {ι : Type*} [Fintype ι] [DecidableEq ι]
variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

/-- **Line–ball intersection bound (the `1/q` mechanism).** A non-degenerate affine line
`γ ↦ u₀ + γ•u₁` is within Hamming radius `R` of a *fixed* word `w` for very few `γ`:
`#{γ : Δ₀(u₀+γ•u₁, w) ≤ R} · (|supp u₁| − R) ≤ |supp u₁|`. -/
theorem card_close_gamma_le (u₀ u₁ w : ι → F) (R : ℕ) :
    (univ.filter (fun γ : F => hammingDist (u₀ + γ • u₁) w ≤ R)).card
        * ((univ.filter (fun i => u₁ i ≠ 0)).card - R)
      ≤ (univ.filter (fun i => u₁ i ≠ 0)).card := by
  classical
  set T : Finset ι := univ.filter (fun i => u₁ i ≠ 0) with hT
  set G : Finset F := univ.filter (fun γ : F => hammingDist (u₀ + γ • u₁) w ≤ R) with hG
  -- (1) every `γ ∈ G` agrees with `w` on `≥ |T| − R` coordinates of `T`
  have hAge : ∀ γ ∈ G, (T.card - R)
      ≤ (T.filter (fun i => (u₀ + γ • u₁) i = w i)).card := by
    intro γ hγ
    rw [hG, Finset.mem_filter] at hγ
    have key := Finset.card_filter_add_card_filter_not (s := T)
      (fun i => (u₀ + γ • u₁) i = w i)
    have hcard : ({a ∈ T | ¬ ((u₀ + γ • u₁) a = w a)}).card ≤ R := by
      refine le_trans (Finset.card_le_card (fun i hi =>
        Finset.mem_filter.mpr ⟨mem_univ _, (Finset.mem_filter.mp hi).2⟩)) ?_
      exact hγ.2
    omega
  -- (2) the per-`γ` agreement sets are pairwise disjoint (each `i ∈ T` forces a unique `γ`)
  have hdisj : (G : Set F).PairwiseDisjoint
      (fun γ => T.filter (fun i => (u₀ + γ • u₁) i = w i)) := by
    intro γ _ γ' _ hne
    rw [Function.onFun, Finset.disjoint_left]
    intro i hi hi'
    rw [Finset.mem_filter] at hi hi'
    have hu1 : u₁ i ≠ 0 := by rw [hT, Finset.mem_filter] at hi; exact hi.1.2
    apply hne
    have heq : γ • u₁ i = γ' • u₁ i := by
      have := hi.2.trans hi'.2.symm
      simpa [Pi.add_apply, Pi.smul_apply] using this
    simp only [smul_eq_mul] at heq
    exact mul_right_cancel₀ hu1 heq
  -- (3) so the agreement sets sum (disjointly) to at most `|T|`
  have hsum : ∑ γ ∈ G, (T.filter (fun i => (u₀ + γ • u₁) i = w i)).card ≤ T.card := by
    rw [← Finset.card_biUnion hdisj]
    refine Finset.card_le_card (fun i hi => ?_)
    rw [Finset.mem_biUnion] at hi
    obtain ⟨γ, _, hiγ⟩ := hi
    exact (Finset.filter_subset _ _) hiγ
  -- (4) combine: `|G| · (|T| − R) ≤ ∑ agreement ≤ |T|`
  calc G.card * (T.card - R)
      = ∑ _γ ∈ G, (T.card - R) := by rw [Finset.sum_const, smul_eq_mul]
    _ ≤ ∑ γ ∈ G, (T.filter (fun i => (u₀ + γ • u₁) i = w i)).card := Finset.sum_le_sum hAge
    _ ≤ T.card := hsum

/-- `Nat`-division form: when the line is non-degenerate (`R < |supp u₁|`), at most
`|supp u₁| / (|supp u₁| − R)` values of `γ` are within radius `R` of a fixed `w`. -/
theorem card_close_gamma_le_div (u₀ u₁ w : ι → F) (R : ℕ)
    (hR : R < (univ.filter (fun i => u₁ i ≠ 0)).card) :
    (univ.filter (fun γ : F => hammingDist (u₀ + γ • u₁) w ≤ R)).card
      ≤ (univ.filter (fun i => u₁ i ≠ 0)).card
          / ((univ.filter (fun i => u₁ i ≠ 0)).card - R) := by
  rw [Nat.le_div_iff_mul_le (by omega)]
  exact card_close_gamma_le u₀ u₁ w R

/-! ## Ratio-census form for the zero-centred line ball -/

/-- The scalar that makes the affine line coordinate `u₀ i + γ * u₁ i` vanish, when
`u₁ i ≠ 0`.  On zero-slope coordinates the value is harmless filler; consumers should pair it with
the support condition in `lineRatioHits`. -/
def lineZeroRoot (u₀ u₁ : ι → F) (i : ι) : F :=
  -u₀ i / u₁ i

/-- Coordinates whose moving part is nonzero and whose zero-root is exactly `γ`.  This is the
ratio-census fibre `{i : u₁ i ≠ 0 ∧ γ = -u₀ i / u₁ i}` up to equality symmetry. -/
def lineRatioHits (u₀ u₁ : ι → F) (γ : F) : Finset ι :=
  univ.filter (fun i => u₁ i ≠ 0 ∧ lineZeroRoot u₀ u₁ i = γ)

/-- Zero-slope coordinates that are nonzero for every scalar on the line. -/
def lineStaticNonzero (u₀ u₁ : ι → F) : Finset ι :=
  univ.filter (fun i => u₁ i = 0 ∧ u₀ i ≠ 0)

/-- On a nonzero-slope coordinate, the affine line vanishes exactly at the ratio-census root. -/
theorem line_coord_zero_iff_lineZeroRoot {u₀ u₁ : ι → F} {γ : F} {i : ι}
    (hi : u₁ i ≠ 0) :
    (u₀ + γ • u₁) i = 0 ↔ lineZeroRoot u₀ u₁ i = γ := by
  simp only [lineZeroRoot, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  rw [div_eq_iff hi]
  constructor
  · intro h
    have h' : u₀ i = -(γ * u₁ i) := eq_neg_of_add_eq_zero_left h
    rw [h']
    ring
  · intro h
    rw [← h]
    ring

/-- **Ratio-census identity, additive form.**  Along the zero-centred affine line,
the Hamming weight plus the multiplicity of the selected ratio equals
`|supp u₁|` plus the always-nonzero zero-slope coordinates. -/
theorem hammingNorm_line_add_lineRatioHits_card (u₀ u₁ : ι → F) (γ : F) :
    hammingNorm (u₀ + γ • u₁) + (lineRatioHits u₀ u₁ γ).card
      = (univ.filter (fun i => u₁ i ≠ 0)).card + (lineStaticNonzero u₀ u₁).card := by
  classical
  set N : Finset ι := univ.filter (fun i => (u₀ + γ • u₁) i ≠ 0) with hN
  set W : Finset ι := univ.filter (fun i => u₁ i ≠ 0) with hW
  set H : Finset ι := lineRatioHits u₀ u₁ γ with hH
  set Z : Finset ι := lineStaticNonzero u₀ u₁ with hZ
  have hZeq : N.filter (fun i => u₁ i = 0) = Z := by
    ext i
    simp only [hN, hZ, lineStaticNonzero, Finset.mem_filter, Finset.mem_univ, true_and]
    constructor
    · rintro ⟨hn, h0⟩
      exact ⟨h0, by simpa [Pi.add_apply, Pi.smul_apply, smul_eq_mul, h0] using hn⟩
    · rintro ⟨h0, hu₀⟩
      exact ⟨by simpa [Pi.add_apply, Pi.smul_apply, smul_eq_mul, h0] using hu₀, h0⟩
  have hNeq : N.filter (fun i => ¬ u₁ i = 0)
      = W.filter (fun i => ¬ lineZeroRoot u₀ u₁ i = γ) := by
    ext i
    simp only [hN, hW, Finset.mem_filter, Finset.mem_univ, true_and]
    constructor
    · rintro ⟨hn, hi⟩
      refine ⟨hi, ?_⟩
      intro hroot
      exact hn ((line_coord_zero_iff_lineZeroRoot (u₀ := u₀) (u₁ := u₁)
        (γ := γ) (i := i) hi).mpr hroot)
    · rintro ⟨hi, hroot⟩
      refine ⟨?_, hi⟩
      intro hzero
      exact hroot ((line_coord_zero_iff_lineZeroRoot (u₀ := u₀) (u₁ := u₁)
        (γ := γ) (i := i) hi).mp hzero)
  have hHeq : H = W.filter (fun i => lineZeroRoot u₀ u₁ i = γ) := by
    ext i
    simp only [hH, hW, lineRatioHits, Finset.mem_filter, Finset.mem_univ, true_and]
  have hNsplit :
      Z.card + (W.filter (fun i => ¬ lineZeroRoot u₀ u₁ i = γ)).card = N.card := by
    simpa [hZeq, hNeq] using
      (Finset.card_filter_add_card_filter_not (s := N) (p := fun i => u₁ i = 0))
  have hWsplit :
      H.card + (W.filter (fun i => ¬ lineZeroRoot u₀ u₁ i = γ)).card = W.card := by
    simpa [hHeq] using
      (Finset.card_filter_add_card_filter_not (s := W)
        (p := fun i => lineZeroRoot u₀ u₁ i = γ))
  have hnorm : hammingNorm (u₀ + γ • u₁) = N.card := by
    simp [hammingNorm, hN]
  calc
    hammingNorm (u₀ + γ • u₁) + H.card
        = N.card + H.card := by rw [hnorm]
    _ = W.card + Z.card := by omega

/-- **Ratio-census identity, subtraction form.**  This is the research-map identity
`wt(u₀ + γu₁) = |supp u₁| - #{i : u₁ᵢ ≠ 0 ∧ γ = -u₀ᵢ/u₁ᵢ}
  + #{i : u₁ᵢ = 0 ∧ u₀ᵢ ≠ 0}`. -/
theorem hammingNorm_line_eq_support_sub_lineRatioHits_card_add_static
    (u₀ u₁ : ι → F) (γ : F) :
    hammingNorm (u₀ + γ • u₁)
      = (univ.filter (fun i => u₁ i ≠ 0)).card - (lineRatioHits u₀ u₁ γ).card
          + (lineStaticNonzero u₀ u₁).card := by
  have hmain := hammingNorm_line_add_lineRatioHits_card (u₀ := u₀) (u₁ := u₁) γ
  have hsub : (lineRatioHits u₀ u₁ γ).card ≤ (univ.filter (fun i => u₁ i ≠ 0)).card := by
    refine Finset.card_le_card ?_
    intro i hi
    rw [lineRatioHits, Finset.mem_filter] at hi
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ i, hi.2.1⟩
  omega

/-- The ratio-census fibres have total mass exactly `|supp u₁|`: every moving coordinate
contributes to exactly one scalar root. -/
theorem sum_lineRatioHits_card_eq_support (u₀ u₁ : ι → F) :
    ∑ γ : F, (lineRatioHits u₀ u₁ γ).card
      = (univ.filter (fun i => u₁ i ≠ 0)).card := by
  classical
  set W : Finset ι := univ.filter (fun i => u₁ i ≠ 0) with hW
  have hfiber : ∀ γ : F,
      lineRatioHits u₀ u₁ γ = W.filter (fun i => lineZeroRoot u₀ u₁ i = γ) := by
    intro γ
    ext i
    simp only [lineRatioHits, hW, Finset.mem_filter, Finset.mem_univ, true_and]
  calc
    ∑ γ : F, (lineRatioHits u₀ u₁ γ).card
        = ∑ γ : F, (W.filter (fun i => lineZeroRoot u₀ u₁ i = γ)).card := by
          refine Finset.sum_congr rfl ?_
          intro γ _
          rw [hfiber γ]
    _ = W.card := by
          rw [← Finset.card_eq_sum_card_fiberwise
            (fun i _ => Finset.mem_univ (lineZeroRoot u₀ u₁ i))]

/-- Heavy ratio fibres are few.  This is the direct Markov/counting form of the ratio census. -/
theorem lineRatioHeavy_card_mul_le_support (u₀ u₁ : ι → F) (A : ℕ) :
    (univ.filter (fun γ : F => A ≤ (lineRatioHits u₀ u₁ γ).card)).card * A
      ≤ (univ.filter (fun i => u₁ i ≠ 0)).card := by
  classical
  set G : Finset F := univ.filter (fun γ : F => A ≤ (lineRatioHits u₀ u₁ γ).card) with hG
  calc
    G.card * A = ∑ _γ ∈ G, A := by rw [Finset.sum_const, smul_eq_mul]
    _ ≤ ∑ γ ∈ G, (lineRatioHits u₀ u₁ γ).card := by
          refine Finset.sum_le_sum ?_
          intro γ hγ
          rw [hG, Finset.mem_filter] at hγ
          exact hγ.2
    _ ≤ ∑ γ : F, (lineRatioHits u₀ u₁ γ).card :=
          Finset.sum_le_sum_of_subset (Finset.subset_univ G)
    _ = (univ.filter (fun i => u₁ i ≠ 0)).card := sum_lineRatioHits_card_eq_support u₀ u₁

/-- Low Hamming weight on the line forces a heavy ratio fibre, so the low-weight scalars satisfy
the corresponding ratio-census bound.  The extra `lineStaticNonzero` term sharpens the basic
line-ball bound when zero-slope coordinates are permanently nonzero. -/
theorem card_low_hammingNorm_gamma_mul_le_support (u₀ u₁ : ι → F) (R : ℕ) :
    (univ.filter (fun γ : F => hammingNorm (u₀ + γ • u₁) ≤ R)).card
        * ((univ.filter (fun i => u₁ i ≠ 0)).card + (lineStaticNonzero u₀ u₁).card - R)
      ≤ (univ.filter (fun i => u₁ i ≠ 0)).card := by
  classical
  set A : ℕ :=
    (univ.filter (fun i => u₁ i ≠ 0)).card + (lineStaticNonzero u₀ u₁).card - R with hA
  set G : Finset F := univ.filter (fun γ : F => hammingNorm (u₀ + γ • u₁) ≤ R) with hG
  set H : Finset F := univ.filter (fun γ : F => A ≤ (lineRatioHits u₀ u₁ γ).card) with hH
  have hsub : G ⊆ H := by
    intro γ hγ
    rw [hG, Finset.mem_filter] at hγ
    rw [hH, Finset.mem_filter]
    refine ⟨Finset.mem_univ γ, ?_⟩
    have hmain := hammingNorm_line_add_lineRatioHits_card (u₀ := u₀) (u₁ := u₁) γ
    omega
  calc
    G.card * A ≤ H.card * A := Nat.mul_le_mul_right A (Finset.card_le_card hsub)
    _ ≤ (univ.filter (fun i => u₁ i ≠ 0)).card :=
          lineRatioHeavy_card_mul_le_support (u₀ := u₀) (u₁ := u₁) A

/-- Low zero-centred Hamming weight forces a large ratio fibre. -/
theorem lineRatioHits_card_ge_of_hammingNorm_le
    (u₀ u₁ : ι → F) (γ : F) {R : ℕ}
    (hR : hammingNorm (u₀ + γ • u₁) ≤ R) :
    (univ.filter (fun i => u₁ i ≠ 0)).card + (lineStaticNonzero u₀ u₁).card - R
      ≤ (lineRatioHits u₀ u₁ γ).card := by
  have hmain := hammingNorm_line_add_lineRatioHits_card (u₀ := u₀) (u₁ := u₁) γ
  omega

/-! ## Ratio-census form for a line ball around an arbitrary centre -/

/-- The scalar that makes the affine line coordinate agree with a fixed centre `w`, when
`u₁ i ≠ 0`.  As with `lineZeroRoot`, zero-slope coordinates are ignored by the fibre. -/
def lineAgreementRoot (u₀ u₁ w : ι → F) (i : ι) : F :=
  (w i - u₀ i) / u₁ i

/-- Moving coordinates whose agreement root with `w` is exactly `γ`. -/
def lineAgreementHits (u₀ u₁ w : ι → F) (γ : F) : Finset ι :=
  univ.filter (fun i => u₁ i ≠ 0 ∧ lineAgreementRoot u₀ u₁ w i = γ)

/-- Zero-slope coordinates that disagree with `w` for every scalar on the line. -/
def lineStaticDisagreement (u₀ u₁ w : ι → F) : Finset ι :=
  univ.filter (fun i => u₁ i = 0 ∧ u₀ i ≠ w i)

/-- On a nonzero-slope coordinate, line agreement with `w` happens exactly at the
agreement root. -/
theorem line_coord_eq_iff_lineAgreementRoot {u₀ u₁ w : ι → F} {γ : F} {i : ι}
    (hi : u₁ i ≠ 0) :
    (u₀ + γ • u₁) i = w i ↔ lineAgreementRoot u₀ u₁ w i = γ := by
  simp only [lineAgreementRoot, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  rw [div_eq_iff hi]
  constructor
  · intro h
    rw [← h]
    ring
  · intro h
    rw [← h]
    ring

/-- **Ratio-census identity for a centred line ball, additive form.**  Distance from
`u₀ + γu₁` to `w`, plus the multiplicity of the selected agreement ratio, is the moving
support plus the permanently-disagreeing zero-slope coordinates. -/
theorem hammingDist_line_add_lineAgreementHits_card (u₀ u₁ w : ι → F) (γ : F) :
    hammingDist (u₀ + γ • u₁) w + (lineAgreementHits u₀ u₁ w γ).card
      = (univ.filter (fun i => u₁ i ≠ 0)).card
          + (lineStaticDisagreement u₀ u₁ w).card := by
  classical
  set N : Finset ι := univ.filter (fun i => (u₀ + γ • u₁) i ≠ w i) with hN
  set W : Finset ι := univ.filter (fun i => u₁ i ≠ 0) with hW
  set H : Finset ι := lineAgreementHits u₀ u₁ w γ with hH
  set Z : Finset ι := lineStaticDisagreement u₀ u₁ w with hZ
  have hZeq : N.filter (fun i => u₁ i = 0) = Z := by
    ext i
    simp only [hN, hZ, lineStaticDisagreement, Finset.mem_filter, Finset.mem_univ, true_and]
    constructor
    · rintro ⟨hn, h0⟩
      exact ⟨h0, by simpa [Pi.add_apply, Pi.smul_apply, smul_eq_mul, h0] using hn⟩
    · rintro ⟨h0, hu₀⟩
      exact ⟨by simpa [Pi.add_apply, Pi.smul_apply, smul_eq_mul, h0] using hu₀, h0⟩
  have hNeq : N.filter (fun i => ¬ u₁ i = 0)
      = W.filter (fun i => ¬ lineAgreementRoot u₀ u₁ w i = γ) := by
    ext i
    simp only [hN, hW, Finset.mem_filter, Finset.mem_univ, true_and]
    constructor
    · rintro ⟨hn, hi⟩
      refine ⟨hi, ?_⟩
      intro hroot
      exact hn ((line_coord_eq_iff_lineAgreementRoot (u₀ := u₀) (u₁ := u₁)
        (w := w) (γ := γ) (i := i) hi).mpr hroot)
    · rintro ⟨hi, hroot⟩
      refine ⟨?_, hi⟩
      intro hagree
      exact hroot ((line_coord_eq_iff_lineAgreementRoot (u₀ := u₀) (u₁ := u₁)
        (w := w) (γ := γ) (i := i) hi).mp hagree)
  have hHeq : H = W.filter (fun i => lineAgreementRoot u₀ u₁ w i = γ) := by
    ext i
    simp only [hH, hW, lineAgreementHits, Finset.mem_filter, Finset.mem_univ, true_and]
  have hNsplit :
      Z.card + (W.filter (fun i => ¬ lineAgreementRoot u₀ u₁ w i = γ)).card = N.card := by
    simpa [hZeq, hNeq] using
      (Finset.card_filter_add_card_filter_not (s := N) (p := fun i => u₁ i = 0))
  have hWsplit :
      H.card + (W.filter (fun i => ¬ lineAgreementRoot u₀ u₁ w i = γ)).card = W.card := by
    simpa [hHeq] using
      (Finset.card_filter_add_card_filter_not (s := W)
        (p := fun i => lineAgreementRoot u₀ u₁ w i = γ))
  have hdist : hammingDist (u₀ + γ • u₁) w = N.card := by
    simp [hammingDist, hN]
  calc
    hammingDist (u₀ + γ • u₁) w + H.card
        = N.card + H.card := by rw [hdist]
    _ = W.card + Z.card := by omega

/-- **Ratio-census identity for a centred line ball, subtraction form.** -/
theorem hammingDist_line_eq_support_sub_lineAgreementHits_card_add_static
    (u₀ u₁ w : ι → F) (γ : F) :
    hammingDist (u₀ + γ • u₁) w
      = (univ.filter (fun i => u₁ i ≠ 0)).card
          - (lineAgreementHits u₀ u₁ w γ).card
          + (lineStaticDisagreement u₀ u₁ w).card := by
  have hmain := hammingDist_line_add_lineAgreementHits_card
    (u₀ := u₀) (u₁ := u₁) (w := w) γ
  have hsub :
      (lineAgreementHits u₀ u₁ w γ).card ≤ (univ.filter (fun i => u₁ i ≠ 0)).card := by
    refine Finset.card_le_card ?_
    intro i hi
    rw [lineAgreementHits, Finset.mem_filter] at hi
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ i, hi.2.1⟩
  omega

/-- Agreement-ratio fibres have total mass exactly `|supp u₁|`. -/
theorem sum_lineAgreementHits_card_eq_support (u₀ u₁ w : ι → F) :
    ∑ γ : F, (lineAgreementHits u₀ u₁ w γ).card
      = (univ.filter (fun i => u₁ i ≠ 0)).card := by
  classical
  set W : Finset ι := univ.filter (fun i => u₁ i ≠ 0) with hW
  have hfiber : ∀ γ : F,
      lineAgreementHits u₀ u₁ w γ =
        W.filter (fun i => lineAgreementRoot u₀ u₁ w i = γ) := by
    intro γ
    ext i
    simp only [lineAgreementHits, hW, Finset.mem_filter, Finset.mem_univ, true_and]
  calc
    ∑ γ : F, (lineAgreementHits u₀ u₁ w γ).card
        = ∑ γ : F, (W.filter (fun i => lineAgreementRoot u₀ u₁ w i = γ)).card := by
          refine Finset.sum_congr rfl ?_
          intro γ _
          rw [hfiber γ]
    _ = W.card := by
          rw [← Finset.card_eq_sum_card_fiberwise
            (fun i _ => Finset.mem_univ (lineAgreementRoot u₀ u₁ w i))]

/-- Heavy agreement-ratio fibres are few. -/
theorem lineAgreementHeavy_card_mul_le_support (u₀ u₁ w : ι → F) (A : ℕ) :
    (univ.filter (fun γ : F => A ≤ (lineAgreementHits u₀ u₁ w γ).card)).card * A
      ≤ (univ.filter (fun i => u₁ i ≠ 0)).card := by
  classical
  set G : Finset F :=
    univ.filter (fun γ : F => A ≤ (lineAgreementHits u₀ u₁ w γ).card) with hG
  calc
    G.card * A = ∑ _γ ∈ G, A := by rw [Finset.sum_const, smul_eq_mul]
    _ ≤ ∑ γ ∈ G, (lineAgreementHits u₀ u₁ w γ).card := by
          refine Finset.sum_le_sum ?_
          intro γ hγ
          rw [hG, Finset.mem_filter] at hγ
          exact hγ.2
    _ ≤ ∑ γ : F, (lineAgreementHits u₀ u₁ w γ).card :=
          Finset.sum_le_sum_of_subset (Finset.subset_univ G)
    _ = (univ.filter (fun i => u₁ i ≠ 0)).card :=
          sum_lineAgreementHits_card_eq_support u₀ u₁ w

/-- Low distance to a fixed centre forces a heavy agreement-ratio fibre, hence inherits
the ratio-census counting bound.  This is the line-ball incidence bridge in multiplicity form. -/
theorem card_close_gamma_mul_le_support_add_static (u₀ u₁ w : ι → F) (R : ℕ) :
    (univ.filter (fun γ : F => hammingDist (u₀ + γ • u₁) w ≤ R)).card
        * ((univ.filter (fun i => u₁ i ≠ 0)).card
            + (lineStaticDisagreement u₀ u₁ w).card - R)
      ≤ (univ.filter (fun i => u₁ i ≠ 0)).card := by
  classical
  set A : ℕ :=
    (univ.filter (fun i => u₁ i ≠ 0)).card
      + (lineStaticDisagreement u₀ u₁ w).card - R with hA
  set G : Finset F :=
    univ.filter (fun γ : F => hammingDist (u₀ + γ • u₁) w ≤ R) with hG
  set H : Finset F :=
    univ.filter (fun γ : F => A ≤ (lineAgreementHits u₀ u₁ w γ).card) with hH
  have hsub : G ⊆ H := by
    intro γ hγ
    rw [hG, Finset.mem_filter] at hγ
    rw [hH, Finset.mem_filter]
    refine ⟨Finset.mem_univ γ, ?_⟩
    have hmain := hammingDist_line_add_lineAgreementHits_card
      (u₀ := u₀) (u₁ := u₁) (w := w) γ
    omega
  calc
    G.card * A ≤ H.card * A := Nat.mul_le_mul_right A (Finset.card_le_card hsub)
    _ ≤ (univ.filter (fun i => u₁ i ≠ 0)).card :=
          lineAgreementHeavy_card_mul_le_support (u₀ := u₀) (u₁ := u₁) (w := w) A

/-- Low distance to a fixed centre forces a large agreement-ratio fibre. -/
theorem lineAgreementHits_card_ge_of_hammingDist_le
    (u₀ u₁ w : ι → F) (γ : F) {R : ℕ}
    (hR : hammingDist (u₀ + γ • u₁) w ≤ R) :
    (univ.filter (fun i => u₁ i ≠ 0)).card + (lineStaticDisagreement u₀ u₁ w).card - R
      ≤ (lineAgreementHits u₀ u₁ w γ).card := by
  have hmain := hammingDist_line_add_lineAgreementHits_card
    (u₀ := u₀) (u₁ := u₁) (w := w) γ
  omega

/-! ## Polynomial ratio fibres -/

/-- **Polynomial ratio-level bound, with the degenerate scalar exposed.** If a line comes from
evaluating two polynomials on an injective domain, then the ratio fibre at `γ` injects into the
root set of the nonzero pencil polynomial `P₀ + γ P₁`. Thus the fibre is degree-bounded unless
that pencil polynomial vanishes identically. -/
theorem lineRatioHits_card_le_natDegree_pencil
    (domain : ι ↪ F) (P₀ P₁ : Polynomial F) (γ : F)
    (hp : P₀ + Polynomial.C γ * P₁ ≠ 0) :
    (lineRatioHits (fun i => P₀.eval (domain i)) (fun i => P₁.eval (domain i)) γ).card
      ≤ (P₀ + Polynomial.C γ * P₁).natDegree := by
  classical
  let p : Polynomial F := P₀ + Polynomial.C γ * P₁
  let u₀ : ι → F := fun i => P₀.eval (domain i)
  let u₁ : ι → F := fun i => P₁.eval (domain i)
  set H : Finset ι := lineRatioHits u₀ u₁ γ with hH
  have hsub : H.image domain ⊆ p.roots.toFinset := by
    intro x hx
    rw [Finset.mem_image] at hx
    obtain ⟨i, hiH, rfl⟩ := hx
    have hiH' : i ∈ lineRatioHits u₀ u₁ γ := by simpa [hH] using hiH
    rw [lineRatioHits, Finset.mem_filter] at hiH'
    have hzero : (u₀ + γ • u₁) i = 0 :=
      (line_coord_zero_iff_lineZeroRoot (u₀ := u₀) (u₁ := u₁)
        (γ := γ) (i := i) hiH'.2.1).mpr hiH'.2.2
    rw [Multiset.mem_toFinset, Polynomial.mem_roots hp, Polynomial.IsRoot.def]
    simpa [p, u₀, u₁, Pi.add_apply, Pi.smul_apply, smul_eq_mul,
      Polynomial.eval_add, Polynomial.eval_mul] using hzero
  change H.card ≤ p.natDegree
  calc
    H.card = (H.image domain).card := by
      rw [Finset.card_image_of_injective _ (fun _ _ h => domain.injective h)]
    _ ≤ p.roots.toFinset.card := Finset.card_le_card hsub
    _ ≤ Multiset.card p.roots := Multiset.toFinset_card_le _
    _ ≤ p.natDegree := Polynomial.card_roots' p

/-- Nondegenerate polynomial ratio fibres are bounded by the larger row degree. The only scalar
not covered is the honest degenerate case `P₀ + γ P₁ = 0`. -/
theorem lineRatioHits_card_le_max_natDegree_pencil
    (domain : ι ↪ F) (P₀ P₁ : Polynomial F) (γ : F)
    (hp : P₀ + Polynomial.C γ * P₁ ≠ 0) :
    (lineRatioHits (fun i => P₀.eval (domain i)) (fun i => P₁.eval (domain i)) γ).card
      ≤ max P₀.natDegree P₁.natDegree := by
  refine (lineRatioHits_card_le_natDegree_pencil domain P₀ P₁ γ hp).trans ?_
  exact Polynomial.natDegree_add_le_of_le (le_refl P₀.natDegree)
    (Polynomial.natDegree_C_mul_le γ P₁)

/-- Caller-facing degree-budget form of `lineRatioHits_card_le_max_natDegree_pencil`. -/
theorem lineRatioHits_card_le_degreeBound_pencil
    (domain : ι ↪ F) (P₀ P₁ : Polynomial F) (γ : F) {D : ℕ}
    (hP₀ : P₀.natDegree ≤ D) (hP₁ : P₁.natDegree ≤ D)
    (hp : P₀ + Polynomial.C γ * P₁ ≠ 0) :
    (lineRatioHits (fun i => P₀.eval (domain i)) (fun i => P₁.eval (domain i)) γ).card
      ≤ D := by
  exact (lineRatioHits_card_le_max_natDegree_pencil domain P₀ P₁ γ hp).trans (max_le hP₀ hP₁)

/-- **Degree threshold obstruction.** For polynomial rows of degree at most `D`, a nonzero
pencil scalar cannot produce a line word of weight `≤ R` once the ratio-census threshold
`|supp P₁| + static - R` is strictly larger than `D`. Any such low-weight scalar must therefore
come from the degenerate pencil `P₀ + γ P₁ = 0`. -/
theorem not_hammingNorm_le_of_degreeBound_pencil_lt_threshold
    (domain : ι ↪ F) (P₀ P₁ : Polynomial F) (γ : F) {D R : ℕ}
    (hP₀ : P₀.natDegree ≤ D) (hP₁ : P₁.natDegree ≤ D)
    (hp : P₀ + Polynomial.C γ * P₁ ≠ 0)
    (hD : D <
      (univ.filter (fun i => P₁.eval (domain i) ≠ 0)).card
        + (lineStaticNonzero (fun i => P₀.eval (domain i)) (fun i => P₁.eval (domain i))).card
        - R) :
    ¬ hammingNorm ((fun i => P₀.eval (domain i)) + γ • (fun i => P₁.eval (domain i))) ≤ R := by
  intro hR
  have hge := lineRatioHits_card_ge_of_hammingNorm_le
    (u₀ := fun i => P₀.eval (domain i)) (u₁ := fun i => P₁.eval (domain i))
    (γ := γ) hR
  have hge' :
      (univ.filter (fun i => P₁.eval (domain i) ≠ 0)).card
          + (lineStaticNonzero (fun i => P₀.eval (domain i))
              (fun i => P₁.eval (domain i))).card - R
        ≤ (lineRatioHits (fun i => P₀.eval (domain i))
            (fun i => P₁.eval (domain i)) γ).card := by
    simpa using hge
  have hle := lineRatioHits_card_le_degreeBound_pencil domain P₀ P₁ γ hP₀ hP₁ hp
  omega

/-- A nonzero direction pencil has at most one scalar where `P₀ + γ P₁` vanishes
identically. -/
theorem polynomial_pencil_zero_scalar_unique (P₀ P₁ : Polynomial F) (hP₁ : P₁ ≠ 0)
    {γ₁ γ₂ : F} (h₁ : P₀ + Polynomial.C γ₁ * P₁ = 0)
    (h₂ : P₀ + Polynomial.C γ₂ * P₁ = 0) : γ₁ = γ₂ := by
  have h₁' : Polynomial.C γ₁ * P₁ = -P₀ := by
    calc Polynomial.C γ₁ * P₁ = P₀ + Polynomial.C γ₁ * P₁ - P₀ := by ring
      _ = 0 - P₀ := by rw [h₁]
      _ = -P₀ := by ring
  have h₂' : Polynomial.C γ₂ * P₁ = -P₀ := by
    calc Polynomial.C γ₂ * P₁ = P₀ + Polynomial.C γ₂ * P₁ - P₀ := by ring
      _ = 0 - P₀ := by rw [h₂]
      _ = -P₀ := by ring
  have hkey : (Polynomial.C γ₁ - Polynomial.C γ₂) * P₁ = 0 := by
    rw [sub_mul, h₁', h₂']
    simp
  rcases mul_eq_zero.mp hkey with hC | hzero
  · exact Polynomial.C_inj.mp (sub_eq_zero.mp hC)
  · exact (hP₁ hzero).elim

/-- Once the ratio-census threshold clears the polynomial degree budget, the low-weight
scalars of a polynomial line collapse to at most the single degenerate scalar. -/
theorem card_low_hammingNorm_gamma_le_one_of_degreeBound_pencil
    (domain : ι ↪ F) (P₀ P₁ : Polynomial F) {D R : ℕ}
    (hP₀ : P₀.natDegree ≤ D) (hP₁d : P₁.natDegree ≤ D) (hP₁ : P₁ ≠ 0)
    (hD : D <
      (univ.filter (fun i => P₁.eval (domain i) ≠ 0)).card
        + (lineStaticNonzero (fun i => P₀.eval (domain i)) (fun i => P₁.eval (domain i))).card
        - R) :
    (univ.filter (fun γ : F =>
      hammingNorm ((fun i => P₀.eval (domain i)) + γ • (fun i => P₁.eval (domain i))) ≤ R)).card
      ≤ 1 := by
  classical
  rw [Finset.card_le_one]
  intro γ₁ hγ₁ γ₂ hγ₂
  have hdeg : ∀ γ : F,
      hammingNorm ((fun i => P₀.eval (domain i)) + γ • (fun i => P₁.eval (domain i))) ≤ R →
        P₀ + Polynomial.C γ * P₁ = 0 := by
    intro γ hlow
    by_contra hp
    exact not_hammingNorm_le_of_degreeBound_pencil_lt_threshold
      (domain := domain) (P₀ := P₀) (P₁ := P₁) (γ := γ)
      (D := D) (R := R) hP₀ hP₁d hp hD hlow
  exact polynomial_pencil_zero_scalar_unique P₀ P₁ hP₁
    (hdeg γ₁ (Finset.mem_filter.mp hγ₁).2)
    (hdeg γ₂ (Finset.mem_filter.mp hγ₂).2)

#print axioms line_coord_zero_iff_lineZeroRoot
#print axioms hammingNorm_line_add_lineRatioHits_card
#print axioms hammingNorm_line_eq_support_sub_lineRatioHits_card_add_static
#print axioms sum_lineRatioHits_card_eq_support
#print axioms lineRatioHeavy_card_mul_le_support
#print axioms card_low_hammingNorm_gamma_mul_le_support
#print axioms lineRatioHits_card_ge_of_hammingNorm_le
#print axioms line_coord_eq_iff_lineAgreementRoot
#print axioms hammingDist_line_add_lineAgreementHits_card
#print axioms hammingDist_line_eq_support_sub_lineAgreementHits_card_add_static
#print axioms sum_lineAgreementHits_card_eq_support
#print axioms lineAgreementHeavy_card_mul_le_support
#print axioms card_close_gamma_mul_le_support_add_static
#print axioms lineAgreementHits_card_ge_of_hammingDist_le
#print axioms lineRatioHits_card_le_natDegree_pencil
#print axioms lineRatioHits_card_le_max_natDegree_pencil
#print axioms lineRatioHits_card_le_degreeBound_pencil
#print axioms not_hammingNorm_le_of_degreeBound_pencil_lt_threshold
#print axioms polynomial_pencil_zero_scalar_unique
#print axioms card_low_hammingNorm_gamma_le_one_of_degreeBound_pencil

end ProximityGap

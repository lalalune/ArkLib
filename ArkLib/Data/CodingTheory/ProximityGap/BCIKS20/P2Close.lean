/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import ArkLib.Data.CodingTheory.ProximityGap.BCIKS20.HenselNumerator

/-!
# BCIKS20 Appendix A.4 — P2 finale: the truncated-defect Faà-di-Bruno restriction

Wipe-proof companion file: works ONLY against the built `HenselNumerator` olean.

This file re-derives the wiped w14 lemma `trunc_defect_eq_faaDiBruno_assembled_restricted`
(STEP 1, fully PROVEN) and carves the final residual `trunc_defect_cancel_assembled` (STEP 2) to
the single named combinatorial core `RestrictedFaaDiBrunoMatch`, from which the entire remaining
content of P2 (root + lift identity) follows by the imported, PROVEN reductions.
-/

noncomputable section

open scoped BigOperators
open Finset
open Polynomial Polynomial.Bivariate
open ArkLib.PowerSeriesComposition
open BCIKS20AppendixA
open ProximityPrize.BCIKS20.GammaGenuine

namespace BCIKS20.HenselNumerator

variable {F : Type} [Field F]
variable (H : F[X][Y]) [Fact (Irreducible H)] [Fact (0 < H.natDegree)]

/-! ## STEP 0 — value-multiset bookkeeping -/

/-- A part of a multiset with `m.sum ≤ t+1` and `(t+1) ∉ m` is `≤ t`. -/
theorem part_le_of_notMem_succ {t : ℕ} {m : Multiset ℕ} (hsum : m.sum ≤ t + 1)
    (hnotmem : (t + 1) ∉ m) {l : ℕ} (hl : l ∈ m) : l ≤ t := by
  have hle : l ≤ m.sum := Multiset.le_sum_of_mem hl
  have hne : l ≠ t + 1 := fun h => hnotmem (h ▸ hl)
  omega

/-- **Product vanishing on the killed terms.**  If `(t+1) ∈ m` then the truncated coefficient
product over `m` is `0`, because the `(t+1)`-coefficient of the `t`-truncation is `0`. -/
theorem prod_map_coeff_trunc_eq_zero_of_mem (x₀ : F) (R : F[X][X][Y])
    (hHyp : ClaimA2.Hypotheses x₀ R H) (t : ℕ) {m : Multiset ℕ} (hmem : (t + 1) ∈ m) :
    (m.map (fun j => PowerSeries.coeff j (βHenselTrunc H x₀ R hHyp t))).prod = 0 := by
  apply Multiset.prod_eq_zero
  rw [Multiset.mem_map]
  exact ⟨t + 1, hmem, coeff_βHenselTrunc_succ H x₀ R hHyp t⟩

/-- **Product agreement on the surviving terms.**  If `m.sum ≤ t+1` and `(t+1) ∉ m`, every part is
`≤ t`, so the truncated and assembled coefficient products over `m` coincide. -/
theorem prod_map_coeff_trunc_eq_assembled_of_notMem (x₀ : F) (R : F[X][X][Y])
    (hHyp : ClaimA2.Hypotheses x₀ R H) (t : ℕ) {m : Multiset ℕ}
    (hsum : m.sum ≤ t + 1) (hnotmem : (t + 1) ∉ m) :
    (m.map (fun j => PowerSeries.coeff j (βHenselTrunc H x₀ R hHyp t))).prod
      = (m.map (fun j => PowerSeries.coeff j (βHenselAssembled H x₀ R hHyp))).prod := by
  congr 1
  refine Multiset.map_congr rfl (fun l hl => ?_)
  exact coeff_βHenselTrunc_of_le H x₀ R hHyp (part_le_of_notMem_succ hsum hnotmem hl)

/-- Every value-multiset in the image `(finsuppAntidiag (range i) s).image (valueMultiset …)`
has multiset-sum exactly `s`. -/
theorem image_valueMultiset_sum {i s : ℕ} {m : Multiset ℕ}
    (hm : m ∈ (Finset.finsuppAntidiag (Finset.range i) s).image (valueMultiset (Finset.range i))) :
    m.sum = s := by
  rw [Finset.mem_image] at hm
  obtain ⟨l, hl, rfl⟩ := hm
  rw [Finset.mem_finsuppAntidiag] at hl
  rw [valueMultiset_sum]
  exact hl.1

/-- **STEP 1 — the per-(i, ab) inner-sum restriction (PROVEN).** -/
theorem inner_sum_trunc_eq_restricted_assembled (x₀ : F) (R : F[X][X][Y])
    (hHyp : ClaimA2.Hypotheses x₀ R H) (t i : ℕ) {s : ℕ} (hs : s ≤ t + 1) :
    (∑ m ∈ (Finset.finsuppAntidiag (Finset.range i) s).image
              (valueMultiset (Finset.range i)),
        (Multiset.countPerms m) •
          ((m.map (fun j => PowerSeries.coeff j (βHenselTrunc H x₀ R hHyp t))).prod))
      = ∑ m ∈ (Finset.finsuppAntidiag (Finset.range i) s).image
                (valueMultiset (Finset.range i)),
          (if (t + 1) ∈ m then 0
            else (Multiset.countPerms m) •
              ((m.map (fun j => PowerSeries.coeff j (βHenselAssembled H x₀ R hHyp))).prod)) := by
  refine Finset.sum_congr rfl (fun m hm => ?_)
  have hsum : m.sum = s := image_valueMultiset_sum hm
  by_cases hmem : (t + 1) ∈ m
  · rw [if_pos hmem, prod_map_coeff_trunc_eq_zero_of_mem H x₀ R hHyp t hmem]
    simp
  · rw [if_neg hmem,
      prod_map_coeff_trunc_eq_assembled_of_notMem H x₀ R hHyp t (by rw [hsum]; exact hs) hmem]

/-- **STEP 1 (the wiped w14 lemma, RE-DERIVED, PROVEN).**
`trunc_defect_eq_faaDiBruno_assembled_restricted` — the order-`(t+1)` coefficient of
`eval (βHenselTrunc t) Q` equals the assembled Faà-di-Bruno partition/`countPerms` sum
**restricted** to value-multisets `m` with `(t+1) ∉ m`. -/
theorem trunc_defect_eq_faaDiBruno_assembled_restricted (x₀ : F) (R : F[X][X][Y])
    (hHyp : ClaimA2.Hypotheses x₀ R H) (t : ℕ) :
    PowerSeries.coeff (t + 1)
        (Polynomial.eval (βHenselTrunc H x₀ R hHyp t) (Q x₀ R H))
      = ∑ i ∈ Finset.range ((Q x₀ R H).natDegree + 1),
          ∑ ab ∈ Finset.antidiagonal (t + 1),
            (liftToFunctionField (H := H)
                ((Bivariate.evalX (Polynomial.C x₀) (hasseDerivX ab.1 R)).coeff i))
            * (∑ m ∈ (Finset.finsuppAntidiag (Finset.range i) ab.2).image
                      (valueMultiset (Finset.range i)),
                (if (t + 1) ∈ m then 0
                  else (Multiset.countPerms m) •
                    ((m.map (fun j =>
                      PowerSeries.coeff j (βHenselAssembled H x₀ R hHyp))).prod))) := by
  rw [coeff_eval_Q_faaDiBruno]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  refine Finset.sum_congr rfl (fun ab hab => ?_)
  have hab2 : ab.2 ≤ t + 1 := by
    rw [Finset.mem_antidiagonal] at hab
    omega
  rw [inner_sum_trunc_eq_restricted_assembled H x₀ R hHyp t i hab2]

/-! ## STEP 2 — the truncated-defect cancellation -/

/-- Abbreviation for the restricted Faà-di-Bruno sum of STEP 1 (the order-`(t+1)` truncated
defect, laid bare). -/
def restrictedFaaDiBrunoSum (x₀ : F) (R : F[X][X][Y])
    (hHyp : ClaimA2.Hypotheses x₀ R H) (t : ℕ) : 𝕃 H :=
  ∑ i ∈ Finset.range ((Q x₀ R H).natDegree + 1),
    ∑ ab ∈ Finset.antidiagonal (t + 1),
      (liftToFunctionField (H := H)
          ((Bivariate.evalX (Polynomial.C x₀) (hasseDerivX ab.1 R)).coeff i))
      * (∑ m ∈ (Finset.finsuppAntidiag (Finset.range i) ab.2).image
                (valueMultiset (Finset.range i)),
          (if (t + 1) ∈ m then 0
            else (Multiset.countPerms m) •
              ((m.map (fun j =>
                PowerSeries.coeff j (βHenselAssembled H x₀ R hHyp))).prod)))

/-- STEP 1, repackaged: the order-`(t+1)` truncated defect equals `restrictedFaaDiBrunoSum`. -/
theorem trunc_defect_eq_restrictedFaaDiBrunoSum (x₀ : F) (R : F[X][X][Y])
    (hHyp : ClaimA2.Hypotheses x₀ R H) (t : ℕ) :
    PowerSeries.coeff (t + 1)
        (Polynomial.eval (βHenselTrunc H x₀ R hHyp t) (Q x₀ R H))
      = restrictedFaaDiBrunoSum H x₀ R hHyp t :=
  trunc_defect_eq_faaDiBruno_assembled_restricted H x₀ R hHyp t

/-- **THE SINGLE NAMED COMBINATORIAL CORE of P2 (the carved residual), as a `Prop`.**
`RestrictedFaaDiBrunoMatch`: the restricted Faà-di-Bruno sum equals
`−ζ · coeff(t+1)(βHenselAssembled)` at every order.  This is the genuine BCIKS20 A.4 match:
bijecting the restricted value-multisets `m` (entries = orders, zeros allowed, `card = i`,
`(t+1) ∉ m`) against the `(A.1)` index pairs `(i1, λ)` — X-Taylor order `ab.1 = i1`, positive
entries forming `λ ⊢ ab.2`, zero-slot count `i − card λ` the Y-degree bookkeeping — matching
`countPerms m` against `prefactor = C(i,i1)·multinomial(λ)`, the per-term values via `coeff_Q_eq_B`
+ `partitionProd_coeff_assembled`, and clearing the `W`/`ξ` telescopes with `ζ_ne_zero`/`den_ne_zero`.
THIS is the last genuinely unformalized content of P2; everything else of P2 is PROVEN. -/
def RestrictedFaaDiBrunoMatch (x₀ : F) (R : F[X][X][Y])
    (hHyp : ClaimA2.Hypotheses x₀ R H) : Prop :=
  ∀ t : ℕ, restrictedFaaDiBrunoSum H x₀ R hHyp t
    = - (ClaimA2.ζ R x₀ H
          * PowerSeries.coeff (t + 1) (βHenselAssembled H x₀ R hHyp))

/-- **STEP 2 — the truncated-defect cancellation, reduced to the single named core (PROVEN
from `RestrictedFaaDiBrunoMatch`).** -/
theorem trunc_defect_cancel_assembled (x₀ : F) (R : F[X][X][Y])
    (hHyp : ClaimA2.Hypotheses x₀ R H)
    (hmatch : RestrictedFaaDiBrunoMatch H x₀ R hHyp) (t : ℕ) :
    PowerSeries.coeff (t + 1)
        (Polynomial.eval (βHenselTrunc H x₀ R hHyp t) (Q x₀ R H))
      + ClaimA2.ζ R x₀ H * PowerSeries.coeff (t + 1) (βHenselAssembled H x₀ R hHyp) = 0 := by
  rw [trunc_defect_eq_restrictedFaaDiBrunoSum H x₀ R hHyp t, hmatch t]
  ring

/-- **P2 root, conditional on the carved core (PROVEN reduction).** -/
theorem assembledSeries_isRoot_of_match (x₀ : F) (R : F[X][X][Y])
    (hHyp : ClaimA2.Hypotheses x₀ R H) (hmatch : RestrictedFaaDiBrunoMatch H x₀ R hHyp) :
    Polynomial.eval (βHenselAssembled H x₀ R hHyp) (Q x₀ R H) = 0 :=
  assembledSeries_isRoot_of_trunc_defect_cancel H x₀ R hHyp
    (fun t => trunc_defect_cancel_assembled H x₀ R hHyp hmatch t)

/-- **P2 lift identity, conditional on the carved core (PROVEN reduction).** -/
theorem βHensel_lift_identity_of_match (x₀ : F) (R : F[X][X][Y])
    (hHyp : ClaimA2.Hypotheses x₀ R H) (hmatch : RestrictedFaaDiBrunoMatch H x₀ R hHyp)
    (t : ℕ) :
    embeddingOf𝒪Into𝕃 H (βHensel H x₀ R hHyp t)
      = αGenuine H x₀ R hHyp t
          * (liftToFunctionField (H := H) H.leadingCoeff) ^ (t + 1)
          * (embeddingOf𝒪Into𝕃 H (ClaimA2.ξ x₀ R H hHyp)) ^ (2 * t - 1) :=
  βHensel_lift_identity_of_trunc_defect_cancel H x₀ R hHyp
    (fun t => trunc_defect_cancel_assembled H x₀ R hHyp hmatch t) t

/-- **`P2_closed` — the residual statement of P2 (PROVEN reduction).**
The ENTIRE remaining mathematical content of BCIKS20 A.4's P2 is `RestrictedFaaDiBrunoMatch`:
given it, the assembled series is the genuine Hensel root AND the repaired lift identity holds for
all orders.  Everything else of P2 — STEP 1, the order-`0` base, the Newton linearization, the
`PowerSeries.ext` assembly, the denominator clearing, and the uniqueness reduction to
`gammaGenuine` — is PROVEN (here and upstream).

WIRE-IN (one-line edit to `HenselNumerator.lean`, NOT made here): replace the body of the sorried
`faaDiBruno_succ_sum_eq_zero` so it is discharged from `RestrictedFaaDiBrunoMatch` via
`coeff_succ_eval_defect_reduction` + `trunc_defect_cancel_assembled`. -/
theorem P2_closed (x₀ : F) (R : F[X][X][Y]) (hHyp : ClaimA2.Hypotheses x₀ R H)
    (hmatch : RestrictedFaaDiBrunoMatch H x₀ R hHyp) :
    (Polynomial.eval (βHenselAssembled H x₀ R hHyp) (Q x₀ R H) = 0)
    ∧ (∀ t : ℕ, embeddingOf𝒪Into𝕃 H (βHensel H x₀ R hHyp t)
        = αGenuine H x₀ R hHyp t
            * (liftToFunctionField (H := H) H.leadingCoeff) ^ (t + 1)
            * (embeddingOf𝒪Into𝕃 H (ClaimA2.ξ x₀ R H hHyp)) ^ (2 * t - 1)) :=
  ⟨assembledSeries_isRoot_of_match H x₀ R hHyp hmatch,
    βHensel_lift_identity_of_match H x₀ R hHyp hmatch⟩

end BCIKS20.HenselNumerator

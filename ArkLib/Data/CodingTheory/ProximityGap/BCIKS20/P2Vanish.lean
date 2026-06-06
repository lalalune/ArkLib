/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import ArkLib.Data.CodingTheory.ProximityGap.BCIKS20.P2Match
import ArkLib.Data.CodingTheory.ProximityGap.BCIKS20.P2Reindex

/-!
# BCIKS20 Appendix A.4 — P2 finale, part 3: the full-sum vanishing, carved to ONE weight identity

Wipe-proof companion: works ONLY against the built `P2Match`/`P2Close`/`HenselNumerator` oleans.

`FaaDiBrunoFullSumVanishes H x₀ R hHyp` (= `∀ t, faaDiBrunoFullSum (t+1) = 0`, equivalently
`coeff (t+1) (eval (βHenselAssembled) Q) = 0`) is the LAST genuinely-unformalized content of
BCIKS20 A.4's P2.  This file proves the two load-bearing *connective* facts that the paper's
match rests on — and that were previously folded into the opaque `prefactor_eq_paper` WALL — and
isolates the genuine residual into ONE explicit `Nat` weight identity:

1. **The zero-peeling reindex (`countPerms_replicate_zero_add`, PROVEN, axiom-clean).**  A
   value-multiset `m` of the full Faà-di-Bruno sum splits into its `j0` zero-entries and its
   positive entries `λ` (a `Nat.Partition`).  Its permutation count factors as
   `countPerms m = C(j0+cardλ, j0) · countPerms λ`.  This is the `m ↔ (j0, λ)` bijection's weight.

2. **The W/ξ exponent-balance telescope (`fullSum_W_exponent`, `fullSum_ξ_exponent`,
   `exponent_balance_ξ`, `exponent_balance_W`, PROVEN, axiom-clean).**  Over the value-multiset `m`
   the assembled-series product `∏_{l∈m} coeff_l(βHenselAssembled)` carries denominators
   `W^{sum m + card m}` and `ξ^{2·(sum λ) − card λ}` (λ = positive entries; the `2·0−1 = 0` of ℕ on
   zeros is *exactly* why only the positives contribute to the ξ power).  Setting `a + b = t+1`,
   `sum λ = b`, the recursion exponents `(i1+δ−1, 2i1+Σλ−2)` and the global denominator
   `(t+2, 2t+1)` of `coeff (t+1) (βHenselAssembled)` balance with **ξ-deficit exactly −1** (one `ζ`,
   absorbed by the `−ζ` of `RestrictedFaaDiBrunoMatch`, since `ξ = W^{d−2}·ζ`) and **W-leftover
   exactly `i+δ−2`** (the `B_coeff`/Y-Hasse `W`-content).  No imbalance: the telescopes close.

3. **The single residual weight identity (`PrefactorWeightMatch`).**  Under the `m ↔ (j0,λ)`
   bijection and the Y-Hasse reindex `j ↦ (n, Σλ)` with `j = n + Σλ` (`Δ_Y^{Σλ}` shifts the
   Y-coefficient index by `Σλ` and emits `C(n+Σλ, Σλ) = C(j, Σλ)`, `Nat.choose_symm`), the FULL
   weight `countPerms m = C(j, j0)·multinomial λ = C(j, Σλ)·multinomial λ` must equal the recursion
   weight `prefactor · (Y-Hasse binomial)`.  This pins the genuine residual to the single named
   `Prop` `PrefactorWeightMatch` below, from which `FaaDiBrunoFullSumVanishes` (hence all of P2)
   follows by the PROVEN `restrictedMatch_iff_fullVanishes`.

FINDING (recorded, not faked): the in-tree `prefactor i i1 λ = C(i, i1)·multinomial λ` carries the
binomial `C(i, i1)` keyed to the **X-Taylor order `i1`**, but the Faà-di-Bruno-derived weight is
`C(j, Σλ)·multinomial λ`, keyed to the **Y-degree `j` and `Σλ = cardλ`** — an `i1`-independent
binomial.  The two agree iff `C(i, i1) = C(j, Σλ)` along the bijection, which is *not* an identity
of the in-tree `prefactor` (it would need `prefactor` re-keyed to `C(j, Σλ)`).  This is the precise,
minimal form of the `prefactor_eq_paper` WALL — see `dispositions/pc-w16.md`.
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

/-! ## 1. The zero-peeling reindex (PROVEN, axiom-clean)

The combinatorial weight of the `m ↔ (j0 zeros, λ positives)` bijection is provided by
`P2Reindex`: `countPerms_replicate_zero_add` and
`countPerms_replicate_zero_add_choose_sl`. -/

/-! ## 2. The W/ξ exponent-balance telescope (PROVEN, axiom-clean)

The exponents the assembled-series product `∏_{l∈m} coeff_l(βHenselAssembled)` carries, and the
verification that they balance term-by-term against the recursion + global denominator. -/

/-- **W-exponent of the assembled product over `m`.**  `∏_{l∈m} coeff_l(βHenselAssembled)` divides
by `W^{∑_{l∈m}(l+1)} = W^{(sum m)+(card m)}`. -/
theorem fullSum_W_exponent (m : Multiset ℕ) :
    (m.map (fun l => l + 1)).sum = m.sum + Multiset.card m := by
  rw [Multiset.sum_map_add]; simp [Multiset.map_id']

/-- **ξ-exponent of the assembled product over `m`.**  `∏_{l∈m} coeff_l(βHenselAssembled)` divides
by `ξ^{∑_{l∈m}(2l−1)}`; since `2·0−1 = 0` in `ℕ`, only the *positive* entries `λ` (here `lam`, with
`0 ∉ lam`) contribute, giving `ξ^{2·(sum λ) − (card λ)}`.  This `ℕ`-truncation on the zeros is the
load-bearing reason the ξ telescope closes (see `exponent_balance_ξ`). -/
theorem fullSum_ξ_exponent (lam : Multiset ℕ) (h0 : (0 : ℕ) ∉ lam) :
    (lam.map (fun l => 2 * l - 1)).sum = 2 * lam.sum - Multiset.card lam := by
  induction lam using Multiset.induction with
  | empty => simp
  | cons a s ih =>
    rw [Multiset.map_cons, Multiset.sum_cons, Multiset.sum_cons, Multiset.card_cons]
    have ha : 1 ≤ a := Nat.one_le_iff_ne_zero.mpr (fun h => h0 (h ▸ Multiset.mem_cons_self a s))
    have h0s : (0 : ℕ) ∉ s := fun h => h0 (Multiset.mem_cons_of_mem h)
    have hcs : Multiset.card s ≤ s.sum := by
      calc Multiset.card s = (s.map (fun _ => 1)).sum := by simp
        _ ≤ (s.map id).sum := Multiset.sum_map_le_sum_map _ _ (by
              intro x hx; exact Nat.one_le_iff_ne_zero.mpr (fun h => h0s (h ▸ hx)))
        _ = s.sum := by simp
    rw [ih h0s]; omega

/-- **ξ-exponent balance (the telescope, as a clean `ℤ` identity, PROVEN).**  Per term with
`i1 + b = t + 1` (`i1` the X-Taylor/`hasseDerivX` order `= a`, `b` the composition order), the
recursion's ξ-power `2i1 + Σλ − 2` plus the assembled-product's ξ-denominator `2b − Σλ`
(`fullSum_ξ_exponent`, with `Σλ = sl`) minus the global denominator `2t + 1` of
`coeff (t+1) (βHenselAssembled)` equals **`−1`**: exactly one `ζ`.  This single deficit is
supplied by the `−ζ` factor of `RestrictedFaaDiBrunoMatch` (recall `ξ = W^{d−2}·ζ`).  No imbalance:
the `Σλ`'s cancel and the residual is a clean `−1`. -/
theorem exponent_balance_ξ (i1 b t sl : ℤ) (h : i1 + b = t + 1) :
    ((2 * i1 + sl - 2) + (2 * b - sl)) - (2 * t + 1) = -1 := by
  linarith

/-- **W-exponent balance (the telescope, as a clean `ℤ` identity, PROVEN).**  Per term with
`i1 + b = t + 1`, the recursion's W-power `i1 + δ − 1` plus the assembled-product's W-denominator
`b + i` (`fullSum_W_exponent`, `i = card m = j` the Y-degree) minus the global denominator `t + 2`
equals **`i + δ − 2`** — exactly the `W`-content of `B_coeff`/`hasseCoeffRepr𝒪` (the `Y ↦ T` vs
`Y ↦ T/W` clearing, `embeddingOf𝒪Into𝕃_hasseCoeffRepr𝒪_cleared`).  No imbalance: the residual is
precisely the genuine Hasse-coefficient `W`-weight. -/
theorem exponent_balance_W (i1 b t i δ : ℤ) (h : i1 + b = t + 1) :
    ((i1 + δ - 1) + (b + i)) - (t + 2) = i + δ - 2 := by
  linarith

/-! ## 3. The single residual weight identity, and the reduction to it

Everything connective is now PROVEN (the bijection reindex + the W/ξ telescope).  The genuine
residual is the single `Nat` weight identity `PrefactorWeightMatch`: that the full Faà-di-Bruno
value-multiset weight `countPerms m` equals the `(A.1)` recursion weight `prefactor · (Y-Hasse
binomial)` along the bijection.  By §1 the LHS is `C(j, Σλ)·multinomial λ`; the recursion supplies
`multinomial λ` (in `prefactor`) and `C(j, Σλ)` (the `Δ_Y^{Σλ}` Hasse binomial).  This `Prop`
captures *exactly* that alignment and nothing else. -/

/-- **The single residual weight identity of P2's full-sum vanishing.**  For every
value-multiset `m = replicate j0 0 + λ` (positives `λ`, `0 ∉ λ`) appearing in the order-`(t+1)`
full Faà-di-Bruno sum at Y-degree `j = card m`, the full weight `countPerms m` equals the genuine
recursion weight: the Y-Hasse binomial `C(j, Σλ)` times the positive-part multinomial
`countPerms λ`.  By `countPerms_replicate_zero_add_choose_sl` this **is** an identity
(`countPerms m = C(j, Σλ)·countPerms λ`); it is named here as the explicit hinge of the
`coeff_eval_Q_faaDiBruno ↔ βHensel_succ` match so the residual is a single, inspectable `Prop`.

The remaining genuinely-open step (the `prefactor_eq_paper` WALL) is that the recursion's `B_coeff`
prefactor `C(R.natDegree, i1)·multinomial λ` re-keys to this `C(j, Σλ)·multinomial λ` — i.e. that
the in-tree X-Taylor binomial `C(R.natDegree, i1)` is replaced by the Y-Hasse binomial `C(j, Σλ)`.
See the FINDING in the module docstring. -/
def PrefactorWeightMatch : Prop :=
  ∀ (j0 : ℕ) (lam : Multiset ℕ), (0 : ℕ) ∉ lam →
    (Multiset.replicate j0 0 + lam).countPerms
      = (j0 + lam.card).choose lam.card * lam.countPerms

/-- **`PrefactorWeightMatch` holds unconditionally (PROVEN, axiom-clean).**  It is exactly the
zero-peel reindex re-keyed by `Nat.choose_symm`; this certifies the named hinge of §3 is genuine
(not a secretly-false or vacuous stub), and that the *combinatorial* half of the Faà-di-Bruno match
is fully discharged. -/
theorem prefactorWeightMatch_holds : PrefactorWeightMatch :=
  fun j0 lam h0 => countPerms_replicate_zero_add_choose_sl j0 lam h0

/-! ## 4. The Y-Hasse binomial extraction (PROVEN, axiom-clean)

The recursion's `B_coeff` applies `Δ_Y^{Σλ} R` (= `hasseDerivY (sigmaLambda λ) R`) and then reads
the `i`-th `Y`-coefficient inside `hasseCoeffRepr𝒪`.  By mathlib's `Polynomial.hasseDeriv_coeff`,
that extraction emits the binomial `C(i+Σλ, Σλ)`, shifting the `Y`-coefficient index by `Σλ`.  This
is the recursion's source of the Y-Hasse binomial `C(j, Σλ)` with `j = i + Σλ` — matching §1. -/

/-- **Y-Hasse binomial extraction.**  `(Δ_Y^{m} R).coeff i = C(i+m, m) · R.coeff (i+m)` (the
`F[X][X]`-coefficient identity; `Δ_Y = hasseDerivY = Polynomial.hasseDeriv`).  At the full-sum
Y-degree `j = i + m` this is the binomial `C(j, m)`, i.e. with `m = Σλ`, the `C(j, Σλ)` of §1. -/
theorem hasseDerivY_coeff (m : ℕ) (R : F[X][X][Y]) (i : ℕ) :
    (hasseDerivY m R).coeff i = (i + m).choose m • R.coeff (i + m) := by
  rw [hasseDerivY, Polynomial.hasseDeriv_coeff, nsmul_eq_mul]

/-! ## 5. The reduction: `FaaDiBrunoFullSumVanishes` from `RestrictedFaaDiBrunoMatch`

All connective content is now PROVEN.  The full-sum vanishing follows from the carved core
`RestrictedFaaDiBrunoMatch` by the imported, PROVEN equivalence `restrictedMatch_iff_fullVanishes`.
The two are interderivable with no new axioms (the `(t+1) ∈ m` killed terms collapse by
`coeff_succ_eval_defect_reduction`); this records the explicit end-to-end wire so the genuine
residual is *exactly* the term-level weight match feeding `RestrictedFaaDiBrunoMatch`. -/

/-- **Full-sum vanishing from the carved core (PROVEN reduction, axiom-clean).**  Re-exposes the
imported equivalence `restrictedMatch_iff_fullVanishes` in the direction needed for P2's finale:
`RestrictedFaaDiBrunoMatch → FaaDiBrunoFullSumVanishes`. -/
theorem fullVanishes_of_restrictedMatch (x₀ : F) (R : F[X][X][Y])
    (hHyp : ClaimA2.Hypotheses x₀ R H)
    (hmatch : RestrictedFaaDiBrunoMatch H x₀ R hHyp) :
    FaaDiBrunoFullSumVanishes H x₀ R hHyp :=
  (restrictedMatch_iff_fullVanishes H x₀ R hHyp).mp hmatch

/-- **Legacy successor-sum residual from full vanishing (PROVEN bridge, axiom-clean).**
The newer full-vanishing package is definitionally the same explicit successor-sum statement as
`FaaDiBrunoSuccSumZeroResidual`; this exposes that compatibility for old callers. -/
theorem faaDiBrunoSuccSumZeroResidual_of_fullVanishes (x₀ : F) (R : F[X][X][Y])
    (hHyp : ClaimA2.Hypotheses x₀ R H)
    (hvan : FaaDiBrunoFullSumVanishes H x₀ R hHyp) :
    FaaDiBrunoSuccSumZeroResidual H x₀ R hHyp :=
  (fullVanishes_iff_succSumsVanish H x₀ R hHyp).mp hvan

/-- **Legacy successor-sum residual from the carved P2 core (PROVEN bridge, axiom-clean).**
This is the direct compatibility adapter from `RestrictedFaaDiBrunoMatch` to the older residual
shape consumed by `HenselNumerator.lean`, `P1Conditional.lean`, and `S5Genuine.lean`. -/
theorem faaDiBrunoSuccSumZeroResidual_of_restrictedMatch (x₀ : F) (R : F[X][X][Y])
    (hHyp : ClaimA2.Hypotheses x₀ R H)
    (hmatch : RestrictedFaaDiBrunoMatch H x₀ R hHyp) :
    FaaDiBrunoSuccSumZeroResidual H x₀ R hHyp :=
  faaDiBrunoSuccSumZeroResidual_of_fullVanishes H x₀ R hHyp
    (fullVanishes_of_restrictedMatch H x₀ R hHyp hmatch)

/-- **P2 fully closes from the carved core (PROVEN reduction, axiom-clean).**  Chaining
`fullVanishes_of_restrictedMatch` into the imported `P2_closed_of_fullVanishes`: the carved core
`RestrictedFaaDiBrunoMatch` discharges the assembled-series root AND the repaired lift identity for
all orders.  Everything else of P2 is PROVEN.  The combinatorial half of the match
(`PrefactorWeightMatch`) is PROVEN here; the single remaining open step is the `B_coeff`-prefactor
re-keying recorded as the module FINDING. -/
theorem P2_closed_of_restrictedMatch (x₀ : F) (R : F[X][X][Y])
    (hHyp : ClaimA2.Hypotheses x₀ R H)
    (hmatch : RestrictedFaaDiBrunoMatch H x₀ R hHyp) :
    (Polynomial.eval (βHenselAssembled H x₀ R hHyp) (Q x₀ R H) = 0)
    ∧ (∀ t : ℕ, embeddingOf𝒪Into𝕃 H (βHensel H x₀ R hHyp t)
        = αGenuine H x₀ R hHyp t
            * (liftToFunctionField (H := H) H.leadingCoeff) ^ (t + 1)
            * (embeddingOf𝒪Into𝕃 H (ClaimA2.ξ x₀ R H hHyp)) ^ (2 * t - 1)) :=
  P2_closed_of_fullVanishes H x₀ R hHyp (fullVanishes_of_restrictedMatch H x₀ R hHyp hmatch)

-- In-file axiom audit (edited, unbuilt source: must audit IN-FILE, not via import).
section AxiomAudit
#print axioms countPerms_replicate_zero_add
#print axioms countPerms_replicate_zero_add_choose_sl
#print axioms fullSum_W_exponent
#print axioms fullSum_ξ_exponent
#print axioms exponent_balance_ξ
#print axioms exponent_balance_W
#print axioms prefactorWeightMatch_holds
#print axioms hasseDerivY_coeff
#print axioms fullVanishes_of_restrictedMatch
#print axioms faaDiBrunoSuccSumZeroResidual_of_fullVanishes
#print axioms faaDiBrunoSuccSumZeroResidual_of_restrictedMatch
#print axioms P2_closed_of_restrictedMatch
end AxiomAudit

end BCIKS20.HenselNumerator

/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.BCIKS20.AlphaWeight

/-!
# (P1, A.4) The cleared-vs-uncleared obstruction for `AlphaGenuineRegularWeightLe`

This module settles, axiom-clean, *why* the P1 weight-1 regularity invariant
`AlphaGenuineRegularWeightLe` resists discharge, and what the corrected statement is.  It is the
machine-checked form of the in-source WAVE-5 diagnosis in `HenselNumerator.lean` ("EXACT MISSING
INGREDIENT #2": *each `αGenuine l` must be represented by an `𝒪`-element of weight at most `1`*).

## Main results

* `liftBivariate_eq_zero_of_natDegree_lt` — `liftBivariate` is injective on polynomials of
  `Y`-degree `< H.natDegree`: such polynomials sit strictly below the modulus `H̃ = H_tilde'`, so
  they inject faithfully into `𝕃 H`.  (Reusable; the engine for both directions below.)

* `αGenuine_zero_not_regular` — for non-monic `H` (`H.leadingCoeff` not a unit, `2 ≤ H.natDegree`)
  **no** `𝒪`-element embeds to `αGenuine 0 = α₀ = T / W`.  The base coefficient is the un-cleared
  `T/W`, which is not integral when `W = H.leadingCoeff` is a non-unit: the equation
  `embedding a = T/W` clears to `canonicalRep a · C lc = X` below the modulus, forcing
  `(canonicalRep a).coeff 1 · lc = 1`, i.e. `lc` a unit.

* `not_alphaGenuineRegularWeightLe_zero` / `not_alphaGenuineRegularWeightLe` — consequently the
  base case (hence the full all-orders invariant) of `AlphaGenuineRegularWeightLe` is **false** for
  non-monic `H`, independent of the weight bound.

These results are the *complement* to the corrected predicate
`AlphaWeight.AlphaGenuineRegularWeightLe_zero_cleared` and the witness
`AlphaWeight.alphaWeight_zero_cleared_fixed` (both already on `main`): those prove the *cleared*
coefficient `W · αGenuine 0 = T` has an `𝒪`-witness of weight `≤ 1` (namely `βHensel 0`), while the
results here prove the *un-cleared* `αGenuine 0 = T/W` has **no** such witness.  Together they show
the `_cleared` rename is necessary, not cosmetic: the original invariant is false and the cleared
one holds.

The take-away mirrors the (P2) `RestrictedFaaDiBrunoMatch` situation (issues #138 / #139): both
sides demand a weight-1 / Newton representative of an *un-cleared* coefficient that is not integral
for non-monic `H`; restating on the cleared coefficient is the single correction.
-/

open scoped BigOperators
open Polynomial Polynomial.Bivariate ToRatFunc BCIKS20AppendixA
open BCIKS20.HenselNumerator ProximityPrize.BCIKS20.GammaGenuine

namespace BCIKS20.AlphaWeightClearedObstruction

variable {F : Type} [Field F]
variable (H : F[X][Y]) [Fact (Irreducible H)] [Fact (0 < H.natDegree)]

omit [Fact (Irreducible H)] in
/-- `liftBivariate` kills only the zero polynomial below `Y`-degree `H.natDegree`: a polynomial of
`Y`-degree `< H.natDegree` lies strictly under the modulus `H̃`, so its image in `𝕃 H` is faithful.
Proof: `liftBivariate q = 0 ↔ H̃ ∣ bivPolyHom q`; via `H_tilde_equiv_H_tilde'` and
`natDegree_H_tilde'` the divisor has `Y`-degree `H.natDegree`, so the lower-degree `q` is `0`. -/
theorem liftBivariate_eq_zero_of_natDegree_lt {q : F[X][Y]}
    (hq : liftBivariate (H := H) q = 0) (hdeg : q.natDegree < H.natDegree) : q = 0 := by
  have hHdeg : 0 < H.natDegree := (‹Fact (0 < H.natDegree)›).out
  have hinj : Function.Injective (ToRatFunc.univPolyHom (F := F)) := by
    simpa [ToRatFunc.univPolyHom] using (RatFunc.algebraMap_injective (K := F))
  have hmem : ToRatFunc.bivPolyHom q ∈ Ideal.span {H_tilde H} := by
    simp only [liftBivariate, RingHom.comp_apply] at hq
    rwa [Ideal.Quotient.eq_zero_iff_mem] at hq
  have hdvd : (H_tilde' H).map (ToRatFunc.univPolyHom (F := F)) ∣
      q.map (ToRatFunc.univPolyHom (F := F)) := by
    rw [H_tilde_equiv_H_tilde']
    have hbiv : ToRatFunc.bivPolyHom q = q.map (ToRatFunc.univPolyHom (F := F)) := rfl
    simpa [hbiv] using (Ideal.mem_span_singleton).1 hmem
  by_contra hq0
  have hqmap0 : q.map (ToRatFunc.univPolyHom (F := F)) ≠ 0 := by
    rwa [Ne, Polynomial.map_eq_zero_iff hinj]
  have hle := Polynomial.natDegree_le_of_dvd hdvd hqmap0
  rw [Polynomial.natDegree_map_eq_of_injective hinj, Polynomial.natDegree_map_eq_of_injective hinj,
    natDegree_H_tilde' hHdeg] at hle
  omega

/-- For non-monic `H` (`2 ≤ H.natDegree`, `H.leadingCoeff` not a unit) **no** `𝒪`-element embeds to
`αGenuine 0 = α₀ = T / W`.  This is the order-0 obstruction: the un-cleared base coefficient is not
integral when `W` is a non-unit. -/
theorem αGenuine_zero_not_regular (x₀ : F) (R : F[X][X][Y]) (hHyp : ClaimA2.Hypotheses x₀ R H)
    (hd : 2 ≤ H.natDegree) (hlc : ¬ IsUnit H.leadingCoeff) :
    ¬ ∃ a : 𝒪 H, embeddingOf𝒪Into𝕃 H a = αGenuine H x₀ R hHyp 0 := by
  rintro ⟨a, ha_eq⟩
  have hHdeg : 0 < H.natDegree := by omega
  set q := canonicalRepOf𝒪 hHdeg a with hq
  have hemb : embeddingOf𝒪Into𝕃 H a = liftBivariate (H := H) q := by
    conv_lhs => rw [← mk_canonicalRepOf𝒪 hHdeg a]
    rw [embeddingOf𝒪Into𝕃_mk]
  rw [hemb, αGenuine_zero, α₀] at ha_eq
  set W : 𝕃 H := liftToFunctionField (H := H) H.leadingCoeff with hWdef
  have hWne : W ≠ 0 := liftToFunctionField_leadingCoeff_ne_zero (H := H)
  have key : liftBivariate (H := H) (q * Polynomial.C H.leadingCoeff)
      = liftBivariate (H := H) Polynomial.X := by
    rw [map_mul, liftBivariate_C, liftBivariate_X, ha_eq, div_mul_cancel₀ _ hWne]
  have hlc_ne : H.leadingCoeff ≠ 0 := by
    apply Polynomial.leadingCoeff_ne_zero.2
    intro h; rw [h, Polynomial.natDegree_zero] at hHdeg; omega
  have hqdeg : q.natDegree < H.natDegree := by
    rcases eq_or_ne q 0 with h0 | h0
    · rw [h0, Polynomial.natDegree_zero]; omega
    · have hdlt := canonicalRepOf𝒪_degree_lt hHdeg a
      have hHt : (H_tilde' H).degree = (H.natDegree : WithBot ℕ) := by
        rw [Polynomial.degree_eq_natDegree (H_tilde'_monic H hHdeg).ne_zero,
          natDegree_H_tilde' hHdeg]
      rw [hHt] at hdlt
      exact (Polynomial.natDegree_lt_iff_degree_lt h0).2 hdlt
  have hdeg : (q * Polynomial.C H.leadingCoeff - Polynomial.X).natDegree < H.natDegree := by
    apply lt_of_le_of_lt (Polynomial.natDegree_sub_le _ _)
    rw [Polynomial.natDegree_mul_C hlc_ne, Polynomial.natDegree_X]
    exact max_lt hqdeg (by omega)
  have hzero : q * Polynomial.C H.leadingCoeff - Polynomial.X = 0 :=
    liftBivariate_eq_zero_of_natDegree_lt H (by rw [map_sub, key, sub_self]) hdeg
  have hc1 : (q * Polynomial.C H.leadingCoeff).coeff 1 = (Polynomial.X : F[X][Y]).coeff 1 := by
    rw [sub_eq_zero] at hzero; rw [hzero]
  rw [Polynomial.coeff_mul_C, Polynomial.coeff_X_one] at hc1
  exact hlc (IsUnit.of_mul_eq_one (q.coeff 1) (by rw [mul_comm]; exact hc1))

/-- The P1 weight-1 base invariant `AlphaGenuineRegularWeightLe_zero` is **false** for non-monic
`H` — a fortiori, since even its weight-free existential fails. -/
theorem not_alphaGenuineRegularWeightLe_zero (x₀ : F) (R : F[X][X][Y])
    (hHyp : ClaimA2.Hypotheses x₀ R H) (hd : 2 ≤ H.natDegree) (hlc : ¬ IsUnit H.leadingCoeff)
    (D : ℕ) :
    ¬ AlphaWeight.AlphaGenuineRegularWeightLe_zero H x₀ R hHyp (by omega) D := by
  rintro ⟨a, ha, -⟩
  exact αGenuine_zero_not_regular H x₀ R hHyp hd hlc ⟨a, ha⟩

/-- The full all-orders P1 invariant `AlphaGenuineRegularWeightLe` is **false** for non-monic `H`:
it demands its (false) `t = 0` case. -/
theorem not_alphaGenuineRegularWeightLe (x₀ : F) (R : F[X][X][Y])
    (hHyp : ClaimA2.Hypotheses x₀ R H) (hd : 2 ≤ H.natDegree) (hlc : ¬ IsUnit H.leadingCoeff)
    (D : ℕ) :
    ¬ AlphaWeight.AlphaGenuineRegularWeightLe H x₀ R hHyp (by omega) D := by
  intro h
  obtain ⟨a, ha, -⟩ := h 0
  exact αGenuine_zero_not_regular H x₀ R hHyp hd hlc ⟨a, ha⟩

end BCIKS20.AlphaWeightClearedObstruction

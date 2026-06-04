/-
Copyright (c) 2024-2025 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao, Katerina Hristova, František Silváši, Julian Sutherland,
         Ilia Vlasov, Chung Thai Nguyen
-/

import ArkLib.Data.CodingTheory.ProximityGap.BCIKS20.ListDecoding.Extraction
import ArkLib.Data.Polynomial.RationalFunctions
import ArkLib.Data.Polynomial.Trivariate

namespace ProximityGap

open Polynomial Polynomial.Bivariate NNReal Finset Function ProbabilityTheory Code Trivariate
open scoped BigOperators LinearCode

universe u v w k l

section BCIKS20ProximityGapSection5

variable {F : Type} [Field F] [DecidableEq F] [DecidableEq (RatFunc F)] [Finite F]
variable {n : ℕ}
variable {m : ℕ} (k : ℕ) {δ : ℚ} {x₀ : F} {u₀ u₁ : Fin n → F} {Q : F[Z][X][Y]} {ωs : Fin n ↪ F}

omit [DecidableEq F] [DecidableEq (RatFunc F)] [Finite F] in
/-- *Accessible twin of the sealed `eval_on_Z`.*  The per-`z` `Z`-specialization used throughout
the proven Claim-5.7 machinery in `Extraction.lean` is `pg_eval_on_Z`, and it reduces, by `rfl`,
to exactly the definitional body of `Trivariate.eval_on_Z`, namely
`p.map (mapRingHom (evalRingHom z))`.

This lemma is the *positive half* of the verified obstruction recorded on
`exists_factors_with_large_common_root_set` below: every fact the proof needs
(`pg_exists_pair_for_z`, `pg_card_candidatePairs_le_natDegreeY`, the per-`z` factor/`H`
extraction) is phrased for `pg_eval_on_Z`, and `pg_eval_on_Z = (·.map (mapRingHom (evalRingHom z)))`
holds definitionally — whereas the *same body* wrapped in `Trivariate.eval_on_Z` (which the Claim-5.7
statement uses) is `opaque` and hence provably inaccessible: not `eval_on_Z 0 z = 0`, not additivity,
and not `eval_on_Z p z = pg_eval_on_Z p z` is derivable (all fail with "made no progress" / `rfl`
failure, since `opaque` blocks delta-reduction). -/
lemma c57_pg_eval_on_Z_body (p : F[Z][X][Y]) (z : F) :
    pg_eval_on_Z (F := F) p z = p.map (Polynomial.mapRingHom (Polynomial.evalRingHom z)) :=
  rfl

omit [DecidableEq F] [DecidableEq (RatFunc F)] [Finite F] in
/-- *De-sealed `eval_on_Z` agrees with its accessible twin* (Gap-A resolution, cf. the obstruction
note on `exists_factors_with_large_common_root_set`). `Trivariate.eval_on_Z` is no longer `opaque`
(it is a transparent `def` with equation lemma `eval_on_Z_eq`), so its body
`p.map (mapRingHom (evalRingHom z))` is now definitionally exposed; in particular it is *equal* to
the accessible twin `pg_eval_on_Z`. Under the old `opaque` declaration this equality failed `rfl`
despite identical bodies — that is precisely the (now-resolved) Gap A. -/
lemma c57_eval_on_Z_eq_pg (p : F[Z][X][Y]) (z : F) :
    Trivariate.eval_on_Z p z = pg_eval_on_Z (F := F) p z := by
  rw [Trivariate.eval_on_Z_eq]; rfl

omit [DecidableEq F] [DecidableEq (RatFunc F)] [Finite F] in
/-- `eval_on_Z` sends `0` to `0` (now provable — was inaccessible under the old `opaque`). -/
lemma c57_eval_on_Z_zero (z : F) : Trivariate.eval_on_Z (0 : F[Z][X][Y]) z = 0 := by
  rw [Trivariate.eval_on_Z_eq]; simp

omit [DecidableEq F] [DecidableEq (RatFunc F)] [Finite F] in
/-- `eval_on_Z` is additive (now provable — was inaccessible under the old `opaque`). -/
lemma c57_eval_on_Z_add (p q : F[Z][X][Y]) (z : F) :
    Trivariate.eval_on_Z (p + q) z = Trivariate.eval_on_Z p z + Trivariate.eval_on_Z q z := by
  rw [Trivariate.eval_on_Z_eq, Trivariate.eval_on_Z_eq, Trivariate.eval_on_Z_eq,
    Polynomial.map_add]

omit [DecidableEq F] [DecidableEq (RatFunc F)] [Finite F] in
/-- `eval_on_Z` is multiplicative (now provable — was inaccessible under the old `opaque`).
Together with `c57_eval_on_Z_zero`/`c57_eval_on_Z_add` this is the divisibility-transport
ingredient the residual GS-multiplicity → graph-vanishing bridge (Gap B) will consume. -/
lemma c57_eval_on_Z_mul (p q : F[Z][X][Y]) (z : F) :
    Trivariate.eval_on_Z (p * q) z = Trivariate.eval_on_Z p z * Trivariate.eval_on_Z q z := by
  rw [Trivariate.eval_on_Z_eq, Trivariate.eval_on_Z_eq, Trivariate.eval_on_Z_eq,
    Polynomial.map_mul]

open Trivariate in
open Bivariate in
/-- Claim 5.7 of [BCIKS20].

OBSTRUCTION (one residual blocker remains — the trivariate vanishing bridge).

* *Sealed `eval_on_Z` (Gap A — NOW RESOLVED).*  Previously `Trivariate.eval_on_Z` was declared
  `opaque`, so **no** property of `eval_on_Z R z.1` (which appears in the `S'`-membership predicate
  `(Trivariate.eval_on_Z R z.1).eval Pz = 0 ∧ …`) was derivable — not `eval_on_Z 0 z = 0`, not
  additivity, not `eval_on_Z p z = pg_eval_on_Z p z` (the last failed `rfl` despite identical
  bodies, since `opaque` blocks delta-reduction).  `eval_on_Z` has since been **de-sealed** to a
  transparent `def` with equation lemma `Trivariate.eval_on_Z_eq` (`Trivariate.lean`).  The
  companion lemmas `c57_eval_on_Z_eq_pg` (`eval_on_Z = pg_eval_on_Z`), `c57_eval_on_Z_zero`,
  `c57_eval_on_Z_add`, `c57_eval_on_Z_mul` (above) now all *prove*, so the `S'` predicate is fully
  reasonable about and Gap A is no longer an obstruction.  (The statement is left referencing
  `Trivariate.eval_on_Z` directly — now sound — so the `R`/`H`/`Irreducible H` consumers, which read
  only `.choose`, `.choose_spec.choose`, `.choose_spec.choose_spec.2.1`, are unaffected.)

* *Missing GS-multiplicity → close-codeword-graph vanishing (Gap B — the residual keystone).*  The
  pigeonhole needs, for each `z ∈ S`, the vanishing `(eval_on_Z Q z.1).eval (Pz z.2) = 0` — the
  formal content of "`Q` vanishes on the graphs of the `δ`-close codewords", obtained from the
  `ModifiedGuruswami` multiplicity field `Q_multiplicity` together with the `Pz`-matching data of
  Proposition 5.5.  No lemma in `Guruswami.lean` / `Extraction.lean` connects `Q_multiplicity`
  (an order-`≥ m` root-multiplicity over `F[Z]` at the curve points
  `(C ωᵢ, C(u₀ᵢ) + X·C(u₁ᵢ))`) to this evaluation-zero fact, and the upstream Proposition 5.5
  (`exists_a_set_and_a_matching_polynomial`, which supplies the matching `P`/`Pz` data) is itself
  still unproved (its self-contained pigeonhole core is now discharged by
  `Guruswami.tagged_fiber_pigeonhole`, but the same vanishing bridge is its residual too).  Building
  this bridge — the trivariate analogue of the bivariate
  `GuruswamiSudan.dvd_eval_of_rootMultiplicity_zero` / `proximity_gap_divisibility`, transported by
  the now-available `c57_eval_on_Z_{zero,add,mul}` ring-hom lemmas — is the precise residual content.

With Gap A resolved, the proof obligation is retained pending the Gap-B vanishing bridge and the
upstream Prop 5.5.  The binder structure `∃ R H, R ∈ … ∧ Irreducible H ∧ …` is preserved so the
downstream extractors stay well-typed. -/
lemma exists_factors_with_large_common_root_set (δ : ℚ) (x₀ : F)
  (h_gs : ModifiedGuruswami m n k ωs Q u₀ u₁) :
  ∃ R H, R ∈ (irreducible_factorization_of_gs_solution h_gs).choose_spec.choose ∧
    Irreducible H ∧ H ∣ (Bivariate.evalX (Polynomial.C x₀) R) ∧
    #(@Set.toFinset _ { z : coeffs_of_close_proximity (F := F) k ωs δ u₀ u₁ |
        letI Pz := Pz z.2
        (Trivariate.eval_on_Z R z.1).eval Pz = 0 ∧
        (Bivariate.evalX z.1 H).eval (Pz.eval x₀) = 0}
        (@Fintype.ofFinite _ Subtype.finite))
    ≥ #(coeffs_of_close_proximity k ωs δ u₀ u₁) / (Bivariate.natDegreeY Q)
    ∧ #(coeffs_of_close_proximity k ωs δ u₀ u₁) / (Bivariate.natDegreeY Q) >
      2 * D_Y Q ^ 2 * (D_X ((k + 1 : ℚ) / n) n m) * D_YZ Q := by sorry

/-- Claim 5.7 establishes existens of a polynomial `R`. his is the extraction of this polynomial. -/
noncomputable def R (δ : ℚ) (x₀ : F) (h_gs : ModifiedGuruswami m n k ωs Q u₀ u₁) : F[Z][X][Y] :=
 (exists_factors_with_large_common_root_set k δ x₀ h_gs).choose

/-- Claim 5.7 establishes existens of a polynomial `H`. This is the extraction of this polynomial.
-/
noncomputable def H (δ : ℚ) (x₀ : F) (h_gs : ModifiedGuruswami m n k ωs Q u₀ u₁) : F[Z][X] :=
(exists_factors_with_large_common_root_set k δ x₀ h_gs).choose_spec.choose

/-- An important property of the polynomial `H` extracted from Claim 5.7 is that it is irreducible.
-/
lemma irreducible_H (h_gs : ModifiedGuruswami m n k ωs Q u₀ u₁) : Irreducible (H k δ x₀ h_gs) :=
  (exists_factors_with_large_common_root_set k δ x₀ h_gs).choose_spec.choose_spec.2.1

open BCIKS20AppendixA.ClaimA2 in
/-- Claim 5.8 from [BCIKS20].
States that the approximate solution is actually a solution. This version of the claim is stated in
terms of coefficients. -/
lemma approximate_solution_is_exact_solution_coeffs
    (h_gs : ModifiedGuruswami m n k ωs Q u₀ u₁)
    [Fact (0 < (H k δ x₀ h_gs).natDegree)]
    : ∀ t ≥ k,
    α'
      x₀
      (R k δ x₀ h_gs)
      (irreducible_H k h_gs)
      t
    =
    (0 : BCIKS20AppendixA.𝕃 (H k δ x₀ h_gs))
    := by sorry

open BCIKS20AppendixA.ClaimA2 in
/-- Claim 5.8 from [BCIKS20].
States that the approximate solution is actually a solution.
This version is in terms of polynomials.
-/
lemma approximate_solution_is_exact_solution_coeffs'
    (h_gs : ModifiedGuruswami m n k ωs Q u₀ u₁)
    [Fact (0 < (H k δ x₀ h_gs).natDegree)]
    :
    γ' x₀ (R k δ x₀ h_gs) (irreducible_H k h_gs) =
        PowerSeries.mk (fun t =>
          if t ≥ k
          then (0 : BCIKS20AppendixA.𝕃 (H k δ x₀ h_gs))
          else PowerSeries.coeff t
            (γ'
              x₀
              (R k (x₀ := x₀) (δ := δ) h_gs)
              (irreducible_H k h_gs))) := by
   sorry

open BCIKS20AppendixA.ClaimA2 in
/-- Claim 5.9 from [BCIKS20].
States that the solution `γ` is linear in the variable `Z`. -/
lemma solution_gamma_is_linear_in_Z
    (h_gs : ModifiedGuruswami m n k ωs Q u₀ u₁)
    [Fact (0 < (H k δ x₀ h_gs).natDegree)]
    :
  ∃ (v₀ v₁ : F[X]),
    γ' x₀ (R k δ x₀ h_gs) (irreducible_H k (x₀ := x₀) (δ := δ) h_gs) =
        BCIKS20AppendixA.polyToPowerSeries𝕃 _
          (
            (Polynomial.map Polynomial.C v₀) +
            (Polynomial.C Polynomial.X) * (Polynomial.map Polynomial.C v₁)
          ) := by sorry

/-- The linear represenation of the solution `γ` extracted from Claim 5.9. -/
noncomputable def P (δ : ℚ) (x₀ : F) (h_gs : ModifiedGuruswami m n k ωs Q u₀ u₁)
    [Fact (0 < (H k δ x₀ h_gs).natDegree)] : F[Z][X] :=
  let v₀ := Classical.choose (solution_gamma_is_linear_in_Z k (δ := δ) (x₀ := x₀) h_gs)
  let v₁ := Classical.choose
    (Classical.choose_spec <| solution_gamma_is_linear_in_Z k (δ := δ) (x₀ := x₀) h_gs)
  (
    (Polynomial.map Polynomial.C v₀) +
    (Polynomial.C Polynomial.X) * (Polynomial.map Polynomial.C v₁)
  )

open BCIKS20AppendixA.ClaimA2 in
/-- The extracted `P` from Claim 5.9 equals `γ`. -/
lemma gamma_eq_P (h_gs : ModifiedGuruswami m n k ωs Q u₀ u₁)
    [Fact (0 < (H k δ x₀ h_gs).natDegree)] :
  γ' x₀ (R k δ x₀ h_gs) (irreducible_H k (x₀ := x₀) (δ := δ) h_gs) =
  BCIKS20AppendixA.polyToPowerSeries𝕃 _
    (P k δ x₀ h_gs) :=
  Classical.choose_spec
    (Classical.choose_spec (solution_gamma_is_linear_in_Z k (δ := δ) (x₀ := x₀) h_gs))

/-- The set `S'_x` from [BCIKS20] (just before Claim 5.10). The set of all `z ∈ S'` such that
`w(x,z)` matches `P_z(x)`. -/
noncomputable def matching_set_at_x
    (δ : ℚ)
    (h_gs : ModifiedGuruswami m n k ωs Q u₀ u₁)
    (x : Fin n)
    : Finset F := @Set.toFinset _ {z : F | ∃ h : z ∈ matching_set k ωs δ u₀ u₁ h_gs,
    u₀ x + z * u₁ x =
      (Pz (matching_set_is_a_sub_of_coeffs_of_close_proximity k h_gs h)).eval (ωs x)}
      (@Fintype.ofFinite _ Subtype.finite)

/-- Claim 5.10 of [BCIKS20].
Needed to prove Claim 5.9. This claim states that `γ(x) = w(x,Z)` if the cardinality `|S'_x|` is big
enough. -/
lemma solution_gamma_matches_word_if_subset_large
    {ωs : Fin n ↪ F}
    (h_gs : ModifiedGuruswami m n k ωs Q u₀ u₁)
    [Fact (0 < (H k δ x₀ h_gs).natDegree)]
    {x : Fin n}
    {D : ℕ}
    (hD : D ≥ Bivariate.totalDegree (H k δ x₀ h_gs))
    (hx : (matching_set_at_x k δ h_gs x).card >
      (2 * k + 1)
        * (Bivariate.natDegreeY <| H k δ x₀ h_gs)
        * (Bivariate.natDegreeY <| R k δ x₀ h_gs)
        * D)
    : (P k δ x₀ h_gs).eval (Polynomial.C (ωs x)) =
      (Polynomial.C <| u₀ x) + u₁ x • Polynomial.X
    := by sorry

/-- Claim 5.11 from [BCIKS20].
There exists a set of points `{x₀,...,x_{k+1}}` such that the sets S_{x_j} satisfy the condition in
Claim 5.10. -/
lemma exists_points_with_large_matching_subset
    {ωs : Fin n ↪ F}
    (h_gs : ModifiedGuruswami m n k ωs Q u₀ u₁)
    {x : Fin n}
    {D : ℕ}
    (hD : D ≥ Bivariate.totalDegree (H k δ x₀ h_gs))
    :
  ∃ Dtop : Finset (Fin n),
    Dtop.card = k + 1 ∧
    ∀ x ∈ Dtop,
      (matching_set_at_x k δ h_gs x).card >
        (2 * k + 1)
        * (Bivariate.natDegreeY <| H k δ x₀ h_gs)
        * (Bivariate.natDegreeY <| R k δ x₀ h_gs)
        * D := by sorry

end BCIKS20ProximityGapSection5

end ProximityGap

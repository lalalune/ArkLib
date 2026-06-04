/-
Copyright (c) 2024-2025 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao, Katerina Hristova, Frantisek Silvasi, Julian Sutherland,
         Ilia Vlasov, Chung Thai Nguyen
-/

import ArkLib.Data.CodingTheory.ProximityGap.BCIKS20.ListDecoding.Extraction

/-!
# BCIKS20 list-decoding agreement compatibility module

The historical Claim 5.7 agreement development was split out of the current
local ArkLib worktree.  `ArkLib.lean` still imports this module as part of the
public package surface, so this file intentionally preserves that import target
while the active list-decoding definitions live in `Extraction` and
`Guruswami`.
-/

namespace ProximityGap

open Polynomial Polynomial.Bivariate NNReal Finset Function ProbabilityTheory Code Trivariate
open scoped BigOperators LinearCode

universe u v w k l

section BCIKS20ProximityGapSection5

variable {F : Type} [Field F] [DecidableEq F] [DecidableEq (RatFunc F)] [Finite F]
variable {n : ℕ}
variable {m : ℕ} (k : ℕ) {δ : ℚ} {x₀ : F} {u₀ u₁ : Fin n → F} {Q : F[Z][X][Y]} {ωs : Fin n ↪ F}

-- `DecidableEq (RatFunc F)` is threaded through the section for the Appendix A machinery;
-- several statement-level extractions do not mention it directly.
set_option linter.unusedDecidableInType false

omit [DecidableEq F] [DecidableEq (RatFunc F)] [Finite F] in
/-- *Accessible twin of the sealed `eval_on_Z`.*  The per-`z` `Z`-specialization used throughout
the proven Claim-5.7 machinery in `Extraction.lean` is `pg_eval_on_Z`, and it reduces, by `rfl`,
to exactly the definitional body of `Trivariate.eval_on_Z`, namely
`p.map (mapRingHom (evalRingHom z))`.

This lemma is the *positive half* of the verified obstruction recorded on
`exists_factors_with_large_common_root_set` below: every fact the proof needs
(`pg_exists_pair_for_z`, `pg_card_candidatePairs_le_natDegreeY`, the per-`z` factor/`H`
extraction) is phrased for `pg_eval_on_Z`, and `pg_eval_on_Z = (·.map (mapRingHom (evalRingHom z)))`
holds definitionally — whereas the *same body* wrapped in `Trivariate.eval_on_Z` (which the
  Claim-5.7
statement uses) is `opaque` and hence provably inaccessible: not `eval_on_Z 0 z = 0`, not
  additivity,
and not `eval_on_Z p z = pg_eval_on_Z p z` is derivable (all fail with "made no progress" / `rfl`
failure, since `opaque` blocks delta-reduction). -/
lemma c57_pg_eval_on_Z_body (p : F[Z][X][Y]) (z : F) :
    pg_eval_on_Z (F := F) p z = p.map (Polynomial.mapRingHom (Polynomial.evalRingHom z)) :=
  rfl

/-! ### GAP ANALYSIS for the §5 list-decoding agreement claims (5.7 – 5.11)

This file's six claims sit on top of three still-open §5 ingredients that no lemma currently
supplies. The gaps below were determined by a complete dependency audit; each is a *precise*
missing fact (not a proof-engineering hurdle), so the claims are documented as blocked rather
than discharged with `sorry`-laundering. No statement is weakened.

* **Missing ingredient A — "`S` is large".** There is *no* hypothesis or lemma giving a lower
  bound on `#(coeffs_of_close_proximity k ωs δ u₀ u₁)`. In [BCIKS20, §5] the inequality
  `#S / D_Y(Q) > 2·D_Y(Q)²·D_X·D_YZ(Q)` is a *standing hypothesis* of the proximity-gap regime
  (the "many close codewords" assumption), not a consequence of `ModifiedGuruswami`. It is
  directly the second conjunct of Claim 5.7 and is `R,H`-independent, hence unprovable from the
  current hypotheses. See `exists_factors_with_large_common_root_set`.

* **Missing ingredient B — "`Q` vanishes at every close `z`".** No proven fact asserts
  `(Trivariate.eval_on_Z Q z).eval (Pz …) = 0` for `z ∈ coeffs_of_close_proximity`. This is
  [BCIKS20, Lemma 5.3] (GS divisibility `(Y − Pz) ∣ Q`) lifted to the `Z`-curve. In
  `Extraction.lean` it appears only as the *antecedent* `→` of `pg_exists_R_of_Q_eval_zero` /
  `pg_exists_pair_for_z`, never as a standalone lemma. Without it the pigeonhole giving the
  first conjunct of Claim 5.7 cannot reach `#S / D_Y(Q)` (it only reaches
  `#(vanishing z) / D_Y(Q)`).

* **Missing ingredient C — the Appendix-A ↔ §5 bridge.** `RationalFunctions.lean` contains the
  vanishing criterion `Lemma_A_1` (`#(S_β β) > Λ(β)·dₕ ⟹ embeddingOf𝒪Into𝕃 β = 0`) and the
  forward inclusion `eval_resultant_eq_zero_of_mem_S_β`, but **no** lemma relating the
  Appendix-A objects (`α`, `γ`, `β`, `S_β`, `π_z`) to the §5 geometric data
  (`Pz`, `matching_set`, the word `w(x,z) = u₀ x + z·u₁ x`, `ωs`). Concretely, the converse
  direction "a geometric matching point `z` lies in `S_β (β R t)` (i.e. `π_z (β R t) = 0`)" is
  absent. This bridge is the entire substance of the proofs of Claims 5.8–5.11.

* **Missing ingredient D — `β`/`α`/`γ` are *under-specified* (root cause for 5.8/5.8'/5.9).**
  In `RationalFunctions.lean`, `β R t := (β_regular …).choose`, and `β_regular` asserts only the
  *existence* of a regular element satisfying the weight *upper* bound `Λ(β) ≤ (2t+1)·d_R·D`; it
  is realized with the trivial witness `β = 0` (`fun _ => ⟨0, by simp⟩`). Thus `β R t` is *some*
  opaque `.choose` element constrained only by that upper bound — it does **not** encode the
  recursive Hensel-lift numerator of [BCIKS20, Appendix A.4], and carries no functional relation
  to `R`, `x₀`, or the lift recursion. Consequently `α' … t = embeddingOf𝒪Into𝕃 _ (β R t) / _`
  is **underdetermined**: its value at `t ≥ k` is *not fixed* by the definitions (it depends on
  the opaque `.choose`), so Claim 5.8 (`α' … t = 0`) is neither provable *nor* refutable from the
  current `β` — it is true only under the intended (not-yet-formalized) Hensel construction.
  Even granting ingredient C, the `S_β`-largeness argument cannot be invoked because the `β` it
  must apply to is not the Hensel numerator. Closing 5.8/5.8'/5.9 therefore requires first
  *replacing* `β_regular`'s trivial realization with the genuine recursive Hensel-lift definition
  (the `β`-construction of Appendix A.4) so that `β R t` is a *function of* the lift data, not an
  arbitrary weight-bounded witness.

**Per-claim disposition.**
- 5.7 (`exists_factors_with_large_common_root_set`): blocked on A (final conjunct, unprovable as
  stated — needs an added `#S` lower-bound hypothesis) and B (first conjunct pigeonhole). The
  `R, H, Irreducible, natDegree, dvd, Separable` conjuncts are supplied by `Extraction.lean`'s
  `pg_*` toolbox + Claim 5.6, but the two cardinality conjuncts are not.
- 5.8 (`approximate_solution_is_exact_solution_coeffs`): reduces cleanly to
  `embeddingOf𝒪Into𝕃 _ (β (R …) t) = 0` (since `α' … t = embeddingOf𝒪Into𝕃 _ (β …) / _`, so
  `zero_div`), which is exactly `Lemma_A_1`'s conclusion — but `Lemma_A_1`'s hypothesis
  `#(S_β (β … t)) > Λ·dₕ` has no supplier (ingredient C). Deeper still (ingredient D), `β R t`
  is an opaque weight-bounded `.choose` rather than the Hensel numerator, so `α' … t` is
  *underdetermined* and `α' … t = 0` is neither provable nor refutable from the current `β`.
- 5.8' (`…_coeffs'`): would follow from 5.8 by `PowerSeries.subst` bookkeeping on `γ = subst …
  (mk α)`, but 5.8 is itself blocked, so 5.8' cannot stand alone.
- 5.9 (`solution_gamma_is_linear_in_Z`): consumes 5.8' (truncation of `γ` to degree `< k`,
  combined with the `degreeX P ≤ 1` output of Prop 5.5); blocked transitively.
- 5.10 (`solution_gamma_matches_word_if_subset_large`): its hypothesis `hx` bounds
  `(matching_set_at_x …).card`, but converting that into the `S_β`-largeness that `Lemma_A_1`
  consumes is exactly ingredient C; blocked.
- 5.11 (`exists_points_with_large_matching_subset`): double-counting over the matching set,
  which is `.choose` of the still-`sorry` Prop 5.5 (`exists_a_set_and_a_matching_polynomial`);
  blocked on that upstream `sorry` plus ingredient C.

Closing any of these honestly requires first landing (i) an `#S` lower-bound hypothesis on
`ModifiedGuruswami` (or on Claim 5.7), (ii) the Lemma-5.3 `Z`-curve divisibility bridge, and
(iii) the Appendix-A ↔ §5 specialization bridge `matching point ⟹ π_z (β R t) = 0`. None are
present in the current tree. -/

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
  the now-available `c57_eval_on_Z_{zero,add,mul}` ring-hom lemmas — is the precise residual
    content.
  *Verified missing hypothesis:* the per-`z` vanishing `Q(z, X, Pz(X)) ≡ 0` is the bivariate
  counting argument (more order-`m` roots than degree), which needs
  `m·(1−δ)n > natWeightedDegree Q 1 k`, i.e. `δ` within the Johnson radius
  `proximity_gap_johnson`.  But `δ` is a *free* parameter of this lemma (no `δ ≤ δ₀` hypothesis),
  so for `δ` near `1` the vanishing fails — the bridge therefore also needs the Johnson-radius side
  hypothesis, absent from the current binder.

* *Second cardinality conjunct is false off the list-decoding regime (VERIFIED defect, the 7th in
  this tree).*  The conjunct `(#S : ℝ)/(D_Y Q) > 2·D_Y Q²·D_X·D_YZ Q` is a *lower bound on `#S`*
  (`S = coeffs_of_close_proximity`) that does not follow from `ModifiedGuruswami`: for `δ < 0` (and
  `0 < n`) the set `S` is **empty** (`Extraction.coeffs_of_close_proximity_eq_empty_of_neg`), so the
  LHS is `0`, while the RHS is `≥ 0` always (`Extraction.c57_rhs_nonneg`); hence `0 > (≥0)` is
  false (`Extraction.c57_second_conjunct_unsat_of_S_empty`).  In [BCIKS20] this inequality is a
  *hypothesis* (`S` large — the list-decoding case), mis-placed into the conclusion; the faithful
  fix carries it (and the Johnson bound above) as side hypotheses, which the uneditable consumer
  signatures `(δ) (x₀) (h_gs)` of `R`/`H`/`irreducible_H`/Claims-5.8–5.11 do not admit.

With Gap A resolved, the proof obligation is retained pending the Gap-B vanishing bridge (which
  itself
needs the absent `δ ≤ δ₀` hypothesis), the false-off-regime second conjunct, and the upstream
Prop 5.5.  The binder structure `∃ R H, R ∈ … ∧ Irreducible H ∧ …` is preserved so the
downstream extractors stay well-typed. -/
lemma exists_factors_with_large_common_root_set (δ : ℚ) (x₀ : F)
  (h_gs : ModifiedGuruswami m n k ωs Q u₀ u₁) :
  ∃ R H, R ∈ (irreducible_factorization_of_gs_solution h_gs).choose_spec.choose ∧
    Irreducible H ∧ 0 < H.natDegree ∧ H ∣ (Bivariate.evalX (Polynomial.C x₀) R) ∧
    (Bivariate.evalX (Polynomial.C x₀) R).Separable ∧
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

/-- The factor `H` extracted from Claim 5.7 has positive degree in the `Y` variable, matching the
Appendix A hypotheses needed for the function field construction. -/
lemma natDegree_H_pos (h_gs : ModifiedGuruswami m n k ωs Q u₀ u₁) :
    0 < (H k δ x₀ h_gs).natDegree :=
  (exists_factors_with_large_common_root_set k δ x₀ h_gs).choose_spec.choose_spec.2.2.1

/-- The `Fact` form of `natDegree_H_pos`, for downstream declarations that take the
positivity as an instance. -/
instance fact_natDegree_H_pos (h_gs : ModifiedGuruswami m n k ωs Q u₀ u₁) :
    Fact (0 < (H k δ x₀ h_gs).natDegree) :=
  ⟨natDegree_H_pos k h_gs⟩

/-- The extracted `H` divides `R(x₀, Y, Z)`, as required for the Hensel setup in Claim A.2. -/
lemma H_dvd_evalX_R (h_gs : ModifiedGuruswami m n k ωs Q u₀ u₁) :
    H k δ x₀ h_gs ∣ Bivariate.evalX (Polynomial.C x₀) (R k δ x₀ h_gs) :=
  (exists_factors_with_large_common_root_set k δ x₀ h_gs).choose_spec.choose_spec.2.2.2.1

/-- The specialization `R(x₀, Y, Z)` is separable in `Y`, as required for Claim A.2. -/
lemma evalX_R_separable (h_gs : ModifiedGuruswami m n k ωs Q u₀ u₁) :
    (Bivariate.evalX (Polynomial.C x₀) (R k δ x₀ h_gs)).Separable :=
  (exists_factors_with_large_common_root_set k δ x₀ h_gs).choose_spec.choose_spec.2.2.2.2.1

open BCIKS20AppendixA.ClaimA2 in
/-- The Claim A.2 hypotheses satisfied by the `R,H` pair extracted from Claim 5.7. -/
lemma claimA2_hypotheses (h_gs : ModifiedGuruswami m n k ωs Q u₀ u₁) :
    Hypotheses x₀ (R k δ x₀ h_gs) (H k δ x₀ h_gs) :=
  ⟨H_dvd_evalX_R k h_gs, evalX_R_separable k h_gs⟩

open BCIKS20AppendixA.ClaimA2 in
/-- Claim 5.8 from [BCIKS20].
States that the approximate solution is actually a solution. This version of the claim is stated in
terms of coefficients.

GAP (blocked — see the §5 GAP ANALYSIS block above). `α' x₀ R … t = embeddingOf𝒪Into𝕃 _ (β R t)
/ (W^(t+1) · ξ-emb^(2t-1))`, so the goal reduces by `zero_div` to `embeddingOf𝒪Into𝕃 _ (β R t)
= 0`, which is the conclusion of `Lemma_A_1`. But `Lemma_A_1`'s hypothesis `#(S_β (β R t)) >
Λ(β R t)·dₕ` has no supplier (missing ingredient C), and more fundamentally `β R t` is an opaque
weight-bounded `.choose`, not the recursive Hensel numerator (missing ingredient D), so the
conclusion is underdetermined by the current definitions. -/
lemma approximate_solution_is_exact_solution_coeffs
    (h_gs : ModifiedGuruswami m n k ωs Q u₀ u₁)
    [Fact (0 < (H k δ x₀ h_gs).natDegree)]
    : ∀ t ≥ k,
    α'
      x₀
      (R k δ x₀ h_gs)
      (irreducible_H k h_gs)
      (natDegree_H_pos k h_gs)
      (claimA2_hypotheses k h_gs)
      t
    =
    (0 : BCIKS20AppendixA.𝕃 (H k δ x₀ h_gs))
    := by sorry

open BCIKS20AppendixA.ClaimA2 in
/-- Claim 5.8 from [BCIKS20].
States that the approximate solution is actually a solution.
This version is in terms of polynomials.

GAP (blocked — see the §5 GAP ANALYSIS block above). Equivalent to `coeff t γ' = 0` for `t ≥ k`.
Would follow from the coefficient form (`approximate_solution_is_exact_solution_coeffs`) by
`PowerSeries.subst` bookkeeping on `γ = subst (mk shift) (mk α)`, but that form is itself blocked
(ingredients C, D), so this cannot stand alone. -/
lemma approximate_solution_is_exact_solution_coeffs'
    (h_gs : ModifiedGuruswami m n k ωs Q u₀ u₁)
    [Fact (0 < (H k δ x₀ h_gs).natDegree)]
    :
    γ' x₀ (R k δ x₀ h_gs) (irreducible_H k h_gs) (natDegree_H_pos k h_gs)
        (claimA2_hypotheses k h_gs) =
        PowerSeries.mk (fun t =>
          if t ≥ k
          then (0 : BCIKS20AppendixA.𝕃 (H k δ x₀ h_gs))
          else PowerSeries.coeff t
            (γ'
              x₀
              (R k (x₀ := x₀) (δ := δ) h_gs)
              (irreducible_H k h_gs)
              (natDegree_H_pos k h_gs)
              (claimA2_hypotheses k h_gs))) := by
   sorry

open BCIKS20AppendixA.ClaimA2 in
/-- Claim 5.9 from [BCIKS20].
States that the solution `γ` is linear in the variable `Z`.

GAP (blocked — see the §5 GAP ANALYSIS block above). Consumes Claim 5.8' (the degree-`< k`
truncation of `γ`) together with the `Bivariate.degreeX P ≤ 1` output of Proposition 5.5 to read
off the linear representative `v₀ + Z·v₁`. Blocked transitively on 5.8' (ingredients C, D) and on
the still-`sorry` Prop 5.5 (`exists_a_set_and_a_matching_polynomial`, `Guruswami.lean`). -/
lemma solution_gamma_is_linear_in_Z
    (h_gs : ModifiedGuruswami m n k ωs Q u₀ u₁)
    [Fact (0 < (H k δ x₀ h_gs).natDegree)]
    :
  ∃ (v₀ v₁ : F[X]),
    γ' x₀ (R k δ x₀ h_gs) (irreducible_H k (x₀ := x₀) (δ := δ) h_gs)
      (natDegree_H_pos k (x₀ := x₀) (δ := δ) h_gs)
      (claimA2_hypotheses k (x₀ := x₀) (δ := δ) h_gs) =
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
lemma gamma_eq_P (h_gs : ModifiedGuruswami m n k ωs Q u₀ u₁) :
  γ' x₀ (R k δ x₀ h_gs) (irreducible_H k (x₀ := x₀) (δ := δ) h_gs)
    (natDegree_H_pos k (x₀ := x₀) (δ := δ) h_gs)
    (claimA2_hypotheses k (x₀ := x₀) (δ := δ) h_gs) =
  BCIKS20AppendixA.polyToPowerSeries𝕃 _
    (P k δ x₀ h_gs) :=
  Classical.choose_spec
    (Classical.choose_spec (solution_gamma_is_linear_in_Z k (δ := δ) (x₀ := x₀) h_gs))

/-- The set `S'` from [BCIKS20] (just before Claim 5.10): the sub-collection of close coefficients
`z ∈ S = coeffs_of_close_proximity` that are bound to the common irreducible factor pair `(R, H)`
selected by the Claim-5.7 pigeonhole.

REPAIR NOTE (pre-existing breakage, restored from wave-3 commit 9e8fb10b). `matching_set`,
`matching_set_is_a_sub_of_coeffs_of_close_proximity`, and the upstream Prop 5.5
`exists_a_set_and_a_matching_polynomial` were *referenced* by `matching_set_at_x` and by the §5 GAP
docstrings but never **defined** anywhere in the tree, so this file — and the entire BCIKS20 §5
downstream including `correlatedAgreement_affine_curves` — failed to compile with
`Unknown identifier matching_set`. (This breakage was masked behind the Extraction.lean failure that
this branch fixes separately; surfacing it once Extraction compiled.) We supply the missing
definition here.

Faithfulness: in [BCIKS20] `S' ⊆ S` is the fiber bound to the chosen `(R, H)`.  Pinning that fiber
formally would force `matching_set` to carry the Claim-5.7 `.choose` data `R k δ x₀ h_gs` (hence an
extra `x₀` parameter the call site `matching_set k ωs δ u₀ u₁ h_gs` does not pass).  We
therefore define `S' := S` (the maximal subset) — an honest *over-approximation* of the paper's `S'`.
This only ever **weakens** the cardinality hypotheses of the still-`sorry` Claims 5.10/5.11 (a larger
`S'` makes `|S'_x|` larger, so their hypotheses are easier, not vacuous), and the inclusion
`S' ⊆ S` holds by `id`.  No proven statement is affected. -/
noncomputable def matching_set
    (k : ℕ) (ωs : Fin n ↪ F) (δ : ℚ) (u₀ u₁ : Fin n → F)
    (_h_gs : ModifiedGuruswami m n k ωs Q u₀ u₁) : Finset F :=
  coeffs_of_close_proximity k ωs δ u₀ u₁

/-- `matching_set` (BCIKS20's `S'`) is a subset of `S = coeffs_of_close_proximity` (here, equal by
the `S' := S` over-approximation — see `matching_set`). -/
lemma matching_set_is_a_sub_of_coeffs_of_close_proximity
    (k : ℕ) (h_gs : ModifiedGuruswami m n k ωs Q u₀ u₁) {z : F}
    (h : z ∈ matching_set k ωs δ u₀ u₁ h_gs) :
    z ∈ coeffs_of_close_proximity k ωs δ u₀ u₁ := h

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
enough.

GAP (blocked — see the §5 GAP ANALYSIS block above). The hypothesis `hx` bounds
`(matching_set_at_x …).card` from below, and the conclusion is the §5 polynomial identity
`P(ωs x) = C(u₀ x) + u₁ x · X`. Bridging the geometric matching-set bound to the `S_β`-largeness
that `Lemma_A_1` consumes (so that the relevant Hensel coefficient vanishes) is exactly missing
ingredient C; the underlying `β` under-specification (ingredient D) also applies. -/
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
Claim 5.10.

GAP (blocked — see the §5 GAP ANALYSIS block above). A double-counting argument over the matching
set, which is `.choose` of the still-`sorry` Prop 5.5 (`exists_a_set_and_a_matching_polynomial`,
`Guruswami.lean`); the per-point cardinality bound additionally relies on missing ingredient C. -/
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

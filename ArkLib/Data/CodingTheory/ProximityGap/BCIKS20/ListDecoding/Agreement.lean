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

/-! ### Gap B — the trivariate graph-vanishing keystone (NOW RESOLVED)

The residual "Gap B" obstruction flagged on `exists_factors_with_large_common_root_set` and on
`exists_a_set_and_a_matching_polynomial` was: *no lemma connects `ModifiedGuruswami.Q_multiplicity`
(order-`≥ m` root multiplicity of `Q : F[Z][X][Y]` over the coefficient ring `F[Z]` at each curve
point `(C ωᵢ, C u₀ᵢ + X · C u₁ᵢ)`) to the per-`z` evaluation-zero fact `(eval_on_Z Q z).eval Pz =
0`* — i.e. "`Q` vanishes on the graph `(X, Pz(X))` of the `δ`-close codeword indexed by `z`".

The lemmas below **supply that bridge**, fully proven (`#print axioms` = `propext`,
`Classical.choice`, `Quot.sound` only).  The argument is the trivariate analogue of the bivariate
GS divisibility chain (`GuruswamiSudan.orderAt_eval_ge` / `roots_le_degree_of_deg_lt_roots`):

1. **Multiplicity transport `F[Z] → F`** (`gapB_transport_mult`).  Applying the coefficient ring
   hom `φ = evalRingHom z : F[Z] → F` (`Z ↦ z`) commutes with both `Bivariate.shift` and
   `Bivariate.coeff` (`gapB_shift_map`, `gapB_coeff_map_biv`).  Hence the order-`m` vanishing of the
   shifted coefficients of `Q` at `(C ωᵢ, C u₀ᵢ + X·C u₁ᵢ)` (extracted from `Q_multiplicity` via the
   integral-domain criterion `gapB_shift_coeff_zero_of_mult_ge_dom`) transports to order-`m`
   vanishing of `eval_on_Z Q z = Q.map (mapRingHom φ)` at the *image* point
   `(φ(C ωᵢ), φ(C u₀ᵢ + X·C u₁ᵢ)) = (ωᵢ, u₀ᵢ + z·u₁ᵢ) = (ωᵢ, (u₀ + z•u₁) i)` — exactly the word
   `w(·, z)`.  This is the field-side input `GuruswamiSudan.rootMultiplicity_ge_of_shift_zero`.

2. **Field-side graph vanishing** (`gapB_vanish_of_orderM_and_count`).  With `Q_z := eval_on_Z Q z`
   carrying order-`m` roots at `(ωᵢ, w_i)` for `i` in the agreement set `A`, `Q_z(X, Pz(X))` has a
   root of order `≥ m` at each `ωᵢ` with `i ∈ A` (`GuruswamiSudan.orderAt_eval_ge`); a polynomial of
   degree `< m·#A` with that many roots is `0` (`roots_le_degree_of_deg_lt_roots`).  The degree
   bound `(Q_z.eval Pz).natDegree ≤ natWeightedDegree Q_z 1 k` is `degree_eval_le_weightedDegree`
   (`Pz.natDegree ≤ k`).

The strict counting inequality `natWeightedDegree (eval_on_Z Q z) 1 k < m·#A` is the
*Johnson-radius* condition — `δ` within the list-decoding radius so that `#A ≥ (1−δ)n` is large
relative to the degree bound.  It is passed as an explicit hypothesis of the keystone:
`exists_factors_with_large_common_root_set` does **not** carry a `δ ≤ δ₀` binder (its `δ` is free),
which is precisely why that top-level claim still cannot be closed without statement repair (see its
docstring).  The keystone is the faithful, reusable form of the bridge: feed it the Johnson side
condition and it discharges the graph vanishing. -/

omit [DecidableEq F] [DecidableEq (RatFunc F)] [Finite F] in
/-- `Bivariate.shift` commutes with `map (mapRingHom φ)` (under `φ` on the base point). -/
private theorem gapB_shift_map {S T : Type} [CommRing S] [CommRing T]
    (φ : S →+* T) (f : S[X][Y]) (x y : S) :
    Polynomial.Bivariate.shift (f.map (Polynomial.mapRingHom φ)) (φ x) (φ y)
      = (Polynomial.Bivariate.shift f x y).map (Polynomial.mapRingHom φ) := by
  unfold Polynomial.Bivariate.shift
  rw [Polynomial.map_map]
  have hcomp : (f.map (Polynomial.mapRingHom φ)).comp
        (Polynomial.X + Polynomial.C (Polynomial.C (φ y)))
      = (f.comp (Polynomial.X + Polynomial.C (Polynomial.C y))).map (Polynomial.mapRingHom φ) := by
    rw [Polynomial.map_comp]; congr 1; simp [Polynomial.mapRingHom]
  rw [hcomp, Polynomial.map_map]
  congr 1
  ext p
  · simp [Polynomial.mapRingHom, Polynomial.compRingHom]
  · simp [Polynomial.mapRingHom, Polynomial.compRingHom]

omit [DecidableEq F] [DecidableEq (RatFunc F)] [Finite F] in
/-- `Bivariate.coeff` commutes with `map (mapRingHom φ)`. -/
private theorem gapB_coeff_map_biv {S T : Type} [CommRing S] [CommRing T]
    (φ : S →+* T) (f : S[X][Y]) (i j : ℕ) :
    Polynomial.Bivariate.coeff (f.map (Polynomial.mapRingHom φ)) i j
      = φ (Polynomial.Bivariate.coeff f i j) := by
  unfold Polynomial.Bivariate.coeff
  simp [Polynomial.coeff_map, Polynomial.mapRingHom]

omit [DecidableEq F] [DecidableEq (RatFunc F)] [Finite F] in
/-- Over an integral-domain coefficient ring, `rootMultiplicity ≥ M` forces every shifted
coefficient of total degree `< M` to vanish.  (The "easy" direction of the multiplicity criterion,
ported off the field-only `GuruswamiSudan.rootMultiplicity_le_of_coeff_ne_zero` so it applies to the
trivariate setting `S = F[Z]`.) -/
private theorem gapB_shift_coeff_zero_of_mult_ge_dom {S : Type} [CommRing S] [IsDomain S]
    [DecidableEq S] (f : S[X][Y]) (x y : S) (M : ℕ)
    (hmult : (M : Option ℕ) ≤ Bivariate.rootMultiplicity f x y) :
    ∀ s t, s + t < M → Polynomial.Bivariate.coeff (Bivariate.shift f x y) s t = 0 := by
  intro s t hst
  by_contra hc
  set g := Bivariate.shift f x y with hg
  have hle : Bivariate.rootMultiplicity₀ g ≤ some (s + t) := by
    unfold Bivariate.rootMultiplicity₀
    cases hwd : Bivariate.weightedDegree g 1 1 with
    | none => exact absurd hwd (Bivariate.weightedDegree_ne_none _ _ _)
    | some deg =>
      simp only
      have hst_le : s ≤ deg ∧ t ≤ deg := by
        have hb : 1 * (g.coeff t).natDegree + 1 * t ≤ Bivariate.natWeightedDegree g 1 1 := by
          refine Finset.le_sup (f := fun mm => 1 * (g.coeff mm).natDegree + 1 * mm)
            (Polynomial.mem_support_iff.mpr ?_)
          intro h0; apply hc; rw [Bivariate.coeff, h0]; simp
        have hsd : 1 * (g.coeff t).natDegree + 1 * t ≥ s + t := by
          have : s ≤ (g.coeff t).natDegree := by
            apply Polynomial.le_natDegree_of_ne_zero
            intro h0; apply hc; rwa [Bivariate.coeff]
          omega
        have hwd_nat : Bivariate.natWeightedDegree g 1 1 = deg := by
          rw [Bivariate.weightedDegree_eq_natWeightedDegree] at hwd; exact Option.some.inj hwd
        rw [hwd_nat] at hb; omega
      set L := List.filterMap
          (fun (p : ℕ × ℕ) ↦ if Polynomial.Bivariate.coeff g p.1 p.2 = 0 then none
            else some (p.1 + p.2))
          (List.product (List.range deg.succ) (List.range deg.succ)) with hL
      have hmem : (s + t) ∈ L := by
        rw [hL, List.mem_filterMap]
        refine ⟨(s, t), ?_, ?_⟩
        · rw [List.product, List.mem_flatMap]
          exact ⟨s, List.mem_range.mpr (Nat.lt_succ_of_le hst_le.1),
            List.mem_map.mpr ⟨t, List.mem_range.mpr (Nat.lt_succ_of_le hst_le.2), rfl⟩⟩
        · simp [hc]
      have hmin := List.min?_getD_le_of_mem (k := s + t) hmem
      cases hmm : L.min? with
      | none =>
          have : L = [] := List.min?_eq_none_iff.mp hmm
          rw [this] at hmem; simp at hmem
      | some v =>
          rw [hmm] at hmin
          simp only [Option.getD_some] at hmin
          exact Option.some_le_some.mpr hmin
  have hmult' : (M : Option ℕ) ≤ Bivariate.rootMultiplicity₀ g := by
    rw [Bivariate.rootMultiplicity] at hmult; exact hmult
  cases hrm : Bivariate.rootMultiplicity₀ g with
  | none => rw [hrm] at hmult'; simp at hmult'
  | some v =>
      rw [hrm] at hmult' hle
      simp only [Option.some_le_some] at hmult' hle
      omega

omit [DecidableEq (RatFunc F)] [Finite F] in
/-- *Multiplicity transport `F[Z] → F`.*  The order-`≥ M` root multiplicity of `Q : F[Z][X][Y]`
(over `F[Z]`) at the curve point `(C ω, C u0 + X · C u1)` transports, under the specialization
`Z ↦ z`, to order-`≥ M` multiplicity of `eval_on_Z Q z` at the image point `(ω, u0 + z·u1)`. -/
private theorem gapB_transport_mult [DecidableEq (Polynomial F)]
    (Qt : F[Z][X][Y]) (z ω u0 u1 : F) (M : ℕ)
    (hQz_ne : Qt.map (Polynomial.mapRingHom (Polynomial.evalRingHom z)) ≠ 0)
    (hm : (M : Option ℕ) ≤ Polynomial.Bivariate.rootMultiplicity Qt
            (Polynomial.C ω) (Polynomial.C u0 + Polynomial.X * Polynomial.C u1)) :
    (M : Option ℕ) ≤ Polynomial.Bivariate.rootMultiplicity
        (Qt.map (Polynomial.mapRingHom (Polynomial.evalRingHom z))) ω (u0 + z * u1) := by
  set φ := Polynomial.evalRingHom z with hφ
  set x : Polynomial F := Polynomial.C ω with hx
  set y : Polynomial F := Polynomial.C u0 + Polynomial.X * Polynomial.C u1 with hy
  have hφx : φ x = ω := by rw [hφ, hx, coe_evalRingHom, eval_C]
  have hφy : φ y = u0 + z * u1 := by
    rw [hφ, hy, map_add, map_mul, coe_evalRingHom, eval_C, eval_X, eval_C, mul_comm]
  have hvanQ := gapB_shift_coeff_zero_of_mult_ge_dom Qt x y M hm
  have hvanQz : ∀ s t, s + t < M →
      ((Bivariate.shift (Qt.map (Polynomial.mapRingHom φ)) ω (u0 + z * u1)).coeff t).coeff s = 0 := by
    intro s t hst
    have : Polynomial.Bivariate.coeff
        (Bivariate.shift (Qt.map (Polynomial.mapRingHom φ)) (φ x) (φ y)) s t = 0 := by
      rw [gapB_shift_map, gapB_coeff_map_biv, hvanQ s t hst, map_zero]
    rwa [hφx, hφy, Bivariate.coeff] at this
  exact GuruswamiSudan.rootMultiplicity_ge_of_shift_zero hQz_ne hvanQz

omit [DecidableEq (RatFunc F)] [Finite F] in
/-- *Field-side graph vanishing from order-`M` roots + a strict degree/agreement count.*  If a
bivariate `Q_z : F[X][Y]` has order-`≥ M` roots at `(ωᵢ, wᵢ)` for `i` in an agreement set `A` where
`wᵢ = P(ωᵢ)`, and `deg (Q_z.eval P) < M·#A`, then `Q_z.eval P = 0`.  This is the trivariate-friendly
re-packaging of the interior of `GuruswamiSudan.dvd_property`. -/
private theorem gapB_vanish_of_orderM_and_count
    (ωs : Fin n ↪ F) (Qz : F[X][Y]) (P : F[X]) (w : Fin n → F) (M D : ℕ) (A : Finset (Fin n))
    (hroots : ∀ i ∈ A, (M : Option ℕ) ≤ Bivariate.rootMultiplicity Qz (ωs i) (w i))
    (hmatch : ∀ i ∈ A, w i = P.eval (ωs i))
    (hdeg : (Qz.eval P).natDegree ≤ D)
    (hcount : D < M * A.card) :
    Qz.eval P = 0 := by
  by_contra hne
  have hRoot : ∀ i ∈ A, M ≤ (Qz.eval P).rootMultiplicity (ωs i) := by
    intro i hi
    have hO : GuruswamiSudan.HasOrderAt Qz (ωs i) (w i) M := by
      intro s t hst
      exact gapB_shift_coeff_zero_of_mult_ge_dom Qz (ωs i) (w i) M (hroots i hi) s t hst
    have := GuruswamiSudan.orderAt_eval_ge Qz P (ωs i) M (by rw [hmatch i hi] at hO; exact hO)
    rcases this with h | h
    · exact absurd h hne
    · exact h
  exact hne (GuruswamiSudan.roots_le_degree_of_deg_lt_roots (ωs := ωs) (Qz.eval P) M A hRoot
    (lt_of_le_of_lt hdeg hcount))

omit [DecidableEq (RatFunc F)] in
/-- **Gap-B keystone: the trivariate graph-vanishing bridge** ([BCIKS20] §5, the residual keystone
of Claim 5.7 / Prop 5.5).  Given a `ModifiedGuruswami` solution `Q`, a coefficient `z` in the
close-proximity set `S` with its `δ`-close codeword polynomial `Pz`, the nonvanishing of the
specialization `eval_on_Z Q z`, an agreement set `A` on which the word `w(·, z) = u₀ + z•u₁` matches
`Pz ∘ ωs`, and the *Johnson-radius* counting hypothesis `natWeightedDegree (eval_on_Z Q z) 1 k <
m·#A`, the polynomial `Q` vanishes on the graph of the close codeword:
`(eval_on_Z Q z).eval Pz = 0`.

This is the fact previously declared missing on `exists_factors_with_large_common_root_set`
("Missing GS-multiplicity → close-codeword-graph vanishing (Gap B)") and on
`exists_a_set_and_a_matching_polynomial` ("the binding of each `z ∈ S` to a factor requires the
vanishing `(eval_on_Z Q z).eval Pz = 0`").  It is derived honestly from
`ModifiedGuruswami.Q_multiplicity` via the transport + field-side counting lemmas above; the
Johnson-radius side condition is made explicit because the consumer claims do not carry a `δ ≤ δ₀`
binder (their `δ` is free), so it cannot be discharged internally — see the obstruction docstrings.
`#print axioms` = `propext, Classical.choice, Quot.sound` only. -/
theorem Q_vanishes_on_close_codeword_graph [DecidableEq (Polynomial F)]
    (k : ℕ) {z : F} (h_gs : ModifiedGuruswami m n k ωs Q u₀ u₁)
    (hS : z ∈ coeffs_of_close_proximity k ωs δ u₀ u₁)
    (hQz_ne : Trivariate.eval_on_Z Q z ≠ 0)
    (A : Finset (Fin n))
    (hA : ∀ i ∈ A, (u₀ + z • u₁) i = (Pz hS).eval (ωs i))
    (hcount : Bivariate.natWeightedDegree (Trivariate.eval_on_Z Q z) 1 k < m * A.card) :
    (Trivariate.eval_on_Z Q z).eval (Pz hS) = 0 := by
  set Qz := Trivariate.eval_on_Z Q z with hQz
  set P := Pz hS with hP
  have hroots : ∀ i ∈ A, (m : Option ℕ) ≤
      Bivariate.rootMultiplicity Qz (ωs i) ((u₀ + z • u₁) i) := by
    intro i hi
    have hmi0 := h_gs.Q_multiplicity i
    have hmi : (m : Option ℕ) ≤ Bivariate.rootMultiplicity Q
        (Polynomial.C (ωs i)) (Polynomial.C (u₀ i) + Polynomial.X * Polynomial.C (u₁ i)) := by
      convert ge_iff_le.mp hmi0 using 2
    have hne' : Q.map (Polynomial.mapRingHom (Polynomial.evalRingHom z)) ≠ 0 := hQz_ne
    have htr := gapB_transport_mult Q z (ωs i) (u₀ i) (u₁ i) m hne' hmi
    have hpt : (u₀ + z • u₁) i = u₀ i + z * u₁ i := by
      simp [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    rw [hpt, hQz]; exact htr
  have hdeg : (Qz.eval P).natDegree ≤ Bivariate.natWeightedDegree Qz 1 k := by
    have hPdeg : P.natDegree ≤ (k + 1) - 1 := by
      simpa using (exists_Pz_of_coeffs_of_close_proximity (n := n) (k := k) hS).choose_spec.1
    simpa using GuruswamiSudan.degree_eval_le_weightedDegree Qz P (k + 1) hPdeg
  have := gapB_vanish_of_orderM_and_count ωs Qz P (u₀ + z • u₁) m
    (Bivariate.natWeightedDegree Qz 1 k) A hroots hA hdeg hcount
  rw [hQz, hP] at this ⊢; exact this

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

* *GS-multiplicity → close-codeword-graph vanishing (Gap B — NOW RESOLVED).*  The pigeonhole needs,
  for each `z ∈ S`, the vanishing `(eval_on_Z Q z.1).eval (Pz z.2) = 0` — the formal content of "`Q`
  vanishes on the graphs of the `δ`-close codewords", obtained from the `ModifiedGuruswami`
  multiplicity field `Q_multiplicity` together with the `Pz`-matching data of Proposition 5.5.  This
  bridge is now **supplied and fully proven** by `Q_vanishes_on_close_codeword_graph` (above): the
  trivariate analogue of the bivariate `GuruswamiSudan.orderAt_eval_ge` /
  `roots_le_degree_of_deg_lt_roots` chain, transporting the order-`≥ m` root multiplicity of `Q`
  over `F[Z]` at `(C ωᵢ, C(u₀ᵢ) + X·C(u₁ᵢ))` under `Z ↦ z` (`gapB_transport_mult`) to order-`≥ m`
  vanishing of `eval_on_Z Q z` at the word point `(ωᵢ, (u₀ + z•u₁) i)`, then a degree-vs-roots count
  (`gapB_vanish_of_orderM_and_count`).  `#print axioms` is clean.
  *Verified residual side hypothesis (NOT in this binder):* the count requires the strict inequality
  `m·#A > natWeightedDegree (eval_on_Z Q z) 1 k` (with `#A ≥ (1−δ)n` the agreement count), i.e. `δ`
  within the Johnson radius `proximity_gap_johnson`.  `δ` is a *free* parameter of this Claim-5.7
  lemma (no `δ ≤ δ₀` hypothesis), so for `δ` near `1` the vanishing genuinely fails; the keystone
  therefore takes that Johnson/count condition as an *explicit hypothesis*.  Closing Claim 5.7 from
  the keystone is thus blocked only on adding the absent `δ ≤ δ₀` binder — a statement repair the
  uneditable downstream consumers forbid (see the second-conjunct note below).

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

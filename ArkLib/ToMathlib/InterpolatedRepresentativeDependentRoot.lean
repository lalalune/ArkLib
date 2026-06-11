/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/

import ArkLib.ToMathlib.InterpolatedRepresentativeSliced
import ArkLib.ToMathlib.RationalRootSupply

/-!
# Issue #304 — the dependent-root packager: `double_assignment` meets the sliced apex

**The satisfiability defect fixed here.**  The interpolation capstones
(`hrep_of_cleared_counting`, the line apexes) take a TOTAL root function
`root : (z : F) → rationalRoot (H_tilde' H) z` but consume it only at `z ∈ T` — and the
matching lane (`DoubleAssignmentChain.double_assignment`) produces rational roots only **on**
its matching set (from the branch incidence `evalEval z ((P z).eval x₀) H = 0`).  A total
function is generally unconstructible (`H̃′(z, ·)` need not have an `F`-root off the matching
set), so the total-root interface is uninstantiable from the lane — the same statement-level
bug class as the F-series findings.  This module re-derives the chain at the **dependent**
root `root : ∀ z ∈ T, rationalRoot (H_tilde' H) z` and packages the `double_assignment`
output shape directly:

* `eq_of_pi_z_eq_on_finset_dep` — the counting weld (Brick C1) at dependent roots;
* `alphaFromBeta_eq_lift_of_counting_dep` / `hrep_of_cleared_counting_dep` — Brick C3;
* `hvan_line_of_perz_data_dep` — Brick V at dependent roots + sliced separability;
* `hrep_line_of_perz_data_dep` / `exists_representative_pair_line_dep` — the apexes;
* `exists_representative_pair_of_matching_branch` — **the packager**: from a monic branch
  `H` with per-`z` incidence `evalEval z ((u₀ + z•u₁).eval x₀) H = 0` (exactly
  `double_assignment`'s output conjunct, with the root built by
  `rationalRoot_of_evalEval` and its value pinned by monicity), the per-`z` divisibilities,
  `ξ`-image nonvanishing, sliced separability, and the counting input, the bundle's
  terminal `(Ppoly, hrep, hdegX)` pair exists.
-/

open Polynomial Polynomial.Bivariate BCIKS20AppendixA BCIKS20AppendixA.ClaimA2

namespace ArkLib

namespace InterpolatedRepresentativeDependentRoot

open InterpolatedRepresentative InterpolatedRepresentativeWiring
  InterpolatedRepresentativeSliced MappedSeparability

variable {F : Type} [Field F]
variable {H : F[X][Y]} [Fact (Irreducible H)] [Fact (0 < H.natDegree)]

/-! ## Brick C1 at dependent roots -/

/-- **The counting weld with dependent roots** — `eq_of_pi_z_eq_on_finset` with the root
function required only on the agreement set. -/
theorem eq_of_pi_z_eq_on_finset_dep
    (hH : 0 < H.natDegree) {a b : 𝒪 H} (D : ℕ) (hD : D ≥ Bivariate.totalDegree H)
    {T : Finset F} (root : ∀ z ∈ T, rationalRoot (H_tilde' H) z)
    (hvan : ∀ z (hz : z ∈ T), (π_z z (root z hz)) a = (π_z z (root z hz)) b)
    {B : ℕ} (hw : weight_Λ_over_𝒪 hH (a - b) D ≤ (B : WithBot ℕ))
    (hcard : B * H.natDegree < T.card) :
    a = b := by
  have hsub : (↑T : Set F) ⊆ S_β (a - b) := by
    intro z hz
    have hz' : z ∈ T := Finset.mem_coe.mp hz
    refine ⟨root z hz', ?_⟩
    rw [map_sub, sub_eq_zero]
    exact hvan z hz'
  have hmul : weight_Λ_over_𝒪 hH (a - b) D * (H.natDegree : WithBot ℕ)
      ≤ ((B * H.natDegree : ℕ) : WithBot ℕ) := by
    have hcast : ((B * H.natDegree : ℕ) : WithBot ℕ)
        = (B : WithBot ℕ) * (H.natDegree : WithBot ℕ) := by push_cast; ring
    rw [hcast]
    gcongr
  have hbig : (↑T.card : WithBot ℕ) > weight_Λ_over_𝒪 hH (a - b) D * H.natDegree :=
    lt_of_le_of_lt hmul (by exact_mod_cast hcard)
  have hemb : embeddingOf𝒪Into𝕃 H (a - b) = 0 :=
    embedding_eq_zero_of_finset_subset_S_β hH (a - b) D hD hsub hbig
  have hzero : a - b = 0 := by
    refine embeddingOf𝒪Into𝕃_injective hH ?_
    rw [map_zero]
    exact hemb
  exact sub_eq_zero.mp hzero

/-! ## Brick C3 at dependent roots -/

section Cleared

variable (x₀ : F) (R : F[X][X][Y]) (H : F[X][Y])
variable [Fact (Irreducible H)] [Fact (0 < H.natDegree)] (hHyp : Hypotheses x₀ R H)

/-- The per-coefficient identity from dependent-root counting. -/
theorem alphaFromBeta_eq_lift_of_counting_dep
    (Bcoeff : (i₁ : ℕ) → {m : ℕ} → Nat.Partition m → 𝒪 H)
    (hH : 0 < H.natDegree) (D : ℕ) (hD : D ≥ Bivariate.totalDegree H)
    (hξ : embeddingOf𝒪Into𝕃 H (ξ x₀ R H hHyp) ≠ 0) {c : F[X]} {t : ℕ}
    {T : Finset F} (root : ∀ z ∈ T, rationalRoot (H_tilde' H) z)
    (hvan : ∀ z (hz : z ∈ T),
      (π_z z (root z hz)) (betaRec x₀ R H hHyp Bcoeff t)
        = (π_z z (root z hz)) (clearedCoeff x₀ R H hHyp c t))
    {B : ℕ}
    (hw : weight_Λ_over_𝒪 hH
        (betaRec x₀ R H hHyp Bcoeff t - clearedCoeff x₀ R H hHyp c t) D
      ≤ (B : WithBot ℕ))
    (hcard : B * H.natDegree < T.card) :
    BetaToCurveCoeffPolys.αFromBeta x₀ R H hHyp Bcoeff t
      = liftToFunctionField (H := H) c :=
  alphaFromBeta_eq_lift_of_betaRec_eq_cleared x₀ R H hHyp Bcoeff hξ
    (eq_of_pi_z_eq_on_finset_dep hH D hD root hvan hw hcard)

/-- **Brick C3 at dependent roots** — `hrep_of_cleared_counting` with the root function
required only on the counting set. -/
theorem hrep_of_cleared_counting_dep
    (Bcoeff : (i₁ : ℕ) → {m : ℕ} → Nat.Partition m → 𝒪 H)
    (hH : 0 < H.natDegree) (D : ℕ) (hD : D ≥ Bivariate.totalDegree H)
    (hξ : embeddingOf𝒪Into𝕃 H (ξ x₀ R H hHyp) ≠ 0)
    {Ppoly : F[X][Y]} {k : ℕ}
    {T : Finset F} (root : ∀ z ∈ T, rationalRoot (H_tilde' H) z)
    (hvan : ∀ t, t < k → ∀ z (hz : z ∈ T),
      (π_z z (root z hz)) (betaRec x₀ R H hHyp Bcoeff t)
        = (π_z z (root z hz)) (clearedCoeff x₀ R H hHyp (Ppoly.coeff t) t))
    {B : ℕ}
    (hw : ∀ t, t < k → weight_Λ_over_𝒪 hH
        (betaRec x₀ R H hHyp Bcoeff t - clearedCoeff x₀ R H hHyp (Ppoly.coeff t) t) D
      ≤ (B : WithBot ℕ))
    (hcard : B * H.natDegree < T.card)
    (htailP : ∀ t, k ≤ t → Ppoly.coeff t = 0)
    (htailα : ∀ t, k ≤ t → BetaToCurveCoeffPolys.αFromBeta x₀ R H hHyp Bcoeff t = 0) :
    polyToPowerSeries𝕃 H Ppoly = BetaToCurveCoeffPolys.gammaLocal x₀ R H hHyp Bcoeff := by
  ext t
  rw [coeff_polyToPowerSeries𝕃, BetaToCurveCoeffPolys.coeff_gammaLocal]
  rcases Nat.lt_or_ge t k with htk | htk
  · exact (alphaFromBeta_eq_lift_of_counting_dep x₀ R H hHyp Bcoeff hH D hD hξ root
      (hvan t htk) (hw t htk) hcard).symm
  · rw [htailP t htk, map_zero, htailα t htk]

end Cleared

/-! ## Brick V + the apexes at dependent roots and sliced separability -/

section Apex

variable (x₀ : F) (R : F[X][X][Y]) (H : F[X][Y])
variable [Fact (Irreducible H)] [Fact (0 < H.natDegree)]

/-- The set-restricted sliced separability with explicit-membership reading (the form the
packager instantiates). -/
theorem hvan_line_of_perz_data_dep (hHyp : Hypotheses x₀ R H)
    (hξ : ξ x₀ R H hHyp ≠ 0) (hlc : H.leadingCoeff = 1)
    {u₀ u₁ : F[X]} {T : Finset F}
    (root : ∀ z ∈ T, rationalRoot (H_tilde' H) z)
    (hx : ∀ z (hz : z ∈ T), (π_z z (root z hz)) (ξ x₀ R H hHyp) ≠ 0)
    (hdvd : ∀ z ∈ T, Polynomial.X - Polynomial.C (u₀ + z • u₁) ∣
      R.map (Polynomial.mapRingHom (Polynomial.evalRingHom z)))
    (hval : ∀ z (hz : z ∈ T), ((u₀ + z • u₁).eval x₀ : F) = (root z hz).1)
    (hsep : ∀ z (hz : z ∈ T),
      ((R.map (coeffHom_loc x₀ hHyp)).map
        (PowerSeries.map (π_hat_z hHyp z (root z hz) (hx z hz)))).Separable) :
    ∀ (t : ℕ), ∀ z (hz : z ∈ T),
      (π_z z (root z hz)) (betaRec x₀ R H hHyp (BetaRecGenuineBridge.BcoeffSigned H x₀ R) t)
        = (π_z z (root z hz)) (InterpolatedRepresentative.clearedCoeff x₀ R H hHyp
            ((InterpolatedRepresentative.linearShape (Polynomial.taylor x₀ u₀)
              (Polynomial.taylor x₀ u₁)).coeff t) t) := by
  intro t z hz
  exact hvan_signed_of_match hHyp hlc z (root z hz) (hx z hz)
    (localSeries_eq_aPTaylor_sliced hHyp hξ hlc z (root z hz) (hx z hz) (hdvd z hz)
      (hval z hz) (hsep z hz))
    (coeff_eval_linearShape_taylor x₀ z u₀ u₁ t).symm

/-- **The line apex at dependent roots.** -/
theorem hrep_line_of_perz_data_dep (hHyp : Hypotheses x₀ R H)
    {D : ℕ} (hD : Bivariate.totalDegree H ≤ D) (hH : 0 < H.natDegree)
    (hmonic : H.Monic) (hd2 : 2 ≤ Bivariate.natDegreeY R)
    (hdHD : H.natDegree ≤ D)
    (hD_Rx0 : D ≥ Bivariate.totalDegree (Bivariate.evalX (Polynomial.C x₀) R))
    (hRgrade : ∀ j, Bivariate.degreeX (R.coeff j) ≤ D - j)
    (hξ : ξ x₀ R H hHyp ≠ 0)
    {u₀ u₁ : F[X]} {k : ℕ} (h₀ : u₀.natDegree < k) (h₁ : u₁.natDegree < k)
    {T : Finset F} (root : ∀ z ∈ T, rationalRoot (H_tilde' H) z)
    (hx : ∀ z (hz : z ∈ T), (π_z z (root z hz)) (ξ x₀ R H hHyp) ≠ 0)
    (hdvd : ∀ z ∈ T, Polynomial.X - Polynomial.C (u₀ + z • u₁) ∣
      R.map (Polynomial.mapRingHom (Polynomial.evalRingHom z)))
    (hval : ∀ z (hz : z ∈ T), ((u₀ + z • u₁).eval x₀ : F) = (root z hz).1)
    (hsep : ∀ z (hz : z ∈ T),
      ((R.map (coeffHom_loc x₀ hHyp)).map
        (PowerSeries.map (π_hat_z hHyp z (root z hz) (hx z hz)))).Separable)
    (hcard : clearedPairBudget (Bivariate.natDegreeY R) D H.natDegree 1 k * H.natDegree
      < T.card)
    (htailα : ∀ t, k ≤ t →
      BetaToCurveCoeffPolys.αFromBeta x₀ R H hHyp
        (BetaRecGenuineBridge.BcoeffSigned H x₀ R) t = 0) :
    polyToPowerSeries𝕃 H (InterpolatedRepresentative.linearShape
        (Polynomial.taylor x₀ u₀) (Polynomial.taylor x₀ u₁))
      = BetaToCurveCoeffPolys.gammaLocal x₀ R H hHyp
          (BetaRecGenuineBridge.BcoeffSigned H x₀ R) :=
  hrep_of_cleared_counting_dep x₀ R H hHyp
    (BetaRecGenuineBridge.BcoeffSigned H x₀ R) hH D hD
    (emb_ξ_ne_zero hHyp hξ) root
    (fun t _ z hz =>
      hvan_line_of_perz_data_dep x₀ R H hHyp hξ hmonic.leadingCoeff root hx hdvd hval hsep
        t z hz)
    (hw_of_graded_signed x₀ R H hHyp hD hH hmonic hd2 hdHD hD_Rx0 hRgrade
      (fun t _ => natDegree_coeff_linearShape_le_one _ _ t))
    hcard
    (fun t hkt => InterpolatedRepresentative.coeff_linearShape_eq_zero
      (by rw [Polynomial.natDegree_taylor]; exact h₀)
      (by rw [Polynomial.natDegree_taylor]; exact h₁) hkt)
    htailα

/-! ## The packager: `double_assignment`'s branch-incidence output, consumed directly -/

/-- **The packager.**  From the matching-branch data exactly as `double_assignment` emits it —
a monic branch `H` carrying per-`z` incidence `evalEval z ((u₀ + z•u₁).eval x₀) H = 0` on the
matching set — the dependent root is `rationalRoot_of_evalEval` and its value is pinned by
monicity (`(root z).1 = (u₀ + z•u₁).eval x₀` since the `Y`-leading coefficient is `1`), so
the bundle's terminal `(Ppoly, hrep, hdegX)` pair exists, given the per-`z` divisibilities,
`ξ`-image nonvanishing, sliced separability, the counting input, and the tail. -/
theorem exists_representative_pair_of_matching_branch (hHyp : Hypotheses x₀ R H)
    {D : ℕ} (hD : Bivariate.totalDegree H ≤ D) (hH : 0 < H.natDegree)
    (hmonic : H.Monic) (hd2 : 2 ≤ Bivariate.natDegreeY R)
    (hdHD : H.natDegree ≤ D)
    (hD_Rx0 : D ≥ Bivariate.totalDegree (Bivariate.evalX (Polynomial.C x₀) R))
    (hRgrade : ∀ j, Bivariate.degreeX (R.coeff j) ≤ D - j)
    (hξ : ξ x₀ R H hHyp ≠ 0)
    {u₀ u₁ : F[X]} {k : ℕ} (h₀ : u₀.natDegree < k) (h₁ : u₁.natDegree < k)
    {T : Finset F}
    (hinc : ∀ z ∈ T, Polynomial.evalEval z ((u₀ + z • u₁).eval x₀) H = 0)
    (hdvd : ∀ z ∈ T, Polynomial.X - Polynomial.C (u₀ + z • u₁) ∣
      R.map (Polynomial.mapRingHom (Polynomial.evalRingHom z)))
    (hx : ∀ z (hz : z ∈ T),
      (π_z z (RationalRootSupply.rationalRoot_of_evalEval hH (hinc z hz)))
        (ξ x₀ R H hHyp) ≠ 0)
    (hsep : ∀ z (hz : z ∈ T),
      ((R.map (coeffHom_loc x₀ hHyp)).map
        (PowerSeries.map (π_hat_z hHyp z
          (RationalRootSupply.rationalRoot_of_evalEval hH (hinc z hz))
          (hx z hz)))).Separable)
    (hcard : clearedPairBudget (Bivariate.natDegreeY R) D H.natDegree 1 k * H.natDegree
      < T.card)
    (htailα : ∀ t, k ≤ t →
      BetaToCurveCoeffPolys.αFromBeta x₀ R H hHyp
        (BetaRecGenuineBridge.BcoeffSigned H x₀ R) t = 0) :
    ∃ Ppoly : F[X][Y],
      polyToPowerSeries𝕃 H Ppoly
          = BetaToCurveCoeffPolys.gammaLocal x₀ R H hHyp
              (BetaRecGenuineBridge.BcoeffSigned H x₀ R)
        ∧ Polynomial.Bivariate.degreeX Ppoly ≤ 1
        ∧ Ppoly.natDegree < k := by
  -- the dependent root from the branch incidence
  refine ⟨InterpolatedRepresentative.linearShape (Polynomial.taylor x₀ u₀)
    (Polynomial.taylor x₀ u₁),
    hrep_line_of_perz_data_dep x₀ R H hHyp hD hH hmonic hd2 hdHD hD_Rx0 hRgrade hξ h₀ h₁
      (fun z hz => RationalRootSupply.rationalRoot_of_evalEval hH (hinc z hz))
      hx hdvd ?_ hsep hcard htailα,
    InterpolatedRepresentative.degreeX_linearShape_le_one _ _,
    lt_of_le_of_lt (InterpolatedRepresentative.natDegree_linearShape_le _ _)
      (by rw [Polynomial.natDegree_taylor, Polynomial.natDegree_taylor]; exact max_lt h₀ h₁)⟩
  -- the branch value is pinned by monicity: the Y-leading coefficient is 1
  intro z hz
  rw [RationalRootSupply.rationalRoot_of_evalEval_val]
  have hlc : H.coeff H.natDegree = 1 := hmonic.leadingCoeff
  rw [hlc]
  simp

end Apex

end InterpolatedRepresentativeDependentRoot

end ArkLib

/-! ## Axiom audit — every declaration must rest only on
`[propext, Classical.choice, Quot.sound]`, with no `sorry`/`admit`/`axiom`/`native_decide`. -/
#print axioms ArkLib.InterpolatedRepresentativeDependentRoot.eq_of_pi_z_eq_on_finset_dep
#print axioms ArkLib.InterpolatedRepresentativeDependentRoot.alphaFromBeta_eq_lift_of_counting_dep
#print axioms ArkLib.InterpolatedRepresentativeDependentRoot.hrep_of_cleared_counting_dep
#print axioms ArkLib.InterpolatedRepresentativeDependentRoot.hvan_line_of_perz_data_dep
#print axioms ArkLib.InterpolatedRepresentativeDependentRoot.hrep_line_of_perz_data_dep
#print axioms ArkLib.InterpolatedRepresentativeDependentRoot.exists_representative_pair_of_matching_branch
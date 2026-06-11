/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.BCIKS20.Claim510AgreementSupply

/-!
# The fully-sliced grand composition (#302): NO trivariate separability anywhere

The trivariate `R.Separable` is a unit-discriminant condition, generically false (the #304
verdicts); the honest supply is per-place specialized separability on the matching loci
(the `MappedSliceSeparabilityOn` producers).  The agreement lane was sliced in
`Claim510AgreementSupply`; this file slices the TRUNCATION lane and re-lands the grand
composition with no trivariate-separability input at all:

* `matchingPoint_of_decoded_sliced` / `hvanish_of_decoded_sliced` /
  `gammaGenuine_eq_trunc_of_decoded_sliced` — the truncation chain with the per-place
  separability `hsepT` replacing `R.Separable` (the only use of `R.Separable` in the
  `t = 1` chain was deriving exactly this per-place fact);
* **`natDegree_eq_one_of_decoded_fold_sliced`** — the grand composition (hlin from GS-side
  data) with BOTH lanes sliced: every separability input is a per-place fact on a matching
  locus, exactly the shape the in-tree sliced producers emit.

Axiom-clean: `[propext, Classical.choice, Quot.sound]` (audited at end of file).
-/

set_option linter.unusedSectionVars false
set_option synthInstance.maxHeartbeats 800000
set_option maxHeartbeats 1600000

open Polynomial Polynomial.Bivariate PowerSeries
open BCIKS20AppendixA BCIKS20AppendixA.ClaimA2
open BCIKS20.HenselNumerator
open ArkLib ArkLib.DecodedProximateRoot

namespace BCIKS20.Claim510SlicedComposition

variable {F : Type} [Field F]
variable {H : F[X][Y]} [Fact (Irreducible H)] [Fact (0 < H.natDegree)]

/-- `matchingPoint_of_decoded` with the per-place separability supplied directly. -/
noncomputable def matchingPoint_of_decoded_sliced {x₀ : F} {R : F[X][X][Y]}
    (hHyp : Hypotheses x₀ R H)
    (hξ : ξ x₀ R H hHyp ≠ 0) (hlc : H.leadingCoeff = 1)
    (z : F) (root : rationalRoot (H_tilde' H) z)
    (hx : (π_z z root) (ξ x₀ R H hHyp) ≠ 0)
    {w : F[X][Y]} {k : ℕ} (hdeg : w.natDegree < k)
    (hdvd : (Polynomial.X - Polynomial.C w) ∣ R)
    (hbase : (w.eval (Polynomial.C x₀)).eval z = root.1)
    (hsepZ : ((R.map (coeffHom_loc x₀ hHyp)).map
      (PowerSeries.map (π_hat_z hHyp z root hx))).Separable)
    (t : ℕ) (hkt : k ≤ t) :
    BetaMatchingVanishes.MatchingPoint x₀ R H hHyp
      (BetaRecGenuineBridge.BcoeffSigned H x₀ R) t z root :=
  matchingPoint_of_localSeries_dvd hHyp hξ hlc z root hx
    (aPDecoded hHyp z root hx w)
    (aPDecoded_dvd hHyp z root hx hdvd)
    (aPDecoded_cong hHyp z root hx hbase)
    hsepZ
    t (coeff_aPDecoded_eq_zero hHyp z root hx (lt_of_lt_of_le hdeg hkt))

variable [Fintype F] [DecidableEq F]

/-- The `hvanish` capstone with per-place separability. -/
theorem hvanish_of_decoded_sliced {x₀ : F} {R : F[X][X][Y]}
    (hHyp : Hypotheses x₀ R H)
    (hξ : ξ x₀ R H hHyp ≠ 0) (hlc : H.leadingCoeff = 1)
    {matchingSet : Finset F}
    (root : (z : F) → rationalRoot (H_tilde' H) z)
    (hx : ∀ z ∈ matchingSet, (π_z z (root z)) (ξ x₀ R H hHyp) ≠ 0)
    {w : F[X][Y]} {k : ℕ} (hdeg : w.natDegree < k)
    (hdvd : (Polynomial.X - Polynomial.C w) ∣ R)
    (hbase : ∀ z ∈ matchingSet, (w.eval (Polynomial.C x₀)).eval z = (root z).1)
    (hsepT : ∀ z, ∀ hz : z ∈ matchingSet,
      ((R.map (coeffHom_loc x₀ hHyp)).map
        (PowerSeries.map (π_hat_z hHyp z (root z) (hx z hz)))).Separable)
    (T : ℕ) :
    ∀ t, k ≤ t → t ≤ T → ∀ z ∈ matchingSet,
      ∃ r : rationalRoot (H_tilde' H) z,
        (π_z z r) (βHensel H x₀ R hHyp t) = 0 :=
  HvanishSupply.hvanish_of_mpPoint H
    (fun t hkt _ z hz =>
      matchingPoint_of_decoded_sliced hHyp hξ hlc z (root z) (hx z hz) hdeg hdvd
        (hbase z hz) (hsepT z hz) t hkt)

/-- Claim 5.8′ (the truncation identity) with per-place separability. -/
theorem gammaGenuine_eq_trunc_of_decoded_sliced {x₀ : F} {R : F[X][X][Y]}
    (hHyp : Hypotheses x₀ R H)
    (hξ : ξ x₀ R H hHyp ≠ 0)
    {D k : ℕ} (hD : Bivariate.totalDegree H ≤ D) (hH : 0 < H.natDegree)
    (hmonic : H.Monic) (hd2 : 2 ≤ Bivariate.natDegreeY R)
    (hdHD : H.natDegree ≤ D)
    (hD_Rx0 : D ≥ Bivariate.totalDegree (Bivariate.evalX (Polynomial.C x₀) R))
    (hRgrade : ∀ j, Bivariate.degreeX (R.coeff j) ≤ D - j)
    {Ppoly : F[X][Y]}
    (hrepG : polyToPowerSeries𝕃 H Ppoly
      = ProximityPrize.BCIKS20.GammaGenuine.gammaGenuine x₀ R H hHyp)
    {matchingSet : Finset F}
    (root : (z : F) → rationalRoot (H_tilde' H) z)
    (hx : ∀ z ∈ matchingSet, (π_z z (root z)) (ξ x₀ R H hHyp) ≠ 0)
    {w : F[X][Y]} (hdeg : w.natDegree < k)
    (hdvd : (Polynomial.X - Polynomial.C w) ∣ R)
    (hbase : ∀ z ∈ matchingSet, (w.eval (Polynomial.C x₀)).eval z = (root z).1)
    (hsepT : ∀ z, ∀ hz : z ∈ matchingSet,
      ((R.map (coeffHom_loc x₀ hHyp)).map
        (PowerSeries.map (π_hat_z hHyp z (root z) (hx z hz)))).Separable)
    {disc : F[X]} (hdisc : disc ≠ 0)
    (hcover : ∀ z : F, disc.eval z ≠ 0 → z ∈ matchingSet)
    (hbig : gradedCardBudget (Bivariate.natDegreeY R) D H.natDegree Ppoly.natDegree
        + disc.natDegree < Fintype.card F) :
    ProximityPrize.BCIKS20.GammaGenuine.gammaGenuine x₀ R H hHyp
      = (↑(PowerSeries.trunc k
            (ProximityPrize.BCIKS20.GammaGenuine.gammaGenuine x₀ R H hHyp))
          : PowerSeries (𝕃 H)) :=
  GenuineTruncationFin.gammaGenuine_eq_trunc_of_graded_disc H hHyp hD hH hmonic hd2 hdHD
    hD_Rx0 hRgrade hrepG
    (hvanish_of_decoded_sliced hHyp hξ hmonic.leadingCoeff root hx hdeg hdvd hbase hsepT
      Ppoly.natDegree)
    hdisc hcover hbig

/-- **THE FULLY-SLICED GRAND COMPOSITION (hlin from GS-side data, no trivariate
separability anywhere)**: both the truncation and agreement lanes consume only per-place
specialized separability on their matching loci — exactly what the in-tree sliced
producers emit. -/
theorem natDegree_eq_one_of_decoded_fold_sliced {x₀ : F} {R : F[X][X][Y]}
    (hHyp : Hypotheses x₀ R H)
    {D n : ℕ} (hD : Bivariate.totalDegree H ≤ D) (hH : 0 < H.natDegree)
    (hmonic : H.Monic) (hd2 : 2 ≤ Bivariate.natDegreeY R)
    (hdHD : H.natDegree ≤ D)
    (hD_Rx0 : D ≥ Bivariate.totalDegree (Bivariate.evalX (Polynomial.C x₀) R))
    (hRgrade : ∀ j, Bivariate.degreeX (R.coeff j) ≤ D - j)
    {Ppoly : F[X][Y]}
    (hrepG : polyToPowerSeries𝕃 H Ppoly
      = ProximityPrize.BCIKS20.GammaGenuine.gammaGenuine x₀ R H hHyp)
    (root : (z : F) → rationalRoot (H_tilde' H) z)
    {w : F[X][Y]} (hdeg : w.natDegree < n)
    (hdvd : (Polynomial.X - Polynomial.C w) ∣ R)
    -- the truncation lane (sliced)
    {truncSet : Finset F}
    (hbaseT : ∀ z ∈ truncSet, (w.eval (Polynomial.C x₀)).eval z = (root z).1)
    (hsepT : ∀ z ∈ truncSet,
      ((R.map (coeffHom_loc x₀ hHyp)).map
        (PowerSeries.map (π_hat_z hHyp z (root z)
          (BCIKS20.Claim510AgreementSupply.pi_z_xi_ne_zero_of_monic hHyp
            hmonic.leadingCoeff z (root z))))).Separable)
    {disc : F[X]} (hdisc : disc ≠ 0)
    (hcover : ∀ z : F, disc.eval z ≠ 0 → z ∈ truncSet)
    (hbig : gradedCardBudget (Bivariate.natDegreeY R) D H.natDegree Ppoly.natDegree
        + disc.natDegree < Fintype.card F)
    -- the agreement lane (sliced)
    (e : Fin n → F) (he : Function.Injective e) (u₀ u₁ : Fin n → F)
    (matchingSet : Fin n → Finset F)
    (hbaseA : ∀ j, ∀ z ∈ matchingSet j, (w.eval (Polynomial.C x₀)).eval z = (root z).1)
    (hsepA : ∀ j, ∀ z ∈ matchingSet j,
      ((R.map (coeffHom_loc x₀ hHyp)).map
        (PowerSeries.map (π_hat_z hHyp z (root z)
          (BCIKS20.Claim510AgreementSupply.pi_z_xi_ne_zero_of_monic hHyp
            hmonic.leadingCoeff z (root z))))).Separable)
    (hfold : ∀ j, ∀ z ∈ matchingSet j,
      (w.eval (Polynomial.C (e j) + Polynomial.C x₀)).eval z = u₀ j + z * u₁ j)
    -- the numerics
    {xw : ℕ}
    (hξw : weight_Λ_over_𝒪 hH (ξ x₀ R H hHyp) D ≤ (WithBot.some xw : WithBot ℕ))
    (hcard : ∀ j, BCIKS20.Claim510Supply.killBudget n D H.natDegree
        (Bivariate.natDegreeY R) xw * H.natDegree < (matchingSet j).card) :
    H.natDegree = 1 := by
  have hlc : H.leadingCoeff = 1 := hmonic.leadingCoeff
  have hξ : ξ x₀ R H hHyp ≠ 0 :=
    BCIKS20.Claim510AgreementSupply.xi_ne_zero_of_monic hHyp hlc
  have htail : ∀ t, n ≤ t → αGenuine H x₀ R hHyp t = 0 :=
    BCIKS20.Claim59Lagrange.alphaGenuine_tail_zero_of_trunc H hHyp
      (gammaGenuine_eq_trunc_of_decoded_sliced hHyp hξ hD hH hmonic hd2 hdHD hD_Rx0
        hRgrade hrepG root
        (fun z _ => BCIKS20.Claim510AgreementSupply.pi_z_xi_ne_zero_of_monic hHyp hlc z
          (root z))
        hdeg hdvd hbaseT (fun z hz => hsepT z hz) hdisc hcover hbig)
  have hagree := BCIKS20.Claim510AgreementSupply.hagree_of_decoded hHyp hξ hlc e u₀ u₁
    matchingSet root
    (fun z => BCIKS20.Claim510AgreementSupply.pi_z_xi_ne_zero_of_monic hHyp hlc z (root z))
    hdeg hdvd hbaseA hsepA hfold
  have hweight := fun j => BCIKS20.Claim510Supply.weight_killTarget_le H x₀ R hHyp hD hH
    hmonic hd2 hdHD hD_Rx0 hRgrade hξw n (e j) (u₀ j) (u₁ j)
  exact BCIKS20.Claim510Supply.natDegree_eq_one_of_heavy_agreement H x₀ R hHyp hlc
    htail e he u₀ u₁ hD matchingSet hagree hweight hcard

/-! ## Sliced improve/capture hand-off -/

/-- **Sliced affine coefficient reading.**  This is the `Claim510AffinePair` coefficient
identity with the same per-place separability surface used by the sliced decoded-fold
theorem above, instead of a global `R.Separable` hypothesis. -/
theorem taylor_coeff_eq_affine_of_heavy_sliced {x₀ : F} {R : F[X][X][Y]}
    (hHyp : Hypotheses x₀ R H)
    (hξ : ξ x₀ R H hHyp ≠ 0) (hlc : H.leadingCoeff = 1)
    {a b : ℕ → F}
    (hlin : ∀ t, αGenuine H x₀ R hHyp t
      = liftToFunctionField (H := H)
          (Polynomial.C (a t) + Polynomial.X * Polynomial.C (b t)))
    {w : F[X][Y]}
    (hdvd : (Polynomial.X - Polynomial.C w) ∣ R)
    (z : F) (root : rationalRoot (H_tilde' H) z)
    (hx : (π_z z root) (ξ x₀ R H hHyp) ≠ 0)
    (hbase : (w.eval (Polynomial.C x₀)).eval z = root.1)
    (hsepZ : ((R.map (coeffHom_loc x₀ hHyp)).map
      (PowerSeries.map (π_hat_z hHyp z root hx))).Separable)
    (t : ℕ) :
    ((Polynomial.taylor (Polynomial.C x₀) w).coeff t).eval z = a t + z * b t := by
  rw [← BCIKS20.Claim510AgreementSupply.pi_z_aPre_eq_taylor_coeff hHyp hξ hlc z root
      hx hdvd hbase hsepZ t,
    BCIKS20.Claim510AffinePair.aPre_eq_groundAffine_of_paperZ_linear hHyp hlc hlin t,
    π_z_groundAffine]

/-- **Sliced pencil identity.**  The decoded slice equals the fixed affine pencil at one
place, with separability supplied only for that specialized place. -/
theorem slice_eq_affinePencil_of_heavy_sliced {x₀ : F} {R : F[X][X][Y]}
    (hHyp : Hypotheses x₀ R H)
    (hξ : ξ x₀ R H hHyp ≠ 0) (hlc : H.leadingCoeff = 1)
    {a b : ℕ → F}
    (hlin : ∀ t, αGenuine H x₀ R hHyp t
      = liftToFunctionField (H := H)
          (Polynomial.C (a t) + Polynomial.X * Polynomial.C (b t)))
    {w : F[X][Y]} {n : ℕ} (hwn : w.natDegree < n)
    (hdvd : (Polynomial.X - Polynomial.C w) ∣ R)
    (z : F) (root : rationalRoot (H_tilde' H) z)
    (hx : (π_z z root) (ξ x₀ R H hHyp) ≠ 0)
    (hbase : (w.eval (Polynomial.C x₀)).eval z = root.1)
    (hsepZ : ((R.map (coeffHom_loc x₀ hHyp)).map
      (PowerSeries.map (π_hat_z hHyp z root hx))).Separable)
    (ω : F) :
    (w.eval (Polynomial.C ω)).eval z
      = (BCIKS20.Claim510SliceAffine.affinePencil x₀ a n).eval ω
        + z * (BCIKS20.Claim510SliceAffine.affinePencil x₀ b n).eval ω := by
  set T : F[X][Y] := Polynomial.taylor (Polynomial.C x₀) w with hT
  have hTdeg : T.natDegree < n := by rw [hT, Polynomial.natDegree_taylor]; exact hwn
  have heval : T.eval (Polynomial.C (ω - x₀))
      = ∑ t ∈ Finset.range n, T.coeff t * (Polynomial.C (ω - x₀)) ^ t :=
    Polynomial.eval_eq_sum_range' hTdeg _
  have hslice : (w.eval (Polynomial.C ω)).eval z
      = ∑ t ∈ Finset.range n, (T.coeff t).eval z * (ω - x₀) ^ t := by
    have h1 : T.eval (Polynomial.C (ω - x₀)) = w.eval (Polynomial.C ω) := by
      rw [hT, Polynomial.taylor_eval, ← Polynomial.C_add]
      congr 2
      ring
    rw [← h1, heval, Polynomial.eval_finset_sum]
    refine Finset.sum_congr rfl fun t _ => ?_
    rw [Polynomial.eval_mul, Polynomial.eval_pow, Polynomial.eval_C]
  rw [hslice,
    Finset.sum_congr rfl fun t _ => by
      rw [show (T.coeff t).eval z = a t + z * b t from
        taylor_coeff_eq_affine_of_heavy_sliced hHyp hξ hlc hlin hdvd z root hx hbase
          hsepZ t]]
  rw [BCIKS20.Claim510SliceAffine.affinePencil_eval,
    BCIKS20.Claim510SliceAffine.affinePencil_eval, Finset.mul_sum,
    ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun t _ => ?_
  ring

variable {ι₀ : Type} [Fintype ι₀] [Nonempty ι₀] [DecidableEq ι₀]

/-- **Sliced affine capture from the heavy pencil.**  The capture step only needs
specialized separability at the bad scalar being captured. -/
theorem affineCaptured_of_pencil_proximity_sliced {x₀ : F} {R : F[X][X][Y]}
    (hHyp : Hypotheses x₀ R H)
    (hξ : ξ x₀ R H hHyp ≠ 0) (hlc : H.leadingCoeff = 1)
    {a b : ℕ → F}
    (hlin : ∀ t, αGenuine H x₀ R hHyp t
      = liftToFunctionField (H := H)
          (Polynomial.C (a t) + Polynomial.X * Polynomial.C (b t)))
    {w : F[X][Y]} {n : ℕ} (hwn : w.natDegree < n)
    (hdvd : (Polynomial.X - Polynomial.C w) ∣ R)
    (z : F) (root : rationalRoot (H_tilde' H) z)
    (hx : (π_z z root) (ξ x₀ R H hHyp) ≠ 0)
    (hbase : (w.eval (Polynomial.C x₀)).eval z = root.1)
    (hsepZ : ((R.map (coeffHom_loc x₀ hHyp)).map
      (PowerSeries.map (π_hat_z hHyp z root hx))).Separable)
    (domain : ι₀ ↪ F) (k : ℕ) (δ : ℝ≥0) (u : Code.WordStack F (Fin 2) ι₀)
    (S : Finset ι₀)
    (hScard : ((S.card : ℝ≥0) ≥ (1 - δ) * Fintype.card ι₀))
    (hSagree : ∀ i ∈ S, (w.eval (Polynomial.C (domain i))).eval z = u 0 i + z • u 1 i)
    (hSnoJoint : ¬ _root_.ProximityGap.pairJointAgreesOn
      ((ReedSolomon.code domain k : Set (ι₀ → F))) S (u 0) (u 1)) :
    CodingTheory.ProximityGap.Hab25Core.Hab25JohnsonEndgame.AffineCaptured domain k δ u z
      (BCIKS20.Claim510SliceAffine.affinePencil x₀ a n,
        BCIKS20.Claim510SliceAffine.affinePencil x₀ b n) := by
  refine ⟨S, hScard, fun i hi => ?_, hSnoJoint⟩
  have hpencil := slice_eq_affinePencil_of_heavy_sliced hHyp hξ hlc hlin hwn hdvd z root
    hx hbase hsepZ (domain i)
  have hagree := hSagree i hi
  rw [hpencil] at hagree
  rw [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_C]
  rw [← hagree]

/-- **The improve disjunct from sliced heavy data.**  This is
`Claim510Improve.improve_disjunct_of_heavy` with the terminal capture step weakened from
global `R.Separable` to per-bad-scalar specialized separability. -/
theorem improve_disjunct_of_heavy_sliced {x₀ : F} {R : F[X][X][Y]}
    (hHyp : Hypotheses x₀ R H)
    (hξ : ξ x₀ R H hHyp ≠ 0) (hlc : H.leadingCoeff = 1)
    {n : ℕ}
    (htail : ∀ t, n ≤ t → αGenuine H x₀ R hHyp t = 0)
    (e : Fin n → F) (he : Function.Injective e) (v₀ v₁ : Fin n → F)
    {D : ℕ} (hD : D ≥ Bivariate.totalDegree H)
    (nodeSet : Fin n → Finset F)
    (hagreeNodes : ∀ j, ∀ z ∈ nodeSet j, ∃ root : rationalRoot (H_tilde' H) z,
      (∑ t ∈ Finset.range n,
        π_z z root (BCIKS20.Claim510Supply.aPre H x₀ R hHyp hlc t) * (e j) ^ t)
        = v₀ j + z * v₁ j)
    {W : ℕ}
    (hweight : ∀ j, weight_Λ_over_𝒪 (Fact.out (p := 0 < H.natDegree))
        (BCIKS20.Claim510Supply.killTarget H x₀ R hHyp n (e j) (v₀ j) (v₁ j)) D
          ≤ (W : WithBot ℕ))
    (hcardNodes : ∀ j, W * H.natDegree < (nodeSet j).card)
    {w : F[X][Y]} (hwn : w.natDegree < n)
    (hdvd : (Polynomial.X - Polynomial.C w) ∣ R)
    (domain : ι₀ ↪ F) (k : ℕ) (hnk : n ≤ k) (δ : ℝ≥0)
    (u : Code.WordStack F (Fin 2) ι₀)
    (Efactor : Finset F)
    (hper : ∀ z ∈ Efactor, ∃ root : rationalRoot (H_tilde' H) z,
      ∃ hx : (π_z z root) (ξ x₀ R H hHyp) ≠ 0,
        ((R.map (coeffHom_loc x₀ hHyp)).map
          (PowerSeries.map (π_hat_z hHyp z root hx))).Separable ∧
        (w.eval (Polynomial.C x₀)).eval z = root.1 ∧
        ∃ S : Finset ι₀, ((S.card : ℝ≥0) ≥ (1 - δ) * Fintype.card ι₀) ∧
          (∀ i ∈ S, (w.eval (Polynomial.C (domain i))).eval z = u 0 i + z • u 1 i) ∧
          ¬ _root_.ProximityGap.pairJointAgreesOn
            ((ReedSolomon.code domain k : Set (ι₀ → F))) S (u 0) (u 1)) :
    ∃ d₀ d₁ : ι₀ → F, ∀ z ∈ Efactor,
      ∃ x ∈ _root_.ProximityGap.disagreeSet d₀ d₁,
        _root_.ProximityGap.affineGap d₀ d₁ z x = 0 := by
  classical
  obtain ⟨a, b, hab⟩ :=
    BCIKS20.Claim510Improve.paperZ_linear_of_heavy_agreement hHyp hlc htail e he v₀ v₁
      hD nodeSet hagreeNodes hweight hcardNodes
  have hn : 0 < n := lt_of_le_of_lt (Nat.zero_le _) hwn
  have hdeg₀ : (BCIKS20.Claim510SliceAffine.affinePencil x₀ a n).natDegree < k :=
    lt_of_lt_of_le (BCIKS20.Claim510SliceAffine.affinePencil_natDegree_lt x₀ a hn) hnk
  have hdeg₁ : (BCIKS20.Claim510SliceAffine.affinePencil x₀ b n).natDegree < k :=
    lt_of_lt_of_le (BCIKS20.Claim510SliceAffine.affinePencil_natDegree_lt x₀ b hn) hnk
  refine ⟨fun i => (BCIKS20.Claim510SliceAffine.affinePencil x₀ a n).eval (domain i)
      - u 0 i,
    fun i => (BCIKS20.Claim510SliceAffine.affinePencil x₀ b n).eval (domain i) - u 1 i,
    fun z hz => ?_⟩
  obtain ⟨root, hx, hsepZ, hbase, S, hScard, hSagree, hSnoJoint⟩ := hper z hz
  have hcap :
      CodingTheory.ProximityGap.Hab25Core.Hab25JohnsonEndgame.AffineCaptured domain k δ u z
        (BCIKS20.Claim510SliceAffine.affinePencil x₀ a n,
          BCIKS20.Claim510SliceAffine.affinePencil x₀ b n) :=
    affineCaptured_of_pencil_proximity_sliced hHyp hξ hlc hab hwn hdvd z root hx hbase
      hsepZ domain k δ u S hScard hSagree hSnoJoint
  exact CodingTheory.ProximityGap.Hab25Core.Hab25JohnsonEndgame.affineCaptured_improve
    hdeg₀ hdeg₁ hcap

/-- **Decoded-fold heavy branch to the dichotomy improve disjunct, fully sliced.**  Both
the truncation/agreement lanes and the terminal affine-capture hand-off consume only
per-place specialized separability. -/
theorem improve_disjunct_of_decoded_fold_sliced {x₀ : F} {R : F[X][X][Y]}
    (hHyp : Hypotheses x₀ R H)
    {D n : ℕ} (hD : Bivariate.totalDegree H ≤ D) (hH : 0 < H.natDegree)
    (hmonic : H.Monic) (hd2 : 2 ≤ Bivariate.natDegreeY R)
    (hdHD : H.natDegree ≤ D)
    (hD_Rx0 : D ≥ Bivariate.totalDegree (Bivariate.evalX (Polynomial.C x₀) R))
    (hRgrade : ∀ j, Bivariate.degreeX (R.coeff j) ≤ D - j)
    {Ppoly : F[X][Y]}
    (hrepG : polyToPowerSeries𝕃 H Ppoly
      = ProximityPrize.BCIKS20.GammaGenuine.gammaGenuine x₀ R H hHyp)
    (root : (z : F) → rationalRoot (H_tilde' H) z)
    {w : F[X][Y]} (hdeg : w.natDegree < n)
    (hdvd : (Polynomial.X - Polynomial.C w) ∣ R)
    {truncSet : Finset F}
    (hbaseT : ∀ z ∈ truncSet, (w.eval (Polynomial.C x₀)).eval z = (root z).1)
    (hsepT : ∀ z ∈ truncSet,
      ((R.map (coeffHom_loc x₀ hHyp)).map
        (PowerSeries.map (π_hat_z hHyp z (root z)
          (BCIKS20.Claim510AgreementSupply.pi_z_xi_ne_zero_of_monic hHyp
            hmonic.leadingCoeff z (root z))))).Separable)
    {disc : F[X]} (hdisc : disc ≠ 0)
    (hcover : ∀ z : F, disc.eval z ≠ 0 → z ∈ truncSet)
    (hbig : gradedCardBudget (Bivariate.natDegreeY R) D H.natDegree Ppoly.natDegree
        + disc.natDegree < Fintype.card F)
    (e : Fin n → F) (he : Function.Injective e) (u₀ u₁ : Fin n → F)
    (matchingSet : Fin n → Finset F)
    (hbaseA : ∀ j, ∀ z ∈ matchingSet j, (w.eval (Polynomial.C x₀)).eval z = (root z).1)
    (hsepA : ∀ j, ∀ z ∈ matchingSet j,
      ((R.map (coeffHom_loc x₀ hHyp)).map
        (PowerSeries.map (π_hat_z hHyp z (root z)
          (BCIKS20.Claim510AgreementSupply.pi_z_xi_ne_zero_of_monic hHyp
            hmonic.leadingCoeff z (root z))))).Separable)
    (hfold : ∀ j, ∀ z ∈ matchingSet j,
      (w.eval (Polynomial.C (e j) + Polynomial.C x₀)).eval z = u₀ j + z * u₁ j)
    {xw : ℕ}
    (hξw : weight_Λ_over_𝒪 hH (ξ x₀ R H hHyp) D ≤ (WithBot.some xw : WithBot ℕ))
    (hcard : ∀ j, BCIKS20.Claim510Supply.killBudget n D H.natDegree
        (Bivariate.natDegreeY R) xw * H.natDegree < (matchingSet j).card)
    (domain : ι₀ ↪ F) (k : ℕ) (hnk : n ≤ k) (δ : ℝ≥0)
    (u : Code.WordStack F (Fin 2) ι₀) (Efactor : Finset F)
    (hper : ∀ z ∈ Efactor,
      ((R.map (coeffHom_loc x₀ hHyp)).map
        (PowerSeries.map (π_hat_z hHyp z (root z)
          (BCIKS20.Claim510AgreementSupply.pi_z_xi_ne_zero_of_monic hHyp
            hmonic.leadingCoeff z (root z))))).Separable ∧
      (w.eval (Polynomial.C x₀)).eval z = (root z).1 ∧
      ∃ S : Finset ι₀, ((S.card : ℝ≥0) ≥ (1 - δ) * Fintype.card ι₀) ∧
        (∀ i ∈ S, (w.eval (Polynomial.C (domain i))).eval z = u 0 i + z • u 1 i) ∧
        ¬ _root_.ProximityGap.pairJointAgreesOn
          ((ReedSolomon.code domain k : Set (ι₀ → F))) S (u 0) (u 1)) :
    ∃ d₀ d₁ : ι₀ → F, ∀ z ∈ Efactor,
      ∃ x ∈ _root_.ProximityGap.disagreeSet d₀ d₁,
        _root_.ProximityGap.affineGap d₀ d₁ z x = 0 := by
  have hlc : H.leadingCoeff = 1 := hmonic.leadingCoeff
  have hξ : ξ x₀ R H hHyp ≠ 0 :=
    BCIKS20.Claim510AgreementSupply.xi_ne_zero_of_monic hHyp hlc
  have htail : ∀ t, n ≤ t → αGenuine H x₀ R hHyp t = 0 :=
    BCIKS20.Claim59Lagrange.alphaGenuine_tail_zero_of_trunc H hHyp
      (gammaGenuine_eq_trunc_of_decoded_sliced hHyp hξ hD hH hmonic hd2 hdHD hD_Rx0
        hRgrade hrepG root
        (fun z _ => BCIKS20.Claim510AgreementSupply.pi_z_xi_ne_zero_of_monic hHyp hlc z
          (root z))
        hdeg hdvd hbaseT (fun z hz => hsepT z hz) hdisc hcover hbig)
  have hagree := BCIKS20.Claim510AgreementSupply.hagree_of_decoded hHyp hξ hlc e u₀ u₁
    matchingSet root
    (fun z => BCIKS20.Claim510AgreementSupply.pi_z_xi_ne_zero_of_monic hHyp hlc z (root z))
    hdeg hdvd hbaseA hsepA hfold
  have hweight := fun j => BCIKS20.Claim510Supply.weight_killTarget_le H x₀ R hHyp hD hH
    hmonic hd2 hdHD hD_Rx0 hRgrade hξw n (e j) (u₀ j) (u₁ j)
  exact improve_disjunct_of_heavy_sliced hHyp hξ hlc htail e he u₀ u₁ hD matchingSet
    hagree hweight hcard hdeg hdvd domain k hnk δ u Efactor
    (fun z hz => by
      obtain ⟨hsepz, hbasez, S, hScard, hSagree, hSnoJoint⟩ := hper z hz
      exact ⟨root z,
        BCIKS20.Claim510AgreementSupply.pi_z_xi_ne_zero_of_monic hHyp hlc z (root z),
        hsepz, hbasez, S, hScard, hSagree, hSnoJoint⟩)

end BCIKS20.Claim510SlicedComposition

/-! ## Axiom audit — all kernel-clean. -/
#print axioms BCIKS20.Claim510SlicedComposition.matchingPoint_of_decoded_sliced
#print axioms BCIKS20.Claim510SlicedComposition.hvanish_of_decoded_sliced
#print axioms BCIKS20.Claim510SlicedComposition.gammaGenuine_eq_trunc_of_decoded_sliced
#print axioms BCIKS20.Claim510SlicedComposition.natDegree_eq_one_of_decoded_fold_sliced
#print axioms BCIKS20.Claim510SlicedComposition.taylor_coeff_eq_affine_of_heavy_sliced
#print axioms BCIKS20.Claim510SlicedComposition.slice_eq_affinePencil_of_heavy_sliced
#print axioms BCIKS20.Claim510SlicedComposition.affineCaptured_of_pencil_proximity_sliced
#print axioms BCIKS20.Claim510SlicedComposition.improve_disjunct_of_heavy_sliced
#print axioms BCIKS20.Claim510SlicedComposition.improve_disjunct_of_decoded_fold_sliced

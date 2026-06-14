/-
Issue #304 — the satisfiable-bundle assembler: `Section5StrictDataFinOn.ofProducersOn`
and the full producer assemblies wiring every landed supplier.

Part 0 inlines the landed `ArkLib.ToMathlib.BCIKS20StrictDataFinOn.lean` verbatim (its
source is on `main` but its `.olean` is not yet built, so the scratch re-elaborates it).
Part 1 is new: the producer-side assembly of the satisfiable bundle.

## Supplier map (everything landed, axiom-clean)

| `Section5StrictDataFinOn` field | supplier |
| ------------------------------- | -------- |
| GS head (`x₀ R H hIrr hPos hHyp hH D hD`) | `GSFactorData.Bundle` (built by `GSFactorData.of_section5Inputs` from the GS interpolant side) |
| `matchingSet`, `rootOn`         | inputs (the honest membership-dependent root family — finding #3) |
| `T`                             | `:= Ppoly.natDegree` (fixed by the Prop-5.5 representative) |
| `mpFinOn`                       | `Match304.mpPointOn_of_polyProximate_at_T` (abstract per-place Hensel datum, per-`(t,z)` `hαβ` input) or `mpFinOn_of_localSeries(_dvd)` below (the canonical per-place series: `hαβ` discharged internally by `coeff_localSeries_mul`, at `Bcoeff := BcoeffSigned`) |
| `hcardFin`                      | `Match304.hcardFin_of_badSet` (App-A weight budgets + bad-set counting) or `GenuineMonicCapstone.hcardFin_of_graded_signed` ∘ `gradedConcreteFin_of_disc` (graded chain at the signed canonical family, budgets PROVEN) |
| `htailDeg`                      | `KeystoneAssembly.htailDeg_field` (= `TailDegProducer.htailDeg_of_polynomial_representative`) |
| `hsubst`                        | input (substitution validity) |
| `hγ`                            | `GammaFromBeta.hγ_field_of_betaEq` (from the numerator identification `hβ`; at `BcoeffSigned` the `hβ` premise becomes `β = βHensel` via `betaRec_BcoeffSigned_eq_βHensel`) |
| `Ppoly`/`hrep`/`hdegX`          | inputs (the Prop-5.5 linear representative) |
| `hPz`                           | `HPzBridge.hPz_of_henselDatum` (from `hHensel`/`hdeg`) |
-/
import ArkLib.ToMathlib.MatchingGeometryProducersOn
import ArkLib.ToMathlib.BCIKS20StrictDataFinOn
import ArkLib.ToMathlib.HcardDischarge
import ArkLib.ToMathlib.KeystoneAssembly
import ArkLib.ToMathlib.BetaWeightGradedSupply
import ArkLib.ToMathlib.GenuineMonicCapstone
import ArkLib.ToMathlib.MatchingPointFromLocalSeries

set_option linter.style.longLine false
set_option linter.unusedSectionVars false

open Polynomial Polynomial.Bivariate BCIKS20AppendixA BCIKS20AppendixA.ClaimA2 ToRatFunc Ideal
open ProximityGap Code NNReal Finset Function ProbabilityTheory
open scoped BigOperators ENNReal ProbabilityTheory LinearCode

namespace ArkLib

namespace RootOn304

open CorrelatedAgreementListDecodingClosed
open BetaToCurveCoeffPolys
open HcardDischarge

/-! # Part 1 — NEW (#304): the producer assembly of the satisfiable bundle -/

/-! ## F. The per-place `mpFinOn` supplier from the canonical local Hensel series

`matchingPoint_of_localSeries` (landed) fires a single `MatchingPoint` at a single `(t, z)`
from the constructed local series — the `hαβ` reading is discharged internally by
`coeff_localSeries_mul` + the signed-canonical bridge, so NO abstract `hαβ` input remains.
Threading it over the finite counting range with the membership-dependent root family gives
the exact `mpFinOn` field at `Bcoeff := BcoeffSigned` (the per-`t` `haP_coeff` is truncation:
the proximate root is the decoded polynomial `Pz z` of `natDegree < k`). -/

section MpFinOnLocalSeries

open BetaRecGenuineBridge

variable {F : Type} [Field F]
variable {H : F[X][Y]} [Fact (Irreducible H)] [Fact (0 < H.natDegree)]

/-- **Restricted-root `mpFinOn` from the canonical per-place local series** (root form).
All series-level matching inputs (`f`, `aβ`, `a₀`, `w`, `x`, `hαβ`) of
`Match304.mpFinOn_of_henselData_polyProximate` are *constructed* here; the remaining per-place
inputs are exclusively GS-side: the unit reading `hx`, the decoded proximate root `Pz` (degree,
root, congruence) and the GS squarefree condition `hsepR`. -/
noncomputable def mpFinOn_of_localSeries {x₀ : F} {R : F[X][X][Y]} (hHyp : Hypotheses x₀ R H)
    (hξ : ξ x₀ R H hHyp ≠ 0) (hlc : H.leadingCoeff = 1)
    {k T : ℕ} {matchingSet : Finset F}
    (rootOn : ∀ z ∈ matchingSet, rationalRoot (H_tilde' H) z)
    (hx : ∀ z (hz : z ∈ matchingSet), (π_z z (rootOn z hz)) (ξ x₀ R H hHyp) ≠ 0)
    (Pz : F → Polynomial F)
    (hPdeg : ∀ z ∈ matchingSet, (Pz z).natDegree < k)
    (haP_root : ∀ z (hz : z ∈ matchingSet),
      ((R.map (coeffHom_loc x₀ hHyp)).map
        (PowerSeries.map (π_hat_z hHyp z (rootOn z hz) (hx z hz)))).IsRoot
        ((Pz z : PowerSeries F)))
    (haP_cong : ∀ z (hz : z ∈ matchingSet),
      (Pz z : PowerSeries F) - PowerSeries.C ((π_z z (rootOn z hz))
          (BCIKS20.HenselNumerator.βHensel H x₀ R hHyp 0))
        ∈ Ideal.span {(PowerSeries.X : PowerSeries F)})
    (hsepR : R.Separable) :
    ∀ t, k ≤ t → t ≤ T → ∀ z (hz : z ∈ matchingSet),
      BetaMatchingVanishes.MatchingPoint x₀ R H hHyp
        (BcoeffSigned H x₀ R) t z (rootOn z hz) :=
  fun t hkt _htT z hz =>
    matchingPoint_of_localSeries hHyp hξ hlc z (rootOn z hz) (hx z hz)
      ((Pz z : PowerSeries F)) (haP_root z hz) (haP_cong z hz)
      (specialized_separable_of_R_separable hHyp z (rootOn z hz) (hx z hz) hsepR)
      t (Match304.coeff_coe_eq_zero_of_natDegree_lt (hPdeg z hz) hkt)

/-- **Restricted-root `mpFinOn` from the canonical per-place local series** (GS-handshake /
divisibility form): the proximate-root membership arrives as the GS matching-factor
divisibility `(Y − P_z) ∣ f_z` — the `MatchingExtractor` output shape. -/
noncomputable def mpFinOn_of_localSeries_dvd {x₀ : F} {R : F[X][X][Y]} (hHyp : Hypotheses x₀ R H)
    (hξ : ξ x₀ R H hHyp ≠ 0) (hlc : H.leadingCoeff = 1)
    {k T : ℕ} {matchingSet : Finset F}
    (rootOn : ∀ z ∈ matchingSet, rationalRoot (H_tilde' H) z)
    (hx : ∀ z (hz : z ∈ matchingSet), (π_z z (rootOn z hz)) (ξ x₀ R H hHyp) ≠ 0)
    (Pz : F → Polynomial F)
    (hPdeg : ∀ z ∈ matchingSet, (Pz z).natDegree < k)
    (hdvd : ∀ z (hz : z ∈ matchingSet),
      (Polynomial.X - Polynomial.C ((Pz z : PowerSeries F))) ∣
        ((R.map (coeffHom_loc x₀ hHyp)).map
          (PowerSeries.map (π_hat_z hHyp z (rootOn z hz) (hx z hz)))))
    (haP_cong : ∀ z (hz : z ∈ matchingSet),
      (Pz z : PowerSeries F) - PowerSeries.C ((π_z z (rootOn z hz))
          (BCIKS20.HenselNumerator.βHensel H x₀ R hHyp 0))
        ∈ Ideal.span {(PowerSeries.X : PowerSeries F)})
    (hsepR : R.Separable) :
    ∀ t, k ≤ t → t ≤ T → ∀ z (hz : z ∈ matchingSet),
      BetaMatchingVanishes.MatchingPoint x₀ R H hHyp
        (BcoeffSigned H x₀ R) t z (rootOn z hz) :=
  fun t hkt _htT z hz =>
    matchingPoint_of_localSeries_dvd hHyp hξ hlc z (rootOn z hz) (hx z hz)
      ((Pz z : PowerSeries F)) (hdvd z hz) (haP_cong z hz)
      (specialized_separable_of_R_separable hHyp z (rootOn z hz) (hx z hz) hsepR)
      t (Match304.coeff_coe_eq_zero_of_natDegree_lt (hPdeg z hz) hkt)

end MpFinOnLocalSeries

/-! ## G. The bundle assemblers -/

section ProducersOn

open BetaRecGenuineBridge

variable {ι : Type} [Fintype ι] [Nonempty ι] [DecidableEq ι]
variable {F : Type} [Field F] [Fintype F] [DecidableEq F]

/-- **The satisfiable-bundle producer assembly** — the restricted (`rootOn`/`mpFinOn`) mirror of
`KeystoneAssembly.section5DataFin_of_producers`: constructs `Section5StrictDataFinOn` from the
GS-factor bundle and per-field suppliers, with `T := Ppoly.natDegree`, `htailDeg` discharged by
`KeystoneAssembly.htailDeg_field`, `hγ` by `GammaFromBeta.hγ_field_of_betaEq`, and `hPz` by
`HPzBridge.hPz_of_henselDatum`.  Unlike the total assembler, NO total root family is demanded:
`rootOn` and `mpPointOn` are membership-dependent (finding #3). -/
noncomputable def Section5StrictDataFinOn.ofProducersOn {k deg : ℕ} {domain : ι ↪ F} {δ : ℝ≥0}
    {u : WordStack F (Fin (k + 1)) ι} {P : F → Polynomial F}
    {x₀ : F} (b : GSFactorData.Bundle (F := F) x₀)
    [_inst_hIrr : Fact (Irreducible b.H)] [_inst_hPos : Fact (0 < b.H.natDegree)]
    (Bcoeff : (i₁ : ℕ) → {m : ℕ} → Nat.Partition m → 𝒪 b.H)
    (matchingSet : Finset F)
    (rootOn : ∀ z ∈ matchingSet, rationalRoot (H_tilde' b.H) z)
    (Ppoly : F[X][Y])
    (hrep : polyToPowerSeries𝕃 b.H Ppoly = γ x₀ b.R b.H b.hHyp)
    (hdegX : Polynomial.Bivariate.degreeX Ppoly ≤ 1)
    (mpPointOn : ∀ t, k ≤ t → t ≤ Ppoly.natDegree → ∀ z (hz : z ∈ matchingSet),
      BetaMatchingVanishes.MatchingPoint x₀ b.R b.H b.hHyp Bcoeff t z (rootOn z hz))
    (hcardFin : ∀ t, k ≤ t → t ≤ Ppoly.natDegree → (↑matchingSet.card : WithBot ℕ)
        > weight_Λ_over_𝒪 b.hH (betaRec x₀ b.R b.H b.hHyp Bcoeff t) b.D * b.H.natDegree)
    (hsubst : PowerSeries.HasSubst (Claim59Conditional.shiftSeries x₀ b.H))
    (hβ : ∀ t, β (H := b.H) b.R t = betaRec x₀ b.R b.H b.hHyp Bcoeff t)
    (hHensel : ∀ v₀ v₁ : F[X],
      γ x₀ b.R b.H b.hHyp = polyToPowerSeries𝕃 b.H
        ((Polynomial.map Polynomial.C v₀)
          + (Polynomial.C Polynomial.X) * (Polynomial.map Polynomial.C v₁)) →
      HPzBridge.HenselDatum (k := k) (deg := deg) (domain := domain) (δ := δ) u P v₀ v₁)
    (hdeg : ∀ v₀ v₁ : F[X],
      γ x₀ b.R b.H b.hHyp = polyToPowerSeries𝕃 b.H
        ((Polynomial.map Polynomial.C v₀)
          + (Polynomial.C Polynomial.X) * (Polynomial.map Polynomial.C v₁)) →
      v₀.natDegree < k + 1 ∧ v₁.natDegree < k + 1) :
    Section5StrictDataFinOn (k := k) (deg := deg) (domain := domain) (δ := δ) u P :=
  haveI := b.hIrr
  haveI := b.hPos
  { x₀ := x₀
    R := b.R
    H := b.H
    hIrr := b.hIrr
    hPos := b.hPos
    hHyp := b.hHyp
    Bcoeff := Bcoeff
    hH := b.hH
    D := b.D
    hD := b.hD
    matchingSet := matchingSet
    rootOn := rootOn
    T := Ppoly.natDegree
    mpFinOn := mpPointOn
    hcardFin := hcardFin
    htailDeg := KeystoneAssembly.htailDeg_field hsubst
      (GammaFromBeta.hγ_field_of_betaEq x₀ b.R b.H b.hHyp Bcoeff hβ) hrep
    hsubst := hsubst
    hγ := GammaFromBeta.hγ_field_of_betaEq x₀ b.R b.H b.hHyp Bcoeff hβ
    Ppoly := Ppoly
    hrep := hrep
    hdegX := hdegX
    hPz := HPzBridge.hPz_of_henselDatum hHensel hdeg }

/-- **Strictness/consistency check**: instantiating the restricted assembler with a total root
family recovers — definitionally — the restriction (`ofTotal`) of the total assembler
`KeystoneAssembly.section5DataFin_of_producers`.  So `ofProducersOn` strictly generalizes the
total producer assembly. -/
theorem ofProducersOn_eq_ofTotal_producers {k deg : ℕ} {domain : ι ↪ F} {δ : ℝ≥0}
    {u : WordStack F (Fin (k + 1)) ι} {P : F → Polynomial F}
    {x₀ : F} (b : GSFactorData.Bundle (F := F) x₀)
    [_inst_hIrr : Fact (Irreducible b.H)] [_inst_hPos : Fact (0 < b.H.natDegree)]
    (Bcoeff : (i₁ : ℕ) → {m : ℕ} → Nat.Partition m → 𝒪 b.H)
    (matchingSet : Finset F)
    (root : (z : F) → rationalRoot (H_tilde' b.H) z)
    (Ppoly : F[X][Y])
    (hrep : polyToPowerSeries𝕃 b.H Ppoly = γ x₀ b.R b.H b.hHyp)
    (hdegX : Polynomial.Bivariate.degreeX Ppoly ≤ 1)
    (mpPoint : ∀ t, k ≤ t → t ≤ Ppoly.natDegree → ∀ z ∈ matchingSet,
      BetaMatchingVanishes.MatchingPoint x₀ b.R b.H b.hHyp Bcoeff t z (root z))
    (hcardFin : ∀ t, k ≤ t → t ≤ Ppoly.natDegree → (↑matchingSet.card : WithBot ℕ)
        > weight_Λ_over_𝒪 b.hH (betaRec x₀ b.R b.H b.hHyp Bcoeff t) b.D * b.H.natDegree)
    (hsubst : PowerSeries.HasSubst (Claim59Conditional.shiftSeries x₀ b.H))
    (hβ : ∀ t, β (H := b.H) b.R t = betaRec x₀ b.R b.H b.hHyp Bcoeff t)
    (hHensel : ∀ v₀ v₁ : F[X],
      γ x₀ b.R b.H b.hHyp = polyToPowerSeries𝕃 b.H
        ((Polynomial.map Polynomial.C v₀)
          + (Polynomial.C Polynomial.X) * (Polynomial.map Polynomial.C v₁)) →
      HPzBridge.HenselDatum (k := k) (deg := deg) (domain := domain) (δ := δ) u P v₀ v₁)
    (hdeg : ∀ v₀ v₁ : F[X],
      γ x₀ b.R b.H b.hHyp = polyToPowerSeries𝕃 b.H
        ((Polynomial.map Polynomial.C v₀)
          + (Polynomial.C Polynomial.X) * (Polynomial.map Polynomial.C v₁)) →
      v₀.natDegree < k + 1 ∧ v₁.natDegree < k + 1) :
    Section5StrictDataFinOn.ofTotal
        (KeystoneAssembly.section5DataFin_of_producers (k := k) (deg := deg) (domain := domain)
          (δ := δ) (u := u) (P := P) (x₀ := x₀) b Bcoeff matchingSet root Ppoly hrep hdegX
          mpPoint hcardFin hsubst hβ hHensel hdeg)
      = Section5StrictDataFinOn.ofProducersOn b Bcoeff matchingSet (fun z _ => root z) Ppoly
          hrep hdegX (fun t hkt htT z hz => mpPoint t hkt htT z hz) hcardFin hsubst hβ
          hHensel hdeg := rfl

/-- **Producer assembly with the bad-set `hcardFin` item** — the restricted mirror of
`Match304.section5DataFin_of_producers_badSet`: the `hcardFin` supplier is replaced by its honest
§6 geometry sources (the App-A weight budgets `hbB`/`hBzero`/`hbξ` and the two counting facts
`hcover`/`hbig`), discharged through `Match304.hcardFin_of_badSet`. -/
noncomputable def Section5StrictDataFinOn.ofProducersOn_badSet {k deg : ℕ} {domain : ι ↪ F}
    {δ : ℝ≥0} {u : WordStack F (Fin (k + 1)) ι} {P : F → Polynomial F}
    {x₀ : F} (b : GSFactorData.Bundle (F := F) x₀)
    [_inst_hIrr : Fact (Irreducible b.H)] [_inst_hPos : Fact (0 < b.H.natDegree)]
    (Bcoeff : (i₁ : ℕ) → {m : ℕ} → Nat.Partition m → 𝒪 b.H)
    (matchingSet bad : Finset F)
    (rootOn : ∀ z ∈ matchingSet, rationalRoot (H_tilde' b.H) z)
    (Ppoly : F[X][Y])
    (hrep : polyToPowerSeries𝕃 b.H Ppoly = γ x₀ b.R b.H b.hHyp)
    (hdegX : Polynomial.Bivariate.degreeX Ppoly ≤ 1)
    (mpPointOn : ∀ t, k ≤ t → t ≤ Ppoly.natDegree → ∀ z (hz : z ∈ matchingSet),
      BetaMatchingVanishes.MatchingPoint x₀ b.R b.H b.hHyp Bcoeff t z (rootOn z hz))
    -- the App-A weight budgets (`d := b.R.natDegree`):
    (hd1 : 1 ≤ b.R.natDegree) (hdH_le : b.H.natDegree ≤ b.R.natDegree)
    (hdH_D : b.H.natDegree ≤ b.D)
    (hbB : ∀ (i₁ : ℕ) {m : ℕ} (p : Nat.Partition m),
        weight_Λ_over_𝒪 b.hH (Bcoeff i₁ p) b.D
          ≤ (WithBot.some ((b.D - Multiset.card p.parts)
              + (b.R.natDegree - betaδ i₁ - Multiset.card p.parts)
                * (b.D - b.H.natDegree)) : WithBot ℕ))
    (hBzero : ∀ (i₁ : ℕ) {m : ℕ} (p : Nat.Partition m),
        b.R.natDegree - betaδ i₁ < Multiset.card p.parts → Bcoeff i₁ p = 0)
    (hbξ : weight_Λ_over_𝒪 b.hH (ξ x₀ b.R b.H b.hHyp) b.D
        ≤ (WithBot.some ((b.R.natDegree - 1) * (b.D - b.H.natDegree + 1)) : WithBot ℕ))
    -- the §6 bad-set counting facts:
    (hcover : ∀ z : F, z ∉ bad → z ∈ matchingSet)
    (hbig : (2 * Ppoly.natDegree + 1) * b.R.natDegree * b.D * b.H.natDegree + bad.card
        < Fintype.card F)
    (hsubst : PowerSeries.HasSubst (Claim59Conditional.shiftSeries x₀ b.H))
    (hβ : ∀ t, β (H := b.H) b.R t = betaRec x₀ b.R b.H b.hHyp Bcoeff t)
    (hHensel : ∀ v₀ v₁ : F[X],
      γ x₀ b.R b.H b.hHyp = polyToPowerSeries𝕃 b.H
        ((Polynomial.map Polynomial.C v₀)
          + (Polynomial.C Polynomial.X) * (Polynomial.map Polynomial.C v₁)) →
      HPzBridge.HenselDatum (k := k) (deg := deg) (domain := domain) (δ := δ) u P v₀ v₁)
    (hdeg : ∀ v₀ v₁ : F[X],
      γ x₀ b.R b.H b.hHyp = polyToPowerSeries𝕃 b.H
        ((Polynomial.map Polynomial.C v₀)
          + (Polynomial.C Polynomial.X) * (Polynomial.map Polynomial.C v₁)) →
      v₀.natDegree < k + 1 ∧ v₁.natDegree < k + 1) :
    Section5StrictDataFinOn (k := k) (deg := deg) (domain := domain) (δ := δ) u P :=
  Section5StrictDataFinOn.ofProducersOn b Bcoeff matchingSet rootOn Ppoly hrep hdegX mpPointOn
    (Match304.hcardFin_of_badSet x₀ b.R b.H b.hHyp Bcoeff b.hD b.hH hd1 hdH_le hdH_D
      hbB hBzero hbξ hcover hbig)
    hsubst hβ hHensel hdeg

/-- **Producer assembly at the signed canonical family with the PROVEN graded weight chain**
(monic case): `Bcoeff := BcoeffSigned`, `hcardFin` fully discharged by
`GenuineMonicCapstone.hcardFin_of_graded_signed` ∘ `gradedConcreteFin_of_disc` (the App-A.4
budgets are theorems, not inputs), and the `hγ` numerator identification taken in its honest
genuine form `β = βHensel` (transported through `betaRec_BcoeffSigned_eq_βHensel`). -/
noncomputable def Section5StrictDataFinOn.ofProducersOn_gradedSigned {k deg : ℕ}
    {domain : ι ↪ F} {δ : ℝ≥0} {u : WordStack F (Fin (k + 1)) ι} {P : F → Polynomial F}
    {x₀ : F} (b : GSFactorData.Bundle (F := F) x₀)
    [_inst_hIrr : Fact (Irreducible b.H)] [_inst_hPos : Fact (0 < b.H.natDegree)]
    (matchingSet : Finset F)
    (rootOn : ∀ z ∈ matchingSet, rationalRoot (H_tilde' b.H) z)
    (Ppoly : F[X][Y])
    (hmonic : b.H.Monic)
    (hrep : polyToPowerSeries𝕃 b.H Ppoly = γ x₀ b.R b.H b.hHyp)
    (hdegX : Polynomial.Bivariate.degreeX Ppoly ≤ 1)
    (mpPointOn : ∀ t, k ≤ t → t ≤ Ppoly.natDegree → ∀ z (hz : z ∈ matchingSet),
      BetaMatchingVanishes.MatchingPoint x₀ b.R b.H b.hHyp
        (BcoeffSigned b.H x₀ b.R) t z (rootOn z hz))
    -- the graded budget side conditions (paper grading of `R`):
    (hd2 : 2 ≤ Bivariate.natDegreeY b.R) (hdHD : b.H.natDegree ≤ b.D)
    (hD_Rx0 : b.D ≥ Bivariate.totalDegree (Bivariate.evalX (Polynomial.C x₀) b.R))
    (hR : ∀ j, Bivariate.degreeX (b.R.coeff j) ≤ b.D - j)
    -- the §6 discriminant counting:
    {disc : F[X]} (hdisc : disc ≠ 0)
    (hcover : ∀ z : F, disc.eval z ≠ 0 → z ∈ matchingSet)
    (hbig : gradedCardBudget (Bivariate.natDegreeY b.R) b.D b.H.natDegree Ppoly.natDegree
        + disc.natDegree < Fintype.card F)
    (hsubst : PowerSeries.HasSubst (Claim59Conditional.shiftSeries x₀ b.H))
    -- the genuine numerator identification (L13 content, in `βHensel` form):
    (hβHensel : ∀ t, β (H := b.H) b.R t = BCIKS20.HenselNumerator.βHensel b.H x₀ b.R b.hHyp t)
    (hHensel : ∀ v₀ v₁ : F[X],
      γ x₀ b.R b.H b.hHyp = polyToPowerSeries𝕃 b.H
        ((Polynomial.map Polynomial.C v₀)
          + (Polynomial.C Polynomial.X) * (Polynomial.map Polynomial.C v₁)) →
      HPzBridge.HenselDatum (k := k) (deg := deg) (domain := domain) (δ := δ) u P v₀ v₁)
    (hdeg : ∀ v₀ v₁ : F[X],
      γ x₀ b.R b.H b.hHyp = polyToPowerSeries𝕃 b.H
        ((Polynomial.map Polynomial.C v₀)
          + (Polynomial.C Polynomial.X) * (Polynomial.map Polynomial.C v₁)) →
      v₀.natDegree < k + 1 ∧ v₁.natDegree < k + 1) :
    Section5StrictDataFinOn (k := k) (deg := deg) (domain := domain) (δ := δ) u P :=
  Section5StrictDataFinOn.ofProducersOn b (BcoeffSigned b.H x₀ b.R) matchingSet rootOn Ppoly
    hrep hdegX mpPointOn
    (GenuineMonicCapstone.hcardFin_of_graded_signed x₀ b.R b.H b.hHyp b.hD b.hH hmonic hd2
      hdHD hD_Rx0 hR (gradedConcreteFin_of_disc hdisc hcover hbig))
    hsubst
    (fun t => (hβHensel t).trans
      (betaRec_BcoeffSigned_eq_βHensel x₀ b.R b.hHyp t).symm)
    hHensel hdeg

/-- **THE CAPSTONE (#304): the satisfiable bundle from the canonical per-place series**
(monic case, GS-handshake shape).  Every assembled supplier is wired:

* `mpFinOn` ← `mpFinOn_of_localSeries_dvd` (canonical local series; `hαβ` PROVEN by
  `coeff_localSeries_mul`; separability from GS squarefreeness; `haP_coeff` by truncation);
* `hcardFin` ← `hcardFin_of_graded_signed` ∘ `gradedConcreteFin_of_disc` (budgets PROVEN);
* `htailDeg`/`hγ`/`hPz` ← `htailDeg_field`/`hγ_field_of_betaEq`/`hPz_of_henselDatum`.

The remaining hypotheses are exactly the honest external research surface of #304 (see the
trailing docnote). -/
noncomputable def Section5StrictDataFinOn.ofProducersOn_localSeries_genuineMonic {k deg : ℕ}
    {domain : ι ↪ F} {δ : ℝ≥0} {u : WordStack F (Fin (k + 1)) ι} {P : F → Polynomial F}
    {x₀ : F} (b : GSFactorData.Bundle (F := F) x₀)
    [_inst_hIrr : Fact (Irreducible b.H)] [_inst_hPos : Fact (0 < b.H.natDegree)]
    (matchingSet : Finset F)
    (rootOn : ∀ z ∈ matchingSet, rationalRoot (H_tilde' b.H) z)
    (Ppoly : F[X][Y])
    (hmonic : b.H.Monic) (hξ : ξ x₀ b.R b.H b.hHyp ≠ 0)
    (hrep : polyToPowerSeries𝕃 b.H Ppoly = γ x₀ b.R b.H b.hHyp)
    (hdegX : Polynomial.Bivariate.degreeX Ppoly ≤ 1)
    -- per-place §5 geometry (GS side):
    (hx : ∀ z (hz : z ∈ matchingSet), (π_z z (rootOn z hz)) (ξ x₀ b.R b.H b.hHyp) ≠ 0)
    (Pz : F → Polynomial F)
    (hPdeg : ∀ z ∈ matchingSet, (Pz z).natDegree < k)
    (hdvd : ∀ z (hz : z ∈ matchingSet),
      (Polynomial.X - Polynomial.C ((Pz z : PowerSeries F))) ∣
        ((b.R.map (coeffHom_loc x₀ b.hHyp)).map
          (PowerSeries.map (π_hat_z b.hHyp z (rootOn z hz) (hx z hz)))))
    (haP_cong : ∀ z (hz : z ∈ matchingSet),
      (Pz z : PowerSeries F) - PowerSeries.C ((π_z z (rootOn z hz))
          (BCIKS20.HenselNumerator.βHensel b.H x₀ b.R b.hHyp 0))
        ∈ Ideal.span {(PowerSeries.X : PowerSeries F)})
    (hsepR : b.R.Separable)
    -- graded budget side conditions + §6 discriminant counting:
    (hd2 : 2 ≤ Bivariate.natDegreeY b.R) (hdHD : b.H.natDegree ≤ b.D)
    (hD_Rx0 : b.D ≥ Bivariate.totalDegree (Bivariate.evalX (Polynomial.C x₀) b.R))
    (hR : ∀ j, Bivariate.degreeX (b.R.coeff j) ≤ b.D - j)
    {disc : F[X]} (hdisc : disc ≠ 0)
    (hcover : ∀ z : F, disc.eval z ≠ 0 → z ∈ matchingSet)
    (hbig : gradedCardBudget (Bivariate.natDegreeY b.R) b.D b.H.natDegree Ppoly.natDegree
        + disc.natDegree < Fintype.card F)
    -- series-level identifications:
    (hsubst : PowerSeries.HasSubst (Claim59Conditional.shiftSeries x₀ b.H))
    (hβHensel : ∀ t, β (H := b.H) b.R t = BCIKS20.HenselNumerator.βHensel b.H x₀ b.R b.hHyp t)
    (hHensel : ∀ v₀ v₁ : F[X],
      γ x₀ b.R b.H b.hHyp = polyToPowerSeries𝕃 b.H
        ((Polynomial.map Polynomial.C v₀)
          + (Polynomial.C Polynomial.X) * (Polynomial.map Polynomial.C v₁)) →
      HPzBridge.HenselDatum (k := k) (deg := deg) (domain := domain) (δ := δ) u P v₀ v₁)
    (hdeg : ∀ v₀ v₁ : F[X],
      γ x₀ b.R b.H b.hHyp = polyToPowerSeries𝕃 b.H
        ((Polynomial.map Polynomial.C v₀)
          + (Polynomial.C Polynomial.X) * (Polynomial.map Polynomial.C v₁)) →
      v₀.natDegree < k + 1 ∧ v₁.natDegree < k + 1) :
    Section5StrictDataFinOn (k := k) (deg := deg) (domain := domain) (δ := δ) u P :=
  Section5StrictDataFinOn.ofProducersOn_gradedSigned b matchingSet rootOn Ppoly hmonic
    hrep hdegX
    (mpFinOn_of_localSeries_dvd b.hHyp hξ hmonic.leadingCoeff rootOn hx Pz hPdeg hdvd
      haP_cong hsepR)
    hd2 hdHD hD_Rx0 hR hdisc hcover hbig hsubst hβHensel hHensel hdeg

/-- **The chain fires end-to-end**: from the capstone producers, the root-free `hcoeffPoly`
existential (the front doors' only consumption of the bundle) follows. -/
theorem hcoeffPoly_witness_of_producersOn_localSeries_genuineMonic {k deg : ℕ}
    {domain : ι ↪ F} {δ : ℝ≥0} {u : WordStack F (Fin (k + 1)) ι} {P : F → Polynomial F}
    {x₀ : F} (b : GSFactorData.Bundle (F := F) x₀)
    [_inst_hIrr : Fact (Irreducible b.H)] [_inst_hPos : Fact (0 < b.H.natDegree)]
    (matchingSet : Finset F)
    (rootOn : ∀ z ∈ matchingSet, rationalRoot (H_tilde' b.H) z)
    (Ppoly : F[X][Y])
    (hmonic : b.H.Monic) (hξ : ξ x₀ b.R b.H b.hHyp ≠ 0)
    (hrep : polyToPowerSeries𝕃 b.H Ppoly = γ x₀ b.R b.H b.hHyp)
    (hdegX : Polynomial.Bivariate.degreeX Ppoly ≤ 1)
    (hx : ∀ z (hz : z ∈ matchingSet), (π_z z (rootOn z hz)) (ξ x₀ b.R b.H b.hHyp) ≠ 0)
    (Pz : F → Polynomial F)
    (hPdeg : ∀ z ∈ matchingSet, (Pz z).natDegree < k)
    (hdvd : ∀ z (hz : z ∈ matchingSet),
      (Polynomial.X - Polynomial.C ((Pz z : PowerSeries F))) ∣
        ((b.R.map (coeffHom_loc x₀ b.hHyp)).map
          (PowerSeries.map (π_hat_z b.hHyp z (rootOn z hz) (hx z hz)))))
    (haP_cong : ∀ z (hz : z ∈ matchingSet),
      (Pz z : PowerSeries F) - PowerSeries.C ((π_z z (rootOn z hz))
          (BCIKS20.HenselNumerator.βHensel b.H x₀ b.R b.hHyp 0))
        ∈ Ideal.span {(PowerSeries.X : PowerSeries F)})
    (hsepR : b.R.Separable)
    (hd2 : 2 ≤ Bivariate.natDegreeY b.R) (hdHD : b.H.natDegree ≤ b.D)
    (hD_Rx0 : b.D ≥ Bivariate.totalDegree (Bivariate.evalX (Polynomial.C x₀) b.R))
    (hR : ∀ j, Bivariate.degreeX (b.R.coeff j) ≤ b.D - j)
    {disc : F[X]} (hdisc : disc ≠ 0)
    (hcover : ∀ z : F, disc.eval z ≠ 0 → z ∈ matchingSet)
    (hbig : gradedCardBudget (Bivariate.natDegreeY b.R) b.D b.H.natDegree Ppoly.natDegree
        + disc.natDegree < Fintype.card F)
    (hsubst : PowerSeries.HasSubst (Claim59Conditional.shiftSeries x₀ b.H))
    (hβHensel : ∀ t, β (H := b.H) b.R t = BCIKS20.HenselNumerator.βHensel b.H x₀ b.R b.hHyp t)
    (hHensel : ∀ v₀ v₁ : F[X],
      γ x₀ b.R b.H b.hHyp = polyToPowerSeries𝕃 b.H
        ((Polynomial.map Polynomial.C v₀)
          + (Polynomial.C Polynomial.X) * (Polynomial.map Polynomial.C v₁)) →
      HPzBridge.HenselDatum (k := k) (deg := deg) (domain := domain) (δ := δ) u P v₀ v₁)
    (hdeg : ∀ v₀ v₁ : F[X],
      γ x₀ b.R b.H b.hHyp = polyToPowerSeries𝕃 b.H
        ((Polynomial.map Polynomial.C v₀)
          + (Polynomial.C Polynomial.X) * (Polynomial.map Polynomial.C v₁)) →
      v₀.natDegree < k + 1 ∧ v₁.natDegree < k + 1) :
    ∃ B : ℕ → Polynomial F,
      (∀ j < deg, (B j).natDegree < k + 1) ∧
        ∀ z ∈ RS_goodCoeffsCurve (k := k) (deg := deg) (domain := domain) u δ,
          ∀ j < deg, (P z).coeff j = (B j).eval z :=
  hcoeffPoly_witness_of_section5DataFinOn
    (Section5StrictDataFinOn.ofProducersOn_localSeries_genuineMonic b matchingSet rootOn Ppoly
      hmonic hξ hrep hdegX hx Pz hPdeg hdvd haP_cong hsepR hd2 hdHD hD_Rx0 hR hdisc hcover
      hbig hsubst hβHensel hHensel hdeg)

end ProducersOn

/-! ## The honest external-hypothesis surface (the remaining #304 research core)

After this assembly, constructing the satisfiable bundle for a monic GS factor requires
EXACTLY (everything else above is proven or constructed):

1. the GS-factor bundle `b` (supplied from the GS interpolant side by
   `GSFactorData.of_section5Inputs` under the documented §5 standing inputs) with
   `hmonic`, `hξ ≠ 0`, the paper grading `hd2`/`hdHD`/`hD_Rx0`/`hR`, and GS squarefreeness
   `hsepR`;
2. the membership-dependent root family `rootOn` + unit readings `hx` (the per-place split
   geometry of `H̃` on the matching set);
3. the per-place proximate-root data: the decoded polynomials `Pz` (`hPdeg`), the GS
   matching-factor divisibility `hdvd`, and the `t = 0` congruence `haP_cong` (the
   "P_z and the branch agree at the centre" normalization);
4. the §6 discriminant counting `disc`/`hdisc`/`hcover`/`hbig`;
5. the Prop-5.5 representative `Ppoly`/`hrep`/`hdegX` and the substitution validity `hsubst`;
6. the genuine numerator identification `hβHensel : β = βHensel` (the L13 content);
7. the §5 specialisation data `hHensel`/`hdeg` (per linear representative).

Items 2-3 are per-place GS geometry (partially supplied by `RationalRootSupply` /
`MatchingExtractor` / `HenselMatchingPolySupply` on their respective routes); items 5-7 are
the genuine series-level §5 research kernels. -/

/-! ## Axiom audit (Part 1 — the producer assembly) -/

#print axioms ArkLib.RootOn304.mpFinOn_of_localSeries
#print axioms ArkLib.RootOn304.mpFinOn_of_localSeries_dvd
#print axioms ArkLib.RootOn304.Section5StrictDataFinOn.ofProducersOn
#print axioms ArkLib.RootOn304.ofProducersOn_eq_ofTotal_producers
#print axioms ArkLib.RootOn304.Section5StrictDataFinOn.ofProducersOn_badSet
#print axioms ArkLib.RootOn304.Section5StrictDataFinOn.ofProducersOn_gradedSigned
#print axioms ArkLib.RootOn304.Section5StrictDataFinOn.ofProducersOn_localSeries_genuineMonic
#print axioms ArkLib.RootOn304.hcoeffPoly_witness_of_producersOn_localSeries_genuineMonic

end RootOn304

end ArkLib

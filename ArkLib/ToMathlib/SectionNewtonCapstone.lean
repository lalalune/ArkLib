/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.ToMathlib.SectionNewtonWindowSharp
import ArkLib.ToMathlib.SectionNewtonRecentre
import ArkLib.ToMathlib.CentreVanishingSupply
import ArkLib.ToMathlib.BranchCollapse

/-!
# The section-Newton capstone (#304): heavy factor + counted seeds ⟹ polynomial branch

The convergence brick (leg 1 of the share/cell route, made true by the fold data): per-place
divisibility of the decoded family into a (cell) factor, heavy-column seeds (leg 2's
`exists_matching_sets_of_decoded` output shape: `x₀ :=` a heavy column, `v :=` the
fold-section coordinate), a flat `Z`-budget (leg 3's shape), and the quadratic count
produce — with **no separability and no `Y`-linearity of the factor** —

* `seed_root_of_matching` — the seed root `(slice).eval v = 0` by counting: per-place centre
  vanishing (`centre_vanishing_of_specialized_dvd` + the eval-eval swap) at more places than
  the slice-value degree;
* `window_vanish_capstone` — the sharp Claim-5.8 window at `gsNewtonData`, every input
  discharged from the named data;
* `exists_polynomial_branch` — **THE CAPSTONE**: the Newton branch of the factor at the
  heavy column is (the coercion of) a polynomial of degree `< k` over
  `Localization.Away ξ̄`.  The bare form of leg 1 is false (`Y² − Z` catches every square
  with no section); the fold data — decoded polynomials of degree `< k` seeding one
  fold-section coordinate — is exactly what makes it true.

## References
* [BCIKS20] Ben-Sasson, Carmon, Ishai, Kopparty, Saraf, *Proximity Gaps for Reed–Solomon
  Codes*, §5 (Prop. 5.5, Claim 5.8), Appendix A.
-/

set_option linter.style.longLine false

namespace ArkLib.SectionNewtonCleared

open PowerSeries ProximityPrize.HenselSeriesCoeff

variable {F : Type} [Field F]

/-! ## Slice degree bookkeeping -/

/-- The slice coefficients keep the flat `Z`-budget. -/
theorem slice_coeff_natDegree_le {x₀ : F} {R : Polynomial (Polynomial (Polynomial F))}
    {DZ : ℕ} (hRflat : ∀ i m, ((R.coeff i).coeff m).natDegree ≤ DZ) (i : ℕ) :
    ((Polynomial.Bivariate.evalX (Polynomial.C x₀) R).coeff i).natDegree ≤ DZ := by
  rw [Polynomial.Bivariate.evalX_eq_map, Polynomial.coeff_map, Polynomial.coe_evalRingHom]
  rw [Polynomial.eval_eq_sum_range]
  apply Polynomial.natDegree_sum_le_of_forall_le
  intro m _
  calc ((R.coeff i).coeff m * (Polynomial.C x₀ : Polynomial F) ^ m).natDegree
      ≤ ((R.coeff i).coeff m).natDegree
        + ((Polynomial.C x₀ : Polynomial F) ^ m).natDegree := Polynomial.natDegree_mul_le
    _ ≤ DZ + 0 := by
        refine Nat.add_le_add (hRflat i m) ?_
        calc ((Polynomial.C x₀ : Polynomial F) ^ m).natDegree
            ≤ m * (Polynomial.C x₀ : Polynomial F).natDegree := Polynomial.natDegree_pow_le
          _ = 0 := by rw [Polynomial.natDegree_C, Nat.mul_zero]
    _ = DZ := Nat.add_zero DZ

/-- The slice-value degree budget: `deg_Z ((slice).eval v) ≤ DZ + d·dv`. -/
theorem sliceValue_natDegree_le {x₀ : F} {R : Polynomial (Polynomial (Polynomial F))}
    {DZ : ℕ} (hRflat : ∀ i m, ((R.coeff i).coeff m).natDegree ≤ DZ) (v : Polynomial F) :
    ((Polynomial.Bivariate.evalX (Polynomial.C x₀) R).eval v).natDegree
      ≤ DZ + R.natDegree * v.natDegree := by
  set Q := Polynomial.Bivariate.evalX (Polynomial.C x₀) R with hQ
  have hQdeg : Q.natDegree ≤ R.natDegree := by
    rw [hQ, Polynomial.Bivariate.evalX_eq_map]
    exact Polynomial.natDegree_map_le
  rw [Polynomial.eval_eq_sum_range]
  apply Polynomial.natDegree_sum_le_of_forall_le
  intro i hi
  have hile : i ≤ R.natDegree := by
    have := Finset.mem_range.mp hi
    omega
  calc (Q.coeff i * v ^ i).natDegree
      ≤ (Q.coeff i).natDegree + (v ^ i).natDegree := Polynomial.natDegree_mul_le
    _ ≤ DZ + i * v.natDegree := by
        refine Nat.add_le_add (slice_coeff_natDegree_le hRflat i) ?_
        exact Polynomial.natDegree_pow_le
    _ ≤ DZ + R.natDegree * v.natDegree :=
        Nat.add_le_add_left (Nat.mul_le_mul_right _ hile) _

/-! ## The seed root, by counting -/

/-- **The seed root** `(slice).eval v = 0`: per-place divisibility reads as centre vanishing
at every matched place, and the count beats the slice-value degree. -/
theorem seed_root_of_matching {x₀ : F} {R : Polynomial (Polynomial (Polynomial F))}
    {DZ : ℕ} (hRflat : ∀ i m, ((R.coeff i).coeff m).natDegree ≤ DZ) {v : Polynomial F}
    {P : F → Polynomial F} (M : Finset F)
    (hcard : DZ + R.natDegree * v.natDegree < M.card)
    (hdvdM : ∀ z ∈ M, Polynomial.X - Polynomial.C (P z) ∣
      R.map (Polynomial.mapRingHom (Polynomial.evalRingHom z)))
    (hval : ∀ z ∈ M, (P z).eval x₀ = v.eval z) :
    (Polynomial.Bivariate.evalX (Polynomial.C x₀) R).eval v = 0 := by
  classical
  set q : Polynomial F := (Polynomial.Bivariate.evalX (Polynomial.C x₀) R).eval v with hq
  by_contra hq0
  have hroots : M.card ≤ q.natDegree := by
    have hsub : M ⊆ q.roots.toFinset := by
      intro z hz
      rw [Multiset.mem_toFinset, Polynomial.mem_roots hq0]
      show q.eval z = 0
      rw [hq, ArkLib.BranchCollapse.eval_eval_eq_evalEval z v _, ← hval z hz]
      exact CentreVanishingSupply.centre_vanishing_of_specialized_dvd
        (hdvdM z hz) x₀
    calc M.card ≤ q.roots.toFinset.card := Finset.card_le_card hsub
      _ ≤ Multiset.card q.roots := q.roots.toFinset_card_le
      _ ≤ q.natDegree := q.card_roots'
  have hbound := sliceValue_natDegree_le hRflat v (x₀ := x₀) (R := R)
  rw [← hq] at hbound
  omega

/-! ## The capstone -/

variable (ξ : Polynomial F)

local notation "𝔞" => algebraMap (Polynomial F) (Localization.Away ξ)

/-- The Newton seed root fact over the localization, from the seed root by counting. -/
theorem hc0_capstone {x₀ : F} {R : Polynomial (Polynomial (Polynomial F))}
    {v : Polynomial F}
    (hseedroot : (Polynomial.Bivariate.evalX (Polynomial.C x₀) R).eval v = 0) :
    Polynomial.eval (𝔞 v) (Q₀ (gsNewtonData ξ x₀ R)) = 0 := by
  rw [Q₀_gsNewtonData]
  have h : Polynomial.eval (𝔞 v)
      ((R.map (Polynomial.evalRingHom (Polynomial.C x₀))).map 𝔞)
      = 𝔞 ((R.map (Polynomial.evalRingHom (Polynomial.C x₀))).eval v) := by
    rw [Polynomial.eval_map, Polynomial.eval₂_hom]
  rw [h, show R.map (Polynomial.evalRingHom (Polynomial.C x₀))
      = Polynomial.Bivariate.evalX (Polynomial.C x₀) R from
    (Polynomial.Bivariate.evalX_eq_map _ _).symm, hseedroot, map_zero]

/-- **The window vanish at the heavy factor**, every input discharged from the named data:
`R` the (cell) factor with the flat `Z`-budget, `ξ := sliceResponse x₀ R v ≠ 0`, the
per-place divisibility, the heavy-column seeds, the decoded degree bound, and the quadratic
count. -/
theorem window_vanish_capstone {x₀ : F} {R : Polynomial (Polynomial (Polynomial F))}
    {v : Polynomial F} {DZ : ℕ}
    (hξ : ξ = sliceResponse x₀ R v) (hξ0 : ξ ≠ 0)
    (hRflat : ∀ i m, ((R.coeff i).coeff m).natDegree ≤ DZ)
    {k T : ℕ} {P : F → Polynomial F} (M : Finset F)
    (hcard : sharpBudget (gsNewtonData ξ x₀ R).natDegree v.natDegree DZ ξ.natDegree T
      + ξ.natDegree < M.card)
    (hdvdM : ∀ z ∈ M, Polynomial.X - Polynomial.C (P z) ∣
      R.map (Polynomial.mapRingHom (Polynomial.evalRingHom z)))
    (hval : ∀ z ∈ M, (P z).eval x₀ = v.eval z)
    (hdeg : ∀ z ∈ M, (P z).natDegree < k) :
    ∀ t, k ≤ t → t ≤ T → coeff t (γ (gsNewtonData ξ x₀ R) (𝔞 v)) = 0 := by
  refine window_vanish_of_decoded_roots_sharp ξ (gsNewtonData ξ x₀ R) v hξ0
    (fun i j => exists_coeff_gsNewtonData ξ x₀ hRflat i j)
    (by rw [eval_derivative_Q₀_gsNewtonData, hξ]) M hcard
    (fun z => Polynomial.taylor x₀ (P z)) ?_ ?_ ?_
  · -- decoded degree, preserved by the recentring
    intro z hz
    rw [Polynomial.natDegree_taylor]
    exact hdeg z hz
  · -- the per-place root, through the place commutation
    intro z hz hzξ
    have h := eval_taylorCoe_gsNewtonData_specialized ξ x₀ hzξ (hdvdM z hz)
    rwa [taylorCoeHom_eq_coe_taylor] at h
  · -- the seed: the recentred base coefficient is the centre value
    intro z hz
    show (Polynomial.taylor x₀ (P z)).coeff 0 = v.eval z
    rw [Polynomial.taylor_coeff_zero]
    exact hval z hz

/-- **THE CAPSTONE (leg 1, made true by the fold data)**: the Newton branch of the heavy
factor at the heavy column is (the coercion of) a **polynomial of degree `< k`** over the
localization — from per-place divisibility, heavy-column seeds, the flat `Z`-budget, an
`X`-degree budget, and the quadratic count.  No separability, no `Y`-linearity. -/
theorem exists_polynomial_branch {x₀ : F} {R : Polynomial (Polynomial (Polynomial F))}
    {v : Polynomial F} {DZ DX : ℕ}
    (hξ : ξ = sliceResponse x₀ R v) (hξ0 : ξ ≠ 0)
    (hRflat : ∀ i m, ((R.coeff i).coeff m).natDegree ≤ DZ)
    (hRX : ∀ i, (R.coeff i).natDegree ≤ DX)
    {k : ℕ} (hk : 0 < k) {P : F → Polynomial F} (M : Finset F)
    (hcard : sharpBudget (gsNewtonData ξ x₀ R).natDegree v.natDegree DZ ξ.natDegree
        (DX + (gsNewtonData ξ x₀ R).natDegree * (k - 1))
      + ξ.natDegree < M.card)
    (hcard0 : DZ + R.natDegree * v.natDegree < M.card)
    (hdvdM : ∀ z ∈ M, Polynomial.X - Polynomial.C (P z) ∣
      R.map (Polynomial.mapRingHom (Polynomial.evalRingHom z)))
    (hval : ∀ z ∈ M, (P z).eval x₀ = v.eval z)
    (hdeg : ∀ z ∈ M, (P z).natDegree < k) :
    ∃ γp : Polynomial (Localization.Away ξ),
      (γp : PowerSeries (Localization.Away ξ)) = γ (gsNewtonData ξ x₀ R) (𝔞 v) ∧
      γp.natDegree < k := by
  -- the Newton seed facts
  have hc0 : Polynomial.eval (𝔞 v) (Q₀ (gsNewtonData ξ x₀ R)) = 0 :=
    hc0_capstone ξ (seed_root_of_matching hRflat M hcard0 hdvdM hval)
  have hu : IsUnit (Polynomial.eval (𝔞 v)
      (Polynomial.derivative (Q₀ (gsNewtonData ξ x₀ R)))) := by
    rw [eval_derivative_Q₀_gsNewtonData, ← hξ]
    exact isUnit_xi ξ
  -- the X-truncation of the Newton data, through the recentring
  have hQX : ∀ i, ∀ a, DX < a →
      PowerSeries.coeff a ((gsNewtonData ξ x₀ R).coeff i) = 0 := by
    intro i a ha
    rw [gsNewtonData, Polynomial.coeff_map, thetaHom]
    simp only [RingHom.coe_comp, Function.comp_apply, Polynomial.coe_mapRingHom,
      Polynomial.coeToPowerSeries.ringHom_apply]
    rw [Polynomial.coeff_coe, Polynomial.coeff_map]
    have hdeg' : (recentreHom x₀ (R.coeff i)).natDegree ≤ DX := by
      have heq : recentreHom x₀ (R.coeff i)
          = Polynomial.taylor (Polynomial.C x₀) (R.coeff i) := by
        rw [Polynomial.taylor_apply, Polynomial.comp]
        rfl
      rw [heq, Polynomial.natDegree_taylor]
      exact hRX i
    rw [Polynomial.coeff_eq_zero_of_natDegree_lt (lt_of_le_of_lt hdeg' ha), map_zero]
  -- the window
  have hwindow := window_vanish_capstone ξ hξ hξ0 hRflat M hcard hdvdM hval hdeg
  -- the tail closes the polynomial
  exact ArkLib.SectionNewtonGamma.exists_polynomial_gamma_of_window
    (gsNewtonData ξ x₀ R) (𝔞 v) hc0 hu hk hQX hwindow

end ArkLib.SectionNewtonCleared

/-! ## Axiom audit — every declaration must rest only on
`[propext, Classical.choice, Quot.sound]`, with no `sorry`/`admit`/`axiom`/`native_decide`. -/
#print axioms ArkLib.SectionNewtonCleared.slice_coeff_natDegree_le
#print axioms ArkLib.SectionNewtonCleared.sliceValue_natDegree_le
#print axioms ArkLib.SectionNewtonCleared.seed_root_of_matching
#print axioms ArkLib.SectionNewtonCleared.hc0_capstone
#print axioms ArkLib.SectionNewtonCleared.window_vanish_capstone
#print axioms ArkLib.SectionNewtonCleared.exists_polynomial_branch

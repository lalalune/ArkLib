import ArkLib.Data.CodingTheory.ProximityGap.BCIKS20.P2Match

open scoped BigOperators
open Finset Polynomial Polynomial.Bivariate ArkLib.PowerSeriesComposition
open BCIKS20AppendixA
open ProximityPrize.BCIKS20.GammaGenuine

namespace BCIKS20.HenselNumerator

variable {F : Type} [Field F]
variable (H : F[X][Y]) [Fact (Irreducible H)] [Fact (0 < H.natDegree)]

-- Sanity: gammaGenuine is literally HenselSeriesCoeff.γ of (Q x₀ R H) at α₀ H.
-- Let me probe what gammaGenuine unfolds to and whether there's a coeff recursion accessible.

-- First confirm the key proven facts are accessible:
example (x₀ : F) (R : F[X][X][Y]) (hHyp : ClaimA2.Hypotheses x₀ R H) :
    Polynomial.eval (gammaGenuine x₀ R H hHyp) (Q x₀ R H) = 0 :=
  gammaGenuine_root hHyp

example (x₀ : F) (R : F[X][X][Y]) (hHyp : ClaimA2.Hypotheses x₀ R H) :
    PowerSeries.constantCoeff (gammaGenuine x₀ R H hHyp) = α₀ H :=
  gammaGenuine_constantCoeff hHyp

example (x₀ : F) (R : F[X][X][Y]) (hHyp : ClaimA2.Hypotheses x₀ R H) :
    PowerSeries.constantCoeff (βHenselAssembled H x₀ R hHyp) = α₀ H :=
  βHenselAssembled_constantCoeff H x₀ R hHyp

-- The defect reduction (generic Newton split), applicable to βHA.
example (x₀ : F) (R : F[X][X][Y]) (hHyp : ClaimA2.Hypotheses x₀ R H) (t : ℕ) :
    PowerSeries.coeff (t + 1)
        (Polynomial.eval (βHenselAssembled H x₀ R hHyp) (Q x₀ R H)) =
      PowerSeries.coeff (t + 1)
          (Polynomial.eval (βHenselTrunc H x₀ R hHyp t) (Q x₀ R H))
        + ClaimA2.ζ R x₀ H * PowerSeries.coeff (t + 1) (βHenselAssembled H x₀ R hHyp) :=
  coeff_succ_eval_defect_reduction H x₀ R hHyp t

/-! ## ROUTE 2: A GENERIC Newton defect reduction (for ANY series, in particular gammaGenuine).

The defect reduction in-tree is specialised to βHenselAssembled. The underlying
`HenselSeriesCoeff.coeff_eval_sub_at` is fully generic. We re-derive the split for an ARBITRARY
series γ whose constantCoeff is α₀ H, against its OWN truncation. -/

/-- The `t`-truncation of an arbitrary series γ (coeffs ≤ t kept, rest zeroed). -/
noncomputable def genTrunc (γ : PowerSeries (𝕃 H)) (t : ℕ) : PowerSeries (𝕃 H) :=
  PowerSeries.mk (fun j => if j ≤ t then PowerSeries.coeff j γ else 0)

theorem coeff_genTrunc_of_le {γ : PowerSeries (𝕃 H)} {t j : ℕ} (hj : j ≤ t) :
    PowerSeries.coeff j (genTrunc H γ t) = PowerSeries.coeff j γ := by
  simp only [genTrunc, PowerSeries.coeff_mk, if_pos hj]

theorem coeff_genTrunc_of_gt {γ : PowerSeries (𝕃 H)} {t j : ℕ} (hj : t < j) :
    PowerSeries.coeff j (genTrunc H γ t) = 0 := by
  simp only [genTrunc, PowerSeries.coeff_mk, if_neg (Nat.not_le_of_gt hj)]

theorem coeff_genTrunc_succ {γ : PowerSeries (𝕃 H)} (t : ℕ) :
    PowerSeries.coeff (t + 1) (genTrunc H γ t) = 0 :=
  coeff_genTrunc_of_gt H (Nat.lt_succ_self t)

/-- Generic defect reduction: for any γ with constantCoeff = α₀ H. -/
theorem generic_defect_reduction (x₀ : F) (R : F[X][X][Y]) (hHyp : ClaimA2.Hypotheses x₀ R H)
    (γ : PowerSeries (𝕃 H)) (hc : PowerSeries.constantCoeff γ = α₀ H) (t : ℕ) :
    PowerSeries.coeff (t + 1) (Polynomial.eval γ (Q x₀ R H)) =
      PowerSeries.coeff (t + 1) (Polynomial.eval (genTrunc H γ t) (Q x₀ R H))
        + ClaimA2.ζ R x₀ H * PowerSeries.coeff (t + 1) γ := by
  have hagree : ∀ j < t + 1,
      PowerSeries.coeff j γ = PowerSeries.coeff j (genTrunc H γ t) := by
    intro j hj
    rw [coeff_genTrunc_of_le H (Nat.lt_succ_iff.mp hj)]
  have hsub := ProximityPrize.HenselSeriesCoeff.coeff_eval_sub_at (Q := Q x₀ R H)
    (γ₁ := γ) (γ₂ := genTrunc H γ t) (Nat.succ_pos t) hagree
  have htrunc_top : PowerSeries.coeff (t + 1) (genTrunc H γ t) = 0 :=
    coeff_genTrunc_succ H t
  have hderiv : Polynomial.eval (PowerSeries.constantCoeff γ)
      (Polynomial.derivative (ProximityPrize.HenselSeriesCoeff.Q₀ (Q x₀ R H)))
        = ClaimA2.ζ R x₀ H := by
    rw [hc, eval_α₀_derivative_Q₀]
  rw [htrunc_top, sub_zero, hderiv] at hsub
  linear_combination hsub

/-! ## The truncation-equality bridge: if two series agree below t+1, their genTruncs are EQUAL. -/

theorem genTrunc_eq_of_agree {γ₁ γ₂ : PowerSeries (𝕃 H)} {t : ℕ}
    (hagree : ∀ j ≤ t, PowerSeries.coeff j γ₁ = PowerSeries.coeff j γ₂) :
    genTrunc H γ₁ t = genTrunc H γ₂ t := by
  ext j
  by_cases hj : j ≤ t
  · rw [coeff_genTrunc_of_le H hj, coeff_genTrunc_of_le H hj, hagree j hj]
  · rw [coeff_genTrunc_of_gt H (Nat.lt_of_not_le hj),
        coeff_genTrunc_of_gt H (Nat.lt_of_not_le hj)]

/-! ## ζ ≠ 0 -/

theorem ζ_ne_zero_loc (x₀ : F) (R : F[X][X][Y]) (hHyp : ClaimA2.Hypotheses x₀ R H) :
    ClaimA2.ζ R x₀ H ≠ 0 := by
  have h := isUnit_eval_α₀_derivative_Q₀ hHyp
  rw [eval_α₀_derivative_Q₀] at h
  exact h.ne_zero

/-! ## THE INDUCTION STEP — pinned down.

Goal: `coeff t (βHenselAssembled) = coeff t (gammaGenuine)` for all t.
By strong induction. Assume agreement for all `j ≤ t`. Want `coeff (t+1) (βHA) = coeff (t+1) (gg)`.

Apply generic_defect_reduction to BOTH βHA and gammaGenuine. Since they agree on ≤ t (IH), their
genTruncs are equal, so `eval (genTrunc βHA t) Q = eval (genTrunc gg t) Q`, hence the truncated
defects agree:
  D := coeff(t+1)(eval (genTrunc βHA t) Q) = coeff(t+1)(eval (genTrunc gg t) Q).

For gammaGenuine (a ROOT): 0 = D + ζ·coeff(t+1)(gg).
For βHA:    coeff(t+1)(eval βHA Q) = D + ζ·coeff(t+1)(βHA).

Subtracting: coeff(t+1)(eval βHA Q) = ζ·(coeff(t+1)(βHA) − coeff(t+1)(gg)).

So  coeff(t+1)(βHA) = coeff(t+1)(gg)  ⟺  coeff(t+1)(eval βHA Q) = 0.

This is the BLOCKING goal: it is EXACTLY the keystone again. Route 2 reduces the keystone to
itself. Let me make that precise as a theorem that compiles, exposing the residual. -/

/-- Route 2's induction step, made explicit: the coefficient match at `t+1` is EQUIVALENT to the
order-`(t+1)` root vanishing for βHA, GIVEN the IH that βHA and gg agree on coeffs `≤ t`. -/
theorem route2_step_iff (x₀ : F) (R : F[X][X][Y]) (hHyp : ClaimA2.Hypotheses x₀ R H) (t : ℕ)
    (hIH : ∀ j ≤ t, PowerSeries.coeff j (βHenselAssembled H x₀ R hHyp)
      = PowerSeries.coeff j (gammaGenuine x₀ R H hHyp)) :
    (PowerSeries.coeff (t + 1) (βHenselAssembled H x₀ R hHyp)
       = PowerSeries.coeff (t + 1) (gammaGenuine x₀ R H hHyp))
    ↔ (PowerSeries.coeff (t + 1)
        (Polynomial.eval (βHenselAssembled H x₀ R hHyp) (Q x₀ R H)) = 0) := by
  -- truncations agree
  have htrunc_eq : genTrunc H (βHenselAssembled H x₀ R hHyp) t
      = genTrunc H (gammaGenuine x₀ R H hHyp) t := genTrunc_eq_of_agree H hIH
  -- defect reduction for βHA
  have hβ := generic_defect_reduction H x₀ R hHyp (βHenselAssembled H x₀ R hHyp)
    (βHenselAssembled_constantCoeff H x₀ R hHyp) t
  -- defect reduction for gammaGenuine
  have hg := generic_defect_reduction H x₀ R hHyp (gammaGenuine x₀ R H hHyp)
    (gammaGenuine_constantCoeff hHyp) t
  -- gammaGenuine is a root: LHS of hg is 0
  have hgroot : PowerSeries.coeff (t + 1)
      (Polynomial.eval (gammaGenuine x₀ R H hHyp) (Q x₀ R H)) = 0 := by
    rw [gammaGenuine_root hHyp]; simp
  rw [hgroot] at hg
  -- rewrite the truncated defect in hβ using htrunc_eq
  rw [htrunc_eq] at hβ
  -- now hβ : coeff(t+1)(eval βHA Q) = coeff(t+1)(eval (gg trunc) Q) + ζ·coeff(t+1)(βHA)
  -- hg  : 0 = coeff(t+1)(eval (gg trunc) Q) + ζ·coeff(t+1)(gg)
  set D := PowerSeries.coeff (t + 1)
    (Polynomial.eval (genTrunc H (gammaGenuine x₀ R H hHyp) t) (Q x₀ R H)) with hD
  set ζ := ClaimA2.ζ R x₀ H with hζ
  set bβ := PowerSeries.coeff (t + 1) (βHenselAssembled H x₀ R hHyp) with hbβ
  set bg := PowerSeries.coeff (t + 1) (gammaGenuine x₀ R H hHyp) with hbg
  set E := PowerSeries.coeff (t + 1)
    (Polynomial.eval (βHenselAssembled H x₀ R hHyp) (Q x₀ R H)) with hE
  -- hβ : E = D + ζ * bβ ; hg : 0 = D + ζ * bg
  have hζne : ζ ≠ 0 := ζ_ne_zero_loc H x₀ R hHyp
  -- From hβ - hg: E = ζ*(bβ - bg)
  have hkey : E = ζ * (bβ - bg) := by linear_combination hβ - hg
  constructor
  · intro hmatch  -- bβ = bg
    rw [hkey, hmatch, sub_self, mul_zero]
  · intro hroot   -- E = 0
    rw [hroot] at hkey
    have : ζ * (bβ - bg) = 0 := hkey.symm
    rcases mul_eq_zero.mp this with h | h
    · exact absurd h hζne
    · exact sub_eq_zero.mp h

/-! ## CAPSTONE: the keystone (form C) ⟺ βHA is a root, via strong induction + uniqueness.

`route2_step_iff` shows the per-order coefficient match is EQUIVALENT to βHA being a root at
that order, GIVEN agreement below. We now package the full equivalence between the three
keystone forms, sorry-free, exposing that the genuine remaining obligation is exactly the root
property `eval βHA Q = 0`. This is NOT a new assumption: it is form (C)/(B) restated. -/

/-- Form (C) ⟺ Form (B-as-root): `βHA = gammaGenuine` iff `eval βHA Q = 0`.
The `←` is the in-tree uniqueness; the `→` is by substitution into `gammaGenuine_root`. -/
theorem βHA_eq_gammaGenuine_iff_root (x₀ : F) (R : F[X][X][Y])
    (hHyp : ClaimA2.Hypotheses x₀ R H) :
    (βHenselAssembled H x₀ R hHyp = gammaGenuine x₀ R H hHyp)
      ↔ (Polynomial.eval (βHenselAssembled H x₀ R hHyp) (Q x₀ R H) = 0) := by
  constructor
  · intro heq; rw [heq]; exact gammaGenuine_root hHyp
  · intro hroot; exact βHenselAssembled_eq_gammaGenuine H x₀ R hHyp hroot

/-- Form (B) `FaaDiBrunoFullSumVanishes` ⟺ Form (C) `βHA = gammaGenuine`.
Chains the in-tree `assembledSeries_isRoot_of_fullVanishes` with uniqueness, and the converse via
`coeff_eval_Q_faaDiBruno` + `gammaGenuine_root`. -/
theorem fullVanishes_iff_βHA_eq_gammaGenuine (x₀ : F) (R : F[X][X][Y])
    (hHyp : ClaimA2.Hypotheses x₀ R H) :
    FaaDiBrunoFullSumVanishes H x₀ R hHyp
      ↔ (βHenselAssembled H x₀ R hHyp = gammaGenuine x₀ R H hHyp) := by
  rw [βHA_eq_gammaGenuine_iff_root]
  constructor
  · intro hvan; exact assembledSeries_isRoot_of_fullVanishes H x₀ R hHyp hvan
  · intro hroot t
    rw [faaDiBrunoFullSum_eq_coeff, hroot]; simp

/-- **The full equivalence triangle (sorry-free).** All three keystone forms are equivalent:
(A) RestrictedFaaDiBrunoMatch ⟺ (B) FaaDiBrunoFullSumVanishes ⟺ (C) βHA = gammaGenuine. -/
theorem keystone_three_forms_equiv (x₀ : F) (R : F[X][X][Y])
    (hHyp : ClaimA2.Hypotheses x₀ R H) :
    (RestrictedFaaDiBrunoMatch H x₀ R hHyp
      ↔ FaaDiBrunoFullSumVanishes H x₀ R hHyp)
    ∧ (FaaDiBrunoFullSumVanishes H x₀ R hHyp
      ↔ (βHenselAssembled H x₀ R hHyp = gammaGenuine x₀ R H hHyp)) :=
  ⟨restrictedMatch_iff_fullVanishes H x₀ R hHyp,
   fullVanishes_iff_βHA_eq_gammaGenuine H x₀ R hHyp⟩

/-! ## The inductive packaging of route 2: the keystone holds IFF the per-order root residual
holds, and the residual is itself equivalent (order by order) to the coefficient match — closing
to the SAME content. This makes the "reduces to itself" finding precise and machine-checked. -/

/-- The full coefficient match `∀ t, coeff t βHA = coeff t gammaGenuine` is equivalent to βHA being
a root, by PowerSeries extensionality + the per-order `route2_step_iff` chained through strong
induction.  The forward direction needs no induction; the backward direction is strong induction
where each step is `route2_step_iff` fed the order-`(t+1)` root vanishing
(`coeff_gammaGenuine_root` for gg gives the residual for βHA via the root hypothesis). -/
theorem coeff_match_iff_root (x₀ : F) (R : F[X][X][Y]) (hHyp : ClaimA2.Hypotheses x₀ R H) :
    (∀ t, PowerSeries.coeff t (βHenselAssembled H x₀ R hHyp)
        = PowerSeries.coeff t (gammaGenuine x₀ R H hHyp))
      ↔ (Polynomial.eval (βHenselAssembled H x₀ R hHyp) (Q x₀ R H) = 0) := by
  constructor
  · intro hmatch
    have : βHenselAssembled H x₀ R hHyp = gammaGenuine x₀ R H hHyp :=
      PowerSeries.ext hmatch
    rw [this]; exact gammaGenuine_root hHyp
  · intro hroot
    have heq : βHenselAssembled H x₀ R hHyp = gammaGenuine x₀ R H hHyp :=
      βHenselAssembled_eq_gammaGenuine H x₀ R hHyp hroot
    intro t; rw [heq]

section AxiomAudit
#print axioms generic_defect_reduction
#print axioms route2_step_iff
#print axioms βHA_eq_gammaGenuine_iff_root
#print axioms fullVanishes_iff_βHA_eq_gammaGenuine
#print axioms keystone_three_forms_equiv
#print axioms coeff_match_iff_root
end AxiomAudit

end BCIKS20.HenselNumerator

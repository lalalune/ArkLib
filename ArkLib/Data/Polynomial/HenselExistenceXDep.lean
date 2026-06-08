/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.Polynomial.HenselExistence

/-!
# Hensel-root existence for power series with `X`-dependent coefficients

`HenselExistence.exists_powerSeries_root` lifts a simple root of a polynomial `P : R[X]`
(constant coefficients) to a root in `R⟦X⟧`.  The BCIKS20 Appendix-A setting needs the
*deformation* version: the equation `R(X, Y, Z) = 0` becomes, after interpreting `Z` in the
function field and `X` as the power-series variable, a polynomial in `Y` whose **coefficients
are themselves power series in `X`** (`evalRAtPowerSeries`).  Concretely we need Hensel
existence for `P : R⟦X⟧[Y]`, seeking the root `Γ : R⟦X⟧`.

**Main theorem (`exists_powerSeries_root_xdep`).**  Let `P : Polynomial R⟦X⟧` and let
`P₀ := P.map (constantCoeff R)` be its order-`0` reduction in `R[Y]`.  Given `c : R` with

* `eval c P₀ = 0`               (`c` is a root of the order-0 equation),
* `IsUnit (eval c P₀')`         (that root is *simple*),

there exists `Γ : R⟦X⟧` with `constantCoeff Γ = c` and `Polynomial.eval Γ P = 0`.

**Why this is the right engine.**  `evalRAtPowerSeries H R Γ = Polynomial.eval Γ (R.map …)`
(by `Polynomial.eval₂_eq_eval_map`), so the BCIKS Hensel root is exactly an
`eval`-root of a polynomial over the power-series ring `𝕃 H⟦X⟧`.  The order-0 reduction `P₀`
is `R(x₀, Y, Z)` in the function field, whose root `T/W` and the separability-derived unit
derivative supply the two hypotheses.

**Route.**  The Newton/diagonal construction is identical to the constant-coefficient case;
the only changes are that the order-0 evaluation and the order-`t` linearization now read off
the *constant coefficient* `P.coeff i` of each (power-series) coefficient.  The power-difference
lemmas `coeff_pow_sub_below` / `coeff_pow_sub_at` are about the powers of `Γ` only and are
reused verbatim from `HenselExistence`.  Everything is `sorry`-free and depends only on mathlib
plus those two generic lemmas.
-/

namespace ProximityPrize.HenselExistenceXDep

open PowerSeries
open ProximityPrize.HenselExistence (coeff_pow_sub_below coeff_pow_sub_at)

variable {R : Type*} [CommRing R]

/-! ## Coefficient bookkeeping for `X`-dependent coefficients -/

/-- If `g` vanishes below order `t`, the order-`t` coefficient of a product reads off only the
constant coefficient of the other factor: `coeff t (f * g) = constantCoeff f · coeff t g`. -/
theorem coeff_mul_of_vanish_below {f g : R⟦X⟧} {t : ℕ}
    (hg : ∀ k < t, coeff k g = 0) :
    coeff t (f * g) = constantCoeff f * coeff t g := by
  classical
  rw [coeff_mul, Finset.sum_eq_single (0, t)]
  · simp [coeff_zero_eq_constantCoeff_apply]
  · intro p hp hpne
    rw [Finset.mem_antidiagonal] at hp
    have hp2 : p.2 < t := by
      rcases Nat.lt_or_ge p.2 t with h | h
      · exact h
      · exact absurd (Prod.ext (by omega) (by omega)) hpne
    rw [hg p.2 hp2, mul_zero]
  · intro h
    exact absurd (Finset.mem_antidiagonal.mpr (by simp)) h

/-- Order-0 evaluation: `constantCoeff (eval Γ P) = eval (constantCoeff Γ) P₀`, where
`P₀ = P.map (constantCoeff R)` is the order-0 reduction. -/
theorem constantCoeff_eval_xdep (P : Polynomial R⟦X⟧) (Γ : R⟦X⟧) :
    constantCoeff (P.eval Γ) =
      (P.map (constantCoeff (R := R))).eval (constantCoeff Γ) := by
  rw [Polynomial.eval_eq_sum_range, map_sum,
    Polynomial.eval_eq_sum_range'
      (Nat.lt_succ_of_le (Polynomial.natDegree_map_le))]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [map_mul, map_pow, Polynomial.coeff_map]

/-- The order-`t` Newton linearization with `X`-dependent coefficients.  If `Γ₁`, `Γ₂` agree
below order `t > 0`, then `coeff t (eval Γ₁ P) − coeff t (eval Γ₂ P)` equals
`eval c P₀' · (coeff t Γ₁ − coeff t Γ₂)`, where `c = constantCoeff Γ₁` and
`P₀ = P.map (constantCoeff R)`. -/
theorem coeff_eval_sub_at_xdep (P : Polynomial R⟦X⟧) {Γ₁ Γ₂ : R⟦X⟧} {t : ℕ} (ht : 0 < t)
    (h : ∀ j < t, coeff j Γ₁ = coeff j Γ₂) :
    coeff t (P.eval Γ₁) - coeff t (P.eval Γ₂) =
      (Polynomial.derivative (P.map (constantCoeff (R := R)))).eval (constantCoeff Γ₁) *
        (coeff t Γ₁ - coeff t Γ₂) := by
  classical
  set c := constantCoeff Γ₁ with hc
  set δ := coeff t Γ₁ - coeff t Γ₂ with hδ
  rw [Polynomial.eval_eq_sum_range, Polynomial.eval_eq_sum_range, map_sum, map_sum,
    ← Finset.sum_sub_distrib]
  have hstep : ∀ i ∈ Finset.range (P.natDegree + 1),
      coeff t (P.coeff i * Γ₁ ^ i) - coeff t (P.coeff i * Γ₂ ^ i)
        = (P.map (constantCoeff (R := R))).coeff i * i * c ^ (i - 1) * δ := by
    intro i _
    rw [(map_sub (coeff (R := R) t) _ _).symm, ← mul_sub]
    rcases i with _ | i
    · simp
    · have hvanish : ∀ k < t, coeff k (Γ₁ ^ (i + 1) - Γ₂ ^ (i + 1)) = 0 := by
        intro k hk
        rw [map_sub, coeff_pow_sub_below h (i + 1) k hk, sub_self]
      have hat : coeff t (Γ₁ ^ (i + 1) - Γ₂ ^ (i + 1)) = (i + 1) • (c ^ i * δ) := by
        rw [map_sub]; exact coeff_pow_sub_at ht h i
      rw [coeff_mul_of_vanish_below hvanish, hat, Polynomial.coeff_map,
        Nat.add_sub_cancel, nsmul_eq_mul]
      push_cast
      ring
  rw [Finset.sum_congr rfl hstep, ← Finset.sum_mul]
  congr 1
  rw [Polynomial.derivative_eval,
    Polynomial.sum_over_range' _ (by simp) (P.natDegree + 1)
      (Nat.lt_succ_of_le Polynomial.natDegree_map_le)]

/-! ## The Newton partial-sum sequence (deformation version) -/

variable (P : Polynomial R⟦X⟧) (c : R)

/-- The Newton partial-sum sequence for `P : R⟦X⟧[Y]`.  Same shape as the constant-coefficient
case, with the correction driven by `eval (S t) P` and the unit `eval c P₀'`. -/
noncomputable def S : ℕ → R⟦X⟧
  | 0 => PowerSeries.C c
  | (t + 1) =>
      S t + PowerSeries.monomial (t + 1)
        (-(Ring.inverse ((Polynomial.derivative (P.map (constantCoeff (R := R)))).eval c))
          * coeff (t + 1) (P.eval (S t)))

theorem coeff_S_succ_of_le {t j : ℕ} (hj : j ≤ t) :
    coeff j (S P c (t + 1)) = coeff j (S P c t) := by
  rw [S, map_add, coeff_monomial, if_neg (by omega), add_zero]

theorem coeff_S_eq_zero_of_lt : ∀ {t j : ℕ}, t < j → coeff j (S P c t) = 0 := by
  intro t
  induction t with
  | zero => intro j hj; rw [S, coeff_C, if_neg (by omega)]
  | succ t ih =>
      intro j hj
      rw [S, map_add, coeff_monomial, if_neg (by omega), add_zero]
      exact ih (by omega)

theorem coeff_S_stable : ∀ {t j : ℕ}, j ≤ t → coeff j (S P c t) = coeff j (S P c j) := by
  intro t
  induction t with
  | zero => intro j hj; rw [Nat.le_zero.mp hj]
  | succ t ih =>
      intro j hj
      rcases Nat.lt_succ_iff_lt_or_eq.mp (Nat.lt_succ_of_le hj) with hlt | heq
      · rw [coeff_S_succ_of_le P c (Nat.lt_succ_iff.mp hlt), ih (Nat.lt_succ_iff.mp hlt)]
      · rw [heq]

/-- The Newton root: diagonalise the stable partial sums. -/
noncomputable def γ : R⟦X⟧ := PowerSeries.mk fun t => coeff t (S P c t)

@[simp] theorem coeff_γ (t : ℕ) : coeff t (γ P c) = coeff t (S P c t) := by
  rw [γ, coeff_mk]

@[simp] theorem constantCoeff_γ : constantCoeff (γ P c) = c := by
  rw [← coeff_zero_eq_constantCoeff_apply, coeff_γ, S, coeff_zero_eq_constantCoeff_apply,
    constantCoeff_C]

theorem coeff_γ_eq_S {t j : ℕ} (hj : j ≤ t) : coeff j (γ P c) = coeff j (S P c t) := by
  rw [coeff_γ, ← coeff_S_stable P c hj]

/-! ## Order-by-order vanishing -/

variable (hc0 : (P.map (constantCoeff (R := R))).eval c = 0)
    (hu : IsUnit ((Polynomial.derivative (P.map (constantCoeff (R := R)))).eval c))

include hc0 in
/-- Order-0 coefficient of `eval γ P` vanishes: it is `eval c P₀ = 0`. -/
theorem coeff_zero_eval_γ : coeff 0 (P.eval (γ P c)) = 0 := by
  rw [coeff_zero_eq_constantCoeff_apply, constantCoeff_eval_xdep, constantCoeff_γ, hc0]

include hu in
/-- Order-`(t+1)` coefficient of `eval γ P` vanishes, by the Newton linearization. -/
theorem coeff_succ_eval_γ (t : ℕ) : coeff (t + 1) (P.eval (γ P c)) = 0 := by
  set A := (Polynomial.derivative (P.map (constantCoeff (R := R)))).eval c with hA
  set u := Ring.inverse A with hudef
  set w := coeff (t + 1) (P.eval (S P c t)) with hw
  have hAu : A * u = 1 := Ring.mul_inverse_cancel A hu
  have hagree : ∀ j < t + 1, coeff j (γ P c) = coeff j (S P c t) := fun j hj =>
    coeff_γ_eq_S P c (Nat.lt_succ_iff.mp hj)
  have hlin := coeff_eval_sub_at_xdep P (Γ₁ := γ P c) (Γ₂ := S P c t) (Nat.succ_pos t) hagree
  rw [constantCoeff_γ, ← hA] at hlin
  have hSt0 : coeff (t + 1) (S P c t) = 0 := coeff_S_eq_zero_of_lt P c (Nat.lt_succ_self t)
  have hγcoeff : coeff (t + 1) (γ P c) = -u * w := by
    rw [coeff_γ, S, map_add, coeff_monomial, if_pos rfl, hSt0, zero_add, ← hA, ← hudef, ← hw]
  rw [hγcoeff, hSt0, ← hw] at hlin
  rw [show A * (-u * w - 0) = -(A * u) * w by ring, hAu, neg_one_mul] at hlin
  have hgoal : coeff (t + 1) (P.eval (γ P c)) = w + (-w) := by
    rw [← hlin]; ring
  rw [hgoal, add_neg_cancel]

include hc0 hu in
/-- Every coefficient of `eval γ P` vanishes, hence `eval γ P = 0`. -/
theorem eval_γ_eq_zero : P.eval (γ P c) = 0 := by
  ext t
  rw [map_zero]
  rcases t with _ | t
  · exact coeff_zero_eval_γ P c hc0
  · exact coeff_succ_eval_γ P c hu t

/-! ## Main existence theorem -/

variable {P c}

include hc0 hu in
/-- **Hensel-root existence for power series with `X`-dependent coefficients.**  Given
`P : R⟦X⟧[Y]` whose order-0 reduction `P₀ = P.map (constantCoeff R)` has a *simple* root `c`
(`eval c P₀ = 0` and `IsUnit (eval c P₀')`), there exists `Γ : R⟦X⟧` lifting `c`
(`constantCoeff Γ = c`) with `Polynomial.eval Γ P = 0`. -/
theorem exists_powerSeries_root_xdep :
    ∃ Γ : R⟦X⟧, constantCoeff Γ = c ∧ Polynomial.eval Γ P = 0 :=
  ⟨γ P c, constantCoeff_γ P c, eval_γ_eq_zero P c hc0 hu⟩

/-! ## `eval₂` form (coefficient-wise; avoids materializing the mapped polynomial)

When the target ring `R⟦X⟧` carries an expensive `R` (e.g. a function field built as a heavy
quotient), materializing `P.map f : R⟦X⟧[Y]` in a *statement* makes elaboration blow up.  This
`eval₂` reformulation keeps the polynomial `P` over the light base ring `A` and the coefficient
map `f : A →+* R⟦X⟧` separate, so the heavy mapped polynomial only ever appears inside the proof
(once), never in the signature. -/

variable {A : Type*} [CommRing A]

/-- **Hensel-root existence, `eval₂` form.**  Given a coefficient map `f : A →+* R⟦X⟧` and
`P : A[Y]`, if `c : R` is a simple root of the order-0 reduction `eval₂ (constantCoeff ∘ f) c`
(`hroot`, with `hunit` its simplicity), then there is `Γ : R⟦X⟧` with `constantCoeff Γ = c` and
`eval₂ f Γ P = 0`. -/
theorem exists_powerSeries_root_eval₂ (f : A →+* R⟦X⟧) {P : Polynomial A} {c : R}
    (hroot : Polynomial.eval₂ ((constantCoeff (R := R)).comp f) c P = 0)
    (hunit : IsUnit (Polynomial.eval₂ ((constantCoeff (R := R)).comp f) c
      (Polynomial.derivative P))) :
    ∃ Γ : R⟦X⟧, constantCoeff Γ = c ∧ Polynomial.eval₂ f Γ P = 0 := by
  have hmap : (P.map f).map (constantCoeff (R := R)) = P.map ((constantCoeff (R := R)).comp f) := by
    rw [Polynomial.map_map]
  have hroot' : ((P.map f).map (constantCoeff (R := R))).eval c = 0 := by
    rw [hmap, ← Polynomial.eval₂_eq_eval_map]; exact hroot
  have hunit' : IsUnit ((Polynomial.derivative ((P.map f).map (constantCoeff (R := R)))).eval c) := by
    rw [hmap, Polynomial.derivative_map, ← Polynomial.eval₂_eq_eval_map]; exact hunit
  obtain ⟨Γ, hc, hev⟩ := exists_powerSeries_root_xdep (P := P.map f) (c := c) hroot' hunit'
  refine ⟨Γ, hc, ?_⟩
  rw [Polynomial.eval₂_eq_eval_map]; exact hev

end ProximityPrize.HenselExistenceXDep

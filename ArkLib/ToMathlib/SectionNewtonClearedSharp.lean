/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.ToMathlib.SectionNewtonCleared

/-!
# The sharp (quadratic) cleared Newton filtration (#304 — Finding F15 and its repair)

**Finding F15 (self-audit)**: the budget of `SectionNewtonCleared.gamma_cleared` is
**exponential in `t`** — `pow_cleared` bounds every factor of `(S t)^i` by the *worst*
coefficient budget (`i · (G + 2t·dξ)`), so the main recursion multiplies the full previous
budget by `d = deg Q` at every order.  At real Guruswami–Sudan parameters
(`T ~ poly(n)`) the count hypothesis `|M| > clearedBudget T` is then unsatisfiable: the
unsharpened window is honest but **vacuous in the genuine regime**.

**The repair — superadditivity of squares.**  The degree of a convolution product is the
*sum over the composition parts*, not `i` times the maximum:

* nonzero parts: `Σ α·bⱼ² ≤ α·b²` (squares are superadditive: `p² + q² ≤ (p+q)²`);
* zero parts contribute the seed degree `dv` each, at most `i ≤ d` times — tracked as the
  *additive* `i·dv`, never multiplied by the running budget;
* **the truncation corner saves the degree exactly as it saves the exponent**: at
  `b = t + 1` all parts are `≤ t`, so two parts are nonzero and
  `p² + q² = (t+1)² − 2pq ≤ t² + 1` — one `2αt` of slack, exactly absorbing the new order's
  data (`DZ`), pads, and zero-part costs.

Result: `gamma_cleared_sharp` — the `(A.4)` clearing at exponent `2t − 1` with the
**quadratic** budget `sharpBudget … t = dv + α·t²`, `α := DZ + d·dv + 3·dξ + 1`.  The window
count `|M| > dv + α·T²` is polynomial in the GS parameters.

## References
* [BCIKS20] Ben-Sasson, Carmon, Ishai, Kopparty, Saraf, *Proximity Gaps for Reed–Solomon
  Codes*, §5 (Claim 5.8), Appendix A.2/A.4.
-/

set_option linter.style.longLine false

namespace ArkLib.SectionNewtonCleared

open PowerSeries ProximityPrize.HenselSeriesCoeff

variable {F : Type*} [Field F] (ξ : Polynomial F)

local notation "𝔞" => algebraMap (Polynomial F) (Localization.Away ξ)

/-- The sharp slope: one `2αt` of corner slack per order absorbs the data degree, the
zero-part seeds, and the `ξ̄`-pads. -/
def sharpSlope (d dv DZ dξ : ℕ) : ℕ := DZ + d * dv + 3 * dξ + 1

/-- **The sharp budget**: quadratic in the order. -/
def sharpBudget (d dv DZ dξ : ℕ) (t : ℕ) : ℕ := dv + sharpSlope d dv DZ dξ * t ^ 2

theorem sharpBudget_mono (d dv DZ dξ : ℕ) : Monotone (sharpBudget d dv DZ dξ) := by
  intro a b hab
  unfold sharpBudget
  have : a ^ 2 ≤ b ^ 2 := Nat.pow_le_pow_left hab 2
  exact Nat.add_le_add_left (Nat.mul_le_mul_left _ this) _

variable (QA : Polynomial (PowerSeries (Localization.Away ξ))) (v : Polynomial F)

/-- **The sharp power filtration**: the degree of `coeff b ((S t)^i)` is governed by the
*sum over composition parts* — `α·b²` for the nonzero parts (superadditivity of squares)
plus `i·dv` for the zero parts — never `i` times the worst budget. -/
theorem pow_cleared_sharp {t : ℕ} {α dv' : ℕ}
    (hγ : ∀ j ≤ t, Cleared ξ (coeff j (γ QA (𝔞 v))) (2 * j - 1) (dv' + α * j ^ 2))
    (hα : ξ.natDegree ≤ α) :
    ∀ i, ∀ b ≤ t, Cleared ξ (coeff b ((S QA (𝔞 v) t) ^ i)) (2 * b - 1)
      (i * dv' + α * b ^ 2) := by
  intro i
  induction i with
  | zero =>
      intro b hb
      rcases Nat.eq_zero_or_pos b with rfl | hb0
      · rw [pow_zero]
        have h1 : coeff 0 (1 : PowerSeries (Localization.Away ξ)) = 1 := by simp
        rw [h1]
        exact (Cleared.one _).mono (Nat.zero_le _)
      · rw [pow_zero]
        have h0 : coeff b (1 : PowerSeries (Localization.Away ξ)) = 0 := by
          rw [PowerSeries.coeff_one, if_neg (by omega)]
        rw [h0]
        exact Cleared.zero _ _
  | succ i ih =>
      intro b hb
      rw [pow_succ', PowerSeries.coeff_mul]
      apply Cleared.sum
      intro p hp
      have hpq : p.1 + p.2 = b := Finset.mem_antidiagonal.mp hp
      have hp1 : p.1 ≤ t := by omega
      have hSγ : coeff p.1 (S QA (𝔞 v) t) = coeff p.1 (γ QA (𝔞 v)) :=
        (coeff_γ_eq_S QA (𝔞 v) hp1).symm
      rw [hSγ]
      have hterm := (hγ p.1 hp1).mul (ih p.2 (by omega))
      have hexp : (2 * p.1 - 1) + (2 * p.2 - 1) ≤ 2 * b - 1 := by omega
      refine hterm.padTo hexp ?_
      -- the pad costs at most one `dξ ≤ α`; squares are superadditive
      have hsq : p.1 ^ 2 + p.2 ^ 2 + p.1 * p.2 ≤ b ^ 2 := by
        have : b ^ 2 = (p.1 + p.2) ^ 2 := by rw [hpq]
        rw [this]
        ring_nf
        nlinarith [Nat.zero_le (p.1 * p.2)]
      have hpad : (2 * b - 1 - ((2 * p.1 - 1) + (2 * p.2 - 1))) ≤ 1 := by omega
      have hpadcost : (2 * b - 1 - ((2 * p.1 - 1) + (2 * p.2 - 1))) * ξ.natDegree
          ≤ ξ.natDegree := by
        calc (2 * b - 1 - ((2 * p.1 - 1) + (2 * p.2 - 1))) * ξ.natDegree
            ≤ 1 * ξ.natDegree := Nat.mul_le_mul_right _ hpad
          _ = ξ.natDegree := one_mul _
      -- if the pad is positive, both parts are nonzero, so a full `α·p₁p₂ ≥ α` is free
      rcases Nat.eq_zero_or_pos (2 * b - 1 - ((2 * p.1 - 1) + (2 * p.2 - 1))) with hz | hpos
      · rw [hz, zero_mul, add_zero]
        have : α * p.1 ^ 2 + α * p.2 ^ 2 ≤ α * b ^ 2 := by
          calc α * p.1 ^ 2 + α * p.2 ^ 2 = α * (p.1 ^ 2 + p.2 ^ 2) := by ring
            _ ≤ α * b ^ 2 := Nat.mul_le_mul_left _ (by omega)
        omega
      · have hp1pos : 1 ≤ p.1 := by omega
        have hp2pos : 1 ≤ p.2 := by omega
        have hprod : 1 ≤ p.1 * p.2 := Nat.one_le_iff_ne_zero.mpr (by positivity)
        have hsq' : α * p.1 ^ 2 + α * p.2 ^ 2 + α ≤ α * b ^ 2 := by
          calc α * p.1 ^ 2 + α * p.2 ^ 2 + α
              ≤ α * p.1 ^ 2 + α * p.2 ^ 2 + α * (p.1 * p.2) := by
                exact Nat.add_le_add_left (Nat.le_mul_of_pos_right _ hprod) _
            _ = α * (p.1 ^ 2 + p.2 ^ 2 + p.1 * p.2) := by ring
            _ ≤ α * b ^ 2 := Nat.mul_le_mul_left _ hsq
        have hξα := hα
        omega

/-- **The sharp top-corner filtration**: at `b = t + 1` all parts are `≤ t`, so
`p² + q² = (t+1)² − 2pq ≤ t² + 1` — the corner slack `2αt` is exactly what the main
recursion's new order spends. -/
theorem powTop_cleared_sharp {t : ℕ} {α dv' : ℕ}
    (hγ : ∀ j ≤ t, Cleared ξ (coeff j (γ QA (𝔞 v))) (2 * j - 1) (dv' + α * j ^ 2)) :
    ∀ i, Cleared ξ (coeff (t + 1) ((S QA (𝔞 v) t) ^ i)) (2 * t)
      (i * dv' + α * (t ^ 2 + 1)) := by
  intro i
  induction i with
  | zero =>
      rw [pow_zero]
      have h0 : coeff (t + 1) (1 : PowerSeries (Localization.Away ξ)) = 0 := by
        rw [PowerSeries.coeff_one, if_neg (by omega)]
      rw [h0]
      exact Cleared.zero _ _
  | succ i ih =>
      rw [pow_succ', PowerSeries.coeff_mul]
      apply Cleared.sum
      intro p hp
      have hpq : p.1 + p.2 = t + 1 := Finset.mem_antidiagonal.mp hp
      rcases Nat.lt_or_ge t p.1 with hp1 | hp1
      · have hzero : coeff p.1 (S QA (𝔞 v) t) = 0 := coeff_S_eq_zero_of_lt QA (𝔞 v) hp1
        rw [hzero, zero_mul]
        exact Cleared.zero _ _
      · have hSγ : coeff p.1 (S QA (𝔞 v) t) = coeff p.1 (γ QA (𝔞 v)) :=
          (coeff_γ_eq_S QA (𝔞 v) hp1).symm
        rw [hSγ]
        rcases Nat.lt_or_ge t p.2 with hp2 | hp2
        · -- the seed corner: `p.1 = 0`, recurse on the top coefficient
          have hp10 : p.1 = 0 := by omega
          have hp2eq : p.2 = t + 1 := by omega
          rw [hp10, hp2eq]
          have hterm := (hγ 0 (Nat.zero_le t)).mul ih
          have hexp : (2 * 0 - 1) + 2 * t = 2 * t := by omega
          rw [hexp] at hterm
          refine hterm.mono ?_
          have h00 : dv' + α * 0 ^ 2 = dv' := by ring_nf
          omega
        · -- two nonzero parts `≤ t`: `p² + q² ≤ t² + 1`, exponent exact
          have hp1pos : 1 ≤ p.1 := by omega
          have hp2pos : 1 ≤ p.2 := by omega
          have hterm := (hγ p.1 hp1).mul (pow_cleared_sharp ξ QA v hγ (le_refl _) i p.2 hp2)
          have hexp : (2 * p.1 - 1) + (2 * p.2 - 1) = 2 * t := by omega
          rw [hexp] at hterm
          refine hterm.mono ?_
          have hsq : p.1 ^ 2 + p.2 ^ 2 ≤ t ^ 2 + 1 := by nlinarith
          have : α * p.1 ^ 2 + α * p.2 ^ 2 ≤ α * (t ^ 2 + 1) := by
            calc α * p.1 ^ 2 + α * p.2 ^ 2 = α * (p.1 ^ 2 + p.2 ^ 2) := by ring
              _ ≤ α * (t ^ 2 + 1) := Nat.mul_le_mul_left _ hsq
          omega

/-- **THE SHARP CLEARED FILTRATION** (the F15 repair): the `(A.4)` clearing at exponent
`2t − 1` with the **quadratic** budget `dv + (DZ + d·dv + 3·dξ + 1)·t²`. -/
theorem gamma_cleared_sharp {DZ : ℕ}
    (hQdeg : ∀ i j, ∃ q : Polynomial F, q.natDegree ≤ DZ ∧ 𝔞 q = coeff j (QA.coeff i))
    (hresp : Polynomial.eval (𝔞 v) (Polynomial.derivative (Q₀ QA)) = 𝔞 ξ) :
    ∀ t, Cleared ξ (coeff t (γ QA (𝔞 v))) (2 * t - 1)
      (sharpBudget QA.natDegree v.natDegree DZ ξ.natDegree t) := by
  set d := QA.natDegree with hd
  set dv := v.natDegree with hdv
  set dξ := ξ.natDegree with hdξ
  set α := sharpSlope d dv DZ dξ with hα
  have hαξ : dξ ≤ α := by rw [hα]; unfold sharpSlope; omega
  intro t
  induction t using Nat.strong_induction_on with
  | _ t ih =>
    cases t with
    | zero =>
        have h0 : coeff 0 (γ QA (𝔞 v)) = 𝔞 v := by
          rw [coeff_zero_eq_constantCoeff_apply, constantCoeff_γ]
        rw [h0]
        exact (Cleared.of_algebraMap v).mono (by unfold sharpBudget; omega)
    | succ t =>
        have hγ : ∀ j ≤ t, Cleared ξ (coeff j (γ QA (𝔞 v))) (2 * j - 1)
            (dv + α * j ^ 2) :=
          fun j hj => (ih j (by omega)).mono (le_of_eq rfl)
        -- the inner sum clears at `2t` with the corner budget
        have hsum : Cleared ξ (coeff (t + 1) (Polynomial.eval (S QA (𝔞 v) t) QA)) (2 * t)
            (DZ + (d * dv + α * (t ^ 2 + 1)) + (2 * t + 1) * dξ) := by
          rw [coeff_eval_eq_sum_range]
          apply Cleared.sum
          intro i hi
          have hile : i ≤ d := by
            have := Finset.mem_range.mp hi
            omega
          rw [PowerSeries.coeff_mul]
          apply Cleared.sum
          intro p hp
          have hpq : p.1 + p.2 = t + 1 := Finset.mem_antidiagonal.mp hp
          obtain ⟨q, hqdeg, hqmap⟩ := hQdeg i p.1
          have hcoeffQ : Cleared ξ (coeff p.1 (QA.coeff i)) 0 DZ := by
            rw [← hqmap]
            exact (Cleared.of_algebraMap q).mono hqdeg
          rcases Nat.lt_or_ge t p.2 with hp2 | hp2
          · -- top corner
            have hp2eq : p.2 = t + 1 := by omega
            rw [hp2eq]
            have hterm := hcoeffQ.mul (powTop_cleared_sharp ξ QA v hγ i)
            have hexp : 0 + 2 * t = 2 * t := by omega
            rw [hexp] at hterm
            refine hterm.mono ?_
            have hidv : i * dv ≤ d * dv := Nat.mul_le_mul_right _ hile
            omega
          · -- generic coefficient, padded
            have hterm := hcoeffQ.mul (pow_cleared_sharp ξ QA v hγ hαξ i p.2 hp2)
            have hexp : 0 + (2 * p.2 - 1) ≤ 2 * t := by omega
            refine hterm.padTo hexp ?_
            have hidv : i * dv ≤ d * dv := Nat.mul_le_mul_right _ hile
            have hsq : α * p.2 ^ 2 ≤ α * (t ^ 2 + 1) :=
              Nat.mul_le_mul_left _ (by nlinarith)
            have hpadcost : (2 * t - (0 + (2 * p.2 - 1))) * dξ ≤ (2 * t + 1) * dξ :=
              Nat.mul_le_mul_right _ (by omega)
            omega
        have hrec := coeff_γ_succ_eq QA (𝔞 v) t
        rw [hresp] at hrec
        rw [hrec, neg_mul]
        have hfinal := (hsum.inverse_xi_mul).neg
        have he : 2 * t + 1 = 2 * (t + 1) - 1 := by omega
        rw [he] at hfinal
        refine hfinal.mono ?_
        -- the corner slack `2αt + α` absorbs `DZ + d·dv + (2t+1)·dξ`
        unfold sharpBudget
        have hslack : DZ + d * dv + (2 * t + 1) * dξ ≤ α * (2 * t + 1) := by
          have h1 : (2 * t + 1) * dξ ≤ (2 * t + 1) * α := Nat.mul_le_mul_right _ hαξ
          have h2 : DZ + d * dv ≤ α := by rw [hα]; unfold sharpSlope; omega
          nlinarith
        have hexpand : α * (t + 1) ^ 2 = α * (t ^ 2 + 1) + α * (2 * t) := by ring
        omega

/-- **The sharp witness pack**. -/
theorem exists_numerator_sharp {DZ : ℕ}
    (hQdeg : ∀ i j, ∃ q : Polynomial F, q.natDegree ≤ DZ ∧ 𝔞 q = coeff j (QA.coeff i))
    (hresp : Polynomial.eval (𝔞 v) (Polynomial.derivative (Q₀ QA)) = 𝔞 ξ) (t : ℕ) :
    ∃ N : Polynomial F,
      N.natDegree ≤ sharpBudget QA.natDegree v.natDegree DZ ξ.natDegree t ∧
      𝔞 N = (𝔞 ξ) ^ (2 * t - 1) * coeff t (γ QA (𝔞 v)) ∧
      (N = 0 → coeff t (γ QA (𝔞 v)) = 0) := by
  obtain ⟨N, hdeg, hmap⟩ := gamma_cleared_sharp ξ QA v hQdeg hresp t
  exact ⟨N, hdeg, hmap, fun h0 => eq_zero_of_cleared_witness ξ hmap h0⟩

end ArkLib.SectionNewtonCleared

/-! ## Axiom audit — every declaration must rest only on
`[propext, Classical.choice, Quot.sound]`, with no `sorry`/`admit`/`axiom`/`native_decide`. -/
#print axioms ArkLib.SectionNewtonCleared.sharpBudget_mono
#print axioms ArkLib.SectionNewtonCleared.pow_cleared_sharp
#print axioms ArkLib.SectionNewtonCleared.powTop_cleared_sharp
#print axioms ArkLib.SectionNewtonCleared.gamma_cleared_sharp
#print axioms ArkLib.SectionNewtonCleared.exists_numerator_sharp

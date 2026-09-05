/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/

import scripts.probes.astra_riccati_contact_obstruction

/-!
# Full quadratic first-order contact at the production profile

This extends the Riccati obstruction to sources containing YR and R².
The hypotheses expose the extracted contact divisibilities, weighted degree
caps, and actual agreements. It does not assert a prize lower bound.
-/

set_option autoImplicit false

namespace AstraQuadraticContactObstruction

open Polynomial AstraRiccatiContactObstruction

variable {K : Type*} [Field K]

/-- Exact coefficients after the first-order contact substitution. -/
theorem quadratic_contact_expansion {R : Type*} [CommRing R]
    (a b c d e f v t r z : R) :
    a + b * (v + t * r + z) + c * (v + t * r + z) ^ 2 + d * r +
        e * (v + t * r + z) * r + f * r ^ 2 =
      (a + b * v + c * v ^ 2) + r * (d + v * e + t * (b + 2 * v * c)) +
      r ^ 2 * (f + t * e + t ^ 2 * c) + z * (b + 2 * v * c) +
      r * z * (e + 2 * t * c) + z ^ 2 * c := by
  ring

/-- Multiplicity forced on the R² coefficient by three local conditions. -/
def squareOrder (m : ℕ) : ℕ := min m (min (1 + (m - 2)) (2 + (m - 4)))

/-- Multiplicity forced on the YR coefficient once the R² coefficient vanishes. -/
def crossOrder (m : ℕ) : ℕ := if m = 2 then 1 else m - 2

private theorem power_mul_divisibility (T B : K[X]) (a k : ℕ)
    (h : T ^ a ∣ B) : T ^ (k + a) ∣ T ^ k * B := by
  rw [pow_add]
  exact mul_dvd_mul_left (T ^ k) h

/-- The R², Rz and z² contact coefficients force the claimed local divisor. -/
theorem local_square_divisibility (T C E F : K[X]) (m : ℕ)
    (hRR : T ^ m ∣ F + T * E + T ^ 2 * C)
    (hRZ : T ^ (m - 2) ∣ E + 2 * T * C)
    (hZZ : T ^ (m - 4) ∣ C) : T ^ squareOrder m ∣ F := by
  have h0 : T ^ squareOrder m ∣ F + T * E + T ^ 2 * C :=
    (pow_dvd_pow T (by unfold squareOrder; omega)).trans hRR
  have h1 : T ^ squareOrder m ∣ T * (E + 2 * T * C) := by
    have h := power_mul_divisibility T (E + 2 * T * C) (m - 2) 1 hRZ
    simpa using (pow_dvd_pow T (by unfold squareOrder; omega)).trans h
  have h2 : T ^ squareOrder m ∣ T ^ 2 * C :=
    (pow_dvd_pow T (by unfold squareOrder; omega)).trans
      (power_mul_divisibility T C (m - 4) 2 hZZ)
  convert dvd_add (dvd_sub h0 h1) h2 using 1
  ring

/-- Products of distinct node powers give the exact multiplicity degree bound. -/
theorem multiplicity_degree_bound (S : Finset K) (W : K[X]) (q : K → ℕ)
    (hW : W ≠ 0) (hlocal : ∀ x ∈ S, (X - C x) ^ q x ∣ W) :
    (∑ x ∈ S, q x) ≤ W.natDegree := by
  classical
  have hdiv : (∏ x ∈ S, (X - C x) ^ q x) ∣ W := by
    apply Finset.prod_dvd_of_coprime
    · intro x _ y _ hxy
      exact (Polynomial.isCoprime_X_sub_C_of_isUnit_sub
        (sub_ne_zero.mpr hxy).isUnit).pow
    · exact hlocal
  have h := Polynomial.natDegree_le_of_dvd hdiv hW
  rw [Polynomial.natDegree_prod_of_monic S _ fun x _ => (monic_X_sub_C x).pow (q x)] at h
  simpa [Polynomial.natDegree_pow] using h

/-- The production weight cap is incompatible with a nonzero R² coefficient. -/
theorem production_square_zero (S : Finset K) (hS : S.card = 1073741823)
    (C E F : K[X]) (m : ℕ) (hm : 0 < m)
    (hdegree : F ≠ 0 → F.natDegree + 1073741820 < m * 715827883)
    (hRR : ∀ x ∈ S, (X - Polynomial.C x) ^ m ∣
      F + (X - Polynomial.C x) * E + (X - Polynomial.C x) ^ 2 * C)
    (hRZ : ∀ x ∈ S, (X - Polynomial.C x) ^ (m - 2) ∣
      E + 2 * (X - Polynomial.C x) * C)
    (hZZ : ∀ x ∈ S, (X - Polynomial.C x) ^ (m - 4) ∣ C) : F = 0 := by
  classical
  by_contra hF
  have hle := multiplicity_degree_bound S F (fun _ => squareOrder m) hF
    (fun x hx => local_square_divisibility (X - Polynomial.C x) C E F m
      (hRR x hx) (hRZ x hx) (hZZ x hx))
  simp only [Finset.sum_const, smul_eq_mul, hS] at hle
  have hd := hdegree hF
  unfold squareOrder at hle
  omega

/-- Cancellation of the local parameter controls the remaining YR coefficient. -/
theorem local_cross_divisibility (T C E : K[X]) (hT : T ≠ 0)
    (m : ℕ) (hm : 0 < m)
    (hRR : T ^ m ∣ T * E + T ^ 2 * C)
    (hRZ : T ^ (m - 2) ∣ E + 2 * T * C) : T ^ crossOrder m ∣ E := by
  have hET : T ^ (m - 1) ∣ E + T * C := by
    have heq : T ^ m = T * T ^ (m - 1) := by
      rw [← pow_succ']; congr 1; omega
    rw [heq] at hRR
    have hr : T * E + T ^ 2 * C = T * (E + T * C) := by ring
    rw [hr] at hRR
    exact (mul_dvd_mul_iff_left hT).mp hRR
  by_cases hm2 : m = 2
  · subst m
    simp only [crossOrder, if_pos, Nat.reduceSub, pow_one] at *
    simpa using dvd_sub hET (dvd_mul_right T C)
  · rw [crossOrder, if_neg hm2]
    have hweak : T ^ (m - 2) ∣ E + T * C :=
      (pow_dvd_pow T (by omega)).trans hET
    have htwice : T ^ (m - 2) ∣ 2 * (E + T * C) := dvd_mul_of_dvd_right hweak 2
    convert dvd_sub htwice hRZ using 1
    ring

/-- Except at contact order three, the production cap already kills YR. -/
theorem production_cross_zero_except_three (S : Finset K)
    (hS : S.card = 1073741823) (C E : K[X]) (m : ℕ) (hm : 0 < m) (hm3 : m ≠ 3)
    (hdegree : E ≠ 0 → E.natDegree + 1073741821 < m * 715827883)
    (hRR : ∀ x ∈ S, (X - Polynomial.C x) ^ m ∣
      (X - Polynomial.C x) * E + (X - Polynomial.C x) ^ 2 * C)
    (hRZ : ∀ x ∈ S, (X - Polynomial.C x) ^ (m - 2) ∣
      E + 2 * (X - Polynomial.C x) * C) : E = 0 := by
  classical
  by_contra hE
  have hle := multiplicity_degree_bound S E (fun _ => crossOrder m) hE
    (fun x hx => local_cross_divisibility (X - Polynomial.C x) C E
      (X_sub_C_ne_zero x) m hm (hRR x hx) (hRZ x hx))
  simp only [Finset.sum_const, smul_eq_mul, hS] at hle
  have hd := hdegree hE
  unfold crossOrder at hle
  split_ifs at hle <;> omega

/-- Simple roots on S and double roots on H force degree at least |S|+|H|. -/
theorem augmented_root_degree (S H : Finset K) (hHS : H ⊆ S)
    (W : K[X]) (hW : W ≠ 0)
    (hS : ∀ x ∈ S, X - C x ∣ W)
    (hH : ∀ x ∈ H, (X - C x) ^ 2 ∣ W) : S.card + H.card ≤ W.natDegree := by
  classical
  have h := multiplicity_degree_bound S W (fun x => if x ∈ H then 2 else 1) hW (by
    intro x hx
    change (X - C x) ^ (if x ∈ H then 2 else 1) ∣ W
    split_ifs with hxH
    · exact hH x hxH
    · simpa using hS x hx)
  have heq : (∑ x ∈ S, if x ∈ H then 2 else 1) = S.card + H.card := by
    calc
      _ = ∑ x ∈ S, (1 + if x ∈ H then 1 else 0) := by
        apply Finset.sum_congr rfl
        intro x _
        split_ifs <;> rfl
      _ = S.card + H.card := by
        simp [Finset.sum_add_distrib, Finset.inter_eq_right.mpr hHS]
  rwa [heq] at h

/-- At contact order three, a decoded candidate kills D+fE by double roots. -/
theorem production_order_three_relation (S H : Finset K)
    (hS : S.card = 1073741823) (hHS : H ⊆ S) (hH : 715827883 ≤ H.card)
    (D E f : K[X]) (v : K → K)
    (hDdegree : D.natDegree ≤ 1610612738)
    (hEdegree : E.natDegree ≤ 1073741827) (hfdegree : f.natDegree ≤ 536870911)
    (hE : ∀ x ∈ S, X - C x ∣ E)
    (hDE : ∀ x ∈ S, (X - C x) ^ 2 ∣ D + C (v x) * E)
    (hagree : ∀ x ∈ H, f.eval x = v x) : D + f * E = 0 := by
  by_contra hW
  have hbase (x : K) (hx : x ∈ S) : X - C x ∣ D + f * E := by
    have hpow : X - C x ∣ (X - C x) ^ 2 := by
      rw [pow_two]
      exact dvd_mul_right _ _
    have hde : X - C x ∣ D + C (v x) * E := hpow.trans (hDE x hx)
    have hdiff : X - C x ∣ (f - C (v x)) * E := dvd_mul_of_dvd_right (hE x hx) _
    convert dvd_add hde hdiff using 1
    ring
  have hdouble (x : K) (hx : x ∈ H) : (X - C x) ^ 2 ∣ D + f * E := by
    have hf : X - C x ∣ f - C (v x) := by
      rw [← hagree x hx]
      exact X_sub_C_dvd_sub_C_eval
    have hdiff : (X - C x) ^ 2 ∣ (f - C (v x)) * E := by
      simpa [pow_two] using mul_dvd_mul hf (hE x (hHS hx))
    convert dvd_add (hDE x (hHS hx)) hdiff using 1
    ring
  have hlo := augmented_root_degree S H hHS (D + f * E) hW hbase hdouble
  have hprod : (f * E).natDegree ≤ 1610612738 :=
    Polynomial.natDegree_mul_le.trans (by omega)
  have hhi := Polynomial.natDegree_add_le_of_degree_le hDdegree hprod
  omega

/-- Two decoded candidates eliminate the exceptional order-three coefficients. -/
theorem production_order_three_zero (S H₀ H₁ : Finset K)
    (hS : S.card = 1073741823) (hH₀S : H₀ ⊆ S) (hH₁S : H₁ ⊆ S)
    (hH₀ : 715827883 ≤ H₀.card) (hH₁ : 715827883 ≤ H₁.card)
    (D E f₀ f₁ : K[X]) (v : K → K)
    (hDdegree : D.natDegree ≤ 1610612738)
    (hEdegree : E.natDegree ≤ 1073741827)
    (hf₀degree : f₀.natDegree ≤ 536870911) (hf₁degree : f₁.natDegree ≤ 536870911)
    (hE : ∀ x ∈ S, X - C x ∣ E)
    (hDE : ∀ x ∈ S, (X - C x) ^ 2 ∣ D + C (v x) * E)
    (hagree₀ : ∀ x ∈ H₀, f₀.eval x = v x) (hagree₁ : ∀ x ∈ H₁, f₁.eval x = v x)
    (hne : f₀ ≠ f₁) : D = 0 ∧ E = 0 := by
  have h0 := production_order_three_relation S H₀ hS hH₀S hH₀ D E f₀ v
    hDdegree hEdegree hf₀degree hE hDE hagree₀
  have h1 := production_order_three_relation S H₁ hS hH₁S hH₁ D E f₁ v
    hDdegree hEdegree hf₁degree hE hDE hagree₁
  have he : E = 0 := by
    apply (mul_eq_zero.mp ?_).resolve_left (sub_ne_zero.mpr hne)
    calc
      (f₀ - f₁) * E = (D + f₀ * E) - (D + f₁ * E) := by ring
      _ = 0 := by rw [h0, h1]; ring
  exact ⟨by simpa [he] using h0, he⟩

/-- Necessary conditions of a full quadratic source under the production cap.
Zero coefficients have no degree obligation, including when their weight alone
exceeds the cap. These conditions do not posit a nonzero interpolator. -/
structure ProductionContact (S : Finset K) (b c d e f : K[X]) (v : K → K) (m : ℕ) : Prop where
  dDegree : d ≠ 0 → d.natDegree + 536870910 < m * 715827883
  eDegree : e ≠ 0 → e.natDegree + 1073741821 < m * 715827883
  fDegree : f ≠ 0 → f.natDegree + 1073741820 < m * 715827883
  rr : ∀ x ∈ S, (X - C x) ^ m ∣ f + (X - C x) * e + (X - C x) ^ 2 * c
  rz : ∀ x ∈ S, (X - C x) ^ (m - 2) ∣ e + 2 * (X - C x) * c
  zz : ∀ x ∈ S, (X - C x) ^ (m - 4) ∣ c
  r : ∀ x ∈ S, (X - C x) ^ m ∣ d + C (v x) * e + (X - C x) * (b + C (2 * v x) * c)
  z : ∀ x ∈ S, (X - C x) ^ (m - 2) ∣ b + C (2 * v x) * c

/-- Two actual decoded candidates eliminate every derivative-containing term. -/
theorem production_derivative_coefficients_zero (S H₀ H₁ : Finset K)
    (hS : S.card = 1073741823) (hH₀S : H₀ ⊆ S) (hH₁S : H₁ ⊆ S)
    (hH₀ : 715827883 ≤ H₀.card) (hH₁ : 715827883 ≤ H₁.card)
    (b c d e f f₀ f₁ : K[X]) (v : K → K) (m : ℕ) (hm : 0 < m)
    (hc : ProductionContact S b c d e f v m)
    (hf₀degree : f₀.natDegree ≤ 536870911) (hf₁degree : f₁.natDegree ≤ 536870911)
    (hagree₀ : ∀ x ∈ H₀, f₀.eval x = v x) (hagree₁ : ∀ x ∈ H₁, f₁.eval x = v x)
    (hne : f₀ ≠ f₁) : d = 0 ∧ e = 0 ∧ f = 0 := by
  have hf := production_square_zero S hS c e f m hm hc.fDegree hc.rr hc.rz hc.zz
  have hrr : ∀ x ∈ S, (X - C x) ^ m ∣ (X - C x) * e + (X - C x) ^ 2 * c := by
    simpa [hf] using hc.rr
  by_cases hm3 : m = 3
  · subst m
    have he (x : K) (hx : x ∈ S) : X - C x ∣ e := by
      simpa [crossOrder] using local_cross_divisibility (X - C x) c e
        (X_sub_C_ne_zero x) 3 (by omega) (hrr x hx) (hc.rz x hx)
    have hde (x : K) (hx : x ∈ S) : (X - C x) ^ 2 ∣ d + C (v x) * e := by
      simpa using local_derivative_divisibility (X - C x) (d + C (v x) * e)
        (b + C (2 * v x) * c) 3 (by omega) (hc.r x hx) (hc.z x hx)
    have hdd : d.natDegree ≤ 1610612738 := by
      by_cases hd : d = 0
      · simp [hd]
      · have h := hc.dDegree hd; omega
    have hed : e.natDegree ≤ 1073741827 := by
      by_cases he : e = 0
      · simp [he]
      · have h := hc.eDegree he; omega
    obtain ⟨hd, he⟩ := production_order_three_zero S H₀ H₁ hS hH₀S hH₁S hH₀ hH₁
      d e f₀ f₁ v hdd hed hf₀degree hf₁degree he hde hagree₀ hagree₁ hne
    exact ⟨hd, he, hf⟩
  · have he := production_cross_zero_except_three S hS c e m hm hm3 hc.eDegree hrr hc.rz
    have hd : d = 0 := by
      by_contra hd
      have hr : ∀ x ∈ S, (X - C x) ^ m ∣ d + (X - C x) * (b + C (2 * v x) * c) := by
        simpa [he] using hc.r
      exact hd (production_derivative_zero S hS d (fun x => b + C (2 * v x) * c)
        m hm (hc.dDegree hd) hr hc.z)
    exact ⟨hd, he, hf⟩

/-- Full quadratic contact with two decoded candidates and three polynomial
solutions is zero. The solution identities are explicit hypotheses; extracting
them from the remaining source degree caps and contact equations is separate. -/
theorem production_quadratic_zero_of_three (S H₀ H₁ : Finset K)
    (hS : S.card = 1073741823) (hH₀S : H₀ ⊆ S) (hH₁S : H₁ ⊆ S)
    (hH₀ : 715827883 ≤ H₀.card) (hH₁ : 715827883 ≤ H₁.card)
    (a b c d e f f₀ f₁ f₂ : K[X]) (v : K → K) (m : ℕ) (hm : 0 < m)
    (hc : ProductionContact S b c d e f v m)
    (hf₀degree : f₀.natDegree ≤ 536870911) (hf₁degree : f₁.natDegree ≤ 536870911)
    (hagree₀ : ∀ x ∈ H₀, f₀.eval x = v x) (hagree₁ : ∀ x ∈ H₁, f₁.eval x = v x)
    (h01 : f₀ ≠ f₁) (h02 : f₀ ≠ f₂) (h12 : f₁ ≠ f₂)
    (h0 : a + b * f₀ + c * f₀ ^ 2 + d * derivative f₀ +
      e * f₀ * derivative f₀ + f * (derivative f₀) ^ 2 = 0)
    (h1 : a + b * f₁ + c * f₁ ^ 2 + d * derivative f₁ +
      e * f₁ * derivative f₁ + f * (derivative f₁) ^ 2 = 0)
    (h2 : a + b * f₂ + c * f₂ ^ 2 + d * derivative f₂ +
      e * f₂ * derivative f₂ + f * (derivative f₂) ^ 2 = 0) :
    a = 0 ∧ b = 0 ∧ c = 0 ∧ d = 0 ∧ e = 0 ∧ f = 0 := by
  obtain ⟨hd, he, hf⟩ := production_derivative_coefficients_zero S H₀ H₁
    hS hH₀S hH₁S hH₀ hH₁ b c d e f f₀ f₁ v m hm hc hf₀degree hf₁degree
    hagree₀ hagree₁ h01
  obtain ⟨ha, hb, hc⟩ := quadratic_coefficients_zero_of_three a b c f₀ f₁ f₂
    h01 h02 h12 (by simpa [hd, he, hf] using h0) (by simpa [hd, he, hf] using h1)
    (by simpa [hd, he, hf] using h2)
  exact ⟨ha, hb, hc, hd, he, hf⟩

/-- After the derivative coefficients vanish, agreement preserves contact order. -/
theorem local_algebraic_divisibility (T a b c f v : K[X]) (m : ℕ)
    (hf : T ∣ f - v)
    (h0 : T ^ m ∣ a + b * v + c * v ^ 2)
    (h1 : T ^ m ∣ T * (b + 2 * v * c))
    (h2 : T ^ m ∣ T ^ 2 * c) : T ^ m ∣ a + b * f + c * f ^ 2 := by
  obtain ⟨g, hg⟩ := hf
  have heq : f = v + T * g := by rw [← hg]; ring
  have hg1 := dvd_mul_of_dvd_right h1 g
  have hg2 := dvd_mul_of_dvd_right h2 (g ^ 2)
  convert dvd_add (dvd_add h0 hg1) hg2 using 1
  rw [heq]
  ring

/-- The remaining source caps bound the specialized algebraic polynomial. -/
theorem specialized_degree_lt (a b c f : K[X]) (cap : ℕ) (hcap : 0 < cap)
    (ha : a ≠ 0 → a.natDegree < cap)
    (hb : b ≠ 0 → b.natDegree + 536870911 < cap)
    (hc : c ≠ 0 → c.natDegree + 1073741822 < cap)
    (hf : f.natDegree ≤ 536870911) : (a + b * f + c * f ^ 2).natDegree < cap := by
  have h0 : a.natDegree < cap := by
    by_cases h : a = 0
    · simpa [h] using hcap
    · exact ha h
  have h1 : (b * f).natDegree < cap := by
    by_cases h : b = 0
    · simpa [h] using hcap
    · have hb' := hb h
      have hd := Polynomial.natDegree_mul_le (p := b) (q := f)
      omega
  have h2 : (c * f ^ 2).natDegree < cap := by
    by_cases h : c = 0
    · simpa [h] using hcap
    · have hc' := hc h
      have hd := Polynomial.natDegree_mul_le (p := c) (q := f ^ 2)
      rw [Polynomial.natDegree_pow] at hd
      omega
  exact (Polynomial.natDegree_add_le _ _).trans_lt
    (max_lt ((Polynomial.natDegree_add_le _ _).trans_lt (max_lt h0 h1)) h2)

/-- Full coefficient conditions, including the constant contact term and all caps. -/
structure FullProductionContact (S : Finset K) (a b c d e f : K[X]) (v : K → K) (m : ℕ) : Prop
    extends ProductionContact S b c d e f v m where
  aDegree : a ≠ 0 → a.natDegree < m * 715827883
  bDegree : b ≠ 0 → b.natDegree + 536870911 < m * 715827883
  cDegree : c ≠ 0 → c.natDegree + 1073741822 < m * 715827883
  constant : ∀ x ∈ S, (X - C x) ^ m ∣ a + b * C (v x) + c * (C (v x)) ^ 2

/-- Root multiplicities extract the candidate identity from contact and degree. -/
theorem production_algebraic_solution (S H : Finset K) (hHS : H ⊆ S)
    (hH : 715827883 ≤ H.card) (a b c f : K[X]) (v : K → K) (m : ℕ) (hm : 0 < m)
    (hc : FullProductionContact S a b c 0 0 0 v m)
    (hf : f.natDegree ≤ 536870911) (hagree : ∀ x ∈ H, f.eval x = v x) :
    a + b * f + c * f ^ 2 = 0 := by
  by_contra hW
  have hlocal (x : K) (hx : x ∈ H) : (X - C x) ^ m ∣ a + b * f + c * f ^ 2 := by
    apply local_algebraic_divisibility (X - C x) a b c f (C (v x)) m
    · rw [← hagree x hx]
      exact X_sub_C_dvd_sub_C_eval
    · exact hc.constant x (hHS hx)
    · have hC : C (2 * v x) = 2 * C (v x) := by
        rw [two_mul, map_add, two_mul]
      simpa only [mul_zero, zero_add, hC] using hc.r x (hHS hx)
    · simpa using hc.rr x (hHS hx)
  have hlow := multiplicity_degree_bound H (a + b * f + c * f ^ 2) (fun _ => m) hW hlocal
  simp only [Finset.sum_const, smul_eq_mul] at hlow
  have hhigh := specialized_degree_lt a b c f (m * 715827883) (by omega)
    hc.aDegree hc.bDegree hc.cDegree hf
  have hmul := Nat.mul_le_mul_right m hH
  omega

/-- At every positive production contact order, a full quadratic source for a
received word with three distinct decoded candidates is zero. This is an
obstruction for the stated contact model, not a bound on arbitrary lists. -/
theorem production_quadratic_contact_zero (S H₀ H₁ H₂ : Finset K)
    (hS : S.card = 1073741823) (hH₀S : H₀ ⊆ S) (hH₁S : H₁ ⊆ S) (hH₂S : H₂ ⊆ S)
    (hH₀ : 715827883 ≤ H₀.card) (hH₁ : 715827883 ≤ H₁.card) (hH₂ : 715827883 ≤ H₂.card)
    (a b c d e f f₀ f₁ f₂ : K[X]) (v : K → K) (m : ℕ) (hm : 0 < m)
    (hc : FullProductionContact S a b c d e f v m)
    (hf₀ : f₀.natDegree ≤ 536870911) (hf₁ : f₁.natDegree ≤ 536870911)
    (hf₂ : f₂.natDegree ≤ 536870911)
    (hagree₀ : ∀ x ∈ H₀, f₀.eval x = v x) (hagree₁ : ∀ x ∈ H₁, f₁.eval x = v x)
    (hagree₂ : ∀ x ∈ H₂, f₂.eval x = v x)
    (h01 : f₀ ≠ f₁) (h02 : f₀ ≠ f₂) (h12 : f₁ ≠ f₂) :
    a = 0 ∧ b = 0 ∧ c = 0 ∧ d = 0 ∧ e = 0 ∧ f = 0 := by
  obtain ⟨hd, he, hf⟩ := production_derivative_coefficients_zero S H₀ H₁ hS hH₀S hH₁S
    hH₀ hH₁ b c d e f f₀ f₁ v m hm hc.toProductionContact hf₀ hf₁ hagree₀ hagree₁ h01
  have hc' : FullProductionContact S a b c 0 0 0 v m := by simpa [hd, he, hf] using hc
  have h0 := production_algebraic_solution S H₀ hH₀S hH₀ a b c f₀ v m hm hc' hf₀ hagree₀
  have h1 := production_algebraic_solution S H₁ hH₁S hH₁ a b c f₁ v m hm hc' hf₁ hagree₁
  have h2 := production_algebraic_solution S H₂ hH₂S hH₂ a b c f₂ v m hm hc' hf₂ hagree₂
  obtain ⟨ha, hb, hc⟩ := quadratic_coefficients_zero_of_three a b c f₀ f₁ f₂
    h01 h02 h12 h0 h1 h2
  exact ⟨ha, hb, hc, hd, he, hf⟩

#print axioms quadratic_contact_expansion
#print axioms local_square_divisibility
#print axioms multiplicity_degree_bound
#print axioms production_square_zero
#print axioms local_cross_divisibility
#print axioms production_cross_zero_except_three
#print axioms augmented_root_degree
#print axioms production_order_three_relation
#print axioms production_order_three_zero
#print axioms production_derivative_coefficients_zero
#print axioms production_quadratic_zero_of_three
#print axioms local_algebraic_divisibility
#print axioms specialized_degree_lt
#print axioms production_algebraic_solution
#print axioms production_quadratic_contact_zero

end AstraQuadraticContactObstruction

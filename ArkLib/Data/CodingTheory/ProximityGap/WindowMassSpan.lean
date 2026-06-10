/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.DeBruijnWeightedWindowLaw
import ArkLib.Data.CodingTheory.ProximityGap.LamLeungSpanTwoPrime

/-!
# Issue #232 — THE WINDOWED MASS-SPAN LAW: the t-general total-mass spectrum of
# the BCH-window code (the windowed Lam–Leung law)

O104 proved the Lam–Leung ℕ-span law at window length `1` (total mass of a
vanishing ℕ-weighted root sum lies in `ℕ·p + ℕ·q`); O107 pinned the **0/1**
weight spectrum at every window length `t` (weights are sums of divisors
`> t`).  This file proves their common generalization, the full
multiplicity-level mass spectrum at every `t` — the quantitative consumer of
O108's weighted windowed law:

* `mass_of_combination` — the **mass formula**: the total mass of an
  ℕ-combination of `μ_d`-coset indicators (`d ∣ n`, `d > t`) is
  `Σ_d c_d·d` with `c_d ∈ ℕ` — each coset of size `d` contributes `d` per unit
  of multiplicity (`sum_mod_fiber`).
* `window_mass_span_two_prime` — **the windowed span law**: for
  `n = p^a·q^b`, `ζ` primitive `n`-th (char 0), `t < n`, any window-`t`-
  vanishing `w : ℕ → ℕ` has `Σ_{e<n} w_e ∈ ℕ-span{d : d ∣ n, t < d}`.
* `window_min_mass_two_prime` — **the sharp minimum**: a window-`t`-vanishing
  weight with positive mass has mass `≥` the least divisor of `n` exceeding
  `t` (the weighted upgrade of O107's 0/1 minimum-weight law).
* `window_mass_sharp` — **sharpness at every divisor**: the canonical
  `μ_{d₀}`-coset indicator (`w₀ e = [e ≡ 0 mod n/d₀]`) vanishes on the whole
  window and has mass exactly `d₀`.
* `window_mass_in_prime_span` — the **O104 upgrade**: for every window length
  `t ≥ 1` (not just `t = 1`), the mass lies in `ℕ·p + ℕ·q` — every divisor
  `d > t ≥ 1` of `p^a·q^b` is a multiple of `p` or of `q`.
* Teeth at `n = 72 = 2³·3²`, `t = 9` (O107's BCH-beating instance, upgraded to
  all multiplicities): the mass spectrum below `24` is EXACTLY `{0, 12, 18}` —
  a kernel-checked **gap theorem**: no window-9-vanishing multiplicity vector
  has total mass in `(0,12) ∪ (12,18) ∪ (18,24)`.

Probe-verified before formalization (`scripts/probes/probe_window_mass_span.py`,
exact ℤ[x]/Φ_n, exhaustive over `{0,1,2}^12`, `{0,1}^18`, `{0,1}^20` at every
window length): span membership, sharp minima, and the full gap structure of
the observed mass spectra.
-/

namespace WindowMassSpan

open Finset DeBruijnWeightedWindowLaw

variable {L : Type*} [Field L]

/-- **The mass formula**: an ℕ-combination of `μ_d`-coset indicators
(`d ∣ n`, `d > t`) has total mass `Σ_d c_d·d` — each unit of multiplicity of a
`μ_d`-coset contributes exactly `d` (the fiber-counting identity per
divisor). -/
theorem mass_of_combination {n t : ℕ} {w : ℕ → ℕ}
    (h : IsWeightedWindowCombination n t w) :
    ∃ c : ℕ → ℕ, ∑ e ∈ Finset.range n, w e
      = ∑ d ∈ n.divisors.filter (t < ·), c d * d := by
  obtain ⟨A, hA⟩ := h
  refine ⟨fun d => ∑ r ∈ Finset.range (n / d), A d r, ?_⟩
  calc ∑ e ∈ Finset.range n, w e
      = ∑ e ∈ Finset.range n,
          ∑ d ∈ n.divisors.filter (t < ·), A d (e % (n / d)) :=
        Finset.sum_congr rfl fun e he => hA e (Finset.mem_range.mp he)
    _ = ∑ d ∈ n.divisors.filter (t < ·),
          ∑ e ∈ Finset.range n, A d (e % (n / d)) := Finset.sum_comm
    _ = ∑ d ∈ n.divisors.filter (t < ·),
          (∑ r ∈ Finset.range (n / d), A d r) * d := by
        refine Finset.sum_congr rfl fun d hd => ?_
        obtain ⟨hmem, htd⟩ := Finset.mem_filter.mp hd
        obtain ⟨hdn, hn0⟩ := Nat.mem_divisors.mp hmem
        have hd0 : 0 < d := by omega
        have hm0 : 0 < n / d :=
          Nat.div_pos (Nat.le_of_dvd (Nat.pos_of_ne_zero hn0) hdn) hd0
        have hsplit : (n / d) * d = n := Nat.div_mul_cancel hdn
        rw [show Finset.range n = Finset.range ((n / d) * d) from by rw [hsplit],
          LamLeungSpanTwoPrime.sum_mod_fiber (A d) (n / d) d hm0]
        exact Nat.mul_comm _ _

/-- **THE WINDOWED MASS-SPAN LAW** (two-prime): the total mass of any
window-`t`-vanishing ℕ-weighted root sum at `n = p^a·q^b` lies in the ℕ-span
of the divisors of `n` exceeding `t`.  At `t = 1` this is O104's Lam–Leung
span law; at 0/1 weights it is O107's weight spectrum; this is the common
generalization. -/
theorem window_mass_span_two_prime [CharZero L]
    {p q a b : ℕ} (hp : p.Prime) (hq : q.Prime) (hpq : p ≠ q)
    {ζ : L} (hζ : IsPrimitiveRoot ζ (p ^ a * q ^ b)) (w : ℕ → ℕ)
    {t : ℕ} (htn : t < p ^ a * q ^ b)
    (hwin : ∀ j, 1 ≤ j → j ≤ t →
        ∑ e ∈ Finset.range (p ^ a * q ^ b), (w e : L) * ζ ^ (j * e) = 0) :
    ∃ c : ℕ → ℕ, ∑ e ∈ Finset.range (p ^ a * q ^ b), w e
      = ∑ d ∈ (p ^ a * q ^ b).divisors.filter (t < ·), c d * d :=
  mass_of_combination
    ((weighted_windowed_two_prime hp hq hpq hζ w htn).mp hwin)

/-- **The sharp minimum mass**: a window-`t`-vanishing ℕ-weight with positive
total mass has mass at least `d₀`, for `d₀` any lower bound on the divisors of
`n = p^a·q^b` exceeding `t` — the all-multiplicities upgrade of O107's 0/1
minimum-weight law. -/
theorem window_min_mass_two_prime [CharZero L]
    {p q a b : ℕ} (hp : p.Prime) (hq : q.Prime) (hpq : p ≠ q)
    {ζ : L} (hζ : IsPrimitiveRoot ζ (p ^ a * q ^ b)) (w : ℕ → ℕ)
    {t : ℕ} (htn : t < p ^ a * q ^ b)
    (hwin : ∀ j, 1 ≤ j → j ≤ t →
        ∑ e ∈ Finset.range (p ^ a * q ^ b), (w e : L) * ζ ^ (j * e) = 0)
    (hpos : 0 < ∑ e ∈ Finset.range (p ^ a * q ^ b), w e)
    {d₀ : ℕ} (hmin : ∀ d, d ∣ p ^ a * q ^ b → t < d → d₀ ≤ d) :
    d₀ ≤ ∑ e ∈ Finset.range (p ^ a * q ^ b), w e := by
  obtain ⟨c, hc⟩ := window_mass_span_two_prime hp hq hpq hζ w htn hwin
  rw [hc] at hpos ⊢
  have hex : ∃ d ∈ (p ^ a * q ^ b).divisors.filter (t < ·), 0 < c d * d := by
    by_contra hno
    have hzero : ∑ d ∈ (p ^ a * q ^ b).divisors.filter (t < ·), c d * d = 0 :=
      Finset.sum_eq_zero fun d hd => by
        rcases Nat.eq_zero_or_pos (c d * d) with h | h
        · exact h
        · exact absurd ⟨d, hd, h⟩ hno
    omega
  obtain ⟨d, hd, hcd⟩ := hex
  obtain ⟨hmem, htd⟩ := Finset.mem_filter.mp hd
  obtain ⟨hdn, _⟩ := Nat.mem_divisors.mp hmem
  have hc0 : 0 < c d := by
    rcases Nat.eq_zero_or_pos (c d) with h0 | h
    · rw [h0, zero_mul] at hcd
      omega
    · exact h
  calc d₀ ≤ d := hmin d hdn htd
    _ ≤ c d * d := Nat.le_mul_of_pos_left d hc0
    _ ≤ ∑ d ∈ (p ^ a * q ^ b).divisors.filter (t < ·), c d * d :=
        Finset.single_le_sum (f := fun d => c d * d)
          (fun i _ => Nat.zero_le _) hd

/-- **Sharpness at every divisor**: for any divisor `d₀ ∣ n` with `t < d₀`,
the canonical `μ_{d₀}`-coset indicator `w₀ e = [e % (n/d₀) = 0]` kills the
whole window `1 ≤ j ≤ t` and has total mass exactly `d₀` — every divisor
exceeding `t` is an achieved mass.  (Works at ANY modulus `n`; the two-prime
hypothesis is only needed for the converse direction.) -/
theorem window_mass_sharp [CharZero L] {n t d₀ : ℕ} (hn : 0 < n)
    (hd₀ : d₀ ∣ n) (htd : t < d₀) {ζ : L} (hζ : IsPrimitiveRoot ζ n) :
    (∀ j, 1 ≤ j → j ≤ t →
        ∑ e ∈ Finset.range n,
          ((if e % (n / d₀) = 0 then 1 else 0 : ℕ) : L) * ζ ^ (j * e) = 0)
      ∧ (∑ e ∈ Finset.range n, (if e % (n / d₀) = 0 then 1 else 0)) = d₀ := by
  have hd0 : 0 < d₀ := by omega
  have hm0 : 0 < n / d₀ := Nat.div_pos (Nat.le_of_dvd hn hd₀) hd0
  have hsplit : (n / d₀) * d₀ = n := Nat.div_mul_cancel hd₀
  have hmem : d₀ ∈ n.divisors.filter (t < ·) :=
    Finset.mem_filter.mpr ⟨Nat.mem_divisors.mpr ⟨hd₀, hn.ne'⟩, htd⟩
  have hcomb : IsWeightedWindowCombination n t
      (fun e => if e % (n / d₀) = 0 then 1 else 0) := by
    refine ⟨fun d r => if d = d₀ ∧ r = 0 then 1 else 0, fun e _ => ?_⟩
    rw [Finset.sum_eq_single d₀
      (fun d _ hne => if_neg fun hcon => hne hcon.1)
      (fun habs => absurd hmem habs)]
    by_cases h0 : e % (n / d₀) = 0
    · simp [h0]
    · simp [h0]
  refine ⟨window_vanishes_of_combination hn hζ hcomb, ?_⟩
  rw [show Finset.range n = Finset.range ((n / d₀) * d₀) from by rw [hsplit],
    LamLeungSpanTwoPrime.sum_mod_fiber (fun r => if r = 0 then 1 else 0)
      (n / d₀) d₀ hm0,
    Finset.sum_ite_eq' (Finset.range (n / d₀)) 0 (fun _ => 1),
    if_pos (Finset.mem_range.mpr hm0), mul_one]

/-- **The O104 upgrade**: at every window length `t ≥ 1` (O104 is the case
`t = 1`), the total mass of a window-`t`-vanishing ℕ-weight at `n = p^a·q^b`
lies in `ℕ·p + ℕ·q` — every divisor `d > t ≥ 1` of `n` is a multiple of `p`
or of `q`, so the divisor span refines into the prime span. -/
theorem window_mass_in_prime_span [CharZero L]
    {p q a b : ℕ} (hp : p.Prime) (hq : q.Prime) (hpq : p ≠ q)
    {ζ : L} (hζ : IsPrimitiveRoot ζ (p ^ a * q ^ b)) (w : ℕ → ℕ)
    {t : ℕ} (ht1 : 1 ≤ t) (htn : t < p ^ a * q ^ b)
    (hwin : ∀ j, 1 ≤ j → j ≤ t →
        ∑ e ∈ Finset.range (p ^ a * q ^ b), (w e : L) * ζ ^ (j * e) = 0) :
    ∃ i j : ℕ, ∑ e ∈ Finset.range (p ^ a * q ^ b), w e = i * p + j * q := by
  obtain ⟨c, hc⟩ := window_mass_span_two_prime hp hq hpq hζ w htn hwin
  set F := (p ^ a * q ^ b).divisors.filter (t < ·) with hF
  refine ⟨∑ d ∈ F.filter (p ∣ ·), c d * (d / p),
    ∑ d ∈ F.filter (fun d => ¬ p ∣ d), c d * (d / q), ?_⟩
  rw [hc, ← Finset.sum_filter_add_sum_filter_not F (p ∣ ·) (fun d => c d * d),
    Finset.sum_mul, Finset.sum_mul]
  congr 1
  · refine Finset.sum_congr rfl fun d hd => ?_
    have hpd : p ∣ d := (Finset.mem_filter.mp hd).2
    rw [mul_assoc, Nat.div_mul_cancel hpd]
  · refine Finset.sum_congr rfl fun d hd => ?_
    obtain ⟨hdF, hnpd⟩ := Finset.mem_filter.mp hd
    obtain ⟨hmem, htd⟩ := Finset.mem_filter.mp hdF
    obtain ⟨hdn, _⟩ := Nat.mem_divisors.mp hmem
    have hcop : Nat.Coprime p d := (Nat.Prime.coprime_iff_not_dvd hp).mpr hnpd
    have hdq : d ∣ q ^ b :=
      Nat.Coprime.dvd_of_dvd_mul_left (hcop.symm.pow_right a) hdn
    have hqd : q ∣ d := by
      obtain ⟨k, hk, rfl⟩ := (Nat.dvd_prime_pow hq).mp hdq
      have hk0 : k ≠ 0 := by
        rintro rfl
        rw [pow_zero] at htd
        omega
      exact dvd_pow_self q hk0
    rw [mul_assoc, Nat.div_mul_cancel hqd]

/-! ## Teeth: the mass GAP theorem at O107's BCH-beating instance

At `n = 72 = 2³·3²` with window `t = 9` the divisors exceeding `9` are
`{12, 18, 24, 36, 72}`; the span law pins the entire mass spectrum below `24`
to `{0, 12, 18}` — no window-9-vanishing multiplicity vector has total mass
`1..11`, `13..17`, or `19..23`.  (O107 gave the 0/1 minimum `12`; this is the
full gap structure at every multiplicity.)  Sharpness: masses `12` and `18`
are realized by `window_mass_sharp` at `d₀ = 12, 18`. -/

example [CharZero L] {ζ : L} (hζ : IsPrimitiveRoot ζ (2 ^ 3 * 3 ^ 2))
    (w : ℕ → ℕ)
    (hwin : ∀ j, 1 ≤ j → j ≤ 9 →
        ∑ e ∈ Finset.range (2 ^ 3 * 3 ^ 2), (w e : L) * ζ ^ (j * e) = 0)
    (hmass : ∑ e ∈ Finset.range (2 ^ 3 * 3 ^ 2), w e < 24) :
    ∑ e ∈ Finset.range (2 ^ 3 * 3 ^ 2), w e = 0
      ∨ ∑ e ∈ Finset.range (2 ^ 3 * 3 ^ 2), w e = 12
      ∨ ∑ e ∈ Finset.range (2 ^ 3 * 3 ^ 2), w e = 18 := by
  obtain ⟨c, hc⟩ := window_mass_span_two_prime Nat.prime_two Nat.prime_three
    (by norm_num) hζ w (by norm_num) hwin
  have hfil : ((2 ^ 3 * 3 ^ 2 : ℕ)).divisors.filter (9 < ·)
      = {12, 18, 24, 36, 72} := by decide
  rw [hfil, Finset.sum_insert (by decide), Finset.sum_insert (by decide),
    Finset.sum_insert (by decide), Finset.sum_insert (by decide),
    Finset.sum_singleton] at hc
  omega

end WindowMassSpan

#print axioms WindowMassSpan.mass_of_combination
#print axioms WindowMassSpan.window_mass_span_two_prime
#print axioms WindowMassSpan.window_min_mass_two_prime
#print axioms WindowMassSpan.window_mass_sharp
#print axioms WindowMassSpan.window_mass_in_prime_span

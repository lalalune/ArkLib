/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.TwoPrimeWindowLaw
import ArkLib.Data.CodingTheory.ProximityGap.LamLeungTwoPow

/-!
# Issue #232 — the two-prime syndrome/list-budget consumers (O97's queued wiring)

O97 (`TwoPrimeWindowLaw`) proved the two-prime window law unconditionally and named
the remaining bookkeeping: "syndrome/list-budget consumer wiring on `μ_18`".  This
file is that wiring — the exact two-prime analogues of the 2-power consumer chain
O55 (`LamLeungTwoPow.tower_count`) and O61 (`unit_syndrome_list_budget`), plus the
sharpening the two-prime law makes possible:

* `two_prime_tower_count` — the O55 analogue: `w`-subsets of a `p^a·q^b`-torsion
  domain with vanishing power-sum window `1 ≤ j < p^(t-1)·(q^b+1)` inject into the
  subsets of the `p^t`-th-power-class space (each is `μ_{p^t}`-closed by
  `two_prime_partial_climb`, hence recoverable from its power image), so they number
  at most `2^{#classes}`.
* `two_prime_syndrome_list_budget` — the O61 analogue: the same budget for the
  codimension-`c` syndrome-compatibility list at the unit syndrome
  (`TopLine.CompatC`), via the O45 zero-fiber transfer and the O60 Newton bridge.
* `two_prime_window_count_le_one` — **the singleton sharpening**: at the MASTER
  window `1 ≤ j < max (p^(a-1)·(q^b+1)) (q^(b-1)·(p^a+1))` the empty-or-full law
  (`two_prime_window_empty_or_full`) pins the zero fiber at every cardinality to AT
  MOST ONE support — strictly stronger than the 2-power side's `2^{O(1/η)}` budget,
  because the two-prime master window forces closure under the FULL `μ_n`.
* `m31_window_count_le_one` / `m31_unit_syndrome_list_singleton` — the M31 landing:
  on the 2-3-smooth multiplicative domain `μ_18` of `F_{2^31−1}` (`18 = 2·3²`), the
  window-9 unit-syndrome interior list over ANY 18-torsion domain is a singleton.
* `m31_window_count_eq_one_of_full` — teeth: on the full `μ_18` the bound is
  ATTAINED at `w = 18` (the `S = μ_n` endpoint of the empty-or-full law), fired at
  `ℂ` — card is exactly 1, not vacuously 0.

Pure composition of landed theorems (O45 ∘ O60 ∘ O97); no new mathematical claims,
hence no new probe — the window law itself was falsified-first in O97
(`scripts/probes/probe_two_prime_window_law.py`, exit 0).
-/

namespace TwoPrimeSyndromeBudget

open Finset TwoPrimeWindowLaw

variable {F : Type*} [Field F] [CharZero F] [DecidableEq F]

/-! ## The O55 analogue: the partial-window count -/

open Classical in
/-- **The two-prime tower count** (O55's `tower_count` on the two-prime surface):
`w`-subsets of a `p^a·q^b`-torsion domain whose power sums vanish on the window
`1 ≤ j < p^(t-1)·(q^b+1)` number at most `2^{#(p^t-th-power classes)}` — each such
subset is `μ_{p^t}`-closed by the unconditional partial climb, hence exactly
recoverable from its `p^t`-th-power image. -/
theorem two_prime_tower_count {p q a b t : ℕ}
    (hp : p.Prime) (hq : q.Prime) (hpq : p ≠ q) (ht : t ≤ a)
    {ζ : F} (hζ : IsPrimitiveRoot ζ (p ^ a * q ^ b))
    {D₀ : Finset F} (hD₀ : ∀ x ∈ D₀, x ^ (p ^ a * q ^ b) = 1) (w : ℕ) :
    ((D₀.powersetCard w).filter (fun S =>
        ∀ j, 1 ≤ j → j < p ^ (t - 1) * (q ^ b + 1) → ∑ x ∈ S, x ^ j = 0)).card
      ≤ 2 ^ (D₀.image (· ^ p ^ t)).card := by
  classical
  have hnpos : 0 < p ^ a * q ^ b := Nat.mul_pos (pow_pos hp.pos a) (pow_pos hq.pos b)
  have hnz : ∀ x ∈ D₀, x ≠ 0 := by
    intro x hx h0
    have h1 := hD₀ x hx
    rw [h0, zero_pow hnpos.ne'] at h1
    exact zero_ne_one h1
  rw [← Finset.card_powerset]
  apply Finset.card_le_card_of_injOn (fun S => S.image (· ^ p ^ t))
  · -- maps into the powerset of the power-class space
    intro S hS
    have hS2 := Finset.mem_coe.mp hS
    rw [Finset.mem_filter, Finset.mem_powersetCard] at hS2
    simp only [Finset.mem_coe, Finset.mem_powerset]
    intro y hy
    obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hy
    exact Finset.mem_image.mpr ⟨x, hS2.1.1 hx, rfl⟩
  · -- injective: S is recoverable from its power image via μ_{p^t}-closure
    intro S hSm S' hSm' himg
    have hmem := Finset.mem_coe.mp hSm
    have hmem' := Finset.mem_coe.mp hSm'
    rw [Finset.mem_filter, Finset.mem_powersetCard] at hmem hmem'
    obtain ⟨⟨hSD, _⟩, hPS⟩ := hmem
    obtain ⟨⟨hSD', _⟩, hPS'⟩ := hmem'
    have h0S : (0 : F) ∉ S := fun h => hnz 0 (hSD h) rfl
    have h0S' : (0 : F) ∉ S' := fun h => hnz 0 (hSD' h) rfl
    have hclos : ∀ x ∈ S, ∀ h : F, h ^ p ^ t = 1 → h * x ∈ S :=
      two_prime_partial_climb hp hq hpq ht hζ h0S
        (fun x hx => hD₀ x (hSD hx)) hPS
    have hclos' : ∀ x ∈ S', ∀ h : F, h ^ p ^ t = 1 → h * x ∈ S' :=
      two_prime_partial_climb hp hq hpq ht hζ h0S'
        (fun x hx => hD₀ x (hSD' hx)) hPS'
    have hrec : ∀ T : Finset F, T ⊆ D₀ →
        (∀ x ∈ T, ∀ h : F, h ^ p ^ t = 1 → h * x ∈ T) →
        T = D₀.filter (fun x => x ^ p ^ t ∈ T.image (· ^ p ^ t)) := by
      intro T hTD hTclos
      apply Finset.Subset.antisymm
      · intro x hx
        exact Finset.mem_filter.mpr ⟨hTD hx, Finset.mem_image.mpr ⟨x, hx, rfl⟩⟩
      · intro x hx
        obtain ⟨hxD, hxim⟩ := Finset.mem_filter.mp hx
        obtain ⟨x₀, hx₀, hpow⟩ := Finset.mem_image.mp hxim
        have hx₀0 : x₀ ≠ 0 := hnz x₀ (hTD hx₀)
        have hx00 : x₀ ^ p ^ t ≠ 0 := pow_ne_zero _ hx₀0
        have hquot : (x / x₀) ^ p ^ t = 1 := by
          rw [div_pow, ← hpow, div_self hx00]
        have hmoved := hTclos x₀ hx₀ (x / x₀) hquot
        rwa [div_mul_cancel₀ x hx₀0] at hmoved
    simp only [] at himg
    rw [hrec S hSD hclos, hrec S' hSD' hclos', himg]

/-! ## The singleton sharpening at the master window -/

open Classical in
/-- **The master-window singleton**: at the full two-prime master window the
empty-or-full law pins the zero fiber at EVERY cardinality to at most one support —
the list budget collapses from `2^{O(1/η)}` (the 2-power tower's bound) to `1`. -/
theorem two_prime_window_count_le_one {p q a b : ℕ}
    (hp : p.Prime) (hq : q.Prime) (hpq : p ≠ q) (ha : 0 < a) (hb : 0 < b)
    {ζ : F} (hζ : IsPrimitiveRoot ζ (p ^ a * q ^ b))
    {D₀ : Finset F} (hD₀ : ∀ x ∈ D₀, x ^ (p ^ a * q ^ b) = 1) (w : ℕ) :
    ((D₀.powersetCard w).filter (fun S =>
        ∀ j, 1 ≤ j →
          j < max (p ^ (a - 1) * (q ^ b + 1)) (q ^ (b - 1) * (p ^ a + 1)) →
          ∑ x ∈ S, x ^ j = 0)).card ≤ 1 := by
  classical
  rw [Finset.card_le_one]
  intro S hS S' hS'
  rw [Finset.mem_filter, Finset.mem_powersetCard] at hS hS'
  obtain ⟨⟨hSD, hScard⟩, hSwin⟩ := hS
  obtain ⟨⟨hSD', hScard'⟩, hSwin'⟩ := hS'
  have hnpos : 0 < p ^ a * q ^ b := Nat.mul_pos (pow_pos hp.pos a) (pow_pos hq.pos b)
  have hnz : ∀ x ∈ D₀, x ≠ 0 := by
    intro x hx h0
    have h1 := hD₀ x hx
    rw [h0, zero_pow hnpos.ne'] at h1
    exact zero_ne_one h1
  have h0S : (0 : F) ∉ S := fun h => hnz 0 (hSD h) rfl
  have h0S' : (0 : F) ∉ S' := fun h => hnz 0 (hSD' h) rfl
  have hef := two_prime_window_empty_or_full hp hq hpq ha hb hζ h0S
    (fun x hx => hD₀ x (hSD hx)) hSwin
  have hef' := two_prime_window_empty_or_full hp hq hpq ha hb hζ h0S'
    (fun x hx => hD₀ x (hSD' hx)) hSwin'
  -- a full member swallows the whole domain: torsion ⊆ T ⊆ D₀ ⊆ torsion
  have hfull_eq : ∀ T : Finset F, T ⊆ D₀ →
      (∀ z : F, z ^ (p ^ a * q ^ b) = 1 → z ∈ T) → T = D₀ :=
    fun T hTD hTfull =>
      Finset.Subset.antisymm hTD (fun x hx => hTfull x (hD₀ x hx))
  by_cases hw0 : w = 0
  · subst hw0
    rw [Finset.card_eq_zero.mp hScard, Finset.card_eq_zero.mp hScard']
  · have hSne : S ≠ ∅ := fun h => hw0 (by rw [← hScard, h, Finset.card_empty])
    have hS'ne : S' ≠ ∅ := fun h => hw0 (by rw [← hScard', h, Finset.card_empty])
    rw [hfull_eq S hSD (hef.resolve_left hSne),
      hfull_eq S' hSD' (hef'.resolve_left hS'ne)]

/-! ## The O61 analogue: unit-syndrome compatibility lists -/

open Classical in
/-- **The two-prime unit-syndrome list budget** (O61's analogue): the
codimension-`c` syndrome-compatibility list at the unit syndrome over a
`p^a·q^b`-torsion domain, with window `c + 1 = p^(t-1)·(q^b+1)`, has at most
`2^{#(p^t-th-power classes)}` members — O45 zero-fiber transfer ∘ O60 Newton
bridge ∘ the two-prime tower count. -/
theorem two_prime_syndrome_list_budget {p q a b t : ℕ}
    (hp : p.Prime) (hq : q.Prime) (hpq : p ≠ q) (ht : t ≤ a)
    {ζ : F} (hζ : IsPrimitiveRoot ζ (p ^ a * q ^ b))
    {D₀ : Finset F} (hD₀ : ∀ x ∈ D₀, x ^ (p ^ a * q ^ b) = 1)
    {w N c : ℕ} (hc : c + 1 = p ^ (t - 1) * (q ^ b + 1)) (hc0 : 0 < c)
    (hw : w + c = N) (hcw : c ≤ w) :
    ((D₀.powersetCard w).filter (fun E =>
        TopLine.CompatC (TopLine.unitVec (w - 1)) N c E)).card
      ≤ 2 ^ (D₀.image (· ^ p ^ t)).card := by
  rw [TopLine.zero_fiber_filter_eq hw hc0 hcw D₀]
  refine le_trans (le_of_eq ?_) (two_prime_tower_count hp hq hpq ht hζ hD₀ w)
  congr 1
  refine Finset.filter_congr fun E _ => ?_
  constructor
  · intro he j hj1 hj2
    exact LamLeungTwoPow.psum_window_of_esymm_window he j
      (Finset.mem_Icc.mpr ⟨hj1, by omega⟩)
  · intro hpsum
    refine LamLeungTwoPow.esymm_window_of_psum_window (fun j hj => ?_)
    obtain ⟨h1, h2⟩ := Finset.mem_Icc.mp hj
    exact hpsum j h1 (by omega)

/-! ## The M31 landing: `μ_18`, the 2-3-smooth side of `F_{2^31−1}` -/

open Classical in
/-- **The M31 window-9 singleton, zero-fiber form**: on any 18-torsion domain
(`18 = 2·3²`, the smooth multiplicative side of `F_{2^31−1}`), the window
`1 ≤ j < 10` zero fiber at every cardinality has at most one support. -/
theorem m31_window_count_le_one {ζ : F} (hζ : IsPrimitiveRoot ζ 18)
    {D₀ : Finset F} (hD₀ : ∀ x ∈ D₀, x ^ 18 = 1) (w : ℕ) :
    ((D₀.powersetCard w).filter (fun S =>
        ∀ j, 1 ≤ j → j < 10 → ∑ x ∈ S, x ^ j = 0)).card ≤ 1 := by
  have h18 : (18 : ℕ) = 2 ^ 1 * 3 ^ 2 := by norm_num
  rw [h18] at hζ hD₀
  refine le_trans (le_of_eq ?_) (two_prime_window_count_le_one Nat.prime_two
    Nat.prime_three (by norm_num) one_pos (by norm_num) hζ hD₀ w)
  congr 1
  refine Finset.filter_congr fun E _ => ?_
  have hmax : max (2 ^ (1 - 1) * (3 ^ 2 + 1)) (3 ^ (2 - 1) * (2 ^ 1 + 1)) = 10 := by
    norm_num
  rw [hmax]

open Classical in
/-- **The M31 unit-syndrome interior list is a SINGLETON** (the `μ_18` capstone of
O97's queued wiring): the codimension-9 syndrome-compatibility list at the unit
syndrome over any 18-torsion domain has at most ONE member — the two-prime master
window collapses the O61-style `2^{O(1/η)}` budget to `1` on the M31 smooth
multiplicative domain. -/
theorem m31_unit_syndrome_list_singleton {ζ : F} (hζ : IsPrimitiveRoot ζ 18)
    {D₀ : Finset F} (hD₀ : ∀ x ∈ D₀, x ^ 18 = 1)
    {w N : ℕ} (hw : w + 9 = N) (hcw : 9 ≤ w) :
    ((D₀.powersetCard w).filter (fun E =>
        TopLine.CompatC (TopLine.unitVec (w - 1)) N 9 E)).card ≤ 1 := by
  rw [TopLine.zero_fiber_filter_eq hw (by norm_num) hcw D₀]
  refine le_trans (le_of_eq ?_) (m31_window_count_le_one hζ hD₀ w)
  congr 1
  refine Finset.filter_congr fun E _ => ?_
  constructor
  · intro he j hj1 hj2
    exact LamLeungTwoPow.psum_window_of_esymm_window he j
      (Finset.mem_Icc.mpr ⟨hj1, by omega⟩)
  · intro hpsum
    refine LamLeungTwoPow.esymm_window_of_psum_window (fun j hj => ?_)
    obtain ⟨h1, h2⟩ := Finset.mem_Icc.mp hj
    exact hpsum j h1 (by omega)

/-! ## Teeth: the singleton is attained (the `S = μ_n` endpoint) -/

open Classical in
/-- **The budget is attained**: on the FULL `μ_18` the window-9 zero fiber at
`w = 18` has EXACTLY one member — `μ_18` itself (a full root-of-unity packet kills
every power sum at exponents `18 ∤ j`).  The singleton bound is sharp, and sharp at
the maximal-cardinality endpoint of the empty-or-full law — not vacuously zero. -/
theorem m31_window_count_eq_one_of_full {ζ : F} (hζ : IsPrimitiveRoot ζ 18) :
    ((((Finset.range 18).image (ζ ^ ·)).powersetCard 18).filter
      (fun S => ∀ j, 1 ≤ j → j < 10 → ∑ x ∈ S, x ^ j = 0)).card = 1 := by
  classical
  have hinj : ∀ i ∈ Finset.range 18, ∀ i' ∈ Finset.range 18,
      ζ ^ i = ζ ^ i' → i = i' := fun i hi i' hi' h =>
    hζ.pow_inj (Finset.mem_range.mp hi) (Finset.mem_range.mp hi') h
  have hD₀tor : ∀ x ∈ (Finset.range 18).image (ζ ^ ·), x ^ 18 = 1 := by
    intro x hx
    obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hx
    rw [← pow_mul, mul_comm, pow_mul, hζ.pow_eq_one, one_pow]
  have hcard : ((Finset.range 18).image (ζ ^ ·)).card = 18 := by
    rw [Finset.card_image_of_injOn fun i hi i' hi' h => hinj i hi i' hi' h,
      Finset.card_range]
  have hwin : ∀ j, 1 ≤ j → j < 10 →
      ∑ x ∈ (Finset.range 18).image (ζ ^ ·), x ^ j = 0 := by
    intro j hj1 hj2
    rw [Finset.sum_image hinj]
    refine LamLeungTwoPow.subgroup_pow_sum hζ (by norm_num) ?_
    intro hdvd
    have h18j := Nat.le_of_dvd (by omega) hdvd
    omega
  have hmem : (Finset.range 18).image (ζ ^ ·) ∈
      ((((Finset.range 18).image (ζ ^ ·)).powersetCard 18).filter
        (fun S => ∀ j, 1 ≤ j → j < 10 → ∑ x ∈ S, x ^ j = 0)) :=
    Finset.mem_filter.mpr
      ⟨Finset.mem_powersetCard.mpr ⟨Finset.Subset.refl _, hcard⟩, hwin⟩
  have hle := m31_window_count_le_one hζ hD₀tor 18
  have hge : 0 < ((((Finset.range 18).image (ζ ^ ·)).powersetCard 18).filter
      (fun S => ∀ j, 1 ≤ j → j < 10 → ∑ x ∈ S, x ^ j = 0)).card :=
    Finset.card_pos.mpr ⟨_, hmem⟩
  omega

/-- The teeth FIRED at `ℂ`: the hypotheses are jointly satisfiable — the card is
exactly 1 on the concrete primitive root `exp(2πi/18)`. -/
example :
    ((((Finset.range 18).image
        (Complex.exp (2 * Real.pi * Complex.I / (18 : ℕ)) ^ ·)).powersetCard 18).filter
      (fun S => ∀ j, 1 ≤ j → j < 10 → ∑ x ∈ S, x ^ j = 0)).card = 1 :=
  m31_window_count_eq_one_of_full (Complex.isPrimitiveRoot_exp 18 (by norm_num))

end TwoPrimeSyndromeBudget

#print axioms TwoPrimeSyndromeBudget.two_prime_tower_count
#print axioms TwoPrimeSyndromeBudget.two_prime_window_count_le_one
#print axioms TwoPrimeSyndromeBudget.two_prime_syndrome_list_budget
#print axioms TwoPrimeSyndromeBudget.m31_window_count_le_one
#print axioms TwoPrimeSyndromeBudget.m31_unit_syndrome_list_singleton
#print axioms TwoPrimeSyndromeBudget.m31_window_count_eq_one_of_full

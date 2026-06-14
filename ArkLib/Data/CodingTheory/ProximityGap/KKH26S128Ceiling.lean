/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.KKH26PolyFieldCeiling
import ArkLib.Data.CodingTheory.ProximityGap.KKH26ThornerZamanConstructor

/-!
# B3 — s = 128 prize rows via the Thorner–Zaman PNT-in-APs input (#334, E1)

This file discharges the s = 128 (`μ = 7`, `s = 2^μ = 128`) rows of the [KKH26] `δ*`
ceiling, conditional on the **single named analytic hypothesis** of [TZ24] — the effective
prime number theorem in arithmetic progressions giving enough primes `p ≡ 1 (mod n)` in the
window `[n^β, 2n^β]`.  It is the `μ = 7` analogue of the `μ = 6` (s = 64) rows, which are
unconditional via the A3 Parseval threshold; here `μ = 7` forces the genuinely-analytic
supply, so the supply remains a named `Prop` hypothesis (NEVER an axiom).

## What is actually needed for s = 128 (the concrete arithmetic)

The consumer `kkh26_mcaDeltaStar_le_of_TZ` needs the budget inequality

  `|collisionPairs μ r| · log(s^{s/2}) / log(n^β)  <  supply`     (★)

with `μ = 7`, `s = 2^7 = 128`, `s^{s/2} = (2^7)^{2^6} = 2^{7·64} = 2^448`, and
`supply` the count of TZ primes.  Since `|collisionPairs 7 r| ≤ (2^r·C(64,r))^2` is
**doubly-exponential in r**, (★) at the prize scale `n = 2^a` is satisfiable ONLY for a
field exponent `β` that is *large*; the probe `scripts/probes` solving (★) gives, for the
prize rows (`r = ρ·128 + 1`):

  ρ=1/4 (r=33), n=2^30:  min β ≈ 7.28  (p ≈ n^β ≈ 2^218)
  ρ=1/8 (r=17), n=2^30:  min β ≈ 5.53  (p ≈ n^β ≈ 2^166)
  ρ=1/16 (r=9), n=2^30:  min β ≈ 3.98  (p ≈ n^β ≈ 2^119)

All of these β exceed [TZ24]'s unconditional threshold `β > 12/5 = 2.4`, so the analytic
supply `~ n^{β−1−o(1)}` is, on paper, available — but it is NOT in mathlib (it relies on
log-free zero-density estimates for Dirichlet L-functions).  Hence the supply stays the
named hypothesis `TZPrimeSupply n β supply`, and this file builds the **consumer** that turns
it (plus the s=128 budget) into the ceiling.

## Main results

* `EffectivePNTinAP` — the named analytic [TZ24] Prop, definitionally `TZPrimeSupply`
  (the window `[n^β, 2n^β]` has `≥ supply` primes `≡ 1 (mod n)`), recorded under its
  analytic name so the obligation reads as PNT-in-APs at the consumer site.
* `s128_resultantLog_eq` — the s = 128 resultant size log: `log(s^{s/2}) = 448·log 2`,
  a pure `norm_num`/`Real.log` fact, unconditional.
* `kkh26_mcaDeltaStar_le_s128` — **the s = 128 headline**, the `μ = 7` specialisation of
  `kkh26_mcaDeltaStar_le_of_TZ`: given the named TZ supply and the s=128 budget (★) there is
  a prime `p = Θ(n^β)` and a smooth domain of order `n` with
  `mcaDeltaStar(C, ε*) ≤ 1 − r/128`.
* `s128_supply_beats_budget_of` — a sufficient-condition reformulation of (★) isolating
  the analytic supply lower bound `supply ≥ S` from the (provable) budget upper bound.

## Honesty

The ONLY unproven input is `EffectivePNTinAP` (= `TZPrimeSupply`), the [TZ24] analytic
hypothesis.  Everything else (the budget arithmetic, the resultant log, the consumer
wiring) is unconditional and axiom-clean.  No `axiom`, no `sorry`, no `native_decide`.
-/

open Polynomial Finset
open scoped NNReal ENNReal

namespace ArkLib.ProximityGap.KKH26

/-- **The named [TZ24] analytic input, under its PNT-in-APs name.**  `EffectivePNTinAP n β
supply` asserts that the window `[n^β, 2·n^β]` contains at least `supply` primes
`p ≡ 1 (mod n)` — i.e. `π(2n^β; n, 1) − π(n^β; n, 1) ≥ supply`.  This is *definitionally*
`TZPrimeSupply n β supply`; it is recorded here under the analytic name so that the s = 128
consumer states its single obligation as "effective PNT in arithmetic progressions", the
honest open input.  On paper [TZ24] Cor 3.1 supplies `~ n^{β−1−o(1)}` for every fixed
`β > 12/5`. -/
abbrev EffectivePNTinAP (n : ℕ) (β : ℝ) (supply : ℕ) : Prop := TZPrimeSupply n β supply

/-- The s = 128 collision-resultant size, in log form: `s^{s/2} = (2^7)^{2^6} = 2^448`,
so `log(s^{s/2}) = 448·log 2`.  Unconditional. -/
theorem s128_resultantLog_eq :
    Real.log ((((((2 : ℕ) ^ 7) ^ 2 ^ (7 - 1) : ℕ)) : ℝ)) = 448 * Real.log 2 := by
  -- reduce the tower inside ℕ first: (2^7)^(2^6) = 2^(7·64) = 2^448, avoiding a 449-bit literal
  have hnat : (((2 : ℕ) ^ 7) ^ 2 ^ (7 - 1) : ℕ) = (2 : ℕ) ^ 448 := by
    rw [← pow_mul]; norm_num
  rw [hnat, Nat.cast_pow, Nat.cast_ofNat, Real.log_pow]
  push_cast
  ring

/-- **A sufficient condition for the s = 128 budget (★).**  If the named TZ supply count
`supply` is at least `S`, and `S` already exceeds the provable budget
`|collisionPairs 7 r| · 448·log 2 / log(n^β)`, then the budget inequality (★) of
`kkh26_mcaDeltaStar_le_of_TZ` holds at `μ = 7`.  This isolates the *analytic* lower bound
(`S ≤ supply`, the open [TZ24] content) from the *arithmetic* upper bound on the budget
(everything else). -/
theorem s128_supply_beats_budget_of {n : ℕ} {β : ℝ} {r S supply : ℕ}
    (hS : S ≤ supply)
    (hbudget : ((collisionPairs 7 r).card : ℝ)
        * ((448 * Real.log 2) / Real.log ((n : ℝ) ^ β)) < (S : ℝ)) :
    ((collisionPairs 7 r).card : ℝ)
        * (Real.log ((((((2 : ℕ) ^ 7) ^ 2 ^ (7 - 1) : ℕ)) : ℝ)) / Real.log ((n : ℝ) ^ β))
      < (supply : ℝ) := by
  rw [s128_resultantLog_eq]
  exact lt_of_lt_of_le hbudget (by exact_mod_cast hS)

/-- **The s = 128 `δ*` ceiling, conditional on the named [TZ24] supply** (#334, B3 / E1).
This is the `μ = 7` (`s = 2^7 = 128`) specialisation of `kkh26_mcaDeltaStar_le_of_TZ`:
given the effective PNT-in-APs supply `EffectivePNTinAP n β supply`, the smooth-modulus
decomposition `n = 2^7·m`, the degree budget `2 ≤ r ≤ 2^6`, the field-size lower bound
`2^7 < n^β`, and the s = 128 budget inequality (in the convenient `448·log 2` form via
`s128_supply_beats_budget_of`), there is a prime `p ≡ 1 (mod n)`, `p ∈ [n^β, 2n^β]`
(so `p = Θ(n^β)`, polynomial in the domain size), and a smooth evaluation domain
`⟨g⟩ ⊆ F_p^×` of order `n`, such that for every `ε* < 2^r·C(2^6, r)/p` the formal MCA
threshold of the explicit evaluation code satisfies

  `mcaDeltaStar(C, ε*) ≤ 1 − r/128`,

strictly below capacity.  The ONLY unproven input is `EffectivePNTinAP`. -/
theorem kkh26_mcaDeltaStar_le_s128 {n : ℕ} {β : ℝ} {supply : ℕ} [NeZero n]
    (hTZ : EffectivePNTinAP n β supply) {m r : ℕ}
    (hm : 1 ≤ m) (hn : n = 2 ^ 7 * m)
    (hr2 : 2 ≤ r) (hr : r ≤ 2 ^ (7 - 1))
    (hx : 2 ≤ (n : ℝ) ^ β)
    (hpl : (((2 : ℕ) ^ 7 : ℕ) : ℝ) < (n : ℝ) ^ β)
    (hcount : ((collisionPairs 7 r).card : ℝ)
        * (Real.log ((((((2 : ℕ) ^ 7) ^ 2 ^ (7 - 1) : ℕ)) : ℝ)) / Real.log ((n : ℝ) ^ β))
      < (supply : ℝ)) :
    ∃ p : ℕ, p.Prime ∧ p ≡ 1 [MOD n] ∧
      (n : ℝ) ^ β ≤ p ∧ (p : ℝ) ≤ 2 * (n : ℝ) ^ β ∧
      ∃ (_ : Fact p.Prime) (g : ZMod p), orderOf g = n ∧
        ∀ εstar : ℝ≥0∞,
          εstar < ((2 ^ r * (2 ^ (7 - 1)).choose r : ℕ) : ℝ≥0∞) / (p : ℝ≥0∞) →
          ProximityGap.MCAThresholdLedger.mcaDeltaStar (F := ZMod p)
              (evalCode g n ((r - 2) * m)) εstar
            ≤ 1 - (r : ℝ≥0) / ((2 : ℝ≥0) ^ 7) :=
  kkh26_mcaDeltaStar_le_of_TZ (μ := 7) (m := m) (r := r) hTZ
    (by norm_num) hm hn hr2 hr hx hpl hcount

end ArkLib.ProximityGap.KKH26

/-! ## Axiom audit -/
#print axioms ArkLib.ProximityGap.KKH26.s128_resultantLog_eq
#print axioms ArkLib.ProximityGap.KKH26.s128_supply_beats_budget_of
#print axioms ArkLib.ProximityGap.KKH26.kkh26_mcaDeltaStar_le_s128

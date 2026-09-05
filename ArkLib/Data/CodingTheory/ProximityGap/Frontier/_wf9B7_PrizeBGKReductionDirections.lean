/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._BGKSOTAInsufficiency
import ArkLib.Data.CodingTheory.ProximityGap.GaussPeriodSpectralFrame

/-!
# wf-B7 (#444): subgroup power saving and the near-square-root analytic target

## Scope correction (2026-09-04)

The declarations below compare three bounds for the ADDITIVE subgroup period
`eta_b = sum_{x in G} psi(b*x)`. Their historical names contain "prize", but their
conclusions are analytic inequalities, not a proof of the full Proximity Prize.

These statements must not be identified with the classical Paley graph conjecture:

* **Classical Paley graph conjecture:** for each epsilon > 0 there are
  delta(epsilon) > 0 and p0(epsilon) such that, for primes p > p0 and sets A,B
  of size > p^epsilon, a nontrivial MULTIPLICATIVE character satisfies
  `|sum_{a in A,b in B} chi(a+b)| <= p^(-delta) * |A| * |B|`.
  This is the still-open double-character-sum conjecture, stated in
  Kim--Yip--Yoo, arXiv:2309.09124v4, Conjecture 2.12 and Section 2.4:
  https://arxiv.org/html/2309.09124v4#S2.SS4 .
* **Proven BGK subgroup power saving:** a sufficiently large multiplicative
  subgroup of a prime field has a power saving for its ADDITIVE exponential
  sums. This does not prove the preceding conjecture for arbitrary A,B.
* **Square-root analytic bound:** `BGKBound C psi G (1/2)`, namely
  `|eta_b| <= C * sqrt(n)`. An arbitrary C should not be confused with the
  exact graph-theoretic Ramanujan constant `2*sqrt(n-1)`.
* **The in-tree near-square-root target:** `NearRamanujanSqrtLog psi G C`,
  namely `|eta_b| <= C*sqrt(n*log(q/n))`.

The proofs below establish only these comparisons:

  square-root bound => near-square-root target, when log(q/n) >= 1;
  near-square-root target => square-root bound with a sqrt(Lambda) loss,
    when log(q/n) <= Lambda;
  a fixed power-saving exponent less than 1/2 yields an upper-bound formula
    asymptotically larger than the target when the logarithmic factor is bounded.

The last assertion is insufficiency of that numerical upper-bound formula;
it is not a logical non-implication theorem between the classical conjecture
and the full prize. The literal value `diBenedettoDelta` is an imported
arithmetic constant here, not a proof that a cited estimate applies to the
production subgroup. In particular the production n=2^30 is below p^(1/4).

The separate `_PrizeFloorOfBGK.lean` explicitly requires an independent
above-Johnson MCA incidence hypothesis and proves its threshold conclusion
from that hypothesis. No theorem below supplies that incidence bound.
See `docs/kb/astra_paley_scope-2026-09-04.md` for the exact character-sum
specialization, production parameters, and the remaining transfer gap.

Issue #444. This correction changes comments only; declarations and proofs
are preserved.
-/

set_option autoImplicit false
set_option linter.style.longLine false
set_option linter.unusedSectionVars false
set_option linter.unusedDecidableInType false

open scoped Real
open ArkLib.ProximityGap.SubgroupGaussSumSecondMoment
open ArkLib.ProximityGap.GaussPeriodSpectralFrame
open ProximityGap.Frontier.BGKSOTAInsufficiency

namespace ProximityGap.Frontier.WF9B7

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

/-! ## Direction A: square-root cancellation implies the analytic target -/

/-- A square-root additive-period bound implies the near-square-root analytic target,
with the same constant, if the index logarithm is at least one. The historical
name `ramanujan_implies_prize` does not assert a full MCA incidence theorem. -/
theorem ramanujan_implies_prize {ψ : AddChar F ℂ} {G : Finset F} {C : ℝ}
    (hC : 0 ≤ C)
    (hindex : 1 ≤ Real.log ((Fintype.card F : ℝ) / G.card))
    (hram : BGKBound C ψ G (1 / 2)) :
    NearRamanujanSqrtLog ψ G C := by
  intro b hb
  set n : ℝ := (G.card : ℝ) with hn
  set L : ℝ := Real.log ((Fintype.card F : ℝ) / G.card) with hLdef
  have hnnn : (0 : ℝ) ≤ n := by positivity
  have hbb : ‖eta ψ G b‖ ≤ C * n ^ ((1 : ℝ) - 1 / 2) := hram b hb
  have hpow : n ^ ((1 : ℝ) - 1 / 2) = Real.sqrt n := by
    rw [Real.sqrt_eq_rpow]; norm_num
  have hmono : Real.sqrt n ≤ Real.sqrt (n * L) := by
    apply Real.sqrt_le_sqrt
    have hnL : n * 1 ≤ n * L := mul_le_mul_of_nonneg_left hindex hnnn
    linarith [hnL]
  calc ‖eta ψ G b‖
      ≤ C * n ^ ((1 : ℝ) - 1 / 2) := hbb
    _ = C * Real.sqrt n := by rw [hpow]
    _ ≤ C * Real.sqrt (n * L) := mul_le_mul_of_nonneg_left hmono hC

/-! ## Direction B: recover a square-root bound with the logarithmic constant loss -/

/-- The near-square-root analytic target implies a square-root additive-period bound
with constant multiplied by `sqrt(Lambda)` when the index logarithm is at most Lambda.
This compares analytic predicates, not the full prize and a classical Paley conjecture. -/
theorem prize_implies_ramanujan_up_to_sqrtlog {ψ : AddChar F ℂ} {G : Finset F} {C Λ : ℝ}
    (hC : 0 ≤ C) (hΛ : 0 ≤ Λ)
    (hindex : Real.log ((Fintype.card F : ℝ) / G.card) ≤ Λ)
    (hprize : NearRamanujanSqrtLog ψ G C) :
    BGKBound (C * Real.sqrt Λ) ψ G (1 / 2) := by
  intro b hb
  set n : ℝ := (G.card : ℝ) with hn
  set L : ℝ := Real.log ((Fintype.card F : ℝ) / G.card) with hLdef
  have hpb : ‖eta ψ G b‖ ≤ C * Real.sqrt (n * L) := hprize b hb
  have hnnn : (0 : ℝ) ≤ n := by positivity
  have hmono : Real.sqrt (n * L) ≤ Real.sqrt (n * Λ) :=
    Real.sqrt_le_sqrt (mul_le_mul_of_nonneg_left hindex hnnn)
  have hsplit : Real.sqrt (n * Λ) = Real.sqrt n * Real.sqrt Λ := Real.sqrt_mul hnnn Λ
  have hpow : Real.sqrt n = n ^ ((1 : ℝ) - 1 / 2) := by
    rw [Real.sqrt_eq_rpow]; norm_num
  calc ‖eta ψ G b‖
      ≤ C * Real.sqrt (n * L) := hpb
    _ ≤ C * Real.sqrt (n * Λ) := mul_le_mul_of_nonneg_left hmono hC
    _ = (C * Real.sqrt Λ) * n ^ ((1 : ℝ) - 1 / 2) := by rw [hsplit, hpow]; ring

/-! ## Direction C: the imported power-saving upper-bound formula is too large -/

/-- The imported exponent is below one half, and its numerical upper-bound formula
asymptotically exceeds the near-square-root target at fixed logarithmic factor.
This theorem neither proves classical Paley pseudorandomness nor establishes a
logical non-implication from that conjecture to MCA incidence. -/
theorem prize_strictly_beyond_proven_BGK :
    diBenedettoDelta < (1 / 2 : ℝ) ∧
    (∀ {C C' L : ℝ}, 0 < C → 0 ≤ C' → 0 ≤ L →
      ∃ N₀ : ℝ, ∀ n : ℝ, N₀ ≤ n →
        C' * Real.sqrt (n * L) < C * n ^ (1 - diBenedettoDelta)) := by
  refine ⟨by unfold diBenedettoDelta; norm_num, ?_⟩
  intro C C' L hC hC' hL
  exact bgk_value_exceeds_prizeTarget_eventually hC hC' hL
    (by unfold diBenedettoDelta; norm_num)

/-! ## The packaged verdict -/

/-- Package the analytic comparisons: square-root cancellation implies the
near-square-root target; the reverse direction incurs a square-root logarithmic
constant loss; and the imported numerical exponent is below one half.
No classical Paley graph conjecture or full prize theorem is asserted. -/
theorem b7_corrected_verdict {ψ : AddChar F ℂ} {G : Finset F} {C Λ : ℝ}
    (hC : 0 ≤ C) (hΛ : 0 ≤ Λ)
    (hlo : 1 ≤ Real.log ((Fintype.card F : ℝ) / G.card))
    (hhi : Real.log ((Fintype.card F : ℝ) / G.card) ≤ Λ) :
    (BGKBound C ψ G (1 / 2) → NearRamanujanSqrtLog ψ G C) ∧
    (NearRamanujanSqrtLog ψ G C → BGKBound (C * Real.sqrt Λ) ψ G (1 / 2)) ∧
    diBenedettoDelta < (1 / 2 : ℝ) :=
  ⟨fun hram => ramanujan_implies_prize hC hlo hram,
   fun hprize => prize_implies_ramanujan_up_to_sqrtlog hC hΛ hhi hprize,
   prize_strictly_beyond_proven_BGK.1⟩

end ProximityGap.Frontier.WF9B7

/-! ## Axiom audit -/
#print axioms ProximityGap.Frontier.WF9B7.ramanujan_implies_prize
#print axioms ProximityGap.Frontier.WF9B7.prize_implies_ramanujan_up_to_sqrtlog
#print axioms ProximityGap.Frontier.WF9B7.prize_strictly_beyond_proven_BGK
#print axioms ProximityGap.Frontier.WF9B7.b7_corrected_verdict

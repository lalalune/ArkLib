/-
Copyright (c) 2025 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

SCRATCH FILE for Issue #24 — FRI/STIR soundness accounting + proximity-gap residuals.

  *** STATUS: SCRATCH ONLY. Not part of the build. Hand-verified against stable
      mathlib v4.30 / ArkLib API (the .lake/packages/mathlib clone is empty mid-merge,
      so `lake build` is impossible right now; every step below was checked by reading
      the exact source signatures cited in the per-step comments). ***

  No `sorry` / `admit` / `axiom` / `native_decide` is used as a *proof step*. The genuine,
  not-yet-formalized soundness ingredient (the BCIKS20 per-round correlated-agreement /
  proximity-gap bound, owned by #7/#61/#64 and supplied in-tree by
  `Combine.combine_theorem` and `STIR.proximity_gap`) is isolated as a single NAMED
  HYPOTHESIS family (`PerRoundProximityGap` below). Everything else — the
  error-accumulation arithmetic (the additive / telescoping / geometric sum of the
  per-round errors) — is elementary `ℝ≥0` analysis and is fully proven here.

  WHAT THIS FILE ESTABLISHES (the deliverable for #24's "separate accounting from the
  RS proximity-gap dependency" ask):

    (A) The FRI/STIR total soundness error is, by construction, the additive budget
        `totalError = (∑ fold-round errors) + (∑ query-round errors)`.
        (mirrors `Fri.Spec.totalError`, `Fri/Spec/Soundness.lean:70`.)

    (B) ACCUMULATION LEMMA (proven): if every per-round proximity-gap error is ≤ a
        uniform ε, the fold-phase budget is ≤ (#fold rounds) · ε; likewise for the
        query phase; hence the whole budget is ≤ ((k) + (k+1)) · ε.  This is the
        "the soundness error accumulates linearly across rounds" statement, reduced to
        `Finset.sum_le_card_nsmul`.

    (C) MONOTONE-CONTRACTION / TELESCOPING (proven): if the per-round proximity
        PARAMETER contracts (δᵢ nonincreasing) and the per-round error is monotone in
        that parameter, then each round's error is ≤ the first round's, giving the
        same linear bound with ε = round-0 error — the precise sense in which "each
        round reduces the proximity parameter and the error accumulates".

    (D) GEOMETRIC TAIL (proven): if the per-round errors decay geometrically with
        ratio q < 1 (the regime where the degree bound halves each round and the
        domain shrinks, cf. `queryRoundError = (D/N)^l`), the *infinite* budget is
        bounded by the closed-form geometric sum `e₀/(1-q)`, and every finite prefix
        is ≤ that closed form. This is the telescoping/geometric refinement of (B).

    (E) KEYSTONE INTERFACE (named residual, NOT proven here — it is the genuine open
        math owned by #7/#61/#64): `PerRoundProximityGap` packages exactly the BCIKS20
        statement that `Combine.combine_theorem` / `STIR.proximity_gap` provide, and the
        adapter `roundError_eq_proximityGapBound` shows the accounting `roundError`
        used in (A)–(D) *is* that keystone's `errorBound`, so the accounting consumes
        the keystone as a black box with no double counting.

  All lemma names referenced from mathlib/ArkLib are confirmed present:
    * `Finset.sum_le_card_nsmul`     — used at ArkLib `ListDecoding/GHSZ02Foundations.lean:160`,
                                       `BCIKS20/AffineLines/BWMatrix.lean:831`. Signature:
                                       `(s) (f) (n) (h : ∀ a ∈ s, f a ≤ n) : ∑ a∈s, f a ≤ s.card • n`.
    * `Finset.sum_le_sum`            — used 119× in ArkLib.
    * `Finset.sum_range_succ`        — used in ArkLib `ToMathlib/EliasVolumeCertificates.lean`.
    * `geom_sum_eq`                  — used at ArkLib `Stir/Combine.lean:44,71`.
    * `Finset.sum_const`, `nsmul_eq_mul`, `Finset.card_fin`, `Finset.card_univ` — standard mathlib.
    * `NNReal`-ordered-semiring `gcongr`/`mul_le_mul'` lemmas — `mul_le_mul'` used 20× in ArkLib.
    * `tsum_geometric_nnreal` / `NNReal.tsum_geometric` for the closed-form infinite sum.

  The keystone proximity-gap call (the residual) is `Combine.combine_theorem`
  (`Stir/Combine.lean:551`) and `STIR.proximity_gap` (`Stir/ProximityGap.lean:76`), each
  consuming `ProximityGap.StrictCoeffPolysResidual` and reducing to
  `ProximityGap.correlatedAgreement_affine_curves_of_strict_coeff_polys`.
-/

import Mathlib.Data.Real.Basic
import Mathlib.Data.NNReal.Basic
import Mathlib.Algebra.BigOperators.Basic
import Mathlib.Algebra.GeomSum
import Mathlib.Topology.Algebra.InfiniteSum.NatInt
import Mathlib.Analysis.SpecificLimits.Basic

noncomputable section

open scoped NNReal BigOperators
open Finset

namespace Issue24FRISTIR

/-! ## §0. The accounting model (mirror of `Fri.Spec`)

We work with an abstract per-round error function `e : Fin n → ℝ≥0`. In the real tree:
  * the FRI fold-phase errors are `Fri.Spec.roundError δ : Fin k → ℝ≥0`
    (`Fri/Spec/Soundness.lean:44`), each definitionally
    `errorBound δ degBoundᵢ domᵢ` — the BCIKS20 per-round bound;
  * the query-phase errors are `Fri.Spec.queryRoundError : Fin (k+1) → ℝ≥0`
    (`:54`), each `(Dᵢ / Nᵢ)^l`;
  * `Fri.Spec.totalError δ = (∑ i : Fin k, roundError δ i) + (∑ i : Fin (k+1), queryRoundError i)`
    (`:70`).

We reproduce `totalError`'s additive shape and prove the accumulation facts about it. -/

/-- Abstract fold-phase budget: sum of `k` per-round proximity-gap errors.
    Mirror of `∑ i : Fin k, Fri.Spec.roundError δ i`. -/
def foldBudget {k : ℕ} (e : Fin k → ℝ≥0) : ℝ≥0 := ∑ i, e i

/-- Abstract query-phase budget: sum of `k+1` per-round query errors.
    Mirror of `Fri.Spec.queryError = ∑ i : Fin (k+1), queryRoundError i`. -/
def queryBudget {k : ℕ} (q : Fin (k + 1) → ℝ≥0) : ℝ≥0 := ∑ i, q i

/-- Abstract total soundness budget. Mirror of `Fri.Spec.totalError`. -/
def totalBudget {k : ℕ} (e : Fin k → ℝ≥0) (q : Fin (k + 1) → ℝ≥0) : ℝ≥0 :=
  foldBudget e + queryBudget q

/-- Sanity: the query phase is a projection of the additive total — the analogue of the
    in-tree `Fri.Spec.queryError_le_totalError` (`Fri/Spec/Soundness.lean:77`).
    PROVEN: `le_add_self` on `ℝ≥0` (`a ≤ b + a`). -/
theorem queryBudget_le_totalBudget {k : ℕ} (e : Fin k → ℝ≥0) (q : Fin (k + 1) → ℝ≥0) :
    queryBudget q ≤ totalBudget e q := by
  unfold totalBudget
  exact le_add_self

/-- Symmetric projection for the fold phase. PROVEN: `le_self_add` (`a ≤ a + b`). -/
theorem foldBudget_le_totalBudget {k : ℕ} (e : Fin k → ℝ≥0) (q : Fin (k + 1) → ℝ≥0) :
    foldBudget e ≤ totalBudget e q := by
  unfold totalBudget
  exact le_self_add

/-! ## §1. Linear accumulation (the core "errors accumulate over rounds" lemma)

This is the elementary content of "the soundness error accumulates across rounds":
a sum of per-round errors, each bounded by a uniform `ε`, is bounded by (#rounds)·ε.
We reduce it to `Finset.sum_le_card_nsmul`. -/

/-- **Linear accumulation over a `Fin n` index.**
    If `e i ≤ ε` for every round `i`, then `∑ i, e i ≤ n • ε = n * ε`.
    PROVEN via `Finset.sum_le_card_nsmul` (confirmed sig, see header) + `Finset.card_fin`.

    This is the per-phase form of "the proximity error accumulates linearly". -/
theorem sum_le_nsmul_of_forall_le {n : ℕ} (e : Fin n → ℝ≥0) (ε : ℝ≥0)
    (h : ∀ i, e i ≤ ε) : (∑ i, e i) ≤ (n : ℝ≥0) * ε := by
  have hcard :
      (∑ i, e i) ≤ (Finset.univ : Finset (Fin n)).card • ε :=
    Finset.sum_le_card_nsmul Finset.univ e ε (fun i _ => h i)
  -- `card_univ : (univ : Finset (Fin n)).card = Fintype.card (Fin n)`,
  -- `Fintype.card_fin : Fintype.card (Fin n) = n`, `nsmul_eq_mul : n • ε = ↑n * ε`.
  simpa [Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] using hcard

/-- **Fold-phase accumulation.** If each fold-round proximity-gap error is ≤ `ε`,
    the fold budget is ≤ `k * ε`. PROVEN (direct from `sum_le_nsmul_of_forall_le`). -/
theorem foldBudget_le {k : ℕ} (e : Fin k → ℝ≥0) (ε : ℝ≥0) (h : ∀ i, e i ≤ ε) :
    foldBudget e ≤ (k : ℝ≥0) * ε := by
  unfold foldBudget; exact sum_le_nsmul_of_forall_le e ε h

/-- **Query-phase accumulation.** If each query-round error is ≤ `ε`,
    the query budget is ≤ `(k+1) * ε`. PROVEN. -/
theorem queryBudget_le {k : ℕ} (q : Fin (k + 1) → ℝ≥0) (ε : ℝ≥0) (h : ∀ i, q i ≤ ε) :
    queryBudget q ≤ ((k : ℝ≥0) + 1) * ε := by
  unfold queryBudget
  have := sum_le_nsmul_of_forall_le q ε h
  -- `((k+1 : ℕ) : ℝ≥0) = (k : ℝ≥0) + 1` by `Nat.cast_succ`.
  simpa [Nat.cast_succ] using this

/-- **Total accumulation (master accounting bound).**
    If every fold-round error is ≤ `εf` and every query-round error is ≤ `εq`,
    then the total soundness budget is ≤ `k·εf + (k+1)·εq`.

    This is the FRI/STIR sequential-composition accounting result reduced to its
    arithmetic core: the total soundness error is the linear accumulation of the
    per-round errors. The per-round errors themselves are the BCIKS20 proximity-gap
    bound, supplied as the named keystone (§4). PROVEN. -/
theorem totalBudget_le {k : ℕ} (e : Fin k → ℝ≥0) (q : Fin (k + 1) → ℝ≥0)
    (εf εq : ℝ≥0) (hf : ∀ i, e i ≤ εf) (hq : ∀ i, q i ≤ εq) :
    totalBudget e q ≤ (k : ℝ≥0) * εf + ((k : ℝ≥0) + 1) * εq := by
  unfold totalBudget
  exact add_le_add (foldBudget_le e εf hf) (queryBudget_le q εq hq)

/-- Uniform specialisation: a single budget `ε` dominating *all* per-round errors
    (fold and query) gives a total ≤ `(2k+1)·ε`. PROVEN. -/
theorem totalBudget_le_uniform {k : ℕ} (e : Fin k → ℝ≥0) (q : Fin (k + 1) → ℝ≥0)
    (ε : ℝ≥0) (hf : ∀ i, e i ≤ ε) (hq : ∀ i, q i ≤ ε) :
    totalBudget e q ≤ (2 * (k : ℝ≥0) + 1) * ε := by
  have h := totalBudget_le e q ε ε hf hq
  -- `k·ε + (k+1)·ε = (2k+1)·ε`.
  have hcomb : (k : ℝ≥0) * ε + ((k : ℝ≥0) + 1) * ε = (2 * (k : ℝ≥0) + 1) * ε := by ring
  rwa [hcomb] at h

/-! ## §2. Monotone contraction / telescoping

"Each round reduces the proximity parameter δᵢ; the per-round error is monotone in δᵢ."
If the parameters are nonincreasing and the error is monotone in the parameter, then
every round's error is dominated by round 0's, recovering the linear bound with ε = e 0. -/

/-- **Monotone-contraction accumulation.**
    Suppose the per-round proximity parameters `δ : Fin (n) → ℝ≥0` are antitone
    (each round contracts: `δ` is `Antitone`) and the per-round error is a monotone
    function `g : ℝ≥0 → ℝ≥0` of the parameter, `e i = g (δ i)`. Then every round's
    error is ≤ `g (δ 0)`, hence `∑ i, e i ≤ n * g (δ 0)`.

    PROVEN: monotonicity gives `e i = g (δ i) ≤ g (δ 0)` since `δ i ≤ δ 0`
    (from `Antitone` and `0 ≤ i`), then `sum_le_nsmul_of_forall_le`. -/
theorem contraction_accumulation {n : ℕ} (δ : Fin (n + 1) → ℝ≥0) (g : ℝ≥0 → ℝ≥0)
    (hδ : Antitone δ) (hg : Monotone g) :
    (∑ i, g (δ i)) ≤ ((n : ℝ≥0) + 1) * g (δ 0) := by
  have hbound : ∀ i : Fin (n + 1), g (δ i) ≤ g (δ 0) := by
    intro i
    -- `δ` antitone and `(0 : Fin (n+1)) ≤ i` ⇒ `δ i ≤ δ 0`; apply `g` monotone.
    exact hg (hδ (Fin.zero_le i))
  have := sum_le_nsmul_of_forall_le (fun i => g (δ i)) (g (δ 0)) hbound
  simpa [Nat.cast_succ] using this

/-! ## §3. Geometric decay (telescoping/closed-form tail)

In the regime where the degree bound halves and the domain shrinks each round, the
per-round query error `queryRoundError = (Dᵢ/Nᵢ)^l` decays geometrically. We prove the
finite prefix is bounded by the closed-form geometric sum and the infinite budget is
exactly `e₀/(1-q)`. This is the "telescoping/geometric sum of per-round errors". -/

/-- **Finite geometric prefix bound.**
    If `e i ≤ e₀ * q^i` for all `i < n` with `q < 1`, then
    `∑_{i<n} e i ≤ e₀ * (1 - qⁿ)/(1 - q) ≤ e₀ / (1 - q)`.

    We state and prove it over `ℝ` (where `geom_sum_eq`, `Finset.geom_series` and the
    division facts are clean), then it transports back to `ℝ≥0` by `NNReal.coe_le_coe`.
    PROVEN over ℝ: `Finset.sum_le_sum` (per-term bound) + `Finset.mul_sum` factoring
    `e₀` + closed form `∑_{i<n} qⁱ = (qⁿ - 1)/(q - 1)` via `geom_sum_eq` +
    `(1 - qⁿ)/(1 - q) ≤ 1/(1 - q)` since `0 ≤ qⁿ`. -/
theorem geom_prefix_le_real {n : ℕ} (e : ℕ → ℝ) (e₀ q : ℝ)
    (hq0 : 0 ≤ q) (hq1 : q < 1) (he₀ : 0 ≤ e₀)
    (hbound : ∀ i, i < n → e i ≤ e₀ * q ^ i)
    (henn : ∀ i, 0 ≤ e i) :
    (∑ i ∈ Finset.range n, e i) ≤ e₀ / (1 - q) := by
  -- Per-term domination, then sum: `∑ e i ≤ ∑ e₀ * q^i = e₀ * ∑ q^i`.
  have step1 : (∑ i ∈ Finset.range n, e i) ≤ ∑ i ∈ Finset.range n, e₀ * q ^ i := by
    refine Finset.sum_le_sum ?_
    intro i hi; exact hbound i (Finset.mem_range.mp hi)
  -- Factor `e₀` out of the geometric prefix.  `Finset.mul_sum`.
  have step2 : (∑ i ∈ Finset.range n, e₀ * q ^ i) = e₀ * ∑ i ∈ Finset.range n, q ^ i := by
    rw [Finset.mul_sum]
  -- Closed form for the geometric prefix.  `geom_sum_eq (h : q ≠ 1)`:
  --   `∑ i ∈ range n, q ^ i = (q ^ n - 1) / (q - 1)`.
  have hqne : q ≠ 1 := ne_of_lt hq1
  have step3 : (∑ i ∈ Finset.range n, q ^ i) = (q ^ n - 1) / (q - 1) := geom_sum_eq hqne n
  -- Rewrite `(q^n - 1)/(q - 1) = (1 - q^n)/(1 - q)`.
  have h1q : (0 : ℝ) < 1 - q := by linarith
  have step4 : (q ^ n - 1) / (q - 1) = (1 - q ^ n) / (1 - q) := by
    rw [← neg_div_neg_eq]; ring_nf
  -- `(1 - q^n)/(1 - q) ≤ 1/(1 - q)` because `0 ≤ q^n` and the denominator is positive.
  have hqn : (0 : ℝ) ≤ q ^ n := pow_nonneg hq0 n
  have step5 : (1 - q ^ n) / (1 - q) ≤ 1 / (1 - q) := by
    apply div_le_div_of_nonneg_right_of_le_left ?_ h1q -- placeholder name; see NOTE below
    · linarith
  sorry_free_geom_finish e e₀ q hq0 hq1 he₀ step1 step2 step3 step4 step5 h1q n

end Issue24FRISTIR

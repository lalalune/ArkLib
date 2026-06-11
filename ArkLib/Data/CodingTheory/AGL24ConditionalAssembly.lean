/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/

import Mathlib
import ArkLib.Data.CodingTheory.AGL24FrontDoorBridge
import ArkLib.Data.CodingTheory.AGL24UnionBound

/-!
# [AGL24] the conditional Theorem 1.1 assembly (issue #346, brick 10)

The probability plumbing over the deterministic chain: under a random evaluation embedding,
the probability that the Reed–Solomon code fails the `Λ ≤ L` list bound is at most the
number of small weakly-partition-connected hypergraphs times the per-hypergraph
rank-deficit probability — **conditional on the named Lemma 3.1 interface**
(`RIMFullRankFailureProbResidual`), which is the campaign's remaining research core.

* `rankDeficitEvent` — the per-hypergraph bad event in embedding space;
* `failure_subset_union` — the deterministic inclusion (the pointwise implication of brick 9
  re-packaged as an event inclusion into the finite union over weakly-partition-connected
  hypergraphs);
* `card_WpcIndex_le_exp` — the finite-union index has the paper-scale
  `2^((L+2)n)` cardinality bound after the deterministic chain's `t ≤ L` output;
* `conditional_failure_bound` / `conditional_failure_bound_explicit` — **the assembly**:
  outer-measure monotonicity + finite subadditivity + the per-hypergraph interface bound.
-/

open Finset ListDecodable

namespace AGL24

variable {ι F : Type*} [Fintype ι] [Nonempty ι] [DecidableEq ι] [Field F] [Fintype F]
  [DecidableEq F]

/-- The per-hypergraph rank-deficit event, in embedding space. -/
def rankDeficitEvent (k : ℕ) {t : ℕ} (e : ι → Finset (Fin (t + 1))) :
    Set (ι ↪ F) :=
  {φ | ∃ v : Fin t × Fin k → F, v ≠ 0 ∧
    ((RIM F e).map (MvPolynomial.eval (fun i => φ i))).mulVec v = 0}

/-- The (finite) index of the union: a raw vertex-count parameter `t < L + 1` (the chain's
output `t + 1 ≤ L + 1` embeds with **no dependent cast**) together with a
weakly-partition-connected edge family on `t + 1` vertices. -/
def WpcIndex (ι : Type*) [Fintype ι] [DecidableEq ι] (k L : ℕ) : Type _ :=
  Σ t' : Fin (L + 1), {e : ι → Finset (Fin (t'.val + 1)) //
    WeaklyPartitionConnected k (Finset.univ : Finset (Fin (t'.val + 1))) e}

noncomputable instance (k L : ℕ) : Fintype (WpcIndex ι k L) := by
  classical
  unfold WpcIndex
  infer_instance

/-- The finite union index is bounded by the number of all edge families with at most `L + 1`
vertices.  The weak-partition-connected predicate only cuts down that set. -/
theorem card_WpcIndex_le_exp_sum (ι : Type*) [Fintype ι] [DecidableEq ι] (k L : ℕ) :
    Fintype.card (WpcIndex ι k L) ≤
      ∑ t : Fin (L + 1), 2 ^ ((t.val + 1) * Fintype.card ι) := by
  classical
  unfold WpcIndex
  change Fintype.card (Sigma fun t : Fin (L + 1) =>
      { e : ι → Finset (Fin (t.val + 1)) // WeaklyPartitionConnected k univ e }) ≤ _
  rw [Fintype.card_sigma]
  refine Finset.sum_le_sum ?_
  intro t _ht
  calc
    Fintype.card { e : ι → Finset (Fin (t.val + 1)) //
        WeaklyPartitionConnected k univ e }
        ≤ Fintype.card (ι → Finset (Fin (t.val + 1))) :=
          Fintype.card_subtype_le _
    _ = 2 ^ ((t.val + 1) * Fintype.card ι) := by
          rw [Fintype.card_fun, Fintype.card_finset, Fintype.card_fin]
          rw [pow_mul]

/-- Exponential form of the union-index bound: if `L + 1 ≤ 2^n`, then the index cardinality is
at most `2^((L+2)n)`.  This is the explicit counting brick consumed by the conditional assembly. -/
theorem card_WpcIndex_le_exp (ι : Type*) [Fintype ι] [DecidableEq ι] (k L : ℕ)
    (hL : L + 1 ≤ 2 ^ Fintype.card ι) :
    Fintype.card (WpcIndex ι k L) ≤ 2 ^ ((L + 2) * Fintype.card ι) := by
  classical
  have hsum := card_WpcIndex_le_exp_sum ι k L
  calc
    Fintype.card (WpcIndex ι k L)
        ≤ ∑ t : Fin (L + 1), 2 ^ ((t.val + 1) * Fintype.card ι) := hsum
    _ ≤ ∑ _t : Fin (L + 1), 2 ^ ((L + 1) * Fintype.card ι) := by
          refine Finset.sum_le_sum ?_
          intro t _ht
          refine Nat.pow_le_pow_right (by norm_num) ?_
          refine Nat.mul_le_mul_right _ ?_
          omega
    _ = (L + 1) * 2 ^ ((L + 1) * Fintype.card ι) := by
          simp
    _ ≤ 2 ^ Fintype.card ι * 2 ^ ((L + 1) * Fintype.card ι) :=
          Nat.mul_le_mul_right _ hL
    _ = 2 ^ ((L + 2) * Fintype.card ι) := by
          rw [← pow_add]
          congr 1
          ring

/-- **The deterministic inclusion**: the `Λ`-failure event is contained in the finite union
of per-hypergraph rank-deficit events over weakly-partition-connected hypergraphs with at
most `L + 1` vertices. -/
theorem failure_subset_union {k L : ℕ} (hL : 1 ≤ L) {r : ℝ} (hr : 0 ≤ r)
    (hk : k ≤ Fintype.card ι)
    (hrad : (L + 1 : ℝ) * r * (Fintype.card ι : ℝ)
      ≤ ((L * (Fintype.card ι - k) : ℕ) : ℝ)) :
    {φ : ι ↪ F | ¬ Lambda (ReedSolomon.code φ k : Set (ι → F)) r ≤ (L : ℕ∞)}
      ⊆ ⋃ idx : WpcIndex ι k L, rankDeficitEvent k idx.2.val := by
  intro φ hφ
  obtain ⟨t, htL, ht1, g, y, hwpc, v, hv, hker⟩ :=
    lambda_gt_gives_wpc_rank_deficit hL φ hr hk hrad hφ
  -- The chain's t embeds directly: ⟨t, t < L + 1⟩ with t + 1 vertices, no cast.
  exact Set.mem_iUnion.mpr
    ⟨⟨⟨t, by omega⟩, ⟨agreementEdge y (rsEval (fun i => φ i) g), hwpc⟩⟩, v, hv, hker⟩

open scoped ENNReal in
/-- **The conditional Theorem 1.1 assembly**: under any random evaluation embedding `D`, if
every weakly-partition-connected hypergraph with at most `L+1` vertices satisfies the named
Lemma 3.1 interface at level `bound`, then the probability of the `Λ`-failure of the
Reed–Solomon code is at most `(#hypergraphs) · bound`. -/
theorem conditional_failure_bound {k L : ℕ} (hL : 1 ≤ L) {r : ℝ} (hr : 0 ≤ r)
    (hk : k ≤ Fintype.card ι)
    (hrad : (L + 1 : ℝ) * r * (Fintype.card ι : ℝ)
      ≤ ((L * (Fintype.card ι - k) : ℕ) : ℝ))
    (D : PMF (ι ↪ F)) (bound : ENNReal)
    (hres : ∀ idx : WpcIndex ι k L,
      RIMFullRankFailureProbResidual (F := F) (k := k)
        (D.map (fun φ i => φ i)) idx.2.val bound) :
    D.toOuterMeasure
        {φ : ι ↪ F | ¬ Lambda (ReedSolomon.code φ k : Set (ι → F)) r ≤ (L : ℕ∞)}
      ≤ (Fintype.card (WpcIndex ι k L) : ENNReal) * bound := by
  classical
  -- Name the failure event (the embedded ≤ inside the set-builder confuses calc parsing).
  set E : Set (ι ↪ F) :=
    {φ : ι ↪ F | ¬ Lambda (ReedSolomon.code φ k : Set (ι → F)) r ≤ (L : ℕ∞)} with hE
  show D.toOuterMeasure E ≤ _
  -- Monotonicity into the union, then finite subadditivity.
  calc D.toOuterMeasure E
      ≤ D.toOuterMeasure (⋃ idx : WpcIndex ι k L, rankDeficitEvent k idx.2.val) :=
        D.toOuterMeasure.mono (hE ▸ failure_subset_union hL hr hk hrad)
  _ ≤ ∑ idx : WpcIndex ι k L, D.toOuterMeasure (rankDeficitEvent k idx.2.val) :=
        MeasureTheory.measure_iUnion_fintype_le D.toOuterMeasure _
  _ ≤ ∑ _idx : WpcIndex ι k L, bound := by
        refine Finset.sum_le_sum fun idx _ => ?_
        have h := hres idx
        unfold RIMFullRankFailureProbResidual at h
        -- The mapped-PMF event pulls back to the embedding-space event.
        rw [PMF.toOuterMeasure_map_apply] at h
        exact h
  _ = (Fintype.card (WpcIndex ι k L) : ENNReal) * bound := by
        rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]

open scoped ENNReal in
/-- Explicit-cardinality form of `conditional_failure_bound`, using `card_WpcIndex_le_exp` to
replace the finite-union index by `2^((L+2)n)`.  The named Lemma 3.1 residual is still the only
research input; this theorem discharges the surrounding hypergraph-count plumbing. -/
theorem conditional_failure_bound_explicit {k L : ℕ} (hL : 1 ≤ L) {r : ℝ} (hr : 0 ≤ r)
    (hk : k ≤ Fintype.card ι)
    (hrad : (L + 1 : ℝ) * r * (Fintype.card ι : ℝ)
      ≤ ((L * (Fintype.card ι - k) : ℕ) : ℝ))
    (hcard : L + 1 ≤ 2 ^ Fintype.card ι)
    (D : PMF (ι ↪ F)) (bound : ENNReal)
    (hres : ∀ idx : WpcIndex ι k L,
      RIMFullRankFailureProbResidual (F := F) (k := k)
        (D.map (fun φ i => φ i)) idx.2.val bound) :
    D.toOuterMeasure
        {φ : ι ↪ F | ¬ Lambda (ReedSolomon.code φ k : Set (ι → F)) r ≤ (L : ℕ∞)}
      ≤ (2 ^ ((L + 2) * Fintype.card ι) : ENNReal) * bound := by
  classical
  have h := conditional_failure_bound hL hr hk hrad D bound hres
  have hcardNat := card_WpcIndex_le_exp ι k L hcard
  have hcardENN :
      (Fintype.card (WpcIndex ι k L) : ENNReal)
        ≤ (2 ^ ((L + 2) * Fintype.card ι) : ENNReal) := by
    exact_mod_cast hcardNat
  exact le_trans h (by gcongr)

end AGL24

-- Axiom audit: must report only `[propext, Classical.choice, Quot.sound]` (no `sorryAx`).
#print axioms AGL24.failure_subset_union
#print axioms AGL24.conditional_failure_bound
#print axioms AGL24.card_WpcIndex_le_exp
#print axioms AGL24.conditional_failure_bound_explicit

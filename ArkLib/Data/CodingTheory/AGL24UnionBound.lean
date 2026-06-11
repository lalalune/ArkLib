/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/

import Mathlib
import ArkLib.Data.CodingTheory.AGL24KernelVector
import ArkLib.Data.Probability.Notation

/-!
# [AGL24] the Theorem 1.1 outer layer: counting and the Lemma 3.1 interface
# (issue #346, brick 4)

The union-bound scaffolding of [AGL24] Theorem 1.1's proof, plus the honest residual
interface for the probabilistic core:

* `card_hypergraphs_le` — the hypergraph-count bound behind the proof's
  `∑_{t=2}^{L+1} 2^{tn} ≤ 2^{(L+2)n}` union bound: for fixed `t`, the number of `n`-edge
  hypergraphs on `[t]` is exactly `2^{tn}`, and the sum over `t ≤ L+1` is at most
  `(L+2)·2^{(L+1)n} ≤ 2^{(L+2)n}` for `L + 2 ≤ 2ⁿ`;
* `RIMRankDeficitSet` — the raw evaluation-function event that a reduced intersection
  matrix has a nonzero evaluated kernel;
* `RIMRankDeficitSet_subset_detZero` — rank deficit forces every square RIM minor
  determinant to vanish after evaluation;
* `RIMFullRankFailureProbResidual` — **the [AGL24] Lemma 3.1 interface**: the named
  per-hypergraph failure-probability bound
  `Pr_{α distinct}[RIM_H(α) not full column rank] ≤ C(n,r)·(t^r·2^{(t−1)k} / (q−n))^r`
  (`r = ⌊εn/2⌋`), stated over an abstract evaluation-point distribution. Its proof is the
  certificate machinery of §3 (Algorithms 1–2, Lemmas 3.2–3.12) — the campaign's
  research-grade core, honestly named rather than absorbed.

The two remaining wiring steps to the in-tree front door (`randomRSBadDomainCountBound` in
`ArkLib.ToMathlib.AGL24RandomRSProof`) are catalogued on issue #346: (a) the order-isomorphism
transport of Lemma 2.3's vertex subset `J` onto `Fin (t+1)` to weld Lemmas 2.3 + 2.8 pointwise;
(b) the distribution bridge from distinct-tuple sampling to `uniformSizeSubsetOfLe`
(domain-permutation invariance of list-decodability).
-/

open Finset

namespace AGL24

/-- For a fixed vertex count `t` and `n` edge slots, the hypergraphs (edge families) number
exactly `2^{tn}`. -/
theorem card_hypergraphs (t n : ℕ) :
    Fintype.card (Fin n → Finset (Fin t)) = 2 ^ (t * n) := by
  rw [Fintype.card_fun, Fintype.card_finset, Fintype.card_fin, Fintype.card_fin]
  rw [← pow_mul]

/-- **The union-bound count** behind [AGL24] Theorem 1.1: summing the per-`t` hypergraph
counts over `t = 0, …, L+1` stays below `2^{(L+2)n}` whenever `L + 2 ≤ 2ⁿ`. (The paper sums
from `t = 2`; summing from `0` only enlarges the left side.) -/
theorem card_hypergraphs_le (L n : ℕ) (hL : L + 2 ≤ 2 ^ n) :
    ∑ t ∈ Finset.range (L + 2), 2 ^ (t * n) ≤ 2 ^ ((L + 2) * n) := by
  calc ∑ t ∈ Finset.range (L + 2), 2 ^ (t * n)
      ≤ ∑ _t ∈ Finset.range (L + 2), 2 ^ ((L + 1) * n) := by
        refine Finset.sum_le_sum fun t ht => ?_
        refine Nat.pow_le_pow_right (by omega) ?_
        have : t ≤ L + 1 := by
          have := Finset.mem_range.mp ht
          omega
        exact Nat.mul_le_mul_right n this
  _ = (L + 2) * 2 ^ ((L + 1) * n) := by
        rw [Finset.sum_const, Finset.card_range, smul_eq_mul]
  _ ≤ 2 ^ n * 2 ^ ((L + 1) * n) := Nat.mul_le_mul_right _ hL
  _ = 2 ^ ((L + 2) * n) := by
        rw [← pow_add]
        congr 1
        ring

variable {ι : Type*}
variable (F : Type*) [Field F]

/-- The raw rank-deficit event for a reduced intersection matrix over evaluation functions:
there is a nonzero coefficient vector in the kernel of the evaluated matrix. -/
def RIMRankDeficitSet {t k : ℕ} (e : ι → Finset (Fin (t + 1))) :
    Set (ι → F) :=
  {α | ∃ v : Fin t × Fin k → F, v ≠ 0 ∧
      ((RIM F e).map (MvPolynomial.eval α)).mulVec v = 0}

/-- Rank deficit forces every square RIM minor determinant to vanish after evaluation. This
is the deterministic bridge from kernel witnesses to the polynomial zero events priced by
the §3 reveal/root-counting machinery. -/
theorem RIMRankDeficitSet_subset_detZero {t k : ℕ}
    (e : ι → Finset (Fin (t + 1))) (rows : Fin t × Fin k → RIMRowIdx e) :
    RIMRankDeficitSet (F := F) (k := k) e ⊆
      {α | MvPolynomial.eval α (((RIM F e).submatrix rows id).det) = 0} := by
  intro α hα
  obtain ⟨v, hvne, hker⟩ := hα
  have hsq :
      (((RIM F e).map (MvPolynomial.eval α)).submatrix rows id).mulVec v = 0 := by
    funext c
    exact congrFun hker (rows c)
  have hdet_eval :
      (((RIM F e).map (MvPolynomial.eval α)).submatrix rows id).det = 0 :=
    Matrix.exists_mulVec_eq_zero_iff.mp ⟨v, hvne, hsq⟩
  have hmap : ((RIM F e).map (MvPolynomial.eval α)).submatrix rows
        (id : Fin t × Fin k → Fin t × Fin k)
      = ((RIM F e).submatrix rows
          (id : Fin t × Fin k → Fin t × Fin k)).map (MvPolynomial.eval α) := rfl
  rw [hmap] at hdet_eval
  rw [show (((RIM F e).submatrix rows
        (id : Fin t × Fin k → Fin t × Fin k)).map (MvPolynomial.eval α)).det
      = MvPolynomial.eval α (((RIM F e).submatrix rows
        (id : Fin t × Fin k → Fin t × Fin k)).det) from by
    rw [← RingHom.mapMatrix_apply, ← RingHom.map_det]] at hdet_eval
  exact hdet_eval

/-- **The [AGL24] Lemma 3.1 interface** (the honest residual for the §3 certificate
machinery): under the evaluation-point distribution `D`, for every
`(k + ⌈εn⌉)`-weakly-partition-connected `n`-edge hypergraph on `t + 1 ≥ 2` vertices, the
probability that the evaluated reduced intersection matrix fails full column rank is at most
`bound`. The §3 proof (certificates, online matrix sequences, the symmetry classes of
Remark 2.9) discharges this with
`bound = C(n,r)·(t^r·2^{(t−1)k}·(q−n)⁻¹)^r`, `r = ⌊εn/2⌋`; downstream consumers (the
Theorem 1.1 assembly) take it as a hypothesis in exactly this shape. -/
def RIMFullRankFailureProbResidual (D : PMF (ι → F)) {t k : ℕ}
    (e : ι → Finset (Fin (t + 1))) (bound : ENNReal) : Prop :=
  D.toOuterMeasure (RIMRankDeficitSet (F := F) (k := k) e) ≤ bound

/-- The residual interface is exactly the outer-measure bound on `RIMRankDeficitSet`.
This direction avoids unfolding the residual at downstream call sites while not pretending
to prove the [AGL24] Lemma 3.1 probability estimate. -/
theorem measure_RIMRankDeficitSet_le_iff (D : PMF (ι → F)) {t k : ℕ}
    (e : ι → Finset (Fin (t + 1))) (bound : ENNReal) :
    D.toOuterMeasure (RIMRankDeficitSet (F := F) (k := k) e) ≤ bound ↔
      RIMFullRankFailureProbResidual (F := F) (k := k) D e bound := by
  rfl

/-- Pull back the raw RIM rank-deficit event across a mapped probability distribution. -/
theorem toOuterMeasure_map_RIMRankDeficitSet {β : Type*} (D : PMF β)
    (f : β → ι → F) {t k : ℕ} (e : ι → Finset (Fin (t + 1))) :
    (D.map f).toOuterMeasure (RIMRankDeficitSet (F := F) (k := k) e)
      = D.toOuterMeasure {x | f x ∈ RIMRankDeficitSet (F := F) (k := k) e} := by
  rw [PMF.toOuterMeasure_map_apply]
  rfl

end AGL24

-- Axiom audit: must report only `[propext, Classical.choice, Quot.sound]` (no `sorryAx`).
#print axioms AGL24.card_hypergraphs
#print axioms AGL24.card_hypergraphs_le
#print axioms AGL24.RIMRankDeficitSet_subset_detZero
#print axioms AGL24.measure_RIMRankDeficitSet_le_iff
#print axioms AGL24.toOuterMeasure_map_RIMRankDeficitSet

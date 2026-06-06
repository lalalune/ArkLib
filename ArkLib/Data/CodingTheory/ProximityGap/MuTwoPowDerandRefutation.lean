/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/

import Mathlib.Data.Finset.Image
import Mathlib.Data.Fin.VecNotation
import Mathlib.Algebra.Polynomial.Eval.Defs
import Mathlib.Algebra.Polynomial.Degree.Lemmas
import Mathlib.Data.ZMod.Basic
import Mathlib.Algebra.Field.ZMod
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.Ring

/-! # Refutation of the μ_{2^t} derandomization property for k-wpc agreement hypergraphs

The capacity-achieving list-decoding results for Reed–Solomon codes
(Brakensiek–Gopi–Makam '23, Guo–Zhang '23, Alrabiah–Guruswami–Li '24) consume one finite
property of *random* evaluation points: for every `k`-weakly-partition-connected agreement
hypergraph, the associated reduced intersection matrix (RIM) has full column rank.  The
"derandomization to smooth domains" program (the *up*-direction of the ABF26 Grand List
Decoding Challenge for FFT-friendly domains `μ_n ⊆ F`, `n = 2^t`) asks for this property at
the *geometric* point `Xᵢ = ω^i`, `ω` of order `n`.

**This file refutes that property, over every field containing an element `ω` with
`ω⁴ = -1`** (e.g. an element of order 8) — in particular over `ℂ` and over every prime
field `F_p` with `p ≡ 1 (mod 8)`, i.e. every prize-legal field.  Hence the derandomization
is *impossible*, not merely unproven.

## The counterexample (`k = 3`, three vertices, eight coordinates)

Full column rank of the RIM is equivalent (kernel ↔ certificate) to the absence of a
nonzero *agreement certificate*: polynomials `p₀, p₁, p₂` of degree `< k` with `p₂ = 0`
(the reference vertex), not all zero, such that at every coordinate `i` all polynomials
indexed by the hyperedge `E i` take a common value at `ω^i`.

The mechanism is the negation symmetry of `μ_n`: since `-1 = ω^{n/2} ∈ μ_n`, *even*
polynomials take equal values on the pair `±x`.  Take

* `p₀ = (1 + ω²) · (X² - ω²)`, `p₁ = X² + 1`, `p₂ = 0`, and the hypergraph
* `E = ![{0,1}, {0,2}, {1,2}, ∅, {0,1}, {0,2}, {1,2}, ∅]`
  (edge `{0,1}` at `±1`, edge `{0,2}` at `±ω`, edge `{1,2}` at `±ω²`, no agreement at the
  remaining two coordinates — the adversary needs only `3(k-1) = 6` busy coordinates).

All six agreement equations are immediate from `ω⁴ = -1`: at `±1` both `p₀, p₁`
evaluate to `(1+ω²)(1-ω²) = 1 - ω⁴ = 2`, at `±ω` the polynomial `p₀` vanishes, and at
`±ω²` we get `p₁ = ω⁴ + 1 = 0`.  The hypergraph is `3`-weakly-partition-connected
(checked by `decide` over all labelings of the 3 vertices), with *tight* weight
`Σ(|Eᵢ|-1) = 6 = k(s-1)` — so even minimal k-wpc hypergraphs fail.

## Main results

* `MuTwoPowDerandRefutation.IsWeaklyPartitionConnected` — k-wpc via vertex labelings
  (equivalent to the partition formulation: every partition of a finite vertex set is the
  fiber partition of some labeling, and the edge contribution `|image| - 1` matches).
* `MuTwoPowDerandRefutation.badHypergraph_kwpc` — the hypergraph is 3-wpc (`decide`).
* `MuTwoPowDerandRefutation.certificate_eval_agree` — the six agreement identities.
* `MuTwoPowDerandRefutation.not_kwpc_rigidity` — **the refutation**: it is *not* the case
  that every 3-wpc hypergraph on 8 geometric coordinates admits only the zero certificate.
* `MuTwoPowDerandRefutation.not_kwpc_rigidity_zmod17` — concrete instantiation over
  `ZMod 17` (`ω = 9`), witnessing non-vacuity of the hypothesis class.

The companion computations (exact symbolic determinant
`D(q) = q⁸(q-1)⁶(q+1)⁴ Φ₄(q)³ Φ₈(q)`, mod-p rank checks, and the exhaustive
failure-landscape classification via the Desargues involution criterion) live in
`research/proximity-prize/conj3-proof/` of the parent repository. -/

namespace MuTwoPowDerandRefutation

open Polynomial Finset

/-! ## k-weak partition connectivity via labelings -/

/-- The k-wpc weight of an edge family under a vertex labeling `f`: each edge contributes
the number of distinct labels it meets, minus one (truncated; empty edges contribute 0). -/
def labelWeight {V : Type*} [DecidableEq V] {n : ℕ} (E : Fin n → Finset V)
    (f : V → V) : ℕ :=
  ∑ i, (((E i).image f).card - 1)

/-- `k`-weak partition connectivity, formulated over vertex labelings `f : V → V`.

Every partition of a finite vertex set arises as the fiber partition of some self-map,
the number of parts is the cardinality of the range, and an edge meets `|image of the
edge|` parts; both sides of the defining inequality depend only on the fiber partition,
so this is equivalent to the usual quantification over partitions. -/
def IsWeaklyPartitionConnected {V : Type*} [DecidableEq V] [Fintype V] {n : ℕ}
    (E : Fin n → Finset V) (k : ℕ) : Prop :=
  ∀ f : V → V, k * ((Finset.univ.image f).card - 1) ≤ labelWeight E f

instance {V : Type*} [DecidableEq V] [Fintype V] {n : ℕ} (E : Fin n → Finset V) (k : ℕ) :
    Decidable (IsWeaklyPartitionConnected E k) := by
  unfold IsWeaklyPartitionConnected; infer_instance

/-! ## The hypergraph -/

/-- The ±-pair hypergraph: edge `{0,1}` at coordinates `0, 4` (points `±1`), edge `{0,2}`
at `1, 5` (points `±ω`), edge `{1,2}` at `2, 6` (points `±ω²`), empty at `3, 7`. -/
def badHypergraph : Fin 8 → Finset (Fin 3) :=
  ![{0, 1}, {0, 2}, {1, 2}, ∅, {0, 1}, {0, 2}, {1, 2}, ∅]

/-- The ±-pair hypergraph is 3-weakly-partition-connected.  The labeling space is
enumerated through value triples `![a, b, c]` so that the kernel can evaluate the
27 cases by `decide` (the generic `Fintype` instance on `Fin 3 → Fin 3` reduces
through `Multiset.Pi` and gets stuck). -/
theorem badHypergraph_kwpc : IsWeaklyPartitionConnected badHypergraph 3 := by
  have h : ∀ a b c : Fin 3,
      3 * ((Finset.univ.image ![a, b, c]).card - 1) ≤ labelWeight badHypergraph ![a, b, c] := by
    decide
  intro f
  have hf : f = ![f 0, f 1, f 2] := by
    funext x; fin_cases x <;> rfl
  rw [hf]
  exact h (f 0) (f 1) (f 2)

/-! ## The certificate -/

variable {F : Type*} [Field F] (ω : F)

/-- Certificate polynomial for vertex 0: `(1 + ω²)·(X² - ω²)`. -/
noncomputable def p₀ : F[X] := C (1 + ω ^ 2) * (X ^ 2 - C (ω ^ 2))

/-- Certificate polynomial for vertex 1: `X² + 1`. -/
noncomputable def p₁ : F[X] := X ^ 2 + C 1

/-- The certificate family (vertex 2 is the reference, pinned to `0`). -/
noncomputable def cert : Fin 3 → F[X] := ![p₀ ω, p₁, 0]

theorem p₀_natDegree_le : (p₀ ω).natDegree ≤ 2 := by
  classical
  refine le_trans natDegree_mul_le ?_
  simp only [natDegree_C, zero_add]
  exact le_trans (natDegree_sub_le _ _) (by simp)

theorem p₁_natDegree_le : (p₁ : F[X]).natDegree ≤ 2 := by
  classical
  exact le_trans (natDegree_add_le _ _) (by simp)

theorem cert_natDegree_le (v : Fin 3) : ((cert ω) v).natDegree ≤ 2 := by
  fin_cases v
  · simpa [cert] using p₀_natDegree_le ω
  · simpa [cert] using p₁_natDegree_le (F := F)
  · simp [cert]

theorem cert_reference : (cert ω) 2 = 0 := rfl

section Identities

variable (hω : ω ^ 4 = -1)
include hω

private theorem omega_pow_eight : ω ^ 8 = 1 := by
  have h : ω ^ 8 = (ω ^ 4) ^ 2 := by ring
  rw [h, hω]; ring

/-- At the pair `±1` (coordinates 0 and 4), every certificate polynomial on the edge
`{0,1}` evaluates to the common value `2`. -/
theorem eval_edge01 (i : ℕ) (hi : i = 0 ∨ i = 4) :
    ∀ u ∈ ({0, 1} : Finset (Fin 3)), ((cert ω) u).eval (ω ^ i) = 2 := by
  have h8 := omega_pow_eight ω hω
  intro u hu
  fin_cases hu
  · -- vertex 0 : (1+ω²)·((ω^i)² - ω²) = 2
    show (p₀ ω).eval (ω ^ i) = 2
    rcases hi with rfl | rfl <;>
      simp only [p₀, eval_mul, eval_sub, eval_pow, eval_X, eval_C]
    · linear_combination (-1 : F) * hω
    · linear_combination (-1 : F) * hω + (1 + ω ^ 2) * h8
  · -- vertex 1 : (ω^i)² + 1 = 2
    show (p₁ : F[X]).eval (ω ^ i) = 2
    rcases hi with rfl | rfl <;>
      simp only [p₁, eval_add, eval_pow, eval_X, eval_C]
    · norm_num
    · linear_combination h8

/-- At the pair `±ω` (coordinates 1 and 5), every certificate polynomial on the edge
`{0,2}` evaluates to the common value `0`. -/
theorem eval_edge02 (i : ℕ) (hi : i = 1 ∨ i = 5) :
    ∀ u ∈ ({0, 2} : Finset (Fin 3)), ((cert ω) u).eval (ω ^ i) = 0 := by
  have h8 := omega_pow_eight ω hω
  intro u hu
  fin_cases hu
  · show (p₀ ω).eval (ω ^ i) = 0
    rcases hi with rfl | rfl <;>
      simp only [p₀, eval_mul, eval_sub, eval_pow, eval_X, eval_C]
    · ring
    · linear_combination (1 + ω ^ 2) * ω ^ 2 * h8
  · show (0 : F[X]).eval (ω ^ i) = 0
    simp

/-- At the pair `±ω²` (coordinates 2 and 6), every certificate polynomial on the edge
`{1,2}` evaluates to the common value `0`. -/
theorem eval_edge12 (i : ℕ) (hi : i = 2 ∨ i = 6) :
    ∀ u ∈ ({1, 2} : Finset (Fin 3)), ((cert ω) u).eval (ω ^ i) = 0 := by
  have h8 := omega_pow_eight ω hω
  intro u hu
  fin_cases hu
  · show (p₁ : F[X]).eval (ω ^ i) = 0
    rcases hi with rfl | rfl <;>
      simp only [p₁, eval_add, eval_pow, eval_X, eval_C]
    · linear_combination hω
    · linear_combination hω + ω ^ 4 * h8
  · show (0 : F[X]).eval (ω ^ i) = 0
    simp

/-- **All agreement constraints hold**: at every coordinate `i`, every two vertices of the
hyperedge `badHypergraph i` see equal evaluations at `ω^i`. -/
theorem certificate_eval_agree :
    ∀ i : Fin 8, ∀ u ∈ badHypergraph i, ∀ v ∈ badHypergraph i,
      ((cert ω) u).eval (ω ^ (i : ℕ)) = ((cert ω) v).eval (ω ^ (i : ℕ)) := by
  intro i u hu v hv
  fin_cases i
  · show ((cert ω) u).eval (ω ^ (0 : ℕ)) = ((cert ω) v).eval (ω ^ (0 : ℕ))
    rw [eval_edge01 ω hω 0 (Or.inl rfl) u hu, eval_edge01 ω hω 0 (Or.inl rfl) v hv]
  · show ((cert ω) u).eval (ω ^ (1 : ℕ)) = ((cert ω) v).eval (ω ^ (1 : ℕ))
    rw [eval_edge02 ω hω 1 (Or.inl rfl) u hu, eval_edge02 ω hω 1 (Or.inl rfl) v hv]
  · show ((cert ω) u).eval (ω ^ (2 : ℕ)) = ((cert ω) v).eval (ω ^ (2 : ℕ))
    rw [eval_edge12 ω hω 2 (Or.inl rfl) u hu, eval_edge12 ω hω 2 (Or.inl rfl) v hv]
  · exact absurd (show u ∈ (∅ : Finset (Fin 3)) from hu) (Finset.notMem_empty u)
  · show ((cert ω) u).eval (ω ^ (4 : ℕ)) = ((cert ω) v).eval (ω ^ (4 : ℕ))
    rw [eval_edge01 ω hω 4 (Or.inr rfl) u hu, eval_edge01 ω hω 4 (Or.inr rfl) v hv]
  · show ((cert ω) u).eval (ω ^ (5 : ℕ)) = ((cert ω) v).eval (ω ^ (5 : ℕ))
    rw [eval_edge02 ω hω 5 (Or.inr rfl) u hu, eval_edge02 ω hω 5 (Or.inr rfl) v hv]
  · show ((cert ω) u).eval (ω ^ (6 : ℕ)) = ((cert ω) v).eval (ω ^ (6 : ℕ))
    rw [eval_edge12 ω hω 6 (Or.inr rfl) u hu, eval_edge12 ω hω 6 (Or.inr rfl) v hv]
  · exact absurd (show u ∈ (∅ : Finset (Fin 3)) from hu) (Finset.notMem_empty u)

end Identities

/-- The certificate is nonzero: `p₁ = X² + 1 ≠ 0` (its evaluation at `0` is `1`). -/
theorem cert_ne_zero : (cert ω) 1 ≠ 0 := by
  intro h
  have h0 : ((cert ω) 1).eval 0 = (1 : F) := by
    simp [cert, p₁]
  rw [h] at h0
  simp at h0

/-! ## The refutation -/

/-- **Refutation of the μ_{2^t} derandomization property.**  Over any field with an
element `ω` satisfying `ω⁴ = -1`, it is FALSE that every 3-weakly-partition-connected
agreement hypergraph on the geometric coordinates `ω⁰, …, ω⁷` admits only the zero
certificate.  Equivalently, the reduced intersection matrix of `badHypergraph` at the
geometric point is column-rank-deficient — the property consumed by the AGL24/GZ
capacity machinery fails on `μ_8 ⊆ μ_{2^t}`. -/
theorem not_kwpc_rigidity (hω : ω ^ 4 = -1) :
    ¬ ∀ (E : Fin 8 → Finset (Fin 3)), IsWeaklyPartitionConnected E 3 →
        ∀ p : Fin 3 → F[X],
          (∀ v, (p v).natDegree ≤ 2) → p 2 = 0 →
          (∀ i : Fin 8, ∀ u ∈ E i, ∀ v ∈ E i,
            (p u).eval (ω ^ (i : ℕ)) = (p v).eval (ω ^ (i : ℕ))) →
          ∀ v, p v = 0 := by
  intro hall
  exact cert_ne_zero ω
    (hall badHypergraph badHypergraph_kwpc (cert ω) (cert_natDegree_le ω)
      (cert_reference ω) (certificate_eval_agree ω hω) 1)

/-- Non-vacuity over a concrete prize-shaped prime field: `ω = 9` satisfies
`9⁴ = 6561 ≡ -1 (mod 17)` (an element of order 8 in `ZMod 17`). -/
private instance : Fact (Nat.Prime 17) := ⟨by norm_num⟩

theorem not_kwpc_rigidity_zmod17 :
    ¬ ∀ (E : Fin 8 → Finset (Fin 3)), IsWeaklyPartitionConnected E 3 →
        ∀ p : Fin 3 → (ZMod 17)[X],
          (∀ v, (p v).natDegree ≤ 2) → p 2 = 0 →
          (∀ i : Fin 8, ∀ u ∈ E i, ∀ v ∈ E i,
            (p u).eval ((9 : ZMod 17) ^ (i : ℕ)) = (p v).eval ((9 : ZMod 17) ^ (i : ℕ))) →
          ∀ v, p v = 0 :=
  not_kwpc_rigidity (9 : ZMod 17) (by decide)

end MuTwoPowDerandRefutation

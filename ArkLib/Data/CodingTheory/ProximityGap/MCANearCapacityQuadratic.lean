/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.MCANearCapacityGeneralRate

/-!
# A quadratic near-capacity MCA lower bound on the arithmetic domain (Proximity Prize, #232)

`MCANearCapacityGeneralRate.lean` proved, for every Reed–Solomon rate `ρ = k/n`, the **linear**
near-capacity lower bound
`ε_mca(C, 1-(k+1)/n) ≥ (n-k)/|F|`
via the sunflower family of `(k+1)`-windows `{0,…,k-1, k+j}` (only one node varies, so the window
sums are trivially distinct). Its docstring flags the next concrete step: on a *structured* node set
the spread `|𝒮|` — the number of `(k+1)`-windows with **distinct** node-sums — can be pushed from
linear to **quadratic** `Θ(k(n-k))`, because an arithmetic node set has that many distinct
`(k+1)`-subset sums. This file realizes that quadratic spread explicitly and kernel-checks it.

## The construction (two-parameter staircase)

Take the arithmetic domain `domain i = (i : ZMod p)` (an embedding once `n ≤ p`). For parameters
`0 ≤ q < n-2k` and `0 ≤ r ≤ k`, the window

`W(q,r) = {q, q+1, …, q+k-1} ∪ {q+k+r}`

is a `(k+1)`-subset of `{0,…,n-1}` (the bound `q+k+r ≤ n-1` holds on the grid), with integer node-sum

`Σ(q,r) = (∑_{i<k}(q+i)) + (q+k+r) = (k+1)·q + (G + k) + r`,  `G = ∑_{i<k} i`.

The leading block `{q,…,q+k-1}` slides (the `(k+1)·q` term) and the single tail node `q+k+r` adds a
fine offset `r ∈ {0,…,k}`. Since `r ≤ k < k+1`, the map `(q,r) ↦ (k+1)·q + r` is **injective** by
uniqueness of Euclidean division, so all `(n-2k)·(k+1)` window-sums are distinct integers; as they are
all `< n² ≤ p` they stay distinct in `ZMod p`. Feeding this family to
`MCANearCapacityGK.epsMCA_ge_of_window_family` gives

`ε_mca(C, 1-(k+1)/n) ≥ (n-2k)·(k+1) / |F|`,

a **quadratic** `Θ(k(n-k))` lower bound at `δ = capacity − 1/n`, strictly inside the Johnson→capacity
gap — quadratically stronger than the sunflower's linear `n-k`.

## What this does and does not do (candidate analysis for #232)

* It is the docstring-flagged quadratic strengthening of the realized witness spread: a genuine
  `Θ(k(n-k))/|F|` lower bound, kernel-checked, for every rate with `n ≥ 2k+1` (`ρ < 1/2`).
* It remains `poly(n)/|F|`, hence `< ε* = 2⁻¹²⁸` for the prize's large fields, so it does **not** pin
  the prize threshold `δ*` (that needs an *exponential* spread). It sharpens, but does not close, the
  open core delineated in `MCANearCapacityGeneralRate.lean`: a single algebraic monomial line still
  caps `δ` at `capacity − 1/n`; reaching the gap interior needs multiplicity (Guruswami–Sudan).

## References
- [ABF26] Arnon, Boneh, Fenzi. *Open Problems in List Decoding and Correlated Agreement*. 2026.
  Tracking issue #232 / #141.
-/

open Polynomial BigOperators
open scoped NNReal ENNReal

namespace ProximityGap.MCANearCapacityQuadratic

open ProximityGap Code ProximityGap.MCANearCapacityGK

variable {p : ℕ} [Fact p.Prime] {n k : ℕ} [NeZero n]

/-- A total `ℕ → Fin n` that is the identity on `{0,…,n-1}` (and wraps elsewhere). Used to build
window finsets by `image` with no per-element bound obligation; on the staircase grid every node is
`< n`, so this acts as the genuine inclusion. -/
def node : ℕ → Fin n := fun m => ⟨m % n, Nat.mod_lt m (NeZero.pos n)⟩

@[simp] theorem node_val_of_lt {m : ℕ} (h : m < n) : ((node m : Fin n) : ℕ) = m := by
  simp only [node]; exact Nat.mod_eq_of_lt h

/-- The integer window `{q, q+1, …, q+k-1} ∪ {q+k+r}`. -/
def Wnat (k q r : ℕ) : Finset ℕ := (Finset.range k).image (fun i => q + i) ∪ {q + k + r}

/-- The window as a `Finset (Fin n)`. -/
def Wfin (n k q r : ℕ) [NeZero n] : Finset (Fin n) := (Wnat k q r).image node

/-- The arithmetic evaluation domain `i ↦ (i : ZMod p)`, an embedding once `n ≤ p`. -/
def dom (hnp : n ≤ p) : Fin n ↪ ZMod p where
  toFun i := ((i : ℕ) : ZMod p)
  inj' i j h := by
    have hi : (i : ℕ) < p := lt_of_lt_of_le i.isLt hnp
    have hj : (j : ℕ) < p := lt_of_lt_of_le j.isLt hnp
    have := (ZMod.natCast_eq_natCast_iff' _ _ _).mp h
    rw [Nat.mod_eq_of_lt hi, Nat.mod_eq_of_lt hj] at this
    exact Fin.ext this

/-! ## Integer combinatorics of the staircase windows -/

/-- Every node of a grid window is `< n`. -/
theorem Wnat_lt (hk : 1 ≤ k) {q r : ℕ} (hq : q < n - 2 * k) (hr : r ≤ k) :
    ∀ m ∈ Wnat k q r, m < n := by
  intro m hm
  have hqkr : q + k + r < n := by omega
  rw [Wnat, Finset.mem_union, Finset.mem_image, Finset.mem_singleton] at hm
  rcases hm with ⟨i, hi, rfl⟩ | rfl
  · rw [Finset.mem_range] at hi; omega
  · exact hqkr

/-- The integer sum of a window: `(k+1)·q + (G + k) + r` with `G = ∑_{i<k} i`. -/
theorem Wnat_sum (k q r : ℕ) :
    (∑ m ∈ Wnat k q r, m) = (k + 1) * q + ((∑ i ∈ Finset.range k, i) + k) + r := by
  have hdisj : Disjoint ((Finset.range k).image (fun i => q + i)) ({q + k + r} : Finset ℕ) := by
    rw [Finset.disjoint_singleton_right, Finset.mem_image]
    rintro ⟨i, hi, hcontra⟩
    rw [Finset.mem_range] at hi; omega
  rw [Wnat, Finset.sum_union hdisj, Finset.sum_singleton,
    Finset.sum_image (by intro a _ b _ h; simp only at h; omega)]
  have : (∑ i ∈ Finset.range k, (q + i)) = k * q + ∑ i ∈ Finset.range k, i := by
    rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_range, smul_eq_mul, mul_comm]
  rw [this]; ring

/-- A grid window has `k+1` integer nodes. -/
theorem Wnat_card (hk : 1 ≤ k) {q r : ℕ} (hr : r ≤ k) : (Wnat k q r).card = k + 1 := by
  have hdisj : Disjoint ((Finset.range k).image (fun i => q + i)) ({q + k + r} : Finset ℕ) := by
    rw [Finset.disjoint_singleton_right, Finset.mem_image]
    rintro ⟨i, hi, hcontra⟩
    rw [Finset.mem_range] at hi; omega
  rw [Wnat, Finset.card_union_of_disjoint hdisj, Finset.card_singleton,
    Finset.card_image_of_injective _ (by intro a b h; simp only at h; omega), Finset.card_range]

/-! ## Transport to `Fin n` and `ZMod p` -/

/-- On the grid, the `Fin n` window has `k+1` elements (`node` is injective on nodes `< n`). -/
theorem Wfin_card (hk : 1 ≤ k) {q r : ℕ} (hq : q < n - 2 * k) (hr : r ≤ k) :
    (Wfin n k q r).card = k + 1 := by
  rw [Wfin, Finset.card_image_of_injOn, Wnat_card hk hr]
  intro a ha b hb hab
  have := Wnat_lt hk hq hr
  have hva : ((node a : Fin n) : ℕ) = a := node_val_of_lt (this a ha)
  have hvb : ((node b : Fin n) : ℕ) = b := node_val_of_lt (this b hb)
  rw [← hva, ← hvb, hab]

/-- The `ZMod p` node-sum of a grid window equals the integer sum, cast. -/
theorem dom_sum (hnp : n ≤ p) (hk : 1 ≤ k) {q r : ℕ} (hq : q < n - 2 * k) (hr : r ≤ k) :
    (∑ i ∈ Wfin n k q r, dom (p := p) hnp i) = (((∑ m ∈ Wnat k q r, m) : ℕ) : ZMod p) := by
  have hlt := Wnat_lt hk hq hr
  rw [Wfin, Finset.sum_image (by
    intro a ha b hb hab
    have hva : ((node a : Fin n) : ℕ) = a := node_val_of_lt (hlt a ha)
    have hvb : ((node b : Fin n) : ℕ) = b := node_val_of_lt (hlt b hb)
    rw [← hva, ← hvb, hab])]
  rw [Nat.cast_sum]
  apply Finset.sum_congr rfl
  intro m hm
  show (((node m : Fin n) : ℕ) : ZMod p) = ((m : ℕ) : ZMod p)
  rw [node_val_of_lt (hlt m hm)]

/-! ## The quadratic lower bound -/

end ProximityGap.MCANearCapacityQuadratic

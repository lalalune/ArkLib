/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Fintype.Card

/-!
# Coverage pigeonhole for multi-γ line decoding

A self-contained combinatorial double-counting / averaging bound used by the GG25 multi-γ
overlap-coverage extraction (issue #140): if many agreement sets each cover a large fraction
of the coordinates, some coordinate is covered many times.  This is the "double coverage"
step that forces a joint pair in the repaired ABF26 T4.21 line-decoding argument.

## Main results

* `Coverage.sum_card_eq_sum_degree` — incidence double-counting: `∑ |S i| = ∑ₓ deg x`.
* `Coverage.exists_degree_gt` — averaging pigeonhole: if `k·n < ∑ |S i|` some coordinate has
  degree `> k`.
-/

open Finset

namespace ArkLib.Coverage

/-- **Incidence double-counting.**  For a finite indexed family `S : κ → Finset ι` over a
fintype `ι`, the total size equals the sum over coordinates of the coordinate degree
(number of sets containing it). -/
theorem sum_card_eq_sum_degree {κ ι : Type*} [Fintype κ] [Fintype ι] [DecidableEq ι]
    (S : κ → Finset ι) :
    (∑ i, (S i).card) = ∑ x : ι, (Finset.univ.filter (fun i => x ∈ S i)).card := by
  classical
  have hcard : ∀ i, (S i).card = ∑ x : ι, (if x ∈ S i then (1 : ℕ) else 0) := by
    intro i
    rw [← Finset.card_filter]
    congr 1
    ext x; simp
  have hdeg : ∀ x : ι, (Finset.univ.filter (fun i => x ∈ S i)).card
      = ∑ i, (if x ∈ S i then (1 : ℕ) else 0) := by
    intro x; rw [Finset.card_filter]
  simp_rw [hcard, hdeg]
  exact Finset.sum_comm

/-- **Coverage pigeonhole.**  If the total agreement mass `∑ |S i|` exceeds `k · |ι|`, some
coordinate lies in strictly more than `k` of the sets — the double-coverage that forces a
joint pair in GG25 multi-γ line decoding (issue #140). -/
theorem exists_degree_gt {κ ι : Type*} [Fintype κ] [Fintype ι] [DecidableEq ι]
    (S : κ → Finset ι) (k : ℕ) (hk : k * Fintype.card ι < ∑ i, (S i).card) :
    ∃ x : ι, k < (Finset.univ.filter (fun i => x ∈ S i)).card := by
  classical
  by_contra h
  push_neg at h
  have hsum : (∑ i, (S i).card) ≤ k * Fintype.card ι := by
    rw [sum_card_eq_sum_degree]
    calc (∑ x : ι, (Finset.univ.filter (fun i => x ∈ S i)).card)
        ≤ ∑ _x : ι, k := Finset.sum_le_sum (fun x _ => h x)
      _ = k * Fintype.card ι := by
          simp [Finset.sum_const, Finset.card_univ, mul_comm]
  omega

end ArkLib.Coverage

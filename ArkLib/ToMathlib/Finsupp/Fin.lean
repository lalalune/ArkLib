/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/

import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Data.Finsupp.Basic

/-!
# Fin-indexed `Finsupp` insertion/removal helpers

Thin wrappers around `Fin.insertNth` and `Fin.removeNth` for finitely supported functions whose
domain is finite.
-/

namespace Finsupp

open Finset

variable {n : ℕ}

/-- Insert a coordinate into a finitely supported function on `Fin n`. -/
noncomputable def insertNth (p : Fin (n + 1)) (i : ℕ) (m : Fin n →₀ ℕ) :
    Fin (n + 1) →₀ ℕ :=
  Finsupp.onFinset Finset.univ (Fin.insertNth p i (fun j => m j)) (by intro a _; simp)

/-- Remove a coordinate from a finitely supported function on `Fin (n+1)`. -/
noncomputable def removeNth (p : Fin (n + 1)) (m : Fin (n + 1) →₀ ℕ) :
    Fin n →₀ ℕ :=
  Finsupp.onFinset Finset.univ (fun j => m (p.succAbove j)) (by intro a _; simp)

@[simp]
theorem insertNth_apply_same (p : Fin (n + 1)) (i : ℕ) (m : Fin n →₀ ℕ) :
    insertNth p i m p = i := by
  simp [insertNth]

@[simp]
theorem insertNth_apply_succAbove (p : Fin (n + 1)) (i : ℕ) (m : Fin n →₀ ℕ) (j : Fin n) :
    insertNth p i m (p.succAbove j) = m j := by
  simp [insertNth]

@[simp]
theorem removeNth_apply (p : Fin (n + 1)) (m : Fin (n + 1) →₀ ℕ) (j : Fin n) :
    removeNth p m j = m (p.succAbove j) := by
  simp [removeNth]

theorem insertNth_self_removeNth (p : Fin (n + 1)) (m : Fin (n + 1) →₀ ℕ) :
    insertNth p (m p) (removeNth p m) = m := by
  ext j
  refine Fin.succAboveCases p ?_ ?_ j
  · simp [insertNth]
  · intro k
    simp [insertNth, removeNth]

theorem insertNth_removeNth (p : Fin (n + 1)) {m : Fin (n + 1) →₀ ℕ} {i : ℕ}
    (h : m p = i) :
    insertNth p i (removeNth p m) = m := by
  rw [← h]
  exact insertNth_self_removeNth p m

theorem insertNth_right_injective (p : Fin (n + 1)) {i : ℕ} :
    Function.Injective (insertNth p i : (Fin n →₀ ℕ) → Fin (n + 1) →₀ ℕ) := by
  intro m m' h
  ext j
  have := congrFun (show (insertNth p i m : Fin (n + 1) → ℕ) = insertNth p i m' from
    congrArg DFunLike.coe h) (p.succAbove j)
  simpa using this

theorem sum_insertNth (m : Fin n →₀ ℕ) (i : ℕ) (p : Fin (n + 1)) :
    (insertNth p i m).sum (fun _ e => e) = m.sum (fun _ e => e) + i := by
  classical
  rw [Finsupp.sum_fintype, Finsupp.sum_fintype]
  · simp [insertNth, add_comm, Fin.sum_insertNth p i (fun j : Fin n => m j)]
  · exact fun _ => rfl
  · exact fun _ => rfl

end Finsupp

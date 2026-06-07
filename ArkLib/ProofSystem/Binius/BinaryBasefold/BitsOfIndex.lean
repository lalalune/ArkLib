/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chung Thai Nguyen, Quang Dao
-/

import ArkLib.ProofSystem.Binius.BinaryBasefold.Basic

/-!
## Binary expansion of an index as a challenge vector

`bitsOfIndex` is a small self-contained helper extracted out of `Soundness/Lift.lean` so that the
Binary Basefold *completeness* layer (`ReductionLogic`, and hence the `Steps/*` modules) does not
have to import — and so does not break on — the in-progress `Soundness/` subtree just to obtain this
two-line definition.
-/

namespace Binius.BinaryBasefold

variable {L : Type} [Field L]

/-- Binary expansion of an index as a challenge vector. -/
def bitsOfIndex {n : ℕ} (k : Fin (2 ^ n)) : Fin n → L :=
  fun j => if Nat.getBit j.val k.val = 1 then 1 else 0

/-- Coordinate form of `bitsOfIndex`. -/
theorem bitsOfIndex_apply {n : ℕ} (k : Fin (2 ^ n)) (j : Fin n) :
    bitsOfIndex (L := L) k j = if Nat.getBit j.val k.val = 1 then 1 else 0 :=
  rfl

/-- If the corresponding natural-number bit is `1`, then `bitsOfIndex` returns `1`. -/
theorem bitsOfIndex_apply_of_getBit_eq_one {n : ℕ}
    (k : Fin (2 ^ n)) (j : Fin n) (h : Nat.getBit j.val k.val = 1) :
    bitsOfIndex (L := L) k j = 1 := by
  simp [bitsOfIndex, h]

/-- If the corresponding natural-number bit is not `1`, then `bitsOfIndex` returns `0`. -/
theorem bitsOfIndex_apply_of_getBit_ne_one {n : ℕ}
    (k : Fin (2 ^ n)) (j : Fin n) (h : Nat.getBit j.val k.val ≠ 1) :
    bitsOfIndex (L := L) k j = 0 := by
  simp [bitsOfIndex, h]

/-- Every coordinate of `bitsOfIndex` is Boolean-valued. -/
theorem bitsOfIndex_apply_eq_zero_or_one {n : ℕ}
    (k : Fin (2 ^ n)) (j : Fin n) :
    bitsOfIndex (L := L) k j = 0 ∨ bitsOfIndex (L := L) k j = 1 := by
  by_cases h : Nat.getBit j.val k.val = 1
  · exact Or.inr (bitsOfIndex_apply_of_getBit_eq_one (L := L) k j h)
  · exact Or.inl (bitsOfIndex_apply_of_getBit_ne_one (L := L) k j h)

/-- `bitsOfIndex` returns `1` exactly on source coordinates whose natural bit is `1`. -/
theorem bitsOfIndex_apply_eq_one_iff {n : ℕ}
    (k : Fin (2 ^ n)) (j : Fin n) :
    bitsOfIndex (L := L) k j = 1 ↔ Nat.getBit j.val k.val = 1 := by
  constructor
  · intro h
    by_contra hbit
    have hzero := bitsOfIndex_apply_of_getBit_ne_one (L := L) k j hbit
    rw [hzero] at h
    exact zero_ne_one h
  · intro h
    exact bitsOfIndex_apply_of_getBit_eq_one (L := L) k j h

/-- `bitsOfIndex` returns `0` exactly on source coordinates whose natural bit is not `1`. -/
theorem bitsOfIndex_apply_eq_zero_iff {n : ℕ}
    (k : Fin (2 ^ n)) (j : Fin n) :
    bitsOfIndex (L := L) k j = 0 ↔ Nat.getBit j.val k.val ≠ 1 := by
  constructor
  · intro h hbit
    have hone := bitsOfIndex_apply_of_getBit_eq_one (L := L) k j hbit
    rw [hone] at h
    exact one_ne_zero h
  · intro h
    exact bitsOfIndex_apply_of_getBit_ne_one (L := L) k j h

#print axioms bitsOfIndex
#print axioms bitsOfIndex_apply
#print axioms bitsOfIndex_apply_of_getBit_eq_one
#print axioms bitsOfIndex_apply_of_getBit_ne_one
#print axioms bitsOfIndex_apply_eq_zero_or_one
#print axioms bitsOfIndex_apply_eq_one_iff
#print axioms bitsOfIndex_apply_eq_zero_iff

end Binius.BinaryBasefold

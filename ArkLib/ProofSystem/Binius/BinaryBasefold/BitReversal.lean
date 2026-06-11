/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/

import ArkLib.ProofSystem.Binius.BinaryBasefold.Prelude

/-!
# Bit-reversal equivariance: `challengeTensorProduct` vs `multilinearWeight`

The legacy `challengeTensorProduct` recursion places the *last* challenge in the LSB of the
fiber index (`idx % 2` selects `r (Fin.last n)`), while `multilinearWeight` (=
`challengeTensorExpansion`) binds bit `j` of the index to challenge `j` directly. The note at
`Prelude.lean` (above `challengeTensorExpansion`) records that the entrywise identity between
the two is *false as stated*; this file proves the correct identity: the two tensors agree up
to the **bit-reversal permutation** of the index — either as a challenge-side reversal
(`r ∘ Fin.rev`) or an index-side permutation (`bitRevPerm`).

This is the H1 utility from the issue-#317 hypothesis ledger: every consumer mixing the
closed-form `challengeTensorProduct` with `multilinearWeight`-style sums can now cross the
LSB/MSB seam through one lemma instead of a bespoke pointwise fight.

Main declarations:
* `challengeTensorProduct_get_eq_multilinearWeight_rev` — entrywise identity, challenge-side:
  `(challengeTensorProduct steps r).get idx = multilinearWeight (r ∘ Fin.rev) idx`.
* `bitRevPerm` — the bit-reversal involution of `Fin (2 ^ n)`.
* `multilinearWeight_bitRevPerm` — index-side/challenge-side exchange.
* `challengeTensorProduct_get_eq_multilinearWeight_bitRevPerm` — entrywise identity,
  index-side.
* `sum_challengeTensorProduct_mul` — tensor-weighted sums over the legacy tensor are
  `multilinearWeight`-weighted sums over bit-reversed data.

The three `binaryFinMapToNat` helpers are local copies of the ones in
`ExtractMLPCorrectness.lean` (kept here to avoid pulling that module's Relations import cone
into this leaf; consolidation target: `CompPoly.Data.Nat.Bitwise`).
-/

namespace Binius.BinaryBasefold

open Finset Nat

variable {r : ℕ} [NeZero r]
variable {L : Type} [Field L] [Fintype L] [DecidableEq L]
variable {ℓ 𝓡 : ℕ} [NeZero ℓ] [NeZero 𝓡]

noncomputable section

/-! ## Bit helpers (local copies; see module docstring) -/

private lemma getBit_le_one' (k n : ℕ) : Nat.getBit k n ≤ 1 := by
  rcases Nat.getBit_eq_zero_or_one (k := k) (n := n) with h | h <;> omega

/-! ## The bit-reversal permutation of `Fin (2 ^ n)` -/

/-- Reverse the `n`-bit binary representation of an index. -/
def bitRevAux {n : ℕ} (k : Fin (2 ^ n)) : Fin (2 ^ n) :=
  Nat.binaryFinMapToNat (fun j : Fin n => Nat.getBit (Fin.rev j).val k.val)
    (fun j => getBit_le_one' (Fin.rev j).val k.val)

lemma getBit_bitRevAux {n : ℕ} (k : Fin (2 ^ n)) (j : Fin n) :
    Nat.getBit j.val (bitRevAux k).val = Nat.getBit (Fin.rev j).val k.val := by
  unfold bitRevAux
  rw [Nat.getBit_of_binaryFinMapToNat]
  simp only [j.isLt, ↓reduceDIte, Fin.eta]

lemma bitRevAux_involutive {n : ℕ} : Function.Involutive (bitRevAux (n := n)) := by
  intro k
  apply Fin.eq_of_val_eq
  apply Nat.eq_iff_eq_all_getBits.mpr
  intro m
  by_cases hm : m < n
  · have h₁ : Nat.getBit m (bitRevAux (bitRevAux k)).val =
        Nat.getBit (Fin.rev ⟨m, hm⟩).val (bitRevAux k).val :=
      getBit_bitRevAux (bitRevAux k) ⟨m, hm⟩
    have h₂ : Nat.getBit (Fin.rev ⟨m, hm⟩).val (bitRevAux k).val =
        Nat.getBit m k.val := by
      have h := getBit_bitRevAux k (Fin.rev ⟨m, hm⟩)
      rwa [Fin.rev_rev] at h
    rw [h₁, h₂]
  · have hout : ∀ (a : Fin (2 ^ n)), Nat.getBit m a.val = 0 := by
      intro a
      have h := Nat.getBit_of_lt_two_pow (a := a) (k := m)
      simpa only [hm, ↓reduceIte] using h
    rw [hout, hout]

/-- The bit-reversal permutation of `Fin (2 ^ n)`. -/
def bitRevPerm (n : ℕ) : Equiv.Perm (Fin (2 ^ n)) :=
  Function.Involutive.toPerm bitRevAux bitRevAux_involutive

@[simp]
lemma bitRevPerm_apply {n : ℕ} (k : Fin (2 ^ n)) : bitRevPerm n k = bitRevAux k := rfl

@[simp]
lemma bitRevPerm_bitRevPerm {n : ℕ} (k : Fin (2 ^ n)) :
    bitRevPerm n (bitRevPerm n k) = k := bitRevAux_involutive k

/-! ## Index-side/challenge-side exchange for `multilinearWeight` -/

/-- Reversing the index bits is the same as reversing the challenge order. -/
lemma multilinearWeight_bitRevPerm {n : ℕ} (rc : Fin n → L) (k : Fin (2 ^ n)) :
    multilinearWeight rc (bitRevPerm n k) =
      multilinearWeight (fun j => rc (Fin.rev j)) k := by
  unfold multilinearWeight
  rw [Fintype.prod_equiv (Fin.revPerm (n := n))
    (fun j : Fin n =>
      if (bitRevPerm n k).val.testBit j.val then rc j else 1 - rc j)
    (fun j : Fin n =>
      if (bitRevPerm n k).val.testBit (Fin.rev j).val then rc (Fin.rev j)
      else 1 - rc (Fin.rev j))
    (fun j => by simp only [Fin.revPerm_apply, Fin.rev_rev])]
  apply Finset.prod_congr rfl
  intro j _
  by_cases htest : k.val.testBit j.val = true
  · have hbit : Nat.getBit j.val k.val = 1 := by
      rw [← Nat.testBit_true_eq_getBit_eq_1]
      exact htest
    have hbit' : Nat.getBit (Fin.rev j).val (bitRevPerm n k).val = 1 := by
      rw [bitRevPerm_apply, getBit_bitRevAux k (Fin.rev j), Fin.rev_rev]
      exact hbit
    have htest' : (bitRevPerm n k).val.testBit (Fin.rev j).val = true := by
      rw [Nat.testBit_true_eq_getBit_eq_1]
      exact hbit'
    simp [htest, htest']
  · have hbit : Nat.getBit j.val k.val = 0 := by
      rcases Nat.getBit_eq_zero_or_one (k := j.val) (n := k.val) with h | h
      · exact h
      · exact absurd (by rw [Nat.testBit_true_eq_getBit_eq_1]; exact h) htest
    have hbit' : Nat.getBit (Fin.rev j).val (bitRevPerm n k).val = 0 := by
      rw [bitRevPerm_apply, getBit_bitRevAux k (Fin.rev j), Fin.rev_rev]
      exact hbit
    have htest' : ¬((bitRevPerm n k).val.testBit (Fin.rev j).val = true) := by
      rw [Nat.testBit_true_eq_getBit_eq_1]
      omega
    simp [htest, htest']

/-! ## The entrywise bridge for `challengeTensorProduct` -/

private lemma rev_succ_eq {n : ℕ} (j : Fin n) :
    Fin.rev j.succ = (Fin.rev j).castSucc := by
  apply Fin.eq_of_val_eq
  simp only [Fin.val_rev, Fin.val_succ, Fin.coe_castSucc]
  omega

private lemma rev_zero_eq_last {n : ℕ} :
    Fin.rev (0 : Fin (n + 1)) = Fin.last n := by
  apply Fin.eq_of_val_eq
  simp [Fin.val_rev]

set_option maxHeartbeats 800000 in
/-- **The corrected entrywise identity** (the note above `challengeTensorExpansion` records
that the un-reversed form is false): the legacy LSB-first tensor at index `idx` is the
MSB-first `multilinearWeight` at `idx` with the challenge order reversed. -/
theorem challengeTensorProduct_get_eq_multilinearWeight_rev
    (steps : ℕ) (rc : Fin steps → L) (idx : Fin (2 ^ steps)) :
    (challengeTensorProduct (L := L) (ℓ := ℓ) (𝓡 := 𝓡) (r := r) steps rc).get idx =
      multilinearWeight (fun j => rc (Fin.rev j)) idx := by
  induction steps generalizing rc idx with
  | zero =>
    unfold multilinearWeight
    simp only [Finset.univ_eq_empty, Finset.prod_empty]
    fin_cases idx
    rfl
  | succ n ih =>
    rw [challengeTensorProduct_succ_get (L := L) (ℓ := ℓ) (𝓡 := 𝓡) (r := r) n rc idx]
    rw [ih (fun j => rc j.castSucc)]
    unfold multilinearWeight
    rw [Fin.prod_univ_succ
      (f := fun j : Fin (n + 1) =>
        if idx.val.testBit j.val then rc (Fin.rev j) else 1 - rc (Fin.rev j))]
    have hhead :
        (if idx.val % 2 = 0 then 1 - rc (Fin.last n) else rc (Fin.last n)) =
          (if idx.val.testBit (0 : Fin (n + 1)).val then rc (Fin.rev 0)
            else 1 - rc (Fin.rev 0)) := by
      rw [rev_zero_eq_last]
      rcases Nat.mod_two_eq_zero_or_one idx.val with h2 | h2
      · have ht : idx.val.testBit 0 = false := by
          rw [Nat.testBit_zero]
          simp [h2]
        simp [h2, ht, Fin.val_zero]
      · have ht : idx.val.testBit 0 = true := by
          rw [Nat.testBit_zero]
          simp [h2]
        simp [h2, ht, Fin.val_zero]
    have htail :
        ∀ j : Fin n,
          (if (idx.val / 2).testBit j.val then rc (Fin.rev j).castSucc
            else 1 - rc (Fin.rev j).castSucc) =
          (if idx.val.testBit j.succ.val then rc (Fin.rev j.succ)
            else 1 - rc (Fin.rev j.succ)) := by
      intro j
      rw [rev_succ_eq]
      have hbit : idx.val.testBit j.succ.val = (idx.val / 2).testBit j.val := by
        show idx.val.testBit (j.val + 1) = (idx.val / 2).testBit j.val
        rw [Nat.testBit_add_one]
      rw [hbit]
    rw [hhead]
    congr 1
    apply Finset.prod_congr rfl
    intro j _
    exact htail j

/-- Entrywise identity, index-side form: the legacy tensor entry at `idx` is the
`multilinearWeight` entry at the bit-reversed index. -/
theorem challengeTensorProduct_get_eq_multilinearWeight_bitRevPerm
    (steps : ℕ) (rc : Fin steps → L) (idx : Fin (2 ^ steps)) :
    (challengeTensorProduct (L := L) (ℓ := ℓ) (𝓡 := 𝓡) (r := r) steps rc).get idx =
      multilinearWeight rc (bitRevPerm steps idx) := by
  rw [challengeTensorProduct_get_eq_multilinearWeight_rev,
    multilinearWeight_bitRevPerm]

/-- Tensor-weighted sums over the legacy tensor are `multilinearWeight`-weighted sums over
bit-reversed data: `∑ k, ctp(k)·w(k) = ∑ k, mw(k)·w(bitRev k)`. -/
theorem sum_challengeTensorProduct_mul
    (steps : ℕ) (rc : Fin steps → L) (w : Fin (2 ^ steps) → L) :
    ∑ k : Fin (2 ^ steps),
        (challengeTensorProduct (L := L) (ℓ := ℓ) (𝓡 := 𝓡) (r := r) steps rc).get k * w k =
      ∑ k : Fin (2 ^ steps), multilinearWeight rc k * w (bitRevPerm steps k) := by
  have hcomp := Equiv.sum_comp (bitRevPerm steps)
    (fun k : Fin (2 ^ steps) => multilinearWeight rc k * w (bitRevPerm steps k))
  calc
    ∑ k : Fin (2 ^ steps),
        (challengeTensorProduct (L := L) (ℓ := ℓ) (𝓡 := 𝓡) (r := r) steps rc).get k * w k
      = ∑ k : Fin (2 ^ steps),
          multilinearWeight rc (bitRevPerm steps k) * w (bitRevPerm steps (bitRevPerm steps k)) := by
        apply Finset.sum_congr rfl
        intro k _
        rw [challengeTensorProduct_get_eq_multilinearWeight_bitRevPerm,
          bitRevPerm_bitRevPerm]
    _ = ∑ k : Fin (2 ^ steps), multilinearWeight rc k * w (bitRevPerm steps k) := hcomp

end

end Binius.BinaryBasefold

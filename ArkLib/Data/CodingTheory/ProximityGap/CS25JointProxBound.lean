/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.InterleavedCode

/-!
# Counting jointly-close stacks (toward T4.17, #82)

Toward the `#{jointProx}` upper bound needed to assemble the CS25 complete-CA-breakdown count
budget `hfar`. This file first establishes the cardinality of the interleaved code: a stack is
jointly `δ`-close to `C` iff its interleaving `⋈|u = uᵀ` is close to *some* interleaved codeword,
and the interleaved code `C^⋈κ = {V | ∀ k, V.transpose k ∈ C}` has exactly `|C|^|κ|` codewords
(it is the `κ`-fold product of `C`, via the transpose bijection).
-/

open Code

namespace CS25

variable {ι : Type*} [Fintype ι] [DecidableEq ι]
variable {κ : Type*} [Fintype κ] [DecidableEq κ]
variable {A : Type*} [Fintype A] [DecidableEq A]

/-- **The interleaved code is the `κ`-fold product of `C`.** As a type, `C^⋈κ ≃ (κ → C)` via the
transpose map `V ↦ (k ↦ Vᵀ k)`. -/
def interleavedCodeSetEquiv (C : Set (ι → A)) :
    ↥(interleavedCodeSet (κ := κ) C) ≃ (κ → ↥C) where
  toFun := fun V k => ⟨V.1.transpose k, V.2 k⟩
  invFun := fun g => ⟨Matrix.of (fun i k => (g k).1 i), fun k => (g k).2⟩
  left_inv := fun V => by ext i k; rfl
  right_inv := fun g => by ext k i; rfl

/-- **The interleaved code `C^⋈κ` has `|C|^|κ|` codewords.** -/
theorem interleavedCodeSet_card (C : Set (ι → A)) [Fintype ↥C]
    [Fintype ↥(interleavedCodeSet (κ := κ) C)] :
    Fintype.card ↥(interleavedCodeSet (κ := κ) C) = (Fintype.card ↥C) ^ (Fintype.card κ) := by
  rw [Fintype.card_congr (interleavedCodeSetEquiv (κ := κ) C), Fintype.card_fun]

end CS25

/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.ProofSystem.Stir.VectorChain

/-!
# The VectorIOP packaging bridge (#301)

The **VectorIOP packaging bridge** — `VectorSpec` append/seqCompose with
`toProtocolSpec` commutation, exhibiting the full vectorised STIR chain's compound spec as
`(stirChainVSpec ι F M).toProtocolSpec F` for a single literal `VectorSpec`. This is the spec
side of packaging `stirFullVectorReduction` as the `VectorIOP`-shaped object quantified over
by `stir_main` / `stir_rbr_soundness`. -/

namespace ProtocolSpec

namespace VectorSpec

open ProtocolSpec

/-- Append two vector specs (the `VectorSpec` mirror of `++ₚ`). -/
def vsAppend {m n : ℕ} (v₁ : VectorSpec m) (v₂ : VectorSpec n) : VectorSpec (m + n) :=
  ⟨Fin.vappend v₁.dir v₂.dir, Fin.vappend v₁.length v₂.length⟩

/-- Sequentially compose a family of vector specs (the `VectorSpec` mirror of `seqCompose`). -/
def vsSeqCompose {m : ℕ} {n : Fin m → ℕ} (v : ∀ i, VectorSpec (n i)) :
    VectorSpec (Fin.vsum n) :=
  ⟨Fin.vflatten (fun i => (v i).dir), Fin.vflatten (fun i => (v i).length)⟩

/-- Postcomposition distributes over `Fin.vappend`. -/
theorem comp_vappend {α β : Type*} {m n : ℕ} (f : α → β) (a : Fin m → α) (b : Fin n → α) :
    f ∘ Fin.vappend a b = Fin.vappend (f ∘ a) (f ∘ b) := by
  funext i
  simp only [Function.comp_apply, Fin.vappend_eq_append]
  rcases Nat.lt_or_ge i.1 m with h | h
  · have hi : i = Fin.castAdd n ⟨i.1, h⟩ := by ext; rfl
    rw [hi, Fin.append_left, Fin.append_left]
    rfl
  · have hi : i = Fin.natAdd m ⟨i.1 - m, by omega⟩ := by
      ext; simp; omega
    rw [hi, Fin.append_right, Fin.append_right]
    rfl

/-- Postcomposition distributes over `Fin.vflatten`. -/
theorem comp_vflatten {α β : Type*} {m : ℕ} {n : Fin m → ℕ} (f : α → β)
    (v : ∀ i, Fin (n i) → α) :
    f ∘ Fin.vflatten v = Fin.vflatten (fun i => f ∘ v i) := by
  funext k
  have hk : k = Fin.embedSum (Fin.splitSum k).1 (Fin.splitSum k).2 := by simp
  rw [hk]
  simp only [Function.comp_apply, Fin.vflatten_embedSum]

/-- **`toProtocolSpec` commutes with append.** -/
theorem toProtocolSpec_vsAppend (A : Type) {m n : ℕ} (v₁ : VectorSpec m) (v₂ : VectorSpec n) :
    (v₁.vsAppend v₂).toProtocolSpec A
      = (v₁.toProtocolSpec A) ++ₚ (v₂.toProtocolSpec A) := by
  unfold toProtocolSpec vsAppend ProtocolSpec.append
  congr 1
  show (fun i => Vector A (Fin.vappend v₁.length v₂.length i))
    = Fin.vappend (fun i => Vector A (v₁.length i)) (fun i => Vector A (v₂.length i))
  exact comp_vappend (Vector A) v₁.length v₂.length

/-- **`toProtocolSpec` commutes with sequential composition.** -/
theorem toProtocolSpec_vsSeqCompose (A : Type) {m : ℕ} {n : Fin m → ℕ}
    (v : ∀ i, VectorSpec (n i)) :
    (vsSeqCompose v).toProtocolSpec A
      = ProtocolSpec.seqCompose (fun i => (v i).toProtocolSpec A) := by
  unfold toProtocolSpec vsSeqCompose ProtocolSpec.seqCompose
  congr 1
  show (fun k => Vector A (Fin.vflatten (fun i => (v i).length) k))
    = Fin.vflatten (fun i k => Vector A ((v i).length k))
  exact comp_vflatten (Vector A) (fun i => (v i).length)

end VectorSpec

end ProtocolSpec

namespace StirIOP

namespace Round3

open OracleSpec OracleComp ProtocolSpec ProtocolSpec.VectorSpec STIR NNReal StirIOP.Round

variable {F : Type} [Field F] [Fintype F] [DecidableEq F] [SampleableType F]
variable {ι : Type} [Fintype ι] [DecidableEq ι]

/-- **The full STIR chain as a single literal `VectorSpec`**:
`[C_fold] ++ᵥ (g,C_out,C_shift) ++ᵥ (g,C_out,C_shift)×M ++ᵥ [p, C_fin]`. -/
def stirChainVSpec (ι F : Type) [Fintype ι] (M : ℕ) :
    ProtocolSpec.VectorSpec (1 + (3 + ((Fin.vsum fun _ : Fin M => 3) + 2))) :=
  stirInitVSpec.vsAppend
    ((stirRound3VSpec ι F).vsAppend
      ((VectorSpec.vsSeqCompose (fun _ : Fin M => stirRound3VSpec ι F)).vsAppend
        (stirFinalVSpec ι F)))

/-- **The packaging bridge**: the compound protocol spec of `stirFullVectorReduction` IS the
`toProtocolSpec` image of the single literal `stirChainVSpec` — so the full vectorised chain
is a protocol over a genuine `VectorSpec`-generated wire format, as `stir_main` /
`stir_rbr_soundness` demand. -/
theorem stirChainVSpec_toProtocolSpec (M : ℕ) :
    (stirChainVSpec ι F M).toProtocolSpec F
      = (stirInitVSpec.toProtocolSpec F) ++ₚ
          (((stirRound3VSpec ι F).toProtocolSpec F) ++ₚ
            ((ProtocolSpec.seqCompose
                (fun _ : Fin M => (stirRound3VSpec ι F).toProtocolSpec F))
              ++ₚ ((stirFinalVSpec ι F).toProtocolSpec F))) := by
  unfold stirChainVSpec
  rw [toProtocolSpec_vsAppend, toProtocolSpec_vsAppend, toProtocolSpec_vsAppend,
    toProtocolSpec_vsSeqCompose]

end Round3

end StirIOP

#print axioms ProtocolSpec.VectorSpec.toProtocolSpec_vsAppend
#print axioms ProtocolSpec.VectorSpec.toProtocolSpec_vsSeqCompose
#print axioms StirIOP.Round3.stirChainVSpec_toProtocolSpec

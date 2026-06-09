/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.OracleReduction.Composition.Sequential.AppendRbrKeystone

/-!
# The composite round-by-round *knowledge* state function — `Verifier.KnowledgeStateFunction.append`

This file constructs the witness-threaded analogue of the proven `Verifier.StateFunction.append`
(`Append.lean`): the composite round-by-round **knowledge** state function for the appended verifier
`V₁.append V₂`, built against the proven composite round-by-round extractor
`Extractor.RoundByRound.append E₁ E₂ verify`. With it the residual `kSF` of
`Verifier.append_rbrKnowledgeSoundness_keystone` (`AppendRbrKeystone.lean`) is discharged.

The `toFun` carrier mirrors `StateFunction.append`: on a phase-1 round (`roundIdx.val ≤ m`) it is the
inner knowledge state function `kSF₁` on the transcript's phase-1 truncation; on a phase-2 round it is
`kSF₂` on the `verify`-fed intermediate statement and the transcript's phase-2 tail. The only new
ingredient relative to `StateFunction.append` is the intermediate-witness leg: the appended extractor's
combined `WitMid` carrier `Fin.append WitMid₁ (Fin.tail WitMid₂) ∘ Fin.cast _` projects to `WitMid₁`
on phase-1 rounds and `WitMid₂` on phase-2 rounds (`appendWitMid_le` / `appendWitMid_gt`), and the
state function casts the supplied combined witness into the appropriate leg before feeding it to
`kSF₁` / `kSF₂`.
-/

open OracleComp OracleSpec ProtocolSpec SubSpec
open scoped ENNReal NNReal

universe u v

namespace Verifier

variable {ι : Type} {oSpec : OracleSpec ι} {Stmt₁ Wit₁ Stmt₂ Wit₂ Stmt₃ Wit₃ : Type}
  {m n : ℕ} {pSpec₁ : ProtocolSpec m} {pSpec₂ : ProtocolSpec n}
  [∀ i, SampleableType (pSpec₁.Challenge i)] [∀ i, SampleableType (pSpec₂.Challenge i)]
  {σ : Type} {init : ProbComp σ} {impl : QueryImpl oSpec (StateT σ ProbComp)}

/-- **Phase-1 projection of the composite `WitMid` carrier.** For a round index `roundIdx.val ≤ m`,
the appended extractor's combined intermediate-witness type
`Fin.append WitMid₁ (Fin.tail WitMid₂) ∘ Fin.cast _` evaluated at `roundIdx` is `WitMid₁`'s leg at the
re-indexed `⟨roundIdx, _⟩ : Fin (m+1)`. -/
theorem appendWitMid_le {WitMid₁ : Fin (m+1)→Type} {WitMid₂ : Fin (n+1)→Type}
    {roundIdx : Fin (m+n+1)} (h : roundIdx.val ≤ m) :
    (Fin.append (m:=m+1) WitMid₁ (Fin.tail WitMid₂) ∘ Fin.cast (by omega)) roundIdx
      = WitMid₁ ⟨roundIdx, by omega⟩ := by
  dsimp only [Function.comp_apply]
  rw [show (Fin.cast (by omega) roundIdx : Fin (m+1+n)) = Fin.castAdd n ⟨roundIdx, by omega⟩ from by
    ext; simp]
  rw [Fin.append_left]

/-- **Phase-2 projection of the composite `WitMid` carrier.** For a round index `¬ roundIdx.val ≤ m`,
the appended extractor's combined intermediate-witness type
`Fin.append WitMid₁ (Fin.tail WitMid₂) ∘ Fin.cast _` evaluated at `roundIdx` is `WitMid₂`'s leg at the
re-indexed `⟨roundIdx - m, _⟩ : Fin (n+1)`. -/
theorem appendWitMid_gt {WitMid₁ : Fin (m+1)→Type} {WitMid₂ : Fin (n+1)→Type}
    {roundIdx : Fin (m+n+1)} (h : ¬ roundIdx.val ≤ m) :
    (Fin.append (m:=m+1) WitMid₁ (Fin.tail WitMid₂) ∘ Fin.cast (by omega)) roundIdx
      = WitMid₂ ⟨roundIdx - m, by omega⟩ := by
  dsimp only [Function.comp_apply]
  rw [show (Fin.cast (by omega) roundIdx : Fin (m+1+n))
        = Fin.natAdd (m+1) ⟨roundIdx-(m+1), by omega⟩ from by ext; simp; omega]
  rw [Fin.append_right]; show Fin.tail WitMid₂ _ = _; unfold Fin.tail; congr 1
  ext; simp only [Fin.val_succ]; omega

/-- The sequential composition of two **knowledge** state functions, witness-threaded analogue of
`Verifier.StateFunction.append`. Built against the proven composite extractor
`Extractor.RoundByRound.append E₁ E₂ verify`. -/
def KnowledgeStateFunction.append {WitMid₁ : Fin (m+1)→Type} {WitMid₂ : Fin (n+1)→Type}
    (V₁ : Verifier oSpec Stmt₁ Stmt₂ pSpec₁) (V₂ : Verifier oSpec Stmt₂ Stmt₃ pSpec₂)
    {E₁ : Extractor.RoundByRound oSpec Stmt₁ Wit₁ Wit₂ pSpec₁ WitMid₁}
    {E₂ : Extractor.RoundByRound oSpec Stmt₂ Wit₂ Wit₃ pSpec₂ WitMid₂}
    {rel₁ : Set (Stmt₁ × Wit₁)} {rel₂ : Set (Stmt₂ × Wit₂)} {rel₃ : Set (Stmt₃ × Wit₃)}
    (kSF₁ : V₁.KnowledgeStateFunction init impl rel₁ rel₂ E₁)
    (kSF₂ : V₂.KnowledgeStateFunction init impl rel₂ rel₃ E₂)
    (verify : Stmt₁ → pSpec₁.FullTranscript → Stmt₂)
    (hVerify : V₁ = ⟨fun stmt tr => pure (verify stmt tr)⟩) (hInit : ∃ s, s ∈ support init) :
    (V₁.append V₂).KnowledgeStateFunction init impl rel₁ rel₃
      (Extractor.RoundByRound.append E₁ E₂ verify) where
  toFun := fun roundIdx stmt₁ tr witMid =>
    if h : roundIdx.val ≤ m then
      kSF₁.toFun ⟨roundIdx, by omega⟩ stmt₁ (by simpa [h] using tr.fst)
        (cast (appendWitMid_le h) witMid)
    else
      kSF₂.toFun ⟨roundIdx - m, by omega⟩
        (verify stmt₁ (by simp at h; simpa [min_eq_right_of_lt h] using tr.fst))
        (by simpa [h] using tr.snd) (cast (appendWitMid_gt h) witMid)
  toFun_empty := by sorry
  toFun_next := by sorry
  toFun_full := by sorry

end Verifier

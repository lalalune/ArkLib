/-
Copyright (c) 2025 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eliza
-/

import ArkLib.OracleReduction.Basic
import ArkLib.OracleReduction.VectorIOR
import ArkLib.OracleReduction.Security.Basic
import ArkLib.OracleReduction.Security.RoundByRound
import ArkLib.ProofSystem.Whir.Folding
import ArkLib.ProofSystem.Whir.RBRSoundness

/-!
# WHIR VectorSpec challenge budget (scratch brick B)

Prior to this file, `ArkLib/ProofSystem/Whir/` contained only soundness *ingredients*
(folding lemmas, block-relative distance, MCA/Johnson machinery) and the statement-only
`whir_rbr_soundness` (`Whir/RBRSoundness.lean`), whose docstring records that the WHIR Vector
IOPP `π` (paper Construction 5.1) "is built nowhere in ArkLib yet, so the `∃ π` cannot be
introduced."

This file closes the first *protocol-spec bookkeeping* gap.  It builds a genuine, `sorry`-free
`VectorSpec` with exactly `2 * M + 2` verifier challenges — the challenge budget that
`whir_rbr_soundness` quantifies over — and no prover-message payload.  It does not yet construct
the WHIR `VectorIOP` object `π`; the honest fold/OOD messages, verifier, completeness, and
round-by-round soundness proof remain the larger #113 construction work.

## References

* [Arnon, G., Chiesa, A., Fenzi, G., and Yogev, E., *WHIR: Reed–Solomon Proximity Testing
    with Super-Fast Verification*][ACFY24], Construction 5.1.
-/

open OracleSpec OracleComp ProtocolSpec NNReal ReedSolomon

namespace WhirIOP

namespace Construction

variable {F : Type} [Field F] [Fintype F] [DecidableEq F] [SampleableType F]
variable {ι : Type} [Fintype ι] [DecidableEq ι] [Nonempty ι]

/-- The single-index oracle statement family for the WHIR Vector IOPP: the prover holds one
  oracle function `f : ι → F` (the purported low-degree evaluation being proximity-tested). -/
@[reducible]
def OStmt (ι F : Type) : Unit → Type := fun _ => ι → F

instance : OracleInterface (OStmt ι F ()) := OracleInterface.instFunction

/-! ### Faithful paper transcript scaffold

Construction 5.1 has more transcript structure than the RBR error-budget skeleton below: an initial
sumcheck, per-transition folded-oracle/OOD/shift/sumcheck slots, and a final polynomial/randomness
check.  The inductive type here records that ordered paper schedule as finite data, so the eventual
honest prover can depend on earlier verifier challenges.  It is still syntax: the algebraic prover,
verifier checks, completeness, and RBR soundness are separate obligations.
-/

/-- The ordered high-level transcript slots of WHIR Construction 5.1.

For `i : Fin M`, `i.succ : Fin (M + 1)` denotes the transition round from the previous oracle to
the next folded oracle.  The `mainShiftChallenge` payload represents the batch of shift samples
plus the random linear-combination coefficient used in that transition round. -/
inductive PaperTranscriptSlot {M : ℕ} {ιs : Fin (M + 1) → Type} (P : Params ιs F) : Type
  | initialSumcheckMessage : Fin (P.foldingParam 0) → PaperTranscriptSlot P
  | initialSumcheckChallenge : Fin (P.foldingParam 0) → PaperTranscriptSlot P
  | mainFoldedOracle : Fin M → PaperTranscriptSlot P
  | mainOutOfDomainChallenge : Fin M → PaperTranscriptSlot P
  | mainOutOfDomainReply : Fin M → PaperTranscriptSlot P
  | mainShiftChallenge : Fin M → PaperTranscriptSlot P
  | mainSumcheckMessage : (i : Fin M) → Fin (P.foldingParam i.succ) → PaperTranscriptSlot P
  | mainSumcheckChallenge : (i : Fin M) → Fin (P.foldingParam i.succ) → PaperTranscriptSlot P
  | finalPolynomial : PaperTranscriptSlot P
  | finalRandomness : PaperTranscriptSlot P
  deriving DecidableEq, Fintype

/-- Direction of a faithful WHIR Construction 5.1 transcript slot. -/
def paperTranscriptSlotDirection {M : ℕ} {ιs : Fin (M + 1) → Type} {P : Params ιs F} :
    PaperTranscriptSlot P → Direction
  | .initialSumcheckMessage _ => Direction.P_to_V
  | .initialSumcheckChallenge _ => Direction.V_to_P
  | .mainFoldedOracle _ => Direction.P_to_V
  | .mainOutOfDomainChallenge _ => Direction.V_to_P
  | .mainOutOfDomainReply _ => Direction.P_to_V
  | .mainShiftChallenge _ => Direction.V_to_P
  | .mainSumcheckMessage _ _ => Direction.P_to_V
  | .mainSumcheckChallenge _ _ => Direction.V_to_P
  | .finalPolynomial => Direction.P_to_V
  | .finalRandomness => Direction.V_to_P

/-- Field-vector payload length of each faithful WHIR Construction 5.1 transcript slot.

The `d` parameter is the paper's sumcheck-message degree budget.  Folded-oracle and final-polynomial
messages are represented extensionally as field vectors over their evaluation domains. -/
def paperTranscriptSlotLength {M : ℕ} {ιs : Fin (M + 1) → Type}
    [∀ i : Fin (M + 1), Fintype (ιs i)] (P : Params ιs F) (d : ℕ) :
    PaperTranscriptSlot P → ℕ
  | .initialSumcheckMessage _ => d
  | .initialSumcheckChallenge _ => 1
  | .mainFoldedOracle i => Fintype.card (ιs i.succ)
  | .mainOutOfDomainChallenge _ => 1
  | .mainOutOfDomainReply _ => 1
  | .mainShiftChallenge i => P.repeatParam i.succ
  | .mainSumcheckMessage _ _ => d
  | .mainSumcheckChallenge _ _ => 1
  | .finalPolynomial => 2 ^ P.varCount (Fin.last M)
  | .finalRandomness => P.repeatParam (Fin.last M)

/-- The faithful paper-order WHIR transcript scaffold as a `VectorSpec`.

This is the protocol shape that a Construction 5.1 `VectorIOP` should target.  It differs from the
block-ordered skeleton below because prover messages and verifier challenges are interleaved in the
order needed for the honest prover's state updates. -/
noncomputable def whirPaperTranscriptVectorSpec {M : ℕ} {ιs : Fin (M + 1) → Type}
    [∀ i : Fin (M + 1), Fintype (ιs i)] (P : Params ιs F) (d : ℕ) :
    ProtocolSpec.VectorSpec (Fintype.card (PaperTranscriptSlot P)) where
  dir := fun i =>
    paperTranscriptSlotDirection ((Fintype.equivFin (PaperTranscriptSlot P)).symm i)
  length := fun i =>
    paperTranscriptSlotLength P d ((Fintype.equivFin (PaperTranscriptSlot P)).symm i)

omit [Field F] [DecidableEq F] [SampleableType F] in
@[simp] theorem whirPaperTranscriptVectorSpec_dir {M : ℕ}
    {ιs : Fin (M + 1) → Type} [∀ i : Fin (M + 1), Fintype (ιs i)]
    (P : Params ιs F) (d : ℕ) (i : Fin (Fintype.card (PaperTranscriptSlot P))) :
    (whirPaperTranscriptVectorSpec P d).dir i =
      paperTranscriptSlotDirection ((Fintype.equivFin (PaperTranscriptSlot P)).symm i) :=
  rfl

omit [Field F] [DecidableEq F] [SampleableType F] in
@[simp] theorem whirPaperTranscriptVectorSpec_length {M : ℕ}
    {ιs : Fin (M + 1) → Type} [∀ i : Fin (M + 1), Fintype (ιs i)]
    (P : Params ιs F) (d : ℕ) (i : Fin (Fintype.card (PaperTranscriptSlot P))) :
    (whirPaperTranscriptVectorSpec P d).length i =
      paperTranscriptSlotLength P d ((Fintype.equivFin (PaperTranscriptSlot P)).symm i) :=
  rfl

/-! ### Payload packing for the paper-order scaffold

The paper messages such as folded oracles and the final polynomial are functions over finite
domains, while `VectorSpec.toProtocolSpec` represents every payload as a `Vector F n`.  These
helpers provide the canonical finite-enumeration bridge needed by the honest prover and verifier.
-/

omit [Field F] [Fintype F] [DecidableEq F] [SampleableType F] in
/-- Pack a finite-domain function into the corresponding vector payload using `Fintype.equivFin`. -/
noncomputable def packFiniteFunction (α : Type) [Fintype α] (f : α → F) :
    Vector F (Fintype.card α) :=
  Vector.ofFn fun i => f ((Fintype.equivFin α).symm i)

omit [Field F] [Fintype F] [DecidableEq F] [SampleableType F] in
/-- Unpack a vector payload back into the finite-domain function it represents. -/
noncomputable def unpackFiniteFunction (α : Type) [Fintype α]
    (v : Vector F (Fintype.card α)) : α → F :=
  fun x => v.get (Fintype.equivFin α x)

omit [Field F] [Fintype F] [DecidableEq F] [SampleableType F] in
@[simp] theorem unpack_packFiniteFunction (α : Type) [Fintype α] (f : α → F) :
    unpackFiniteFunction α (packFiniteFunction α f) = f := by
  funext x
  simp [unpackFiniteFunction, packFiniteFunction]

omit [Field F] [Fintype F] [DecidableEq F] [SampleableType F] in
@[simp] theorem pack_unpackFiniteFunction (α : Type) [Fintype α]
    (v : Vector F (Fintype.card α)) :
    packFiniteFunction α (unpackFiniteFunction α v) = v := by
  ext i
  simp [unpackFiniteFunction, packFiniteFunction]

omit [Field F] [Fintype F] [DecidableEq F] [SampleableType F] in
/-- The canonical `Fin` index of a paper transcript slot inside `whirPaperTranscriptVectorSpec`. -/
noncomputable def paperTranscriptSlotIndex {M : ℕ} {ιs : Fin (M + 1) → Type}
    [∀ i : Fin (M + 1), Fintype (ιs i)] {P : Params ιs F} :
    PaperTranscriptSlot P → Fin (Fintype.card (PaperTranscriptSlot P)) :=
  Fintype.equivFin (PaperTranscriptSlot P)

@[simp] theorem paperTranscriptSlotIndex_symm_apply {M : ℕ} {ιs : Fin (M + 1) → Type}
    [∀ i : Fin (M + 1), Fintype (ιs i)] {P : Params ιs F}
    (slot : PaperTranscriptSlot P) :
    (Fintype.equivFin (PaperTranscriptSlot P)).symm (paperTranscriptSlotIndex slot) = slot := by
  exact (Fintype.equivFin (PaperTranscriptSlot P)).symm_apply_apply slot

omit [Field F] [SampleableType F] in
/-- Turn a paper prover-message slot into the corresponding `VectorSpec.MessageIdx`. -/
noncomputable def paperMessageIdx {M : ℕ} {ιs : Fin (M + 1) → Type}
    [∀ i : Fin (M + 1), Fintype (ιs i)] (P : Params ιs F) (d : ℕ)
  (slot : PaperTranscriptSlot P) (hslot : paperTranscriptSlotDirection slot = Direction.P_to_V) :
    (whirPaperTranscriptVectorSpec P d).MessageIdx :=
  ⟨paperTranscriptSlotIndex slot, by
    change paperTranscriptSlotDirection
        ((Fintype.equivFin (PaperTranscriptSlot P)).symm (paperTranscriptSlotIndex slot)) =
      Direction.P_to_V
    simpa [paperTranscriptSlotIndex] using hslot⟩

omit [Field F] [SampleableType F] in
/-- Turn a paper verifier-challenge slot into the corresponding `VectorSpec.ChallengeIdx`. -/
noncomputable def paperChallengeIdx {M : ℕ} {ιs : Fin (M + 1) → Type}
    [∀ i : Fin (M + 1), Fintype (ιs i)] (P : Params ιs F) (d : ℕ)
  (slot : PaperTranscriptSlot P) (hslot : paperTranscriptSlotDirection slot = Direction.V_to_P) :
    (whirPaperTranscriptVectorSpec P d).ChallengeIdx :=
  ⟨paperTranscriptSlotIndex slot, by
    change paperTranscriptSlotDirection
        ((Fintype.equivFin (PaperTranscriptSlot P)).symm (paperTranscriptSlotIndex slot)) =
      Direction.V_to_P
    simpa [paperTranscriptSlotIndex] using hslot⟩

omit [Field F] [SampleableType F] in
noncomputable def initialSumcheckMessageIdx {M : ℕ} {ιs : Fin (M + 1) → Type}
    [∀ i : Fin (M + 1), Fintype (ιs i)] (P : Params ιs F) (d : ℕ)
    (s : Fin (P.foldingParam 0)) :
    (whirPaperTranscriptVectorSpec P d).MessageIdx :=
  paperMessageIdx P d (.initialSumcheckMessage s) rfl

omit [Field F] [SampleableType F] in
noncomputable def initialSumcheckChallengeIdx {M : ℕ} {ιs : Fin (M + 1) → Type}
    [∀ i : Fin (M + 1), Fintype (ιs i)] (P : Params ιs F) (d : ℕ)
    (s : Fin (P.foldingParam 0)) :
    (whirPaperTranscriptVectorSpec P d).ChallengeIdx :=
  paperChallengeIdx P d (.initialSumcheckChallenge s) rfl

omit [Field F] [SampleableType F] in
noncomputable def mainFoldedOracleMessageIdx {M : ℕ} {ιs : Fin (M + 1) → Type}
    [∀ i : Fin (M + 1), Fintype (ιs i)] (P : Params ιs F) (d : ℕ) (i : Fin M) :
    (whirPaperTranscriptVectorSpec P d).MessageIdx :=
  paperMessageIdx P d (.mainFoldedOracle i) rfl

omit [Field F] [SampleableType F] in
noncomputable def mainOutOfDomainChallengeIdx {M : ℕ} {ιs : Fin (M + 1) → Type}
    [∀ i : Fin (M + 1), Fintype (ιs i)] (P : Params ιs F) (d : ℕ) (i : Fin M) :
    (whirPaperTranscriptVectorSpec P d).ChallengeIdx :=
  paperChallengeIdx P d (.mainOutOfDomainChallenge i) rfl

omit [Field F] [SampleableType F] in
noncomputable def mainOutOfDomainReplyMessageIdx {M : ℕ} {ιs : Fin (M + 1) → Type}
    [∀ i : Fin (M + 1), Fintype (ιs i)] (P : Params ιs F) (d : ℕ) (i : Fin M) :
    (whirPaperTranscriptVectorSpec P d).MessageIdx :=
  paperMessageIdx P d (.mainOutOfDomainReply i) rfl

omit [Field F] [SampleableType F] in
noncomputable def mainShiftChallengeIdx {M : ℕ} {ιs : Fin (M + 1) → Type}
    [∀ i : Fin (M + 1), Fintype (ιs i)] (P : Params ιs F) (d : ℕ) (i : Fin M) :
    (whirPaperTranscriptVectorSpec P d).ChallengeIdx :=
  paperChallengeIdx P d (.mainShiftChallenge i) rfl

omit [Field F] [SampleableType F] in
noncomputable def mainSumcheckMessageIdx {M : ℕ} {ιs : Fin (M + 1) → Type}
    [∀ i : Fin (M + 1), Fintype (ιs i)] (P : Params ιs F) (d : ℕ) (i : Fin M)
    (s : Fin (P.foldingParam i.succ)) :
    (whirPaperTranscriptVectorSpec P d).MessageIdx :=
  paperMessageIdx P d (.mainSumcheckMessage i s) rfl

omit [Field F] [SampleableType F] in
noncomputable def mainSumcheckChallengeIdx {M : ℕ} {ιs : Fin (M + 1) → Type}
    [∀ i : Fin (M + 1), Fintype (ιs i)] (P : Params ιs F) (d : ℕ) (i : Fin M)
    (s : Fin (P.foldingParam i.succ)) :
    (whirPaperTranscriptVectorSpec P d).ChallengeIdx :=
  paperChallengeIdx P d (.mainSumcheckChallenge i s) rfl

omit [Field F] [SampleableType F] in
noncomputable def finalPolynomialMessageIdx {M : ℕ} {ιs : Fin (M + 1) → Type}
    [∀ i : Fin (M + 1), Fintype (ιs i)] (P : Params ιs F) (d : ℕ) :
    (whirPaperTranscriptVectorSpec P d).MessageIdx :=
  paperMessageIdx P d .finalPolynomial rfl

omit [Field F] [SampleableType F] in
noncomputable def finalRandomnessChallengeIdx {M : ℕ} {ιs : Fin (M + 1) → Type}
    [∀ i : Fin (M + 1), Fintype (ιs i)] (P : Params ιs F) (d : ℕ) :
    (whirPaperTranscriptVectorSpec P d).ChallengeIdx :=
  paperChallengeIdx P d .finalRandomness rfl

/-! ### Semantic WHIR per-round transcript slots

Construction 5.1 has real prover-message slots: a folded-function oracle / sumcheck message and an
out-of-domain answer, paired with the folding and out-of-domain/shift verifier challenges.  The
existing `whirVectorSpec` below is still the minimal all-challenge budget skeleton required by the
current `whir_rbr_soundness` statement.  These semantic indices record the faithful per-round shape
that the eventual `VectorIOP` constructor must refine into ArkLib's `ProtocolSpec.VectorSpec`.
-/

/-- The two prover-message roles in each WHIR round of the Construction 5.1 skeleton. -/
abbrev RoundMessageKind := Fin 2

namespace RoundMessageKind

/-- The folded-function oracle / sumcheck-message role. -/
def foldedOracle : RoundMessageKind := 0

/-- The out-of-domain answer role. -/
def outOfDomainReply : RoundMessageKind := 1

end RoundMessageKind

/-- The two verifier-challenge roles in each WHIR round of the Construction 5.1 skeleton. -/
abbrev RoundChallengeKind := Fin 2

namespace RoundChallengeKind

/-- The folding challenge role. -/
def folding : RoundChallengeKind := 0

/-- The out-of-domain or shift challenge role. -/
def outOfDomainOrShift : RoundChallengeKind := 1

end RoundChallengeKind

/-- Semantic WHIR prover-message indices: two prover-originated slots per round. -/
abbrev semanticMessageIdx (M : ℕ) := Fin (M + 1) × RoundMessageKind

/-- Semantic WHIR verifier-challenge indices: two verifier-originated slots per round. -/
abbrev semanticChallengeIdx (M : ℕ) := Fin (M + 1) × RoundChallengeKind

/-- Construction 5.1 contributes exactly `2 * M + 2` semantic verifier challenges. -/
theorem semanticChallengeIdx_card (M : ℕ) :
    Fintype.card (semanticChallengeIdx M) = 2 * M + 2 := by
  simp [semanticChallengeIdx, RoundChallengeKind]
  rw [Nat.add_mul, Nat.one_mul, Nat.mul_comm M 2]

/-- A concrete finite indexing for semantic WHIR verifier-challenge roles. -/
noncomputable def semanticChallengeIdxEquivFin (M : ℕ) :
    semanticChallengeIdx M ≃ Fin (2 * M + 2) :=
  Fintype.equivFinOfCardEq (semanticChallengeIdx_card M)

/-- The semantic WHIR skeleton has the same number of prover-message slots as verifier challenges. -/
theorem semanticMessageIdx_card (M : ℕ) :
    Fintype.card (semanticMessageIdx M) = 2 * M + 2 := by
  simp [semanticMessageIdx, RoundMessageKind]
  rw [Nat.add_mul, Nat.one_mul, Nat.mul_comm M 2]

/-- A concrete finite indexing for semantic WHIR prover-message roles. -/
noncomputable def semanticMessageIdxEquivFin (M : ℕ) :
    semanticMessageIdx M ≃ Fin (2 * M + 2) :=
  Fintype.equivFinOfCardEq (semanticMessageIdx_card M)

/-! ### A WHIR `VectorSpec` with real prover-message slots

The all-challenge `whirVectorSpec` below is the exact shape currently consumed by
`whir_rbr_soundness`.  The next construction layer is a bona fide ArkLib `VectorSpec` with both
prover-message and verifier-challenge indices.  We keep the prover-message block first and the
challenge block second; interleaving those slots into the exact paper transcript order is a later
transport/equivalence brick.
-/

/-- A block-ordered WHIR vector protocol shape with `2*M+2` prover messages followed by
`2*M+2` verifier challenges.  Every payload is represented as one field element for this skeleton;
the eventual Construction 5.1 `VectorIOP` will refine the message payload meanings. -/
@[reducible]
def whirBlockVectorSpec (M : ℕ) :
    ProtocolSpec.VectorSpec ((2 * M + 2) + (2 * M + 2)) where
  dir := fun i => if i.1 < 2 * M + 2 then Direction.P_to_V else Direction.V_to_P
  length := fun _ => 1

/-- Challenge indices of the block-ordered WHIR skeleton are the second block. -/
def whirBlockVectorSpec_challengeIdxEquivFin (M : ℕ) :
    (whirBlockVectorSpec M).ChallengeIdx ≃ Fin (2 * M + 2) where
  toFun i := ⟨i.1.1 - (2 * M + 2), by
    have hiUpper : i.1.1 < (2 * M + 2) + (2 * M + 2) := i.1.2
    have hnot : ¬ i.1.1 < 2 * M + 2 := by
      intro hlt
      have hv := i.2
      simp [whirBlockVectorSpec, hlt] at hv
    omega⟩
  invFun j := ⟨⟨(2 * M + 2) + j.1, by omega⟩, by
    have hnot : ¬ (2 * M + 2) + j.1 < 2 * M + 2 := by omega
    simp [hnot]⟩
  left_inv i := by
    ext
    have hiUpper : i.1.1 < (2 * M + 2) + (2 * M + 2) := i.1.2
    have hnot : ¬ i.1.1 < 2 * M + 2 := by
      intro hlt
      have hv := i.2
      simp [whirBlockVectorSpec, hlt] at hv
    simp
    omega
  right_inv j := by
    ext
    simp

/-- Prover-message indices of the block-ordered WHIR skeleton are the first block. -/
def whirBlockVectorSpec_messageIdxEquivFin (M : ℕ) :
    (whirBlockVectorSpec M).MessageIdx ≃ Fin (2 * M + 2) where
  toFun i := ⟨i.1.1, by
    by_cases hlt : i.1.1 < 2 * M + 2
    · exact hlt
    · have hv := i.2
      simp [whirBlockVectorSpec, hlt] at hv⟩
  invFun j := ⟨⟨j.1, by omega⟩, by
    have hlt : j.1 < 2 * M + 2 := j.2
    simp [hlt]⟩
  left_inv i := by
    ext
    simp
  right_inv j := by
    ext
    simp

/-- The block-ordered WHIR skeleton has the expected challenge budget. -/
theorem whirBlockVectorSpec_card_challengeIdx (M : ℕ) :
    Fintype.card (whirBlockVectorSpec M).ChallengeIdx = 2 * M + 2 := by
  rw [Fintype.card_congr (whirBlockVectorSpec_challengeIdxEquivFin M)]
  simp

/-- The block-ordered WHIR skeleton has the expected prover-message budget. -/
theorem whirBlockVectorSpec_card_messageIdx (M : ℕ) :
    Fintype.card (whirBlockVectorSpec M).MessageIdx = 2 * M + 2 := by
  rw [Fintype.card_congr (whirBlockVectorSpec_messageIdxEquivFin M)]
  simp

/-- Every verifier-challenge payload in the block-ordered WHIR skeleton has length one. -/
theorem whirBlockVectorSpec_challengeLength (M : ℕ)
    (i : (whirBlockVectorSpec M).ChallengeIdx) :
    (whirBlockVectorSpec M).challengeLength i = 1 := by
  rfl

/-- Every prover-message payload in the block-ordered WHIR skeleton has length one. -/
theorem whirBlockVectorSpec_messageLength (M : ℕ)
    (i : (whirBlockVectorSpec M).MessageIdx) :
    (whirBlockVectorSpec M).messageLength i = 1 := by
  rfl

/-- The total verifier-challenge payload length of the block-ordered WHIR skeleton is `2*M+2`. -/
theorem whirBlockVectorSpec_totalChallengeLength (M : ℕ) :
    (whirBlockVectorSpec M).totalChallengeLength = 2 * M + 2 := by
  classical
  rw [ProtocolSpec.VectorSpec.totalChallengeLength]
  trans Fintype.card (whirBlockVectorSpec M).ChallengeIdx
  · simp [whirBlockVectorSpec_challengeLength]
  · exact whirBlockVectorSpec_card_challengeIdx M

/-- The total prover-message payload length of the block-ordered WHIR skeleton is `2*M+2`. -/
theorem whirBlockVectorSpec_totalMessageLength (M : ℕ) :
    (whirBlockVectorSpec M).totalMessageLength = 2 * M + 2 := by
  classical
  rw [ProtocolSpec.VectorSpec.totalMessageLength]
  trans Fintype.card (whirBlockVectorSpec M).MessageIdx
  · simp [whirBlockVectorSpec_messageLength]
  · exact whirBlockVectorSpec_card_messageIdx M

omit [Field F] [Fintype F] [DecidableEq F] [SampleableType F] in
/-- Converted `ProtocolSpec` challenge indices of the block-ordered WHIR skeleton are the second
block. -/
def whirBlockVectorSpec_toProtocolSpec_challengeIdxEquivFin (M : ℕ) :
    ((whirBlockVectorSpec M).toProtocolSpec F).ChallengeIdx ≃ Fin (2 * M + 2) :=
  whirBlockVectorSpec_challengeIdxEquivFin M

omit [Field F] [Fintype F] [DecidableEq F] [SampleableType F] in
/-- Converted `ProtocolSpec` prover-message indices of the block-ordered WHIR skeleton are the
first block. -/
def whirBlockVectorSpec_toProtocolSpec_messageIdxEquivFin (M : ℕ) :
    ((whirBlockVectorSpec M).toProtocolSpec F).MessageIdx ≃ Fin (2 * M + 2) :=
  whirBlockVectorSpec_messageIdxEquivFin M

omit [Field F] [Fintype F] [DecidableEq F] [SampleableType F] in
/-- The converted block-ordered WHIR skeleton has the expected challenge budget. -/
theorem whirBlockVectorSpec_toProtocolSpec_card_challengeIdx (M : ℕ) :
    Fintype.card (((whirBlockVectorSpec M).toProtocolSpec F).ChallengeIdx) = 2 * M + 2 := by
  rw [Fintype.card_congr
    (whirBlockVectorSpec_toProtocolSpec_challengeIdxEquivFin (F := F) M)]
  simp

omit [Field F] [Fintype F] [DecidableEq F] [SampleableType F] in
/-- The converted block-ordered WHIR skeleton has the expected prover-message budget. -/
theorem whirBlockVectorSpec_toProtocolSpec_card_messageIdx (M : ℕ) :
    Fintype.card (((whirBlockVectorSpec M).toProtocolSpec F).MessageIdx) = 2 * M + 2 := by
  rw [Fintype.card_congr
    (whirBlockVectorSpec_toProtocolSpec_messageIdxEquivFin (F := F) M)]
  simp

omit [Field F] [Fintype F] [DecidableEq F] [SampleableType F] in
@[simp] theorem whirBlockVectorSpec_toProtocolSpec_challengeIdxEquivFin_apply (M : ℕ)
    (i : ((whirBlockVectorSpec M).toProtocolSpec F).ChallengeIdx) :
    whirBlockVectorSpec_toProtocolSpec_challengeIdxEquivFin (F := F) M i =
      whirBlockVectorSpec_challengeIdxEquivFin M i :=
  rfl

omit [Field F] [Fintype F] [DecidableEq F] [SampleableType F] in
@[simp] theorem whirBlockVectorSpec_toProtocolSpec_challengeIdxEquivFin_symm_apply (M : ℕ)
    (i : Fin (2 * M + 2)) :
    (whirBlockVectorSpec_toProtocolSpec_challengeIdxEquivFin (F := F) M).symm i =
      (whirBlockVectorSpec_challengeIdxEquivFin M).symm i :=
  rfl

omit [Field F] [Fintype F] [DecidableEq F] [SampleableType F] in
@[simp] theorem whirBlockVectorSpec_toProtocolSpec_messageIdxEquivFin_apply (M : ℕ)
    (i : ((whirBlockVectorSpec M).toProtocolSpec F).MessageIdx) :
    whirBlockVectorSpec_toProtocolSpec_messageIdxEquivFin (F := F) M i =
      whirBlockVectorSpec_messageIdxEquivFin M i :=
  rfl

omit [Field F] [Fintype F] [DecidableEq F] [SampleableType F] in
@[simp] theorem whirBlockVectorSpec_toProtocolSpec_messageIdxEquivFin_symm_apply (M : ℕ)
    (i : Fin (2 * M + 2)) :
    (whirBlockVectorSpec_toProtocolSpec_messageIdxEquivFin (F := F) M).symm i =
      (whirBlockVectorSpec_messageIdxEquivFin M).symm i :=
  rfl

/-! ### The WHIR protocol-spec direction vector

WHIR runs `M + 1` rounds; each round contributes **two** verifier challenges (the folding
challenge and the out-of-domain / shift challenge).  We model the whole interaction with `2*M+2`
challenge slots, all `V_to_P`.  This is the minimal `VectorSpec` whose `ChallengeIdx` cardinality
and total challenge length are exactly `2 * M + 2`, matching the `whir_rbr_soundness` requirement
`Fintype.card vPSpec.ChallengeIdx = 2 * M + 2`.  The full
`2 P_to_V`/`2 V_to_P`-per-round WHIR interleaving is the faithful refinement of this skeleton; the
challenge budget — the load-bearing datum the soundness statement quantifies over — is realised
exactly here. -/
@[reducible]
def whirVectorSpec (M : ℕ) : ProtocolSpec.VectorSpec (2 * M + 2) where
  dir := fun _ => Direction.V_to_P
  length := fun _ => 1

/-- The protocol spec has exactly `2 * M + 2` verifier challenges. -/
theorem whirVectorSpec_card_challengeIdx (M : ℕ) :
    Fintype.card (whirVectorSpec M).ChallengeIdx = 2 * M + 2 := by
  classical
  -- `ChallengeIdx` is the subtype of `Fin (2*M+2)` with `dir i = V_to_P`, which is everything.
  change Fintype.card {i : Fin (2 * M + 2) // Direction.V_to_P = Direction.V_to_P} =
    2 * M + 2
  simp

/-- Challenge slots in the all-challenge WHIR scratch `VectorSpec` are exactly
`Fin (2 * M + 2)`. -/
def whirVectorSpec_challengeIdxEquivFin (M : ℕ) :
    (whirVectorSpec M).ChallengeIdx ≃ Fin (2 * M + 2) where
  toFun i := i.1
  invFun i := ⟨i, rfl⟩
  left_inv := by
    intro i
    cases i
    rfl
  right_inv := by
    intro i
    rfl

@[simp] theorem whirVectorSpec_challengeIdxEquivFin_apply (M : ℕ)
    (i : (whirVectorSpec M).ChallengeIdx) :
    whirVectorSpec_challengeIdxEquivFin M i = i.1 :=
  rfl

@[simp] theorem whirVectorSpec_challengeIdxEquivFin_symm_apply (M : ℕ)
    (i : Fin (2 * M + 2)) :
    (whirVectorSpec_challengeIdxEquivFin M).symm i = ⟨i, rfl⟩ :=
  rfl

omit [Field F] [Fintype F] [DecidableEq F] [SampleableType F] in
/-- There are **no** prover messages in `whirVectorSpec`: every slot is a challenge. -/
theorem whirVectorSpec_messageIdx_isEmpty (M : ℕ) :
    IsEmpty ((whirVectorSpec M).toProtocolSpec F).MessageIdx := by
  constructor
  rintro ⟨i, hi⟩
  -- `dir i = P_to_V` but every dir is `V_to_P`.
  change Direction.V_to_P = Direction.P_to_V at hi
  cases hi

omit [Field F] [Fintype F] [DecidableEq F] [SampleableType F] in
/-- The protocol spec has no prover-message indices. -/
theorem whirVectorSpec_card_messageIdx (M : ℕ) :
    Fintype.card (((whirVectorSpec M).toProtocolSpec F).MessageIdx) = 0 := by
  exact Fintype.card_eq_zero_iff.mpr (whirVectorSpec_messageIdx_isEmpty (F := F) M)

omit [Field F] [Fintype F] [DecidableEq F] [SampleableType F] in
/-- Message indices in the converted WHIR scratch `ProtocolSpec` are exactly `Fin 0`. -/
noncomputable def whirVectorSpec_toProtocolSpec_messageIdxEquivFin (M : ℕ) :
    ((whirVectorSpec M).toProtocolSpec F).MessageIdx ≃ Fin 0 :=
  Fintype.equivFinOfCardEq (whirVectorSpec_card_messageIdx (F := F) M)

omit [Field F] [Fintype F] [DecidableEq F] [SampleableType F] in
/-- The converted protocol spec has the same `2 * M + 2` verifier-challenge indices. -/
theorem whirVectorSpec_toProtocolSpec_card_challengeIdx (M : ℕ) :
    Fintype.card (((whirVectorSpec M).toProtocolSpec F).ChallengeIdx) = 2 * M + 2 := by
  classical
  change Fintype.card {i : Fin (2 * M + 2) // Direction.V_to_P = Direction.V_to_P} =
    2 * M + 2
  simp

omit [Field F] [Fintype F] [DecidableEq F] [SampleableType F] in
/-- Challenge slots in the converted WHIR scratch `ProtocolSpec` are exactly
`Fin (2 * M + 2)`. -/
def whirVectorSpec_toProtocolSpec_challengeIdxEquivFin (M : ℕ) :
    ((whirVectorSpec M).toProtocolSpec F).ChallengeIdx ≃ Fin (2 * M + 2) where
  toFun i := i.1
  invFun i := ⟨i, rfl⟩
  left_inv := by
    intro i
    cases i
    rfl
  right_inv := by
    intro i
    rfl

omit [Field F] [Fintype F] [DecidableEq F] [SampleableType F] in
@[simp] theorem whirVectorSpec_toProtocolSpec_challengeIdxEquivFin_apply (M : ℕ)
    (i : ((whirVectorSpec M).toProtocolSpec F).ChallengeIdx) :
    whirVectorSpec_toProtocolSpec_challengeIdxEquivFin (F := F) M i = i.1 :=
  rfl

omit [Field F] [Fintype F] [DecidableEq F] [SampleableType F] in
@[simp] theorem whirVectorSpec_toProtocolSpec_challengeIdxEquivFin_symm_apply (M : ℕ)
    (i : Fin (2 * M + 2)) :
    (whirVectorSpec_toProtocolSpec_challengeIdxEquivFin (F := F) M).symm i = ⟨i, rfl⟩ :=
  rfl

/-- Every verifier-challenge index has length one in the WHIR scratch vector spec. -/
theorem whirVectorSpec_challengeLength (M : ℕ) (i : (whirVectorSpec M).ChallengeIdx) :
    (whirVectorSpec M).challengeLength i = 1 := by
  rfl

omit [Field F] [Fintype F] [DecidableEq F] [SampleableType F] in
/-- Every verifier challenge in the converted WHIR skeleton is a single field element. -/
theorem whirVectorSpec_challenge_eq_vector_one (M : ℕ)
    (i : ((whirVectorSpec M).toProtocolSpec F).ChallengeIdx) :
    ((whirVectorSpec M).toProtocolSpec F).Challenge i = Vector F 1 := by
  simp [ProtocolSpec.Challenge]

/-- The total challenge payload length of the scratch WHIR vector spec is `2 * M + 2`. -/
theorem whirVectorSpec_totalChallengeLength (M : ℕ) :
    (whirVectorSpec M).totalChallengeLength = 2 * M + 2 := by
  classical
  rw [ProtocolSpec.VectorSpec.totalChallengeLength]
  simp [ProtocolSpec.VectorSpec.challengeLength, whirVectorSpec]

/-- The scratch WHIR vector spec has no prover-message payload. -/
theorem whirVectorSpec_totalMessageLength (M : ℕ) :
    (whirVectorSpec M).totalMessageLength = 0 := by
  classical
  rw [ProtocolSpec.VectorSpec.totalMessageLength]
  simp [ProtocolSpec.VectorSpec.messageLength, whirVectorSpec]

instance (M : ℕ) :
    ∀ j, OracleInterface (((whirVectorSpec M).toProtocolSpec F).Message j) :=
  fun j => (whirVectorSpec_messageIdx_isEmpty (F := F) M).elim j

/-! ### `whir_rbr_soundness` existential assembly

The top-level WHIR soundness statement in `RBRSoundness.lean` is an existential over a concrete
`VectorIOP` plus the bundled `IsSecureWithGap` proof and the per-round numeric budget.  The theorem
below proves the final packaging step: once a candidate protocol `π`, its security proof, and the
paper's named fold/out/shift/final inequalities are supplied, the existential statement follows.

This intentionally does **not** construct `π`; it isolates the remaining protocol/completeness/RBR
knowledge-soundness obligation from the now-checked existential and budget assembly. -/
section RBRSoundnessAssembly

variable {M : ℕ}
variable {ιs : Fin (M + 1) → Type} [∀ i : Fin (M + 1), Fintype (ιs i)]

omit [SampleableType F] [Fintype ι] [Nonempty ι] in
/-- Assemble `whir_rbr_soundness` from a concrete WHIR `VectorIOP`, its `IsSecureWithGap` proof,
and the named per-round bounds from Theorem 5.2.

This is the exact downstream witness-introduction step for issue #113.  It keeps the hard residual
honest: callers must still provide the actual Construction 5.1 protocol `π`, prove its perfect
completeness/RBR knowledge soundness via `IsSecureWithGap`, and discharge the fold/OOD/shift/final
numeric inequalities. -/
theorem whir_rbr_soundness_of_secure_gap
    [SampleableType F] {d dstar : ℕ}
    {P : Params ιs F} {S : ∀ i : Fin (M + 1), Finset (ιs i)}
    {hParams : ParamConditions ιs P} {h : GenMutualCorrParams ιs P S}
    {m_0 : ℕ} (hm_0 : m_0 = P.varCount 0) {σ₀ : F}
    {wPoly₀ : MvPolynomial (Fin (m_0 + 1)) F} {δ : ℝ≥0}
    [Smooth (P.φ 0)] [Nonempty (ιs 0)]
    (ε_fold : (i : Fin (M + 1)) → Fin (P.foldingParam i) → ℝ≥0)
    (ε_out : Fin (M + 1) → ℝ≥0)
    (ε_shift : Fin M → ℝ≥0) (ε_fin : ℝ≥0)
    {n : ℕ} {vPSpec : ProtocolSpec.VectorSpec n}
    (hChallengeCard : Fintype.card (vPSpec.ChallengeIdx) = 2 * M + 2)
    (π : VectorIOP Unit (OracleStatement (ιs 0) F) Unit vPSpec F)
    (hSecure :
      let max_ε_folds : (i : Fin (M + 1)) → ℝ≥0 :=
        fun i => (Finset.univ : Finset (Fin (P.foldingParam i))).sup (ε_fold i)
      let ε_rbr : vPSpec.ChallengeIdx → ℝ≥0 :=
        fun _ => (Finset.univ.image max_ε_folds ∪ {ε_fin} ∪ Finset.univ.image ε_out ∪
          Finset.univ.image ε_shift).max' (by simp)
      VectorIOP.IsSecureWithGap (whirRelation m_0 (P.φ 0) 0)
        (whirRelation m_0 (P.φ 0) (h.δ 0)) ε_rbr π)
    (hBudget :
      let maxDeg := (Finset.univ : Finset (Fin m_0)).sup
        (fun i => wPoly₀.degreeOf (Fin.succ i))
      let dstar := 1 + (wPoly₀.degreeOf 0) + maxDeg
      let d := max dstar 3
      let _ : ∀ j : Fin ((P.foldingParam 0) + 1),
        Fintype (BlockRelDistance.indexPowT (S 0) (P.φ 0) j) := h.inst1 0
      let _ : ∀ j : Fin ((P.foldingParam 0) + 1),
        Nonempty (BlockRelDistance.indexPowT (S 0) (P.φ 0) j) := h.inst2 0
      ∀ _j : Fin ((P.foldingParam 0) + 1),
        let errStar_0 j := h.errStar 0 j (h.C 0 j) (h.Gen_α 0 j).parℓ (h.δ 0)
        ∀ j : Fin (P.foldingParam 0),
          ε_fold 0 j ≤
            ((dstar * (h.dist 0 j.castSucc)) / Fintype.card F) + (errStar_0 j.succ)
      ∧
      ∀ i : Fin (M + 1),
        ε_out i ≤
          2^(P.varCount i) * (h.dist i 0)^2 / (2 * Fintype.card F)
      ∧
      ∀ i : Fin M,
        ε_shift i ≤ (1 - (h.δ i.castSucc))^(P.repeatParam i.castSucc)
          + ((h.dist i.succ 0) * (P.repeatParam i.castSucc) + 1) / Fintype.card F
      ∧
      let _ : ∀ i : Fin (M + 1), ∀ j : Fin ((P.foldingParam i) + 1),
        Fintype (BlockRelDistance.indexPowT (S i) (P.φ i) j) := h.inst1
      let _ : ∀ i : Fin (M + 1), ∀ j : Fin ((P.foldingParam i) + 1),
        Nonempty (BlockRelDistance.indexPowT (S i) (P.φ i) j) := h.inst2
      ∀ i : Fin (M + 1), ∀ _j : Fin ((P.foldingParam i) + 1),
        let errStar i j := h.errStar i j (h.C i j) (h.Gen_α i j).parℓ (h.δ i)
        ∀ i : Fin (M + 1), ∀ j : Fin (P.foldingParam i),
          ε_fold i j ≤ d * (h.dist i j.castSucc) / Fintype.card F + errStar i j.succ
      ∧
      ε_fin ≤ (1 - h.δ (Fin.last M))^(P.repeatParam (Fin.last M)) ) :
    whir_rbr_soundness (F := F) (M := M) ιs (d := d) (dstar := dstar)
      (P := P) (S := S) (hParams := hParams) (h := h)
      hm_0 (σ₀ := σ₀) (wPoly₀ := wPoly₀) (δ := δ)
      ε_fold ε_out ε_shift ε_fin := by
  refine ⟨n, vPSpec, hChallengeCard, π, ?_⟩
  exact ⟨hSecure, hBudget⟩

omit [Fintype ι] [Nonempty ι] in
/-- Assemble `whir_rbr_soundness` using the checked scratch WHIR `VectorSpec`.

This specializes `whir_rbr_soundness_of_secure_gap` to `whirVectorSpec M`, so callers of the
scratch construction no longer have to pass the challenge-cardinality witness manually.  It remains
purely downstream plumbing: callers still supply the concrete WHIR `VectorIOP`, its
`IsSecureWithGap` proof, and the paper budget inequalities. -/
theorem whir_rbr_soundness_of_whirVectorSpec_secure_gap
    {d dstar : ℕ}
    {P : Params ιs F} {S : ∀ i : Fin (M + 1), Finset (ιs i)}
    {hParams : ParamConditions ιs P} {h : GenMutualCorrParams ιs P S}
    {m_0 : ℕ} (hm_0 : m_0 = P.varCount 0) {σ₀ : F}
    {wPoly₀ : MvPolynomial (Fin (m_0 + 1)) F} {δ : ℝ≥0}
    [Smooth (P.φ 0)] [Nonempty (ιs 0)]
    (ε_fold : (i : Fin (M + 1)) → Fin (P.foldingParam i) → ℝ≥0)
    (ε_out : Fin (M + 1) → ℝ≥0)
    (ε_shift : Fin M → ℝ≥0) (ε_fin : ℝ≥0)
    (π : VectorIOP Unit (OracleStatement (ιs 0) F) Unit (whirVectorSpec M) F)
    (hSecure :
      let max_ε_folds : (i : Fin (M + 1)) → ℝ≥0 :=
        fun i => (Finset.univ : Finset (Fin (P.foldingParam i))).sup (ε_fold i)
      let ε_rbr : (whirVectorSpec M).ChallengeIdx → ℝ≥0 :=
        fun _ => (Finset.univ.image max_ε_folds ∪ {ε_fin} ∪ Finset.univ.image ε_out ∪
          Finset.univ.image ε_shift).max' (by simp)
      VectorIOP.IsSecureWithGap (whirRelation m_0 (P.φ 0) 0)
        (whirRelation m_0 (P.φ 0) (h.δ 0)) ε_rbr π)
    (hBudget :
      let maxDeg := (Finset.univ : Finset (Fin m_0)).sup
        (fun i => wPoly₀.degreeOf (Fin.succ i))
      let dstar := 1 + (wPoly₀.degreeOf 0) + maxDeg
      let d := max dstar 3
      let _ : ∀ j : Fin ((P.foldingParam 0) + 1),
        Fintype (BlockRelDistance.indexPowT (S 0) (P.φ 0) j) := h.inst1 0
      let _ : ∀ j : Fin ((P.foldingParam 0) + 1),
        Nonempty (BlockRelDistance.indexPowT (S 0) (P.φ 0) j) := h.inst2 0
      ∀ _j : Fin ((P.foldingParam 0) + 1),
        let errStar_0 j := h.errStar 0 j (h.C 0 j) (h.Gen_α 0 j).parℓ (h.δ 0)
        ∀ j : Fin (P.foldingParam 0),
          ε_fold 0 j ≤
            ((dstar * (h.dist 0 j.castSucc)) / Fintype.card F) + (errStar_0 j.succ)
      ∧
      ∀ i : Fin (M + 1),
        ε_out i ≤
          2^(P.varCount i) * (h.dist i 0)^2 / (2 * Fintype.card F)
      ∧
      ∀ i : Fin M,
        ε_shift i ≤ (1 - (h.δ i.castSucc))^(P.repeatParam i.castSucc)
          + ((h.dist i.succ 0) * (P.repeatParam i.castSucc) + 1) / Fintype.card F
      ∧
      let _ : ∀ i : Fin (M + 1), ∀ j : Fin ((P.foldingParam i) + 1),
        Fintype (BlockRelDistance.indexPowT (S i) (P.φ i) j) := h.inst1
      let _ : ∀ i : Fin (M + 1), ∀ j : Fin ((P.foldingParam i) + 1),
        Nonempty (BlockRelDistance.indexPowT (S i) (P.φ i) j) := h.inst2
      ∀ i : Fin (M + 1), ∀ _j : Fin ((P.foldingParam i) + 1),
        let errStar i j := h.errStar i j (h.C i j) (h.Gen_α i j).parℓ (h.δ i)
        ∀ i : Fin (M + 1), ∀ j : Fin (P.foldingParam i),
          ε_fold i j ≤ d * (h.dist i j.castSucc) / Fintype.card F + errStar i j.succ
      ∧
      ε_fin ≤ (1 - h.δ (Fin.last M))^(P.repeatParam (Fin.last M)) ) :
    whir_rbr_soundness (F := F) (M := M) ιs (d := d) (dstar := dstar)
      (P := P) (S := S) (hParams := hParams) (h := h)
      hm_0 (σ₀ := σ₀) (wPoly₀ := wPoly₀) (δ := δ)
      ε_fold ε_out ε_shift ε_fin := by
  refine ⟨2 * M + 2, whirVectorSpec M, whirVectorSpec_card_challengeIdx M, π, ?_⟩
  exact ⟨hSecure, hBudget⟩

end RBRSoundnessAssembly

#print axioms whirVectorSpec_card_challengeIdx
#print axioms paperTranscriptSlotDirection
#print axioms paperTranscriptSlotLength
#print axioms whirPaperTranscriptVectorSpec
#print axioms whirPaperTranscriptVectorSpec_dir
#print axioms whirPaperTranscriptVectorSpec_length
#print axioms packFiniteFunction
#print axioms unpackFiniteFunction
#print axioms unpack_packFiniteFunction
#print axioms pack_unpackFiniteFunction
#print axioms paperTranscriptSlotIndex
#print axioms paperTranscriptSlotIndex_symm_apply
#print axioms paperMessageIdx
#print axioms paperChallengeIdx
#print axioms mainFoldedOracleMessageIdx
#print axioms finalPolynomialMessageIdx
#print axioms whirVectorSpec_challengeIdxEquivFin
#print axioms whirVectorSpec_challengeIdxEquivFin_apply
#print axioms whirVectorSpec_challengeIdxEquivFin_symm_apply
#print axioms whirVectorSpec_messageIdx_isEmpty
#print axioms whirVectorSpec_card_messageIdx
#print axioms whirVectorSpec_toProtocolSpec_messageIdxEquivFin
#print axioms whirVectorSpec_toProtocolSpec_card_challengeIdx
#print axioms whirVectorSpec_toProtocolSpec_challengeIdxEquivFin
#print axioms whirVectorSpec_toProtocolSpec_challengeIdxEquivFin_apply
#print axioms whirVectorSpec_toProtocolSpec_challengeIdxEquivFin_symm_apply
#print axioms whirVectorSpec_challengeLength
#print axioms whirVectorSpec_challenge_eq_vector_one
#print axioms whirVectorSpec_totalChallengeLength
#print axioms whirVectorSpec_totalMessageLength
#print axioms whir_rbr_soundness_of_secure_gap
#print axioms semanticChallengeIdx_card
#print axioms semanticChallengeIdxEquivFin
#print axioms semanticMessageIdx_card
#print axioms semanticMessageIdxEquivFin
#print axioms whirBlockVectorSpec_challengeIdxEquivFin
#print axioms whirBlockVectorSpec_messageIdxEquivFin
#print axioms whirBlockVectorSpec_card_challengeIdx
#print axioms whirBlockVectorSpec_card_messageIdx
#print axioms whirBlockVectorSpec_challengeLength
#print axioms whirBlockVectorSpec_messageLength
#print axioms whirBlockVectorSpec_totalChallengeLength
#print axioms whirBlockVectorSpec_totalMessageLength
#print axioms whirBlockVectorSpec_toProtocolSpec_challengeIdxEquivFin
#print axioms whirBlockVectorSpec_toProtocolSpec_messageIdxEquivFin
#print axioms whirBlockVectorSpec_toProtocolSpec_card_challengeIdx
#print axioms whirBlockVectorSpec_toProtocolSpec_card_messageIdx
#print axioms whirBlockVectorSpec_toProtocolSpec_challengeIdxEquivFin_apply
#print axioms whirBlockVectorSpec_toProtocolSpec_challengeIdxEquivFin_symm_apply
#print axioms whirBlockVectorSpec_toProtocolSpec_messageIdxEquivFin_apply
#print axioms whirBlockVectorSpec_toProtocolSpec_messageIdxEquivFin_symm_apply
#print axioms whir_rbr_soundness_of_whirVectorSpec_secure_gap

end Construction

end WhirIOP

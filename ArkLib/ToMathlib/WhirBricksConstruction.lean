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

open OracleSpec OracleComp ProtocolSpec NNReal

namespace WhirIOP

namespace Construction

variable {F : Type} [Field F] [Fintype F] [DecidableEq F] [SampleableType F]
variable {ι : Type} [Fintype ι] [DecidableEq ι] [Nonempty ι]

/-- The single-index oracle statement family for the WHIR Vector IOPP: the prover holds one
  oracle function `f : ι → F` (the purported low-degree evaluation being proximity-tested). -/
@[reducible]
def OStmt (ι F : Type) : Unit → Type := fun _ => ι → F

instance : OracleInterface (OStmt ι F ()) := OracleInterface.instFunction

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
/-- The converted protocol spec has the same `2 * M + 2` verifier-challenge indices. -/
theorem whirVectorSpec_toProtocolSpec_card_challengeIdx (M : ℕ) :
    Fintype.card (((whirVectorSpec M).toProtocolSpec F).ChallengeIdx) = 2 * M + 2 := by
  classical
  change Fintype.card {i : Fin (2 * M + 2) // Direction.V_to_P = Direction.V_to_P} =
    2 * M + 2
  simp

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

#print axioms whirVectorSpec_card_challengeIdx
#print axioms whirVectorSpec_messageIdx_isEmpty
#print axioms whirVectorSpec_card_messageIdx
#print axioms whirVectorSpec_toProtocolSpec_card_challengeIdx
#print axioms whirVectorSpec_challengeLength
#print axioms whirVectorSpec_challenge_eq_vector_one
#print axioms whirVectorSpec_totalChallengeLength
#print axioms whirVectorSpec_totalMessageLength

end Construction

end WhirIOP

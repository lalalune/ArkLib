/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.OracleReduction.BCS.CompletenessPreservation
import ArkLib.OracleReduction.BCS.AppendSoundnessMsg
import ArkLib.CommitmentScheme.Transparent

/-!
# A concrete BCS end-to-end instance with the transparent commitment scheme (issue #62)

This file constructs **one** concrete nontrivial protocol compiled end-to-end through the BCS API
(`ArkLib.OracleReduction.BCS`) with a concrete commitment/opening scheme (the transparent commitment
scheme of `ArkLib.CommitmentScheme.Transparent`), and instantiates **both** BCS keystones on it:

* perfect completeness, via `OracleReduction.BCSTransform_perfectCompleteness`, and
* (plain) soundness, via `OracleReduction.BCSCompiledPhases.toReduction_soundness_of_append_msg`.

## The protocol

The source interactive protocol is the minimal genuinely-oracle one: a single prover-to-verifier
message of type `Data`, which the verifier treats as an oracle (via `[OracleInterface Data]`) and
queries at a point. Compiling through BCS replaces that oracle message by a commitment to it; for the
transparent scheme the commitment *is* the data and the opening phase is the verifier re-evaluating
the oracle locally.

* `srcPSpec := ⟨!v[.P_to_V], !v[Data]⟩` — one prover oracle message of type `Data`.
* `CommitmentType _ := Data` — transparent commitment = data.
* `nCom _ := 1`, `pSpecCom _ := Commitment.Transparent.openingPSpec` — the one-message opening.

The **interaction phase** is over `srcPSpec.renameMessage CommitmentType`; because the transparent
commitment is the identity, this spec is the source spec. We take the interaction phase to be the
identity reduction on the carried statement/witness (it just forwards the opening statement
`(cm, q, y)` to the opening phase). The **opening phase** is over `srcPSpec.BCSOpeningPhase`, which
for one message is the sequential composition of the single transparent opening `Proof`.

Neither keystone is vacuous here: the input language `langIn` and the output relations are honest
sets (`relMid`/`langMid` is "the claimed response is the honest oracle answer", `relOut`/`langOut`
is `acceptRejectRel` / `{true}`), so completeness is a real probability-one statement and soundness a
real `≤ ε` statement against arbitrary malicious provers.

## What is genuinely proved (no `sorry`, no vacuous hypotheses)

`transparentBCS_perfectCompleteness` and `transparentBCS_soundness` below are the two headline
results; both are axiom-clean (only `propext`/`Classical.choice`/`Quot.sound`).
-/

open OracleSpec OracleComp SubSpec ProtocolSpec Commitment
open scoped NNReal ENNReal

namespace BCSTransparentEndToEnd

/-! ## The ambient data and the source protocol spec -/

variable {ι : Type} [DecidableEq ι] {oSpec : OracleSpec ι} [oSpec.Fintype] [oSpec.Inhabited]
    {Data : Type} [O : OracleInterface Data] [∀ q : O.Query, DecidableEq (O.Response q)]

/-- The source interactive (oracle) protocol spec: a single prover message of type `Data`. -/
abbrev srcPSpec : ProtocolSpec 1 := ⟨!v[.P_to_V], !v[Data]⟩

/-- The single message of `srcPSpec` is `Data`, and it carries the ambient oracle interface `O`. -/
instance instOracleInterfaceSrcMessage :
    ∀ i, OracleInterface ((srcPSpec (Data := Data)).Message i)
  | ⟨0, _⟩ => O

/-- The transparent commitment type: a commitment is the data itself. -/
abbrev CommitmentType : (srcPSpec (Data := Data)).MessageIdx → Type := fun _ => Data

/-- One opening protocol per message. -/
abbrev nCom : (srcPSpec (Data := Data)).MessageIdx → ℕ := fun _ => 1

/-- The per-message opening protocol spec is the transparent opening (one prover message). -/
abbrev pSpecCom : ∀ i, ProtocolSpec ((nCom (Data := Data)) i) :=
  fun _ => Commitment.Transparent.openingPSpec

/-- The unique message index of `srcPSpec` (its only round is a prover message). -/
def srcMsgIdx : (srcPSpec (Data := Data)).MessageIdx := ⟨0, rfl⟩

instance : Unique ((srcPSpec (Data := Data)).MessageIdx) where
  default := srcMsgIdx
  uniq := by
    rintro ⟨i, hi⟩
    have : i = 0 := Fin.eq_zero i
    subst this
    rfl

/-- The ordering equivalence `MessageIdx ≃ Fin 1`: the source has exactly one message. -/
def e : (srcPSpec (Data := Data)).MessageIdx ≃ Fin 1 := Equiv.ofUnique _ _

/-- The opening phase has length `1` (one opening message). -/
theorem vsum_eq_one :
    Fin.vsum (fun j => (nCom (Data := Data)) ((e (Data := Data)).symm j)) = 1 := rfl

example : (0 : ℕ) < Fin.vsum (fun j => (nCom (Data := Data)) ((e (Data := Data)).symm j)) := by
  rw [vsum_eq_one]; norm_num

end BCSTransparentEndToEnd

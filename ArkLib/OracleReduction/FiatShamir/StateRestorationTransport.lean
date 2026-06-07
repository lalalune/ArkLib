/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/

import ArkLib.OracleReduction.FiatShamir.Basic

/-!
# Basic Fiat-Shamir State-Restoration Pre-Transport Wrappers (#116)

`FiatShamir/Basic.lean` exposes wrappers that apply a discharged state-restoration transfer
residual and then weaken the Fiat-Shamir conclusion.  This companion file provides the dual
consumer shape: first transport the state-restoration hypothesis with
`Verifier.StateRestoration.*.mono_*`, then apply a transfer residual that is already stated at the
target parameters.

These declarations are API plumbing over the existing residual surfaces. They do not discharge the
semantic state-restoration-to-Fiat-Shamir transfer residuals.
-/

noncomputable section

open ProtocolSpec OracleComp OracleSpec
open scoped NNReal

section TranscriptAliases

namespace ProtocolSpec

/-- The slow Fiat-Shamir challenge oracle is definitionally the state-restoration challenge
oracle. This is the structural coupling used by the #116 soundness-transfer reduction. -/
theorem fsChallengeOracle_eq_srChallengeOracle {Statement : Type} {n : ℕ}
    {pSpec : ProtocolSpec n} :
    fsChallengeOracle Statement pSpec = srChallengeOracle Statement pSpec := by
  rfl

/-- The cached slow Fiat-Shamir challenge query implementation is definitionally the cached
state-restoration challenge query implementation. -/
theorem fsChallengeQueryImpl'_eq_srChallengeQueryImpl' {Statement : Type} {n : ℕ}
    {pSpec : ProtocolSpec n} [∀ i, SampleableType (pSpec.Challenge i)] :
    fsChallengeQueryImpl' (Statement := Statement) (pSpec := pSpec) =
      srChallengeQueryImpl' (Statement := Statement) (pSpec := pSpec) := by
  rfl

namespace MessagesUpTo

/-- Partial transcript derivation for slow Fiat-Shamir is definitionally the state-restoration
transcript derivation. -/
theorem deriveTranscriptFS_eq_deriveTranscriptSR {n : ℕ} {pSpec : ProtocolSpec n}
    {ι : Type} {oSpec : OracleSpec ι} {StmtIn : Type}
    (stmt : StmtIn) (k : Fin (n + 1)) (messages : pSpec.MessagesUpTo k) :
    deriveTranscriptFS (oSpec := oSpec) stmt k messages =
      deriveTranscriptSR (oSpec := oSpec) stmt k messages := by
  rfl

end MessagesUpTo

namespace Messages

/-- Full transcript derivation for slow Fiat-Shamir is definitionally the state-restoration
transcript derivation. -/
theorem deriveTranscriptFS_eq_deriveTranscriptSR {n : ℕ} {pSpec : ProtocolSpec n}
    {ι : Type} {oSpec : OracleSpec ι} {StmtIn : Type}
    (stmt : StmtIn) (messages : pSpec.Messages) :
    deriveTranscriptFS (oSpec := oSpec) stmt messages =
      deriveTranscriptSR (oSpec := oSpec) stmt messages := by
  rfl

end Messages

end ProtocolSpec

namespace Verifier

/-- The basic Fiat-Shamir verifier can be expanded using the state-restoration transcript
derivation, since `deriveTranscriptFS` and `deriveTranscriptSR` are aliases. -/
theorem fiatShamir_verify_eq_deriveTranscriptSR {n : ℕ} {pSpec : ProtocolSpec n}
    {ι : Type} {oSpec : OracleSpec ι} {StmtIn StmtOut : Type}
    (V : Verifier oSpec StmtIn StmtOut pSpec) (stmtIn : StmtIn)
    (proof : FullTranscript ⟨!v[Direction.P_to_V], !v[pSpec.Messages]⟩) :
    (V.fiatShamir).verify stmtIn proof =
      (do
        let messages : pSpec.Messages := proof 0
        let transcript ← messages.deriveTranscriptSR (oSpec := oSpec) stmtIn
        let v ← (V.verify stmtIn transcript).run
        v.getM) := by
  rfl

namespace StateRestoration

/-- The state-restoration soundness game can be read through the slow Fiat-Shamir transcript
derivation, since both derivations query the same challenge oracle. -/
theorem srSoundnessGame_eq_deriveTranscriptFS {n : ℕ} {pSpec : ProtocolSpec n}
    {ι : Type} {oSpec : OracleSpec ι} {StmtIn : Type}
    (P : Prover.StateRestoration.Soundness oSpec StmtIn pSpec) :
    srSoundnessGame P =
      (do
        let ⟨stmtIn, messages⟩ ← P
        let transcript ← messages.deriveTranscriptFS (oSpec := oSpec) stmtIn
        return ⟨transcript, stmtIn⟩) := by
  rfl

/-- The state-restoration knowledge-soundness game can likewise be read through the slow
Fiat-Shamir transcript derivation. -/
theorem srKnowledgeSoundnessGame_eq_deriveTranscriptFS {n : ℕ} {pSpec : ProtocolSpec n}
    {ι : Type} {oSpec : OracleSpec ι} {StmtIn WitOut : Type}
    (P : Prover.StateRestoration.KnowledgeSoundness oSpec StmtIn WitOut pSpec) :
    srKnowledgeSoundnessGame P =
      (do
        let ⟨stmtIn, messages, witOut⟩ ← P
        let transcript ← messages.deriveTranscriptFS (oSpec := oSpec) stmtIn
        return ⟨transcript, stmtIn, witOut⟩) := by
  rfl

end StateRestoration

end Verifier

#print axioms ProtocolSpec.fsChallengeOracle_eq_srChallengeOracle
#print axioms ProtocolSpec.fsChallengeQueryImpl'_eq_srChallengeQueryImpl'
#print axioms ProtocolSpec.MessagesUpTo.deriveTranscriptFS_eq_deriveTranscriptSR
#print axioms ProtocolSpec.Messages.deriveTranscriptFS_eq_deriveTranscriptSR
#print axioms Verifier.fiatShamir_verify_eq_deriveTranscriptSR
#print axioms Verifier.StateRestoration.srSoundnessGame_eq_deriveTranscriptFS
#print axioms Verifier.StateRestoration.srKnowledgeSoundnessGame_eq_deriveTranscriptFS

end TranscriptAliases

namespace Reduction

variable {n : ℕ}
variable {pSpec : ProtocolSpec n} {ι : Type} {oSpec : OracleSpec ι}
  {StmtIn WitIn StmtOut WitOut : Type}
  [VCVCompatible StmtIn] [∀ i, VCVCompatible (pSpec.Challenge i)]
  [∀ i, SampleableType (pSpec.Challenge i)]
  {σ : Type}

attribute [local instance 10000] Reduction.fiatShamirNoChallengeSampleable

/-- Basic Fiat-Shamir soundness from a transfer residual at the target error, after first relaxing
the state-restoration soundness hypothesis to that target error. -/
theorem fiatShamir_soundness_of_stateRestoration_pre_mono_error
    (srInit : ProbComp (QueryImpl (fsChallengeOracle StmtIn pSpec) Id))
    (srImpl : QueryImpl oSpec
      (StateT (QueryImpl (fsChallengeOracle StmtIn pSpec) Id) ProbComp))
    (fsInit : ProbComp σ)
    (fsImpl : QueryImpl (oSpec + fsChallengeOracle StmtIn pSpec) (StateT σ ProbComp))
    (langIn : Set StmtIn) (langOut : Set StmtOut)
    {soundnessError₁ soundnessError₂ : ℝ≥0}
    (V : Verifier oSpec StmtIn StmtOut pSpec)
    (hTransfer :
      fiatShamir_soundnessTransferResidual srInit srImpl fsInit fsImpl
        langIn langOut soundnessError₂ V)
    (hSR : Verifier.StateRestoration.soundness srInit srImpl
      langIn langOut V soundnessError₁)
    (hle : soundnessError₁ ≤ soundnessError₂) :
    Verifier.soundness fsInit fsImpl langIn langOut V.fiatShamir soundnessError₂ := by
  classical
  exact fiatShamir_soundness_of_stateRestoration srInit srImpl fsInit fsImpl langIn langOut
    soundnessError₂ V hTransfer
    (Verifier.StateRestoration.soundness.mono_error srInit srImpl hSR
      (ENNReal.coe_le_coe.mpr hle))

/-- Basic Fiat-Shamir soundness from a transfer residual at the target languages, after first
transporting the state-restoration soundness hypothesis to those languages. -/
theorem fiatShamir_soundness_of_stateRestoration_pre_mono_languages
    (srInit : ProbComp (QueryImpl (fsChallengeOracle StmtIn pSpec) Id))
    (srImpl : QueryImpl oSpec
      (StateT (QueryImpl (fsChallengeOracle StmtIn pSpec) Id) ProbComp))
    (fsInit : ProbComp σ)
    (fsImpl : QueryImpl (oSpec + fsChallengeOracle StmtIn pSpec) (StateT σ ProbComp))
    {langIn langIn' : Set StmtIn} {langOut langOut' : Set StmtOut}
    (soundnessError : ℝ≥0)
    (V : Verifier oSpec StmtIn StmtOut pSpec)
    (hTransfer :
      fiatShamir_soundnessTransferResidual srInit srImpl fsInit fsImpl
        langIn' langOut' soundnessError V)
    (hSR : Verifier.StateRestoration.soundness srInit srImpl
      langIn langOut V soundnessError)
    (hIn : langIn ⊆ langIn') (hOut : langOut' ⊆ langOut) :
    Verifier.soundness fsInit fsImpl langIn' langOut' V.fiatShamir soundnessError := by
  classical
  exact fiatShamir_soundness_of_stateRestoration srInit srImpl fsInit fsImpl langIn' langOut'
    soundnessError V hTransfer
    (Verifier.StateRestoration.soundness.mono_languages srInit srImpl hSR hIn hOut)

/-- Basic Fiat-Shamir soundness from a transfer residual at the target languages/error, after first
transporting the state-restoration soundness hypothesis to those target parameters. -/
theorem fiatShamir_soundness_of_stateRestoration_pre_mono_languages_error
    (srInit : ProbComp (QueryImpl (fsChallengeOracle StmtIn pSpec) Id))
    (srImpl : QueryImpl oSpec
      (StateT (QueryImpl (fsChallengeOracle StmtIn pSpec) Id) ProbComp))
    (fsInit : ProbComp σ)
    (fsImpl : QueryImpl (oSpec + fsChallengeOracle StmtIn pSpec) (StateT σ ProbComp))
    {langIn langIn' : Set StmtIn} {langOut langOut' : Set StmtOut}
    {soundnessError₁ soundnessError₂ : ℝ≥0}
    (V : Verifier oSpec StmtIn StmtOut pSpec)
    (hTransfer :
      fiatShamir_soundnessTransferResidual srInit srImpl fsInit fsImpl
        langIn' langOut' soundnessError₂ V)
    (hSR : Verifier.StateRestoration.soundness srInit srImpl
      langIn langOut V soundnessError₁)
    (hIn : langIn ⊆ langIn') (hOut : langOut' ⊆ langOut)
    (hle : soundnessError₁ ≤ soundnessError₂) :
    Verifier.soundness fsInit fsImpl langIn' langOut' V.fiatShamir soundnessError₂ := by
  classical
  exact fiatShamir_soundness_of_stateRestoration srInit srImpl fsInit fsImpl langIn' langOut'
    soundnessError₂ V hTransfer
    (Verifier.StateRestoration.soundness.mono_languages_error srInit srImpl hSR hIn hOut
      (ENNReal.coe_le_coe.mpr hle))

/-- Basic Fiat-Shamir knowledge soundness from a transfer residual at the target error, after first
relaxing the state-restoration knowledge-soundness hypothesis to that target error. -/
theorem fiatShamir_knowledgeSoundness_of_stateRestoration_pre_mono_error
    (srInit : ProbComp (QueryImpl (fsChallengeOracle StmtIn pSpec) Id))
    (srImpl : QueryImpl oSpec
      (StateT (QueryImpl (fsChallengeOracle StmtIn pSpec) Id) ProbComp))
    (fsInit : ProbComp σ)
    (fsImpl : QueryImpl (oSpec + fsChallengeOracle StmtIn pSpec) (StateT σ ProbComp))
    (relIn : Set (StmtIn × WitIn)) (relOut : Set (StmtOut × WitOut))
    {knowledgeError₁ knowledgeError₂ : ℝ≥0}
    (V : Verifier oSpec StmtIn StmtOut pSpec)
    (hTransfer :
      fiatShamir_knowledgeSoundnessTransferResidual srInit srImpl fsInit fsImpl
        relIn relOut knowledgeError₂ V)
    (hSR : Verifier.StateRestoration.knowledgeSoundness srInit srImpl
      relIn relOut V knowledgeError₁)
    (hle : knowledgeError₁ ≤ knowledgeError₂) :
    Verifier.knowledgeSoundness fsInit fsImpl relIn relOut V.fiatShamir knowledgeError₂ := by
  classical
  exact fiatShamir_knowledgeSoundness_of_stateRestoration srInit srImpl fsInit fsImpl relIn relOut
    knowledgeError₂ V hTransfer
    (Verifier.StateRestoration.knowledgeSoundness.mono_error srInit srImpl hSR
      (ENNReal.coe_le_coe.mpr hle))

/-- Basic Fiat-Shamir knowledge soundness from a transfer residual at the target relations, after
first transporting the state-restoration knowledge-soundness hypothesis to those relations. -/
theorem fiatShamir_knowledgeSoundness_of_stateRestoration_pre_mono_relations
    (srInit : ProbComp (QueryImpl (fsChallengeOracle StmtIn pSpec) Id))
    (srImpl : QueryImpl oSpec
      (StateT (QueryImpl (fsChallengeOracle StmtIn pSpec) Id) ProbComp))
    (fsInit : ProbComp σ)
    (fsImpl : QueryImpl (oSpec + fsChallengeOracle StmtIn pSpec) (StateT σ ProbComp))
    {relIn relIn' : Set (StmtIn × WitIn)} {relOut relOut' : Set (StmtOut × WitOut)}
    (knowledgeError : ℝ≥0)
    (V : Verifier oSpec StmtIn StmtOut pSpec)
    (hTransfer :
      fiatShamir_knowledgeSoundnessTransferResidual srInit srImpl fsInit fsImpl
        relIn' relOut' knowledgeError V)
    (hSR : Verifier.StateRestoration.knowledgeSoundness srInit srImpl
      relIn relOut V knowledgeError)
    (hIn : relIn ⊆ relIn') (hOut : relOut' ⊆ relOut) :
    Verifier.knowledgeSoundness fsInit fsImpl relIn' relOut' V.fiatShamir knowledgeError := by
  classical
  exact fiatShamir_knowledgeSoundness_of_stateRestoration srInit srImpl fsInit fsImpl relIn' relOut'
    knowledgeError V hTransfer
    (Verifier.StateRestoration.knowledgeSoundness.mono_relations srInit srImpl hSR hIn hOut)

/-- Basic Fiat-Shamir knowledge soundness from a transfer residual at the target relations/error,
after first transporting the state-restoration knowledge-soundness hypothesis to those target
parameters. -/
theorem fiatShamir_knowledgeSoundness_of_stateRestoration_pre_mono_relations_error
    (srInit : ProbComp (QueryImpl (fsChallengeOracle StmtIn pSpec) Id))
    (srImpl : QueryImpl oSpec
      (StateT (QueryImpl (fsChallengeOracle StmtIn pSpec) Id) ProbComp))
    (fsInit : ProbComp σ)
    (fsImpl : QueryImpl (oSpec + fsChallengeOracle StmtIn pSpec) (StateT σ ProbComp))
    {relIn relIn' : Set (StmtIn × WitIn)} {relOut relOut' : Set (StmtOut × WitOut)}
    {knowledgeError₁ knowledgeError₂ : ℝ≥0}
    (V : Verifier oSpec StmtIn StmtOut pSpec)
    (hTransfer :
      fiatShamir_knowledgeSoundnessTransferResidual srInit srImpl fsInit fsImpl
        relIn' relOut' knowledgeError₂ V)
    (hSR : Verifier.StateRestoration.knowledgeSoundness srInit srImpl
      relIn relOut V knowledgeError₁)
    (hIn : relIn ⊆ relIn') (hOut : relOut' ⊆ relOut)
    (hle : knowledgeError₁ ≤ knowledgeError₂) :
    Verifier.knowledgeSoundness fsInit fsImpl relIn' relOut' V.fiatShamir
      knowledgeError₂ := by
  classical
  exact fiatShamir_knowledgeSoundness_of_stateRestoration srInit srImpl fsInit fsImpl relIn' relOut'
    knowledgeError₂ V hTransfer
    (Verifier.StateRestoration.knowledgeSoundness.mono_relations_error srInit srImpl hSR hIn hOut
      (ENNReal.coe_le_coe.mpr hle))

/-- Basic Fiat-Shamir soundness with both SR-side pretransport and FS-side posttransport around the
explicit state-restoration transfer residual. -/
theorem fiatShamir_soundness_of_stateRestoration_prepost_mono_languages_error
    (srInit : ProbComp (QueryImpl (fsChallengeOracle StmtIn pSpec) Id))
    (srImpl : QueryImpl oSpec
      (StateT (QueryImpl (fsChallengeOracle StmtIn pSpec) Id) ProbComp))
    (fsInit : ProbComp σ)
    (fsImpl : QueryImpl (oSpec + fsChallengeOracle StmtIn pSpec) (StateT σ ProbComp))
    {langInSR langInTransfer langInFS : Set StmtIn}
    {langOutSR langOutTransfer langOutFS : Set StmtOut}
    {soundnessErrorSR soundnessErrorTransfer soundnessErrorFS : ℝ≥0}
    (V : Verifier oSpec StmtIn StmtOut pSpec)
    (hTransfer :
      fiatShamir_soundnessTransferResidual srInit srImpl fsInit fsImpl
        langInTransfer langOutTransfer soundnessErrorTransfer V)
    (hSR : Verifier.StateRestoration.soundness srInit srImpl
      langInSR langOutSR V soundnessErrorSR)
    (hInPre : langInSR ⊆ langInTransfer)
    (hOutPre : langOutTransfer ⊆ langOutSR)
    (hlePre : soundnessErrorSR ≤ soundnessErrorTransfer)
    (hInPost : langInTransfer ⊆ langInFS)
    (hOutPost : langOutFS ⊆ langOutTransfer)
    (hlePost : soundnessErrorTransfer ≤ soundnessErrorFS) :
    Verifier.soundness fsInit fsImpl langInFS langOutFS V.fiatShamir
      soundnessErrorFS := by
  classical
  have hMid :
      Verifier.soundness fsInit fsImpl langInTransfer langOutTransfer V.fiatShamir
        soundnessErrorTransfer :=
    fiatShamir_soundness_of_stateRestoration_pre_mono_languages_error
      srInit srImpl fsInit fsImpl V hTransfer hSR hInPre hOutPre hlePre
  have hLang :
      Verifier.soundness fsInit fsImpl langInFS langOutFS V.fiatShamir
        soundnessErrorTransfer :=
    Verifier.soundness.mono_languages fsInit fsImpl hMid hInPost hOutPost
  exact Verifier.soundness.mono_error fsInit fsImpl hLang hlePost

/-- Basic Fiat-Shamir knowledge soundness with both SR-side pretransport and FS-side posttransport
around the explicit state-restoration transfer residual. -/
theorem fiatShamir_knowledgeSoundness_of_stateRestoration_prepost_mono_relations_error
    (srInit : ProbComp (QueryImpl (fsChallengeOracle StmtIn pSpec) Id))
    (srImpl : QueryImpl oSpec
      (StateT (QueryImpl (fsChallengeOracle StmtIn pSpec) Id) ProbComp))
    (fsInit : ProbComp σ)
    (fsImpl : QueryImpl (oSpec + fsChallengeOracle StmtIn pSpec) (StateT σ ProbComp))
    {relInSR relInTransfer relInFS : Set (StmtIn × WitIn)}
    {relOutSR relOutTransfer relOutFS : Set (StmtOut × WitOut)}
    {knowledgeErrorSR knowledgeErrorTransfer knowledgeErrorFS : ℝ≥0}
    (V : Verifier oSpec StmtIn StmtOut pSpec)
    (hTransfer :
      fiatShamir_knowledgeSoundnessTransferResidual srInit srImpl fsInit fsImpl
        relInTransfer relOutTransfer knowledgeErrorTransfer V)
    (hSR : Verifier.StateRestoration.knowledgeSoundness srInit srImpl
      relInSR relOutSR V knowledgeErrorSR)
    (hInPre : relInSR ⊆ relInTransfer)
    (hOutPre : relOutTransfer ⊆ relOutSR)
    (hlePre : knowledgeErrorSR ≤ knowledgeErrorTransfer)
    (hInPost : relInTransfer ⊆ relInFS)
    (hOutPost : relOutFS ⊆ relOutTransfer)
    (hlePost : knowledgeErrorTransfer ≤ knowledgeErrorFS) :
    Verifier.knowledgeSoundness fsInit fsImpl relInFS relOutFS V.fiatShamir
      knowledgeErrorFS := by
  classical
  have hMid :
      Verifier.knowledgeSoundness fsInit fsImpl relInTransfer relOutTransfer V.fiatShamir
        knowledgeErrorTransfer :=
    fiatShamir_knowledgeSoundness_of_stateRestoration_pre_mono_relations_error
      srInit srImpl fsInit fsImpl V hTransfer hSR hInPre hOutPre hlePre
  have hRel :
      Verifier.knowledgeSoundness fsInit fsImpl relInFS relOutFS V.fiatShamir
        knowledgeErrorTransfer :=
    Verifier.knowledgeSoundness.mono_relations fsInit fsImpl hMid hInPost hOutPost
  exact Verifier.knowledgeSoundness.mono_error fsInit fsImpl hRel hlePost

#print axioms fiatShamir_soundness_of_stateRestoration_pre_mono_error
#print axioms fiatShamir_soundness_of_stateRestoration_pre_mono_languages
#print axioms fiatShamir_soundness_of_stateRestoration_pre_mono_languages_error
#print axioms fiatShamir_knowledgeSoundness_of_stateRestoration_pre_mono_error
#print axioms fiatShamir_knowledgeSoundness_of_stateRestoration_pre_mono_relations
#print axioms fiatShamir_knowledgeSoundness_of_stateRestoration_pre_mono_relations_error
#print axioms fiatShamir_soundness_of_stateRestoration_prepost_mono_languages_error
#print axioms fiatShamir_knowledgeSoundness_of_stateRestoration_prepost_mono_relations_error

end Reduction

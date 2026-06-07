/-
Copyright (c) 2024-2025 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

import ArkLib.OracleReduction.Security.StateRestoration
import ArkLib.OracleReduction.Security.ZeroKnowledge

/-!
  # The Basic Fiat-Shamir Transformation

  This file defines the basic Fiat-Shamir transformation. This transformation takes in a
  (public-coin) interactive reduction (IR) `R` and transforms it into a non-interactive reduction in
  the following way:
  - Each verifier's challenge, instead of being sent from the verifier, will be obtained from a
    Fiat-Shamir oracle, which for the `i`-th challenge requires the input statement and all messages
    up to round `i`

  This is the _basic_ (or slow) version to be distinguished from the more efficient version based on
  duplex sponge (see `DuplexSponge` folder).

  We will show that the transformation satisfies security properties as follows:

  - Completeness is preserved
  - State-restoration (knowledge) soundness implies (knowledge) soundness
  - Honest-verifier zero-knowledge implies zero-knowledge

  ## Notes

  Our formalization mostly follows the treatment in the Chiesa-Yogev textbook.
-/

universe u v

section find_home

variable {n : ℕ} {σ τ : Type u} {m : Type u → Type v} [Monad m]

/-- Traverse a dependent function indexed by `Fin n` in any monad. -/
def Fin.traverseM {β : Fin n → Type u}
    (f : (i : Fin n) → m (β i)) : m ((i : Fin n) → β i) :=
  let rec aux (k : ℕ) (h : k ≤ n) : m ((i : Fin k) → β (Fin.castLE h i)) :=
    match k with
    | 0 => pure (fun i => i.elim0)
    | k' + 1 => do
      let tail ← aux k' (Nat.le_of_succ_le h)
      let head ← f (Fin.castLE h (Fin.last k'))
      return (Fin.snoc tail head)
  aux n (le_refl n)

instance : MonadLift (StateT σ m) (StateT (σ × τ) m) where
  monadLift := fun x st => do let y ← x st.1; return (y.1, y.2, st.2)

instance : MonadLift (StateT τ m) (StateT (σ × τ) m) where
  monadLift := fun x st => do let y ← x st.2; return (y.1, st.1, y.2)

end find_home

open ProtocolSpec OracleComp OracleSpec

open scoped BigOperators

variable {n : ℕ}

variable {pSpec : ProtocolSpec n} {ι : Type} {oSpec : OracleSpec ι}
  {StmtIn WitIn StmtOut WitOut : Type}
  [VCVCompatible StmtIn] [∀ i, VCVCompatible (pSpec.Challenge i)]

-- In order to define the Fiat-Shamir transformation for the prover, we need to define
-- a slightly altered execution for the prover

/--
Prover's function for processing the next round, given the current result of the previous round.

  This is modified for Fiat-Shamir, where we only accumulate the messages and not the challenges.
-/
@[inline, specialize]
def Prover.processRoundFS [∀ i, VCVCompatible (pSpec.Challenge i)] (j : Fin n)
    (prover : Prover oSpec StmtIn WitIn StmtOut WitOut pSpec)
    (currentResult : OracleComp (oSpec + fsChallengeOracle StmtIn pSpec)
      (pSpec.MessagesUpTo j.castSucc × StmtIn × prover.PrvState j.castSucc)) :
      OracleComp (oSpec + fsChallengeOracle StmtIn pSpec)
        (pSpec.MessagesUpTo j.succ × StmtIn × prover.PrvState j.succ) := do
  let ⟨messages, stmtIn, state⟩ ← currentResult
  match hDir : pSpec.dir j with
  | .V_to_P => do
    let f ← prover.receiveChallenge ⟨j, hDir⟩ state
    let challenge ← query (spec := fsChallengeOracle StmtIn pSpec) ⟨⟨j, hDir⟩, ⟨stmtIn, messages⟩⟩
    return ⟨messages.extend hDir, stmtIn, f challenge⟩
  | .P_to_V => do
    let ⟨msg, newState⟩ ← prover.sendMessage ⟨j, hDir⟩ state
    return ⟨messages.concat hDir msg, stmtIn, newState⟩

/--
Run the prover in an interactive reduction up to round index `i`, via first inputting the
  statement and witness, and then processing each round up to round `i`. Returns the transcript up
  to round `i`, and the prover's state after round `i`.
-/
@[inline, specialize]
def Prover.runToRoundFS [∀ i, VCVCompatible (pSpec.Challenge i)] (i : Fin (n + 1))
    (stmt : StmtIn) (prover : Prover oSpec StmtIn WitIn StmtOut WitOut pSpec)
    (state : prover.PrvState 0) :
        OracleComp (oSpec + fsChallengeOracle StmtIn pSpec)
          (pSpec.MessagesUpTo i × StmtIn × prover.PrvState i) :=
  Fin.induction
    (pure ⟨default, stmt, state⟩)
    prover.processRoundFS
    i

/-- The (slow) Fiat-Shamir transformation for the prover. -/
def Prover.fiatShamir (P : Prover oSpec StmtIn WitIn StmtOut WitOut pSpec) :
    NonInteractiveProver (∀ i, pSpec.Message i) (oSpec + fsChallengeOracle StmtIn pSpec)
      StmtIn WitIn StmtOut WitOut where
  PrvState := fun i => match i with
    | 0 => StmtIn × P.PrvState 0
    | _ => P.PrvState (Fin.last n)
  input := fun ctx => ⟨ctx.1, P.input ctx⟩
  -- Compute the messages to send via the modified `runToRoundFS`
  sendMessage | ⟨0, _⟩ => fun ⟨stmtIn, state⟩ => do
    let ⟨messages, _, state⟩ ← P.runToRoundFS (Fin.last n) stmtIn state
    return ⟨messages, state⟩
  -- This function is never invoked so we apply the elimination principle
  receiveChallenge | ⟨0, h⟩ => nomatch h
  output := fun st => (P.output st).liftComp _

/-- The (slow) Fiat-Shamir transformation for the verifier. -/
def Verifier.fiatShamir (V : Verifier oSpec StmtIn StmtOut pSpec) :
    NonInteractiveVerifier (∀ i, pSpec.Message i) (oSpec + fsChallengeOracle StmtIn pSpec)
      StmtIn StmtOut where
  verify := fun stmtIn proof => do
    let messages : pSpec.Messages := proof 0
    let transcript ← (messages.deriveTranscriptFS (oSpec := oSpec) stmtIn)
    Option.getM (← (V.verify stmtIn transcript).run)

/-- The Fiat-Shamir transformation for an (interactive) reduction, which consists of applying the
  Fiat-Shamir transformation to both the prover and the verifier. -/
def Reduction.fiatShamir (R : Reduction oSpec StmtIn WitIn StmtOut WitOut pSpec) :
    NonInteractiveReduction (∀ i, pSpec.Message i) (oSpec + fsChallengeOracle StmtIn pSpec)
      StmtIn WitIn StmtOut WitOut where
  prover := R.prover.fiatShamir
  verifier := R.verifier.fiatShamir

section Execution

-- Show that the Fiat-Shamir prover's run gives the same output as the original prover's run

namespace Verifier

omit [VCVCompatible StmtIn] [∀ i, VCVCompatible (pSpec.Challenge i)] in
/-- Expanding the basic Fiat-Shamir verifier shows that it re-derives the transcript from the proof
messages via the Fiat-Shamir oracle and then runs the original verifier. -/
@[simp]
theorem fiatShamir_verify_eq
    (V : Verifier oSpec StmtIn StmtOut pSpec) (stmtIn : StmtIn)
    (proof : FullTranscript ⟨!v[Direction.P_to_V], !v[pSpec.Messages]⟩) :
    (V.fiatShamir).verify stmtIn proof =
      (do
        let messages : pSpec.Messages := proof 0
        let transcript ← messages.deriveTranscriptFS (oSpec := oSpec) stmtIn
        let v ← (V.verify stmtIn transcript).run
        v.getM) := by
  rfl

end Verifier



end Execution

section Security

noncomputable section

open scoped NNReal

variable [∀ i, SampleableType (pSpec.Challenge i)]
  {σ : Type}

namespace Reduction

section Completeness

local instance fiatShamirProverOnly : ProtocolSpec.ProverOnly
    ⟨!v[Direction.P_to_V], !v[pSpec.Messages]⟩ where
  prover_first' := by simp

abbrev FiatShamirProtocolSpec : ProtocolSpec 1 :=
  ⟨!v[Direction.P_to_V], !v[pSpec.Messages]⟩

local instance fiatShamirChallengeOracleInterface :
    ∀ i : (FiatShamirProtocolSpec (pSpec := pSpec)).ChallengeIdx,
      OracleInterface ((FiatShamirProtocolSpec (pSpec := pSpec)).Challenge i) :=
  challengeOracleInterface (pSpec := FiatShamirProtocolSpec (pSpec := pSpec))

/-- The one-message proof transcript produced by the basic Fiat-Shamir transform. -/
abbrev FiatShamirProofTranscript :=
  FullTranscript (FiatShamirProtocolSpec (pSpec := pSpec))

/-- The explicit honest execution underlying the basic Fiat-Shamir transform. -/
def fiatShamirHonestExecution
    (R : Reduction oSpec StmtIn WitIn StmtOut WitOut pSpec)
    (stmtIn : StmtIn) (witIn : WitIn) :
    OptionT (OracleComp (oSpec + fsChallengeOracle StmtIn pSpec))
      ((FiatShamirProofTranscript (pSpec := pSpec) × StmtOut × WitOut) × StmtOut) := do
  let state := R.prover.input (stmtIn, witIn)
  let ⟨messages, _, state⟩ ← liftM <|
    R.prover.runToRoundFS (Fin.last n) stmtIn state
  let ctxOut ← liftM <|
    (R.prover.output state).liftComp (oSpec + fsChallengeOracle StmtIn pSpec)
  let proof : FiatShamirProofTranscript (pSpec := pSpec) := fun
    | ⟨0, _⟩ => messages
  let stmtOut ← (R.verifier.fiatShamir).run stmtIn proof
  return ⟨⟨proof, ctxOut⟩, stmtOut⟩

/-- The transformed basic Fiat-Shamir run is the lifted explicit honest execution. -/
def fiatShamir_run_eq_honestExecution
    (R : Reduction oSpec StmtIn WitIn StmtOut WitOut pSpec)
    (stmtIn : StmtIn) (witIn : WitIn) :
    Prop :=
    R.fiatShamir.run stmtIn witIn =
      liftM (R.fiatShamirHonestExecution stmtIn witIn)

/-- Residual for collapsing the outer basic-Fiat-Shamir challenge implementation after unrolling
the transformed run. The right-hand honest execution already queries the Fiat-Shamir challenge
oracle directly; the remaining content is the same `OptionT` lift-coherence wall as the DSFS
completeness bridge, specialized to the unsalted basic transform. -/
def fiatShamir_runCollapseResidual
    {σ : Type}
    (impl : QueryImpl (oSpec + fsChallengeOracle StmtIn pSpec) (StateT σ ProbComp))
    (R : Reduction oSpec StmtIn WitIn StmtOut WitOut pSpec)
    (stmtIn : StmtIn) (witIn : WitIn) :
    Prop :=
    simulateQ (QueryImpl.addLift impl challengeQueryImpl)
        (R.fiatShamir.run stmtIn witIn).run =
      simulateQ impl
        (R.fiatShamirHonestExecution stmtIn witIn).run

/-- Completeness of the transformed one-message reduction is equivalent to the explicit honest
Fiat-Shamir execution packaged via `Reduction.fiatShamirHonestExecution`. -/
def fiatShamir_completeness_unroll
    (init : ProbComp σ)
    (impl : QueryImpl (oSpec + fsChallengeOracle StmtIn pSpec) (StateT σ ProbComp))
    (relIn : Set (StmtIn × WitIn))
    (relOut : Set (StmtOut × WitOut))
    (completenessError : ℝ≥0)
    (R : Reduction oSpec StmtIn WitIn StmtOut WitOut pSpec) :
    Prop :=
    R.fiatShamir.completeness init impl relIn relOut completenessError ↔
      Reduction.completenessFromRun init impl relIn relOut
        (R.fiatShamirHonestExecution) completenessError

/-- **Reduction of `fiatShamir_completeness_unroll` to the run-collapse residual.**

Given the per-input `fiatShamir_runCollapseResidual`, completeness of the transformed one-message
basic Fiat-Shamir reduction is definitionally the generic `completenessFromRun` predicate over
`fiatShamirHonestExecution`. -/
theorem fiatShamir_completeness_unroll_of_runCollapse
    (init : ProbComp σ)
    (impl : QueryImpl (oSpec + fsChallengeOracle StmtIn pSpec) (StateT σ ProbComp))
    (relIn : Set (StmtIn × WitIn))
    (relOut : Set (StmtOut × WitOut))
    (completenessError : ℝ≥0)
    (R : Reduction oSpec StmtIn WitIn StmtOut WitOut pSpec)
    (hCollapse : ∀ stmtIn witIn,
      fiatShamir_runCollapseResidual impl R stmtIn witIn) :
    fiatShamir_completeness_unroll init impl relIn relOut completenessError R := by
  unfold fiatShamir_completeness_unroll
  rw [Reduction.completeness_iff_completenessFromRun]
  unfold Reduction.completenessFromRun
  refine forall_congr' fun stmtIn => forall_congr' fun witIn => ?_
  refine imp_congr_right fun _ => ?_
  have hcollapse :
      simulateQ (QueryImpl.addLift impl challengeQueryImpl)
          (R.fiatShamir.run stmtIn witIn).run =
        simulateQ impl
          (R.fiatShamirHonestExecution stmtIn witIn).run :=
    hCollapse stmtIn witIn
  rw [hcollapse]

-- Future work: discharge `fiatShamir_runCollapseResidual` itself.
-- `Reduction.run_of_prover_first` is now available, and `simulateQ_add_run_liftM_left` in
-- `Execution.lean` collapses the unused outer challenge oracle on lifted `OptionT` runs. The
-- remaining gap is the final file-local normalization between the elaborated run of
-- `R.fiatShamir` and `liftM (R.fiatShamirHonestExecution ...)`, where Lean still chooses multiple
-- coercion paths for the same lifted computation.

#print axioms Reduction.fiatShamir_runCollapseResidual
#print axioms Reduction.fiatShamir_completeness_unroll_of_runCollapse

end Completeness

section StateRestorationSoundness

variable [DecidableEq StmtIn]
  [∀ i, DecidableEq (pSpec.Message i)] [∀ i, DecidableEq (pSpec.Challenge i)]

local instance fiatShamirNoChallengeSampleable :
    ∀ i : (FiatShamirProtocolSpec (pSpec := pSpec)).ChallengeIdx,
      SampleableType ((FiatShamirProtocolSpec (pSpec := pSpec)).Challenge i) := by
  intro i
  rcases i with ⟨i, hi⟩
  exact False.elim (by
    rcases i with ⟨k, hk⟩
    have hk0 : k = 0 := by omega
    subst k
    simp at hi)

/-- Residual statement for the basic Fiat-Shamir state-restoration soundness transfer.

The state-restoration game samples an `fsChallengeOracle` table as its ambient state; the
Fiat-Shamir target exposes that same challenge table as part of the transformed reduction's oracle
spec. Discharging this residual is the remaining semantic coupling between those two views. -/
def fiatShamir_soundnessTransferResidual
    (srInit : ProbComp (QueryImpl (fsChallengeOracle StmtIn pSpec) Id))
    (srImpl : QueryImpl oSpec
      (StateT (QueryImpl (fsChallengeOracle StmtIn pSpec) Id) ProbComp))
    (fsInit : ProbComp σ)
    (fsImpl : QueryImpl (oSpec + fsChallengeOracle StmtIn pSpec) (StateT σ ProbComp))
    (langIn : Set StmtIn) (langOut : Set StmtOut)
    (soundnessError : ℝ≥0)
    (V : Verifier oSpec StmtIn StmtOut pSpec) : Prop :=
  Verifier.StateRestoration.soundness srInit srImpl langIn langOut V soundnessError →
    Verifier.soundness fsInit fsImpl langIn langOut V.fiatShamir soundnessError

/-- Basic Fiat-Shamir soundness follows immediately from a discharged state-restoration transfer
residual. This theorem isolates the remaining proof obligation without claiming to solve it. -/
theorem fiatShamir_soundness_of_stateRestoration
    (srInit : ProbComp (QueryImpl (fsChallengeOracle StmtIn pSpec) Id))
    (srImpl : QueryImpl oSpec
      (StateT (QueryImpl (fsChallengeOracle StmtIn pSpec) Id) ProbComp))
    (fsInit : ProbComp σ)
    (fsImpl : QueryImpl (oSpec + fsChallengeOracle StmtIn pSpec) (StateT σ ProbComp))
    (langIn : Set StmtIn) (langOut : Set StmtOut)
    (soundnessError : ℝ≥0)
    (V : Verifier oSpec StmtIn StmtOut pSpec)
    (hTransfer :
      fiatShamir_soundnessTransferResidual srInit srImpl fsInit fsImpl
        langIn langOut soundnessError V)
    (hSR : Verifier.StateRestoration.soundness srInit srImpl
      langIn langOut V soundnessError) :
    Verifier.soundness fsInit fsImpl langIn langOut V.fiatShamir soundnessError :=
  hTransfer hSR

/-- Residual statement for the basic Fiat-Shamir state-restoration knowledge-soundness transfer.

As in `fiatShamir_soundnessTransferResidual`, this names only the semantic bridge from an
interactive state-restoration adversary/extractor game to the one-message Fiat-Shamir verifier
game. The extractor construction and query-log correspondence remain the open content. -/
def fiatShamir_knowledgeSoundnessTransferResidual
    (srInit : ProbComp (QueryImpl (fsChallengeOracle StmtIn pSpec) Id))
    (srImpl : QueryImpl oSpec
      (StateT (QueryImpl (fsChallengeOracle StmtIn pSpec) Id) ProbComp))
    (fsInit : ProbComp σ)
    (fsImpl : QueryImpl (oSpec + fsChallengeOracle StmtIn pSpec) (StateT σ ProbComp))
    (relIn : Set (StmtIn × WitIn)) (relOut : Set (StmtOut × WitOut))
    (knowledgeError : ℝ≥0)
    (V : Verifier oSpec StmtIn StmtOut pSpec) : Prop :=
  Verifier.StateRestoration.knowledgeSoundness srInit srImpl relIn relOut V knowledgeError →
    Verifier.knowledgeSoundness fsInit fsImpl relIn relOut V.fiatShamir knowledgeError

/-- Basic Fiat-Shamir knowledge soundness follows immediately from a discharged
state-restoration knowledge-soundness transfer residual. -/
theorem fiatShamir_knowledgeSoundness_of_stateRestoration
    (srInit : ProbComp (QueryImpl (fsChallengeOracle StmtIn pSpec) Id))
    (srImpl : QueryImpl oSpec
      (StateT (QueryImpl (fsChallengeOracle StmtIn pSpec) Id) ProbComp))
    (fsInit : ProbComp σ)
    (fsImpl : QueryImpl (oSpec + fsChallengeOracle StmtIn pSpec) (StateT σ ProbComp))
    (relIn : Set (StmtIn × WitIn)) (relOut : Set (StmtOut × WitOut))
    (knowledgeError : ℝ≥0)
    (V : Verifier oSpec StmtIn StmtOut pSpec)
    (hTransfer :
      fiatShamir_knowledgeSoundnessTransferResidual srInit srImpl fsInit fsImpl
        relIn relOut knowledgeError V)
    (hSR : Verifier.StateRestoration.knowledgeSoundness srInit srImpl
      relIn relOut V knowledgeError) :
    Verifier.knowledgeSoundness fsInit fsImpl relIn relOut V.fiatShamir knowledgeError :=
  hTransfer hSR

#print axioms Reduction.fiatShamir_soundnessTransferResidual
#print axioms Reduction.fiatShamir_soundness_of_stateRestoration
#print axioms Reduction.fiatShamir_knowledgeSoundnessTransferResidual
#print axioms Reduction.fiatShamir_knowledgeSoundness_of_stateRestoration

end StateRestorationSoundness

section ZeroKnowledgeTransfer

/-!
### Basic Fiat-Shamir zero-knowledge transfer

The transformed reduction `R.fiatShamir` is *non-interactive*: its protocol spec
`FiatShamirProtocolSpec` carries a single prover message and no verifier challenges. For a
one-message reduction there is no challenge transcript for a zero-knowledge simulator to
re-randomize beyond the honest transcript distribution, so the relevant zero-knowledge notion here
is exactly honest-verifier zero-knowledge of the transformed reduction.

A full simulator-based zero-knowledge predicate for arbitrary reductions is not yet defined in the
core security layer: `Reduction.Simulator` is declared in `Security/Basic.lean`, but no
`zeroKnowledge` predicate is built on it (see the zero-knowledge-definition issue). Pending that, we
record the transfer at the HVZK level in both its statistical form (`Reduction.isStatHVZK`, with a
free error `ε`) and its perfect form (`Reduction.isHVZK`, exact distributions), naming each
obligation as a residual with its bridge theorem, mirroring the completeness and state-restoration
soundness scaffolding above.
-/

local instance fiatShamirZKNoChallengeSampleable :
    ∀ i : (FiatShamirProtocolSpec (pSpec := pSpec)).ChallengeIdx,
      SampleableType ((FiatShamirProtocolSpec (pSpec := pSpec)).Challenge i) := by
  intro i
  rcases i with ⟨i, hi⟩
  exact False.elim (by
    rcases i with ⟨k, hk⟩
    have hk0 : k = 0 := by omega
    subst k
    simp at hi)

/-- Residual statement for the basic Fiat-Shamir HVZK-to-statistical-HVZK transfer.

The underlying interactive reduction is measured by the transcript-level `Reduction.isHVZK`
predicate. The transformed one-message Fiat-Shamir reduction is measured by `Reduction.isStatHVZK`
over the enlarged oracle specification containing the Fiat-Shamir challenge oracle. Supplying this
residual is exactly the semantic simulator-transfer theorem promised by the basic Fiat-Shamir
interface; this wrapper keeps that construction explicit. -/
def fiatShamir_statisticalHVZKTransferResidual
    {τ : Type}
    (init : ProbComp σ)
    (impl : QueryImpl oSpec (StateT σ ProbComp))
    (fsInit : ProbComp τ)
    (fsImpl : QueryImpl (oSpec + fsChallengeOracle StmtIn pSpec) (StateT τ ProbComp))
    (rel : Set (StmtIn × WitIn)) (ε : ℝ≥0)
    (R : Reduction oSpec StmtIn WitIn StmtOut WitOut pSpec) : Prop :=
  Reduction.isHVZK init impl rel R →
    Reduction.isStatHVZK fsInit fsImpl rel R.fiatShamir ε

/-- Basic Fiat-Shamir statistical HVZK follows immediately from a discharged simulator-transfer
residual. This theorem names the target surface for the future malicious-verifier/Fiat-Shamir
simulator argument without claiming to construct that simulator here. -/
theorem fiatShamir_isStatHVZK_of_HVZK
    {τ : Type}
    (init : ProbComp σ)
    (impl : QueryImpl oSpec (StateT σ ProbComp))
    (fsInit : ProbComp τ)
    (fsImpl : QueryImpl (oSpec + fsChallengeOracle StmtIn pSpec) (StateT τ ProbComp))
    (rel : Set (StmtIn × WitIn)) (ε : ℝ≥0)
    (R : Reduction oSpec StmtIn WitIn StmtOut WitOut pSpec)
    (hTransfer :
      fiatShamir_statisticalHVZKTransferResidual init impl fsInit fsImpl rel ε R)
    (hHVZK : Reduction.isHVZK init impl rel R) :
    Reduction.isStatHVZK fsInit fsImpl rel R.fiatShamir ε :=
  hTransfer hHVZK

/-- Residual statement for the basic Fiat-Shamir *perfect* honest-verifier zero-knowledge transfer.

The exact-distribution counterpart of `fiatShamir_statisticalHVZKTransferResidual` (the `ε = 0`
case): `R.fiatShamir` is the one-message non-interactive reduction, whose only randomness is the
prover message recomputed through the Fiat-Shamir challenge oracle. The open content of this
residual is the construction of a transcript simulator for the transformed reduction out of a
transcript simulator for the interactive source, together with the distribution-equality argument
coupling the Fiat-Shamir honest transcript distribution to the source honest transcript
distribution. -/
def fiatShamir_hvzkTransferResidual
    {τ : Type}
    (init : ProbComp σ) (impl : QueryImpl oSpec (StateT σ ProbComp))
    (fsInit : ProbComp τ)
    (fsImpl : QueryImpl (oSpec + fsChallengeOracle StmtIn pSpec) (StateT τ ProbComp))
    (rel : Set (StmtIn × WitIn))
    (R : Reduction oSpec StmtIn WitIn StmtOut WitOut pSpec) : Prop :=
  Reduction.isHVZK init impl rel R →
    Reduction.isHVZK fsInit fsImpl rel R.fiatShamir

/-- Basic Fiat-Shamir perfect honest-verifier zero-knowledge follows immediately from a discharged
transfer residual. This isolates the remaining proof obligation (simulator construction plus
transcript distribution coupling) without claiming to solve it. -/
theorem fiatShamir_isHVZK_of_transfer
    {τ : Type}
    (init : ProbComp σ) (impl : QueryImpl oSpec (StateT σ ProbComp))
    (fsInit : ProbComp τ)
    (fsImpl : QueryImpl (oSpec + fsChallengeOracle StmtIn pSpec) (StateT τ ProbComp))
    (rel : Set (StmtIn × WitIn))
    (R : Reduction oSpec StmtIn WitIn StmtOut WitOut pSpec)
    (hTransfer : fiatShamir_hvzkTransferResidual init impl fsInit fsImpl rel R)
    (hHVZK : Reduction.isHVZK init impl rel R) :
    Reduction.isHVZK fsInit fsImpl rel R.fiatShamir :=
  hTransfer hHVZK

#print axioms Reduction.fiatShamir_statisticalHVZKTransferResidual
#print axioms Reduction.fiatShamir_isStatHVZK_of_HVZK
#print axioms Reduction.fiatShamir_hvzkTransferResidual
#print axioms Reduction.fiatShamir_isHVZK_of_transfer

end ZeroKnowledgeTransfer

end Reduction

-- Future work: discharge the run-collapse, state-restoration transfer, and HVZK simulator-transfer
-- residuals named above for the basic Fiat-Shamir transform (statistical and perfect forms); the
-- HVZK legs are additionally gated on a core simulator-based zero-knowledge definition.

end

end Security

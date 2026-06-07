/-
Copyright (c) 2024 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

import ArkLib.CommitmentScheme.Basic
import ArkLib.OracleReduction.Composition.Sequential.General

/-!
# The Generalized Ben-Sasson–Chiesa–Spooner (BCS) Compiler

This module formalizes the generalized Ben-Sasson–Chiesa–Spooner (BCS) compilation technique
(TCC 2016) at the protocol specification and reduction levels. The BCS transform compiles an
Interactive Oracle Reduction (IOR) into a standard Interactive Reduction (IR) (or interactive proof
system) by replacing oracle messages with cryptographic commitments.

In the compiled protocol, the prover sends commitments to each oracle message, and the verifier
interacts with the prover to receive challenges. Finally, in the opening phase, the prover shows
that the verifier's oracle queries are consistent with the sent commitments using interactive
opening arguments. This compiles oracle-dependent protocols into concrete protocols, capturing both
the classical Merkle-tree compilation of IOPs and modern polynomial commitment compilers
(e.g., Marlin, Plonk) for polynomial IOPs.

The transformation establishes a composition where:
1. Every oracle message type is replaced with a commitment type (via `renameMessage`).
2. An opening phase consisting of the sequential composition of the per-message commitment-opening
   protocol specifications is appended.

  ## What this file states (ArkLib#2: "initial attempt to state the BCS transform")

  This is a *definitional* first attempt at stating the transform; no security proofs are given.

  * `ProtocolSpec.renameMessage` (pre-existing): replace each prover-message type by a new type
    (here, a commitment type), keeping all directions fixed.
  * `ProtocolSpec.BCSOpeningPhase`: the opening phase as the sequential composition
    (`ProtocolSpec.seqCompose`) of the per-message commitment-opening protocol specs.
  * `ProtocolSpec.BCSTransform`: **fully general** at the protocol-spec level — the renamed
    interaction phase appended (`++ₚ`) to the opening phase.
  * `Reduction.bcsMessageOpening`: the per-message opening reduction extracted from a commitment
    `Commitment.Scheme` (this is exactly its `opening` proof).
  * `OracleReduction.BCSTransform`: the reduction-level transform, stated as `Reduction.append` of an
    interaction phase and an opening phase over `ProtocolSpec.BCSTransform`.

  ## What is deferred

  The reduction-level transform takes its two phases (interaction, opening) as inputs rather than
  constructing them from the input oracle reduction plus the commitment schemes. The honest
  constructions — the prover committing via `Scheme.commit` instead of sending each message, and the
  opening phase reading the oracle verifier's (possibly adaptive) query log to decide which openings
  to run and with which witnesses — are the dependent-type-plumbing-over-query-logs parts, and are
  deferred together with all security-preservation results (completeness, the soundness notions,
  HVZK) to the core oracle-reduction rewrite (ArkLib#433). Restricting to
  `OracleVerifier.NonAdaptive` removes the adaptivity blocker but not the type-threading one; see the
  design note at the end of the file. The fully general transform thus depends on #433.

  ## Notes

  The BCS transform has a lot of degrees of freedom. For instance, we can choose to run the opening
  arguments for each verifier's query in any order; here that choice of order is recorded explicitly
  by the ordering equivalence `e : pSpec.MessageIdx ≃ Fin m` passed to the transform.

  There are also a lot of variants and avenues for optimization:

  - We can ``batch'' many opening arguments together (using homomorphic properties of the commitment
    scheme, or via another round of interaction, or via specialized techniques like Merkle capping).

  ## References

  * [Ben-Sasson, E., Chiesa, A., and Spooner, N., *Interactive Oracle Proofs*, TCC 2016][BCS16] —
    the original BCS transform (vector IOPs + Merkle commitments).
  * [Chiesa, A. and Yogev, E., *Building Cryptographic Proofs from Hash Functions*][ChiesaYogev2024]
    — textbook treatment of the BCS / hash-based-SNARG compilation.
-/

variable {n : ℕ}

namespace ProtocolSpec

/-- Switch the type of prover's messages in a protocol specification. The directions are preserved.
-/
def renameMessage (pSpec : ProtocolSpec n) (NewMessage : pSpec.MessageIdx → Type) :
    ProtocolSpec n :=
  ⟨ pSpec.dir,
    fun i => if h : pSpec.dir i = Direction.P_to_V then NewMessage ⟨i, h⟩ else pSpec.«Type» i⟩

/-! ### The BCS transform on protocol specifications

  The protocol-spec layer of the BCS transform is fully general: it takes the interaction phase of
  the original protocol with every prover message replaced by a commitment to it (via the existing
  `renameMessage`), and appends an opening phase consisting of the sequential composition of the
  per-message commitment-opening protocol specifications.

  The opening phase is the sequential composition (`ProtocolSpec.seqCompose`) of the per-message
  opening specs. Since `seqCompose` composes a `Fin m`-indexed family while the opening specs are
  indexed by `pSpec.MessageIdx`, we take an explicit ordering equivalence
  `e : pSpec.MessageIdx ≃ Fin m` as a parameter. This makes the order of the opening phase
  explicit: as noted in the module docstring, the BCS transform has a genuine degree of freedom in
  the order in which the opening arguments are run, and `e` records that choice. (Taking `e` as a
  parameter rather
  than the canonical `Fintype.equivFin` also keeps the definition computable.) -/

/-- The opening phase of the BCS transform: the sequential composition of the per-message
  commitment-opening protocol specifications, ordered by the equivalence `e : pSpec.MessageIdx ≃
  Fin m`. -/
def BCSOpeningPhase (pSpec : ProtocolSpec n) {m : ℕ}
    {nCom : pSpec.MessageIdx → ℕ} (pSpecCom : ∀ i, ProtocolSpec (nCom i))
    (e : pSpec.MessageIdx ≃ Fin m) :
    ProtocolSpec (Fin.vsum (fun j => nCom (e.symm j))) :=
  ProtocolSpec.seqCompose (fun j => pSpecCom (e.symm j))

/-- The BCS transformation on protocol specifications.

  Given an interaction-phase spec `pSpec`, a type `CommitmentType i` of commitments for each prover
  message `i`, a commitment-opening protocol spec `pSpecCom i` for each prover message, and an
  ordering `e : pSpec.MessageIdx ≃ Fin m` of the messages, the transformed spec is:

  * the interaction phase `pSpec.renameMessage CommitmentType`, in which every prover message is
    replaced by a commitment to it, followed by
  * the opening phase `BCSOpeningPhase`, which runs the per-message opening protocols in sequence.

  This is the faithful statement sketched by composing the renamed interaction phase with the
  per-message opening phase. -/
def BCSTransform (pSpec : ProtocolSpec n) {m : ℕ}
    {nCom : pSpec.MessageIdx → ℕ} (pSpecCom : ∀ i, ProtocolSpec (nCom i))
    (CommitmentType : pSpec.MessageIdx → Type) (e : pSpec.MessageIdx ≃ Fin m) :
    ProtocolSpec (n + Fin.vsum (fun j => nCom (e.symm j))) :=
  (pSpec.renameMessage CommitmentType) ++ₚ (pSpec.BCSOpeningPhase pSpecCom e)

end ProtocolSpec

open Commitment

namespace Reduction

variable {pSpec : ProtocolSpec n} {ι : Type} {oSpec : OracleSpec ι}
    [Oₘ : ∀ i, OracleInterface (pSpec.Message i)]

variable {m : ℕ} {nCom : pSpec.MessageIdx → ℕ} {pSpecCom : ∀ i, ProtocolSpec (nCom i)}
    {Commitment Decommitment ComKey VerifKey : pSpec.MessageIdx → Type}

/-! ### The opening phase of the BCS transform

  The opening phase is fully constructible from the data of the commitment schemes: each scheme's
  `opening` field is a `Proof` (an interactive reduction whose output statement is `Bool`) for the
  evaluation of one committed message. The opening phase runs these one after another via the
  existing `Reduction.seqCompose`, ordered by `e : pSpec.MessageIdx ≃ Fin m`, over the protocol
  spec `ProtocolSpec.BCSOpeningPhase`.

  For a single message `i`, the opening proof proves the relation
  "the response `y` to query `q` against commitment `cm` is correct", with statement type
  `Commitment i × (q : (Oₘ i).Query) × (Oₘ i).Response q` and witness type
  `pSpec.Message i × Decommitment i`. Threading these statement/witness types through the sequential
  composition is what the `Stmt`/`Wit` families below record. -/

/-- The per-message opening reduction obtained from a commitment scheme for message `i`, given the
  committer/verifier keys. This is literally the scheme's `opening` proof, viewed as a `Reduction`
  over the opening protocol spec `pSpecCom i`. -/
def bcsMessageOpening (i : pSpec.MessageIdx)
    (scheme : Scheme oSpec (pSpec.Message i) (Commitment i) (Decommitment i)
      (ComKey i) (VerifKey i) (pSpecCom i))
    (keys : ComKey i × VerifKey i) :
    Reduction oSpec
      (Commitment i × (q : (Oₘ i).Query) × (Oₘ i).Response q)
      (pSpec.Message i × Decommitment i) Bool Unit (pSpecCom i) :=
  scheme.opening keys

end Reduction

namespace OracleReduction

variable {pSpec : ProtocolSpec n} {ι : Type} {oSpec : OracleSpec ι}
    [Oₘ : ∀ i, OracleInterface (pSpec.Message i)]

variable {m : ℕ} {nCom : pSpec.MessageIdx → ℕ} {pSpecCom : ∀ i, ProtocolSpec (nCom i)}
    {Commitment Decommitment ComKey VerifKey : pSpec.MessageIdx → Type}

variable {StmtIn StmtOut WitIn WitOut : Type}
    {ιₛᵢ : Type} {OStmtIn : ιₛᵢ → Type} [Oₛᵢ : ∀ i, OracleInterface (OStmtIn i)]
    {ιₛₒ : Type} {OStmtOut : ιₛₒ → Type}

/-! ### The BCS transform on (oracle) reductions

  **Scope.** We state the reduction-level BCS transform as the sequential composition (via the
  existing `Reduction.append`) of two phases over the transformed spec
  `ProtocolSpec.BCSTransform pSpecCom CommitmentType e`:

  1. an **interaction phase** `interaction`, an interactive (non-oracle) reduction over
     `pSpec.renameMessage CommitmentType` — morally the original oracle reduction with every prover
     message replaced by a commitment to it — and
  2. an **opening phase** `opening`, an interactive reduction over
     `pSpec.BCSOpeningPhase pSpecCom e` — morally the verifier's evaluation queries discharged by
     the per-message opening proofs (see `Reduction.bcsMessageOpening`), composed in the order `e`.

  The honest construction of the **interaction phase** from the input oracle `reduction` and the
  commitment schemes (the prover commits to each message via `scheme.commit` instead of sending it,
  and the verifier checks the renamed transcript) and the honest construction of the **opening
  phase** from the verifier's query log (which queries to discharge, in which order, with which
  witnesses) are precisely the parts that require the dependent-type plumbing over query logs.
  These, together with the proofs that the transform preserves completeness / soundness / knowledge
  soundness / HVZK, are deferred to the core oracle-reduction rewrite (ArkLib#433). We therefore
  take the two phases as inputs and record the resulting type-level statement of the transform;
  this is the "initial attempt to state the BCS transform" called for by ArkLib#2.

  The fully general transform (no separate-phase inputs) is sketched in the design comment below. -/

/-- The BCS transformation on (interactive) reductions, stated as the sequential composition of the
  interaction phase (messages replaced by commitments) and the opening phase (per-message opening
  proofs run in sequence), over the BCS-transformed protocol spec
  `ProtocolSpec.BCSTransform pSpecCom CommitmentType e`.

  Here `StmtMid`/`WitMid` are the intermediate statement/witness handed from the interaction phase
  to the opening phase (it carries, e.g., the commitments, the queried points, and the openings
  needed
  by the opening phase). -/
def BCSTransform {StmtMid WitMid : Type} {CommitmentType : pSpec.MessageIdx → Type}
    (e : pSpec.MessageIdx ≃ Fin m)
    (interaction :
      Reduction oSpec StmtIn WitIn StmtMid WitMid (pSpec.renameMessage CommitmentType))
    (opening :
      Reduction oSpec StmtMid WitMid StmtOut WitOut (pSpec.BCSOpeningPhase pSpecCom e)) :
    Reduction oSpec StmtIn WitIn StmtOut WitOut
      (pSpec.BCSTransform pSpecCom CommitmentType e) :=
  Reduction.append interaction opening

/-! #### Current compiler-frontier interface

The definition above is the already-buildable reduction-level composition once the two phases are
available.  The compiler work that remains is to construct those phases from an input
`OracleReduction` and commitment schemes.  The structures below make that boundary explicit without
turning it into prose-only debt: callers can pass the phases today, while the future compiler must
replace the two realization fields by proofs produced from the oracle verifier/query-log machinery.
-/

/-- The two concrete phases of a BCS-compiled protocol, plus the two realization obligations that
are not yet constructible by the generic compiler.

`interaction_realizes_oracle_messages` should say that the interaction phase faithfully simulates
the source oracle reduction while replacing each oracle message by a commitment.
`opening_realizes_query_log` should say that the opening phase opens exactly the oracle queries made
by the verifier with the retained `(message, decommitment)` witnesses.  Both are left as `Prop`
fields because their
eventual statement depends on the query-log API being stabilized. -/
structure BCSCompiledPhases {StmtMid WitMid : Type}
    (CommitmentType : pSpec.MessageIdx → Type) (e : pSpec.MessageIdx ≃ Fin m) where
  interaction :
    Reduction oSpec StmtIn WitIn StmtMid WitMid (pSpec.renameMessage CommitmentType)
  opening :
    Reduction oSpec StmtMid WitMid StmtOut WitOut (pSpec.BCSOpeningPhase pSpecCom e)
  interaction_realizes_oracle_messages : Prop
  opening_realizes_query_log : Prop

/-- One verifier query to a committed oracle message, together with the commitment and response
that the BCS opening phase must justify. -/
structure BCSOpeningRequest (CommitmentType : pSpec.MessageIdx → Type) where
  messageIdx : pSpec.MessageIdx
  commitment : CommitmentType messageIdx
  query : (Oₘ messageIdx).Query
  response : (Oₘ messageIdx).Response query

/-- The dependent opening statement for one committed oracle message.

For `CommitmentType = Commitment`, this is exactly the statement type consumed by
`Reduction.bcsMessageOpening` at the message index `i`. -/
abbrev BCSOpeningStatementAt (CommitmentType : pSpec.MessageIdx → Type)
    (i : pSpec.MessageIdx) :=
  CommitmentType i × (q : (Oₘ i).Query) × (Oₘ i).Response q

/-- Convert one typed BCS opening request to the dependent opening statement expected by the
per-message commitment-opening reduction. -/
def BCSOpeningRequest.toOpeningStatement {CommitmentType : pSpec.MessageIdx → Type}
    (request : BCSOpeningRequest (pSpec := pSpec) (Oₘ := Oₘ) CommitmentType) :
    BCSOpeningStatementAt (pSpec := pSpec) (Oₘ := Oₘ) CommitmentType request.messageIdx :=
  (request.commitment, ⟨request.query, request.response⟩)

@[simp] theorem BCSOpeningRequest.toOpeningStatement_commitment
    {CommitmentType : pSpec.MessageIdx → Type}
    (request : BCSOpeningRequest (pSpec := pSpec) (Oₘ := Oₘ) CommitmentType) :
    request.toOpeningStatement.1 = request.commitment :=
  rfl

@[simp] theorem BCSOpeningRequest.toOpeningStatement_query
    {CommitmentType : pSpec.MessageIdx → Type}
    (request : BCSOpeningRequest (pSpec := pSpec) (Oₘ := Oₘ) CommitmentType) :
    request.toOpeningStatement.2.1 = request.query :=
  rfl

@[simp] theorem BCSOpeningRequest.toOpeningStatement_response
    {CommitmentType : pSpec.MessageIdx → Type}
    (request : BCSOpeningRequest (pSpec := pSpec) (Oₘ := Oₘ) CommitmentType) :
    request.toOpeningStatement.2.2 = request.response :=
  rfl

/-- The concrete query/opening schedule consumed by the BCS opening phase.

For a non-adaptive oracle verifier this schedule should be obtained from
`OracleVerifier.NonAdaptive.queryMsg` after the interaction phase has retained the corresponding
commitments and oracle responses.  In the fully adaptive case, the future query-log API should
produce the same shape from the realized verifier execution. -/
abbrev BCSOpeningSchedule (CommitmentType : pSpec.MessageIdx → Type) :=
  List (BCSOpeningRequest (pSpec := pSpec) (Oₘ := Oₘ) CommitmentType)

/-- A schedule as the list of indexed opening statements that the per-message opening reductions
must discharge. -/
def BCSOpeningSchedule.toOpeningStatements {CommitmentType : pSpec.MessageIdx → Type}
    (schedule : BCSOpeningSchedule (pSpec := pSpec) (Oₘ := Oₘ) CommitmentType) :
    List ((i : pSpec.MessageIdx) ×
      BCSOpeningStatementAt (pSpec := pSpec) (Oₘ := Oₘ) CommitmentType i) :=
  schedule.map fun request => ⟨request.messageIdx, request.toOpeningStatement⟩

@[simp] theorem BCSOpeningSchedule.toOpeningStatements_nil
    {CommitmentType : pSpec.MessageIdx → Type} :
    (BCSOpeningSchedule.toOpeningStatements (pSpec := pSpec) (Oₘ := Oₘ)
      (CommitmentType := CommitmentType) []) = [] :=
  rfl

@[simp] theorem BCSOpeningSchedule.toOpeningStatements_cons
    {CommitmentType : pSpec.MessageIdx → Type}
    (request : BCSOpeningRequest (pSpec := pSpec) (Oₘ := Oₘ) CommitmentType)
    (schedule : BCSOpeningSchedule (pSpec := pSpec) (Oₘ := Oₘ) CommitmentType) :
    BCSOpeningSchedule.toOpeningStatements (request :: schedule) =
      ⟨request.messageIdx, request.toOpeningStatement⟩ ::
        BCSOpeningSchedule.toOpeningStatements schedule :=
  rfl

@[simp] theorem BCSOpeningSchedule.toOpeningStatements_length
    {CommitmentType : pSpec.MessageIdx → Type}
    (schedule : BCSOpeningSchedule (pSpec := pSpec) (Oₘ := Oₘ) CommitmentType) :
    schedule.toOpeningStatements.length = schedule.length :=
  List.length_map _

/-- Projecting the indexed opening statements back to message indices recovers the message-index
projection of the original typed schedule. -/
@[simp] theorem BCSOpeningSchedule.toOpeningStatements_map_messageIdx
    {CommitmentType : pSpec.MessageIdx → Type}
    (schedule : BCSOpeningSchedule (pSpec := pSpec) (Oₘ := Oₘ) CommitmentType) :
    schedule.toOpeningStatements.map (fun statement => statement.1) =
      schedule.map (fun request => request.messageIdx) := by
  induction schedule with
  | nil => rfl
  | cons request schedule ih =>
      simp [BCSOpeningSchedule.toOpeningStatements, ih]

/-- The typed opening-log boundary for the not-yet-generic BCS compiler.

The current `BCSCompiledPhases` interface still accepts an abstract opening phase.  This structure
records the concrete schedule that such an opening phase is meant to discharge, plus the two proof
obligations that connect the schedule back to the source oracle verifier and to retained
opening witnesses. -/
structure BCSOpeningLogFrontier (CommitmentType : pSpec.MessageIdx → Type) where
  schedule : BCSOpeningSchedule (pSpec := pSpec) (Oₘ := Oₘ) CommitmentType
  schedule_realizes_query_log : Prop
  schedule_has_retained_witnesses : Prop

/-- The typed opening-log obligations needed before an abstract BCS opening phase can be read as
faithfully discharging the source verifier's oracle queries. -/
def BCSOpeningLogFrontierSatisfied {CommitmentType : pSpec.MessageIdx → Type}
    (log : BCSOpeningLogFrontier (pSpec := pSpec) (Oₘ := Oₘ) CommitmentType) : Prop :=
  log.schedule_realizes_query_log ∧ log.schedule_has_retained_witnesses

/-- Package the two opening-log obligations from their independent proof bricks. -/
theorem BCSOpeningLogFrontierSatisfied.intro {CommitmentType : pSpec.MessageIdx → Type}
    {log : BCSOpeningLogFrontier (pSpec := pSpec) (Oₘ := Oₘ) CommitmentType}
    (hQueryLog : log.schedule_realizes_query_log)
    (hWitnesses : log.schedule_has_retained_witnesses) :
    BCSOpeningLogFrontierSatisfied log :=
  ⟨hQueryLog, hWitnesses⟩

/-- Project the query-log realization brick from the typed opening-log frontier. -/
theorem BCSOpeningLogFrontierSatisfied.queryLog {CommitmentType : pSpec.MessageIdx → Type}
    {log : BCSOpeningLogFrontier (pSpec := pSpec) (Oₘ := Oₘ) CommitmentType}
    (h : BCSOpeningLogFrontierSatisfied log) :
    log.schedule_realizes_query_log :=
  h.1

/-- Project the retained-witness brick from the typed opening-log frontier. -/
theorem BCSOpeningLogFrontierSatisfied.retainedWitnesses
    {CommitmentType : pSpec.MessageIdx → Type}
    {log : BCSOpeningLogFrontier (pSpec := pSpec) (Oₘ := Oₘ) CommitmentType}
    (h : BCSOpeningLogFrontierSatisfied log) :
    log.schedule_has_retained_witnesses :=
  h.2

/-- The remaining bridge from a discharged typed opening log to the abstract opening-phase
realization field carried by `BCSCompiledPhases`.  The eventual generic compiler should prove this
from the query-log API and the construction of the opening phase. -/
def BCSOpeningLogBridge {StmtMid WitMid : Type}
    {CommitmentType : pSpec.MessageIdx → Type} {e : pSpec.MessageIdx ≃ Fin m}
    (phases : BCSCompiledPhases (oSpec := oSpec) (pSpec := pSpec) (pSpecCom := pSpecCom)
      (StmtIn := StmtIn) (WitIn := WitIn) (StmtOut := StmtOut) (WitOut := WitOut)
      (StmtMid := StmtMid) (WitMid := WitMid) CommitmentType e)
    (log : BCSOpeningLogFrontier (pSpec := pSpec) (Oₘ := Oₘ) CommitmentType) : Prop :=
  BCSOpeningLogFrontierSatisfied log → phases.opening_realizes_query_log

/-- Interpret a packaged BCS compiler-frontier object as the currently available transformed
reduction.  This is definitionally the `Reduction.append` composition used by `BCSTransform`. -/
def BCSCompiledPhases.toReduction {StmtMid WitMid : Type}
    {CommitmentType : pSpec.MessageIdx → Type} {e : pSpec.MessageIdx ≃ Fin m}
    (phases : BCSCompiledPhases (oSpec := oSpec) (pSpec := pSpec) (pSpecCom := pSpecCom)
      (StmtIn := StmtIn) (WitIn := WitIn) (StmtOut := StmtOut) (WitOut := WitOut)
      (StmtMid := StmtMid) (WitMid := WitMid) CommitmentType e) :
    Reduction oSpec StmtIn WitIn StmtOut WitOut
      (pSpec.BCSTransform pSpecCom CommitmentType e) :=
  BCSTransform e phases.interaction phases.opening

/-- The phase-realization half of the BCS compiler frontier: the interaction phase must realize
the original oracle-message flow through commitments, and the opening phase must realize the
verifier's query log through commitment openings. This is deliberately a conjunction of the two
fields already carried by `BCSCompiledPhases`, so downstream files can require the compiler-frontier
content as one named hypothesis while still projecting the two independent bricks. -/
def BCSPhaseRealizationFrontier {StmtMid WitMid : Type}
    {CommitmentType : pSpec.MessageIdx → Type} {e : pSpec.MessageIdx ≃ Fin m}
    (phases : BCSCompiledPhases (oSpec := oSpec) (pSpec := pSpec) (pSpecCom := pSpecCom)
      (StmtIn := StmtIn) (WitIn := WitIn) (StmtOut := StmtOut) (WitOut := WitOut)
      (StmtMid := StmtMid) (WitMid := WitMid) CommitmentType e) : Prop :=
  phases.interaction_realizes_oracle_messages ∧ phases.opening_realizes_query_log

/-- Project the interaction-realization brick from the named phase frontier. -/
theorem BCSPhaseRealizationFrontier.interaction {StmtMid WitMid : Type}
    {CommitmentType : pSpec.MessageIdx → Type} {e : pSpec.MessageIdx ≃ Fin m}
    {phases : BCSCompiledPhases (oSpec := oSpec) (pSpec := pSpec) (pSpecCom := pSpecCom)
      (StmtIn := StmtIn) (WitIn := WitIn) (StmtOut := StmtOut) (WitOut := WitOut)
      (StmtMid := StmtMid) (WitMid := WitMid) CommitmentType e}
    (h : BCSPhaseRealizationFrontier phases) :
    phases.interaction_realizes_oracle_messages :=
  h.1

/-- Project the query-log-opening brick from the named phase frontier. -/
theorem BCSPhaseRealizationFrontier.opening {StmtMid WitMid : Type}
    {CommitmentType : pSpec.MessageIdx → Type} {e : pSpec.MessageIdx ≃ Fin m}
    {phases : BCSCompiledPhases (oSpec := oSpec) (pSpec := pSpec) (pSpecCom := pSpecCom)
      (StmtIn := StmtIn) (WitIn := WitIn) (StmtOut := StmtOut) (WitOut := WitOut)
      (StmtMid := StmtMid) (WitMid := WitMid) CommitmentType e}
    (h : BCSPhaseRealizationFrontier phases) :
    phases.opening_realizes_query_log :=
  h.2

/-- Build the phase-realization frontier from an interaction-realization proof and a discharged
typed opening-log frontier, provided the remaining opening-log bridge is available. -/
theorem BCSPhaseRealizationFrontier.ofOpeningLogBridge {StmtMid WitMid : Type}
    {CommitmentType : pSpec.MessageIdx → Type} {e : pSpec.MessageIdx ≃ Fin m}
    {phases : BCSCompiledPhases (oSpec := oSpec) (pSpec := pSpec) (pSpecCom := pSpecCom)
      (StmtIn := StmtIn) (WitIn := WitIn) (StmtOut := StmtOut) (WitOut := WitOut)
      (StmtMid := StmtMid) (WitMid := WitMid) CommitmentType e}
    {log : BCSOpeningLogFrontier (pSpec := pSpec) (Oₘ := Oₘ) CommitmentType}
    (hInteraction : phases.interaction_realizes_oracle_messages)
    (hLog : BCSOpeningLogFrontierSatisfied log)
    (hBridge : BCSOpeningLogBridge phases log) :
    BCSPhaseRealizationFrontier phases :=
  ⟨hInteraction, hBridge hLog⟩

/-- `BCSCompiledPhases.toReduction` is exactly the appended BCS transform on the packaged
interaction and opening phases. This small bridge lets downstream code unfold the current compiler
frontier through a named theorem rather than through record projections. -/
theorem BCSCompiledPhases.toReduction_eq_BCSTransform {StmtMid WitMid : Type}
    {CommitmentType : pSpec.MessageIdx → Type} {e : pSpec.MessageIdx ≃ Fin m}
    (phases : BCSCompiledPhases (oSpec := oSpec) (pSpec := pSpec) (pSpecCom := pSpecCom)
      (StmtIn := StmtIn) (WitIn := WitIn) (StmtOut := StmtOut) (WitOut := WitOut)
      (StmtMid := StmtMid) (WitMid := WitMid) CommitmentType e) :
    phases.toReduction = BCSTransform e phases.interaction phases.opening :=
  rfl

/-- Security obligations still required to turn `BCSCompiledPhases.toReduction` into the final
compiler theorem.  These are intentionally named as fields rather than hidden in one opaque
assumption: each field corresponds to a separate proof brick in issue #62.

The intended endgame is to replace this interface by the actual preservation theorems:
completeness from commitment correctness plus phase realization, and soundness / knowledge
soundness from commitment binding or extractability plus the oracle-reduction security theorem. -/
structure BCSSecurityFrontier {StmtMid WitMid : Type}
    {CommitmentType : pSpec.MessageIdx → Type} {e : pSpec.MessageIdx ≃ Fin m}
    (_phases : BCSCompiledPhases (oSpec := oSpec) (pSpec := pSpec) (pSpecCom := pSpecCom)
      (StmtIn := StmtIn) (WitIn := WitIn) (StmtOut := StmtOut) (WitOut := WitOut)
      (StmtMid := StmtMid) (WitMid := WitMid) CommitmentType e) where
  commitment_correctness_available : Prop
  commitment_binding_or_extractability_available : Prop
  completeness_preservation_target : Prop
  soundness_preservation_target : Prop
  knowledge_soundness_preservation_target : Prop

/-- The explicit checklist that remains before `BCSCompiledPhases.toReduction` can be promoted
from a compositional front door to a genuine BCS compiler theorem.

This is still an interface, not a security proof: each conjunct names one proof brick that the
full compiler must eventually produce from the source oracle reduction, the commitment schemes,
and the query-log API. -/
def BCSCompilerFrontierSatisfied {StmtMid WitMid : Type}
    {CommitmentType : pSpec.MessageIdx → Type} {e : pSpec.MessageIdx ≃ Fin m}
    (phases : BCSCompiledPhases (oSpec := oSpec) (pSpec := pSpec) (pSpecCom := pSpecCom)
      (StmtIn := StmtIn) (WitIn := WitIn) (StmtOut := StmtOut) (WitOut := WitOut)
      (StmtMid := StmtMid) (WitMid := WitMid) CommitmentType e)
    (frontier : BCSSecurityFrontier (oSpec := oSpec) (pSpec := pSpec) (pSpecCom := pSpecCom)
      (StmtIn := StmtIn) (WitIn := WitIn) (StmtOut := StmtOut) (WitOut := WitOut)
      (StmtMid := StmtMid) (WitMid := WitMid) phases) : Prop :=
  phases.interaction_realizes_oracle_messages ∧
  phases.opening_realizes_query_log ∧
  frontier.commitment_correctness_available ∧
  frontier.commitment_binding_or_extractability_available ∧
  frontier.completeness_preservation_target ∧
  frontier.soundness_preservation_target ∧
  frontier.knowledge_soundness_preservation_target

theorem BCSCompilerFrontierSatisfied.interaction_realizes_oracle_messages
    {StmtMid WitMid : Type}
    {CommitmentType : pSpec.MessageIdx → Type} {e : pSpec.MessageIdx ≃ Fin m}
    {phases : BCSCompiledPhases (oSpec := oSpec) (pSpec := pSpec) (pSpecCom := pSpecCom)
      (StmtIn := StmtIn) (WitIn := WitIn) (StmtOut := StmtOut) (WitOut := WitOut)
      (StmtMid := StmtMid) (WitMid := WitMid) CommitmentType e}
    {frontier : BCSSecurityFrontier (oSpec := oSpec) (pSpec := pSpec) (pSpecCom := pSpecCom)
      (StmtIn := StmtIn) (WitIn := WitIn) (StmtOut := StmtOut) (WitOut := WitOut)
      (StmtMid := StmtMid) (WitMid := WitMid) phases}
    (h : BCSCompilerFrontierSatisfied phases frontier) :
    phases.interaction_realizes_oracle_messages :=
  h.1

theorem BCSCompilerFrontierSatisfied.opening_realizes_query_log
    {StmtMid WitMid : Type}
    {CommitmentType : pSpec.MessageIdx → Type} {e : pSpec.MessageIdx ≃ Fin m}
    {phases : BCSCompiledPhases (oSpec := oSpec) (pSpec := pSpec) (pSpecCom := pSpecCom)
      (StmtIn := StmtIn) (WitIn := WitIn) (StmtOut := StmtOut) (WitOut := WitOut)
      (StmtMid := StmtMid) (WitMid := WitMid) CommitmentType e}
    {frontier : BCSSecurityFrontier (oSpec := oSpec) (pSpec := pSpec) (pSpecCom := pSpecCom)
      (StmtIn := StmtIn) (WitIn := WitIn) (StmtOut := StmtOut) (WitOut := WitOut)
      (StmtMid := StmtMid) (WitMid := WitMid) phases}
    (h : BCSCompilerFrontierSatisfied phases frontier) :
    phases.opening_realizes_query_log :=
  h.2.1

theorem BCSCompilerFrontierSatisfied.commitment_correctness_available
    {StmtMid WitMid : Type}
    {CommitmentType : pSpec.MessageIdx → Type} {e : pSpec.MessageIdx ≃ Fin m}
    {phases : BCSCompiledPhases (oSpec := oSpec) (pSpec := pSpec) (pSpecCom := pSpecCom)
      (StmtIn := StmtIn) (WitIn := WitIn) (StmtOut := StmtOut) (WitOut := WitOut)
      (StmtMid := StmtMid) (WitMid := WitMid) CommitmentType e}
    {frontier : BCSSecurityFrontier (oSpec := oSpec) (pSpec := pSpec) (pSpecCom := pSpecCom)
      (StmtIn := StmtIn) (WitIn := WitIn) (StmtOut := StmtOut) (WitOut := WitOut)
      (StmtMid := StmtMid) (WitMid := WitMid) phases}
    (h : BCSCompilerFrontierSatisfied phases frontier) :
    frontier.commitment_correctness_available :=
  h.2.2.1

theorem BCSCompilerFrontierSatisfied.commitment_binding_or_extractability_available
    {StmtMid WitMid : Type}
    {CommitmentType : pSpec.MessageIdx → Type} {e : pSpec.MessageIdx ≃ Fin m}
    {phases : BCSCompiledPhases (oSpec := oSpec) (pSpec := pSpec) (pSpecCom := pSpecCom)
      (StmtIn := StmtIn) (WitIn := WitIn) (StmtOut := StmtOut) (WitOut := WitOut)
      (StmtMid := StmtMid) (WitMid := WitMid) CommitmentType e}
    {frontier : BCSSecurityFrontier (oSpec := oSpec) (pSpec := pSpec) (pSpecCom := pSpecCom)
      (StmtIn := StmtIn) (WitIn := WitIn) (StmtOut := StmtOut) (WitOut := WitOut)
      (StmtMid := StmtMid) (WitMid := WitMid) phases}
    (h : BCSCompilerFrontierSatisfied phases frontier) :
    frontier.commitment_binding_or_extractability_available :=
  h.2.2.2.1

theorem BCSCompilerFrontierSatisfied.completeness_preservation_target
    {StmtMid WitMid : Type}
    {CommitmentType : pSpec.MessageIdx → Type} {e : pSpec.MessageIdx ≃ Fin m}
    {phases : BCSCompiledPhases (oSpec := oSpec) (pSpec := pSpec) (pSpecCom := pSpecCom)
      (StmtIn := StmtIn) (WitIn := WitIn) (StmtOut := StmtOut) (WitOut := WitOut)
      (StmtMid := StmtMid) (WitMid := WitMid) CommitmentType e}
    {frontier : BCSSecurityFrontier (oSpec := oSpec) (pSpec := pSpec) (pSpecCom := pSpecCom)
      (StmtIn := StmtIn) (WitIn := WitIn) (StmtOut := StmtOut) (WitOut := WitOut)
      (StmtMid := StmtMid) (WitMid := WitMid) phases}
    (h : BCSCompilerFrontierSatisfied phases frontier) :
    frontier.completeness_preservation_target :=
  h.2.2.2.2.1

theorem BCSCompilerFrontierSatisfied.soundness_preservation_target
    {StmtMid WitMid : Type}
    {CommitmentType : pSpec.MessageIdx → Type} {e : pSpec.MessageIdx ≃ Fin m}
    {phases : BCSCompiledPhases (oSpec := oSpec) (pSpec := pSpec) (pSpecCom := pSpecCom)
      (StmtIn := StmtIn) (WitIn := WitIn) (StmtOut := StmtOut) (WitOut := WitOut)
      (StmtMid := StmtMid) (WitMid := WitMid) CommitmentType e}
    {frontier : BCSSecurityFrontier (oSpec := oSpec) (pSpec := pSpec) (pSpecCom := pSpecCom)
      (StmtIn := StmtIn) (WitIn := WitIn) (StmtOut := StmtOut) (WitOut := WitOut)
      (StmtMid := StmtMid) (WitMid := WitMid) phases}
    (h : BCSCompilerFrontierSatisfied phases frontier) :
    frontier.soundness_preservation_target :=
  h.2.2.2.2.2.1

theorem BCSCompilerFrontierSatisfied.knowledge_soundness_preservation_target
    {StmtMid WitMid : Type}
    {CommitmentType : pSpec.MessageIdx → Type} {e : pSpec.MessageIdx ≃ Fin m}
    {phases : BCSCompiledPhases (oSpec := oSpec) (pSpec := pSpec) (pSpecCom := pSpecCom)
      (StmtIn := StmtIn) (WitIn := WitIn) (StmtOut := StmtOut) (WitOut := WitOut)
      (StmtMid := StmtMid) (WitMid := WitMid) CommitmentType e}
    {frontier : BCSSecurityFrontier (oSpec := oSpec) (pSpec := pSpec) (pSpecCom := pSpecCom)
      (StmtIn := StmtIn) (WitIn := WitIn) (StmtOut := StmtOut) (WitOut := WitOut)
      (StmtMid := StmtMid) (WitMid := WitMid) phases}
    (h : BCSCompilerFrontierSatisfied phases frontier) :
    frontier.knowledge_soundness_preservation_target :=
  h.2.2.2.2.2.2

/-- Compatibility name for the full BCS compiler-frontier checklist. -/
abbrev BCSCompilerFrontierReady {StmtMid WitMid : Type}
    {CommitmentType : pSpec.MessageIdx → Type} {e : pSpec.MessageIdx ≃ Fin m}
    (phases : BCSCompiledPhases (oSpec := oSpec) (pSpec := pSpec) (pSpecCom := pSpecCom)
      (StmtIn := StmtIn) (WitIn := WitIn) (StmtOut := StmtOut) (WitOut := WitOut)
      (StmtMid := StmtMid) (WitMid := WitMid) CommitmentType e)
    (frontier : BCSSecurityFrontier (oSpec := oSpec) (pSpec := pSpec) (pSpecCom := pSpecCom)
      (StmtIn := StmtIn) (WitIn := WitIn) (StmtOut := StmtOut) (WitOut := WitOut)
      (StmtMid := StmtMid) (WitMid := WitMid) phases) : Prop :=
  BCSCompilerFrontierSatisfied phases frontier

/-- Package the named BCS compiler-frontier obligations from their independent proof bricks. -/
theorem BCSCompilerFrontierReady.intro {StmtMid WitMid : Type}
    {CommitmentType : pSpec.MessageIdx → Type} {e : pSpec.MessageIdx ≃ Fin m}
    {phases : BCSCompiledPhases (oSpec := oSpec) (pSpec := pSpec) (pSpecCom := pSpecCom)
      (StmtIn := StmtIn) (WitIn := WitIn) (StmtOut := StmtOut) (WitOut := WitOut)
      (StmtMid := StmtMid) (WitMid := WitMid) CommitmentType e}
    {frontier : BCSSecurityFrontier (oSpec := oSpec) (pSpec := pSpec) (pSpecCom := pSpecCom)
      (StmtIn := StmtIn) (WitIn := WitIn) (StmtOut := StmtOut) (WitOut := WitOut)
      (StmtMid := StmtMid) (WitMid := WitMid) phases}
    (hPhase : BCSPhaseRealizationFrontier phases)
    (hCorrect : frontier.commitment_correctness_available)
    (hBindingOrExtract : frontier.commitment_binding_or_extractability_available)
    (hComplete : frontier.completeness_preservation_target)
    (hSound : frontier.soundness_preservation_target)
    (hKS : frontier.knowledge_soundness_preservation_target) :
    BCSCompilerFrontierReady phases frontier :=
  ⟨hPhase.1, hPhase.2, hCorrect, hBindingOrExtract, hComplete, hSound, hKS⟩

/-- Project the phase-realization obligations from a ready BCS compiler frontier. -/
theorem BCSCompilerFrontierReady.phase {StmtMid WitMid : Type}
    {CommitmentType : pSpec.MessageIdx → Type} {e : pSpec.MessageIdx ≃ Fin m}
    {phases : BCSCompiledPhases (oSpec := oSpec) (pSpec := pSpec) (pSpecCom := pSpecCom)
      (StmtIn := StmtIn) (WitIn := WitIn) (StmtOut := StmtOut) (WitOut := WitOut)
      (StmtMid := StmtMid) (WitMid := WitMid) CommitmentType e}
    {frontier : BCSSecurityFrontier (oSpec := oSpec) (pSpec := pSpec) (pSpecCom := pSpecCom)
      (StmtIn := StmtIn) (WitIn := WitIn) (StmtOut := StmtOut) (WitOut := WitOut)
      (StmtMid := StmtMid) (WitMid := WitMid) phases}
    (h : BCSCompilerFrontierReady phases frontier) :
    BCSPhaseRealizationFrontier phases :=
  ⟨h.1, h.2.1⟩

/-- Build the full ready checklist from a discharged typed opening log plus the remaining
security-frontier fields. This is the direct adapter expected from the current BCS interface:
`BCSPhaseRealizationFrontier.ofOpeningLogBridge` supplies the phase half, and
`BCSCompilerFrontierReady.intro` adds the commitment/security obligations. -/
theorem BCSCompilerFrontierReady.ofOpeningLogBridge {StmtMid WitMid : Type}
    {CommitmentType : pSpec.MessageIdx → Type} {e : pSpec.MessageIdx ≃ Fin m}
    {phases : BCSCompiledPhases (oSpec := oSpec) (pSpec := pSpec) (pSpecCom := pSpecCom)
      (StmtIn := StmtIn) (WitIn := WitIn) (StmtOut := StmtOut) (WitOut := WitOut)
      (StmtMid := StmtMid) (WitMid := WitMid) CommitmentType e}
    {frontier : BCSSecurityFrontier (oSpec := oSpec) (pSpec := pSpec) (pSpecCom := pSpecCom)
      (StmtIn := StmtIn) (WitIn := WitIn) (StmtOut := StmtOut) (WitOut := WitOut)
      (StmtMid := StmtMid) (WitMid := WitMid) phases}
    {log : BCSOpeningLogFrontier (pSpec := pSpec) (Oₘ := Oₘ) CommitmentType}
    (hInteraction : phases.interaction_realizes_oracle_messages)
    (hLog : BCSOpeningLogFrontierSatisfied log)
    (hBridge : BCSOpeningLogBridge phases log)
    (hCorrect : frontier.commitment_correctness_available)
    (hBindingOrExtract : frontier.commitment_binding_or_extractability_available)
    (hComplete : frontier.completeness_preservation_target)
    (hSound : frontier.soundness_preservation_target)
    (hKS : frontier.knowledge_soundness_preservation_target) :
    BCSCompilerFrontierReady phases frontier :=
  BCSCompilerFrontierReady.intro
    (BCSPhaseRealizationFrontier.ofOpeningLogBridge hInteraction hLog hBridge)
    hCorrect hBindingOrExtract hComplete hSound hKS
/-! #### Design note: the fully general transform

  In full generality (deferred to ArkLib#433), the transform should take

  * `reduction : OracleReduction oSpec StmtIn OStmtIn WitIn StmtOut OStmtOut WitOut pSpec`, and
  * for each prover message `i : pSpec.MessageIdx`, a commitment scheme
    `Scheme oSpec (pSpec.Message i) (Commitment i) (Decommitment i) (ComKey i) (VerifKey i)
      (pSpecCom i)`,

  and produce a `Reduction` over `pSpec.BCSTransform pSpecCom Commitment e`, where:

  * the interaction phase is built from `reduction` by having the prover, at each message round,
    compute `(cm, decomm) ← scheme.commit ck msg` and send `cm : Commitment i` (the renamed message
    type) while retaining `(msg, decomm)` in its state; the verifier runs the original oracle
    verifier with each oracle-message query answered against the committed value;
  * the opening phase is `Reduction.seqCompose` of the per-message opening reductions
    `Reduction.bcsMessageOpening i (scheme i) (ck i, vk i)` (reindexed by `e`), where the queried
    points and responses are read off from the oracle verifier's query log and the witnesses are the
    retained `(msg, decomm)` pairs.

  The blocker is reading the (possibly adaptive) oracle verifier's query log to determine which
  openings to run; restricting to `OracleVerifier.NonAdaptive` (whose `queryMsg` is a fixed list)
  removes the adaptivity blocker but the statement/witness threading still depends on the #433
  refactor. -/

end OracleReduction

/-! ## Axiom audit — BCS transform/frontier declarations.

These lines are regression anchors for the current interface boundary only. They do not prove the
generic compiler construction or the completeness/soundness preservation theorems. -/
#print axioms ProtocolSpec.renameMessage
#print axioms ProtocolSpec.BCSOpeningPhase
#print axioms ProtocolSpec.BCSTransform
#print axioms Reduction.bcsMessageOpening
#print axioms OracleReduction.BCSTransform
#print axioms OracleReduction.BCSCompiledPhases
#print axioms OracleReduction.BCSOpeningRequest
#print axioms OracleReduction.BCSOpeningStatementAt
#print axioms OracleReduction.BCSOpeningRequest.toOpeningStatement
#print axioms OracleReduction.BCSOpeningRequest.toOpeningStatement_commitment
#print axioms OracleReduction.BCSOpeningRequest.toOpeningStatement_query
#print axioms OracleReduction.BCSOpeningRequest.toOpeningStatement_response
#print axioms OracleReduction.BCSOpeningSchedule
#print axioms OracleReduction.BCSOpeningSchedule.toOpeningStatements
#print axioms OracleReduction.BCSOpeningSchedule.toOpeningStatements_nil
#print axioms OracleReduction.BCSOpeningSchedule.toOpeningStatements_cons
#print axioms OracleReduction.BCSOpeningSchedule.toOpeningStatements_length
#print axioms OracleReduction.BCSOpeningSchedule.toOpeningStatements_map_messageIdx
#print axioms OracleReduction.BCSOpeningLogFrontier
#print axioms OracleReduction.BCSOpeningLogFrontierSatisfied
#print axioms OracleReduction.BCSOpeningLogFrontierSatisfied.intro
#print axioms OracleReduction.BCSOpeningLogFrontierSatisfied.queryLog
#print axioms OracleReduction.BCSOpeningLogFrontierSatisfied.retainedWitnesses
#print axioms OracleReduction.BCSOpeningLogBridge
#print axioms OracleReduction.BCSCompiledPhases.toReduction
#print axioms OracleReduction.BCSPhaseRealizationFrontier
#print axioms OracleReduction.BCSPhaseRealizationFrontier.interaction
#print axioms OracleReduction.BCSPhaseRealizationFrontier.opening
#print axioms OracleReduction.BCSPhaseRealizationFrontier.ofOpeningLogBridge
#print axioms OracleReduction.BCSCompiledPhases.toReduction_eq_BCSTransform
#print axioms OracleReduction.BCSSecurityFrontier
#print axioms OracleReduction.BCSCompilerFrontierSatisfied
#print axioms OracleReduction.BCSCompilerFrontierSatisfied.interaction_realizes_oracle_messages
#print axioms OracleReduction.BCSCompilerFrontierSatisfied.opening_realizes_query_log
#print axioms OracleReduction.BCSCompilerFrontierSatisfied.commitment_correctness_available
#print axioms OracleReduction.BCSCompilerFrontierSatisfied.commitment_binding_or_extractability_available
#print axioms OracleReduction.BCSCompilerFrontierSatisfied.completeness_preservation_target
#print axioms OracleReduction.BCSCompilerFrontierSatisfied.soundness_preservation_target
#print axioms OracleReduction.BCSCompilerFrontierSatisfied.knowledge_soundness_preservation_target
#print axioms OracleReduction.BCSCompilerFrontierReady
#print axioms OracleReduction.BCSCompilerFrontierReady.intro
#print axioms OracleReduction.BCSCompilerFrontierReady.phase
#print axioms OracleReduction.BCSCompilerFrontierReady.ofOpeningLogBridge

/-
Copyright (c) 2024 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

import ArkLib.CommitmentScheme.Basic
import ArkLib.OracleReduction.Composition.Sequential.General

/-!
# The Generalized Ben-Sasson–Chiesa–Spooner (BCS) Compiler

This module formalizes the generalized Ben-Sasson–Chiesa–Spooner (BCS) compilation technique (TCC 2016)
at the protocol specification and reduction levels. The BCS transform compiles an Interactive Oracle
Reduction (IOR) into a standard Interactive Reduction (IR) (or interactive proof system) by replacing
oracle messages with cryptographic commitments.

In the compiled protocol, the prover sends commitments to each oracle message, and the verifier interacts
with the prover to receive challenges. Finally, in the opening phase, the prover shows that the verifier's
oracle queries are consistent with the sent commitments using interactive opening arguments. This compiles
oracle-dependent protocols into concrete protocols, capturing both the classical Merkle-tree compilation
of IOPs and modern polynomial commitment compilers (e.g., Marlin, Plonk) for polynomial IOPs.

The transformation establishes a composition where:
1. Every oracle message type is replaced with a commitment type (via `renameMessage`).
2. An opening phase consisting of the sequential composition of the per-message commitment-opening protocol
   specifications is appended.
-/

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
  `e : pSpec.MessageIdx ≃ Fin m` as a parameter. This makes the order of the opening phase explicit:
  as noted in the module docstring, the BCS transform has a genuine degree of freedom in the order in
  which the opening arguments are run, and `e` records that choice. (Taking `e` as a parameter rather
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

  This is the faithful statement sketched in the original commented placeholder
  `.append (pSpec.renameMessage CommType) (placeholder)`. -/
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
     `pSpec.BCSOpeningPhase pSpecCom e` — morally the verifier's evaluation queries discharged by the
     per-message opening proofs (see `Reduction.bcsMessageOpening`), composed in the order `e`.

  The honest construction of the **interaction phase** from the input oracle `reduction` and the
  commitment schemes (the prover commits to each message via `scheme.commit` instead of sending it,
  and the verifier checks the renamed transcript) and the honest construction of the **opening
  phase** from the verifier's query log (which queries to discharge, in which order, with which
  witnesses) are precisely the parts that require the dependent-type plumbing over query logs. These,
  together with the proofs that the transform preserves completeness / soundness / knowledge
  soundness / HVZK, are deferred to the core oracle-reduction rewrite (ArkLib#433). We therefore take
  the two phases as inputs and record the resulting type-level statement of the transform; this is
  the "initial attempt to state the BCS transform" called for by ArkLib#2.

  The fully general transform (no separate-phase inputs) is sketched in the design comment below. -/

/-- The BCS transformation on (interactive) reductions, stated as the sequential composition of the
  interaction phase (messages replaced by commitments) and the opening phase (per-message opening
  proofs run in sequence), over the BCS-transformed protocol spec
  `ProtocolSpec.BCSTransform pSpecCom CommitmentType e`.

  Here `StmtMid`/`WitMid` are the intermediate statement/witness handed from the interaction phase to
  the opening phase (it carries, e.g., the commitments, the queried points, and the openings needed
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

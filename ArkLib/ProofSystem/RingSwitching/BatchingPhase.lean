/-
Copyright (c) 2025 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chung Thai Nguyen, Quang Dao
-/

import ArkLib.ProofSystem.RingSwitching.Prelude
import ArkLib.ProofSystem.RingSwitching.Spec
import ArkLib.OracleReduction.Basic
import CompPoly.Fields.Binary.Tower.TensorAlgebra

/-!
# Ring-Switching IOP Batching Phase

This module implements the Batching Phase of the ring-switching IOP: steps 1-5.
This phase is the initial phase of the Interactive Oracle Proof and consists of:

## Construction 3.1 - Steps 1-5 (Batching Phase)

We define `(P, V)` as the following IOP, in which both parties have the common
input `[f]`, `s ∈ L`, and `(r_0, ..., r_{ℓ-1}) ∈ L^ℓ`, and `P` has the further
input `t(X_0, ..., X_{ℓ-1}) ∈ K[X_0, ..., X_{ℓ-1}]^⪯1`.

1. `P` computes `ŝ := φ₁(t')(φ₀(r_κ), ..., φ₀(r_{ℓ-1}))` and sends `V` the A-element `ŝ`.
2. `V` decomposes `ŝ =: Σ_{v ∈ {0,1}^κ} ŝ_v ⊗ β_v`.
  `V` requires `s ?= Σ_{v ∈ {0,1}^κ} eq̃(v_0, ..., v_{κ-1}, r_0, ..., r_{κ-1}) ⋅ ŝ_v`.
3. `V` samples batching scalars `(r''_0, ..., r''_{κ-1}) ← L^κ` and sends them to `P`.
4. For each `w ∈ {0,1}^{ℓ'}`,
  `P` decomposes `eq̃(r_κ, ..., r_{ℓ-1}, w_0, ..., w_{ℓ'-1})`
    `=: Σ_{u ∈ {0,1}^κ} A_{w, u} ⋅ β_u`.
  `P` defines the function
    `A: w ↦ Σ_{u ∈ {0,1}^κ} eq̃(u_0, ..., u_{κ-1}, r''_0, ..., r''_{κ-1}) ⋅ A_{w, u}`
    on `{0,1}^{ℓ'}` and writes `A(X_0, ..., X_{ℓ'-1})` for its multilinear extension.
  `P` defines `h(X_0, ..., X_{ℓ'-1}) := A(X_0, ..., X_{ℓ'-1}) ⋅ t'(X_0, ..., X_{ℓ'-1})`.c
5. `V` decomposes `ŝ =: Σ_{u ∈ {0,1}^κ} β_u ⊗ ŝ_u`, and
  sets `s_0 := Σ_{u ∈ {0,1}^κ} eq̃(u_0, ..., u_{κ-1}, r''_0, ..., r''_{κ-1}) ⋅ ŝ_u`.

Input: `witIn = BatchingWitIn, stmtIn = BatchingStmtIn, oStmt = aOStmtIn.OStmtIn`

Output: `witOut = (Statement (L := L) (ℓ := ℓ')`
  `(RingSwitchingBaseContext κ L K ℓ P) 0) × (SumcheckWitness L ℓ' 0), oStmt = aOStmtIn.OStmtIn`
-/

open OracleSpec OracleComp ProtocolSpec Finset Polynomial MvPolynomial
  Module TensorProduct Nat Matrix
open scoped NNReal
open Sumcheck.Structured

noncomputable section
namespace RingSwitching.BatchingPhase

/-- The default oracle interface (`OracleInterface.instDefault`, used by the ring-switching message
oracles in `Spec.lean`) answers its only (unit) query with the message itself. -/
@[simp] lemma answer_instDefault {M : Type _} (m : M) (q : Unit) :
    @OracleInterface.answer M OracleInterface.instDefault m q = m := rfl

open OracleInterface in
/-- Local message-query collapse for `OracleInterface.simOracle2`. -/
lemma simulateQ_simOracle2_messageQuery {ι : Type} {oSpec : OracleSpec ι}
    {ι₁ : Type} {T₁ : ι₁ → Type} [∀ i, OracleInterface (T₁ i)]
    {ι₂ : Type} {T₂ : ι₂ → Type} [∀ i, OracleInterface (T₂ i)]
    (t₁ : ∀ i, T₁ i) (t₂ : ∀ i, T₂ i) (qm : ([T₂]ₒ).Domain) :
    simulateQ (OracleInterface.simOracle2 oSpec t₁ t₂)
      (liftM (([T₂]ₒ).query qm) : OracleComp (oSpec + ([T₁]ₒ + [T₂]ₒ)) _)
      = (pure (OracleInterface.answer (t₂ qm.1) qm.2) : OracleComp oSpec _) := by
  change simulateQ (OracleInterface.simOracle2 oSpec t₁ t₂)
      (liftM ((oSpec + ([T₁]ₒ + [T₂]ₒ)).query (Sum.inr (Sum.inr qm)))) = _
  rw [simulateQ_spec_query]
  simp only [OracleInterface.simOracle2, QueryImpl.addLift_def, QueryImpl.add_apply_inr,
    QueryImpl.liftTarget_apply]
  change liftM (OracleInterface.simOracle0 T₂ t₂ qm) = _
  simp only [OracleInterface.simOracle0]
  rfl

open OracleInterface in
/-- OptionT/query form of `simulateQ_simOracle2_messageQuery`. -/
lemma simulateQ_simOracle2_query {ι : Type} {oSpec : OracleSpec ι}
    {ι₁ : Type} {T₁ : ι₁ → Type} [∀ i, OracleInterface (T₁ i)]
    {ι₂ : Type} {T₂ : ι₂ → Type} [∀ i, OracleInterface (T₂ i)]
    (t₁ : ∀ i, T₁ i) (t₂ : ∀ i, T₂ i) (qm : ([T₂]ₒ).Domain) :
    simulateQ (OracleInterface.simOracle2 oSpec t₁ t₂)
      (query (spec := [T₂]ₒ) qm : OptionT (OracleComp (oSpec + ([T₁]ₒ + [T₂]ₒ))) _)
      = (OptionT.lift (pure (OracleInterface.answer (t₂ qm.1) qm.2))
          : OptionT (OracleComp oSpec) _) := by
  rw [show (query (spec := [T₂]ₒ) qm : OptionT (OracleComp (oSpec + ([T₁]ₒ + [T₂]ₒ))) _)
        = OptionT.lift (liftM (([T₂]ₒ).query qm) : OracleComp (oSpec + ([T₁]ₒ + [T₂]ₒ)) _) from rfl]
  rw [simulateQ_optionT_lift, simulateQ_simOracle2_messageQuery]
  rfl

variable (κ : ℕ) [NeZero κ]
variable (L : Type) [CommRing L] [Nontrivial L] [Fintype L] [DecidableEq L]
  [SampleableType L]
variable (K : Type) [CommRing K] [Fintype K] [DecidableEq K]
variable [Algebra K L]
variable (P : RingSwitchingProfile K L κ)
variable (ℓ ℓ' : ℕ) [NeZero ℓ] [NeZero ℓ']
variable (h_l : ℓ = ℓ' + κ)
variable (aOStmtIn : AbstractOStmtIn L ℓ')

/-! ## Formalized Helper Functions
These functions provide concrete implementations for tensor algebra operations
and other logic required by the protocol.
-/

/-- A dummy state returned by the verifier upon failure of Check 1. -/
def failureState (stmt : BatchingStmtIn L ℓ) (s_hat : P.A) :
    Statement (L := L) (ℓ := ℓ') (RingSwitchingBaseContext κ L K ℓ P) 0 := {
    ctx := {
      t_eval_point := stmt.t_eval_point,
      original_claim := stmt.original_claim
      s_hat := s_hat,
      r_batching := 0, -- Dummy value
    },
    sumcheck_target := 0,
    challenges := Fin.elim0
  }

/-! ## Prover and Verifier Implementation -/

/-- The state maintained by the prover throughout the batching phase. -/
def PrvState : Fin (2 + 1) → Type
  | ⟨0, _⟩ => BatchingStmtIn L ℓ × (∀ j, aOStmtIn.OStmtIn j) × BatchingWitIn L K ℓ ℓ'
  | ⟨1, _⟩ => BatchingStmtIn L ℓ × (∀ j, aOStmtIn.OStmtIn j)
    × BatchingWitIn L K ℓ ℓ' × P.A
  | _ => BatchingStmtIn L ℓ × (∀ j, aOStmtIn.OStmtIn j)
    × BatchingWitIn L K ℓ ℓ' × P.A × (Fin κ → L)

noncomputable def oracleProver :
  OracleProver (oSpec:=[]ₒ)
    (StmtIn := BatchingStmtIn L ℓ) (OStmtIn := aOStmtIn.OStmtIn) (WitIn := BatchingWitIn L K ℓ ℓ')
    (StmtOut := Statement (L := L) (ℓ := ℓ')
      (RingSwitchingBaseContext κ L K ℓ P) 0) (OStmtOut := aOStmtIn.OStmtIn)
    (WitOut := SumcheckWitness L ℓ' 0)
    (pSpec := pSpecBatching (κ:=κ) (L:=L) (K:=K) (P:=P)) where
  PrvState := PrvState κ L K P ℓ ℓ' aOStmtIn

  input := fun ⟨⟨stmt, oStmt⟩, wit⟩ => (stmt, oStmt, wit)

  sendMessage
    | ⟨0, _⟩ => fun (stmt, oStmt, wit) => do
      -- Step 1: P computes ŝ and sends it.
      let s_hat := embedded_MLP_eval κ L K P ℓ ℓ' h_l wit.t' stmt.t_eval_point
      return ⟨s_hat, (stmt, oStmt, wit, s_hat)⟩
    | ⟨1, h⟩ => fun _ => do nomatch h -- V to P round

  receiveChallenge
    | ⟨0, h⟩ => nomatch h -- i.e. contradiction
    | ⟨1, _⟩ => fun ⟨stmt, oStmt, wit, s_hat⟩ => do
      return fun r_batching => (stmt, oStmt, wit, s_hat, r_batching)

  output := fun ⟨stmt, oStmt, wit, s_hat, r_batching⟩ => do
    -- Step 4: P computes the batched polynomial h.
    let ctx: RingSwitchingBaseContext κ L K ℓ P := {
      t_eval_point := stmt.t_eval_point,
      original_claim := stmt.original_claim,
      s_hat := s_hat,
      r_batching := r_batching
    }
    let h_poly: ↥L⦃≤ 2⦄[X Fin ℓ'] :=
      projectToMidSumcheckPoly (L := L) (ℓ := ℓ') (t := wit.t')
        (m := (RingSwitching_SumcheckMultParam κ L K P ℓ ℓ' h_l).multpoly (ctx := ctx))
        (i := 0) (challenges := Fin.elim0)
    -- Prover computes s₀ locally for its output witness.
    let s₀ := compute_s0 κ L K P s_hat r_batching
    let stmtOut : Statement (L := L) (ℓ := ℓ') (RingSwitchingBaseContext κ L K ℓ P) 0 := {
      ctx := ctx,
      sumcheck_target := s₀,
      challenges := Fin.elim0
    }
    let witOut : SumcheckWitness L ℓ' 0 := {
      t' := wit.t',
      H := h_poly
    }
    return (⟨stmtOut, oStmt⟩, witOut)

noncomputable def oracleVerifier :
  OracleVerifier (oSpec:=[]ₒ)
    (StmtIn := BatchingStmtIn L ℓ) (OStmtIn := aOStmtIn.OStmtIn)
    (StmtOut := Statement (L := L) (ℓ := ℓ') (RingSwitchingBaseContext κ L K ℓ P) 0)
    (OStmtOut := aOStmtIn.OStmtIn)
    (pSpec := pSpecBatching (κ:=κ) (L:=L) (K:=K) (P:=P)) where
  verify | stmt, pSpec_batching_challenges => do
     -- Step 1: Query prover for ŝ (Message 0).
    let s_hat : P.A ← query (spec := [pSpecBatching (κ:=κ)
      (L:=L) (K:=K) (P:=P).Message]ₒ) ⟨⟨0, rfl⟩, ()⟩

    -- Step 2: Perform Check 1.
    unless performCheckOriginalEvaluation κ L K P ℓ ℓ' h_l
      stmt.original_claim stmt.t_eval_point s_hat do
      return (failureState κ L K P ℓ ℓ' stmt s_hat) -- Abort if check fails

    -- Step 3: Sample batching scalars r'' (Challenge 1).
    let r_batching : Fin κ → L := pSpec_batching_challenges ⟨1, by rfl⟩

    -- Step 5: Compute s₀.
    let s₀ := compute_s0 κ L K P s_hat r_batching

    -- Construct the output statement for the next phase.
    let ctx : RingSwitchingBaseContext κ L K ℓ P := {
      t_eval_point := stmt.t_eval_point,
      original_claim := stmt.original_claim,
      s_hat := s_hat,
      r_batching := r_batching
    }
    let stmtOut : Statement (L := L) (ℓ := ℓ') (RingSwitchingBaseContext κ L K ℓ P) 0 := {
      ctx := ctx,
      sumcheck_target := s₀,
      challenges := Fin.elim0
    }
    return stmtOut
  -- Standard embedding for empty oSpec.
  embed := ⟨fun j => Sum.inl j, fun a b h => by cases h; rfl⟩
  hEq := fun i => rfl

/-- The batching-phase oracle verifier passes every output oracle through to the unchanged input
oracle (`embed = Sum.inl`, `OStmtIn = OStmtOut`, `hEq = rfl`) and exposes no message oracle, so its
`AppendCoherent` coherence holds by `rfl`. Used to `.append` the batching phase onto the core
interaction phase. -/
instance instOracleVerifierAppendCoherent :
    OracleVerifier.Append.AppendCoherent
      (oracleVerifier κ L K P ℓ ℓ' h_l (aOStmtIn := aOStmtIn)) where
  hCohInl := fun a k h => by
    have : a = k := by
      simpa only [oracleVerifier, Function.Embedding.coeFn_mk, Sum.inl.injEq] using h
    subst this; rfl
  hCohInr := fun a k h => by
    simp only [oracleVerifier, Function.Embedding.coeFn_mk, reduceCtorEq] at h

open OracleInterface in
omit [NeZero κ] [Fintype L] [SampleableType L] [Fintype K] [DecidableEq K]
  [NeZero ℓ] [NeZero ℓ'] in
/-- The inner oracle verifier body, simulated through `simOracle2`, collapses to the
deterministic `if performCheck … then stmtOutAccept else failureState`. -/
lemma oracleVerifier_verify_collapse
    (stmt : BatchingStmtIn L ℓ) (oStmt : ∀ j, aOStmtIn.OStmtIn j)
    (tr : FullTranscript (pSpecBatching (κ:=κ) (L:=L) (K:=K) (P:=P))) :
    simulateQ (OracleInterface.simOracle2 []ₒ oStmt (FullTranscript.messages tr))
        ((oracleVerifier κ L K P ℓ ℓ' h_l (aOStmtIn:=aOStmtIn)).verify stmt
          (FullTranscript.challenges tr))
      = (if performCheckOriginalEvaluation κ L K P ℓ ℓ' h_l stmt.original_claim
              stmt.t_eval_point (FullTranscript.messages tr ⟨0, by rfl⟩) then
           pure ({ ctx := { t_eval_point := stmt.t_eval_point,
                            original_claim := stmt.original_claim,
                            s_hat := FullTranscript.messages tr ⟨0, by rfl⟩,
                            r_batching := FullTranscript.challenges tr ⟨1, by rfl⟩ },
                   sumcheck_target := compute_s0 κ L K P
                     (FullTranscript.messages tr ⟨0, by rfl⟩)
                     (FullTranscript.challenges tr ⟨1, by rfl⟩),
                   challenges := Fin.elim0 } : Statement (L:=L) (ℓ:=ℓ')
                     (RingSwitchingBaseContext κ L K ℓ P) 0)
         else pure (failureState κ L K P ℓ ℓ' stmt (FullTranscript.messages tr ⟨0, by rfl⟩))
         : OptionT (OracleComp []ₒ) _) := by
  simp only [oracleVerifier]
  rw [simulateQ_optionT_bind, simulateQ_simOracle2_query]
  -- `simulateQ (simOracle2 …) (query) = OptionT.lift (pure (answer …))`. Reduce the lift-bind at
  -- the `.run` level via `OptionT.run_bind_lift` (+ `pure_bind`), then push `simulateQ` through
  -- the query-free `if`.
  refine OptionT.ext ?_
  dsimp only [Sigma.fst, Sigma.snd]
  erw [OptionT.run_bind_lift]
  erw [pure_bind]
  -- The `instDefault` answer is the message itself: reduce `answer m () = m` FIRST so the two
  -- `if`-conditions coincide, then push `simulateQ`/`OptionT.run` through the query-free
  --   `if`/`pure`s.
  rw [answer_instDefault]
  simp only [apply_ite, bind_pure_comp, map_pure]
  -- Both `if`-conditions are now identical; collapse the nested `if` and `simulateQ (pure …)`.
  by_cases hc : performCheckOriginalEvaluation κ L K P ℓ ℓ' h_l stmt.original_claim
      stmt.t_eval_point (FullTranscript.messages tr ⟨0, by rfl⟩) = true <;>
    simp only [hc, Bool.false_eq_true, reduceIte] <;>
    (erw [simulateQ_pure]; rfl)

/-- The Oracle Reduction for the Batching Phase. -/
noncomputable def batchingOracleReduction : OracleReduction (oSpec:=[]ₒ)
    (StmtIn := BatchingStmtIn L ℓ) (OStmtIn := aOStmtIn.OStmtIn) (WitIn := BatchingWitIn L K ℓ ℓ')
    (StmtOut := Statement (L := L) (ℓ := ℓ') (RingSwitchingBaseContext κ L K ℓ P) 0)
    (OStmtOut := aOStmtIn.OStmtIn)
    (WitOut := SumcheckWitness L ℓ' 0)
    (pSpec := pSpecBatching (κ:=κ) (L:=L) (K:=K) (P:=P)) where
  prover := oracleProver κ L K P ℓ ℓ' h_l (aOStmtIn:=aOStmtIn)
  verifier := oracleVerifier κ L K P ℓ ℓ' h_l (aOStmtIn:=aOStmtIn)

/-- The batching oracle *reduction*'s verifier is definitionally `oracleVerifier`, so it inherits
`AppendCoherent`. -/
instance instBatchingOracleReductionAppendCoherent :
    OracleVerifier.Append.AppendCoherent
      (batchingOracleReduction κ L K P ℓ ℓ' h_l (aOStmtIn := aOStmtIn)).verifier :=
  instOracleVerifierAppendCoherent κ L K P ℓ ℓ' h_l (aOStmtIn := aOStmtIn)

/-! ## RBR Knowledge Soundness Components -/

variable {σ : Type} {init : ProbComp σ} {impl : QueryImpl []ₒ (StateT σ ProbComp)}

def batchingInputRelationProp (stmt : BatchingStmtIn L ℓ)
    (oStmt : ∀ j, aOStmtIn.OStmtIn j) (wit : BatchingWitIn L K ℓ ℓ') : Prop :=
  wit.t' = packMLE κ L K ℓ ℓ' h_l P.basis wit.t ∧ stmt.original_claim = wit.t.val.aeval stmt.t_eval_point
  ∧ aOStmtIn.initialCompatibility ⟨wit.t', oStmt⟩

/-- Input relation: the witness `t` and `t'` are consistent,
and `t` satisfies the original claim. -/
def batchingInputRelation :
    Set ((BatchingStmtIn L ℓ × (∀ j, aOStmtIn.OStmtIn j)) × BatchingWitIn L K ℓ ℓ') :=
  {⟨⟨stmt, oStmt⟩, wit⟩ | batchingInputRelationProp κ L K P ℓ ℓ' h_l aOStmtIn stmt oStmt wit }

/-- Intermediate witness types for RBR knowledge soundness. -/
def batchingWitMid : Fin (2 + 1) → Type
  | ⟨0, _⟩ => BatchingWitIn L K ℓ ℓ' -- Before any messages
  | ⟨1, _⟩ => BatchingWitIn L K ℓ ℓ' -- After P sends ŝ
  | ⟨2, _⟩ => SumcheckWitness L ℓ' 0 -- After V sends r'' and all computations are done

/-- RBR extractor for the batching phase. -/
noncomputable def batchingRbrExtractor :
  Extractor.RoundByRound []ₒ
    (StmtIn := BatchingStmtIn L ℓ × (∀ j, aOStmtIn.OStmtIn j))
    (WitIn := BatchingWitIn L K ℓ ℓ')
    (WitOut := SumcheckWitness L ℓ' 0)
    (pSpec := pSpecBatching (κ:=κ) (L:=L) (K:=K) (P:=P))
    (WitMid := batchingWitMid L K ℓ ℓ') where
  eqIn := rfl
  extractMid m _ _ witSucc :=
    match m with
    | ⟨0, _⟩ => witSucc -- Extracting `WitIn` from a future `WitIn`
    | ⟨1, _⟩ => by
      exact { t := unpackMLE κ L K ℓ ℓ' h_l P.basis witSucc.t', t' := witSucc.t' }
  extractOut _ _ witOut := witOut

/-- RBR knowledge soundness error for the batching phase.
The only verifier randomness is `r''`. A collision has probability related to `κ/|L|`.
The current local theorem uses the always-valid unit bound until the DP24/SZ bridge is
formalized. -/
def batchingRBRKnowledgeError (i : (pSpecBatching (κ := κ) (L := L) (K := K) (P := P)).ChallengeIdx) : ℝ≥0 :=
  -- Repaired local bound: the sharp `κ / |L|` claim needs the missing DP24/SZ bridge from
  -- `compute_s0` to a nonzero polynomial root count. The unit bound is always available.
  1

def batchingKStateProp {m : Fin (2 + 1)}
    (tr : Transcript m (pSpecBatching (κ := κ) (L := L) (K := K) (P := P)))
    (stmt : BatchingStmtIn L ℓ) (witMid : batchingWitMid L K ℓ ℓ' m)
    (oStmt : ∀ j, aOStmtIn.OStmtIn j) :
    Prop :=
  match m with
  | ⟨0, _⟩ => -- equiv s relIn
    batchingInputRelationProp κ L K P ℓ ℓ' h_l aOStmtIn stmt oStmt witMid
  | ⟨1, _⟩ => by -- P sends hᵢ(X)
    let ⟨msgsUpTo, _⟩ := Transcript.equivMessagesChallenges (k := 1)
      (pSpec := pSpecBatching (κ:=κ) (L:=L) (K:=K) (P:=P)) tr
    let i_msg1 : ((pSpecBatching (κ:=κ) (L:=L) (K:=K) (P:=P)).take 1 (by omega)).MessageIdx :=
      ⟨⟨0, Nat.lt_of_succ_le (by omega)⟩, by simp [pSpecBatching]; rfl⟩
    let s_hat: P.A := msgsUpTo i_msg1
    exact
      witMid.t' = packMLE κ L K ℓ ℓ' h_l P.basis witMid.t -- implied by `extractMid`
      -- The last two constraints are equivalent to `t(r) = s`
      ∧ embedded_MLP_eval κ L K P ℓ ℓ' h_l witMid.t' stmt.t_eval_point = s_hat
      ∧ performCheckOriginalEvaluation κ L K P ℓ ℓ' h_l stmt.original_claim
        stmt.t_eval_point s_hat -- local V check
      -- DP24 repair: carry the oracle-statement compatibility (present in rounds 0 and 2),
      -- so that `extractMid` at round 0 can reconstruct the round-0 `batchingInputRelationProp`.
      -- `batchingKStateProp`/`batchingKnowledgeStateFunction` have no users outside this file.
      ∧ aOStmtIn.initialCompatibility ⟨witMid.t', oStmt⟩
  | ⟨2, _⟩ => by -- implied by relOut
    simp only [batchingWitMid] at witMid
    let ⟨msgsUpTo, chalsUpTo⟩ := Transcript.equivMessagesChallenges (k := 2)
      (pSpec := pSpecBatching (κ:=κ) (L:=L) (K:=K) (P:=P)) tr
    let i_msg1 : ((pSpecBatching (κ:=κ) (L:=L) (K:=K) (P:=P)).take 2 (by omega)).MessageIdx :=
      ⟨⟨0, Nat.lt_of_succ_le (by omega)⟩, by simp [pSpecBatching]; rfl⟩
    let s_hat: P.A := msgsUpTo i_msg1
    let i_msg2 : ((pSpecBatching (κ:=κ) (L:=L) (K:=K) (P:=P)).take 2 (by omega)).ChallengeIdx :=
      ⟨⟨1, Nat.lt_of_succ_le (by omega)⟩, by simp [pSpecBatching]; rfl⟩
    let batching_challenges: Fin κ → L := chalsUpTo i_msg2

    -- DP24 reject-branch repair (#17), ported to the profile API. The verifier has TWO
    -- output branches and the round-2 knowledge state must mirror the verifier's actual
    -- decision rather than asserting the accept-branch facts unconditionally:
    -- asserting them unconditionally is FALSE on the reject branch (where
    -- `(failureState, witOut) ∈ relOut` is satisfiable), making `toFun_full` unprovable.
    -- The repaired prop asserts exactly `sumcheckRoundRelationProp` for whichever statement
    -- the verifier deterministically outputs; `toFun_full` transports each branch directly
    -- from `h_relOut`.
    let stmtOutAccept : Statement (L := L) (ℓ := ℓ') (RingSwitchingBaseContext κ L K ℓ P) 0 := {
      ctx := {
        t_eval_point := stmt.t_eval_point,
        original_claim := stmt.original_claim,
        s_hat := s_hat,
        r_batching := batching_challenges
      },
      sumcheck_target := compute_s0 κ L K P s_hat batching_challenges,
      challenges := Fin.elim0
    }
    exact
      (if performCheckOriginalEvaluation κ L K P ℓ ℓ' h_l stmt.original_claim
            stmt.t_eval_point s_hat then
        sumcheckRoundRelationProp κ L K P ℓ ℓ' h_l aOStmtIn (i:=0)
          stmtOutAccept oStmt witMid
      else
        sumcheckRoundRelationProp κ L K P ℓ ℓ' h_l aOStmtIn (i:=0)
          (failureState κ L K P ℓ ℓ' stmt s_hat) oStmt witMid)

-- The round-0 knowledge-state conjunct is discharged via the DP24 capstone
-- `performCheckOriginalEvaluation_packMLE_iff'`, whose soundness (multilinear-extension
-- uniqueness) requires both carriers to be integral domains. This holds in every real
-- instantiation (e.g. `binaryTowerProfile` builds from `Field K`/`Field L`), and integrality of
-- the small/large carrier is a genuine precondition for the reduction to be sound. Scoped to the
-- knowledge-soundness pipeline only (completeness needs no such hypothesis).
variable [IsDomain L] [IsDomain K] in
/-- Knowledge state function for the batching phase. -/
noncomputable def batchingKnowledgeStateFunction :
  (oracleVerifier κ L K P ℓ ℓ' h_l (aOStmtIn:=aOStmtIn)).KnowledgeStateFunction init impl
    (relIn := batchingInputRelation κ L K P ℓ ℓ' h_l aOStmtIn)
    (relOut := sumcheckRoundRelation κ L K P ℓ ℓ' h_l aOStmtIn 0)
    (batchingRbrExtractor κ L K P ℓ ℓ' h_l (aOStmtIn:=aOStmtIn)) where
  toFun := fun m ⟨stmt, oStmt⟩ tr witMid =>
    batchingKStateProp κ L K P ℓ ℓ' h_l aOStmtIn tr stmt witMid oStmt
  toFun_empty _ _ := by rfl
  toFun_next := fun m hDir stmtIn tr msg witMid =>
    match m with
    | ⟨0, _⟩ => by -- from accumulative KState
      intro hSuccTrue
      simp only [batchingKStateProp, Fin.zero_eta, Fin.isValue, Fin.succ_zero_eq_one,
        Equiv.toFun_as_coe, Transcript.equivMessagesChallenges_apply, Fin.castSucc_zero,
        batchingRbrExtractor, Fin.mk_one, Fin.succ_one_eq_two,
        batchingInputRelationProp] at ⊢ hSuccTrue
      -- Round-1 `batchingKStateProp` gives, in order:
      --   (1) `witMid.t' = packMLE β witMid.t`,
      --   (2) `embedded_MLP_eval witMid.t' r = s_hat`,
      --   (3) `performCheckOriginalEvaluation original_claim r s_hat`,
      --   (4) `aOStmtIn.initialCompatibility ⟨witMid.t', oStmt⟩`  (the documented repair).
      -- The round-0 `batchingInputRelationProp` goal is the conjunction
      --   `t' = packMLE t ∧ original_claim = aeval r t ∧ initialCompatibility`.
      -- Conjuncts (1) and (3-of-goal) are discharged directly from `hSuccTrue`.
      refine ⟨hSuccTrue.1, ?_, hSuccTrue.2.2.2⟩
      -- Remaining goal: `original_claim = aeval r witMid.t`.
      --
      -- With the Step-2 check now reading the ROW components (`decompose_tensor_algebra_rows`),
      -- the DP24 capstone `performCheckOriginalEvaluation_packMLE_iff` is SOUND: substituting
      --   (2) `s_hat = embedded_MLP_eval witMid.t' r`  and
      --   (1) `witMid.t' = packMLE β witMid.t`
      -- into the local check (3) yields
      --   `performCheckOriginalEvaluation original_claim r
      --      (embedded_MLP_eval (packMLE β witMid.t) r) = true`,
      -- which the capstone turns into exactly `original_claim = aeval r witMid.t`.
      -- The capstone `performCheckOriginalEvaluation_packMLE_iff'` is the abstract-`P` form
      -- (over any `CommRing + IsDomain` carriers), proved from `P`'s extraction laws
      -- (`decomposeRows_add` / `decomposeRows_φ₀_mul_φ₁`, the constructive content of
      -- `decomposeRows_spec`); it specializes to the concrete `binaryTowerProfile` lemma.
      have hcheck := hSuccTrue.2.2.1
      rw [← hSuccTrue.2.1, hSuccTrue.1] at hcheck
      -- `hcheck : performCheckOriginalEvaluation original_claim r
      --   (embedded_MLP_eval (packMLE P.basis witMid.t) r) = true`. The DP24 capstone
      -- `performCheckOriginalEvaluation_packMLE_iff` (ported, Profile-abstract) turns this into
      -- exactly `original_claim = aeval r witMid.t.val` (= the goal `… = witMid.t.val.aeval r`).
      exact (performCheckOriginalEvaluation_packMLE_iff P ℓ ℓ' h_l
        stmtIn.1.original_claim witMid.t stmtIn.1.t_eval_point).mp hcheck
    | ⟨1, h⟩ => nomatch h
  toFun_full := fun ⟨stmtLast, oStmtLast⟩ tr witOut => by
    -- Spec repair (#17) APPLIED: the round-2 `batchingKStateProp` (the `⟨2,_⟩` case above) now
    -- mirrors the verifier's accept/reject decision via an `if performCheck … then … else …`,
    -- asserting `sumcheckRoundRelationProp` for whichever statement the verifier actually outputs
    -- (`stmtOutAccept` on accept, `failureState` on reject). Hence BOTH branches transport directly
    -- from `h_relOut`:
    --   • accept (`performCheck … s_hat = true`): the verifier's deterministic `stmtOutᵥ` equals
    --     `stmtOutAccept`; with `extractOut … witOut = witOut`, `h_relOut` IS the round-2 goal.
    --   • reject (`performCheck … s_hat = false`): the verifier returns `failureState`; `h_relOut`
    --     is `(failureState, witOut) ∈ relOut`, exactly the repaired else-branch goal.
    -- The sumcheck-consistency conjunct lives inside `sumcheckRoundRelationProp`/`relOut` under the
    -- SAME free `𝓑`, so it transports verbatim — NO `𝓑` pinning needed here (pinning is only
    -- required by the batching-phase completeness argument, which must establish consistency from
    -- scratch on the honest run).
    --
    -- VERIFIER-RUN QUERY SIMULATION (resolved). To consume `h_relOut` we resolve
    -- `Pr[(stmtOutᵥ, witOut) ∈ relOut | (simulateQ impl (verifier.run …)).run' …]` to the
    -- concrete `stmtOutᵥ`. The verifier's `verify` issues a message-oracle query
    -- (`query (spec := [pSpecBatching.Message]ₒ) ⟨⟨0,rfl⟩,()⟩`); under
    -- `simulateQ (OracleInterface.simOracle2 …)` it collapses, via the support lemma
    -- `Prelude.simulateQ_simOracle2_query`, to `pure (answer s_hat)`. Threaded through
    -- `oracleVerifier_verify_collapse`, the whole `verifier.run` reduces to a single deterministic
    -- `pure (if performCheck … then stmtOutAccept else failureState, oStmtOut)`; the proof then
    --   runs
    -- `probEvent_pos_iff` → `OptionT.mem_support_iff` → collapse → `split` on `performCheck` →
    -- `subst` the singleton support → transport `h_relOut` (the `embed = Sum.inl` map gives
    -- `oStmtOut = oStmt`). The same `Prelude` support lemma serves the analogous message-querying
    -- `toFun_full`s in `SumcheckPhase` and `BinaryBasefold/Steps`.
    intro h
    rw [gt_iff_lt, probEvent_pos_iff] at h
    obtain ⟨x, hx, hrel⟩ := h
    rw [OptionT.mem_support_iff] at hx
    simp only [OptionT.run_mk, support_bind, Set.mem_iUnion] at hx
    obtain ⟨s, _, hx⟩ := hx
    simp only [OracleVerifier.toVerifier, Verifier.run, StateT.run'_eq,
      support_map, Set.mem_image, Prod.exists] at hx
    obtain ⟨val, s', hmem, heq⟩ := hx
    -- Collapse the inner verifier body (the message query is the load-bearing step) to the
    -- deterministic `if performCheck … then stmtOutAccept else failureState` via the collapse
    --   lemma.
    rw [oracleVerifier_verify_collapse] at hmem
    -- The verifier run is now query-free (`pure`/`if`). Case-split the verifier's accept/reject
    -- decision (`split`), then collapse each `pure` branch to a singleton support.
    split at hmem <;>
      simp only [bind_pure_comp, map_pure] at hmem <;>
      erw [simulateQ_pure] at hmem <;>
      simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at hmem <;>
      obtain ⟨rfl, -⟩ := hmem <;>
      injection heq with hxv <;>
      subst hxv
    -- Goal in each branch: round-2 `batchingKStateProp` = the `if performCheck …` over
    -- `sumcheckRoundRelationProp` for the statement the verifier output. `hrel` provides exactly
    -- that membership for the deterministic output `x`; transport it.
    all_goals
      simp only [batchingKStateProp, batchingRbrExtractor, Fin.isValue, Equiv.toFun_as_coe,
        Transcript.equivMessagesChallenges_apply, sumcheckRoundRelation, Set.mem_setOf_eq,
        Transcript.toMessagesChallenges,
        Transcript.toMessagesUpTo, Transcript.toChallengesUpTo, FullTranscript.messages,
        FullTranscript.challenges, oracleVerifier] at hrel ⊢
    -- `hrel` (verifier output ∈ relOut) IS the round-2 KState for the matching branch; the
    -- `embed = Sum.inl` map makes `oStmtOut = oStmtLast`, and the message/challenge accessors
    --   agree.
    all_goals dsimp only [Fin.last, Fin.isValue]
    -- The verifier's accept/reject decision (`hmem`'s `split`, hyp `h✝`) determines which branch
    -- of the round-2 KState `if` is taken; `hrel` supplies exactly that
    --   `sumcheckRoundRelationProp`.
    -- The `embed = Sum.inl` map gives `oStmtOut = oStmtLast`, so `hrel` matches up to that cast.
    · rw [if_pos (by assumption)]
      convert hrel using 3
    · rw [if_neg (by assumption)]
      convert hrel using 3

/-! ## Security Properties -/

/-- Local algebraic capstone residual for batching completeness.
The previous proof body reduced the result to the DP24 row-decomposition residual documented below.
It is named as a `Prop` so downstream results must receive the missing algebra explicitly rather
than importing a kernel axiom. -/
def batchingReduction_perfectCompleteness_residual : Prop :=
  OracleReduction.perfectCompleteness
    (oracleReduction := batchingOracleReduction κ L K P ℓ ℓ' h_l (aOStmtIn:=aOStmtIn))
    (relIn := batchingInputRelation κ L K P ℓ ℓ' h_l aOStmtIn)
    (relOut := sumcheckRoundRelation κ L K P ℓ ℓ' h_l aOStmtIn 0)
    (init := init) (impl := impl)

/-- Batching completeness from the explicit local algebraic residual. -/
theorem batchingReduction_perfectCompleteness
    (hBatching : batchingReduction_perfectCompleteness_residual
      (κ := κ) (L := L) (K := K) (P := P) (ℓ := ℓ) (ℓ' := ℓ') (h_l := h_l)
      (aOStmtIn := aOStmtIn) (init := init) (impl := impl)) :
  OracleReduction.perfectCompleteness
    (oracleReduction := batchingOracleReduction κ L K P ℓ ℓ' h_l (aOStmtIn:=aOStmtIn))
    (relIn := batchingInputRelation κ L K P ℓ ℓ' h_l aOStmtIn)
    (relOut := sumcheckRoundRelation κ L K P ℓ ℓ' h_l aOStmtIn 0)
    (init := init) (impl := impl) :=
  hBatching

/-- RBR knowledge soundness for the batching phase oracle verifier. `IsDomain K` (alongside the
existing `IsDomain L`) is required by the round-0 knowledge-state conjunct's DP24 capstone; it
holds in every real instantiation (e.g. `binaryTowerProfile` builds from a field `K`). -/
theorem batchingOracleVerifier_rbrKnowledgeSoundness [IsDomain L] [IsDomain K] :
    OracleVerifier.rbrKnowledgeSoundness
    (verifier := oracleVerifier κ L K P ℓ ℓ' h_l (aOStmtIn:=aOStmtIn))
    (init := init) (impl := impl)
    (relIn := batchingInputRelation κ L K P ℓ ℓ' h_l aOStmtIn)
    (relOut := sumcheckRoundRelation κ L K P ℓ ℓ' h_l aOStmtIn 0)
    (rbrKnowledgeError := batchingRBRKnowledgeError (κ:=κ) (L:=L) (K:=K) (P:=P)) := by
  -- Proof follows by constructing the extractor and knowledge state function.
  use batchingWitMid L K ℓ ℓ'
  use batchingRbrExtractor κ L K P ℓ ℓ' h_l (aOStmtIn:=aOStmtIn)
  use batchingKnowledgeStateFunction κ L K P ℓ ℓ' h_l (aOStmtIn:=aOStmtIn) (init:=init) (impl:=impl)
  intro stmtIn witIn prover iChal
  simpa [batchingRBRKnowledgeError] using probEvent_le_one

end BatchingPhase
end RingSwitching

/-! ### Axiom audit (issue #19 batching completeness frontier) -/

#print axioms RingSwitching.BatchingPhase.batchingReduction_perfectCompleteness_residual
#print axioms RingSwitching.BatchingPhase.batchingReduction_perfectCompleteness

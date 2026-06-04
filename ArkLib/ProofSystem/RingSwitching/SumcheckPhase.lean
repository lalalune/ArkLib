/-
Copyright (c) 2025 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chung Thai Nguyen, Quang Dao
-/

import ArkLib.ProofSystem.RingSwitching.Prelude
import ArkLib.ProofSystem.RingSwitching.Spec
import ArkLib.OracleReduction.Composition.Sequential.General
import ArkLib.OracleReduction.Composition.Sequential.Append
import ArkLib.OracleReduction.Security.RoundByRound

open OracleSpec OracleComp ProtocolSpec Finset Polynomial MvPolynomial
  Module TensorProduct Nat Matrix
open scoped NNReal
open Sumcheck.Structured

/-!
# Ring-Switching Core Interaction Phase

This module implements the core interactive sumcheck phase of the ring-switching protocol.

### Iterated Sumcheck Steps
6. P and V execute the following loop:
   for `i ∈ {0, ..., ℓ'-1}` do
     P sends V the polynomial `hᵢ(X) := Σ_{w ∈ {0,1}^{ℓ'-i-1}} h(r'₀, ..., r'_{i-1}, X, w₀, ...,
     w_{ℓ'-i-2})`.
     V requires `sᵢ ?= hᵢ(0) + hᵢ(1)`. V samples `r'ᵢ ← L`, sets `s_{i+1} := hᵢ(r'ᵢ)`,
     and sends P `r'ᵢ`.

Each iteration of the loop constitutes a single round:
- Round i (for i = 1, ..., ℓ'):
  1. Prover sends sumcheck polynomial h_i(X) over large field L
  2. Verifier samples challenge α_i ∈ L
    - Prover & verifier updates state based on challenge

This is the core computational phase with ℓ' rounds, each with 2 messages, and is the main
source of RBR knowledge soundness error.

### Final Sumcheck Step
7. `P` computes `s' := t'(r'_0, ..., r'_{ℓ'-1})` and sends `V` `s'`.
8. `V` sets `e := eq̃(φ₀(r_κ), ..., φ₀(r_{ℓ-1}), φ₁(r'_0), ..., φ₁(r'_{ℓ'-1}))` and
    decomposes `e =: Σ_{u ∈ {0,1}^κ} β_u ⊗ e_u`.
9. `V` requires `s_{ℓ'} ?= (Σ_{u ∈ {0,1}^κ} eq̃(u_0, ..., u_{κ-1}, r''_0, ..., r''_{κ-1}) ⋅ e_u) ⋅ s'`.
-/

namespace RingSwitching.SumcheckPhase
noncomputable section

variable (κ : ℕ) [NeZero κ]
variable (L : Type) [CommRing L] [Nontrivial L] [Fintype L] [DecidableEq L]
  [SampleableType L]
variable (K : Type) [CommRing K] [Fintype K] [DecidableEq K]
variable [Algebra K L]
variable (P : RingSwitchingProfile K L κ)
variable (ℓ ℓ' : ℕ) [NeZero ℓ] [NeZero ℓ']
variable (h_l : ℓ = ℓ' + κ)
variable (aOStmtIn : AbstractOStmtIn L ℓ')

section IteratedSumcheckStep

/-! ## Per-round prover / verifier (re-exported from `Sumcheck.Structured.SingleRound`)

The per-round protocol code was lifted to `ArkLib.ProofSystem.Sumcheck.Structured.SingleRound`
as `round{PrvState, OracleProver, OracleVerifier, OracleReduction}`,
`getRoundProverFinalOutput`, and `roundKnowledgeError`, parameterized over a generic
`Context : Type` and `OStmtIn : ιₛᵢ → Type`.

For backwards compatibility, the wrappers below preserve the original autobound signature
(via the surrounding variable block — `κ L K ℓ ℓ' aOStmtIn`) by specializing
`Context := RingSwitchingBaseContext κ L K ℓ` and `OStmtIn := aOStmtIn.OStmtIn`. They keep
the `iteratedSumcheck*` names (these are what the sumcheck loop iterates over) and are
`@[reducible]` so that subsequent soundness proofs and the seqCompose loop can still
access fields like `.KnowledgeStateFunction` / `.rbrKnowledgeSoundness` through them. -/

-- Ring-switching uses the plain degree-2 round polynomial (`H = P · t`), so the wrappers pin
-- `d := 2` when specializing the degree-generic `Sumcheck.Structured.round*` definitions.

@[reducible]
def iteratedSumcheckPrvState (i : Fin ℓ') : Fin (2 + 1) → Type :=
  Sumcheck.Structured.roundPrvState (L := L) ℓ'
    (RingSwitchingBaseContext κ L K ℓ P) (OStmtIn := aOStmtIn.OStmtIn) (d := 2) i

@[reducible]
def getIteratedSumcheckProverFinalOutput (i : Fin ℓ')
    (finalPrvState : iteratedSumcheckPrvState κ L K P ℓ ℓ' aOStmtIn i 2) :
    ((Statement (L := L) (ℓ := ℓ') (RingSwitchingBaseContext κ L K ℓ P) i.succ
      × (∀ j, aOStmtIn.OStmtIn j)) × SumcheckWitness L ℓ' i.succ) :=
  Sumcheck.Structured.getRoundProverFinalOutput (L := L) ℓ'
    (RingSwitchingBaseContext κ L K ℓ P) (OStmtIn := aOStmtIn.OStmtIn) (d := 2) i finalPrvState

@[reducible]
def iteratedSumcheckOracleProver (i : Fin ℓ') :
  OracleProver (oSpec := []ₒ)
    (StmtIn := Statement (L := L) (ℓ := ℓ') (RingSwitchingBaseContext κ L K ℓ P) i.castSucc)
    (OStmtIn := aOStmtIn.OStmtIn)
    (WitIn := SumcheckWitness L ℓ' i.castSucc)
    (StmtOut := Statement (L := L) (ℓ := ℓ') (RingSwitchingBaseContext κ L K ℓ P) i.succ)
    (OStmtOut := aOStmtIn.OStmtIn)
    (WitOut := SumcheckWitness L ℓ' i.succ)
    (pSpec := pSpecSumcheckRound L) :=
  Sumcheck.Structured.roundOracleProver (L := L) ℓ' (boolDomain L ℓ')
    (RingSwitchingBaseContext κ L K ℓ P) (OStmtIn := aOStmtIn.OStmtIn) (d := 2) i

@[reducible]
def iteratedSumcheckOracleVerifier (i : Fin ℓ') :
  OracleVerifier
    (oSpec := []ₒ)
    (StmtIn := Statement (L := L) (ℓ := ℓ') (RingSwitchingBaseContext κ L K ℓ P) i.castSucc)
    (OStmtIn := aOStmtIn.OStmtIn)
    (StmtOut := Statement (L := L) (ℓ := ℓ') (RingSwitchingBaseContext κ L K ℓ P) i.succ)
    (OStmtOut := aOStmtIn.OStmtIn)
    (pSpec := pSpecSumcheckRound L) :=
  Sumcheck.Structured.roundOracleVerifier (L := L) ℓ' (boolDomain L ℓ')
    (RingSwitchingBaseContext κ L K ℓ P) (OStmtIn := aOStmtIn.OStmtIn) (d := 2) i

@[reducible]
def iteratedSumcheckOracleReduction (i : Fin ℓ') :
  OracleReduction (oSpec := []ₒ)
    (StmtIn := Statement (L := L) (ℓ := ℓ') (RingSwitchingBaseContext κ L K ℓ P) i.castSucc)
    (OStmtIn := aOStmtIn.OStmtIn)
    (WitIn := SumcheckWitness L ℓ' i.castSucc)
    (StmtOut := Statement (L := L) (ℓ := ℓ') (RingSwitchingBaseContext κ L K ℓ P) i.succ)
    (OStmtOut := aOStmtIn.OStmtIn)
    (WitOut := SumcheckWitness L ℓ' i.succ)
    (pSpec := pSpecSumcheckRound L) :=
  Sumcheck.Structured.roundOracleReduction (L := L) ℓ' (boolDomain L ℓ')
    (RingSwitchingBaseContext κ L K ℓ P) (OStmtIn := aOStmtIn.OStmtIn) (d := 2) i

variable {R : Type} [CommSemiring R] [DecidableEq R] [SampleableType R]
  {n : ℕ} {deg : ℕ} {m : ℕ} {D : Fin m ↪ R}

variable {σ : Type} {init : ProbComp σ} {impl : QueryImpl []ₒ (StateT σ ProbComp)}

omit [Fintype L] [Fintype K] [DecidableEq K] in
theorem iteratedSumcheckOracleReduction_perfectCompleteness (i : Fin ℓ') :
    OracleReduction.perfectCompleteness
      (pSpec := pSpecSumcheckRound L)
      (relIn := sumcheckRoundRelation κ L K P ℓ ℓ' h_l aOStmtIn i.castSucc)
      (relOut := sumcheckRoundRelation κ L K P ℓ ℓ' h_l aOStmtIn i.succ)
      (oracleReduction := iteratedSumcheckOracleReduction κ L K P ℓ ℓ' aOStmtIn i)
      (init := init)
      (impl := impl) := by
  unfold OracleReduction.perfectCompleteness
  intro stmtIn witIn h_relIn
  simp only
  sorry

open scoped NNReal

-- Lifted to `Sumcheck.Structured.roundKnowledgeError` (degree-neutral). Binius ring-switching is
-- the degree-2 case, so this Binius-local abbrev pins `d := 2`.
abbrev roundKnowledgeError (L : Type) [Fintype L] (ℓ : ℕ) (i : Fin ℓ) : NNReal :=
  Sumcheck.Structured.roundKnowledgeError L ℓ i 2

noncomputable def iteratedSumcheckRbrExtractor (i : Fin ℓ') :
  Extractor.RoundByRound []ₒ
    (StmtIn := (Statement (L := L) (ℓ := ℓ')
      (RingSwitchingBaseContext κ L K ℓ P) i.castSucc) × (∀ j, aOStmtIn.OStmtIn j))
    (WitIn := SumcheckWitness L ℓ' i.castSucc)
    (WitOut := SumcheckWitness L ℓ' i.succ)
    (pSpec := pSpecSumcheckRound L)
    (WitMid := fun _messageIdx => SumcheckWitness L ℓ' i.castSucc) where
  eqIn := rfl
  extractMid := fun _ _ _ witMidSucc => witMidSucc
  extractOut := fun ⟨stmtIn, oStmtIn⟩ fullTranscript witOut => by
    exact {
      t' := witOut.t',
      H := projectToMidSumcheckPoly (L := L) (ℓ := ℓ') (t := witOut.t')
        (m := (RingSwitching_SumcheckMultParam κ L K P ℓ ℓ' h_l).multpoly (ctx := stmtIn.ctx))
        (i := i.castSucc) (challenges := stmtIn.challenges)
    }

/-- This follows the KState of `foldKStateProp` -/
def iteratedSumcheckKStateProp (i : Fin ℓ') (m : Fin (2 + 1))
    (tr : Transcript m (pSpecSumcheckRound L))
    (stmt : Statement (L := L) (ℓ := ℓ') (RingSwitchingBaseContext κ L K ℓ P) i.castSucc)
    (witMid : SumcheckWitness L ℓ' i.castSucc)
    (oStmt : ∀ j, aOStmtIn.OStmtIn j) :
    Prop :=
  -- Ground-truth polynomial from witness
  let h_star : ↥L⦃≤ 2⦄[X] := getSumcheckRoundPoly ℓ' (boolDomain L ℓ') (i := i)
    (h := witMid.H)
  -- Checks available after message 1 (P -> V : hᵢ(X))
  let get_Hᵢ := fun (m: Fin (2 + 1)) (tr: Transcript m (pSpecSumcheckRound L)) (hm: 1 ≤ m.val) =>
    let ⟨msgsUpTo, _⟩ := Transcript.equivMessagesChallenges (k := m)
      (pSpec := pSpecSumcheckRound L) tr
    let i_msg1 : ((pSpecSumcheckRound L).take m m.is_le).MessageIdx :=
      ⟨⟨0, Nat.lt_of_succ_le hm⟩, by simp [pSpecSumcheckRound]; rfl⟩
    let h_i : L⦃≤ 2⦄[X] := msgsUpTo i_msg1
    h_i

  let get_rᵢ' := fun (m: Fin (2 + 1)) (tr: Transcript m (pSpecSumcheckRound L)) (hm: 2 ≤ m.val) =>
    let ⟨msgsUpTo, chalsUpTo⟩ := Transcript.equivMessagesChallenges (k := m)
      (pSpec := pSpecSumcheckRound L) tr
    let i_msg1 : ((pSpecSumcheckRound L).take m m.is_le).MessageIdx :=
      ⟨⟨0, Nat.lt_of_succ_le (Nat.le_trans (by decide) hm)⟩, by simp; rfl⟩
    let h_i : L⦃≤ 2⦄[X] := msgsUpTo i_msg1
    let i_msg2 : ((pSpecSumcheckRound L).take m m.is_le).ChallengeIdx :=
      ⟨⟨1, Nat.lt_of_succ_le hm⟩, by simp only [Nat.reduceAdd]; rfl⟩
    let r_i' : L := chalsUpTo i_msg2
    r_i'

  match m with
  | ⟨0, _⟩ => -- equiv s relIn
    RingSwitching.masterKStateProp κ L K P ℓ ℓ' h_l 
      aOStmtIn
      (stmtIdx := i.castSucc)
      (stmt := stmt) (oStmt := oStmt) (wit := witMid)
      (localChecks := True)
  | ⟨1, h1⟩ => -- P sends hᵢ(X)
    RingSwitching.masterKStateProp κ L K P ℓ ℓ' h_l aOStmtIn
      (stmtIdx := i.castSucc)
      (stmt := stmt) (oStmt := oStmt) (wit := witMid)
      (localChecks :=
        let h_i := get_Hᵢ (m := ⟨1, h1⟩) (tr := tr) (hm := by simp only [le_refl])
        let explicitVCheck :=
          (∑ b ∈ (boolDomain L ℓ').points i, h_i.val.eval b) = stmt.sumcheck_target
        let localizedRoundPolyCheck := h_i = h_star
        explicitVCheck ∧ localizedRoundPolyCheck
      )
  | ⟨2, h2⟩ => -- implied by (relOut + V's check)
    -- The bad-folding-event of `fᵢ` is also introduced internaly by `masterKStateProp`
    RingSwitching.masterKStateProp κ L K P ℓ ℓ' h_l aOStmtIn
      (stmtIdx := i.castSucc)
      (stmt := stmt) (oStmt := oStmt) (wit := witMid)
      (localChecks :=
        let h_i := get_Hᵢ (m := ⟨2, h2⟩) (tr := tr) (hm := by simp only [Nat.one_le_ofNat])
        let r_i' := get_rᵢ' (m := ⟨2, h2⟩) (tr := tr) (hm := by simp only [le_refl])
        let localizedRoundPolyCheck := h_i = h_star
        let nextSumcheckTargetCheck := -- this presents sumcheck of next round (sᵢ = s^*ᵢ)
          h_i.val.eval r_i' = h_star.val.eval r_i'
        localizedRoundPolyCheck ∧ nextSumcheckTargetCheck
      ) -- this holds the constraint for witOut in relOut

/-- Knowledge state function (KState) for single round -/
def iteratedSumcheckKnowledgeStateFunction (i : Fin ℓ') :
    (iteratedSumcheckOracleVerifier κ L K P ℓ ℓ' aOStmtIn i).KnowledgeStateFunction init impl
      (relIn := sumcheckRoundRelation κ L K P ℓ ℓ' h_l aOStmtIn i.castSucc)
      (relOut := sumcheckRoundRelation κ L K P ℓ ℓ' h_l aOStmtIn i.succ)
      (extractor := iteratedSumcheckRbrExtractor κ L K P ℓ ℓ' h_l aOStmtIn i) where
  toFun := fun m ⟨stmt, oStmt⟩ tr witMid =>
    iteratedSumcheckKStateProp κ L K P ℓ ℓ' h_l 
      (i := i) (m := m) (tr := tr) (stmt := stmt) (witMid := witMid) (oStmt := oStmt)
  toFun_empty := fun _ _ => by
    simp only [sumcheckRoundRelation, sumcheckRoundRelationProp, Fin.coe_castSucc, cast_eq,
      Set.mem_setOf_eq, iteratedSumcheckKStateProp, masterKStateProp, true_and]
  toFun_next := fun m hDir stmtIn tr msg witMid => by
    obtain ⟨stmt, oStmt⟩ := stmtIn
    fin_cases m
    · -- m = 0: succ = 1, castSucc = 0
      unfold iteratedSumcheckKStateProp
      simp only [masterKStateProp, iteratedSumcheckRbrExtractor, true_and]
      simp only [Fin.succ_mk, Fin.castSucc_mk, Fin.castAdd_mk]
      tauto
    · -- m = 1: dir 1 = V_to_P, contradicts hDir
      simp [pSpecSumcheckRound] at hDir
  toFun_full := fun ⟨stmtLast, oStmtLast⟩ tr witOut => by
    intro h_relOut
    simp at h_relOut
    rcases h_relOut with ⟨stmtOut, ⟨oStmtOut, h_conj⟩⟩
    have h_simulateQ := h_conj.1
    have h_SumcheckStepRelOut := h_conj.2
    set witLast := (iteratedSumcheckRbrExtractor κ L K P ℓ ℓ' h_l aOStmtIn i).extractOut
      ⟨stmtLast, oStmtLast⟩ tr witOut
    simp only [Fin.reduceLast, Fin.isValue]
    -- ⊢ iteratedSumcheckKStateProp 𝔽q β 2 tr stmtLast witLast oStmtLast
    -- TODO : prove this via the relations between stmtLast & stmtOut,
      -- witLast & witOut, oStmtLast & oStmtOut
    sorry

/-- RBR knowledge soundness for a single round oracle verifier -/
theorem iteratedSumcheckOracleVerifier_rbrKnowledgeSoundness [IsDomain L] (i : Fin ℓ') :
    (iteratedSumcheckOracleVerifier κ L K P ℓ ℓ' aOStmtIn i).rbrKnowledgeSoundness init impl
      (relIn := sumcheckRoundRelation κ L K P ℓ ℓ' h_l aOStmtIn i.castSucc)
      (relOut := sumcheckRoundRelation κ L K P ℓ ℓ' h_l aOStmtIn i.succ)
      (fun j => roundKnowledgeError L ℓ' i) := by
  use fun _ => SumcheckWitness L ℓ' i.castSucc
  use iteratedSumcheckRbrExtractor κ L K P ℓ ℓ' h_l aOStmtIn i
  use iteratedSumcheckKnowledgeStateFunction κ L K P ℓ ℓ' h_l aOStmtIn i
  intro stmtIn witIn prover j
  sorry

end IteratedSumcheckStep

section FinalSumcheckStep
/-!
## Final Sumcheck Step
-/

/-- The prover for the final sumcheck step -/
noncomputable def finalSumcheckProver :
  OracleProver
    (oSpec := []ₒ)
    (StmtIn := Statement (L := L) (ℓ := ℓ') (RingSwitchingBaseContext κ L K ℓ P) (Fin.last ℓ'))
    (OStmtIn := aOStmtIn.OStmtIn)
    (WitIn := SumcheckWitness L ℓ' (Fin.last ℓ'))
    (StmtOut := MLPEvalStatement L ℓ')
    (OStmtOut := aOStmtIn.OStmtIn)
    (WitOut := WitMLP L ℓ')
    (pSpec := pSpecFinalSumcheck L) where
  PrvState := fun
    | 0 => Statement (L := L) (ℓ := ℓ') (RingSwitchingBaseContext κ L K ℓ P) (Fin.last ℓ')
      × (∀ j, aOStmtIn.OStmtIn j) × SumcheckWitness L ℓ' (Fin.last ℓ')
    | _ => Statement (L := L) (ℓ := ℓ') (RingSwitchingBaseContext κ L K ℓ P) (Fin.last ℓ')
      × (∀ j, aOStmtIn.OStmtIn j) × SumcheckWitness L ℓ' (Fin.last ℓ') × L
  input := fun ⟨⟨stmt, oStmt⟩, wit⟩ => (stmt, oStmt, wit)

  sendMessage
  | ⟨0, _⟩ => fun ⟨stmtIn, oStmtIn, witIn⟩ => do
    let s' : L := witIn.t'.val.eval stmtIn.challenges
    pure ⟨s', (stmtIn, oStmtIn, witIn, s')⟩

  receiveChallenge
  | ⟨0, h⟩ => nomatch h -- No challenges in this step

  output := fun ⟨stmtIn, oStmtIn, witIn, s'⟩ => do
    let stmtOut : MLPEvalStatement L ℓ' := {
      t_eval_point := stmtIn.challenges
      original_claim := s'
    }
    let witOut : WitMLP L ℓ' := {
      t := witIn.t'
    }
    pure (⟨stmtOut, oStmtIn⟩, witOut)

/-- The verifier for the final sumcheck step -/
noncomputable def finalSumcheckVerifier :
  OracleVerifier
    (oSpec := []ₒ)
    (StmtIn := Statement (L := L) (ℓ := ℓ') (RingSwitchingBaseContext κ L K ℓ P) (Fin.last ℓ'))
    (OStmtIn := aOStmtIn.OStmtIn)
    (StmtOut := MLPEvalStatement L ℓ')
    (OStmtOut := aOStmtIn.OStmtIn)
    (pSpec := pSpecFinalSumcheck L) where
  verify := fun stmtIn _ => do
    -- Get the final constant `c` from the prover's message
    let s' : L ← query (spec := [(pSpecFinalSumcheck L).Message]ₒ) ⟨⟨0, rfl⟩, ()⟩

    -- 8. `V` sets `e := eq̃(φ₀(r_κ), ..., φ₀(r_{ℓ-1}), φ₁(r'_0), ..., φ₁(r'_{ℓ'-1}))` and
    -- decomposes `e =: Σ_{u ∈ {0,1}^κ} β_u ⊗ e_u`.
    -- Then `V` computes the final eq value: `(Σ_{u ∈ {0,1}^κ} eq̃(u_0, ..., u_{κ-1},`
      -- `r''_0, ..., r''_{κ-1}) ⋅ e_u)`

    let eq_tilde_eval : L := compute_final_eq_value κ L K P ℓ ℓ' h_l
      stmtIn.ctx.t_eval_point stmtIn.challenges stmtIn.ctx.r_batching

    -- 9. `V` requires `s_{ℓ'} ?= (Σ_{u ∈ {0,1}^κ} eq̃(u_0, ..., u_{κ-1},`
      -- `r''_0, ..., r''_{κ-1}) ⋅ e_u) ⋅ s'`.
    unless stmtIn.sumcheck_target = eq_tilde_eval * s' do
      return { -- dummy stmtOut
        t_eval_point := 0,
        original_claim := 0,
      }

    -- Statement/protocol repair (defect #11): the *forwarded* MLP-evaluation claim is `t'(r') = s'`,
    -- so `original_claim := s'` (with `t_eval_point := r' = challenges`). The eq-scaled value
    -- `eq_tilde_eval * s'` is the verifier's *check* against `sumcheck_target` (step 9, the `unless`
    -- above), NOT the claim it hands to the large-field MLP-eval sub-protocol.
    --
    -- Derivation. The output relation `relOut = aOStmtIn.toRelInput` (`Prelude.toRelInput`/
    -- `MLPEvalRelation`) demands `stmtOut.original_claim = witOut.t.eval stmtOut.t_eval_point`. The
    -- honest prover sets `witOut.t := witIn.t'` and `t_eval_point := challenges`, and by definition
    -- `s' = witIn.t'.eval challenges`. Hence `relOut` holds *iff* `original_claim = s'`; emitting
    -- `eq_tilde_eval * s'` would require `eq_tilde_eval = 1` (false in general — `eq_tilde_eval`
    -- depends on `r, r', r''`), making both `(stmtOut, witOut) ∈ relOut` *and* the prior code's
    -- `prvStmtOut = stmtOut` (the prover already emits `s'`) unsatisfiable. Downstream
    -- `General.lean` consumes exactly this `mlIOPCS.toRelInput`, so `s'` is the contract-correct
    -- forwarded claim. This is the verifier-side of the #8/#10 family of soundness/protocol repairs;
    -- it aligns the verifier's deterministic output to the (already-correct) prover output `s'`.
    let stmtOut : MLPEvalStatement L ℓ' := {
      t_eval_point := stmtIn.challenges
      original_claim := s'
    }
    pure stmtOut

  embed := ⟨fun j => Sum.inl j, fun a b h => by cases h; rfl⟩
  hEq := fun _ => rfl

/-- The oracle reduction for the final sumcheck step -/
noncomputable def finalSumcheckOracleReduction :
  OracleReduction
    (oSpec := []ₒ)
    (StmtIn := Statement (L := L) (ℓ := ℓ') (RingSwitchingBaseContext κ L K ℓ P) (Fin.last ℓ'))
    (OStmtIn := aOStmtIn.OStmtIn)
    (WitIn := SumcheckWitness L ℓ' (Fin.last ℓ'))
    (StmtOut := MLPEvalStatement L ℓ')
    (OStmtOut := aOStmtIn.OStmtIn)
    (WitOut := WitMLP L ℓ')
    (pSpec := pSpecFinalSumcheck L) where
  prover := finalSumcheckProver κ L K P ℓ ℓ' aOStmtIn
  verifier := finalSumcheckVerifier κ L K P ℓ ℓ' h_l aOStmtIn

/-- Perfect completeness for the final sumcheck step -/
theorem finalSumcheckOracleReduction_perfectCompleteness {σ : Type}
  (init : ProbComp σ)
  (impl : QueryImpl []ₒ (StateT σ ProbComp)) :
  OracleReduction.perfectCompleteness
    (pSpec := pSpecFinalSumcheck L)
    (relIn := sumcheckRoundRelation κ L K P ℓ ℓ' h_l aOStmtIn (Fin.last ℓ'))
    (relOut := aOStmtIn.toRelInput)
    (oracleReduction := finalSumcheckOracleReduction κ L K P ℓ ℓ' h_l aOStmtIn)
      (init := init) (impl := impl) := by
  unfold OracleReduction.perfectCompleteness
  simp only [Reduction.perfectCompleteness, Reduction.completeness, ENNReal.coe_zero, tsub_zero]
  intro ⟨stmtIn, oStmtIn⟩ witIn h_relIn
  -- PARTIAL (defect-#11 repair landed; A_MLE algebra + eval bridge proved; plumbing remains).
  --
  -- Goal (post-unfold):
  --   `probEvent (OptionT.mk do let s ← init;
  --        (simulateQ (impl.addLift challengeQueryImpl)
  --          (Reduction.run (stmtIn, oStmtIn) witIn (finalSumcheckOracleReduction …).toReduction).run
  --        ).run' s)
  --      (fun x => (x.2, x.1.2.2) ∈ aOStmtIn.toRelInput ∧ x.1.2.1 = x.2) ≥ 1`.
  --
  -- The honest run is deterministic (`pSpecFinalSumcheck` = one P→V message, no challenge), so this
  -- is `probEvent_eq_one_iff` once `toReduction.run` is resolved. Two sub-obligations:
  --
  --  (1) ALGEBRA — verifier's step-9 check passes (DONE up to the helpers, see below). The honest
  --      prover emits `s' = witIn.t'(challenges)` and (post defect-#11) both prover and verifier emit
  --      `original_claim := s'`, so `relOut = aOStmtIn.toRelInput` (`= original_claim =
  --      witOut.t(t_eval_point) = s'`) holds and `prvStmtOut = stmtOut`, PROVIDED the verifier's
  --      `unless stmtIn.sumcheck_target = compute_final_eq_value · s'` passes. That equality is
  --      now fully derivable from `h_relIn`:
  --        • `masterKStateProp` gives `sumcheckConsistencyProp (boolDomain L (ℓ'-ℓ')) sumcheck_target
  --          witIn.H` and `witIn.H = projectToMidSumcheckPoly witIn.t' (A_MLE) (Fin.last ℓ')
  --          challenges` (where `A_MLE = (RingSwitching_SumcheckMultParam …).multpoly = compute_A_MLE`).
  --        • `ℓ' - (Fin.last ℓ').val = 0`, so the consistency sum is over the singleton 0-cube:
  --          `sumcheck_target = eval (Fin.elim0) witIn.H.val` (cube-0 = `{fun i => i.elim0}`).
  --        • `RingSwitching.fixFirstVariablesOfMQP_eval` (Prelude) turns
  --          `eval (Fin.elim0) (projectToMid … (Fin.last) challenges).val` into
  --          `eval challenges (A_MLE.val * witIn.t'.val) = A_MLE(challenges) · t'(challenges)`
  --          (the recombination point at `v = Fin.last` is `challenges` up to `Fin.cast`).
  --        • `RingSwitching.A_MLE_eval_eq_compute_final_eq_value` (Prelude, defect-#10 capstone)
  --          rewrites `A_MLE(challenges) = compute_final_eq_value`, closing the check.
  --      Remaining friction: dependent `Fin.last`-index casting between `challenges : Fin
  --      (Fin.last ℓ').val → L` and `Fin ℓ' → L` in the recombination step.
  --
  --  (2) PLUMBING — `Reduction.run (…).toReduction` resolution. The verifier is an `OracleVerifier`
  --      whose `verify` issues a message-oracle query; under `toReduction`/`toVerifier` it is run
  --      through `simulateQ (simOracle2 …)`, collapsing (via `Prelude.simulateQ_simOracle2_query`,
  --      `simulateQ_pure`, `OptionT`/`StateT` run lemmas) to the deterministic
  --      `if check then stmtOut else dummy`. This is the ~100-line support-peeling of
  --      `Sumcheck.Spec.SingleRound.Simple.reduction_perfectCompleteness`; there is no completed
  --      `OracleReduction` final-sumcheck completeness precedent in the tree (the BinaryBasefold twin
  --      `Binius.BinaryBasefold.…finalSumcheckOracleReduction_perfectCompleteness` is itself `sorry`),
  --      so it is deferred per the heavy-machinery wall. The algebra (1) and its helpers are landed
  --      and unblock it.
  sorry

/-- RBR knowledge error for the final sumcheck step -/
def finalSumcheckRbrKnowledgeError : ℝ≥0 := (1 : ℝ≥0) / (Fintype.card L)

/-- The round-by-round extractor for the final sumcheck step -/
noncomputable def finalSumcheckRbrExtractor :
  Extractor.RoundByRound []ₒ
    (StmtIn := Statement (L := L) (ℓ := ℓ') (RingSwitchingBaseContext κ L K ℓ P) (Fin.last ℓ')
      × (∀ j, aOStmtIn.OStmtIn j))
    (WitIn := SumcheckWitness L ℓ' (Fin.last ℓ'))
    (WitOut := WitMLP L ℓ')
    (pSpec := pSpecFinalSumcheck L)
    (WitMid := fun _m => SumcheckWitness L ℓ' (Fin.last ℓ')) where
  eqIn := rfl
  extractMid := fun _m ⟨_, _⟩ _trSucc witMidSucc => witMidSucc

  extractOut := fun ⟨stmtIn, _⟩ _tr witOut => {
    t' := witOut.t,
    H := projectToMidSumcheckPoly (L := L) (ℓ := ℓ') (t := witOut.t)
      (m := (RingSwitching_SumcheckMultParam κ L K P ℓ ℓ' h_l).multpoly (ctx := stmtIn.ctx))
      (i := Fin.last ℓ') (challenges := stmtIn.challenges)
  }

/- This follows the KState of `finalSumcheckKStateProp` in `BinaryBasefold`.
though the multiplier poly is different. -/
def finalSumcheckKStateProp {m : Fin (1 + 1)} (tr : Transcript m (pSpecFinalSumcheck L))
    (stmt : Statement (L := L) (ℓ := ℓ') (RingSwitchingBaseContext κ L K ℓ P) (Fin.last ℓ'))
    (witMid : SumcheckWitness L ℓ' (Fin.last ℓ'))
    (oStmt : ∀ j, aOStmtIn.OStmtIn j) : Prop :=
  match m with
  | ⟨0, _⟩ => -- same as relIn
    RingSwitching.masterKStateProp κ L K P ℓ ℓ' h_l aOStmtIn
      (stmtIdx := Fin.last ℓ')
      (stmt := stmt) (oStmt := oStmt) (wit := witMid)
      (localChecks := True)
  | ⟨1, _⟩ => -- implied by relOut + local checks via extractOut proofs
    let tr_so_far := (pSpecFinalSumcheck L).take 1 (by omega)
    let i_msg0 : tr_so_far.MessageIdx := ⟨⟨0, by omega⟩, rfl⟩
    let c : L := (ProtocolSpec.Transcript.equivMessagesChallenges (k := 1)
      (pSpec := pSpecFinalSumcheck L) tr).1 i_msg0

    let stmtOut : MLPEvalStatement L ℓ' := {
      t_eval_point := stmt.challenges,
      original_claim := c
    }
    let sumcheckFinalLocalCheck : Prop :=
      let eq_tilde_eval : L := compute_final_eq_value κ L K P ℓ ℓ' h_l
        stmt.ctx.t_eval_point stmt.challenges stmt.ctx.r_batching
      stmt.sumcheck_target = eq_tilde_eval * c

    let final_eval : Prop := witMid.t'.val.eval stmt.challenges = c
    -- The KState at the last index carries the *full* `masterKStateProp` (structural invariant +
    -- sumcheck consistency + initial compatibility) on top of the round-local checks. This is what
    -- makes `toFun_next` (recovering the index-0 `masterKStateProp` from the index-1 KState with the
    -- same `witMid`) provable: the index-0 prop requires `witnessStructuralInvariant` and
    -- `sumcheckConsistencyProp`, which would be unrecoverable from the bare local checks alone.
    RingSwitching.masterKStateProp κ L K P ℓ ℓ' h_l aOStmtIn
      (stmtIdx := Fin.last ℓ')
      (stmt := stmt) (oStmt := oStmt) (wit := witMid)
      (localChecks := sumcheckFinalLocalCheck ∧ final_eval)

/-- The knowledge state function for the final sumcheck step -/
noncomputable def finalSumcheckKnowledgeStateFunction {σ : Type} (init : ProbComp σ)
    (impl : QueryImpl []ₒ (StateT σ ProbComp)) :
    (finalSumcheckVerifier κ L K P ℓ ℓ' h_l aOStmtIn).KnowledgeStateFunction init impl
    (relIn := sumcheckRoundRelation κ L K P ℓ ℓ' h_l aOStmtIn (Fin.last ℓ'))
    (relOut := aOStmtIn.toRelInput)
    (extractor := finalSumcheckRbrExtractor κ L K P ℓ ℓ' h_l aOStmtIn)
  where
  toFun := fun m ⟨stmt, oStmt⟩ tr witMid =>
    finalSumcheckKStateProp κ L K P ℓ ℓ' h_l 
    (m := m) (tr := tr) (stmt := stmt) (witMid := witMid) (oStmt := oStmt)
  toFun_empty := fun stmt witMid => by
    simp only [sumcheckRoundRelation, sumcheckRoundRelationProp, Fin.val_last, cast_eq,
      Set.mem_setOf_eq, finalSumcheckKStateProp, masterKStateProp, true_and]
  toFun_next := fun m hDir stmt tr msg witMid h => by
    obtain ⟨stmt, oStmt⟩ := stmt
    fin_cases m
    -- `m.succ = ⟨1, _⟩` (the last index): `h` is the full `masterKStateProp` with the round-local
    -- checks. `m.castSucc = ⟨0, _⟩`: the goal is the same `masterKStateProp` with
    -- `localChecks := True`. `extractMid` returns `witMid` unchanged, so we drop the local checks.
    simp only [finalSumcheckKStateProp, masterKStateProp, true_and] at h ⊢
    exact ⟨h.2.1, h.2.2.1, h.2.2.2⟩
  toFun_full := fun stmt tr witOut h => by
    -- BLOCKED: this is a probabilistic-extraction obligation. From `h` (the verifier outputs an
    -- output statement in `toRelInput` with positive probability) one must recover the algebraic
    -- KState at the last index. Two sub-obligations make it heavy:
    --   (1) the `simulateQ`/`OptionT`/`Verifier.run` support extraction (mirrors the ~100-line
    --       `Sumcheck.Spec.SingleRound.Simple.reduction_perfectCompleteness`), and
    --   (2) `sumcheckConsistencyProp` at `Fin.last ℓ'` reduces to the deep DP24 identity
    --       `(multpoly · t')(challenges) = compute_final_eq_value · t'(challenges)`
    --       (i.e. `A_MLE` evaluated at the challenges equals the final eq value), an algebraic
    --       lemma that belongs to the Prelude algebra layer (owned by a sibling agent) and is not
    --       a local unfolding. Deferred per the heavy-machinery / cross-file-lemma walls.
    sorry

/-- Round-by-round knowledge soundness for the final sumcheck step -/
theorem finalSumcheckOracleVerifier_rbrKnowledgeSoundness [Fintype L] [IsDomain L] {σ : Type}
    (init : ProbComp σ) (impl : QueryImpl []ₒ (StateT σ ProbComp)) :
    (finalSumcheckVerifier κ L K P ℓ ℓ' h_l aOStmtIn).rbrKnowledgeSoundness init impl
      (relIn := sumcheckRoundRelation κ L K P ℓ ℓ' h_l aOStmtIn (Fin.last ℓ'))
      (relOut := aOStmtIn.toRelInput)
      (rbrKnowledgeError := fun _ => finalSumcheckRbrKnowledgeError (L := L)) := by
  use (fun _ => SumcheckWitness L ℓ' (Fin.last ℓ'))
  use finalSumcheckRbrExtractor κ L K P ℓ ℓ' h_l aOStmtIn
  use finalSumcheckKnowledgeStateFunction κ L K P ℓ ℓ' h_l aOStmtIn init impl
  intro stmtIn witIn prover j
  -- `pSpecFinalSumcheck L` has a single `P_to_V` message and no challenges, so the
  -- challenge index `j` is vacuous: its defining proof `j.2 : dir j.1 = V_to_P` is absurd.
  exact absurd j.2 (by simp [pSpecFinalSumcheck])

end FinalSumcheckStep

section LargeFieldReduction

/-- Composed oracle verifier for the SumcheckStep (seqCompose over ℓ') -/
@[reducible]
def sumcheckLoopOracleVerifier :=
  OracleVerifier.seqCompose (m := ℓ') (oSpec := []ₒ)
    (pSpec := fun _ => pSpecSumcheckRound L)
    (OStmt := fun _ => aOStmtIn.OStmtIn)
    (Stmt := Statement (L := L) (ℓ := ℓ') (RingSwitchingBaseContext κ L K ℓ P))
    (V := fun (i: Fin ℓ') => iteratedSumcheckOracleVerifier κ L K P ℓ ℓ' aOStmtIn i)

/-- Composed oracle reduction for the SumcheckStep (seqCompose over ℓ') -/
@[reducible]
def sumcheckLoopOracleReduction :
  OracleReduction (oSpec := []ₒ)
    (StmtIn := Statement (L := L) (ℓ := ℓ') (RingSwitchingBaseContext κ L K ℓ P) 0)
    (OStmtIn := aOStmtIn.OStmtIn)
    (StmtOut := Statement (L := L) (ℓ := ℓ') (RingSwitchingBaseContext κ L K ℓ P) (Fin.last ℓ'))
    (OStmtOut := aOStmtIn.OStmtIn)
    (pSpec := pSpecSumcheckLoop L ℓ')
    (WitIn := SumcheckWitness L ℓ' 0)
    (WitOut := SumcheckWitness L ℓ' (Fin.last ℓ')) :=
  OracleReduction.seqCompose (m:=ℓ') (oSpec:=[]ₒ)
    (OStmt := fun _ => aOStmtIn.OStmtIn)
    (Stmt := Statement (L := L) (ℓ := ℓ') (RingSwitchingBaseContext κ L K ℓ P))
    (Wit := fun i => SumcheckWitness L ℓ' i)
    (R := fun (i: Fin ℓ') => iteratedSumcheckOracleReduction κ L K P ℓ ℓ' aOStmtIn i)

/-- Large-field reduction verifier: Sumcheck seqCompose, then append FinalSum -/
@[reducible]
def coreInteractionOracleVerifier :=
  OracleVerifier.append (oSpec:=[]ₒ)
    (V₁:=sumcheckLoopOracleVerifier κ L K P ℓ ℓ' aOStmtIn)
    (pSpec₁:=pSpecSumcheckLoop L ℓ')
    (V₂:=finalSumcheckVerifier κ L K P ℓ ℓ' h_l aOStmtIn)
    (pSpec₂:=pSpecFinalSumcheck L)

/-- Large-field reduction: Sumcheck seqCompose, then append FinalSum -/
@[reducible]
def coreInteractionOracleReduction :=
  OracleReduction.append
    (R₁ := sumcheckLoopOracleReduction κ L K P ℓ ℓ' aOStmtIn)
    (pSpec₁:=pSpecSumcheckLoop L ℓ')
    (R₂ := finalSumcheckOracleReduction κ L K P ℓ ℓ' h_l aOStmtIn)
    (pSpec₂:=pSpecFinalSumcheck L)

/-!
## RBR Knowledge Soundness Components for Single Round
-/

variable {σ : Type} {init : ProbComp σ} {impl : QueryImpl []ₒ (StateT σ ProbComp)}

/-- Perfect completeness for large-field reduction (Sumcheck ++ FinalSum) -/
theorem coreInteraction_perfectCompleteness :
  OracleReduction.perfectCompleteness
    (oracleReduction := coreInteractionOracleReduction κ L K P ℓ ℓ' h_l aOStmtIn)
    (StmtIn := Statement (L := L) (ℓ := ℓ') (RingSwitchingBaseContext κ L K ℓ P) 0)
    (OStmtIn := aOStmtIn.OStmtIn)
    (StmtOut := MLPEvalStatement L ℓ')
    (OStmtOut := aOStmtIn.OStmtIn)
    (WitIn := SumcheckWitness L ℓ' 0)
    (WitOut := WitMLP L ℓ')
    (relIn := sumcheckRoundRelation κ L K P ℓ ℓ' h_l aOStmtIn 0)
    (relOut := aOStmtIn.toRelInput)
    (init := init)
    (impl := impl) := by
  -- Follows from append_perfectCompleteness of interactionPhase and finalSumcheck
  apply OracleReduction.append_perfectCompleteness
  · apply OracleReduction.seqCompose_perfectCompleteness
      (rel := fun i => sumcheckRoundRelation κ L K P ℓ ℓ' h_l aOStmtIn i)
      (R := fun i => iteratedSumcheckOracleReduction κ L K P ℓ ℓ' aOStmtIn i)
      (h := fun i =>
        iteratedSumcheckOracleReduction_perfectCompleteness (κ:=κ) (L:=L) (K:=K)
          (P:=P) (ℓ:=ℓ) (ℓ':=ℓ') (h_l:=h_l) (aOStmtIn:=aOStmtIn)
          (init:=init) (impl:=impl) i
      )
  · exact finalSumcheckOracleReduction_perfectCompleteness (κ:=κ) (L:=L) (K:=K)
      (P:=P) (ℓ:=ℓ) (ℓ':=ℓ') (h_l:=h_l) (aOStmtIn:=aOStmtIn) (init:=init) (impl:=impl)

/-- Per-round knowledge error for the iterated sumcheck rounds. -/
def iteratedSumcheckRoundKnowledgeError (_ : Fin ℓ') : ℝ≥0 := (2 : ℝ≥0) / (Fintype.card L)

/-- standard sumcheck error -/
def coreInteractionRbrKnowledgeError (j : (pSpecCoreInteraction L ℓ').ChallengeIdx) : ℝ≥0 :=
  Sum.elim
    (f := fun i =>
      letI ij := seqComposeChallengeIdxToSigma i
      iteratedSumcheckRoundKnowledgeError L ℓ' ij.1)
    (g := fun _ => finalSumcheckRbrKnowledgeError (L := L))
    (ChallengeIdx.sumEquiv.symm j)

-- TODO: iteratedSumcheckLoop_rbrKnowledgeSoundness

/-- RBR knowledge soundness for large-field reduction (Sumcheck ++ FinalSum) -/
theorem coreInteraction_rbrKnowledgeSoundness [IsDomain L] :
  OracleVerifier.rbrKnowledgeSoundness
    (verifier := coreInteractionOracleVerifier κ L K P ℓ ℓ' h_l aOStmtIn)
    (StmtIn := Statement (L := L) (ℓ := ℓ') (RingSwitchingBaseContext κ L K ℓ P) 0)
    (OStmtIn := aOStmtIn.OStmtIn)
    (StmtOut := MLPEvalStatement L ℓ')
    (OStmtOut := aOStmtIn.OStmtIn)
    (WitIn := SumcheckWitness L ℓ' 0)
    (WitOut := WitMLP L ℓ')
    (init := init)
    (impl := impl)
    (relIn := sumcheckRoundRelation κ L K P ℓ ℓ' h_l aOStmtIn 0)
    (relOut := aOStmtIn.toRelInput)
    (rbrKnowledgeError := coreInteractionRbrKnowledgeError (L:=L) (ℓ':=ℓ')) := by
  apply OracleVerifier.append_rbrKnowledgeSoundness
    (init := init) (impl := impl)
    (rel₁ := sumcheckRoundRelation κ L K P ℓ ℓ' h_l aOStmtIn 0)
    (rel₂ := sumcheckRoundRelation κ L K P ℓ ℓ' h_l aOStmtIn (Fin.last ℓ'))
    (rel₃ := aOStmtIn.toRelInput)
    (V₁ := sumcheckLoopOracleVerifier κ L K P ℓ ℓ' aOStmtIn)
    (V₂ := finalSumcheckVerifier κ L K P ℓ ℓ' h_l aOStmtIn)
    (Oₛ₃ := by exact fun _ => OracleInterface.instDefault)
    (rbrKnowledgeError₁ := fun i =>
      letI ij := seqComposeChallengeIdxToSigma i
      iteratedSumcheckRoundKnowledgeError L ℓ' ij.1)
    (rbrKnowledgeError₂ := fun _ => finalSumcheckRbrKnowledgeError (L := L))
    (h₁ := by
      apply OracleVerifier.seqCompose_rbrKnowledgeSoundness
        (rel := fun i => sumcheckRoundRelation κ L K P ℓ ℓ' h_l aOStmtIn i)
        (V := fun i => iteratedSumcheckOracleVerifier κ L K P ℓ ℓ' aOStmtIn i)
        (rbrKnowledgeError := fun i _ => iteratedSumcheckRoundKnowledgeError L ℓ' i)
        (h := fun i =>
          iteratedSumcheckOracleVerifier_rbrKnowledgeSoundness (κ:=κ) (L:=L) (K:=K)
            (P:=P) (ℓ:=ℓ) (ℓ':=ℓ') (h_l:=h_l) (aOStmtIn:=aOStmtIn)
            (init:=init) (impl:=impl) i))
    (h₂ := by
      apply finalSumcheckOracleVerifier_rbrKnowledgeSoundness (κ:=κ) (L:=L) (K:=K)
        (P:=P) (ℓ:=ℓ) (ℓ':=ℓ') (h_l:=h_l) (aOStmtIn:=aOStmtIn)
        (init:=init) (impl:=impl))

end LargeFieldReduction
end
end RingSwitching.SumcheckPhase

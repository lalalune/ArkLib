/-
Copyright (c) 2025 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chung Thai Nguyen, Quang Dao
-/
import ArkLib.ProofSystem.Binius.BinaryBasefold.Spec

namespace Binius.BinaryBasefold.CoreInteraction
/-!
## Binary Basefold single steps
- **Fold step** :
  P sends V the polynomial `h_i(X) := Σ_{w ∈ B_{ℓ-i-1}} h(r'_0, ..., r'_{i-1}, X, w_0, ...,
  w_{ℓ-i-2})`.
  V requires `s_i ?= h_i(0) + h_i(1)`. V samples `r'_i ← L`, sets `s_{i+1} := h_i(r'_i)`,
  and sends P `r'_i`.
- **Relay step** : transform relOut of fold step in case of non-commitment round to match
  roundRelation
- **Commit step** :
    P defines `f^(i+1): S^(i+1) → L` as the function `fold(f^(i), r'_i)` of Definition 4.6.
    if `i+1 < ℓ` and `ϑ | i+1` then
    P submits (submit, ℓ+R-i-1, f^(i+1)) to the oracle `F_Vec^L`
- **Final sum-check step** :
  - P sends V the final constant `c := f^(ℓ)(0, ..., 0)`
  - V verifies : `s_ℓ = eqTilde(r, r') * c`
  => `c` should be equal to `t(r'_0, ..., r'_{ℓ-1})`
-/
noncomputable section
open OracleSpec OracleComp ProtocolSpec Finset AdditiveNTT Polynomial MvPolynomial
open Binius.BinaryBasefold
open scoped NNReal

variable {r : ℕ} [NeZero r]
variable {L : Type} [Field L] [Fintype L] [DecidableEq L] [CharP L 2]
  [SampleableType L]
variable (𝔽q : Type) [Field 𝔽q] [Fintype 𝔽q] [DecidableEq 𝔽q]
  [h_Fq_char_prime : Fact (Nat.Prime (ringChar 𝔽q))] [hF₂ : Fact (Fintype.card 𝔽q = 2)]
variable [Algebra 𝔽q L]
variable (β : Fin r → L) [hβ_lin_indep : Fact (LinearIndependent 𝔽q β)]
  [h_β₀_eq_1 : Fact (β 0 = 1)]
variable {ℓ 𝓡 ϑ : ℕ} (γ_repetitions : ℕ) [NeZero ℓ] [NeZero 𝓡] [NeZero ϑ] -- Should we allow ℓ = 0?
variable {h_ℓ_add_R_rate : ℓ + 𝓡 < r} -- ℓ ∈ {1, ..., r-1}
variable [hdiv : Fact (ϑ ∣ ℓ)]

section SingleIteratedSteps
variable {Context : Type} {mp : SumcheckMultiplierParam L ℓ Context} -- Sumcheck context
section FoldStep
/-- Most security properties happen at FoldStep, the CommitmentRound is
  just to place the conditional oracle message -/

def foldPrvState (i : Fin ℓ) : Fin (2 + 1) → Type := fun
  -- Initial : current witness x t_eval_point x challenges
  | ⟨0, _⟩ => (Statement (L := L) Context i.castSucc ×
    (∀ j, OracleStatement 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) ϑ i.castSucc j) ×
    Witness (L := L) 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) i.castSucc)
  -- After sending h_i(X)
  | ⟨1, _⟩ => Statement (L := L) Context i.castSucc ×
    (∀ j, OracleStatement 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) ϑ i.castSucc j) ×
    Witness (L := L) 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) i.castSucc × L⦃≤ 2⦄[X]
  -- After receiving r'_i (Note that this covers the last two messages, i.e. after each of them)
  | _ => Statement (L := L) Context i.castSucc ×
    (∀ j, OracleStatement 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) ϑ i.castSucc j) ×
    Witness (L := L) 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) i.castSucc × L⦃≤ 2⦄[X] × L

/-- This is in fact usable immediately after the V->P challenge since all inputs
are available at that time. -/
noncomputable def getFoldProverFinalOutput (i : Fin ℓ)
    (finalPrvState : foldPrvState 𝔽q β (ϑ := ϑ) (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
      i 2 (Context := Context)) :
  ((Statement (L := L) Context i.succ × ((j : Fin (toOutCodewordsCount ℓ ϑ i.castSucc)) →
    OracleStatement 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) ϑ i.castSucc j))
      × Witness (L := L) 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) i.succ)
  := by
  let (stmtIn, oStmtIn, witIn, h_i, r_i') := finalPrvState
  let newSumcheckTarget : L := h_i.val.eval r_i'
  let stmtOut : Statement (L := L) Context i.succ := {
    ctx := stmtIn.ctx,
    sumcheck_target := newSumcheckTarget,
    challenges := Fin.snoc stmtIn.challenges r_i'
  }
  let currentSumcheckPoly : L⦃≤ 2⦄[X Fin (ℓ - i)] := witIn.H
  let f_i : OracleFunction 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
    (i := ⟨i, by omega⟩) := witIn.f
  let challenges : Fin (1) → L := fun cId => r_i'
  let fᵢ_succ := iterated_fold 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
    (steps := ⟨1, by apply Nat.lt_add_of_pos_right_of_le; exact NeZero.one_le⟩)
    (i := ⟨i, by omega⟩)
    (h_i_add_steps := by simp only; apply Nat.lt_add_of_pos_right_of_le; omega)
    f_i challenges
  simp only at fᵢ_succ
  let witOut : Witness (L := L) 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (ℓ := ℓ) i.succ := by
    -- Advance Hᵢ → Hᵢ₊₁ by fixing the first variable to rᵢ'
    let projectedH := projectToNextSumcheckPoly (L := L) (ℓ := ℓ)
      (i := i) (Hᵢ := witIn.H) (rᵢ := r_i')
    exact {
      t := witIn.t,
      H := projectedH,
      f := fᵢ_succ
    }
  have h_succ_val : i.succ.val = i.val + 1 := rfl
  let oStmtOut : ∀ j, OracleStatement 𝔽q β (ϑ := ϑ)
    (h_ℓ_add_R_rate := h_ℓ_add_R_rate) i.castSucc j := oStmtIn
  exact ⟨⟨stmtOut, oStmtOut⟩, witOut⟩

/-- The prover for the `i`-th round of Binary Foldfold. -/
noncomputable def foldOracleProver (i : Fin ℓ) :
  OracleProver (oSpec := []ₒ)
    -- current round
    (StmtIn := Statement (L := L) Context i.castSucc)
    (OStmtIn := OracleStatement 𝔽q β (ϑ := ϑ) (h_ℓ_add_R_rate := h_ℓ_add_R_rate) i.castSucc)
    (WitIn := Witness (L := L) 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (ℓ := ℓ) i.castSucc)
    -- Both stmt and wit advances, but oStmt only advances at the commitment rounds only
    (StmtOut := Statement (L := L) Context i.succ)
    (OStmtOut := OracleStatement 𝔽q β (ϑ := ϑ) (h_ℓ_add_R_rate := h_ℓ_add_R_rate) i.castSucc)
    (WitOut := Witness (L := L) 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (ℓ := ℓ) i.succ)
    (pSpec := pSpecFold (L := L)) where

  PrvState := foldPrvState 𝔽q β (ϑ := ϑ) (h_ℓ_add_R_rate := h_ℓ_add_R_rate) i

  input := fun ⟨⟨stmt, oStmt⟩, wit⟩ => (stmt, oStmt, wit)

  sendMessage -- There are either 2 or 3 messages in the pSpec depending on commitment rounds
  | ⟨0, _⟩ => fun ⟨stmt, oStmt, wit⟩ => do
    let curH : ↥L⦃≤ 2⦄[X Fin (ℓ - ↑i.castSucc)] := wit.H
    let h_i : L⦃≤ 2⦄[X] := by
      exact getSumcheckRoundPoly ℓ (boolDomain L ℓ) (i := i) curH
    pure ⟨h_i, (stmt, oStmt, wit, h_i)⟩
  | ⟨1, _⟩ => by contradiction

  receiveChallenge
  | ⟨0, h⟩ => nomatch h -- i.e. contradiction
  | ⟨1, _⟩ => fun ⟨stmt, oStmt, wit, h_i⟩ => do
    pure (fun r_i' => (stmt, oStmt, wit, h_i, r_i'))
  -- | ⟨2, h⟩ => nomatch h -- no challenge after third message

  -- output : PrvState → StmtOut × (∀i, OracleStatement i) × WitOut
  output := fun finalPrvState =>
    let res := getFoldProverFinalOutput 𝔽q β (ϑ := ϑ)
      (h_ℓ_add_R_rate := h_ℓ_add_R_rate) i finalPrvState
    pure res

/-- The oracle verifier for the `i`-th round of Binary Foldfold. -/
noncomputable def foldOracleVerifier (i : Fin ℓ) :
  OracleVerifier
    (oSpec := []ₒ)
    (StmtIn := Statement (L := L) Context i.castSucc)
    (OStmtIn := OracleStatement 𝔽q β (ϑ := ϑ)
      (h_ℓ_add_R_rate := h_ℓ_add_R_rate) i.castSucc)
    (Oₘ := fun i => by infer_instance)
    -- next round
    (StmtOut := Statement (L := L) Context i.succ)
    (OStmtOut := OracleStatement 𝔽q β (ϑ := ϑ)
      (h_ℓ_add_R_rate := h_ℓ_add_R_rate) i.castSucc)
    (pSpec := pSpecFold (L := L)) where

  -- The core verification logic. Takes the input statement `stmtIn` and the transcript, and
  -- performs an oracle computation that outputs a new statement
  verify := fun stmtIn pSpecChallenges => do
    -- Message 0 : Receive h_i(X) from prover
    let h_i : L⦃≤ 2⦄[X] ← query (spec := [(pSpecFold (L := L)).Message]ₒ)
      ⟨⟨0, rfl⟩, ()⟩

    -- Check sumcheck : s_i ?= h_i((0 : L)) + h_i((1 : L)), i.e. ∑_{y ∈ univ.map (boolEmbedding L)} h_i(y)
    -- (matching how the prover sums the round poly over `univ.map (boolEmbedding L)`, not literal `0`/`1`).
    let sumcheck_check := h_i.val.eval ((0 : L)) + h_i.val.eval ((1 : L)) = stmtIn.sumcheck_target
    unless sumcheck_check do
      -- Return a dummy statement indicating failure
      let dummyStmt : Statement (L := L) Context i.succ := {
        ctx := stmtIn.ctx,
        sumcheck_target := 0,
        challenges := Fin.snoc stmtIn.challenges 0
      }
      return dummyStmt

    -- Message 1 : Sample challenge r'_i and send to prover
    let r_i' : L := pSpecChallenges ⟨1, rfl⟩ -- This gets the challenge for message 1

    -- Update statement for next round
    let stmtOut : Statement (L := L) Context i.succ := {
      ctx := stmtIn.ctx,
      sumcheck_target := h_i.val.eval r_i',
      challenges := Fin.snoc stmtIn.challenges r_i'
    }

    pure stmtOut
  embed := ⟨fun j => by
    if hj : j.val < toOutCodewordsCount ℓ ϑ i.castSucc then
      exact Sum.inl ⟨j.val, by omega⟩
    else omega -- never happens
  , by
    intro a b h_ab_eq
    simp only [MessageIdx, Fin.is_lt, ↓reduceDIte, Fin.eta, Sum.inl.injEq] at h_ab_eq
    exact h_ab_eq
  ⟩
  hEq := fun oracleIdx => by
    simp only [MessageIdx, Fin.is_lt, ↓reduceDIte, Fin.eta, Function.Embedding.coeFn_mk]

/-- The oracle reduction that is the `i`-th round of Binary Foldfold. -/
noncomputable def foldOracleReduction (i : Fin ℓ) :
  OracleReduction (oSpec := []ₒ)
    (StmtIn := Statement (L := L) Context i.castSucc)
    (OStmtIn := OracleStatement 𝔽q β (ϑ := ϑ)
      (h_ℓ_add_R_rate := h_ℓ_add_R_rate) i.castSucc)
    (WitIn := Witness (L := L) 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) i.castSucc)
    (StmtOut := Statement (L := L) Context i.succ)
    (OStmtOut := OracleStatement 𝔽q β (ϑ := ϑ)
      (h_ℓ_add_R_rate := h_ℓ_add_R_rate) i.castSucc)
    (WitOut := Witness (L := L) 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) i.succ)
    (pSpec := pSpecFold (L := L)) where
  prover := foldOracleProver 𝔽q β (ϑ := ϑ) (h_ℓ_add_R_rate := h_ℓ_add_R_rate) i
  verifier := foldOracleVerifier 𝔽q β (ϑ := ϑ) (h_ℓ_add_R_rate := h_ℓ_add_R_rate) i

/-- The fold-step oracle verifier routes every output oracle to the unchanged input oracle (`embed`
maps `j ↦ Sum.inl ⟨j.val,_⟩`, `OStmtIn = OStmtOut`, `hEq` by `simp`) and exposes no message oracle,
so its `AppendCoherent` coherence holds by `rfl` after resolving the `embed` `dite`. -/
instance instFoldOracleVerifierAppendCoherent (i : Fin ℓ) :
    OracleVerifier.Append.AppendCoherent
      (foldOracleVerifier 𝔽q β (ϑ := ϑ) (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (Context := Context) i) where
  hCohInl := fun a k h => by
    simp only [foldOracleVerifier, Function.Embedding.coeFn_mk] at h
    split_ifs at h with hj
    · obtain rfl := Sum.inl.inj h; rfl
    · exact absurd a.isLt (by simpa [toOutCodewordsCount] using hj)
  hCohInr := fun a k h => by
    simp only [foldOracleVerifier, Function.Embedding.coeFn_mk] at h
    split_ifs at h with hj
    exact absurd a.isLt (by simpa [toOutCodewordsCount] using hj)

instance instFoldOracleReductionAppendCoherent (i : Fin ℓ) :
    OracleVerifier.Append.AppendCoherent
      (foldOracleReduction 𝔽q β (ϑ := ϑ) (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (Context := Context) i).verifier :=
  instFoldOracleVerifierAppendCoherent 𝔽q β (ϑ := ϑ) (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (Context := Context) i

variable {R : Type} [CommSemiring R] [DecidableEq R] [SampleableType R]
  {n : ℕ} {deg : ℕ} {m : ℕ} {D : Fin m ↪ R}

variable {σ : Type} {init : ProbComp σ} {impl : QueryImpl []ₒ (StateT σ ProbComp)}

theorem foldOracleReduction_perfectCompleteness (i : Fin ℓ) :
    OracleReduction.perfectCompleteness
      (pSpec := pSpecFold (L := L))
      (relIn := roundRelation 𝔽q β (ϑ := ϑ) (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
         i.castSucc (mp := mp))
      (relOut := foldStepRelOut 𝔽q β (ϑ := ϑ) (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
         i (mp := mp))
      (oracleReduction := foldOracleReduction 𝔽q β (ϑ := ϑ)
        (h_ℓ_add_R_rate := h_ℓ_add_R_rate) i)
      (init := init)
      (impl := impl) := by
  unfold OracleReduction.perfectCompleteness
  intro stmtIn witIn h_relIn
  simp only
  sorry

open scoped NNReal

open Classical in
/-- Definition of the per-round RBR KS error for Binary FoldFold.
This combines the Sumcheck error (1/|L|) and the LDT Bad Event probability.
For round i : rbrKnowledgeError(i) = err_SC + err_BE where
- err_SC = 1/|L| (Schwartz-Zippel for degree 1)
- err_BE = (if ϑ ∣ (i + 1) then ϑ * |S^(i+1)| / |L| else 0)
  where k = i / ϑ and |S^(j)| is the size of the j-th domain
-/
def foldKnowledgeError (i : Fin ℓ) (_ : (pSpecFold (L := L)).ChallengeIdx) : ℝ≥0 :=
  let err_SC := (1 : ℝ≥0) / (Fintype.card L)
  -- bad event of `fⱼ` exists RIGHT AFTER the V's challenge of sumcheck round `j+ϑ-1`,
  let err_BE := if hi : ϑ ∣ (i.val + 1) then
    -- HERE: we view `i` as `j+ϑ-1`, error rate is `ϑ * |S^(j+ϑ)| / |L| = ϑ * |S^(i+1)| / |L|`
    ϑ * (Fintype.card ((sDomain 𝔽q β h_ℓ_add_R_rate)
      ⟨i.val + 1, by -- ⊢ ↑i + 1 < r
        omega⟩) : ℝ≥0) / (Fintype.card L)
  else 0
  err_SC + err_BE

/-- The round-by-round extractor for a single round.
Since f^(0) is always available, we can invoke the extractMLP function directly. -/
noncomputable def foldRbrExtractor (i : Fin ℓ) :
  Extractor.RoundByRound []ₒ
    (StmtIn := (Statement (L := L) Context i.castSucc) × (∀ j,
      OracleStatement 𝔽q β (ϑ := ϑ) (h_ℓ_add_R_rate := h_ℓ_add_R_rate) i.castSucc j))
    (WitIn := Witness (L := L) 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) i.castSucc)
    (WitOut := Witness (L := L) 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) i.succ)
    (pSpec := pSpecFold (L := L))
    (WitMid := fun _messageIdx => Witness (L := L) 𝔽q β
      (h_ℓ_add_R_rate := h_ℓ_add_R_rate) i.castSucc) where
  eqIn := rfl
  extractMid := fun _ _ _ witMidSucc => witMidSucc
  extractOut := fun ⟨stmtIn, oStmtIn⟩ fullTranscript witOut => by
    exact {
      t := witOut.t,
      H :=
        projectToMidSumcheckPoly (L := L) (ℓ := ℓ)
          (t := witOut.t) (m := mp.multpoly stmtIn.ctx)
          (i := i.castSucc) (challenges := stmtIn.challenges),
      f := getMidCodewords 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) witOut.t
        (challenges := stmtIn.challenges)
    }

/-- This follows the KState of sum-check -/
def foldKStateProp {i : Fin ℓ} (m : Fin (2 + 1))
    (tr : Transcript m (pSpecFold (L := L))) (stmt : Statement (L := L) Context i.castSucc)
    (witMid : Witness (L := L) 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) i.castSucc)
    (oStmt : ∀ j, OracleStatement 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) ϑ i.castSucc j) :
    Prop :=
  -- Ground-truth polynomial from witness
  let h_star : ↥L⦃≤ 2⦄[X] := getSumcheckRoundPoly ℓ (boolDomain L ℓ) (i := i)
    (h := witMid.H)
  -- Checks available after message 1 (P -> V : hᵢ(X))
  let get_Hᵢ := fun (m: Fin (2 + 1)) (tr: Transcript m pSpecFold) (hm: 1 ≤ m.val) =>
    let ⟨msgsUpTo, _⟩ := Transcript.equivMessagesChallenges (k := m)
      (pSpec := pSpecFold (L := L)) tr
    let i_msg1 : ((pSpecFold (L := L)).take m m.is_le).MessageIdx :=
      ⟨⟨0, Nat.lt_of_succ_le hm⟩, by simp [pSpecFold]; rfl⟩
    let h_i : L⦃≤ 2⦄[X] := msgsUpTo i_msg1
    h_i

  let get_rᵢ' := fun (m: Fin (2 + 1)) (tr: Transcript m pSpecFold) (hm: 2 ≤ m.val) =>
    let ⟨msgsUpTo, chalsUpTo⟩ := Transcript.equivMessagesChallenges (k := m)
      (pSpec := pSpecFold (L := L)) tr
    let i_msg1 : ((pSpecFold (L := L)).take m m.is_le).MessageIdx :=
      ⟨⟨0, Nat.lt_of_succ_le (Nat.le_trans (by decide) hm)⟩, by simp; rfl⟩
    let h_i : L⦃≤ 2⦄[X] := msgsUpTo i_msg1
    let i_msg2 : ((pSpecFold (L := L)).take m m.is_le).ChallengeIdx :=
      ⟨⟨1, Nat.lt_of_succ_le hm⟩, by simp only [Nat.reduceAdd]; rfl⟩
    let r_i' : L := chalsUpTo i_msg2
    r_i'

  match m with
  | ⟨0, _⟩ => -- equiv s relIn
    masterKStateProp (mp := mp) 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) 
      (stmtIdx := i.castSucc) (oracleIdx := i.castSucc)
      (h_le := le_refl _)
      (stmt := stmt) (wit := witMid) (oStmt := oStmt)
      (localChecks := True)
  | ⟨1, h1⟩ => -- P sends hᵢ(X)
    masterKStateProp (mp := mp) 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) 
      (stmtIdx := i.castSucc) (oracleIdx := i.castSucc)
      (h_le := le_refl _)
      (stmt := stmt) (wit := witMid) (oStmt := oStmt)
      (localChecks :=
        let h_i := get_Hᵢ (m := ⟨1, h1⟩) (tr := tr) (hm := by simp only [le_refl])
        let explicitVCheck := h_i.val.eval ((0 : L)) + h_i.val.eval ((1 : L)) = stmt.sumcheck_target
        let localizedRoundPolyCheck := h_i = h_star
        explicitVCheck ∧ localizedRoundPolyCheck
      )
  | ⟨2, h2⟩ => -- implied by (relOut + V's check)
    -- The bad-folding-event of `fᵢ` is also introduced internaly by `masterKStateProp`
    masterKStateProp (mp := mp) 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) 
      (stmtIdx := i.castSucc) (oracleIdx := i.castSucc)
      (h_le := le_refl _)
      (stmt := stmt) (wit := witMid) (oStmt := oStmt)
      (localChecks :=
        let h_i := get_Hᵢ (m := ⟨2, h2⟩) (tr := tr) (hm := by simp only [Nat.one_le_ofNat])
        let r_i' := get_rᵢ' (m := ⟨2, h2⟩) (tr := tr) (hm := by simp only [le_refl])
        let localizedRoundPolyCheck := h_i = h_star
        let nextSumcheckTargetCheck := -- this presents sumcheck of next round (sᵢ = s^*ᵢ)
          h_i.val.eval r_i' = h_star.val.eval r_i'
        localizedRoundPolyCheck ∧ nextSumcheckTargetCheck
      ) -- this holds the constraint for witOut in relOut

-- Note: this fold step couldn't carry bad-event errors, because we don't have oracles yet.

/-- Knowledge state function (KState) for single round -/
def foldKnowledgeStateFunction (i : Fin ℓ) :
    (foldOracleVerifier 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) i).KnowledgeStateFunction
      init impl
      (relIn := roundRelation (mp := mp) 𝔽q β (ϑ := ϑ) (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
         i.castSucc)
      (relOut := foldStepRelOut (mp := mp) 𝔽q β (ϑ := ϑ) (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
         i)
      (extractor := foldRbrExtractor (mp:=mp) 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) i) where
  toFun := fun m ⟨stmt, oStmt⟩ tr witMid =>
    foldKStateProp (mp:=mp) 𝔽q β (ϑ := ϑ) (h_ℓ_add_R_rate := h_ℓ_add_R_rate) 
      (i := i) (m := m) (tr := tr) (stmt := stmt) (witMid := witMid) (oStmt := oStmt)
  toFun_empty := fun _ _ => by rfl
  toFun_next := fun m hDir stmtIn tr msg witMid => by
    obtain ⟨stmt, oStmt⟩ := stmtIn
    fin_cases m
    · exact fun ⟨_, h⟩ => ⟨trivial, h⟩
    · simp at hDir
  toFun_full := fun ⟨stmtLast, oStmtLast⟩ tr witOut h_relOut => by
    simp at h_relOut
    rcases h_relOut with ⟨stmtOut, ⟨oStmtOut, h_conj⟩⟩
    have h_simulateQ := h_conj.1
    have h_foldStepRelOut := h_conj.2
    set witLast := (foldRbrExtractor (mp:=mp) 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) i).extractOut
      ⟨stmtLast, oStmtLast⟩ tr witOut
    simp only [Fin.reduceLast, Fin.isValue]
    -- ⊢ foldKStateProp 𝔽q β 2 tr stmtLast witLast oStmtLast
    -- TODO : prove this via the relations between stmtLast & stmtOut,
      -- witLast & witOut, oStmtLast & oStmtOut
    have h_oStmt : oStmtLast = oStmtOut := by sorry
    sorry

/-- RBR knowledge soundness for a single round oracle verifier -/
theorem foldOracleVerifier_rbrKnowledgeSoundness (i : Fin ℓ) :
    (foldOracleVerifier 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) i).rbrKnowledgeSoundness
      init impl
      (relIn := roundRelation (mp := mp) 𝔽q β (ϑ := ϑ) (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
         i.castSucc)
      (relOut := foldStepRelOut (mp := mp) 𝔽q β (ϑ := ϑ) (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
         i)
      (foldKnowledgeError 𝔽q β (ϑ := ϑ) (h_ℓ_add_R_rate := h_ℓ_add_R_rate) i) := by
  use fun _ => Witness (L := L) 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) i.castSucc
  use foldRbrExtractor (mp:=mp) 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) i
  use foldKnowledgeStateFunction (mp:=mp) 𝔽q β (ϑ := ϑ)
    (h_ℓ_add_R_rate := h_ℓ_add_R_rate) i
  intro stmtIn witIn prover j
  sorry

end FoldStep
section CommitStep
/- the CommitStep is a 1-message oracle reduction to place the conditional oracle message -/

def commitPrvState (i : Fin ℓ) : Fin (1 + 1) → Type := fun
  | ⟨0, _⟩ => Statement (L := L) Context i.succ ×
    (∀ j, OracleStatement 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) ϑ i.castSucc j) ×
    Witness (L := L) 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) i.succ
  | ⟨1, _⟩ => Statement (L := L) Context i.succ ×
    (∀ j, OracleStatement 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) ϑ i.succ j) ×
    Witness (L := L) 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) i.succ

def getCommitProverFinalOutput (i : Fin ℓ)
    (inputPrvState : commitPrvState (Context := Context) 𝔽q β (ϑ := ϑ)
      (h_ℓ_add_R_rate := h_ℓ_add_R_rate) i 0) :
  (↥(sDomain 𝔽q β h_ℓ_add_R_rate ⟨↑i + 1, by omega⟩) → L) ×
  commitPrvState (Context := Context) 𝔽q β (ϑ := ϑ) (h_ℓ_add_R_rate := h_ℓ_add_R_rate) i 1 :=
  let (stmt, oStmtIn, wit) := inputPrvState
  let fᵢ_succ := wit.f
  let oStmtOut := snoc_oracle 𝔽q β (ϑ := ϑ) (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
    oStmtIn fᵢ_succ -- The only thing the prover does is to sends f_{i+1} as an oracle
  (fᵢ_succ, (stmt, oStmtOut, wit))

/-- The prover for the `i`-th round of Binary commitmentfold. -/
noncomputable def commitOracleProver (i : Fin ℓ) :
  OracleProver (oSpec := []ₒ)
    -- current round
    (StmtIn := Statement (L := L) Context i.succ)
    (OStmtIn := OracleStatement 𝔽q β (ϑ := ϑ)
      (h_ℓ_add_R_rate := h_ℓ_add_R_rate) i.castSucc)
    (WitIn := Witness (L := L) 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (ℓ := ℓ) i.succ)
    (StmtOut := Statement (L := L) Context i.succ)
    (OStmtOut := OracleStatement 𝔽q β (ϑ := ϑ)
      (h_ℓ_add_R_rate := h_ℓ_add_R_rate) i.succ)
    (WitOut := Witness (L := L) 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (ℓ := ℓ) i.succ)
    (pSpec := pSpecCommit 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) i) where

  PrvState := commitPrvState 𝔽q β (ϑ := ϑ) (h_ℓ_add_R_rate := h_ℓ_add_R_rate) i

  input := fun ⟨⟨stmt, oStmt⟩, wit⟩ => (stmt, oStmt, wit)

  sendMessage -- There are either 2 or 3 messages in the pSpec depending on commitment rounds
  | ⟨0, _⟩ => fun inputPrvState => by
    let res := getCommitProverFinalOutput 𝔽q β (ϑ := ϑ)
      (h_ℓ_add_R_rate := h_ℓ_add_R_rate) i inputPrvState
    exact pure res

  receiveChallenge
  | ⟨0, h⟩ => nomatch h -- i.e. contradiction

  output := fun ⟨stmt, oStmt, wit⟩ => by
    exact pure ⟨⟨stmt, oStmt⟩, wit⟩

/-- The oracle verifier for the `i`-th round of Binary commitmentfold. -/
noncomputable def commitOracleVerifier (i : Fin ℓ) (hCR : isCommitmentRound ℓ ϑ i) :
  OracleVerifier
    (oSpec := []ₒ)
    (StmtIn := Statement (L := L) Context i.succ)
    (OStmtIn := OracleStatement 𝔽q β (ϑ := ϑ)
      (h_ℓ_add_R_rate := h_ℓ_add_R_rate) i.castSucc)
    (Oₘ := fun i => by infer_instance)
    -- next round
    (StmtOut := Statement (L := L) Context i.succ)
    (OStmtOut := OracleStatement 𝔽q β (ϑ := ϑ)
      (h_ℓ_add_R_rate := h_ℓ_add_R_rate) i.succ)
    (pSpec := pSpecCommit 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) i) where

  -- The core verification logic. Takes the input statement `stmtIn` and the transcript, and
  -- performs an oracle computation that outputs a new statement
  verify := fun stmtIn pSpecChallenges => do
    pure stmtIn

  embed := ⟨fun j => by
    classical
    if hj : j.val < toOutCodewordsCount ℓ ϑ i.castSucc then
      exact Sum.inl ⟨j.val, by omega⟩
    else
      exact Sum.inr ⟨0, by rfl⟩
  , by
    intro a b h_ab_eq
    simp only [MessageIdx, Fin.isValue] at h_ab_eq
    split_ifs at h_ab_eq with h_ab_eq_l h_ab_eq_r
    · simp at h_ab_eq; apply Fin.eq_of_val_eq; exact h_ab_eq
    · have ha_lt : a < toOutCodewordsCount ℓ ϑ i.succ := by omega
      have hb_lt : b < toOutCodewordsCount ℓ ϑ i.succ := by omega
      conv_rhs at ha_lt => rw [toOutCodewordsCount_succ_eq ℓ ϑ i]
      conv_rhs at hb_lt => rw [toOutCodewordsCount_succ_eq ℓ ϑ i]
      simp only [hCR, ↓reduceIte] at ha_lt hb_lt
      have h_a : a = toOutCodewordsCount ℓ ϑ i.castSucc := by omega
      have h_b : b = toOutCodewordsCount ℓ ϑ i.castSucc := by omega
      omega
  ⟩
  hEq := fun oracleIdx => by
    unfold OracleStatement pSpecCommit
    simp only [MessageIdx, Fin.isValue, Function.Embedding.coeFn_mk, Message,
      Matrix.cons_val_fin_one]
    by_cases hlt : oracleIdx.val < toOutCodewordsCount ℓ ϑ i.castSucc
    · -- oracleIdx maps to an existing prior-oracle index
      simp only [hlt, ↓reduceDIte]
    · -- oracleIdx is out of previous range, check commitment round
      simp only [hlt, ↓reduceDIte, Fin.isValue]
      have hOracleIdx_lt : oracleIdx.val < toOutCodewordsCount ℓ ϑ i.succ := by omega
      simp only [toOutCodewordsCount_succ_eq ℓ ϑ i, hCR, ↓reduceIte] at hOracleIdx_lt
      have hOracleIdx : oracleIdx = toOutCodewordsCount ℓ ϑ i.castSucc := by omega
      simp_rw [hOracleIdx];
      have h := toOutCodewordsCount_mul_ϑ_eq_i_succ ℓ ϑ (i := i) (hCR := hCR)
      rw! [h]
      rfl

/-- The oracle reduction that is the `i`-th round of Binary commitmentfold. -/
noncomputable def commitOracleReduction (i : Fin ℓ) (hCR : isCommitmentRound ℓ ϑ i) :
  OracleReduction (oSpec := []ₒ)
    (StmtIn := Statement (L := L) Context i.succ)
    (OStmtIn := OracleStatement 𝔽q β (ϑ := ϑ)
      (h_ℓ_add_R_rate := h_ℓ_add_R_rate) i.castSucc)
    (WitIn := Witness (L := L) 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) i.succ)
    (StmtOut := Statement (L := L) Context i.succ)
    (OStmtOut := OracleStatement 𝔽q β (ϑ := ϑ)
      (h_ℓ_add_R_rate := h_ℓ_add_R_rate) i.succ)
    (WitOut := Witness (L := L) 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) i.succ)
    (pSpec := pSpecCommit 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) i) where
  prover := commitOracleProver 𝔽q β (ϑ := ϑ) (h_ℓ_add_R_rate := h_ℓ_add_R_rate) i
  verifier := commitOracleVerifier 𝔽q β (ϑ := ϑ) (h_ℓ_add_R_rate := h_ℓ_add_R_rate) i hCR

variable {R : Type} [CommSemiring R] [DecidableEq R] [SampleableType R]
  {n : ℕ} {deg : ℕ} {m : ℕ} {D : Fin m ↪ R}

variable {σ : Type} {init : ProbComp σ} {impl : QueryImpl []ₒ (StateT σ ProbComp)}

theorem commitOracleReduction_perfectCompleteness (i : Fin ℓ)
    (hCR : isCommitmentRound ℓ ϑ i) :
    OracleReduction.perfectCompleteness
      (pSpec := pSpecCommit 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) i)
      (relIn := foldStepRelOut (mp := mp) 𝔽q β (ϑ := ϑ) (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
         i)
      (relOut := roundRelation (mp := mp) 𝔽q β (ϑ := ϑ) (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
         i.succ)
      (oracleReduction := commitOracleReduction 𝔽q β (ϑ := ϑ)
        (h_ℓ_add_R_rate := h_ℓ_add_R_rate) i hCR)
      (init := init)
      (impl := impl) := by
  unfold OracleReduction.perfectCompleteness
  intro stmtIn witIn h_relIn
  sorry

open scoped NNReal

def commitKnowledgeError {i : Fin ℓ}
    (m : (pSpecCommit 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) i).ChallengeIdx) : ℝ≥0 :=
  match m with
  | ⟨j, hj⟩ => by
    simp only [ne_eq, reduceCtorEq, not_false_eq_true, Matrix.cons_val_fin_one,
      Direction.not_P_to_V_eq_V_to_P] at hj -- not a V challenge

/-- The round-by-round extractor for a single round.
Since f^(0) is always available, we can invoke the extractMLP function directly. -/
noncomputable def commitRbrExtractor (i : Fin ℓ) :
  Extractor.RoundByRound []ₒ
    (StmtIn := (Statement (L := L) Context i.succ) × (∀ j, OracleStatement 𝔽q β (ϑ := ϑ)
      (h_ℓ_add_R_rate := h_ℓ_add_R_rate) i.castSucc j))
    (WitIn := Witness (L := L) 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) i.succ)
    (WitOut := Witness (L := L) 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) i.succ)
    (pSpec := pSpecCommit 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) i)
    (WitMid := fun _messageIdx => Witness (L := L) 𝔽q β
      (h_ℓ_add_R_rate := h_ℓ_add_R_rate) i.succ) where
  eqIn := rfl
  extractMid := fun _ _ _ witMidSucc => witMidSucc
  extractOut := fun _ _ witOut => witOut

/-- Note : stmtIn and witMid already advances to state `(i+1)` from the fold step,
while oStmtIn is not. -/
def commitKStateProp (i : Fin ℓ) (m : Fin (1 + 1))
  (stmtIn : Statement (L := L) Context i.succ)
  (witMid : Witness (L := L) 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) i.succ)
  (oStmtIn : (i_1 : Fin (toOutCodewordsCount ℓ ϑ i.castSucc)) →
    OracleStatement 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) ϑ i.castSucc i_1)
  : Prop :=

  match m with
  | ⟨0, _⟩ => -- same as relIn
    masterKStateProp (mp := mp) 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) 
      (stmtIdx := i.succ) (oracleIdx := i.castSucc)
      (h_le := by simp only [Fin.coe_castSucc, Fin.val_succ, le_add_iff_nonneg_right, zero_le])
      (stmt := stmtIn) (wit := witMid) (oStmt := oStmtIn)
      (localChecks := True)
  | ⟨1, _⟩ => -- implied by relOut
    let ⟨_, stmtOut, oStmtOut, witOut⟩ := getCommitProverFinalOutput 𝔽q β (ϑ := ϑ)
      (h_ℓ_add_R_rate := h_ℓ_add_R_rate) i ⟨stmtIn, oStmtIn, witMid⟩
    masterKStateProp (mp := mp) 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) 
      (stmtIdx := i.succ) (oracleIdx := i.succ)
      (h_le := le_refl _)
      (stmt := stmtOut) (wit := witOut) (oStmt := oStmtOut)
      (localChecks := True)

/-- Knowledge state function (KState) for single round -/
def commitKState (i : Fin ℓ) (hCR : isCommitmentRound ℓ ϑ i) :
    (commitOracleVerifier 𝔽q β (ϑ := ϑ) (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
      i hCR).KnowledgeStateFunction init impl
      (relIn := foldStepRelOut (mp := mp) 𝔽q β (ϑ := ϑ)
        (h_ℓ_add_R_rate := h_ℓ_add_R_rate) i)
      (relOut := roundRelation (mp := mp) 𝔽q β (ϑ := ϑ)
        (h_ℓ_add_R_rate := h_ℓ_add_R_rate) i.succ)
      (extractor := commitRbrExtractor 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) i) := by
  sorry

/-- RBR knowledge soundness for a single round oracle verifier -/
theorem commitOracleVerifier_rbrKnowledgeSoundness (i : Fin ℓ)
    (hCR : isCommitmentRound ℓ ϑ i) :
    (commitOracleVerifier 𝔽q β (ϑ := ϑ) (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
      i hCR).rbrKnowledgeSoundness init impl
      (relIn := foldStepRelOut (mp := mp) 𝔽q β (ϑ := ϑ)
        (h_ℓ_add_R_rate := h_ℓ_add_R_rate) i)
      (relOut := roundRelation (mp := mp) 𝔽q β (ϑ := ϑ)
        (h_ℓ_add_R_rate := h_ℓ_add_R_rate) i.succ)
      (commitKnowledgeError 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate)) := by
  use fun _ => Witness (L := L) 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) i.succ
  use commitRbrExtractor 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) i
  use commitKState (mp:=mp) 𝔽q β (ϑ := ϑ) (h_ℓ_add_R_rate := h_ℓ_add_R_rate) i hCR
  intro stmtIn witIn prover j
  exact absurd j.2 (by simp [pSpecCommit])

end CommitStep

section RelayStep
/- the relay is just to place the conditional oracle message -/

def relayPrvState (i : Fin ℓ) : Fin (0 + 1) → Type := fun
  | ⟨0, _⟩ => Statement (L := L) Context i.succ ×
    (∀ j, OracleStatement 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) ϑ i.castSucc j) ×
    Witness (L := L) 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) i.succ

/-- The prover for the `i`-th round of Binary relayfold. -/
noncomputable def relayOracleProver (i : Fin ℓ) (hNCR : ¬ isCommitmentRound ℓ ϑ i) :
  OracleProver (oSpec := []ₒ)
    -- current round
    (StmtIn := Statement (L := L) Context i.succ)
    (OStmtIn := OracleStatement 𝔽q β (ϑ := ϑ)
      (h_ℓ_add_R_rate := h_ℓ_add_R_rate) i.castSucc)
    (WitIn := Witness (L := L) 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (ℓ := ℓ) i.succ)
    (StmtOut := Statement (L := L) Context i.succ)
    (OStmtOut := OracleStatement 𝔽q β (ϑ := ϑ)
      (h_ℓ_add_R_rate := h_ℓ_add_R_rate) i.succ)
    (WitOut := Witness (L := L) 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (ℓ := ℓ) i.succ)
    (pSpec := pSpecRelay) where
  PrvState := relayPrvState 𝔽q β (ϑ := ϑ) (h_ℓ_add_R_rate := h_ℓ_add_R_rate) i
  input := fun ⟨⟨stmtIn, oStmtIn⟩, witIn⟩ => (stmtIn, oStmtIn, witIn)
  sendMessage | ⟨x, h⟩ => by exact x.elim0
  receiveChallenge | ⟨x, h⟩ => by exact x.elim0
  output := fun ⟨stmt, oStmt, wit⟩ =>
    pure ⟨⟨stmt, mapOStmtOutRelayStep 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
      i hNCR oStmt⟩, wit⟩

/-- The oracle verifier for the `i`-th round of Binary relayfold. -/
noncomputable def relayOracleVerifier (i : Fin ℓ) (hNCR : ¬ isCommitmentRound ℓ ϑ i) :
  OracleVerifier
    (oSpec := []ₒ)
    (StmtIn := Statement (L := L) Context i.succ)
    (OStmtIn := OracleStatement 𝔽q β (ϑ := ϑ)
      (h_ℓ_add_R_rate := h_ℓ_add_R_rate) i.castSucc)
    -- next round
    (StmtOut := Statement (L := L) Context i.succ)
    (OStmtOut := OracleStatement 𝔽q β (ϑ := ϑ)
      (h_ℓ_add_R_rate := h_ℓ_add_R_rate) i.succ)
    (pSpec := pSpecRelay) where
  verify := fun stmtIn _ => pure stmtIn
  embed := ⟨fun j => by
    have h_oracle_size_eq : toOutCodewordsCount ℓ ϑ i.castSucc =
      toOutCodewordsCount ℓ ϑ i.succ := by
      simp only [toOutCodewordsCount_succ_eq, hNCR, ↓reduceIte]
    exact Sum.inl ⟨j.val, by rw [h_oracle_size_eq]; omega⟩
  , by
    intro a b h_ab_eq
    simp only [MessageIdx, Sum.inl.injEq, Fin.mk.injEq] at h_ab_eq
    exact Fin.ext h_ab_eq
  ⟩
  hEq := fun oracleIdx => by simp only

/-- The oracle reduction that is the `i`-th round of Binary relayfold. -/
noncomputable def relayOracleReduction (i : Fin ℓ) (hNCR : ¬ isCommitmentRound ℓ ϑ i) :
  OracleReduction (oSpec := []ₒ)
    (StmtIn := Statement (L := L) Context i.succ)
    (OStmtIn := OracleStatement 𝔽q β (ϑ := ϑ)
      (h_ℓ_add_R_rate := h_ℓ_add_R_rate) i.castSucc)
    (WitIn := Witness (L := L) 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) i.succ)
    (StmtOut := Statement (L := L) Context i.succ)
    (OStmtOut := OracleStatement 𝔽q β (ϑ := ϑ)
      (h_ℓ_add_R_rate := h_ℓ_add_R_rate) i.succ)
    (WitOut := Witness (L := L) 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) i.succ)
    (pSpec := pSpecRelay) where
  prover := relayOracleProver 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) i hNCR
  verifier := relayOracleVerifier 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) i hNCR

/-- The relay-step oracle verifier routes each output oracle (round `i.succ`) to the input oracle
(round `i.castSucc`) at the same numeric index; on a non-commitment round the codeword counts agree
(`toOutCodewordsCount_succ_eq`), so the `OracleStatement` interfaces — index-dependent only through
the numeric position — coincide, giving `AppendCoherent` by `rfl` after the index `subst`. -/
instance instRelayOracleVerifierAppendCoherent (i : Fin ℓ) (hNCR : ¬ isCommitmentRound ℓ ϑ i) :
    OracleVerifier.Append.AppendCoherent
      (relayOracleVerifier 𝔽q β (ϑ := ϑ) (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (Context := Context)
        i hNCR) where
  hCohInl := fun a k h => by
    have hak : a.val = k.val := by
      simpa only [relayOracleVerifier, Function.Embedding.coeFn_mk, Sum.inl.injEq]
        using congrArg (·.val) (Sum.inl.inj h)
    have hcnt : toOutCodewordsCount ℓ ϑ i.castSucc = toOutCodewordsCount ℓ ϑ i.succ := by
      simp only [toOutCodewordsCount_succ_eq, hNCR, ↓reduceIte]
    obtain ⟨av, hav⟩ := a; obtain ⟨kv, hkv⟩ := k
    simp only [] at hak; subst hak; rfl
  hCohInr := fun a k h => by
    simp only [relayOracleVerifier, Function.Embedding.coeFn_mk, reduceCtorEq] at h

instance instRelayOracleReductionAppendCoherent (i : Fin ℓ) (hNCR : ¬ isCommitmentRound ℓ ϑ i) :
    OracleVerifier.Append.AppendCoherent
      (relayOracleReduction 𝔽q β (ϑ := ϑ) (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (Context := Context)
        i hNCR).verifier :=
  instRelayOracleVerifierAppendCoherent 𝔽q β (ϑ := ϑ) (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
    (Context := Context) i hNCR

variable {R : Type} [CommSemiring R] [DecidableEq R] [SampleableType R]
  {n : ℕ} {deg : ℕ} {m : ℕ} {D : Fin m ↪ R}

variable {σ : Type} {init : ProbComp σ} {impl : QueryImpl []ₒ (StateT σ ProbComp)}

/-- Run-collapse for the relay reduction: since `pSpecRelay` is the zero-round protocol, the honest
prover and (oracle) verifier execute deterministically. The verifier returns the input non-oracle
statement, and both prover and verifier relabel the oracle statements via `mapOStmtOutRelayStep`. -/
private lemma relayReduction_run_collapse (i : Fin ℓ) (hNCR : ¬ isCommitmentRound ℓ ϑ i)
    (stmtIn : Statement (L := L) Context i.succ)
    (oStmtIn : ∀ j, OracleStatement 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) ϑ i.castSucc j)
    (witIn : Witness (L := L) 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) i.succ) :
    (relayOracleReduction 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) i hNCR).toReduction.run
        (stmtIn, oStmtIn) witIn =
      (pure ⟨⟨default,
          (stmtIn, mapOStmtOutRelayStep 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) i hNCR oStmtIn),
          witIn⟩,
          (stmtIn, mapOStmtOutRelayStep 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) i hNCR oStmtIn)⟩) := by
  simp only [OracleReduction.toReduction, Reduction.run, relayOracleReduction,
    relayOracleProver, relayOracleVerifier, Prover.run,
    Prover.runToRound_zero_of_prover_first,
    OracleVerifier.toVerifier, Verifier.run,
    simulateQ_pure, OptionT.run_pure,
    bind_pure_comp, map_pure, pure_bind, monadLift_pure, liftM_pure,
    Option.getM, StateT.run'_eq, StateT.run_pure]
  rfl

theorem relayOracleReduction_perfectCompleteness (i : Fin ℓ)
    (hNCR : ¬ isCommitmentRound ℓ ϑ i) :
    OracleReduction.perfectCompleteness
      (pSpec := pSpecRelay)
      (relIn := foldStepRelOut (mp := mp) 𝔽q β (ϑ := ϑ) (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
         i)
      (relOut := roundRelation (mp := mp) 𝔽q β (ϑ := ϑ) (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
         i.succ)
      (oracleReduction := relayOracleReduction 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
        i hNCR)
      (init := init)
      (impl := impl) := by
  unfold OracleReduction.perfectCompleteness
  rw [Reduction.perfectCompleteness_eq_prob_one]
  intro ⟨stmtIn, oStmtIn⟩ witIn h_relIn
  -- The relay reduction is a 0-round protocol; both prover and verifier execute deterministically.
  rw [relayReduction_run_collapse]
  -- Abbreviation for the deterministic relabeled oracle statement.
  set relayO := mapOStmtOutRelayStep 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) i hNCR oStmtIn
    with hrelayO
  -- The output statement-witness pair is in `roundRelation i.succ` (the mathematical core).
  have h_rel : ((stmtIn, relayO), witIn) ∈
      roundRelation (mp := mp) 𝔽q β (ϑ := ϑ) (h_ℓ_add_R_rate := h_ℓ_add_R_rate) i.succ := by
    simp only [roundRelation, Set.mem_setOf_eq, roundRelationProp, masterKStateProp]
    simp only [foldStepRelOut, Set.mem_setOf_eq, foldStepRelOutProp, hNCR, if_false] at h_relIn
    have h_take : Fin.take (m := (i.succ : Fin (ℓ + 1)).val) (le_refl _) stmtIn.challenges
        = stmtIn.challenges := by funext x; simp [Fin.take_apply]
    refine ⟨trivial, ?_⟩
    rw [h_take, hrelayO]
    rw [← badEventExistsProp_relay_preserved 𝔽q β i hNCR stmtIn.challenges oStmtIn,
        ← oracleWitnessConsistency_relay_preserved 𝔽q β i hNCR stmtIn witIn oStmtIn]
    exact h_relIn
  -- The run collapses to a deterministic `pure`; its event probability is exactly one because the
  -- success predicate holds on the (unique) output and `init` contributes probability one.
  -- (Same plumbing as `Reduction.id_perfectCompleteness`, with the relabeled oracle statement.)
  rw [probEvent_eq_one_iff]
  refine ⟨?_, ?_⟩
  · -- `Pr[⊥ | OptionT.mk ...] = 0`.
    rw [OptionT.probFailure_eq, OptionT.run_mk]
    simp only [probFailure_eq_zero, zero_add]
    apply probOutput_eq_zero_of_not_mem_support
    simp only [support_bind, Set.mem_iUnion, not_exists]
    intro s _
    change none ∈ _root_.support
      (StateT.run' (simulateQ _ (pure (some
        (((default : pSpecRelay.FullTranscript), (stmtIn, relayO), witIn), stmtIn, relayO)) :
        OracleComp _ _)) s) → False
    rw [simulateQ_pure]
    change none ∈ _root_.support
      (Prod.fst <$> (pure (some
        (((default : pSpecRelay.FullTranscript), (stmtIn, relayO), witIn), stmtIn, relayO)) :
        StateT σ ProbComp _).run s) → False
    rw [StateT.run_pure]; simp [map_pure]
  · -- Every supported output satisfies the success predicate.
    intro x hx
    rw [OptionT.mem_support_iff] at hx
    simp only [OptionT.run_mk, support_bind, Set.mem_iUnion] at hx
    obtain ⟨s, _, hx⟩ := hx
    change some x ∈ _root_.support
      (StateT.run' (simulateQ _ (pure (some
        (((default : pSpecRelay.FullTranscript), (stmtIn, relayO), witIn), stmtIn, relayO)) :
        OracleComp _ _)) s) at hx
    rw [simulateQ_pure] at hx
    change some x ∈ _root_.support
      (Prod.fst <$> (pure (some
        (((default : pSpecRelay.FullTranscript), (stmtIn, relayO), witIn), stmtIn, relayO)) :
        StateT σ ProbComp _).run s) at hx
    rw [StateT.run_pure] at hx
    simp [map_pure, support_pure] at hx
    cases hx
    exact ⟨h_rel, rfl⟩

def relayKnowledgeError (m : pSpecRelay.ChallengeIdx) : ℝ≥0 :=
  match m with
  | ⟨j, _⟩ => j.elim0

/-- The round-by-round extractor for a single round.
Since f^(0) is always available, we can invoke the extractMLP function directly. -/
noncomputable def relayRbrExtractor (i : Fin ℓ) :
  Extractor.RoundByRound []ₒ
    (StmtIn := (Statement (L := L) Context i.succ) × (∀ j, OracleStatement 𝔽q β (ϑ := ϑ)
      (h_ℓ_add_R_rate := h_ℓ_add_R_rate) i.castSucc j))
    (WitIn := Witness (L := L) 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) i.succ)
    (WitOut := Witness (L := L) 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) i.succ)
    (pSpec := pSpecRelay)
    (WitMid := fun _messageIdx => Witness (L := L) 𝔽q β
      (h_ℓ_add_R_rate := h_ℓ_add_R_rate) i.succ) where
  eqIn := rfl
  extractMid := fun _ _ _ witMidSucc => witMidSucc
  extractOut := fun _ _ witOut => witOut

def relayKStateProp (i : Fin ℓ) (hNCR : ¬ isCommitmentRound ℓ ϑ i)
  (stmtIn : Statement (L := L) Context i.succ)
  (witMid : Witness (L := L) 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) i.succ)
  (oStmtIn : (∀ j, OracleStatement 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) ϑ i.castSucc j))
  : Prop :=
  masterKStateProp (mp := mp) (ϑ := ϑ) 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) 
    (stmtIdx := i.succ) (oracleIdx := i.succ)
    (h_le := le_refl _)
    (stmt := stmtIn) (wit := witMid) (oStmt := mapOStmtOutRelayStep
      𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) i hNCR oStmtIn)
    (localChecks := True)

/-- Knowledge state function (KState) for single round -/
def relayKnowledgeStateFunction (i : Fin ℓ) (hNCR : ¬ isCommitmentRound ℓ ϑ i) :
    (relayOracleVerifier 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
        i hNCR).KnowledgeStateFunction init impl
      (relIn := foldStepRelOut (mp := mp) 𝔽q β (ϑ := ϑ)
        (h_ℓ_add_R_rate := h_ℓ_add_R_rate) i)
      (relOut := roundRelation (mp := mp) 𝔽q β (ϑ := ϑ)
        (h_ℓ_add_R_rate := h_ℓ_add_R_rate) i.succ)
      (extractor := relayRbrExtractor 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) i) where
  toFun := fun m ⟨stmtIn, oStmtIn⟩ tr witMid =>
    relayKStateProp (mp:=mp) 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
      i hNCR stmtIn witMid oStmtIn
  toFun_empty := fun ⟨stmtIn, oStmtIn⟩ witIn => by
    simp only [foldStepRelOut, foldStepRelOutProp, cast_eq, Set.mem_setOf_eq, relayKStateProp]
    -- relay round ⇒ non-commitment ⇒ `foldStepRelOutProp` takes its `else` (relay) branch, whose
    -- bad event is evaluated at the statement index `i.succ` (oracle `i.castSucc`).
    rw [if_neg hNCR]
    unfold masterKStateProp
    simp only [Fin.val_succ, Fin.coe_castSucc, Fin.take_eq_init, true_and, Fin.take_eq_self]
    have hRight := oracleWitnessConsistency_relay_preserved (mp := mp) 𝔽q β i
      hNCR stmtIn witIn oStmtIn
    rw [hRight]
    -- The two `oracleWitnessConsistency` disjuncts now coincide (via `hRight`). The bad-event
    -- disjuncts coincide too: both are evaluated at the statement index `i.succ` (LHS oracle
    -- `i.castSucc`, RHS oracle `i.succ` on the relay-mapped oracle), and
    -- `badEventExistsProp_relay_preserved` shows the relay relabel preserves the existential.
    -- Hence the `↔` is `Iff.rfl` at every non-commitment round, including the last (`i.val+1 = ℓ`).
    rw [badEventExistsProp_relay_preserved 𝔽q β i hNCR stmtIn.challenges oStmtIn]
  toFun_next := fun m hDir (stmtIn, oStmtIn) tr msg witMid => by exact fun a ↦ a
  toFun_full := fun (stmtIn, oStmtIn) tr witOut=> by
    intro h
    rw [gt_iff_lt, probEvent_pos_iff] at h
    obtain ⟨x, hx, hrel⟩ := h
    -- The relay verifier deterministically outputs `(stmtIn, mapOStmtOutRelayStep ... oStmtIn)`.
    have hrun : Verifier.run (stmtIn, oStmtIn) tr (relayOracleVerifier 𝔽q β
        (h_ℓ_add_R_rate := h_ℓ_add_R_rate) i hNCR).toVerifier =
        (pure (stmtIn, mapOStmtOutRelayStep 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) i hNCR oStmtIn)
          : OptionT (OracleComp []ₒ) _) := by
      simp only [Verifier.run, OracleVerifier.toVerifier, relayOracleVerifier]
      erw [simulateQ_pure]
      rfl
    rw [hrun] at hx
    rw [OptionT.mem_support_iff] at hx
    simp only [OptionT.run_mk, support_bind, Set.mem_iUnion] at hx
    obtain ⟨s, _, hx⟩ := hx
    have key : (simulateQ impl (pure (stmtIn,
        mapOStmtOutRelayStep 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) i hNCR oStmtIn) :
          OptionT (OracleComp []ₒ) _)).run' s =
        pure (some (stmtIn,
          mapOStmtOutRelayStep 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) i hNCR oStmtIn)) := by
      change (simulateQ impl (pure (some (stmtIn,
        mapOStmtOutRelayStep 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) i hNCR oStmtIn)) :
          OracleComp []ₒ _)).run' s = _
      rw [simulateQ_pure]
      change Prod.fst <$> (pure (some (stmtIn,
        mapOStmtOutRelayStep 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) i hNCR oStmtIn)) :
          StateT σ ProbComp _).run s = _
      rw [StateT.run_pure]; simp [map_pure]
    rw [key] at hx
    simp only [support_pure, Set.mem_singleton_iff] at hx
    cases hx
    -- Now `hrel : ((stmtIn, mapOStmtOutRelayStep ...), witOut) ∈ roundRelation i.succ`,
    -- which is definitionally `relayKStateProp 𝔽q β i hNCR stmtIn witOut oStmtIn`.
    exact hrel

/-- RBR knowledge soundness for a single round oracle verifier -/
theorem relayOracleVerifier_rbrKnowledgeSoundness (i : Fin ℓ)
    (hNCR : ¬ isCommitmentRound ℓ ϑ i) :
    (relayOracleVerifier 𝔽q β (ϑ := ϑ) (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
        i hNCR).rbrKnowledgeSoundness init impl
      (relIn := foldStepRelOut (mp := mp) 𝔽q β (ϑ := ϑ)
        (h_ℓ_add_R_rate := h_ℓ_add_R_rate) i)
      (relOut := roundRelation (mp := mp) 𝔽q β (ϑ := ϑ)
        (h_ℓ_add_R_rate := h_ℓ_add_R_rate) i.succ)
      (relayKnowledgeError) := by
  use fun _ => Witness (L := L) 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) i.succ
  use relayRbrExtractor 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) i
  use relayKnowledgeStateFunction (mp:=mp) 𝔽q β (ϑ := ϑ)
    (h_ℓ_add_R_rate := h_ℓ_add_R_rate) i hNCR
  intro stmtIn witIn prover j
  exact j.val.elim0

end RelayStep

end SingleIteratedSteps

section FinalSumcheckStep
/-!
## Final Sumcheck Step

This section implements the final sumcheck step that sends the constant `c := f^(ℓ)(0, ..., 0)`
from the prover to the verifier. This step completes the sumcheck verification by ensuring
the final constant is consistent with the folding chain.

The step consists of :
- P → V : constant `c := f^(ℓ)(0, ..., 0)`
- V verifies : `s_ℓ = eqTilde(r, r') * c`
=> `c` should be equal to `t(r'_0, ..., r'_{ℓ-1})` and `f^(ℓ)(0, ..., 0)`

**Key Mathematical Insight** : At round ℓ, we have :
- `P^(ℓ)(X) = Σ_{w ∈ B_0} H_ℓ(w) · X_w^(ℓ)(X) = H_ℓ(0) · X_0^(ℓ)(X) = H_ℓ(0)`
- Since `H_ℓ(X)` is constant (zero-variate): `H_ℓ(X) = t(r'_0, ..., r'_{ℓ-1})`
- Therefore : `P^(ℓ)(X) = t(r'_0, ..., r'_{ℓ-1})` (constant polynomial)
- And `s_ℓ = ∑_{w ∈ B_0} t(r'_0, ..., r'_{ℓ-1}) = t(r'_0, ..., r'_{ℓ-1})`
-/

/-- Oracle interface instance for the final sumcheck step message -/
instance : ∀ j, OracleInterface ((pSpecFinalSumcheckStep (L := L)).Message j) := fun j =>
  match j with
  | ⟨0, _⟩ => OracleInterface.instDefault

/-- The prover for the final sumcheck step -/
noncomputable def finalSumcheckProver :
  OracleProver
    (oSpec := []ₒ)
    (StmtIn := Statement (L := L) (SumcheckBaseContext L ℓ) (Fin.last ℓ))
    (OStmtIn := OracleStatement 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) ϑ (Fin.last ℓ))
    (WitIn := Witness (L := L) 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (Fin.last ℓ))
    (StmtOut := FinalSumcheckStatementOut (L := L) (ℓ := ℓ))
    (OStmtOut := OracleStatement 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) ϑ (Fin.last ℓ))
    (WitOut := Unit)
    (pSpec := pSpecFinalSumcheckStep (L := L)) where
  PrvState := fun
    | 0 => Statement (L := L) (SumcheckBaseContext L ℓ) (Fin.last ℓ) × (∀ j, OracleStatement 𝔽q β
      (h_ℓ_add_R_rate := h_ℓ_add_R_rate) ϑ (Fin.last ℓ) j)
        × Witness (L := L) 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (Fin.last ℓ)
    | _ => Statement (L := L) (SumcheckBaseContext L ℓ) (Fin.last ℓ) × (∀ j, OracleStatement 𝔽q β
      (h_ℓ_add_R_rate := h_ℓ_add_R_rate) ϑ (Fin.last ℓ) j)
        × Witness (L := L) 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (Fin.last ℓ) × L
  input := fun ⟨⟨stmt, oStmt⟩, wit⟩ => (stmt, oStmt, wit)

  sendMessage
  | ⟨0, _⟩ => fun ⟨stmtIn, oStmtIn, witIn⟩ => do
    let fℓ : OracleFunction 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (i := ⟨ℓ, by omega⟩)
      := witIn.f
    -- Evaluate f^(ℓ) at the zero point to get the final constant
    let c : L := fℓ ⟨0, by simp only [zero_mem]⟩ -- f^(ℓ)(0, ..., 0)
    pure ⟨c, (stmtIn, oStmtIn, witIn, c)⟩

  receiveChallenge
  | ⟨0, h⟩ => nomatch h -- No challenges in this step

  output := fun ⟨stmtIn, oStmtIn, witIn, c⟩ => do
    let stmtOut : FinalSumcheckStatementOut (L := L) (ℓ := ℓ) := {
      ctx := stmtIn.ctx,
      -- Current round state
      sumcheck_target := stmtIn.sumcheck_target,
      challenges := stmtIn.challenges,
      final_constant := c
    }

    pure (⟨stmtOut, oStmtIn⟩, ())

/-- The verifier for the final sumcheck step -/
noncomputable def finalSumcheckVerifier :
  OracleVerifier
    (oSpec := []ₒ)
    (StmtIn := Statement (L := L) (SumcheckBaseContext L ℓ) (Fin.last ℓ))
    (OStmtIn := OracleStatement 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) ϑ (Fin.last ℓ))
    (StmtOut := FinalSumcheckStatementOut (L := L) (ℓ := ℓ))
    (OStmtOut := OracleStatement 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) ϑ (Fin.last ℓ))
    (pSpec := pSpecFinalSumcheckStep (L := L)) where
  verify := fun stmtIn _ => do
    -- Get the final constant `c` from the prover's message
    let c : L ← query (spec := [(pSpecFinalSumcheckStep (L := L)).Message]ₒ) ⟨⟨0, rfl⟩, ()⟩

    -- Check final sumcheck consistency
    let eq_tilde_eval : L := eqTilde (r := stmtIn.ctx.t_eval_point) (r' := stmtIn.challenges)
    unless stmtIn.sumcheck_target = eq_tilde_eval * c do
      return { -- dummy stmtOut
        ctx := {t_eval_point := 0, original_claim := 0},
        sumcheck_target := 0,
        challenges := 0,
        final_constant := 0
      }

    -- Return the final sumcheck statement with the constant
    let stmtOut : FinalSumcheckStatementOut (L := L) (ℓ := ℓ) := {
      ctx := stmtIn.ctx,
      sumcheck_target := eq_tilde_eval * c, -- = s_ℓ = h_{ℓ-1}.eval r_{ℓ - 1}
      challenges := stmtIn.challenges,
      final_constant := c
    }
    pure stmtOut

  embed := ⟨fun j => by
    if hj : j.val < toOutCodewordsCount ℓ ϑ (Fin.last ℓ) then
      exact Sum.inl ⟨j.val, by omega⟩
    else omega -- never happens
  , by
    intro a b h_ab_eq
    simp only [MessageIdx, Fin.is_lt, ↓reduceDIte, Fin.eta, Sum.inl.injEq] at h_ab_eq
    exact h_ab_eq
  ⟩
  hEq := fun oracleIdx => by
    simp only [MessageIdx, Fin.is_lt, ↓reduceDIte, Fin.eta, Function.Embedding.coeFn_mk]

/-- The oracle reduction for the final sumcheck step -/
noncomputable def finalSumcheckOracleReduction :
  OracleReduction
    (oSpec := []ₒ)
    (StmtIn := Statement (L := L) (SumcheckBaseContext L ℓ) (Fin.last ℓ))
    (OStmtIn := OracleStatement 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) ϑ (Fin.last ℓ))
    (WitIn := Witness (L := L) 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (Fin.last ℓ))
    (StmtOut := FinalSumcheckStatementOut (L := L) (ℓ := ℓ))
    (OStmtOut := OracleStatement 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) ϑ (Fin.last ℓ))
    (WitOut := Unit)
    (pSpec := pSpecFinalSumcheckStep (L := L)) where
  prover := finalSumcheckProver 𝔽q β (ϑ := ϑ) (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
  verifier := finalSumcheckVerifier 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate)

/-- Perfect completeness for the final sumcheck step -/
theorem finalSumcheckOracleReduction_perfectCompleteness {σ : Type}
  (init : ProbComp σ)
  (impl : QueryImpl []ₒ (StateT σ ProbComp)) :
  OracleReduction.perfectCompleteness
    (pSpec := pSpecFinalSumcheckStep (L := L))
    (relIn := roundRelation 𝔽q β (ϑ := ϑ) (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
       (mp := BBF_SumcheckMultiplierParam) (Fin.last ℓ))
    (relOut := finalSumcheckRelOut 𝔽q β (ϑ := ϑ) (h_ℓ_add_R_rate := h_ℓ_add_R_rate))
    (oracleReduction := finalSumcheckOracleReduction 𝔽q β (ϑ := ϑ)
      (h_ℓ_add_R_rate := h_ℓ_add_R_rate)) (init := init) (impl := impl) := by
  unfold OracleReduction.perfectCompleteness
  intro stmtIn witIn h_relIn
  simp only
  -- HONEST STOP (residual — deep missing algebra, same class as the sibling
  -- `RingSwitching.…finalSumcheck…_perfectCompleteness`'s `finalSumcheck_check_of_relIn`):
  -- the honest run is deterministic (`pSpecFinalSumcheckStep` = one P→V message, no challenge); the
  -- prover sends `c := witIn.f ⟨0,_⟩ = f^(ℓ)(0)` and the verifier checks
  --   `stmtIn.sumcheck_target = eqTilde r r' * c`  (the `if` guard).
  -- Discharging the guard requires the algebraic chain
  --   relIn (roundRelation = masterKStateProp at `Fin.last ℓ`)  ⟹  sumcheck_target = eqTilde · c,
  -- i.e. a `finalSumcheck_check_of_relIn`-analog tying `sumcheckConsistencyProp` + the
  -- `witnessStructuralInvariant` (`wit.f = getMidCodewords … t`, `wit.H = projectToMidSumcheckPoly`)
  -- to `f^(ℓ)(0) = t(r')` and the final `H_ℓ`-collapse `s_ℓ = eqTilde(r,r') · t(r')`. No such lemma
  -- exists in-tree for BinaryBasefold (only the RingSwitching variant has the DP24 cube-0 algebra),
  -- and relIn may hold via the bad-event disjunct alone (no `owc`), under which the honest `c` need
  -- not pass the guard — so even the deterministic-run collapse cannot close without this algebra.
  sorry

/-- RBR knowledge error for the final sumcheck step -/
def finalSumcheckKnowledgeError (m : pSpecFinalSumcheckStep (L := L).ChallengeIdx) :
  ℝ≥0 :=
  match m with
  | ⟨0, h0⟩ => nomatch h0

def FinalSumcheckWit := fun (m : Fin (1 + 1)) =>
 match m with
 | ⟨0, _⟩ => Witness (L := L) 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (Fin.last ℓ)
 | ⟨1, _⟩ => Unit

/-- The round-by-round extractor for the final sumcheck step -/
noncomputable def finalSumcheckRbrExtractor :
  Extractor.RoundByRound []ₒ
    (StmtIn := (Statement (L := L) (SumcheckBaseContext L ℓ) (Fin.last ℓ)) × (∀ j, OracleStatement 𝔽q β
      (h_ℓ_add_R_rate := h_ℓ_add_R_rate) ϑ (Fin.last ℓ) j))
    (WitIn := Witness (L := L) 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (Fin.last ℓ))
    (WitOut := Unit)
    (pSpec := pSpecFinalSumcheckStep (L := L))
    (WitMid := FinalSumcheckWit (L := L) 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (ℓ := ℓ)) where
  eqIn := rfl
  extractMid := fun m ⟨stmtMid, oStmtMid⟩ trSucc witMidSucc => by
    have hm : m = 0 := by omega
    subst hm
    -- Decode t from the first oracle f^(0)
    let f0 := getFirstOracle 𝔽q β oStmtMid
    let polyOpt := extractMLP 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
      (i := ⟨0, by exact Nat.pos_of_neZero ℓ⟩) (f := f0)
    match polyOpt with
    | none => -- NOTE, In proofs of toFun_next, this case would be eliminated
      exact dummyLastWitness (L := L) 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
    | some tpoly =>
      -- Build H_ℓ from t and challenges r'
      exact {
        t := tpoly,
        H := projectToMidSumcheckPoly (L := L) (ℓ := ℓ) (t := tpoly)
          (m := BBF_SumcheckMultiplierParam.multpoly stmtMid.ctx)
          (i := Fin.last ℓ) (challenges := stmtMid.challenges),
        f := getMidCodewords 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) tpoly stmtMid.challenges
      }
  extractOut := fun ⟨stmtIn, oStmtIn⟩ tr witOut => ()

def finalSumcheckKStateProp {m : Fin (1 + 1)} (tr : Transcript m (pSpecFinalSumcheckStep (L := L)))
    (stmt : Statement (L := L) (SumcheckBaseContext L ℓ) (Fin.last ℓ))
    (witMid : FinalSumcheckWit (L := L) 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (ℓ := ℓ) m)
    (oStmt : ∀ j, OracleStatement 𝔽q β
      (h_ℓ_add_R_rate := h_ℓ_add_R_rate) ϑ (Fin.last ℓ) j) : Prop :=
  match m with
  | ⟨0, _⟩ => -- same as relIn
    masterKStateProp 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) 
      (mp := BBF_SumcheckMultiplierParam)
      (stmtIdx := Fin.last ℓ) (oracleIdx := Fin.last ℓ) (h_le := le_refl _)
      (stmt := stmt) (wit := witMid) (oStmt := oStmt) (localChecks := True)
  | ⟨1, _⟩ => -- implied by relOut + local checks via extractOut proofs
    let tr_so_far := (pSpecFinalSumcheckStep (L := L)).take 1 (by omega)
    let i_msg0 : tr_so_far.MessageIdx := ⟨⟨0, by omega⟩, rfl⟩
    let c : L := (ProtocolSpec.Transcript.equivMessagesChallenges (k := 1)
      (pSpec := pSpecFinalSumcheckStep (L := L)) tr).1 i_msg0

    let stmtOut : FinalSumcheckStatementOut (L := L) (ℓ := ℓ) := {
      ctx := stmt.ctx,
      sumcheck_target := stmt.sumcheck_target,
      challenges := stmt.challenges,
      final_constant := c
    }

    let sumcheckFinalCheck : Prop := stmt.sumcheck_target = eqTilde r stmt.challenges * c
    let finalFoldingProp := finalNonDoomedFoldingProp 𝔽q β (ϑ := ϑ)
      (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (h_le := by
        apply Nat.le_of_dvd;
        · exact Nat.pos_of_neZero ℓ
        · exact hdiv.out) (input := ⟨stmtOut, oStmt⟩)

    sumcheckFinalCheck ∧ finalFoldingProp -- local checks ∧ (oracleConsitency ∨ badEventExists)

/-! ### Local `simulateQ`/`simOracle2` message-query collapse toolkit

`Steps.lean` does not import the `RingSwitching` tree (where the analogous helpers live), so the
three small `simulateQ` collapse lemmas needed by `finalSumcheckKnowledgeStateFunction.toFun_full`
are replicated here from core VCVio primitives (`simulateQ_spec_query`, `simulateQ_optionT_lift`,
`simulateQ_pure`). They are protocol-agnostic. -/
section SimulateQCollapse

open OracleInterface in
/-- The `OracleInterface.simOracle2` collapse for a message (right-family) query, `OracleComp`
form: simulating a query to the prover-message oracle answers with the message itself. -/
private lemma simulateQ_simOracle2_messageQuery {ι : Type} {oSpec : OracleSpec ι}
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
/-- `OptionT`/`query` form of `simulateQ_simOracle2_messageQuery`: the form appearing verbatim in an
`OracleVerifier.verify` body. -/
private lemma simulateQ_simOracle2_query {ι : Type} {oSpec : OracleSpec ι}
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

/-- The `instDefault` oracle answer is the message itself (`answer m () = m`). -/
@[simp] private lemma answer_instDefault' {M : Type} (m : M) (q : Unit) :
    @OracleInterface.answer M OracleInterface.instDefault m q = m := rfl

/-- `simulateQ` commutes with `OptionT.pure`, for any target monad `n` (in particular
`StateT σ ProbComp`, which the outer `impl` simulation maps into). -/
@[simp] private theorem simulateQ_optionT_pure' {ιₐ : Type} {specₐ : OracleSpec ιₐ}
    {n : Type → Type} [Monad n] [LawfulMonad n] {γ : Type}
    (impl : QueryImpl specₐ n) (b : γ) :
    simulateQ impl (pure b : OptionT (OracleComp specₐ) γ)
      = (pure b : OptionT n γ) := by
  rw [show (pure b : OptionT (OracleComp specₐ) γ) = OptionT.lift (pure b)
        from (OptionT.lift_pure b).symm]
  rw [simulateQ_optionT_lift, simulateQ_pure, OptionT.lift_pure]

end SimulateQCollapse

/-- The knowledge state function for the final sumcheck step -/
noncomputable def finalSumcheckKnowledgeStateFunction {σ : Type} (init : ProbComp σ)
    (impl : QueryImpl []ₒ (StateT σ ProbComp)) :
    (finalSumcheckVerifier 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate)).KnowledgeStateFunction init impl
    (relIn := roundRelation 𝔽q β (ϑ := ϑ) (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
       (mp := BBF_SumcheckMultiplierParam) (Fin.last ℓ))
    (relOut := finalSumcheckRelOut 𝔽q β (ϑ := ϑ) (h_ℓ_add_R_rate := h_ℓ_add_R_rate))
    (extractor := finalSumcheckRbrExtractor 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate))
  where
  toFun := fun m ⟨stmt, oStmt⟩ tr witMid =>
    finalSumcheckKStateProp 𝔽q β (ϑ := ϑ) (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
       (tr := tr) (stmt := stmt) (witMid := witMid) (oStmt := oStmt)
  toFun_empty := fun stmt witMid => by simp only; rfl
  toFun_next := fun m hDir stmt tr msg witMid h => by
    -- Either bad events exist, or (oracleFoldingConsistency is true so
      -- the extractor can construct a satisfying witness)
    obtain ⟨stmt, oStmt⟩ := stmt
    fin_cases m
    -- `m.succ = ⟨1, _⟩`: `h` is `finalSumcheckKStateProp 1 = sumcheckFinalCheck ∧ finalFoldingProp`.
    -- `m.castSucc = ⟨0, _⟩`: goal is `finalSumcheckKStateProp 0 =
    --   masterKStateProp (stmtIdx := oracleIdx := Fin.last ℓ) (localChecks := True)
    --   = True ∧ (badEventExists ∨ oracleWitnessConsistency)`.
    simp only [finalSumcheckKStateProp, masterKStateProp, true_and] at h ⊢
    obtain ⟨_hSumcheckCheck, hFold⟩ := h
    -- `hFold : finalNonDoomedFoldingProp · = oracleFoldingConsistency ∨ foldingBadEventExists`.
    -- The `foldingBadEventExists` disjunct is exactly the `badEventExists` of the index-0
    -- `masterKStateProp` (oracleIdx := Fin.last ℓ, challenges = stmt.challenges, modulo
    -- `Fin.take_eq_self`).
    rcases hFold with hOFC | hBad
    · -- `oracleFoldingConsistency` branch: deriving `badEventExists ∨ oracleWitnessConsistency`
      -- requires extraction soundness for the m=0 `extractMid` witness (`witnessStructuralInvariant`,
      -- `sumcheckConsistency`, `firstOracleConsistency`), which is not available in-tree.
      sorry
    · -- `foldingBadEventExists` branch: route into `badEventExists` directly.
      refine Or.inl ?_
      simpa only [finalNonDoomedFoldingProp, Fin.take_eq_self] using hBad
  toFun_full := fun stmt tr witOut h => by
    obtain ⟨stmt, oStmt⟩ := stmt
    -- (1) PLUMBING (mechanical, lands): unfold the positive-probability hypothesis to a support
    -- membership of the simulated verifier run, then collapse the single message-oracle query
    -- (`c := tr ⟨0,_⟩`) via `simulateQ_simOracle2_query` + `answer_instDefault'`.
    rw [gt_iff_lt, probEvent_pos_iff] at h
    obtain ⟨x, hx, hrel⟩ := h
    rw [OptionT.mem_support_iff] at hx
    simp only [OptionT.run_mk, support_bind, Set.mem_iUnion] at hx
    obtain ⟨s, _, hx⟩ := hx
    simp only [Verifier.run, OracleVerifier.toVerifier, finalSumcheckVerifier] at hx
    -- Collapse the simOracle2 layer through the OptionT binds and the single message query.
    simp only [simulateQ_optionT_bind, simulateQ_simOracle2_query, OptionT.lift_pure, pure_bind,
      answer_instDefault', FullTranscript.messages, apply_ite, simulateQ_optionT_pure'] at hx
    -- After this, `hx` (verified via `pp.all`) reads:
    --   ∃ x₁ ∈ support (StateT.run ((fun a => (a, oStmtOut)) <$>
    --     (do let a ← simulateQ impl (pure (tr ⟨0,_⟩));   -- the message value `c`
    --         if stmt.sumcheck_target = eqTilde stmt.ctx.t_eval_point stmt.challenges * a
    --         then pure { …, final_constant := a }        -- accept: stmtOut carries `c`
    --         else pure { 0,0,0,0 })) s), x₁.1 = some x
    -- HONEST STOP (residual #1 — `simulateQ`/cast unpacking explodes): the inner
    -- `simulateQ impl (pure (tr ⟨0,_⟩))` resists every `simulateQ_pure`/`simulateQ_optionT_pure'`
    -- rewrite because the message term `tr ⟨0,_⟩` is wrapped in the opaque `pSpecFinalSumcheckStep`
    -- message-index cast machinery (`OracleSpec.Range`/`Sigma (MessageIdx …)`), the same
    -- "BaseFold cast alignment" wall noted in `QueryPhase.queryKnowledgeStateFunction.toFun_full`.
    -- HONEST STOP (residual #2 — genuine math obstruction in the reject branch): even with the
    -- plumbing finished, the `else` (reject) branch outputs the dummy `stmtOut = {0,0,0,0}`. From
    -- `hrel : (dummy, ()) ∈ finalSumcheckRelOut` one cannot reconstruct the goal's
    -- `finalSumcheckKStateProp 1` on the *real* `stmt`, since its `sumcheckFinalCheck`
    -- (`stmt.sumcheck_target = eqTilde · * c`) is exactly the verifier check that FAILED in this
    -- branch. Closing it requires proving the dummy `{0,0,0,0}` is not in `finalSumcheckRelOut`
    -- (i.e. `¬ finalNonDoomedFoldingProp ({0,0,0,0}, oStmt)`), which is NOT true in general (zero
    -- challenges can trigger the bad-event disjunct). This is the same unsolved `if`-branch case
    -- split flagged in the sibling `RingSwitching.…finalSumcheck…toFun_full` (left open there too).
    sorry

/-- Round-by-round knowledge soundness for the final sumcheck step -/
theorem finalSumcheckOracleVerifier_rbrKnowledgeSoundness [Fintype L] {σ : Type}
    (init : ProbComp σ) (impl : QueryImpl []ₒ (StateT σ ProbComp)) :
    (finalSumcheckVerifier 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate)).rbrKnowledgeSoundness init impl
      (relIn := roundRelation 𝔽q β (ϑ := ϑ) 
        (mp := BBF_SumcheckMultiplierParam) (Fin.last ℓ))
      (relOut := finalSumcheckRelOut 𝔽q β (ϑ := ϑ) (h_ℓ_add_R_rate := h_ℓ_add_R_rate))
      (rbrKnowledgeError := finalSumcheckKnowledgeError) := by
  use FinalSumcheckWit (L := L) 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (ℓ := ℓ)
  use finalSumcheckRbrExtractor 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
  use finalSumcheckKnowledgeStateFunction 𝔽q β (ϑ := ϑ) (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
     init impl
  intro stmtIn witIn prover j
  exact absurd j.2 (by simp [pSpecFinalSumcheckStep])

end FinalSumcheckStep
end
end Binius.BinaryBasefold.CoreInteraction

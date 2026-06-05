/-
Copyright (c) 2025 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chung Thai Nguyen, Quang Dao
-/

import ArkLib.ProofSystem.Binius.BinaryBasefold.Steps
import ArkLib.OracleReduction.Composition.Sequential.Append

/-!
## Binary Basefold Core Interaction Phase

This module contains the core interaction phase of the Binary Basefold IOP,
which combines, where both sumcheck and codeword folding occur in each round.

There are ℓ rounds in the core interaction phase, so there are ℓ + 1 states.
The i'th round receives the state i as input and outputs state i+1.

We define `(P, V)` as the following IOP, in which both parties have the common input
`[f], s ∈ L`, and `(r_0, ..., r_{ℓ-1}) ∈ L^ℓ`, and P has the further input
`t(X_0, ..., X_{ℓ-1}) ∈ L[X_0, ..., X_{ℓ-1}]^≤1`.

- P writes `h(X) := t(X) * eqTilde(r_0, ..., r_{ℓ-1}, X_0, ..., X_{ℓ-1})`.
- P and V both abbreviate `f^(0) := f` and `s_0 := s`, and execute the following loop:

  for `i in {0, ..., ℓ-1}` do
    P sends V the polynomial `h_i(X) := Σ_{w ∈ B_{ℓ-i-1}} h(r'_0, ..., r'_{i-1}, X, w_0, ...,
    w_{ℓ-i-2})`.
    V requires `s_i ?= h_i(0) + h_i(1)`. V samples `r'_i ← L`, sets `s_{i+1} := h_i(r'_i)`, and
    sends P `r'_i`.
    P defines `f^(i+1): S^(i+1) → L` as the function `fold(f^(i), r'_i)` of Definition 4.6.
    if `i+1 < ℓ` and `ϑ | i+1` then
      P submits (submit, ℓ+R-i-1, f^(i+1)) to the oracle `F_Vec^L`

- P sends V the final constant `c := f^(ℓ)(0, ..., 0)`
- V verifies: `s_ℓ = eqTilde(r, r') * c`
=> `c` should be equal to `t(r'_0, ..., r'_{ℓ-1})`
-/
namespace Binius.BinaryBasefold.CoreInteraction

noncomputable section
open OracleSpec OracleComp ProtocolSpec Finset AdditiveNTT Polynomial MvPolynomial
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

section ComponentReductions
variable {Context : Type} {mp : SumcheckMultiplierParam L ℓ Context} -- Sumcheck context

section FoldRelayRound -- foldRound + relay

@[reducible]
def foldRelayOracleVerifier (i : Fin ℓ)
    (hNCR : ¬ isCommitmentRound ℓ ϑ i) :
  OracleVerifier []ₒ
    (StmtIn := Statement (L := L) Context i.castSucc)
    (OStmtIn := OracleStatement 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) ϑ i.castSucc)
    (StmtOut := Statement (L := L) Context i.succ)
    (OStmtOut := OracleStatement 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) ϑ i.succ)
    (pSpec := pSpecFoldRelay (L:=L)) :=
  OracleVerifier.append
        (pSpec₁ := pSpecFold (L:=L))
    (pSpec₂ := pSpecRelay)
    (foldOracleVerifier 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) i)
    (relayOracleVerifier 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) i hNCR)

@[reducible]
def foldRelayOracleReduction (i : Fin ℓ)
    (hNCR : ¬ isCommitmentRound ℓ ϑ i) :
  OracleReduction []ₒ
    (StmtIn := Statement (L := L) Context i.castSucc)
    (OStmtIn := OracleStatement 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) ϑ i.castSucc)
    (WitIn := Witness (L := L) 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (ℓ:=ℓ) i.castSucc)
    (StmtOut := Statement (L := L) Context i.succ)
    (OStmtOut := OracleStatement 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) ϑ i.succ)
    (WitOut := Witness (L := L) 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (ℓ:=ℓ) i.succ)
    (pSpec := pSpecFoldRelay (L:=L)) :=
  OracleReduction.append
    (pSpec₁ := pSpecFold (L:=L))
    (pSpec₂ := pSpecRelay)
        (foldOracleReduction 𝔽q β (ϑ:=ϑ) (h_ℓ_add_R_rate := h_ℓ_add_R_rate) i)
    (relayOracleReduction 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) i hNCR)

/-- `foldRelayOracleVerifier` is `@[reducible]`-defined as `OracleVerifier.append` of the fold-step
and relay-step verifiers, whose appended message interface is exactly
`instOracleInterfaceMessageAppend` (= the registered interface of `pSpecFoldRelay`). Both leaf
verifiers are `AppendCoherent` (Steps.lean), so the composite is by `AppendCoherent.append`; we expose
it as a named instance so type-class synthesis at the `seqCompose` sites need not unfold the
`@[reducible]` definition. -/
instance instFoldRelayOracleVerifierAppendCoherent (i : Fin ℓ) (hNCR : ¬ isCommitmentRound ℓ ϑ i) :
    OracleVerifier.Append.AppendCoherent
      (foldRelayOracleVerifier 𝔽q β (ϑ := ϑ) (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
        (Context := Context) i hNCR) :=
  inferInstanceAs (OracleVerifier.Append.AppendCoherent
    (OracleVerifier.append
      (foldOracleVerifier 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) i)
      (relayOracleVerifier 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) i hNCR)))

/-- The reduction-level analogue: `(foldRelayOracleReduction …).verifier` is definitionally the
above composite verifier, so it inherits `AppendCoherent`. -/
instance instFoldRelayOracleReductionAppendCoherent (i : Fin ℓ)
    (hNCR : ¬ isCommitmentRound ℓ ϑ i) :
    OracleVerifier.Append.AppendCoherent
      (foldRelayOracleReduction 𝔽q β (ϑ := ϑ) (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
        (Context := Context) i hNCR).verifier :=
  inferInstanceAs (OracleVerifier.Append.AppendCoherent
    (OracleVerifier.append
      (foldOracleVerifier 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) i)
      (relayOracleVerifier 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) i hNCR)))


variable {σ : Type} {init : ProbComp σ} {impl : QueryImpl []ₒ (StateT σ ProbComp)}

/-- Perfect completeness of the non-commitment round reduction follows by append composition
    of the fold-round and the transfer-round reductions. -/
theorem foldRelayOracleReduction_perfectCompleteness
     (i : Fin ℓ) (hNCR : ¬ isCommitmentRound ℓ ϑ i) :
  OracleReduction.perfectCompleteness
    (pSpec := pSpecFoldRelay (L:=L))
    (relIn := roundRelation (mp := mp) 𝔽q β (ϑ:=ϑ)
      (h_ℓ_add_R_rate := h_ℓ_add_R_rate) i.castSucc)
    (relOut := roundRelation (mp := mp) 𝔽q β (ϑ:=ϑ)
      (h_ℓ_add_R_rate := h_ℓ_add_R_rate) i.succ)
    (oracleReduction := foldRelayOracleReduction 𝔽q β (ϑ:=ϑ) (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
       i hNCR) (init := init) (impl := impl) := by
  unfold foldRelayOracleReduction pSpecFoldRelay
  exact OracleReduction.append_perfectCompleteness _ _
    (foldOracleReduction_perfectCompleteness 𝔽q β i)
    (relayOracleReduction_perfectCompleteness 𝔽q β i hNCR)

/-- RBR Knowledge Soundness of the non-commitment round verifier via append composition
    of fold-round and transfer-round RBR KS. -/
theorem foldRelayOracleVerifier_rbrKnowledgeSoundness
    (i : Fin ℓ) (hNCR : ¬ isCommitmentRound ℓ ϑ i) :
    (foldRelayOracleVerifier 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) i hNCR).rbrKnowledgeSoundness
      init impl
      (relIn := roundRelation 𝔽q β (ϑ:=ϑ) (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
         i.castSucc (mp := mp))
      (relOut := roundRelation 𝔽q β (ϑ:=ϑ) (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
         i.succ (mp := mp))
      (rbrKnowledgeError := fun m => foldKnowledgeError 𝔽q β (ϑ:=ϑ)
        (h_ℓ_add_R_rate := h_ℓ_add_R_rate) i ⟨m, by
        match m with
        | ⟨0, h0⟩ => nomatch h0
        | ⟨1, h1⟩ => rfl
      ⟩) := by
  unfold foldRelayOracleVerifier pSpecFoldRelay
  suffices h : OracleVerifier.rbrKnowledgeSoundness init impl (roundRelation 𝔽q β i.castSucc)
      (roundRelation 𝔽q β i.succ)
      ((foldOracleVerifier 𝔽q β i).append (relayOracleVerifier 𝔽q β i hNCR))
      (Sum.elim (foldKnowledgeError 𝔽q β (ϑ := ϑ) (h_ℓ_add_R_rate := h_ℓ_add_R_rate) i)
        relayKnowledgeError ∘ ChallengeIdx.sumEquiv.symm) by
    convert h using 1
    funext m
    simp only [Function.comp, ChallengeIdx.sumEquiv, Equiv.symm, Equiv.coe_fn_mk]
    split
    · congr 1; ext; simp
    · omega
  exact OracleVerifier.append_rbrKnowledgeSoundness _ _
    (foldOracleVerifier_rbrKnowledgeSoundness 𝔽q β i)
    (relayOracleVerifier_rbrKnowledgeSoundness 𝔽q β i hNCR)

end FoldRelayRound -- foldRound + relay

section FoldCommitRound -- foldRound + commit

@[reducible]
def foldCommitOracleVerifier (i : Fin ℓ) (hCR : isCommitmentRound ℓ ϑ i) :
  OracleVerifier []ₒ
    (StmtIn := Statement (L := L) Context i.castSucc)
    (OStmtIn := OracleStatement 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) ϑ i.castSucc)
    (StmtOut := Statement (L := L) Context i.succ)
    (OStmtOut := OracleStatement 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) ϑ i.succ)
    (pSpec := pSpecFoldCommit 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) i) :=
    OracleVerifier.append (oSpec:=[]ₒ)
      (pSpec₁ := pSpecFold (L:=L))
      (pSpec₂ := pSpecCommit 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) i)
      (V₁ := foldOracleVerifier 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) i)
      (V₂ := commitOracleVerifier 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) i hCR)

@[reducible]
def foldCommitOracleReduction (i : Fin ℓ)
    (hCR : isCommitmentRound ℓ ϑ i) :
  OracleReduction []ₒ
    (StmtIn := Statement (L := L) Context i.castSucc)
    (OStmtIn := OracleStatement 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) ϑ i.castSucc)
    (WitIn := Witness (L := L) 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (ℓ:=ℓ) i.castSucc)
    (StmtOut := Statement (L := L) Context i.succ)
    (OStmtOut := OracleStatement 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) ϑ i.succ)
    (WitOut := Witness (L := L) 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (ℓ:=ℓ) i.succ)
    (pSpec := pSpecFoldCommit 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) i) :=
  OracleReduction.append (oSpec:=[]ₒ)
    (pSpec₁ := pSpecFold (L:=L))
    (pSpec₂ := pSpecCommit 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) i)
    (R₁ := foldOracleReduction 𝔽q β (ϑ:=ϑ) (h_ℓ_add_R_rate := h_ℓ_add_R_rate) i)
    (R₂ := commitOracleReduction 𝔽q β (ϑ:=ϑ) (h_ℓ_add_R_rate := h_ℓ_add_R_rate) i hCR)

/-- `foldCommitOracleVerifier` is the `OracleVerifier.append` of the fold-step and commit-step
verifiers; both leaves are `AppendCoherent` (Steps.lean, the commit case using the point-query
codeword interface), so the composite is by `AppendCoherent.append`.  Exposed as a named instance so
type-class synthesis at the block-level `seqCompose`/`append` sites need not unfold the `@[reducible]`
definition. -/
instance instFoldCommitOracleVerifierAppendCoherent (i : Fin ℓ) (hCR : isCommitmentRound ℓ ϑ i) :
    OracleVerifier.Append.AppendCoherent
      (foldCommitOracleVerifier 𝔽q β (ϑ := ϑ) (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
        (Context := Context) i hCR) :=
  inferInstanceAs (OracleVerifier.Append.AppendCoherent
    (OracleVerifier.append
      (foldOracleVerifier 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) i)
      (commitOracleVerifier 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) i hCR)))

instance instFoldCommitOracleReductionAppendCoherent (i : Fin ℓ) (hCR : isCommitmentRound ℓ ϑ i) :
    OracleVerifier.Append.AppendCoherent
      (foldCommitOracleReduction 𝔽q β (ϑ := ϑ) (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
        (Context := Context) i hCR).verifier :=
  inferInstanceAs (OracleVerifier.Append.AppendCoherent
    (OracleVerifier.append
      (foldOracleVerifier 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) i)
      (commitOracleVerifier 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) i hCR)))

variable {σ : Type} {init : ProbComp σ} {impl : QueryImpl []ₒ (StateT σ ProbComp)}

/-- Perfect completeness for Fold+Commitment block by append composition. -/
theorem foldCommitOracleReduction_perfectCompleteness
    (i : Fin ℓ) (hCR : isCommitmentRound ℓ ϑ i) :
    OracleReduction.perfectCompleteness
      (pSpec := pSpecFoldCommit 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) i)
      (relIn := roundRelation (mp := mp) 𝔽q β (ϑ:=ϑ)
        (h_ℓ_add_R_rate := h_ℓ_add_R_rate) i.castSucc)
      (relOut := roundRelation (mp := mp) 𝔽q β (ϑ:=ϑ)
        (h_ℓ_add_R_rate := h_ℓ_add_R_rate) i.succ)
      (oracleReduction := foldCommitOracleReduction 𝔽q β (ϑ:=ϑ)
        (h_ℓ_add_R_rate := h_ℓ_add_R_rate) i hCR) (init := init) (impl := impl) := by
  unfold foldCommitOracleReduction pSpecFoldCommit
  exact OracleReduction.append_perfectCompleteness _ _
    (foldOracleReduction_perfectCompleteness 𝔽q β i)
    (commitOracleReduction_perfectCompleteness 𝔽q β i hCR)

/-- RBR KS for Fold+Commitment block by append composition. -/
theorem foldCommitOracleVerifier_rbrKnowledgeSoundness
    (i : Fin ℓ) (hCR : isCommitmentRound ℓ ϑ i) :
    (foldCommitOracleVerifier 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) i hCR).rbrKnowledgeSoundness
      init impl
      (relIn := roundRelation (mp := mp) 𝔽q β (ϑ:=ϑ)
        (h_ℓ_add_R_rate := h_ℓ_add_R_rate) i.castSucc)
      (relOut := roundRelation (mp := mp) 𝔽q β (ϑ:=ϑ)
        (h_ℓ_add_R_rate := h_ℓ_add_R_rate) i.succ)
      (rbrKnowledgeError := fun _ => foldKnowledgeError 𝔽q β (ϑ:=ϑ)
        (h_ℓ_add_R_rate := h_ℓ_add_R_rate) i ⟨1, by rfl⟩
      ) := by
  unfold foldCommitOracleVerifier pSpecFoldCommit
  have herr : (fun _ => foldKnowledgeError 𝔽q β (ϑ := ϑ) (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
      i ⟨1, by rfl⟩) =
      (Sum.elim (foldKnowledgeError 𝔽q β (ϑ := ϑ) (h_ℓ_add_R_rate := h_ℓ_add_R_rate) i)
        (commitKnowledgeError 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate)) ∘
        (ChallengeIdx.sumEquiv (pSpec₁ := pSpecFold (L := L))
          (pSpec₂ := pSpecCommit 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) i)).symm) := by
    funext m
    simp only [Function.comp, ChallengeIdx.sumEquiv, Equiv.symm]
    dsimp
    split
    · simp [foldKnowledgeError]
    · next hlt =>
      exfalso
      have hv := m.1.isLt
      have hp := m.2
      simp only [ProtocolSpec.append, Fin.vappend_eq_append, Fin.append, Fin.addCases,
        Direction.not_P_to_V_eq_V_to_P] at hp
      split at hp <;> simp_all <;> omega
  rw [herr]
  exact OracleVerifier.append_rbrKnowledgeSoundness _ _
    (foldOracleVerifier_rbrKnowledgeSoundness 𝔽q β i)
    (commitOracleVerifier_rbrKnowledgeSoundness 𝔽q β i hCR)

end FoldCommitRound

section IteratedSumcheckFoldComposition
/-!
## Composed Components (SumcheckFold)

Iterative composition across ℓ rounds: for each i, use Fold+Commitment when
`isCommitmentRound ℓ ϑ i`, otherwise use Fold+Relay. We rely on the fixed-size
block verifiers/reductions built earlier to avoid dependent casts.
-/
section composedOracleVerifiers
def nonLastBlockOracleVerifier (bIdx : Fin (ℓ / ϑ - 1)) :
    OracleVerifier []ₒ
      (StmtIn := Statement (L := L) (ℓ := ℓ) Context ⟨bIdx * ϑ, by
        have := bIdx_mul_ϑ_add_x_lt_ℓ_succ (ℓ := ℓ) (ϑ := ϑ) bIdx 0 (hx := Nat.zero_le _); omega⟩)
      (OStmtIn := OracleStatement 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) ϑ ⟨bIdx * ϑ, by
        have := bIdx_mul_ϑ_add_x_lt_ℓ_succ (ℓ := ℓ) (ϑ := ϑ) bIdx 0 (hx := Nat.zero_le _); omega⟩)
      (StmtOut := Statement (L := L) Context ⟨(bIdx + 1) * ϑ, bIdx_succ_mul_ϑ_lt_ℓ_succ bIdx⟩)
      (OStmtOut := OracleStatement 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) ϑ
        ⟨(bIdx + 1) * ϑ, bIdx_succ_mul_ϑ_lt_ℓ_succ bIdx⟩)
      (pSpec := pSpecFullNonLastBlock 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) bIdx) :=
  let stmt : Fin (ϑ - 1 + 1) → Type :=
    fun i => Statement (L := L) Context ⟨bIdx * ϑ + i, bIdx_mul_ϑ_add_i_cast_lt_ℓ_succ bIdx i⟩
  let oStmt := fun i: Fin (ϑ - 1 + 1) => OracleStatement 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) ϑ
    ⟨bIdx * ϑ + i, bIdx_mul_ϑ_add_i_cast_lt_ℓ_succ bIdx i⟩
  let firstFoldRelayRoundsOracleVerifier :=
    OracleVerifier.seqCompose (oSpec := []ₒ)
      (Stmt := stmt)
      (OStmt := oStmt)
      (pSpec := fun i => pSpecFoldRelay (L:=L))
      (V := fun i =>
        foldRelayOracleVerifier (L:=L) 𝔽q β (ϑ:=ϑ) (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
           ⟨bIdx * ϑ + i, bIdx_mul_ϑ_add_i_fin_ℓ_pred_lt_ℓ bIdx i⟩
           (isNeCommitmentRound (r:=r) (ℓ:=ℓ) (𝓡:=𝓡) (ϑ:=ϑ) bIdx (x:=i.val) (hx:=by omega)))
      (coh := fun i =>
        instFoldRelayOracleVerifierAppendCoherent (L:=L) 𝔽q β (ϑ:=ϑ)
          (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (Context := Context)
          ⟨bIdx * ϑ + i, bIdx_mul_ϑ_add_i_fin_ℓ_pred_lt_ℓ bIdx i⟩
          (isNeCommitmentRound (r:=r) (ℓ:=ℓ) (𝓡:=𝓡) (ϑ:=ϑ) bIdx (x:=i.val) (hx:=by omega)))
  let h1 : ↑bIdx * ϑ + (ϑ - 1) < ℓ := by
    let fv: Fin ϑ := ⟨ϑ - 1, by
      have h := NeZero.one_le (n:=ϑ)
      exact Nat.sub_one_lt_of_lt h
    ⟩
    have h_eq: fv.val = ϑ - 1 := by rfl
    change ↑bIdx * ϑ + fv.val < ℓ + 0
    apply bIdx_mul_ϑ_add_i_lt_ℓ_succ
  let h1_succ : ↑bIdx * ϑ + (ϑ - 1) < ℓ + 1 := by omega

  let lastOracleVerifier := foldCommitOracleVerifier 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
     (i := ⟨bIdx * ϑ + (ϑ - 1), h1⟩)
    (hCR:=isCommitmentRoundOfNonLastBlock (𝓡:=𝓡) (r:=r) bIdx)

  -- the fold-relay prefix, re-indexed (`bIdx*ϑ+0 = bIdx*ϑ` is `rfl`, `Fin.last (ϑ-1)` endpoint)
  -- so the appended `Stmt₁/Stmt₂` line up.  Because the endpoints are *definitionally* equal
  -- (`Nat.add … 0` reduces, `Fin.mk` proof-irrelevant), we transport by `exact` (no cast), so
  -- `V₁`'s `AppendCoherent` is literally the raw seqCompose's and synthesizes directly.
  let V₁ : OracleVerifier []ₒ
      (StmtIn := Statement (L := L) (ℓ := ℓ) Context ⟨bIdx * ϑ, by
        apply Nat.lt_trans (m:=ℓ) (h₁:=by
          change bIdx.val * ϑ + (⟨0, by exact Nat.pos_of_neZero ϑ⟩: Fin (ϑ)).val < ℓ + 0
          apply bIdx_mul_ϑ_add_i_lt_ℓ_succ
        ) (by omega)⟩)
      (OStmtIn := OracleStatement 𝔽q β ϑ ⟨bIdx * ϑ, Nat.lt_of_add_right_lt h1_succ⟩)
      (StmtOut := Statement (L := L) Context ⟨bIdx * ϑ + (ϑ - 1), h1_succ⟩)
      (OStmtOut := OracleStatement 𝔽q β ϑ ⟨bIdx * ϑ + (ϑ - 1), h1_succ⟩)
      (pSpec := pSpecFoldRelaySequence (L:=L) (n:=ϑ - 1)) :=
    firstFoldRelayRoundsOracleVerifier
  letI V₁coh : OracleVerifier.Append.AppendCoherent V₁ :=
    OracleVerifier.seqCompose_appendCoherent stmt oStmt
      (fun i => by
        have nHCR : ¬ isCommitmentRound ℓ ϑ ⟨bIdx * ϑ + i, bIdx_mul_ϑ_add_i_fin_ℓ_pred_lt_ℓ bIdx i⟩
          := isNeCommitmentRound (r:=r) (ℓ:=ℓ) (𝓡:=𝓡) (ϑ:=ϑ) bIdx (x:=i.val) (hx:=by omega)
        exact foldRelayOracleVerifier (L:=L) 𝔽q β (ϑ:=ϑ) (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
           ⟨bIdx * ϑ + i, bIdx_mul_ϑ_add_i_fin_ℓ_pred_lt_ℓ bIdx i⟩ nHCR)
      (coh := fun i =>
        instFoldRelayOracleVerifierAppendCoherent (L:=L) 𝔽q β (ϑ:=ϑ)
          (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (Context := Context)
          ⟨bIdx * ϑ + i, bIdx_mul_ϑ_add_i_fin_ℓ_pred_lt_ℓ bIdx i⟩
          (isNeCommitmentRound (r:=r) (ℓ:=ℓ) (𝓡:=𝓡) (ϑ:=ϑ) bIdx (x:=i.val) (hx:=by omega)))

  -- the fold-commit block, with output endpoint realigned `bIdx*ϑ+(ϑ-1)+1 = (bIdx+1)*ϑ` by `rw!`;
  -- its `AppendCoherent` is the (transported) `instFoldCommitOracleVerifierAppendCoherent`.
  let h : ↑bIdx * ϑ + (ϑ - 1) + 1 = (↑bIdx + 1) * ϑ := by
    rw [Nat.add_assoc, Nat.sub_add_cancel (by exact NeZero.one_le)]
    rw [Nat.add_mul, Nat.one_mul]
  let V₂ : OracleVerifier []ₒ
      (StmtIn := Statement (L := L) Context ⟨bIdx * ϑ + (ϑ - 1), h1_succ⟩)
      (OStmtIn := OracleStatement 𝔽q β ϑ ⟨bIdx * ϑ + (ϑ - 1), h1_succ⟩)
      (StmtOut := Statement (L := L) Context ⟨(bIdx + 1) * ϑ, bIdx_succ_mul_ϑ_lt_ℓ_succ bIdx⟩)
      (OStmtOut := OracleStatement 𝔽q β ϑ ⟨(bIdx + 1) * ϑ, bIdx_succ_mul_ϑ_lt_ℓ_succ bIdx⟩)
      (pSpec := pSpecFoldCommit 𝔽q β ⟨bIdx * ϑ + (ϑ - 1), h1⟩) := by
    have lastOV := lastOracleVerifier
    simp only [Fin.succ_mk, Fin.castSucc_mk] at lastOV
    rw! (castMode := .all) [h] at lastOV
    exact lastOV
  letI V₂coh : OracleVerifier.Append.AppendCoherent V₂ := by
    show OracleVerifier.Append.AppendCoherent
      (by have lastOV := lastOracleVerifier
          simp only [Fin.succ_mk, Fin.castSucc_mk] at lastOV
          rw! (castMode := .all) [h] at lastOV; exact lastOV)
    rw! (castMode := .all) [← h]
    exact instFoldCommitOracleVerifierAppendCoherent 𝔽q β (ϑ := ϑ)
      (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (Context := Context)
      ⟨bIdx * ϑ + (ϑ - 1), h1⟩ (isCommitmentRoundOfNonLastBlock (𝓡:=𝓡) (r:=r) bIdx)

  let nonLastBlockOracleVerifier :=
    OracleVerifier.append (oSpec:=[]ₒ)
      (Stmt₃:=Statement (L := L) Context ⟨(bIdx + 1) * ϑ, bIdx_succ_mul_ϑ_lt_ℓ_succ bIdx⟩)
      (OStmt₃:=OracleStatement 𝔽q β ϑ ⟨(bIdx + 1) * ϑ, bIdx_succ_mul_ϑ_lt_ℓ_succ bIdx⟩)
      (pSpec₂:=pSpecFoldCommit 𝔽q β ⟨bIdx * ϑ + (ϑ - 1), h1⟩)
      (V₁:=V₁)
      (V₂:=V₂)

  nonLastBlockOracleVerifier

instance instNonLastBlockOracleVerifierAppendCoherent (bIdx : Fin (ℓ / ϑ - 1)) :
    OracleVerifier.Append.AppendCoherent
      (nonLastBlockOracleVerifier 𝔽q β (ϑ := ϑ) (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
        (Context := Context) bIdx) := by
  -- both leaves (`V₁` the fold-relay `seqCompose`, `V₂` the re-indexed fold-commit) carry local
  -- `AppendCoherent` instances inside the def; `unfold` exposes them and `infer_instance` assembles
  -- the composite via `AppendCoherent.append`.
  unfold nonLastBlockOracleVerifier
  infer_instance

def lastBlockOracleVerifier :=
  let bIdx := ℓ / ϑ - 1
  let stmt : Fin (ϑ + 1) → Type := fun i => Statement (L := L) (ℓ:=ℓ) Context
    ⟨bIdx * ϑ + i, by apply lastBlockIdx_mul_ϑ_add_x_lt_ℓ_succ (hx:=by omega)⟩
  let oStmt := fun i: Fin (ϑ + 1) => OracleStatement 𝔽q β ϑ
    ⟨bIdx * ϑ + i, by apply lastBlockIdx_mul_ϑ_add_x_lt_ℓ_succ (hx:=by omega)⟩
  let V: OracleVerifier []ₒ (StmtIn := Statement (L := L) (ℓ := ℓ) Context
      ⟨bIdx * ϑ, by apply lastBlockIdx_mul_ϑ_add_x_lt_ℓ_succ (x:=0) (hx:=by omega)⟩)
    (OStmtIn := OracleStatement 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) ϑ
      ⟨bIdx * ϑ, by apply lastBlockIdx_mul_ϑ_add_x_lt_ℓ_succ (x:=0) (hx:=by omega)⟩)
    (StmtOut := Statement (L := L) (ℓ := ℓ) Context (Fin.last ℓ))
    (OStmtOut := OracleStatement 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) ϑ (Fin.last ℓ))
    (pSpec := pSpecLastBlock (L:=L) (ϑ:=ϑ)) := by
    let cur := OracleVerifier.seqCompose (oSpec := []ₒ)
      (Stmt := stmt)
      (OStmt := oStmt)
      (pSpec := fun i => pSpecFoldRelay (L:=L))
      (V := fun i =>
        foldRelayOracleVerifier (L:=L) 𝔽q β (ϑ:=ϑ) (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
           ⟨bIdx * ϑ + i, lastBlockIdx_mul_ϑ_add_fin_lt_ℓ i⟩
           (lastBlockIdx_isNeCommitmentRound i))
      (coh := fun i =>
        instFoldRelayOracleVerifierAppendCoherent (L:=L) 𝔽q β (ϑ:=ϑ)
          (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (Context := Context)
          ⟨bIdx * ϑ + i, lastBlockIdx_mul_ϑ_add_fin_lt_ℓ i⟩
          (lastBlockIdx_isNeCommitmentRound i))
    simp [stmt, oStmt, Nat.zero_mod] at cur
    have h: (⟨bIdx * ϑ + ϑ, by apply lastBlockIdx_mul_ϑ_add_x_lt_ℓ_succ (hx:=by omega)⟩)
      = Fin.last ℓ := by
      apply Fin.eq_of_val_eq
      simp only [Fin.val_last]; dsimp [bIdx];
      rw [Nat.sub_mul, one_mul, Nat.div_mul_cancel (hdiv.out)]
      rw [Nat.sub_add_cancel (by exact Nat.le_of_dvd (h:=by exact Nat.pos_of_neZero ℓ) (hdiv.out))]
    rw! [h] at cur
    exact cur
  V

@[reducible]
def sumcheckFoldOracleVerifier :=
  let stmt : Fin (ℓ / ϑ - 1 + 1) → Type :=
    fun i => Statement (L := L) (ℓ := ℓ) Context ⟨i * ϑ, blockIdx_mul_ϑ_lt_ℓ_succ i⟩
  let oStmt :=
    fun i: Fin (ℓ / ϑ - 1 + 1) => OracleStatement 𝔽q β ϑ ⟨i * ϑ, blockIdx_mul_ϑ_lt_ℓ_succ i⟩
  let nonLastBlocksOracleVerifier :=
  OracleVerifier.seqCompose (oSpec := []ₒ)
      (Stmt := stmt)
      (OStmt := oStmt)
      (pSpec := fun (bIdx: Fin (ℓ / ϑ - 1)) => pSpecFullNonLastBlock 𝔽q β bIdx)
      (V := fun bIdx => nonLastBlockOracleVerifier (L:=L) 𝔽q β (ϑ:=ϑ) (bIdx:=bIdx))

  let lastOracleVerifier := lastBlockOracleVerifier 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
    

  let sumcheckFoldOV: OracleVerifier []ₒ
    (StmtIn := Statement (L := L) (ℓ := ℓ) Context 0)
    (OStmtIn := OracleStatement 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) ϑ 0)
    (StmtOut := Statement (L := L) (ℓ := ℓ) Context (Fin.last ℓ))
    (OStmtOut := OracleStatement 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) ϑ (Fin.last ℓ))
    (pSpec := pSpecSumcheckFold 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate))
     := by
    let res := OracleVerifier.append (oSpec:=[]ₒ)
      (V₁:=by
        exact nonLastBlocksOracleVerifier
      )
      (V₂:=by
        exact lastOracleVerifier
      )
    simp [stmt, oStmt, Nat.zero_mod] at res
    unfold pSpecSumcheckFold pSpecNonLastBlocks
    convert res
    all_goals simp
    all_goals (congr 1; ext; simp)

  sumcheckFoldOV

end composedOracleVerifiers

section composedOracleRedutions

def nonLastBlockOracleReduction (bIdx : Fin (ℓ / ϑ - 1)) :=
  let stmt : Fin (ϑ - 1 + 1) → Type :=
    fun i => Statement (L := L) (ℓ := ℓ) Context ⟨bIdx * ϑ + i, bIdx_mul_ϑ_add_i_cast_lt_ℓ_succ bIdx i⟩
  let oStmt := fun i: Fin (ϑ - 1 + 1) =>
    OracleStatement 𝔽q β ϑ ⟨bIdx * ϑ + i, bIdx_mul_ϑ_add_i_cast_lt_ℓ_succ bIdx i⟩
  let wit := fun i: Fin (ϑ - 1 + 1) =>
    Witness (L := L) 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (ℓ:=ℓ)
      ⟨bIdx * ϑ + i, bIdx_mul_ϑ_add_i_cast_lt_ℓ_succ bIdx i⟩
  let firstFoldRelayRoundsOracleReduction :=
    OracleReduction.seqCompose (oSpec := []ₒ)
      (Stmt := stmt)
      (OStmt := oStmt)
      (Wit := wit)
      (pSpec := fun i => pSpecFoldRelay (L:=L))
      (R := fun i => by
        have nHCR : ¬ isCommitmentRound ℓ ϑ ⟨bIdx * ϑ + i, bIdx_mul_ϑ_add_i_fin_ℓ_pred_lt_ℓ bIdx i⟩
          := isNeCommitmentRound (r:=r) (ℓ:=ℓ) (𝓡:=𝓡) (ϑ:=ϑ) bIdx (x:=i.val) (hx:=by omega)
        exact foldRelayOracleReduction (L:=L) 𝔽q β (ϑ:=ϑ) (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
           (i:=⟨bIdx * ϑ + i, bIdx_mul_ϑ_add_i_fin_ℓ_pred_lt_ℓ bIdx i⟩) nHCR
      )

  let h1 : ↑bIdx * ϑ + (ϑ - 1) < ℓ := by
    let fv: Fin ϑ := ⟨ϑ - 1, by
      have h := NeZero.one_le (n:=ϑ)
      exact Nat.sub_one_lt_of_lt h
    ⟩
    have h_eq: fv.val = ϑ - 1 := by rfl
    change ↑bIdx * ϑ + fv.val < ℓ + 0
    apply bIdx_mul_ϑ_add_i_lt_ℓ_succ
  let h1_succ : ↑bIdx * ϑ + (ϑ - 1) < ℓ + 1 := by omega

  let lastOracleReduction := foldCommitOracleReduction 𝔽q β (ϑ:=ϑ)
    (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
     (i := ⟨bIdx * ϑ + (ϑ - 1), h1⟩) (hCR:=isCommitmentRoundOfNonLastBlock (𝓡:=𝓡) (r:=r) bIdx)

  let nonLastBlockOracleReduction :=
    OracleReduction.append (oSpec:=[]ₒ)
      (Stmt₁:=Statement (L := L) (ℓ := ℓ) Context ⟨bIdx * ϑ, by
        apply Nat.lt_trans (m:=ℓ) (h₁:=by
          change bIdx.val * ϑ + (⟨0, by exact Nat.pos_of_neZero ϑ⟩: Fin (ϑ)).val < ℓ + 0
          apply bIdx_mul_ϑ_add_i_lt_ℓ_succ
        ) (by omega)
      ⟩)
      (Stmt₂:=Statement (L := L) (ℓ := ℓ) Context ⟨bIdx * ϑ + (ϑ - 1), h1_succ⟩)
      (Stmt₃:=Statement (L := L) (ℓ := ℓ) Context ⟨(bIdx + 1) * ϑ, bIdx_succ_mul_ϑ_lt_ℓ_succ bIdx⟩)
      (Wit₁:=Witness (L := L) 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (ℓ:=ℓ) ⟨bIdx * ϑ, by
        apply Nat.lt_trans (m:=ℓ) (h₁:=by
          change bIdx.val * ϑ + (⟨0, by exact Nat.pos_of_neZero ϑ⟩: Fin (ϑ)).val < ℓ + 0
          apply bIdx_mul_ϑ_add_i_lt_ℓ_succ
        ) (by omega)
      ⟩)
      (Wit₂:=Witness (L := L) 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (ℓ:=ℓ)
        ⟨bIdx * ϑ + (ϑ - 1), h1_succ⟩)
      (Wit₃:=Witness (L := L) 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (ℓ:=ℓ)
        ⟨(bIdx + 1) * ϑ, bIdx_succ_mul_ϑ_lt_ℓ_succ bIdx⟩)
      (OStmt₁:=OracleStatement 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) ϑ ⟨bIdx * ϑ, by
        apply Nat.lt_trans (m:=ℓ) (h₁:=by
          change bIdx.val * ϑ + (⟨0, by exact Nat.pos_of_neZero ϑ⟩: Fin (ϑ)).val < ℓ + 0
          apply bIdx_mul_ϑ_add_i_lt_ℓ_succ
        ) (by omega)
      ⟩)
      (OStmt₂:=OracleStatement 𝔽q β ϑ ⟨bIdx * ϑ + (ϑ - 1), h1_succ⟩)
      (OStmt₃:=OracleStatement 𝔽q β ϑ ⟨(bIdx + 1) * ϑ, bIdx_succ_mul_ϑ_lt_ℓ_succ bIdx⟩)
      (pSpec₁:=pSpecFoldRelaySequence (L:=L) (n:=ϑ - 1))
      (pSpec₂:=pSpecFoldCommit 𝔽q β ⟨bIdx * ϑ + (ϑ - 1), h1⟩)
      (R₁:=by
        simp [stmt, oStmt, Nat.zero_mod] at firstFoldRelayRoundsOracleReduction
        exact firstFoldRelayRoundsOracleReduction
      )
      (R₂:=by
        simp at lastOracleReduction
        have h: ↑bIdx * ϑ + (ϑ - 1) + 1 = (↑bIdx + 1) * ϑ := by
          rw [Nat.add_assoc, Nat.sub_add_cancel (by exact NeZero.one_le)]
          rw [Nat.add_mul, Nat.one_mul]
        rw! (castMode:=.all) [h] at lastOracleReduction
        exact lastOracleReduction
      )

  nonLastBlockOracleReduction

def lastBlockOracleReduction :=
  let bIdx := ℓ / ϑ - 1
  let stmt : Fin (ϑ + 1) → Type := fun i => Statement (L := L) (ℓ := ℓ) Context
    ⟨bIdx * ϑ + i, by apply lastBlockIdx_mul_ϑ_add_x_lt_ℓ_succ (hx:=by omega)⟩
  let oStmt := fun i: Fin (ϑ + 1) => OracleStatement 𝔽q β ϑ
    ⟨bIdx * ϑ + i, by apply lastBlockIdx_mul_ϑ_add_x_lt_ℓ_succ (hx:=by omega)⟩
  let wit := fun i: Fin (ϑ + 1) => Witness (L := L) 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (ℓ:=ℓ)
    ⟨bIdx * ϑ + i, by apply lastBlockIdx_mul_ϑ_add_x_lt_ℓ_succ (hx:=by omega)⟩
  let V: OracleReduction []ₒ (StmtIn := Statement (L := L) (ℓ := ℓ) Context
    ⟨bIdx * ϑ, by apply lastBlockIdx_mul_ϑ_add_x_lt_ℓ_succ (x:=0) (hx:=by omega)⟩)
    (OStmtIn := OracleStatement 𝔽q β ϑ
      ⟨bIdx * ϑ, by apply lastBlockIdx_mul_ϑ_add_x_lt_ℓ_succ (x:=0) (hx:=by omega)⟩)
    (WitIn := Witness (L := L) 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (ℓ:=ℓ)
      ⟨bIdx * ϑ, by apply lastBlockIdx_mul_ϑ_add_x_lt_ℓ_succ (x:=0) (hx:=by omega)⟩)
    (StmtOut := Statement (L := L) (ℓ := ℓ) Context (Fin.last ℓ))
    (OStmtOut := OracleStatement 𝔽q β ϑ (Fin.last ℓ))
    (WitOut := Witness (L := L) 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (ℓ:=ℓ) (Fin.last ℓ))
    (pSpec := pSpecLastBlock (L:=L) (ϑ:=ϑ)) := by
      let cur := OracleReduction.seqCompose (oSpec := []ₒ)
        (Stmt := stmt)
        (OStmt := oStmt)
        (Wit := wit)
        (pSpec := fun i => pSpecFoldRelay (L:=L))
        (R := fun i => by
          have nHCR : ¬ isCommitmentRound ℓ ϑ ⟨bIdx * ϑ + i, lastBlockIdx_mul_ϑ_add_fin_lt_ℓ i⟩ :=
            lastBlockIdx_isNeCommitmentRound i
          exact foldRelayOracleReduction (L:=L) 𝔽q β (ϑ:=ϑ) (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
             (i:=⟨bIdx * ϑ + i, lastBlockIdx_mul_ϑ_add_fin_lt_ℓ i⟩) nHCR
        )
      simp [stmt, oStmt, wit, Nat.zero_mod] at cur
      have h: (⟨bIdx * ϑ + ϑ, by apply lastBlockIdx_mul_ϑ_add_x_lt_ℓ_succ (hx:=by omega)⟩)
        = Fin.last ℓ := by
        apply Fin.eq_of_val_eq
        simp only [Fin.val_last]; dsimp [bIdx];
        rw [Nat.sub_mul, one_mul, Nat.div_mul_cancel (hdiv.out)]
        rw [Nat.sub_add_cancel
          (by exact Nat.le_of_dvd (h:=by exact Nat.pos_of_neZero ℓ) (hdiv.out))]
      rw! [h] at cur
      exact cur
  V

@[reducible]
def sumcheckFoldOracleReduction :=
  let stmt : Fin (ℓ / ϑ - 1 + 1) → Type :=
    fun i => Statement (L := L) (ℓ := ℓ) Context ⟨i * ϑ, blockIdx_mul_ϑ_lt_ℓ_succ i⟩
  let oStmt := fun i: Fin (ℓ / ϑ - 1 + 1) =>
    OracleStatement 𝔽q β ϑ ⟨i * ϑ, blockIdx_mul_ϑ_lt_ℓ_succ i⟩
  let wit := fun i: Fin (ℓ / ϑ - 1 + 1) =>
    Witness (L := L) 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (ℓ:=ℓ)
      ⟨i * ϑ, blockIdx_mul_ϑ_lt_ℓ_succ i⟩
  let nonLastBlocksOracleReduction :=
  OracleReduction.seqCompose (oSpec := []ₒ)
      (Stmt := stmt)
      (OStmt := oStmt) (Wit := wit)
      (pSpec := fun (bIdx: Fin (ℓ / ϑ - 1)) => pSpecFullNonLastBlock 𝔽q β bIdx)
      (R := fun bIdx => nonLastBlockOracleReduction (L:=L) 𝔽q β (ϑ:=ϑ) (bIdx:=bIdx))

  let lastOracleReduction := lastBlockOracleReduction 𝔽q β (ϑ:=ϑ) 

  let coreInteractionOracleReduction: OracleReduction []ₒ
    (StmtIn := Statement (L := L) (ℓ := ℓ) Context 0)
    (OStmtIn := OracleStatement 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) ϑ 0)
    (WitIn := Witness (L := L) 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (ℓ:=ℓ) 0)
    (StmtOut := Statement (L := L) (ℓ:=ℓ) Context (Fin.last ℓ))
    (OStmtOut := OracleStatement 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) ϑ (Fin.last ℓ))
    (WitOut := Witness (L := L) 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (ℓ:=ℓ) (Fin.last ℓ))
    (pSpec := pSpecSumcheckFold 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate))
     := by
    let res := OracleReduction.append (oSpec:=[]ₒ)
      (R₁:=by
        exact nonLastBlocksOracleReduction
      )
      (R₂:=by
        exact lastOracleReduction
      )
    simp [stmt, oStmt, wit, Nat.zero_mod] at res
    unfold pSpecSumcheckFold pSpecNonLastBlocks
    convert res
    all_goals simp
    all_goals (congr 1; ext; simp)

  coreInteractionOracleReduction

end composedOracleRedutions

section SecurityProps

variable {σ : Type} {init : ProbComp σ} {impl : QueryImpl []ₒ (StateT σ ProbComp)}

set_option maxHeartbeats 1000000 in
/-- Perfect completeness of the literal `ϑ`-fold-relay `seqCompose` underlying the last block,
    stated at the untransported endpoint `Fin` value `⟨(ℓ/ϑ-1)*ϑ + k, _⟩`. This is the genuine
    mathematical content of the last block (`ϑ` honest fold-relay rounds chained); the only thing
    separating it from `lastBlockOracleReduction_perfectCompleteness` is the cosmetic endpoint
    re-indexing `⟨(ℓ/ϑ-1)*ϑ+ϑ, _⟩ = Fin.last ℓ` that the *definition* performs with `rw!`. -/
theorem lastBlock_seqCompose_perfectCompleteness :
      (OracleReduction.seqCompose (oSpec := []ₒ)
        (Stmt := fun i : Fin (ϑ + 1) => Statement (L := L) (ℓ := ℓ) Context
          ⟨(ℓ / ϑ - 1) * ϑ + i, by apply lastBlockIdx_mul_ϑ_add_x_lt_ℓ_succ (hx:=by omega)⟩)
        (OStmt := fun i : Fin (ϑ + 1) => OracleStatement 𝔽q β ϑ
          ⟨(ℓ / ϑ - 1) * ϑ + i, by apply lastBlockIdx_mul_ϑ_add_x_lt_ℓ_succ (hx:=by omega)⟩)
        (Wit := fun i : Fin (ϑ + 1) =>
          Witness (L := L) 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (ℓ:=ℓ)
            ⟨(ℓ / ϑ - 1) * ϑ + i, by apply lastBlockIdx_mul_ϑ_add_x_lt_ℓ_succ (hx:=by omega)⟩)
        (pSpec := fun _ => pSpecFoldRelay (L:=L))
        (R := fun i => by
          have nHCR : ¬ isCommitmentRound ℓ ϑ
              ⟨(ℓ / ϑ - 1) * ϑ + i, lastBlockIdx_mul_ϑ_add_fin_lt_ℓ i⟩ :=
            lastBlockIdx_isNeCommitmentRound i
          exact foldRelayOracleReduction (L:=L) 𝔽q β (ϑ:=ϑ) (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
             (i:=⟨(ℓ / ϑ - 1) * ϑ + i, lastBlockIdx_mul_ϑ_add_fin_lt_ℓ i⟩)
             nHCR)).perfectCompleteness
        init impl
        (roundRelation (mp := mp) 𝔽q β (ϑ:=ϑ) (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
          ⟨(ℓ / ϑ - 1) * ϑ + (0 : Fin (ϑ + 1)).val, by
            apply lastBlockIdx_mul_ϑ_add_x_lt_ℓ_succ (x:=(0 : Fin (ϑ + 1)).val) (hx:=by omega)⟩)
        (roundRelation (mp := mp) 𝔽q β (ϑ:=ϑ) (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
          ⟨(ℓ / ϑ - 1) * ϑ + (Fin.last ϑ).val, by
            apply lastBlockIdx_mul_ϑ_add_x_lt_ℓ_succ (x:=(Fin.last ϑ).val) (hx:=by omega)⟩) := by
    apply OracleReduction.seqCompose_perfectCompleteness
      (rel := fun k => roundRelation (mp := mp) 𝔽q β (ϑ:=ϑ)
        (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
        ⟨(ℓ / ϑ - 1) * ϑ + k, by
          apply lastBlockIdx_mul_ϑ_add_x_lt_ℓ_succ (x:=k) (hx:=by omega)⟩)
    intro i
    have nHCR : ¬ isCommitmentRound ℓ ϑ
        ⟨(ℓ / ϑ - 1) * ϑ + i, lastBlockIdx_mul_ϑ_add_fin_lt_ℓ i⟩ :=
      lastBlockIdx_isNeCommitmentRound i
    have key := foldRelayOracleReduction_perfectCompleteness (mp := mp) 𝔽q β (ϑ:=ϑ)
      (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (init := init) (impl := impl)
      (i := ⟨(ℓ / ϑ - 1) * ϑ + i, lastBlockIdx_mul_ϑ_add_fin_lt_ℓ i⟩) nHCR
    -- The reduction in `key` is *the same* as in the goal; only the relation indices differ
    -- (the `seqCompose` family is indexed by `i.castSucc`/`i.succ : Fin (ϑ+1)` while `key` uses
    -- the round index's own `.castSucc`/`.succ : Fin (ℓ+1)`). They are equal `Fin` values.
    convert key using 2 <;>
      · apply Fin.ext
        simp only [Fin.coe_castSucc, Fin.val_succ, Fin.val_zero, Fin.val_last]
        omega

set_option maxHeartbeats 1600000 in
/-- Perfect completeness of `lastBlockOracleReduction`. We transport the clean
    `lastBlock_seqCompose_perfectCompleteness` along the endpoint re-indexing
    `⟨(ℓ/ϑ-1)*ϑ+ϑ, _⟩ = Fin.last ℓ` that the definition performs with `rw!`. -/
theorem lastBlockOracleReduction_perfectCompleteness :
    OracleReduction.perfectCompleteness
      (pSpec := pSpecLastBlock (L:=L) (ϑ:=ϑ))
      (relIn := roundRelation (mp := mp) 𝔽q β (ϑ:=ϑ)
        (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
        ⟨(ℓ / ϑ - 1) * ϑ, by
          apply lastBlockIdx_mul_ϑ_add_x_lt_ℓ_succ (x:=0) (hx:=by omega)⟩)
      (relOut := roundRelation (mp := mp) 𝔽q β (ϑ:=ϑ)
        (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (Fin.last ℓ))
      (oracleReduction := lastBlockOracleReduction 𝔽q β (ϑ:=ϑ)
        (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (Context := Context))
      (init := init)
      (impl := impl) := by
  have base := lastBlock_seqCompose_perfectCompleteness (mp := mp) 𝔽q β (ϑ:=ϑ)
    (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (init := init) (impl := impl) (Context := Context)
  have h : (⟨(ℓ / ϑ - 1) * ϑ + ϑ, by
      apply lastBlockIdx_mul_ϑ_add_x_lt_ℓ_succ (hx:=by omega)⟩
      : Fin (ℓ + 1)) = Fin.last ℓ := by
    apply Fin.ext
    simp only [Fin.val_last]
    rw [Nat.sub_mul, one_mul, Nat.div_mul_cancel (hdiv.out)]
    rw [Nat.sub_add_cancel
      (by exact Nat.le_of_dvd (h:=by exact Nat.pos_of_neZero ℓ) (hdiv.out))]
  simp only [Fin.val_zero, Fin.val_last] at base
  rw! (castMode := .all) [h] at base
  unfold lastBlockOracleReduction pSpecLastBlock pSpecFoldRelaySequence
  convert base using 2 <;>
    first
      | rfl
      | (apply Fin.ext; simp; done)
      | (simp only [eqRec_eq_cast, eq_mp_eq_cast, eq_mpr_eq_cast, cast_cast, cast_eq]; rfl)
      | (simp only [eqRec_eq_cast, eq_mp_eq_cast, eq_mpr_eq_cast, cast_cast, cast_eq])

set_option maxHeartbeats 1000000 in
/-- Perfect completeness of the literal `(ϑ-1)`-fold-relay `seqCompose` underlying every non-last
    block (the honest fold-relay rounds `bIdx*ϑ, …, bIdx*ϑ+(ϑ-2)`), stated at the untransported
    endpoint `Fin` values. This is the genuine mathematical content of the fold-relay prefix of a
    non-last block; `nonLastBlockOracleReduction` glues it (via `append`) to a single fold-commit
    round. -/
theorem nonLastBlock_firstFoldRelay_seqCompose_perfectCompleteness
    (bIdx : Fin (ℓ / ϑ - 1)) :
      (OracleReduction.seqCompose (oSpec := []ₒ)
        (Stmt := fun i : Fin (ϑ - 1 + 1) => Statement (L := L) (ℓ := ℓ) Context
          ⟨bIdx * ϑ + i, bIdx_mul_ϑ_add_i_cast_lt_ℓ_succ bIdx i⟩)
        (OStmt := fun i : Fin (ϑ - 1 + 1) => OracleStatement 𝔽q β ϑ
          ⟨bIdx * ϑ + i, bIdx_mul_ϑ_add_i_cast_lt_ℓ_succ bIdx i⟩)
        (Wit := fun i : Fin (ϑ - 1 + 1) =>
          Witness (L := L) 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (ℓ:=ℓ)
            ⟨bIdx * ϑ + i, bIdx_mul_ϑ_add_i_cast_lt_ℓ_succ bIdx i⟩)
        (pSpec := fun _ => pSpecFoldRelay (L:=L))
        (R := fun i => by
          have nHCR : ¬ isCommitmentRound ℓ ϑ
              ⟨bIdx * ϑ + i, bIdx_mul_ϑ_add_i_fin_ℓ_pred_lt_ℓ bIdx i⟩ :=
            isNeCommitmentRound (r:=r) (ℓ:=ℓ) (𝓡:=𝓡) (ϑ:=ϑ) bIdx (x:=i.val) (hx:=by omega)
          exact foldRelayOracleReduction (L:=L) 𝔽q β (ϑ:=ϑ) (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
             (i:=⟨bIdx * ϑ + i, bIdx_mul_ϑ_add_i_fin_ℓ_pred_lt_ℓ bIdx i⟩)
             nHCR)).perfectCompleteness
        init impl
        (roundRelation (mp := mp) 𝔽q β (ϑ:=ϑ) (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
          ⟨bIdx * ϑ + (0 : Fin (ϑ - 1 + 1)).val, bIdx_mul_ϑ_add_i_cast_lt_ℓ_succ bIdx 0⟩)
        (roundRelation (mp := mp) 𝔽q β (ϑ:=ϑ) (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
          ⟨bIdx * ϑ + (Fin.last (ϑ - 1)).val,
            bIdx_mul_ϑ_add_i_cast_lt_ℓ_succ bIdx (Fin.last (ϑ - 1))⟩) := by
    apply OracleReduction.seqCompose_perfectCompleteness
      (rel := fun k => roundRelation (mp := mp) 𝔽q β (ϑ:=ϑ)
        (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
        ⟨bIdx * ϑ + k, bIdx_mul_ϑ_add_i_cast_lt_ℓ_succ bIdx k⟩)
    intro i
    have nHCR : ¬ isCommitmentRound ℓ ϑ
        ⟨bIdx * ϑ + i, bIdx_mul_ϑ_add_i_fin_ℓ_pred_lt_ℓ bIdx i⟩ :=
      isNeCommitmentRound (r:=r) (ℓ:=ℓ) (𝓡:=𝓡) (ϑ:=ϑ) bIdx (x:=i.val) (hx:=by omega)
    have key := foldRelayOracleReduction_perfectCompleteness (mp := mp) 𝔽q β (ϑ:=ϑ)
      (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (init := init) (impl := impl)
      (i := ⟨bIdx * ϑ + i, bIdx_mul_ϑ_add_i_fin_ℓ_pred_lt_ℓ bIdx i⟩) nHCR
    convert key using 2 <;>
      · apply Fin.ext
        simp only [Fin.coe_castSucc, Fin.val_succ, Fin.val_zero, Fin.val_last]
        omega

set_option maxHeartbeats 4000000 in
/-- Perfect completeness of `nonLastBlockOracleReduction bIdx`. It is the `append` of the
    `(ϑ-1)`-fold-relay prefix (`nonLastBlock_firstFoldRelay_seqCompose_perfectCompleteness`) and one
    fold-commit round (`foldCommitOracleReduction_perfectCompleteness`); the definition realigns the
    output endpoint `⟨bIdx*ϑ+(ϑ-1)+1, _⟩ = ⟨(bIdx+1)*ϑ, _⟩` with `rw!`, which we transport here. -/
theorem nonLastBlockOracleReduction_perfectCompleteness (bIdx : Fin (ℓ / ϑ - 1)) :
    OracleReduction.perfectCompleteness
      (pSpec := pSpecFullNonLastBlock 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) bIdx)
      (relIn := roundRelation (mp := mp) 𝔽q β (ϑ:=ϑ)
        (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
        ⟨bIdx * ϑ, by
          have := bIdx_mul_ϑ_add_i_lt_ℓ_succ (m:=0) bIdx ⟨0, Nat.pos_of_neZero ϑ⟩; omega⟩)
      (relOut := roundRelation (mp := mp) 𝔽q β (ϑ:=ϑ)
        (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
        ⟨(bIdx + 1) * ϑ, bIdx_succ_mul_ϑ_lt_ℓ_succ bIdx⟩)
      (oracleReduction := nonLastBlockOracleReduction 𝔽q β (ϑ:=ϑ)
        (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (Context := Context) bIdx)
      (init := init)
      (impl := impl) := by
  -- intermediate endpoint `⟨bIdx*ϑ+(ϑ-1), _⟩`
  have h1 : ↑bIdx * ϑ + (ϑ - 1) < ℓ := by
    have := bIdx_mul_ϑ_add_i_lt_ℓ_succ (m:=0) bIdx ⟨ϑ - 1, by
      have := NeZero.one_le (n:=ϑ); exact Nat.sub_one_lt_of_lt this⟩
    simpa using this
  -- clean append: fold-relay prefix ++ fold-commit, at untransported output `i.succ`.
  -- fold-relay prefix, with relOut realigned to the fold-commit's `relIn` (`i.castSucc`)
  have pre : _root_.OracleReduction.perfectCompleteness init impl
      (roundRelation (mp := mp) 𝔽q β (ϑ:=ϑ) (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
        ⟨bIdx * ϑ + (0 : Fin (ϑ - 1 + 1)).val, bIdx_mul_ϑ_add_i_cast_lt_ℓ_succ bIdx 0⟩)
      (roundRelation (mp := mp) 𝔽q β (ϑ:=ϑ) (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
        (⟨bIdx * ϑ + (ϑ - 1), h1⟩ : Fin ℓ).castSucc)
      (OracleReduction.seqCompose (oSpec := []ₒ)
          (Stmt := fun i : Fin (ϑ - 1 + 1) => Statement (L := L) (ℓ := ℓ) Context
            ⟨bIdx * ϑ + i, bIdx_mul_ϑ_add_i_cast_lt_ℓ_succ bIdx i⟩)
          (OStmt := fun i : Fin (ϑ - 1 + 1) => OracleStatement 𝔽q β ϑ
            ⟨bIdx * ϑ + i, bIdx_mul_ϑ_add_i_cast_lt_ℓ_succ bIdx i⟩)
          (Wit := fun i : Fin (ϑ - 1 + 1) =>
            Witness (L := L) 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (ℓ:=ℓ)
              ⟨bIdx * ϑ + i, bIdx_mul_ϑ_add_i_cast_lt_ℓ_succ bIdx i⟩)
          (pSpec := fun _ => pSpecFoldRelay (L:=L))
          (R := fun i => by
            have nHCR : ¬ isCommitmentRound ℓ ϑ
                ⟨bIdx * ϑ + i, bIdx_mul_ϑ_add_i_fin_ℓ_pred_lt_ℓ bIdx i⟩ :=
              isNeCommitmentRound (r:=r) (ℓ:=ℓ) (𝓡:=𝓡) (ϑ:=ϑ) bIdx (x:=i.val) (hx:=by omega)
            exact foldRelayOracleReduction (L:=L) 𝔽q β (ϑ:=ϑ) (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
               (i:=⟨bIdx * ϑ + i, bIdx_mul_ϑ_add_i_fin_ℓ_pred_lt_ℓ bIdx i⟩) nHCR)) := by
    have pre0 := nonLastBlock_firstFoldRelay_seqCompose_perfectCompleteness (mp := mp) 𝔽q β (ϑ:=ϑ)
      (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (init := init) (impl := impl) (Context := Context) bIdx
    convert pre0 using 2 <;>
      (try (apply Fin.ext; simp only [Fin.coe_castSucc, Fin.val_last]; omega))
  have commit := foldCommitOracleReduction_perfectCompleteness (mp := mp) 𝔽q β (ϑ:=ϑ)
    (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (init := init) (impl := impl)
    (i := ⟨bIdx * ϑ + (ϑ - 1), h1⟩)
    (hCR := isCommitmentRoundOfNonLastBlock (𝓡:=𝓡) (r:=r) bIdx)
  have base := OracleReduction.append_perfectCompleteness _ _ pre commit
  -- transport the output endpoint `i.succ = ⟨bIdx*ϑ+(ϑ-1)+1, _⟩` to `⟨(bIdx+1)*ϑ, _⟩`
  have h : ↑bIdx * ϑ + (ϑ - 1) + 1 = (↑bIdx + 1) * ϑ := by
    rw [Nat.add_assoc, Nat.sub_add_cancel (by exact NeZero.one_le)]
    rw [Nat.add_mul, Nat.one_mul]
  simp only [Fin.succ_mk, Fin.val_zero, Nat.add_zero] at base
  rw! (castMode := .all) [h] at base
  unfold nonLastBlockOracleReduction pSpecFullNonLastBlock pSpecFoldRelaySequence
  convert base using 2 <;>
    first
      | rfl
      | (apply Fin.ext
         simp only [Fin.coe_castSucc, Fin.val_succ, Fin.val_zero, Fin.val_last]
         omega)
      | (simp only [eqRec_eq_cast, eq_mp_eq_cast, eq_mpr_eq_cast, cast_cast, cast_eq]; rfl)
      | (simp only [eqRec_eq_cast, eq_mp_eq_cast, eq_mpr_eq_cast, cast_cast, cast_eq])
      | (apply Fin.ext; simp)
      | exact HEq.rfl
      | (apply proof_irrel_heq)

set_option maxHeartbeats 1000000 in
/-- Perfect completeness of the `seqCompose` of all `(ℓ/ϑ-1)` non-last blocks, stated at the
    untransported endpoint `Fin` values. -/
theorem nonLastBlocks_seqCompose_perfectCompleteness :
      (OracleReduction.seqCompose (oSpec := []ₒ)
        (Stmt := fun i : Fin (ℓ / ϑ - 1 + 1) => Statement (L := L) (ℓ := ℓ) Context
          ⟨i * ϑ, blockIdx_mul_ϑ_lt_ℓ_succ i⟩)
        (OStmt := fun i : Fin (ℓ / ϑ - 1 + 1) => OracleStatement 𝔽q β ϑ
          ⟨i * ϑ, blockIdx_mul_ϑ_lt_ℓ_succ i⟩)
        (Wit := fun i : Fin (ℓ / ϑ - 1 + 1) =>
          Witness (L := L) 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (ℓ:=ℓ)
            ⟨i * ϑ, blockIdx_mul_ϑ_lt_ℓ_succ i⟩)
        (pSpec := fun (bIdx : Fin (ℓ / ϑ - 1)) => pSpecFullNonLastBlock 𝔽q β bIdx)
        (R := fun bIdx => nonLastBlockOracleReduction (L:=L) 𝔽q β (ϑ:=ϑ)
          (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (bIdx:=bIdx))).perfectCompleteness
        init impl
        (roundRelation (mp := mp) 𝔽q β (ϑ:=ϑ) (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
          ⟨(0 : Fin (ℓ / ϑ - 1 + 1)).val * ϑ, blockIdx_mul_ϑ_lt_ℓ_succ 0⟩)
        (roundRelation (mp := mp) 𝔽q β (ϑ:=ϑ) (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
          ⟨(Fin.last (ℓ / ϑ - 1)).val * ϑ, blockIdx_mul_ϑ_lt_ℓ_succ (Fin.last (ℓ / ϑ - 1))⟩) := by
  apply OracleReduction.seqCompose_perfectCompleteness
    (rel := fun i => roundRelation (mp := mp) 𝔽q β (ϑ:=ϑ)
      (h_ℓ_add_R_rate := h_ℓ_add_R_rate) ⟨i * ϑ, blockIdx_mul_ϑ_lt_ℓ_succ i⟩)
  intro bIdx
  have key := nonLastBlockOracleReduction_perfectCompleteness (mp := mp) 𝔽q β (ϑ:=ϑ)
    (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (init := init) (impl := impl) (Context := Context) bIdx
  convert key using 2 <;>
    · apply Fin.ext
      simp only [Fin.coe_castSucc, Fin.val_succ, Fin.val_last, Fin.val_zero]
      ring

set_option maxHeartbeats 4000000 in
/-- Perfect completeness for the core interaction oracle reduction.
    `sumcheckFoldOracleReduction` is the `append` of the all-non-last-blocks `seqCompose`
    (`nonLastBlocks_seqCompose_perfectCompleteness`) with the last block
    (`lastBlockOracleReduction_perfectCompleteness`); the definition realigns the protocol-spec
    shape with `convert`, which we transport here. -/
theorem sumcheckFoldOracleReduction_perfectCompleteness :
    OracleReduction.perfectCompleteness
      (pSpec := pSpecSumcheckFold 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate))
      (relIn := roundRelation (mp := mp) 𝔽q β (ϑ:=ϑ)
        (h_ℓ_add_R_rate := h_ℓ_add_R_rate) 0)
      (relOut := roundRelation (mp := mp) 𝔽q β (ϑ:=ϑ)
        (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (Fin.last ℓ))
      (oracleReduction := sumcheckFoldOracleReduction 𝔽q β (ϑ:=ϑ)
        (h_ℓ_add_R_rate := h_ℓ_add_R_rate) )
      (init := init)
      (impl := impl) := by
  -- the last-block index `(ℓ/ϑ-1)*ϑ` is the split point of the top-level append
  have hlast : ((Fin.last (ℓ / ϑ - 1)).val * ϑ) = (ℓ / ϑ - 1) * ϑ := by simp [Fin.val_last]
  have nonLast := nonLastBlocks_seqCompose_perfectCompleteness (mp := mp) 𝔽q β (ϑ:=ϑ)
    (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (init := init) (impl := impl) (Context := Context)
  have last := lastBlockOracleReduction_perfectCompleteness (mp := mp) 𝔽q β (ϑ:=ϑ)
    (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (init := init) (impl := impl) (Context := Context)
  -- align the split-point relation of `nonLast` (`⟨(Fin.last _)*ϑ,_⟩`) with `last`'s relIn
  -- (`⟨(ℓ/ϑ-1)*ϑ,_⟩`); they are the same `Fin` value, so `nonLast`'s relOut matches.
  have base := OracleReduction.append_perfectCompleteness _ _ nonLast last
  -- `base : (nonLast.seqCompose).append (lastBlock) : perfectCompleteness 0 (Fin.last ℓ)`
  -- normalise the trivial index `↑0 * ϑ` to `0` so it matches the goal's `relIn = roundRelation 0`
  simp only [Fin.val_zero, Nat.zero_mul, Fin.mk_zero] at base
  unfold sumcheckFoldOracleReduction pSpecSumcheckFold pSpecNonLastBlocks
  convert base using 1 <;>
    first
      | rfl
      | (apply Fin.ext
         simp only [Fin.coe_castSucc, Fin.val_succ, Fin.val_zero, Fin.val_last]
         ring)
      | (simp only [id_eq, eqRec_eq_cast, eq_mp_eq_cast, eq_mpr_eq_cast, cast_cast, cast_eq]; rfl)
      | (simp only [id_eq, eqRec_eq_cast, eq_mp_eq_cast, eq_mpr_eq_cast, cast_cast, cast_eq]
         exact (cast_heq _ _).trans (by rfl))
      | (exact (cast_heq _ _).trans (by rfl))
      | (congr 2 <;> (apply Fin.ext; simp))
      | (congr 1 <;> (apply Fin.ext; simp))
      | (apply heq_of_eq; congr 2 <;> (apply Fin.ext; simp))

def NBlockMessages := 2 * (ϑ - 1) + 3

/-- **q-ary block-counting step.**
A global message position `x` of `pSpecSumcheckFold` lives inside a protocol made of `B` non-last
blocks of `2ϑ+1 = NBlockMessages` messages each, followed by one last block of `2ϑ` messages
(so `x < B*(2ϑ+1) + 2ϑ`).  An (odd-offset) challenge at position `x` belongs to the fold round
`(x / (2ϑ+1)) * ϑ + (x % (2ϑ+1)) / 2`, which is strictly below `ℓ = (B+1)*ϑ`.

This is the pure arithmetic core of the `Fin ℓ`-bound inside `sumcheckFoldKnowledgeError`. -/
theorem sumcheckFold_round_lt (ϑ B x : ℕ) (hϑ : 1 ≤ ϑ)
    (hx : x < B * (2 * ϑ + 1) + 2 * ϑ)
    (hodd : (x % (2 * ϑ + 1)) % 2 = 1) :
    (x / (2 * ϑ + 1)) * ϑ + (x % (2 * ϑ + 1)) / 2 < (B + 1) * ϑ := by
  set M := 2 * ϑ + 1 with hM
  set q := x / M with hq
  set s := x % M with hs
  have hMpos : 0 < M := by omega
  have hdm : x = M * q + s := (Nat.div_add_mod x M).symm
  have hsM : s < M := Nat.mod_lt _ hMpos
  have hsodd : s % 2 = 1 := hodd
  have hds : s = 2 * (s / 2) + 1 := by omega
  set d := s / 2 with hd
  have hdϑ : d ≤ ϑ - 1 := by omega
  -- the position cannot exceed the `B` non-last blocks plus the last block
  have hqB : q ≤ B := by
    by_contra h
    push_neg at h
    have hle : (B + 1) * M ≤ q * M := Nat.mul_le_mul_right M h
    have hexp : (B + 1) * M = B * M + 2 * ϑ + 1 := by ring
    have hMq : M * q = q * M := Nat.mul_comm M q
    omega
  rcases Nat.lt_or_ge q B with hqlt | hqge
  · -- challenge inside a non-last block: round ≤ B*ϑ - 1 < (B+1)*ϑ
    have h2 : q * ϑ + (ϑ - 1) < (q + 1) * ϑ := by
      have he : (q + 1) * ϑ = q * ϑ + ϑ := by ring
      omega
    have h3 : (q + 1) * ϑ ≤ B * ϑ := Nat.mul_le_mul_right ϑ (by omega)
    have h4 : (B + 1) * ϑ = B * ϑ + ϑ := by ring
    omega
  · -- challenge inside the last block: there only `2ϑ` messages remain, so `s < 2ϑ`
    have hqeq : q = B := le_antisymm hqB hqge
    have hslt : s < 2 * ϑ := by
      have hMq : M * q = q * M := Nat.mul_comm M q
      have hlt : q * M + s < B * M + 2 * ϑ := by omega
      rw [hqeq] at hlt
      omega
    have hd2 : d ≤ ϑ - 1 := by omega
    have h4 : (B + 1) * ϑ = B * ϑ + ϑ := by ring
    rw [hqeq]
    omega

/-- Per-challenge RBR knowledge error for the composed sumcheck-fold protocol: challenge `j`
(at offset `j % NBlockMessages` inside block `j / NBlockMessages`) is the verifier challenge of
fold round `(j / NBlockMessages) · ϑ + (j % NBlockMessages) / 2`, whose error is
`foldKnowledgeError` at that round.

STATEMENT REPAIR (index off-by-one): the previous form added `+ 1` to the in-block fold index
`(j % NBlockMessages) / 2`.  That (a) overflows `Fin ℓ` exactly at the last challenge of the last
block (`j = (ℓ/ϑ − 1)·(2ϑ+1) + (2ϑ−1)` maps to `(ℓ/ϑ)·ϑ = ℓ`, since `ϑ ∣ ℓ`), making the bound
unprovable as stated, and (b) misroutes `foldKnowledgeError`'s bad-event term: that term fires
when `ϑ ∣ (i + 1)`, i.e. at the *commit-round* challenge `i = b·ϑ + (ϑ−1)` (block offset `2ϑ−1`),
which is the image of the un-shifted map — with the `+ 1` the commit challenge would land on
`(b+1)·ϑ` where the term does not fire. -/
def sumcheckFoldKnowledgeError := fun j : (pSpecSumcheckFold 𝔽q β (ϑ:=ϑ)
    (h_ℓ_add_R_rate := h_ℓ_add_R_rate)).ChallengeIdx =>
    if hj: (j.val % NBlockMessages (ϑ:=ϑ)) % 2 = 1 then
      foldKnowledgeError 𝔽q β (ϑ:=ϑ) (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
        -- Faithful fold-round index for the `↑↑j`-th challenge of `pSpecSumcheckFold`.
        -- The original `(j % NBlockMessages) / 2 + 1` is OFF BY ONE: at the last challenge
        -- (`j % B = 2ϑ-1`, `j / B = ℓ/ϑ-1`) it evaluates to `ℓ`, making the `< ℓ` bound FALSE.
        -- The ℓ challenges (`ℓ/ϑ` blocks × ϑ each) map bijectively onto fold rounds `0..ℓ-1`
        -- via `s = 1,3,…,2ϑ-1 ↦ s/2 = 0,…,ϑ-1`, so the faithful index drops the `+1`.
        ⟨j / NBlockMessages (ϑ:=ϑ) * ϑ + (j % NBlockMessages (ϑ:=ϑ)) / 2, by
          -- The `↑↑j`-th challenge of `pSpecSumcheckFold` is the sumcheck challenge of fold round
          -- `(↑↑j / NBlockMessages) * ϑ + (↑↑j % NBlockMessages) / 2`, which lies in `{0,…,ℓ-1}`.
          -- `pSpecSumcheckFold` has `ℓ/ϑ` blocks, each of `NBlockMessages = 2ϑ+1` messages and
          -- carrying `ϑ` challenges at the odd positions `1,3,…,2ϑ-1`; the last block contributes
          -- only its first `2ϑ` messages. We bound `↑↑j` by this layout and conclude with `ϑ ∣ ℓ`.
          -- Basic positivity facts about the parameters.
          have hϑ_pos : 0 < ϑ := Nat.pos_of_neZero ϑ
          have hℓ_pos : 0 < ℓ := Nat.pos_of_neZero ℓ
          -- `NBlockMessages = 2ϑ + 1`; rewrite the block size to this concrete value everywhere.
          have hB_eq : NBlockMessages (ϑ := ϑ) = 2 * ϑ + 1 := by
            unfold NBlockMessages; omega
          rw [hB_eq] at hj ⊢
          -- `ϑ ∣ ℓ`, so `(ℓ/ϑ) * ϑ = ℓ` and `ℓ/ϑ ≥ 1`.
          have hdvd : ϑ ∣ ℓ := hdiv.out
          have hℓ_ge : ϑ ≤ ℓ := Nat.le_of_dvd hℓ_pos hdvd
          have hdiv_mul : ℓ / ϑ * ϑ = ℓ := Nat.div_mul_cancel hdvd
          have hℓϑ_pos : 1 ≤ ℓ / ϑ := by
            rw [Nat.one_le_div_iff hϑ_pos]; exact Nat.le_of_dvd hℓ_pos hdvd
          -- Upper bound on `m := ↑↑j` from the protocol layout (evaluating the `Fin.vsum`s).
          have hb := j.val.isLt
          simp only [Fin.vsum_eq_univ_sum, Finset.sum_const, Finset.card_univ,
            Fintype.card_fin, smul_eq_mul] at hb
          rw [show ((ϑ - 1) * 2 + 3) = 2 * ϑ + 1 by omega] at hb
          -- Hence `m < (ℓ/ϑ) * (2ϑ+1)`, since `ϑ * 2 ≤ 2ϑ+1`.
          have hm_lt : j.val.val < ℓ / ϑ * (2 * ϑ + 1) := by
            have hrec : (ℓ / ϑ - 1) * (2 * ϑ + 1) + (2 * ϑ + 1) = ℓ / ϑ * (2 * ϑ + 1) := by
              rw [← Nat.succ_mul]; congr 1; omega
            have hle : (ℓ / ϑ - 1) * (2 * ϑ + 1) + ϑ * 2 ≤ ℓ / ϑ * (2 * ϑ + 1) := by
              rw [← hrec]
              exact Nat.add_le_add_left (by omega) _
            exact lt_of_lt_of_le hb hle
          -- Quotient bound: `m / (2ϑ+1) < ℓ/ϑ`, i.e. `m / (2ϑ+1) ≤ ℓ/ϑ - 1`.
          have hq_lt : j.val.val / (2 * ϑ + 1) < ℓ / ϑ :=
            (Nat.div_lt_iff_lt_mul (by omega)).mpr hm_lt
          have hq_le : j.val.val / (2 * ϑ + 1) ≤ ℓ / ϑ - 1 := Nat.le_sub_one_of_lt hq_lt
          -- `(m / (2ϑ+1)) * ϑ ≤ (ℓ/ϑ - 1) * ϑ = ℓ - ϑ`.
          have hqϑ_le : j.val.val / (2 * ϑ + 1) * ϑ ≤ ℓ - ϑ := by
            calc j.val.val / (2 * ϑ + 1) * ϑ ≤ (ℓ / ϑ - 1) * ϑ := Nat.mul_le_mul_right _ hq_le
              _ = ℓ - ϑ := by rw [Nat.sub_mul, Nat.one_mul, hdiv_mul]
          -- Remainder bound: `s := m % (2ϑ+1) < 2ϑ+1`, and `s` is odd, so `s / 2 ≤ ϑ - 1`.
          have hs_lt : j.val.val % (2 * ϑ + 1) < 2 * ϑ + 1 := Nat.mod_lt _ (by omega)
          -- Combine: `(m/(2ϑ+1))*ϑ + (m%(2ϑ+1))/2 ≤ (ℓ - ϑ) + (ϑ - 1) = ℓ - 1 < ℓ`.
          omega⟩ ⟨1, rfl⟩
    else 0 -- this case never happens

/-- Round-by-round knowledge soundness for the sumcheck fold oracle verifier.

    REMAINS `sorry`: closing this requires (a) two block-level RBR-KS theorems
    (`nonLastBlockOracleVerifier`/`lastBlockOracleVerifier`, currently absent), (b) transporting
    RBR-KS across each block def's `simp`/`rw!` casts, (c) `seqCompose`+`append` assembly, and
    (d) an error-index bridge proving the `Sum.elim … ∘ ChallengeIdx.sumEquiv.symm` form equals the
    explicit modular `sumcheckFoldKnowledgeError` closed form. The pure-arithmetic core of (d) —
    that every odd-offset challenge maps into a valid fold round `< ℓ` — is proven sorry-free above
    as `sumcheckFold_round_lt`, which also discharges the `Fin ℓ` bound inside
    `sumcheckFoldKnowledgeError`. -/
theorem sumcheckFoldOracleVerifier_rbrKnowledgeSoundness :
    (sumcheckFoldOracleVerifier 𝔽q β ).rbrKnowledgeSoundness init impl
      (pSpec := pSpecSumcheckFold 𝔽q β (ϑ:=ϑ) (h_ℓ_add_R_rate := h_ℓ_add_R_rate))
      (relIn := roundRelation (mp := mp) 𝔽q β (ϑ:=ϑ)
        (h_ℓ_add_R_rate := h_ℓ_add_R_rate) 0)
      (relOut := roundRelation (mp := mp) 𝔽q β (ϑ:=ϑ)
        (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (Fin.last ℓ))
      (rbrKnowledgeError := sumcheckFoldKnowledgeError 𝔽q β (ϑ:=ϑ)) := by
  unfold sumcheckFoldOracleVerifier pSpecSumcheckFold
  sorry

end SecurityProps

end IteratedSumcheckFoldComposition
end ComponentReductions

section CoreInteractionPhaseReduction

/-- The final oracle verifier that composes sumcheckFold with finalSumcheckStep -/
@[reducible]
def coreInteractionOracleVerifier :=
  OracleVerifier.append (oSpec:=[]ₒ)
    (Stmt₁ := Statement (L := L) (ℓ:=ℓ) (SumcheckBaseContext L ℓ) 0)
    (Stmt₂ := Statement (L := L) (ℓ:=ℓ) (SumcheckBaseContext L ℓ) (Fin.last ℓ))
    (Stmt₃ := FinalSumcheckStatementOut (L:=L) (ℓ:=ℓ))
    (OStmt₁ := OracleStatement 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) ϑ 0)
    (OStmt₂ := OracleStatement 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) ϑ (Fin.last ℓ))
    (OStmt₃ := OracleStatement 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) ϑ (Fin.last ℓ))
    (pSpec₁ := pSpecSumcheckFold 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate))
    (pSpec₂ := pSpecFinalSumcheckStep (L:=L))
    (V₁ := sumcheckFoldOracleVerifier 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) )
    (V₂ := finalSumcheckVerifier 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate))

/-- The final oracle reduction that composes sumcheckFold with finalSumcheckStep -/
@[reducible]
def coreInteractionOracleReduction :=
  OracleReduction.append (oSpec:=[]ₒ)
    (Stmt₁ := Statement (L := L) (ℓ:=ℓ) (SumcheckBaseContext L ℓ) 0)
    (Stmt₂ := Statement (L := L) (ℓ:=ℓ) (SumcheckBaseContext L ℓ) (Fin.last ℓ))
    (Stmt₃ := FinalSumcheckStatementOut (L:=L) (ℓ:=ℓ))
    (Wit₁ := Witness (L := L) 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (ℓ:=ℓ) 0)
    (Wit₂ := Witness (L := L) 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (ℓ:=ℓ) (Fin.last ℓ))
    (Wit₃ := Unit)
    (OStmt₁ := OracleStatement 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) ϑ 0)
    (OStmt₂ := OracleStatement 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) ϑ (Fin.last ℓ))
    (OStmt₃ := OracleStatement 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) ϑ (Fin.last ℓ))
    (pSpec₁ := pSpecSumcheckFold 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate))
    (pSpec₂ := pSpecFinalSumcheckStep (L:=L))
    (R₁ := sumcheckFoldOracleReduction 𝔽q β (ϑ:=ϑ) (h_ℓ_add_R_rate := h_ℓ_add_R_rate) )
    (R₂ := finalSumcheckOracleReduction 𝔽q β (ϑ:=ϑ) (h_ℓ_add_R_rate := h_ℓ_add_R_rate))

variable {σ : Type} {init : ProbComp σ} {impl : QueryImpl []ₒ (StateT σ ProbComp)}

/-- Perfect completeness for the core interaction oracle reduction -/
theorem coreInteractionOracleReduction_perfectCompleteness :
    OracleReduction.perfectCompleteness
      (pSpec := pSpecCoreInteraction 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate))
      (relIn := roundRelation (mp := BBF_SumcheckMultiplierParam) 𝔽q β (ϑ:=ϑ)
        (h_ℓ_add_R_rate := h_ℓ_add_R_rate) 0)
      (relOut := finalSumcheckRelOut 𝔽q β (ϑ:=ϑ) (h_ℓ_add_R_rate := h_ℓ_add_R_rate))
      (oracleReduction := coreInteractionOracleReduction 𝔽q β (ϑ:=ϑ) )
      (init := init)
      (impl := impl) := by
  unfold coreInteractionOracleReduction pSpecCoreInteraction
  apply OracleReduction.append_perfectCompleteness
  · -- Perfect completeness of sumcheckFoldOracleReduction
    exact sumcheckFoldOracleReduction_perfectCompleteness 𝔽q β (ϑ:=ϑ)
      (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (mp := BBF_SumcheckMultiplierParam)
      (init := init) (impl := impl)
  · -- Perfect completeness of finalSumcheckOracleReduction
    exact finalSumcheckOracleReduction_perfectCompleteness 𝔽q β (ϑ:=ϑ) init impl

def coreInteractionOracleRbrKnowledgeError (j : (pSpecCoreInteraction 𝔽q β (ϑ := ϑ)
    (h_ℓ_add_R_rate := h_ℓ_add_R_rate)).ChallengeIdx) : ℝ≥0 :=
    Sum.elim
      (f := fun i => sumcheckFoldKnowledgeError 𝔽q β (ϑ:=ϑ) (h_ℓ_add_R_rate := h_ℓ_add_R_rate) i)
      (g := fun i => finalSumcheckKnowledgeError (L := L) i)
      (ChallengeIdx.sumEquiv.symm j)

/-- Round-by-round knowledge soundness for the core interaction oracle verifier -/
theorem coreInteractionOracleVerifier_rbrKnowledgeSoundness :
    (coreInteractionOracleVerifier 𝔽q β ).rbrKnowledgeSoundness init impl
      (pSpec := pSpecCoreInteraction 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate))
      (relIn := roundRelation (mp := BBF_SumcheckMultiplierParam) 𝔽q β (ϑ:=ϑ)
        (h_ℓ_add_R_rate := h_ℓ_add_R_rate) 0)
      (relOut := finalSumcheckRelOut 𝔽q β (ϑ:=ϑ) (h_ℓ_add_R_rate := h_ℓ_add_R_rate))
      (rbrKnowledgeError := coreInteractionOracleRbrKnowledgeError 𝔽q β (ϑ:=ϑ)) := by
  unfold coreInteractionOracleVerifier pSpecCoreInteraction
  apply OracleVerifier.append_rbrKnowledgeSoundness
    (init:=init) (impl:=impl)
    (rel₁ := roundRelation 𝔽q β (ϑ:=ϑ) (h_ℓ_add_R_rate := h_ℓ_add_R_rate) 0)
    (rel₂ := roundRelation 𝔽q β (ϑ:=ϑ) (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (Fin.last ℓ))
    (rel₃ := finalSumcheckRelOut 𝔽q β (ϑ:=ϑ) (h_ℓ_add_R_rate := h_ℓ_add_R_rate))
    (V₁ := sumcheckFoldOracleVerifier 𝔽q β
      (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (ϑ:=ϑ) )
    (V₂ := finalSumcheckVerifier 𝔽q β
      (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (ϑ:=ϑ))
    (Oₛ₃:=by exact fun i ↦ by exact OracleInterface.instDefault)
    (rbrKnowledgeError₁ := sumcheckFoldKnowledgeError 𝔽q β (ϑ:=ϑ))
    (rbrKnowledgeError₂ := finalSumcheckKnowledgeError (L := L))
    (h₁ := by apply sumcheckFoldOracleVerifier_rbrKnowledgeSoundness)
    (h₂ := by apply finalSumcheckOracleVerifier_rbrKnowledgeSoundness)

end CoreInteractionPhaseReduction

end
end Binius.BinaryBasefold.CoreInteraction

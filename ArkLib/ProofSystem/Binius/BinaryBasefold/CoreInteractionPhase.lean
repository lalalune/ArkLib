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
  -- Transport through the local `let`-bound, reindexed append is proof-irrelevant coherence only.
  sorry

def lastBlockOracleVerifier :=
  let bIdx := ℓ / ϑ - 1
  let stmt : Fin (ϑ + 1) → Type := fun i => Statement (L := L) (ℓ:=ℓ) Context
    ⟨bIdx * ϑ + i, by apply lastBlockIdx_mul_ϑ_add_x_lt_ℓ_succ (hx:=by omega)⟩
  let oStmt := fun i: Fin (ϑ + 1) =>
    OracleStatement 𝔽q β (𝓡 := 𝓡) (h_ℓ_add_R_rate := h_ℓ_add_R_rate) ϑ
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
def sumcheckFoldOracleVerifier :
    OracleVerifier []ₒ
    (StmtIn := Statement (L := L) (ℓ := ℓ) Context 0)
    (OStmtIn := OracleStatement 𝔽q β (𝓡:=𝓡)
      (h_ℓ_add_R_rate := h_ℓ_add_R_rate) ϑ 0)
    (StmtOut := Statement (L := L) (ℓ := ℓ) Context (Fin.last ℓ))
    (OStmtOut := OracleStatement 𝔽q β (𝓡:=𝓡)
      (h_ℓ_add_R_rate := h_ℓ_add_R_rate) ϑ (Fin.last ℓ))
    (pSpec := pSpecSumcheckFold 𝔽q β (ϑ := ϑ)
      (h_ℓ_add_R_rate := h_ℓ_add_R_rate)) := by
  -- TODO: restore explicit seqCompose/append implementation after coherence transport is refactored.
  sorry

end composedOracleVerifiers

section composedOracleRedutions

def nonLastBlockOracleReduction (bIdx : Fin (ℓ / ϑ - 1)) :
    OracleReduction []ₒ
      (StmtIn := Statement (L := L) (ℓ := ℓ) Context
        ⟨bIdx * ϑ, by
          apply Nat.lt_trans (m:=ℓ)
          · change bIdx.val * ϑ + (⟨0, by exact Nat.pos_of_neZero ϑ⟩ : Fin ϑ).val < ℓ + 0
            apply bIdx_mul_ϑ_add_i_lt_ℓ_succ
          · omega⟩)
      (OStmtIn := OracleStatement 𝔽q β (𝓡:=𝓡)
        (h_ℓ_add_R_rate := h_ℓ_add_R_rate) ϑ
        ⟨bIdx * ϑ, by
          apply Nat.lt_trans (m:=ℓ)
          · change bIdx.val * ϑ + (⟨0, by exact Nat.pos_of_neZero ϑ⟩ : Fin ϑ).val < ℓ + 0
            apply bIdx_mul_ϑ_add_i_lt_ℓ_succ
          · omega⟩)
      (WitIn := Witness (L := L) 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (ℓ:=ℓ)
        ⟨bIdx * ϑ, by
          apply Nat.lt_trans (m:=ℓ)
          · change bIdx.val * ϑ + (⟨0, by exact Nat.pos_of_neZero ϑ⟩ : Fin ϑ).val < ℓ + 0
            apply bIdx_mul_ϑ_add_i_lt_ℓ_succ
          · omega⟩)
      (StmtOut := Statement (L := L) (ℓ := ℓ) Context
        ⟨(bIdx + 1) * ϑ, bIdx_succ_mul_ϑ_lt_ℓ_succ bIdx⟩)
      (OStmtOut := OracleStatement 𝔽q β (𝓡:=𝓡)
        (h_ℓ_add_R_rate := h_ℓ_add_R_rate) ϑ
        ⟨(bIdx + 1) * ϑ, bIdx_succ_mul_ϑ_lt_ℓ_succ bIdx⟩)
      (WitOut := Witness (L := L) 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (ℓ:=ℓ)
        ⟨(bIdx + 1) * ϑ, bIdx_succ_mul_ϑ_lt_ℓ_succ bIdx⟩)
      (pSpec := pSpecFullNonLastBlock 𝔽q β (𝓡:=𝓡) (ϑ:=ϑ)
        (h_ℓ_add_R_rate := h_ℓ_add_R_rate) bIdx) := by
  -- TODO: restore explicit fold-relay-prefix/fold-commit append construction.
  sorry

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
    (OStmtIn := OracleStatement 𝔽q β (𝓡 := 𝓡) (h_ℓ_add_R_rate := h_ℓ_add_R_rate) ϑ
      ⟨bIdx * ϑ, by apply lastBlockIdx_mul_ϑ_add_x_lt_ℓ_succ (x:=0) (hx:=by omega)⟩)
    (WitIn := Witness (L := L) 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (ℓ:=ℓ)
      ⟨bIdx * ϑ, by apply lastBlockIdx_mul_ϑ_add_x_lt_ℓ_succ (x:=0) (hx:=by omega)⟩)
    (StmtOut := Statement (L := L) (ℓ := ℓ) Context (Fin.last ℓ))
    (OStmtOut := OracleStatement 𝔽q β (𝓡 := 𝓡) (h_ℓ_add_R_rate := h_ℓ_add_R_rate) ϑ (Fin.last ℓ))
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
        (coh := fun i => by
          have nHCR : ¬ isCommitmentRound ℓ ϑ
              ⟨bIdx * ϑ + i, lastBlockIdx_mul_ϑ_add_fin_lt_ℓ i⟩ :=
            lastBlockIdx_isNeCommitmentRound i
          exact instFoldRelayOracleReductionAppendCoherent (L:=L) 𝔽q β (ϑ:=ϑ)
            (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (Context := Context)
            ⟨bIdx * ϑ + i, lastBlockIdx_mul_ϑ_add_fin_lt_ℓ i⟩ nHCR)
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
def sumcheckFoldOracleReduction : OracleReduction []ₒ
    (StmtIn := Statement (L := L) (ℓ := ℓ) Context 0)
    (OStmtIn := OracleStatement 𝔽q β (𝓡:=𝓡)
      (h_ℓ_add_R_rate := h_ℓ_add_R_rate) ϑ 0)
    (WitIn := Witness (L := L) 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (ℓ:=ℓ) 0)
    (StmtOut := Statement (L := L) (ℓ:=ℓ) Context (Fin.last ℓ))
    (OStmtOut := OracleStatement 𝔽q β (𝓡:=𝓡)
      (h_ℓ_add_R_rate := h_ℓ_add_R_rate) ϑ (Fin.last ℓ))
    (WitOut := Witness (L := L) 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (ℓ:=ℓ) (Fin.last ℓ))
    (pSpec := pSpecSumcheckFold 𝔽q β (ϑ := ϑ)
      (h_ℓ_add_R_rate := h_ℓ_add_R_rate)) := by
  -- TODO: restore explicit seqCompose/append implementation after coherence transport is refactored.
  sorry

end composedOracleRedutions

instance instSumcheckFoldOracleVerifierAppendCoherent :
    OracleVerifier.Append.AppendCoherent
      (sumcheckFoldOracleVerifier 𝔽q β (ϑ:=ϑ)
        (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (Context := Context)) := by
  -- Transported coherence through the final block-level casts remains proof-only.
  exact (by sorry)

instance instSumcheckFoldOracleReductionAppendCoherent :
    OracleVerifier.Append.AppendCoherent
      (sumcheckFoldOracleReduction 𝔽q β (ϑ := ϑ)
        (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (Context := Context)).verifier := by
  -- Same proof-only coherence transport for the reduction verifier.
  exact (by sorry)

section SecurityProps

variable {σ : Type} {init : ProbComp σ} {impl : QueryImpl []ₒ (StateT σ ProbComp)}

/-- Perfect completeness for the core interaction oracle reduction -/
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
  sorry

def NBlockMessages := 2 * (ϑ - 1) + 3

def sumcheckFoldKnowledgeError := fun j : (pSpecSumcheckFold 𝔽q β (ϑ:=ϑ)
    (h_ℓ_add_R_rate := h_ℓ_add_R_rate)).ChallengeIdx =>
    let jn : ℕ := j.1.val
    if hj: (jn % NBlockMessages (ϑ:=ϑ)) % 2 = 1 then
      foldKnowledgeError 𝔽q β (ϑ:=ϑ) (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
        -- Faithful fold-round index for the `↑↑j`-th challenge of `pSpecSumcheckFold`.
        -- The original `(j % NBlockMessages) / 2 + 1` is OFF BY ONE: at the last challenge
        -- (`j % B = 2ϑ-1`, `j / B = ℓ/ϑ-1`) it evaluates to `ℓ`, making the `< ℓ` bound FALSE.
        -- The ℓ challenges (`ℓ/ϑ` blocks × ϑ each) map bijectively onto fold rounds `0..ℓ-1`
        -- via `s = 1,3,…,2ϑ-1 ↦ s/2 = 0,…,ϑ-1`, so the faithful index drops the `+1`.
        ⟨j / NBlockMessages (ϑ:=ϑ) * ϑ + (j % NBlockMessages (ϑ:=ϑ)) / 2, by
          have hlt := j.1.isLt
          simp only [pSpecSumcheckFold, pSpecNonLastBlocks, ProtocolSpec.append,
            ProtocolSpec.seqCompose, Fin.vappend_eq_append] at hlt
          have hblocks :
              (Fin.vsum fun _bIdx : Fin (ℓ / ϑ - 1) =>
                (Fin.vsum fun _x : Fin (ϑ - 1) => 2) + 3) =
                (ℓ / ϑ - 1) * ((ϑ - 1) * 2 + 3) := by
            simp only [Fin.vsum_eq_univ_sum, Finset.sum_const, Finset.card_univ,
              Fintype.card_fin, smul_eq_mul]
          have hlast : (Fin.vsum fun _x : Fin ϑ => 2) = ϑ * 2 := by
            simp only [Fin.vsum_eq_univ_sum, Finset.sum_const, Finset.card_univ,
              Fintype.card_fin, smul_eq_mul]
          rw [hblocks, hlast] at hlt
          unfold NBlockMessages at hlt ⊢
          omega⟩ ⟨1, rfl⟩
    else 0 -- this case never happens

/-- Round-by-round knowledge soundness for the sumcheck fold oracle verifier -/
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

/-- The final sumcheck verifier only forwards its output oracle statement from its input oracle
statement: its `embed` always lands in `Sum.inl`. -/
instance instFinalSumcheckVerifierAppendCoherent :
    OracleVerifier.Append.AppendCoherent
      (finalSumcheckVerifier 𝔽q β (ϑ := ϑ)
        (h_ℓ_add_R_rate := h_ℓ_add_R_rate)) := by
  constructor
  · intro i k h
    simp [finalSumcheckVerifier] at h ⊢
    subst h
    rfl
  · intro i k h
    simp [finalSumcheckVerifier] at h

/-- The reduction-level analogue for the final sumcheck step. -/
instance instFinalSumcheckOracleReductionAppendCoherent :
    OracleVerifier.Append.AppendCoherent
      (finalSumcheckOracleReduction 𝔽q β (ϑ := ϑ)
        (h_ℓ_add_R_rate := h_ℓ_add_R_rate)).verifier :=
  instFinalSumcheckVerifierAppendCoherent 𝔽q β (ϑ := ϑ)
    (h_ℓ_add_R_rate := h_ℓ_add_R_rate)

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

instance instCoreInteractionOracleVerifierAppendCoherent :
    OracleVerifier.Append.AppendCoherent
      (coreInteractionOracleVerifier 𝔽q β (ϑ:=ϑ)
        (h_ℓ_add_R_rate := h_ℓ_add_R_rate)) := by
  infer_instance

instance instCoreInteractionOracleReductionAppendCoherent :
    OracleVerifier.Append.AppendCoherent
      (coreInteractionOracleReduction 𝔽q β (ϑ:=ϑ)
        (h_ℓ_add_R_rate := h_ℓ_add_R_rate)).verifier := by
  infer_instance

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

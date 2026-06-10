/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.ProofSystem.Logup.Security.OuterVerifierSupport
import ArkLib.ProofSystem.Logup.Security.OuterMaliciousClaim
import ArkLib.ProofSystem.Logup.Security.Soundness

open OracleComp OracleSpec ProtocolSpec
open scoped BigOperators NNReal ENNReal

/-!
# Outer malicious soundness: readback, transcript claim, and the claim-based state function

The run-level wiring of `hOuter@midLanguage` (design: issue #13 comment `4668149886`):
full verifier readback (with the pole guard), the transcript claim, acceptance ⟺ claim-vanishing,
and the complete claim-based RBR `StateFunction` whose `toFun_full` is proven. Axiom-clean.
-/

namespace Logup


variable {ι : Type} {oSpec : OracleSpec ι}
variable {F : Type} [Field F] [Fintype F] [DecidableEq F] [Fact ((-1 : F) ≠ 1)]
variable {n M : ℕ} {params : ProtocolParams M}

/-- **Full-field readback for the compiled outer verifier.** Every surviving output reads its
entire statement off the transcript — the challenge fields are the round-1/round-3 draws and the
output oracles are the input oracles plus the round-0/round-2 prover messages. -/
theorem outer_toVerifier_verify_support_full
    (stmt : StmtIn F n M) (oStmt : ∀ i, OStmtIn F n M i)
    (transcript : FullTranscript (outerPSpec F n params))
    (res : StmtAfterOuter F n M params × (∀ i, OStmtAfterOuter F n M params i))
    (hres : some res ∈ support
      (((outerVerifier oSpec F n M params).toVerifier.verify
        (stmt, oStmt) transcript).run)) :
    (∀ u : Hypercube n,
      chalX F n M params (transcript.challenges)
        + evalOnHypercube (tableOracle oStmt) u ≠ 0) ∧
    res.1.xChallenge = chalX F n M params (transcript.challenges) ∧
    res.1.zChallenge = (chalBatch F n M params (transcript.challenges)).1 ∧
    res.1.batchingScalars = (chalBatch F n M params (transcript.challenges)).2 ∧
    (∀ i, res.2 (.input i) = oStmt i) ∧
    res.2 .multiplicity = transcript.messages ⟨0, rfl⟩ ∧
    res.2 .helpers = transcript.messages ⟨2, rfl⟩ := by
  classical
  simp only [OracleVerifier.toVerifier] at hres
  rw [simulateQ_outerVerify_eq (oSpec := oSpec) (F := F) (n := n) (M := M) (params := params)
    (stmt := stmt) (oStmt := oStmt) (chal := transcript.challenges)
    (msgs := transcript.messages)] at hres
  by_cases hacc : ∀ u : Hypercube n,
      chalX F n M params transcript.challenges + evalOnHypercube (tableOracle oStmt) u ≠ 0
  · rw [if_pos hacc] at hres
    simp only [OptionT.run_pure, pure_bind, support_pure,
      Set.mem_singleton_iff, Option.some.injEq] at hres
    subst hres
    exact ⟨hacc, rfl, rfl, rfl, fun i => rfl, rfl, rfl⟩
  · rw [if_neg hacc] at hres
    simp only [OptionT.run_failure, failure_bind] at hres
    simp at hres






variable {ι : Type} {oSpec : OracleSpec ι}
variable {F : Type} [Field F] [Fintype F] [DecidableEq F] [Fact ((-1 : F) ≠ 1)]
variable {n M : ℕ} {params : ProtocolParams M}

/-- The after-outer mid-claim read directly off a full outer transcript: the batched hypercube
sum at the transcript's challenges and prover messages, against the input oracles. -/
noncomputable def transcriptClaim (oStmt : ∀ i, OStmtIn F n M i)
    (transcript : FullTranscript (outerPSpec F n params)) : F :=
  ∑ u : Hypercube n,
    qOnHypercube (canonicalGroups params) oStmt
      (transcript.messages ⟨0, rfl⟩) (transcript.messages ⟨2, rfl⟩)
      (chalX F n M params (transcript.challenges))
      (chalBatch F n M params (transcript.challenges)).1
      (chalBatch F n M params (transcript.challenges)).2 u

/-- **Accepted outputs land in `midLanguage` iff the transcript claim vanishes.** Combining the
full readback with the definition of `logupOuterSumcheckClaim`. -/
theorem outer_accept_mem_midLanguage_iff
    (stmt : StmtIn F n M) (oStmt : ∀ i, OStmtIn F n M i)
    (transcript : FullTranscript (outerPSpec F n params))
    (res : StmtAfterOuter F n M params × (∀ i, OStmtAfterOuter F n M params i))
    (hres : some res ∈ support
      (((outerVerifier oSpec F n M params).toVerifier.verify
        (stmt, oStmt) transcript).run)) :
    res ∈ midLanguage F n M params ↔ transcriptClaim oStmt transcript = 0 := by
  obtain ⟨-, hx, hz, hb, hin, hm, hh⟩ :=
    outer_toVerifier_verify_support_full stmt oStmt transcript res hres
  unfold midLanguage
  rw [Set.mem_setOf_eq]
  unfold logupOuterSumcheckClaim transcriptClaim
  constructor <;> intro h <;> rw [← h] <;>
    exact Finset.sum_congr rfl (fun u _ => by rw [hx, hz, hb, hm, hh, funext hin])


section MalSoundDefs

variable (F : Type) [Field F] [Fintype F] [DecidableEq F] [Fact ((-1 : F) ≠ 1)]
variable (n M : ℕ) (params : ProtocolParams M)

/-- The mid-claim assembled from the four outer-transcript entries. -/
noncomputable def entriesClaim (oStmt : ∀ i, OStmtIn F n M i)
    (mult : MultilinearOracle F n) (x : F)
    (helpers : HelperMessages F n params.numGroups)
    (zb : BatchingChallenge F n params.numGroups) : F :=
  ∑ u : Hypercube n,
    qOnHypercube (canonicalGroups params) oStmt mult helpers x zb.1 zb.2 u

/-- The claim-based RBR state for the outer phase at `midLanguage`. -/
def outerMidState (m : Fin 5) (stmt : StmtIn F n M × (∀ i, OStmtIn F n M i))
    (tr : (outerPSpec F n params).Transcript m) : Prop :=
  stmt ∈ (inputRelation F n M).language ∨
    (∃ h4 : 3 < m.val,
      (∀ u : Hypercube n,
        (show F from tr ⟨1, by omega⟩)
          + evalOnHypercube (tableOracle stmt.2) u ≠ 0) ∧
      entriesClaim F n M params stmt.2
        (show MultilinearOracle F n from tr ⟨0, by omega⟩)
        (show F from tr ⟨1, by omega⟩)
        (show HelperMessages F n params.numGroups from tr ⟨2, by omega⟩)
        (show BatchingChallenge F n params.numGroups from tr ⟨3, h4⟩) = 0) ∨
    (∃ h1 : 1 < m.val, m.val ≤ 3 ∧
      (show F from tr ⟨1, h1⟩) ∈
        outerBadChallenges params stmt.2
          (show MultilinearOracle F n from tr ⟨0, by omega⟩))








end MalSoundDefs

section MalSoundSF

variable {ι : Type} (oSpec : OracleSpec ι)
variable (F : Type) [Field F] [Fintype F] [DecidableEq F] [Fact ((-1 : F) ≠ 1)]
  [SampleableType F]
variable (n M : ℕ) (params : ProtocolParams M)
variable {σ : Type} (init : ProbComp σ) (impl : QueryImpl oSpec (StateT σ ProbComp))

local instance instInhabitedFieldMalSoundSF : Inhabited F := ⟨0⟩

/-- **The claim-based outer state function at `midLanguage`.** -/
noncomputable def outerMidStateFunction :
    ((outerVerifier oSpec F n M params).toVerifier).StateFunction init impl
      (inputRelation F n M).language (midLanguage F n M params) where
  toFun := outerMidState F n M params
  toFun_empty := fun stmt => by
    unfold outerMidState
    constructor
    · exact fun h => Or.inl h
    · rintro (h | ⟨h, -⟩ | ⟨h, -⟩)
      · exact h
      · exact absurd h (by omega)
      · exact absurd h (by omega)
  toFun_next := fun m hdir stmt tr hno msg => by
    fin_cases m
    · -- round 0
      unfold outerMidState at hno ⊢
      rintro (h | ⟨h, -⟩ | ⟨h, -⟩)
      · exact hno (Or.inl h)
      · exact absurd h (by norm_num)
      · exact absurd h (by norm_num)
    · exact absurd hdir (by exact fun h => by cases h)
    · -- round 2: entries 0/1 preserved by concat
      unfold outerMidState at hno ⊢
      rintro (h | ⟨h, -⟩ | ⟨h, -, hmem⟩)
      · exact hno (Or.inl h)
      · exact absurd h (by norm_num)
      · exact hno (Or.inr (Or.inr ⟨by norm_num, by norm_num, hmem⟩))
    · exact absurd hdir (by exact fun h => by cases h)
  toFun_full := fun stmt tr hno => by
    classical
    refine probEvent_eq_zero ?_
    intro x hx hmem
    rw [OptionT.mem_support_iff] at hx
    simp only [OptionT.run_mk, mem_support_bind_iff] at hx
    obtain ⟨s, -, hx⟩ := hx
    have hx' := _root_.support_simulateQ_run'_subset impl _ s hx
    have hguard :=
      (outer_toVerifier_verify_support_full stmt.1 stmt.2 tr x hx').1
    have hiff := outer_accept_mem_midLanguage_iff stmt.1 stmt.2 tr x hx'
    -- so the state at the last round is true — contradiction
    refine hno ?_
    unfold outerMidState
    exact Or.inr (Or.inl ⟨by norm_num, hguard, hiff.mp hmem⟩)





end MalSoundSF

end Logup

#print axioms Logup.outer_toVerifier_verify_support_full
#print axioms Logup.outer_accept_mem_midLanguage_iff
#print axioms Logup.outerMidStateFunction

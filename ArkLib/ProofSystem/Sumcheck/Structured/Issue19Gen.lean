import ArkLib.ProofSystem.Sumcheck.Structured.SingleRound
import ArkLib.OracleReduction.Completeness

/-! Dev: general perfect-completeness of `Sumcheck.Structured.roundOracleReduction`,
    parameterised by abstract relations + honest-round logic hypotheses.  Iterated via
    `lake env lean` against the warm `SingleRound`/`Completeness` oleans, isolated from the
    RingSwitching dependency churn.  Once verified this moves into `SingleRound.lean` and the
    #19 residual instantiates it. -/

open OracleSpec OracleComp ProtocolSpec Finset
open scoped NNReal

namespace Sumcheck.Structured

variable {L : Type} [CommRing L] [DecidableEq L] [Fintype L] [SampleableType L]
variable (ℓ : ℕ) [NeZero ℓ] (D : SumcheckDomain L ℓ)
variable (Context : Type) {ιₛᵢ : Type} {OStmtIn : ιₛᵢ → Type}
  [Oₛᵢ : ∀ j, OracleInterface (OStmtIn j)]
variable (d : ℕ)
variable {σ : Type} (init : ProbComp σ) (impl : QueryImpl []ₒ (StateT σ ProbComp))

local instance : (([]ₒ : OracleSpec PEmpty).Inhabited) where
  inhabited_B q := nomatch q
local instance : (([]ₒ : OracleSpec PEmpty).Fintype) where
  fintype_B q := nomatch q

local instance : ([(pSpecSumcheckRound L d).Challenge]ₒ).Inhabited := by
  refine { inhabited_B := ?_ }
  intro q
  rcases q with ⟨⟨j, hj⟩, _query⟩
  have hj_one : j = 1 := by
    fin_cases j
    · simp [pSpecSumcheckRound] at hj
    · rfl
  subst hj_one
  change Inhabited L
  exact ⟨0⟩

local instance : ([(pSpecSumcheckRound L d).Challenge]ₒ).Fintype := by
  refine { fintype_B := ?_ }
  intro q
  rcases q with ⟨⟨j, hj⟩, _query⟩
  have hj_one : j = 1 := by
    fin_cases j
    · simp [pSpecSumcheckRound] at hj
    · rfl
  subst hj_one
  change Fintype L
  infer_instance

/-- **General perfect completeness of one structured sumcheck round.**
The honest prover's round univariate `h_i = getSumcheckRoundPoly i witIn.H` passes the
verifier sum-check (`hCheck`), and the honest output lands in `relOut` at every challenge
(`hOut`); hence the round oracle reduction is perfectly complete (given `hInit`). -/
theorem roundOracleReduction_perfectCompleteness (i : Fin ℓ)
    (relIn : Set ((Statement (L := L) (ℓ := ℓ) Context i.castSucc × ∀ j, OStmtIn j)
      × SumcheckWitness L ℓ i.castSucc d))
    (relOut : Set ((Statement (L := L) (ℓ := ℓ) Context i.succ × ∀ j, OStmtIn j)
      × SumcheckWitness L ℓ i.succ d))
    (hInit : NeverFail init)
    (hCheck : ∀ stmtIn oStmtIn witIn, ((stmtIn, oStmtIn), witIn) ∈ relIn →
        (∑ b ∈ D.points i,
          (getSumcheckRoundPoly ℓ D (i := i) witIn.H).val.eval b) = stmtIn.sumcheck_target)
    (hOut : ∀ stmtIn oStmtIn witIn, ((stmtIn, oStmtIn), witIn) ∈ relIn → ∀ r : L,
        getRoundProverFinalOutput (L := L) ℓ Context (OStmtIn := OStmtIn) d i
          (stmtIn, oStmtIn, witIn, getSumcheckRoundPoly ℓ D (i := i) witIn.H, r) ∈ relOut) :
    OracleReduction.perfectCompleteness init impl relIn relOut
      (roundOracleReduction (L := L) ℓ D Context (OStmtIn := OStmtIn) d i) := by
  rw [OracleReduction.unroll_2_message_reduction_perfectCompleteness
      (oSpec := []ₒ) (pSpec := pSpecSumcheckRound L d)
      (roundOracleReduction (L := L) ℓ D Context (OStmtIn := OStmtIn) d i)
      relIn relOut init impl hInit (by rfl) (by rfl)
      (by simp only [Set.fmap_eq_image, IsEmpty.forall_iff, implies_true])]
  intro stmtIn oStmtIn witIn h_relIn
  simp_rw [probEvent_eq_one_iff]
  dsimp only [roundOracleReduction, roundOracleProver, roundOracleVerifier,
    OracleVerifier.toVerifier, FullTranscript.mk2]
  refine ⟨?_, ?_⟩
  · trace_state
    sorry
  · trace_state
    sorry

end Sumcheck.Structured

import ArkLib.ProofSystem.RingSwitching.SumcheckPhase
import ArkLib.OracleReduction.Completeness

open OracleSpec OracleComp ProtocolSpec Finset Polynomial MvPolynomial
  Module TensorProduct Nat Matrix
open scoped NNReal
open Sumcheck.Structured

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
variable {σ : Type} {init : ProbComp σ} {impl : QueryImpl []ₒ (StateT σ ProbComp)}

local instance : (([]ₒ : OracleSpec PEmpty).Inhabited) where
  inhabited_B q := nomatch q

local instance : (([]ₒ : OracleSpec PEmpty).Fintype) where
  fintype_B q := nomatch q

local instance : ∀ j, OracleInterface ((pSpecSumcheckRound L).Challenge j) :=
  ProtocolSpec.challengeOracleInterface

local instance : ([(pSpecSumcheckRound L).Challenge]ₒ).Inhabited := by
  refine { inhabited_B := ?_ }
  intro q
  rcases q with ⟨⟨i, hi⟩, query⟩
  have hi_one : i = 1 := by
    fin_cases i
    · simp at hi
    · rfl
  subst i
  cases query
  change Inhabited L
  exact ⟨0⟩

local instance : ([(pSpecSumcheckRound L).Challenge]ₒ).Fintype := by
  refine { fintype_B := ?_ }
  intro q
  rcases q with ⟨⟨i, hi⟩, query⟩
  have hi_one : i = 1 := by
    fin_cases i
    · simp at hi
    · rfl
  subst i
  cases query
  change Fintype L
  infer_instance

theorem iteratedSumcheckOracleReduction_perfectCompleteness_residual_holds
    (hInit : NeverFail init) :
    iteratedSumcheckOracleReduction_perfectCompleteness_residual
      (κ := κ) (L := L) (K := K) (P := P) (ℓ := ℓ) (ℓ' := ℓ') (h_l := h_l)
      (aOStmtIn := aOStmtIn) (init := init) (impl := impl) := by
  intro i
  letI : ([(pSpecSumcheckRound L).Challenge]ₒ).Inhabited := inferInstance
  letI : ([(pSpecSumcheckRound L).Challenge]ₒ).Fintype := inferInstance
  have key := OracleReduction.unroll_2_message_reduction_perfectCompleteness
    (oSpec := []ₒ) (pSpec := pSpecSumcheckRound L)
    (iteratedSumcheckOracleReduction κ L K P ℓ ℓ' aOStmtIn i)
    (sumcheckRoundRelation κ L K P ℓ ℓ' h_l aOStmtIn i.castSucc)
    (sumcheckRoundRelation κ L K P ℓ ℓ' h_l aOStmtIn i.succ)
    init impl hInit (by rfl) (by rfl)
    (by simp only [Set.fmap_eq_image, IsEmpty.forall_iff, implies_true])
  rw [key]
  intro stmtIn oStmtIn witIn h_relIn
  simp_rw [probEvent_eq_one_iff]
  dsimp only [iteratedSumcheckOracleReduction, iteratedSumcheckOracleProver,
    iteratedSumcheckOracleVerifier, OracleVerifier.toVerifier, FullTranscript.mk2]
  refine ⟨?_, ?_⟩
  · sorry
  · sorry

end
end RingSwitching.SumcheckPhase

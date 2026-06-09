import ArkLib.ToMathlib.SpartanBricks

open OracleComp OracleInterface ProtocolSpec Function Spartan.Spec Spartan

variable {R : Type} [CommRing R] [IsDomain R] [Fintype R] {pp : PublicParams}
variable {ι : Type} {oSpec : OracleSpec ι} [SampleableType R]

def firstSumcheckRelIn : Set ((Statement.AfterFirstChallenge R pp × ∀ i, OracleStatement.AfterFirstChallenge R pp i) × Unit) := Set.univ
def firstSumcheckRelOut : Set ((Statement.AfterFirstSumcheck R pp × ∀ i, OracleStatement.AfterFirstSumcheck R pp i) × Unit) := Set.univ

instance firstSumcheckContextLens_isComplete : Context.Lens.IsComplete (firstSumcheckRelIn (R:=R) (pp:=pp)) Set.univ (firstSumcheckRelOut (R:=R) (pp:=pp)) Set.univ (fun _ _ => True) (firstSumcheckContextLens pp).toContext where
  proj_complete _ _ _ := trivial
  lift_complete _ _ _ _ _ _ _ := trivial

theorem firstSumcheckReduction_completeness
    {σ : Type} (init : ProbComp σ) (impl : QueryImpl oSpec (StateT σ ProbComp)) :
    (firstSumcheckReduction pp oSpec).perfectCompleteness init impl firstSumcheckRelIn firstSumcheckRelOut := by
  apply OracleReduction.liftContext_perfectCompleteness (lens := (firstSumcheckContextLens pp).toContext) (stmtLens := firstSumcheckOracleLens pp oSpec)
  · rfl
  · apply Sumcheck.Spec.oracleReduction_perfectCompleteness

theorem firstSumcheckReduction_rbrKnowledgeSoundness
    {σ : Type} (init : ProbComp σ) (impl : QueryImpl oSpec (StateT σ ProbComp))
    (rbrKnowledgeError : (Sumcheck.Spec.pSpec R 3 pp.ℓ_m).ChallengeIdx → ℝ≥0)
    (h_inner : (Sumcheck.Spec.oracleReduction R 3 (boolEmbedding R) pp.ℓ_m oSpec).verifier.rbrKnowledgeSoundness init impl Set.univ Set.univ rbrKnowledgeError) :
    (firstSumcheckReduction pp oSpec).verifier.rbrKnowledgeSoundness init impl firstSumcheckRelIn firstSumcheckRelOut rbrKnowledgeError := by
  apply OracleVerifier.liftContext_rbrKnowledgeSoundness (lens := (firstSumcheckContextLens pp).toContext) (stmtLens := firstSumcheckOracleLens pp oSpec)
  · exact h_inner


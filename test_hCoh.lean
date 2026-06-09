import ArkLib.ProofSystem.Spartan.Basic

open Spartan OracleReduction OracleVerifier OracleStatement

variable {R : Type} [CommRing R] [IsDomain R] [Fintype R] [SampleableType R] {pp : PublicParams}
variable {ι : Type} {oSpec : OracleSpec ι}

instance instFirstChallengeVerifierAppendCoherent :
    OracleVerifier.Append.AppendCoherent (oracleReduction.firstChallenge R pp oSpec).verifier where
  hCohInl i k h := by
    cases i with
    | inl j =>
      dsimp [oracleReduction.firstChallenge, firstChallengeOracleLens, OracleVerifier.liftContext] at h
      obtain rfl := Sum.inl.inj h
      -- now the goal is `instRecType (Sum.inl j) = cast (by rw [rfl]) (instRecType (Sum.inl (embed j)))`
      -- but instRecType (Sum.inl j) is exactly instRecType (Sum.inl (embed j)) because of lens.hEq?
      -- Wait! What is lens.hEq?
      apply heq_of_eq at h
      -- actually we can just apply proof irrelevance on cast
      sorry
    | inr j =>
      dsimp [oracleReduction.firstChallenge, firstChallengeOracleLens, OracleVerifier.liftContext] at h
      contradiction
  hCohInr i k h := by
    cases i with
    | inl j =>
      dsimp [oracleReduction.firstChallenge, firstChallengeOracleLens, OracleVerifier.liftContext] at h
      contradiction
    | inr j =>
      dsimp [oracleReduction.firstChallenge, firstChallengeOracleLens, OracleVerifier.liftContext] at h
      obtain rfl := Sum.inr.inj h
      rfl

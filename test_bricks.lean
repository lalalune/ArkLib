import ArkLib.ToMathlib.SpartanBricks
import ArkLib.ProofSystem.Spartan.FirstSumcheckComplete
import ArkLib.ProofSystem.Spartan.SecondSumcheckComplete

open OracleComp OracleInterface ProtocolSpec Function Spartan.Spec Spartan

variable {R : Type} [CommRing R] [IsDomain R] [Fintype R] [DecidableEq R] {pp : PublicParams}
variable {ι : Type} {oSpec : OracleSpec ι} [SampleableType R]

noncomputable def composedPIOP_Rc (R : Type) [CommRing R] [IsDomain R] [Fintype R] [DecidableEq R] (pp : PublicParams) (oSpec : OracleSpec ι) [SampleableType R] :=
  (((((Spartan.Spec.oracleReduction.firstMessage R pp oSpec)
  .append (Spartan.Spec.oracleReduction.firstChallenge R pp oSpec))
  .append (firstSumcheckReduction pp oSpec))
  .append (Spartan.Spec.oracleReduction.sendEvalClaim R pp oSpec))
  .append (Spartan.Spec.oracleReduction.linearCombination R pp oSpec))
  .append (secondSumcheckReduction pp oSpec)
  .append (finalCheck R pp oSpec)


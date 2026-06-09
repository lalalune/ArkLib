import ArkLib.ToMathlib.SpartanBricks
open Spartan

def myComposedPIOP {R : Type} [CommRing R] (pp : PublicParams) (oSpec : OracleSpec) :
    OracleReduction oSpec
      (Statement R pp) (OracleStatement R pp) (Witness R pp)
      (FinalStatement R pp) (FinalOracleStatement R pp) Unit
      _ :=
  OracleReduction.append
    (OracleReduction.append
      (OracleReduction.append
        (OracleReduction.append
          (OracleReduction.append
            (OracleReduction.append
              (Spartan.Spec.oracleReduction.firstMessage R pp oSpec)
              (Spartan.Spec.oracleReduction.firstChallenge R pp oSpec))
            (Classical.choice (firstSumcheckResidual_holds R pp oSpec)))
          (Spartan.Spec.oracleReduction.sendEvalClaim R pp oSpec))
        (Spartan.Spec.oracleReduction.linearCombination R pp oSpec))
      (Classical.choice (secondSumcheckResidual_holds R pp oSpec)))
    (CheckClaim.oracleReduction oSpec (FinalStatement R pp) (FinalOracleStatement R pp))

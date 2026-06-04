/-
Copyright (c) 2024-2025 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

import ArkLib.OracleReduction.LiftContext.Reduction

/-!
  ## Lifting Oracle Reductions to Larger Contexts

  This file is a continuation of `LiftContext/Reduction.lean`, where we lift oracle reductions to
  larger contexts.

  The only new thing here is the definition of the oracle verifier. The rest (oracle prover +
  security properties) are just ported from `LiftContext/Reduction.lean`, with suitable conversions.
-/

open OracleSpec OracleComp ProtocolSpec

open scoped NNReal

variable {ι : Type} {oSpec : OracleSpec ι}
  {OuterStmtIn OuterWitIn OuterStmtOut OuterWitOut : Type}
  {Outer_ιₛᵢ : Type} {OuterOStmtIn : Outer_ιₛᵢ → Type} [∀ i, OracleInterface (OuterOStmtIn i)]
  {Outer_ιₛₒ : Type} {OuterOStmtOut : Outer_ιₛₒ → Type} [∀ i, OracleInterface (OuterOStmtOut i)]
  {Inner_ιₛᵢ : Type} {InnerOStmtIn : Inner_ιₛᵢ → Type} [∀ i, OracleInterface (InnerOStmtIn i)]
  {Inner_ιₛₒ : Type} {InnerOStmtOut : Inner_ιₛₒ → Type} [∀ i, OracleInterface (InnerOStmtOut i)]
  {InnerStmtIn InnerWitIn InnerStmtOut InnerWitOut : Type}
  {n : ℕ} {pSpec : ProtocolSpec n}

/-- The lifting of the prover from an inner oracle reduction to an outer oracle reduction, requiring
  an associated oracle context lens -/
def OracleProver.liftContext
    (lens : OracleContext.Lens OuterStmtIn OuterStmtOut InnerStmtIn InnerStmtOut
                              OuterOStmtIn OuterOStmtOut InnerOStmtIn InnerOStmtOut
                              OuterWitIn OuterWitOut InnerWitIn InnerWitOut)
    (P : OracleProver oSpec InnerStmtIn InnerOStmtIn InnerWitIn
                            InnerStmtOut InnerOStmtOut InnerWitOut pSpec) :
    OracleProver oSpec OuterStmtIn OuterOStmtIn OuterWitIn
                      OuterStmtOut OuterOStmtOut OuterWitOut pSpec :=
  Prover.liftContext lens.toContext P

variable [∀ i, OracleInterface (pSpec.Message i)]

/-- The lifting of the verifier from an inner oracle reduction to an outer oracle reduction,
  requiring an associated oracle statement lens -/
def OracleVerifier.liftContext
    (lens : OracleStatement.Lens OuterStmtIn OuterStmtOut InnerStmtIn InnerStmtOut
                              OuterOStmtIn OuterOStmtOut InnerOStmtIn InnerOStmtOut)
    (V : OracleVerifier oSpec InnerStmtIn InnerOStmtIn InnerStmtOut InnerOStmtOut pSpec) :
      OracleVerifier oSpec OuterStmtIn OuterOStmtIn OuterStmtOut OuterOStmtOut pSpec where
  -- The current bundled oracle-statement lens does not carry enough data to project the
  -- inner verifier input or simulate its input-oracle queries here.
  verify := fun _ _ => OptionT.mk (pure none)
  embed := by
    have := V.embed

    sorry
  hEq := sorry

/-- The lifting of an inner oracle reduction to an outer oracle reduction,
  requiring an associated oracle context lens -/
def OracleReduction.liftContext
    (lens : OracleContext.Lens OuterStmtIn OuterStmtOut InnerStmtIn InnerStmtOut
                              OuterOStmtIn OuterOStmtOut InnerOStmtIn InnerOStmtOut
                              OuterWitIn OuterWitOut InnerWitIn InnerWitOut)
    (R : OracleReduction oSpec InnerStmtIn InnerOStmtIn InnerWitIn
                            InnerStmtOut InnerOStmtOut InnerWitOut pSpec) :
      OracleReduction oSpec OuterStmtIn OuterOStmtIn OuterWitIn
                      OuterStmtOut OuterOStmtOut OuterWitOut pSpec where
  prover := R.prover.liftContext lens
  verifier := R.verifier.liftContext lens.stmt

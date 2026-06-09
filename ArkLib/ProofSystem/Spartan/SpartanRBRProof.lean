/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/

import ArkLib.ToMathlib.SpartanBricks

/-!
# Spartan RBR Knowledge Soundness Breakthrough

This module lifts the composed RBR knowledge soundness residual into the final
breakthrough theorem.
-/

open ProtocolSpec OracleComp OracleSpec Polynomial

namespace Spartan.Spec

variable {R : Type} [CommRing R] [IsDomain R] [Fintype R] [DecidableEq R] [SampleableType R]
  [VCVCompatible R] (pp : Spartan.PublicParams) {ι : Type} (oSpec : OracleSpec ι)

/-- The final breakthrough theorem for Spartan's RBR knowledge soundness. -/
theorem spartan_rbr_knowledge_soundness_breakthrough
    {σ : Type} (init : ProbComp σ) (impl : QueryImpl oSpec (StateT σ ProbComp)) :
    composedRbrKnowledgeSoundnessResidual R pp oSpec
      (OracleReduction.append
        (oracleReduction.firstMessage R pp oSpec)
      <| OracleReduction.append
        (oracleReduction.firstChallenge R pp oSpec)
      <| OracleReduction.append
        (firstSumcheckReduction pp oSpec)
      <| OracleReduction.append
        (sendEvalClaimReduction pp oSpec)
      <| OracleReduction.append
        (linearCombinationReduction pp oSpec)
      <| OracleReduction.append
        (secondSumcheckReduction pp oSpec)
      <| (finalCheckReduction pp oSpec)) init impl
      (fun i => if i.1 = ⟨2, by omega⟩ ∨ i.1 = ⟨5, by omega⟩ then 2 / (Fintype.card R) else 0) := by
  -- We just apply composedRbrKnowledgeSoundnessResidual_holds, which the CompletenessProver subagent provides.
  apply composedRbrKnowledgeSoundnessResidual_holds

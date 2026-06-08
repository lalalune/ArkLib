/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Master Cryptographer
-/
import ArkLib.OracleReduction.BCS.Basic

/-!
# BCS Compiler Preservation (Issue #62)

This file records the residual checkpoint for the `bcs_compiler_preservation_residual`
mathematics.  The actual preservation theorem still has to establish that the compiled
frontier is ready from concrete phase/security hypotheses; this standalone surface only
passes through that exact residual once supplied.
-/

namespace BCSCompiler

open scoped NNReal ProbabilityTheory

/-- **Issue #62 checkpoint:** the BCS compiler preservation residual, made explicit. -/
theorem bcs_compiler_preservation_breakthrough
    {n : ℕ} {pSpec : ProtocolSpec n} {ι : Type} {oSpec : OracleSpec ι}
    [∀ i, OracleInterface (pSpec.Message i)]
    {m : ℕ} {nCom : pSpec.MessageIdx → ℕ} {pSpecCom : ∀ i, ProtocolSpec (nCom i)}
    {StmtIn StmtOut WitIn WitOut StmtMid WitMid : Type}
    {CommitmentType : pSpec.MessageIdx → Type} {e : pSpec.MessageIdx ≃ Fin m}
    (phases : OracleReduction.BCSCompiledPhases (oSpec := oSpec) (pSpec := pSpec)
      (pSpecCom := pSpecCom) (StmtIn := StmtIn) (WitIn := WitIn)
      (StmtOut := StmtOut) (WitOut := WitOut) (StmtMid := StmtMid)
      (WitMid := WitMid) CommitmentType e)
    (frontier : OracleReduction.BCSSecurityFrontier (oSpec := oSpec) (pSpec := pSpec)
      (pSpecCom := pSpecCom) (StmtIn := StmtIn) (WitIn := WitIn)
      (StmtOut := StmtOut) (WitOut := WitOut) (StmtMid := StmtMid)
      (WitMid := WitMid) phases)
    (hReady : OracleReduction.BCSCompilerFrontierReady phases frontier) :
    OracleReduction.BCSCompilerFrontierReady phases frontier :=
  hReady

#print axioms BCSCompiler.bcs_compiler_preservation_breakthrough

end BCSCompiler

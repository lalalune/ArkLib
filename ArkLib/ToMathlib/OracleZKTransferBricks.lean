/-
Copyright (c) 2024-2025 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/

import ArkLib.OracleReduction.Security.OracleZeroKnowledge
import ArkLib.ToMathlib.ZKTransferBricks

/-!
  # Oracle-reduction HVZK transfer bricks for #112

  This module lifts the reusable Reduction-level transfer lemmas from
  `ArkLib.ToMathlib.ZKTransferBricks` to the `OracleReduction` HVZK API boundary.
-/

noncomputable section

open OracleComp OracleSpec ProtocolSpec
open scoped NNReal

namespace OracleReduction

variable {ι : Type} {oSpec : OracleSpec ι}
  {StmtIn : Type} {ιₛᵢ : Type} {OStmtIn : ιₛᵢ → Type} {WitIn : Type}
  {StmtOut : Type} {ιₛₒ : Type} {OStmtOut : ιₛₒ → Type} {WitOut : Type}
  {n : ℕ} {pSpec : ProtocolSpec n}
  [∀ i, OracleInterface (OStmtIn i)] [∀ i, OracleInterface (pSpec.Message i)]
  [∀ i, SampleableType (pSpec.Challenge i)]
  {σ : Type}

/-- **OracleReduction perfect HVZK transfers along an equal honest distribution.** -/
theorem perfectHVZK.congr_honestDist
    {init : ProbComp σ} {impl : QueryImpl oSpec (StateT σ ProbComp)}
    {rel : Set ((StmtIn × (∀ i, OStmtIn i)) × WitIn)}
    {R₁ R₂ : OracleReduction oSpec StmtIn OStmtIn WitIn StmtOut OStmtOut WitOut pSpec}
    {sim : TranscriptSimulator oSpec StmtIn OStmtIn pSpec}
    (h : perfectHVZK init impl rel R₁ sim)
    (hdist : ∀ stmtIn witIn, (stmtIn, witIn) ∈ rel →
      evalDist (Reduction.honestTranscriptDist init impl R₁.toReduction stmtIn witIn) =
        evalDist (Reduction.honestTranscriptDist init impl R₂.toReduction stmtIn witIn)) :
    perfectHVZK init impl rel R₂ sim :=
  Reduction.perfectHVZK.congr_honestDist h hdist

/-- **OracleReduction statistical HVZK transfers along an equal honest distribution.** -/
theorem statisticalHVZK.congr_honestDist
    {init : ProbComp σ} {impl : QueryImpl oSpec (StateT σ ProbComp)}
    {rel : Set ((StmtIn × (∀ i, OStmtIn i)) × WitIn)}
    {R₁ R₂ : OracleReduction oSpec StmtIn OStmtIn WitIn StmtOut OStmtOut WitOut pSpec}
    {sim : TranscriptSimulator oSpec StmtIn OStmtIn pSpec} {ε : ℝ≥0}
    (h : statisticalHVZK init impl rel R₁ sim ε)
    (hdist : ∀ stmtIn witIn, (stmtIn, witIn) ∈ rel →
      evalDist (Reduction.honestTranscriptDist init impl R₁.toReduction stmtIn witIn) =
        evalDist (Reduction.honestTranscriptDist init impl R₂.toReduction stmtIn witIn)) :
    statisticalHVZK init impl rel R₂ sim ε :=
  Reduction.statisticalHVZK.congr_honestDist h hdist

/-- **OracleReduction perfect HVZK is preserved under an equal simulator distribution.** -/
theorem perfectHVZK.simulator_congr
    {init : ProbComp σ} {impl : QueryImpl oSpec (StateT σ ProbComp)}
    {rel : Set ((StmtIn × (∀ i, OStmtIn i)) × WitIn)}
    {R : OracleReduction oSpec StmtIn OStmtIn WitIn StmtOut OStmtOut WitOut pSpec}
    {sim sim' : TranscriptSimulator oSpec StmtIn OStmtIn pSpec}
    (h : perfectHVZK init impl rel R sim)
    (hsim : ∀ stmtIn, evalDist (sim stmtIn) = evalDist (sim' stmtIn)) :
    perfectHVZK init impl rel R sim' :=
  Reduction.perfectHVZK.simulator_congr h hsim

/-- **OracleReduction statistical HVZK is preserved under an equal simulator distribution.** -/
theorem statisticalHVZK.simulator_congr
    {init : ProbComp σ} {impl : QueryImpl oSpec (StateT σ ProbComp)}
    {rel : Set ((StmtIn × (∀ i, OStmtIn i)) × WitIn)}
    {R : OracleReduction oSpec StmtIn OStmtIn WitIn StmtOut OStmtOut WitOut pSpec}
    {sim sim' : TranscriptSimulator oSpec StmtIn OStmtIn pSpec} {ε : ℝ≥0}
    (h : statisticalHVZK init impl rel R sim ε)
    (hsim : ∀ stmtIn, evalDist (sim stmtIn) = evalDist (sim' stmtIn)) :
    statisticalHVZK init impl rel R sim' ε :=
  Reduction.statisticalHVZK.simulator_congr h hsim

/-- **Triangle composition of statistical HVZK at the OracleReduction API boundary.** -/
theorem statisticalHVZK.simulator_triangle
    {init : ProbComp σ} {impl : QueryImpl oSpec (StateT σ ProbComp)}
    {rel : Set ((StmtIn × (∀ i, OStmtIn i)) × WitIn)}
    {R : OracleReduction oSpec StmtIn OStmtIn WitIn StmtOut OStmtOut WitOut pSpec}
    {sim₁ sim₂ : TranscriptSimulator oSpec StmtIn OStmtIn pSpec} {ε₁ ε₂ : ℝ≥0}
    (h₁ : statisticalHVZK init impl rel R sim₁ ε₁)
    (h₂ : ∀ stmtIn witIn, (stmtIn, witIn) ∈ rel →
      tvDist (Reduction.honestTranscriptDist init impl R.toReduction stmtIn witIn)
        (sim₂ stmtIn) ≤ (ε₂ : ℝ)) :
    ∀ stmtIn witIn, (stmtIn, witIn) ∈ rel →
      tvDist (sim₁ stmtIn) (sim₂ stmtIn) ≤ ((ε₁ + ε₂ : ℝ≥0) : ℝ) :=
  Reduction.statisticalHVZK.simulator_triangle h₁ h₂

/-- **Approximate honest-distribution transfer at the OracleReduction API boundary.** -/
theorem statisticalHVZK.triangle_honestDist
    {init : ProbComp σ} {impl : QueryImpl oSpec (StateT σ ProbComp)}
    {rel : Set ((StmtIn × (∀ i, OStmtIn i)) × WitIn)}
    {R₁ R₂ : OracleReduction oSpec StmtIn OStmtIn WitIn StmtOut OStmtOut WitOut pSpec}
    {sim : TranscriptSimulator oSpec StmtIn OStmtIn pSpec} {ε₁ ε₂ : ℝ≥0}
    (h : statisticalHVZK init impl rel R₁ sim ε₁)
    (hdist : ∀ stmtIn witIn, (stmtIn, witIn) ∈ rel →
      tvDist (Reduction.honestTranscriptDist init impl R₁.toReduction stmtIn witIn)
        (Reduction.honestTranscriptDist init impl R₂.toReduction stmtIn witIn) ≤ (ε₂ : ℝ)) :
    statisticalHVZK init impl rel R₂ sim (ε₁ + ε₂) :=
  Reduction.statisticalHVZK.triangle_honestDist h hdist

/-- **OracleReduction constant-simulator criterion for perfect HVZK.** -/
theorem perfectHVZK_of_honestDist_eq_const
    {init : ProbComp σ} {impl : QueryImpl oSpec (StateT σ ProbComp)}
    {rel : Set ((StmtIn × (∀ i, OStmtIn i)) × WitIn)}
    {R : OracleReduction oSpec StmtIn OStmtIn WitIn StmtOut OStmtOut WitOut pSpec}
    (d : OptionT ProbComp (FullTranscript pSpec))
    (hdist : ∀ stmtIn witIn, (stmtIn, witIn) ∈ rel →
      evalDist (Reduction.honestTranscriptDist init impl R.toReduction stmtIn witIn) =
        evalDist d) :
    perfectHVZK init impl rel R (fun _ => d) :=
  Reduction.perfectHVZK_of_honestDist_eq_const d hdist

/-- **OracleReduction constant-simulator criterion for statistical HVZK.** -/
theorem statisticalHVZK_of_honestDist_eq_const
    {init : ProbComp σ} {impl : QueryImpl oSpec (StateT σ ProbComp)}
    {rel : Set ((StmtIn × (∀ i, OStmtIn i)) × WitIn)}
    {R : OracleReduction oSpec StmtIn OStmtIn WitIn StmtOut OStmtOut WitOut pSpec}
    (d : OptionT ProbComp (FullTranscript pSpec))
    (hdist : ∀ stmtIn witIn, (stmtIn, witIn) ∈ rel →
      evalDist (Reduction.honestTranscriptDist init impl R.toReduction stmtIn witIn) =
        evalDist d)
    (ε : ℝ≥0) :
    statisticalHVZK init impl rel R (fun _ => d) ε :=
  Reduction.statisticalHVZK_of_honestDist_eq_const d hdist ε

/-- **OracleReduction `isHVZK` from the constant-simulator criterion.** -/
theorem isHVZK_of_honestDist_eq_const
    {init : ProbComp σ} {impl : QueryImpl oSpec (StateT σ ProbComp)}
    {rel : Set ((StmtIn × (∀ i, OStmtIn i)) × WitIn)}
    {R : OracleReduction oSpec StmtIn OStmtIn WitIn StmtOut OStmtOut WitOut pSpec}
    (d : OptionT ProbComp (FullTranscript pSpec))
    (hdist : ∀ stmtIn witIn, (stmtIn, witIn) ∈ rel →
      evalDist (Reduction.honestTranscriptDist init impl R.toReduction stmtIn witIn) =
        evalDist d) :
    isHVZK init impl rel R :=
  ⟨fun _ => d, perfectHVZK_of_honestDist_eq_const d hdist⟩

/-- **OracleReduction `isStatHVZK` from the constant-simulator criterion.** -/
theorem isStatHVZK_of_honestDist_eq_const
    {init : ProbComp σ} {impl : QueryImpl oSpec (StateT σ ProbComp)}
    {rel : Set ((StmtIn × (∀ i, OStmtIn i)) × WitIn)}
    {R : OracleReduction oSpec StmtIn OStmtIn WitIn StmtOut OStmtOut WitOut pSpec}
    (d : OptionT ProbComp (FullTranscript pSpec))
    (hdist : ∀ stmtIn witIn, (stmtIn, witIn) ∈ rel →
      evalDist (Reduction.honestTranscriptDist init impl R.toReduction stmtIn witIn) =
        evalDist d)
    (ε : ℝ≥0) :
    isStatHVZK init impl rel R ε :=
  ⟨fun _ => d, statisticalHVZK_of_honestDist_eq_const d hdist ε⟩

/-- **OracleReduction `isHVZK` transfers along an equal honest distribution.** -/
theorem isHVZK.congr_honestDist
    {init : ProbComp σ} {impl : QueryImpl oSpec (StateT σ ProbComp)}
    {rel : Set ((StmtIn × (∀ i, OStmtIn i)) × WitIn)}
    {R₁ R₂ : OracleReduction oSpec StmtIn OStmtIn WitIn StmtOut OStmtOut WitOut pSpec}
    (h : isHVZK init impl rel R₁)
    (hdist : ∀ stmtIn witIn, (stmtIn, witIn) ∈ rel →
      evalDist (Reduction.honestTranscriptDist init impl R₁.toReduction stmtIn witIn) =
        evalDist (Reduction.honestTranscriptDist init impl R₂.toReduction stmtIn witIn)) :
    isHVZK init impl rel R₂ :=
  let ⟨sim, hsim⟩ := h
  ⟨sim, hsim.congr_honestDist hdist⟩

/-- **OracleReduction `isStatHVZK` transfers along an equal honest distribution.** -/
theorem isStatHVZK.congr_honestDist
    {init : ProbComp σ} {impl : QueryImpl oSpec (StateT σ ProbComp)}
    {rel : Set ((StmtIn × (∀ i, OStmtIn i)) × WitIn)}
    {R₁ R₂ : OracleReduction oSpec StmtIn OStmtIn WitIn StmtOut OStmtOut WitOut pSpec}
    {ε : ℝ≥0}
    (h : isStatHVZK init impl rel R₁ ε)
    (hdist : ∀ stmtIn witIn, (stmtIn, witIn) ∈ rel →
      evalDist (Reduction.honestTranscriptDist init impl R₁.toReduction stmtIn witIn) =
        evalDist (Reduction.honestTranscriptDist init impl R₂.toReduction stmtIn witIn)) :
    isStatHVZK init impl rel R₂ ε :=
  let ⟨sim, hsim⟩ := h
  ⟨sim, hsim.congr_honestDist hdist⟩

/-- **Existential approximate honest-distribution transfer at the OracleReduction API boundary.** -/
theorem isStatHVZK.triangle_honestDist
    {init : ProbComp σ} {impl : QueryImpl oSpec (StateT σ ProbComp)}
    {rel : Set ((StmtIn × (∀ i, OStmtIn i)) × WitIn)}
    {R₁ R₂ : OracleReduction oSpec StmtIn OStmtIn WitIn StmtOut OStmtOut WitOut pSpec}
    {ε₁ ε₂ : ℝ≥0}
    (h : isStatHVZK init impl rel R₁ ε₁)
    (hdist : ∀ stmtIn witIn, (stmtIn, witIn) ∈ rel →
      tvDist (Reduction.honestTranscriptDist init impl R₁.toReduction stmtIn witIn)
        (Reduction.honestTranscriptDist init impl R₂.toReduction stmtIn witIn) ≤ (ε₂ : ℝ)) :
    isStatHVZK init impl rel R₂ (ε₁ + ε₂) :=
  let ⟨sim, hsim⟩ := h
  ⟨sim, hsim.triangle_honestDist hdist⟩

#print axioms perfectHVZK.congr_honestDist
#print axioms statisticalHVZK.congr_honestDist
#print axioms perfectHVZK.simulator_congr
#print axioms statisticalHVZK.simulator_congr
#print axioms statisticalHVZK.simulator_triangle
#print axioms statisticalHVZK.triangle_honestDist
#print axioms perfectHVZK_of_honestDist_eq_const
#print axioms statisticalHVZK_of_honestDist_eq_const
#print axioms isHVZK_of_honestDist_eq_const
#print axioms isStatHVZK_of_honestDist_eq_const
#print axioms isHVZK.congr_honestDist
#print axioms isStatHVZK.congr_honestDist
#print axioms isStatHVZK.triangle_honestDist

end OracleReduction

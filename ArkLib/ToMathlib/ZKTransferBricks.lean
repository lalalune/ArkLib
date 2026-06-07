/-
Copyright (c) 2024-2025 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/

import ArkLib.OracleReduction.Security.ZeroKnowledge

/-!
  # Scratch: HVZK transfer / composability bricks for #112

  Reusable lemmas that downstream simulator-composition and Fiat-Shamir HVZK transfer steps need:

  - `perfectHVZK.congr_honestDist`: perfect HVZK transfers to any reduction with the same honest
    transcript distribution (the simulator is reused unchanged).
  - `perfectHVZK.simulator_congr`: perfect HVZK is preserved when swapping in an
    `evalDist`-equal simulator.
  - `statisticalHVZK.simulator_triangle`: two statistical-HVZK bounds compose by the triangle
    inequality, giving a combined error budget. This is the shape used when transferring a
    simulator across an `evalDist`-equal intermediate honest distribution.
  - `perfectHVZK_of_honestDist_eq_const`: a constant simulator achieves perfect HVZK whenever the
    honest transcript distribution is `evalDist`-equal to a fixed distribution, generalizing the
    zero-round identity instance.

  Everything is stated over the promoted `Reduction.perfectHVZK` / `statisticalHVZK` vocabulary in
  `ArkLib.OracleReduction.Security.ZeroKnowledge`.
-/

noncomputable section

open OracleComp OracleSpec ProtocolSpec
open scoped NNReal

namespace Reduction

variable {ι : Type} {oSpec : OracleSpec ι}
  {StmtIn WitIn StmtOut WitOut : Type}
  {n : ℕ} {pSpec : ProtocolSpec n} [∀ i, SampleableType (pSpec.Challenge i)]
  {σ : Type}

/-- **Perfect HVZK transfers along an `evalDist`-equal honest distribution.** If two reductions have
the same honest transcript distribution on every related pair, a simulator that is perfect-HVZK for
one is perfect-HVZK for the other. -/
theorem perfectHVZK.congr_honestDist
    {init : ProbComp σ} {impl : QueryImpl oSpec (StateT σ ProbComp)}
    {rel : Set (StmtIn × WitIn)}
    {R₁ R₂ : Reduction oSpec StmtIn WitIn StmtOut WitOut pSpec}
    {sim : TranscriptSimulator oSpec StmtIn pSpec}
    (h : perfectHVZK init impl rel R₁ sim)
    (hdist : ∀ stmtIn witIn, (stmtIn, witIn) ∈ rel →
      evalDist (honestTranscriptDist init impl R₁ stmtIn witIn) =
        evalDist (honestTranscriptDist init impl R₂ stmtIn witIn)) :
    perfectHVZK init impl rel R₂ sim := by
  intro stmtIn witIn hMem
  rw [← hdist stmtIn witIn hMem]
  exact h stmtIn witIn hMem

/-- **Statistical HVZK transfers along an `evalDist`-equal honest distribution.** The same
simulator and error budget apply to any reduction with the same honest transcript distribution. -/
theorem statisticalHVZK.congr_honestDist
    {init : ProbComp σ} {impl : QueryImpl oSpec (StateT σ ProbComp)}
    {rel : Set (StmtIn × WitIn)}
    {R₁ R₂ : Reduction oSpec StmtIn WitIn StmtOut WitOut pSpec}
    {sim : TranscriptSimulator oSpec StmtIn pSpec} {ε : ℝ≥0}
    (h : statisticalHVZK init impl rel R₁ sim ε)
    (hdist : ∀ stmtIn witIn, (stmtIn, witIn) ∈ rel →
      evalDist (honestTranscriptDist init impl R₁ stmtIn witIn) =
        evalDist (honestTranscriptDist init impl R₂ stmtIn witIn)) :
    statisticalHVZK init impl rel R₂ sim ε := by
  intro stmtIn witIn hMem
  unfold tvDist
  rw [← hdist stmtIn witIn hMem]
  exact h stmtIn witIn hMem

/-- **Perfect HVZK is preserved under an `evalDist`-equal simulator.** Swapping in a simulator that
produces the same transcript distribution everywhere preserves perfect HVZK. -/
theorem perfectHVZK.simulator_congr
    {init : ProbComp σ} {impl : QueryImpl oSpec (StateT σ ProbComp)}
    {rel : Set (StmtIn × WitIn)}
    {R : Reduction oSpec StmtIn WitIn StmtOut WitOut pSpec}
    {sim sim' : TranscriptSimulator oSpec StmtIn pSpec}
    (h : perfectHVZK init impl rel R sim)
    (hsim : ∀ stmtIn, evalDist (sim stmtIn) = evalDist (sim' stmtIn)) :
    perfectHVZK init impl rel R sim' := by
  intro stmtIn witIn hMem
  rw [← hsim stmtIn]
  exact h stmtIn witIn hMem

/-- **Triangle composition of statistical HVZK.** If `sim₁` is within `ε₁` of the honest
distribution and the honest distribution is within `ε₂` of `sim₂`'s, then `sim₁` is within
`ε₁ + ε₂` of `sim₂`. Used when transferring a simulator through an intermediate distribution. -/
theorem statisticalHVZK.simulator_triangle
    {init : ProbComp σ} {impl : QueryImpl oSpec (StateT σ ProbComp)}
    {rel : Set (StmtIn × WitIn)}
    {R : Reduction oSpec StmtIn WitIn StmtOut WitOut pSpec}
    {sim₁ sim₂ : TranscriptSimulator oSpec StmtIn pSpec} {ε₁ ε₂ : ℝ≥0}
    (h₁ : statisticalHVZK init impl rel R sim₁ ε₁)
    (h₂ : ∀ stmtIn witIn, (stmtIn, witIn) ∈ rel →
      tvDist (honestTranscriptDist init impl R stmtIn witIn) (sim₂ stmtIn) ≤ (ε₂ : ℝ)) :
    ∀ stmtIn witIn, (stmtIn, witIn) ∈ rel →
      tvDist (sim₁ stmtIn) (sim₂ stmtIn) ≤ ((ε₁ + ε₂ : ℝ≥0) : ℝ) := by
  intro stmtIn witIn hMem
  have hstep₁ := h₁ stmtIn witIn hMem
  have hstep₂ := h₂ stmtIn witIn hMem
  have htri := tvDist_triangle (sim₁ stmtIn)
    (honestTranscriptDist init impl R stmtIn witIn) (sim₂ stmtIn)
  calc tvDist (sim₁ stmtIn) (sim₂ stmtIn)
      ≤ tvDist (sim₁ stmtIn) (honestTranscriptDist init impl R stmtIn witIn)
          + tvDist (honestTranscriptDist init impl R stmtIn witIn) (sim₂ stmtIn) := htri
    _ ≤ (ε₁ : ℝ) + (ε₂ : ℝ) := add_le_add hstep₁ hstep₂
    _ = ((ε₁ + ε₂ : ℝ≥0) : ℝ) := by push_cast; ring

/-- **Constant-simulator criterion for perfect HVZK.** If the honest transcript distribution is
`evalDist`-equal to a fixed distribution `d` on every related pair, then the constant simulator
returning `d` achieves perfect HVZK. This generalizes the zero-round identity instance, where
`d = pure default`. -/
theorem perfectHVZK_of_honestDist_eq_const
    {init : ProbComp σ} {impl : QueryImpl oSpec (StateT σ ProbComp)}
    {rel : Set (StmtIn × WitIn)}
    {R : Reduction oSpec StmtIn WitIn StmtOut WitOut pSpec}
    (d : OptionT ProbComp (FullTranscript pSpec))
    (hdist : ∀ stmtIn witIn, (stmtIn, witIn) ∈ rel →
      evalDist (honestTranscriptDist init impl R stmtIn witIn) = evalDist d) :
    perfectHVZK init impl rel R (fun _ => d) := by
  intro stmtIn witIn hMem
  exact (hdist stmtIn witIn hMem).symm

/-- **`isHVZK` from the constant-simulator criterion.** -/
theorem isHVZK_of_honestDist_eq_const
    {init : ProbComp σ} {impl : QueryImpl oSpec (StateT σ ProbComp)}
    {rel : Set (StmtIn × WitIn)}
    {R : Reduction oSpec StmtIn WitIn StmtOut WitOut pSpec}
    (d : OptionT ProbComp (FullTranscript pSpec))
    (hdist : ∀ stmtIn witIn, (stmtIn, witIn) ∈ rel →
      evalDist (honestTranscriptDist init impl R stmtIn witIn) = evalDist d) :
    isHVZK init impl rel R :=
  ⟨fun _ => d, perfectHVZK_of_honestDist_eq_const d hdist⟩

/-- **`isHVZK` transfers along an `evalDist`-equal honest distribution.** -/
theorem isHVZK.congr_honestDist
    {init : ProbComp σ} {impl : QueryImpl oSpec (StateT σ ProbComp)}
    {rel : Set (StmtIn × WitIn)}
    {R₁ R₂ : Reduction oSpec StmtIn WitIn StmtOut WitOut pSpec}
    (h : isHVZK init impl rel R₁)
    (hdist : ∀ stmtIn witIn, (stmtIn, witIn) ∈ rel →
      evalDist (honestTranscriptDist init impl R₁ stmtIn witIn) =
        evalDist (honestTranscriptDist init impl R₂ stmtIn witIn)) :
    isHVZK init impl rel R₂ :=
  let ⟨sim, hsim⟩ := h
  ⟨sim, hsim.congr_honestDist hdist⟩

/-- **`isStatHVZK` transfers along an `evalDist`-equal honest distribution.** -/
theorem isStatHVZK.congr_honestDist
    {init : ProbComp σ} {impl : QueryImpl oSpec (StateT σ ProbComp)}
    {rel : Set (StmtIn × WitIn)}
    {R₁ R₂ : Reduction oSpec StmtIn WitIn StmtOut WitOut pSpec} {ε : ℝ≥0}
    (h : isStatHVZK init impl rel R₁ ε)
    (hdist : ∀ stmtIn witIn, (stmtIn, witIn) ∈ rel →
      evalDist (honestTranscriptDist init impl R₁ stmtIn witIn) =
        evalDist (honestTranscriptDist init impl R₂ stmtIn witIn)) :
    isStatHVZK init impl rel R₂ ε :=
  let ⟨sim, hsim⟩ := h
  ⟨sim, hsim.congr_honestDist hdist⟩

#print axioms perfectHVZK.congr_honestDist
#print axioms statisticalHVZK.congr_honestDist
#print axioms perfectHVZK.simulator_congr
#print axioms statisticalHVZK.simulator_triangle
#print axioms perfectHVZK_of_honestDist_eq_const
#print axioms isHVZK_of_honestDist_eq_const
#print axioms isHVZK.congr_honestDist
#print axioms isStatHVZK.congr_honestDist

end Reduction

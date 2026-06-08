/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/

import ArkLib.OracleReduction.FiatShamir.Basic
import ArkLib.OracleReduction.Security.ZeroKnowledge

/-!
# Basic Fiat-Shamir HVZK transfer — explicit simulator and reduction to the coupling kernel (#116)

The basic Fiat-Shamir HVZK transfer residual `fiatShamir_hvzkTransferResidual`
(`isHVZK R → isHVZK R.fiatShamir`) asks for a transcript simulator for the transformed reduction.
This file supplies that simulator *explicitly* and reduces the whole residual to a single concrete
distributional identity (the "coupling" between the honest Fiat-Shamir transcript distribution and
the interactive honest transcript distribution projected onto its messages).

The transformed reduction `R.fiatShamir` runs over the one-message protocol
`FiatShamirProtocolSpec = ⟨!v[.P_to_V], !v[pSpec.Messages]⟩`, so its full transcript is exactly the
interactive messages (`msgProjFS`). The honest Fiat-Shamir prover draws each round's challenge from
the Fiat-Shamir challenge oracle, which samples uniformly — identically to the interactive verifier;
hence the FS transcript distribution is the interactive one projected to its messages. Pinning that
identity as `coupling`, the FS simulator is just `msgProjFS <$> sim` for the interactive simulator
`sim`, and perfect HVZK transfers.

This removes the *simulator-construction* step of #116 (the conceptually non-obvious part), leaving
only the distributional `coupling` lemma — the Fiat-Shamir-HVZK analogue of the already-proven
completeness run-equality (`Reduction.fiatShamir_runCollapse`).
-/

open OracleComp OracleSpec ProtocolSpec
open scoped NNReal

namespace Reduction

attribute [local instance 2000] Reduction.fiatShamirZKNoChallengeSampleable

set_option linter.unusedSectionVars false

variable {ι : Type} {oSpec : OracleSpec ι} {StmtIn WitIn StmtOut WitOut : Type}
  {n : ℕ} {pSpec : ProtocolSpec n} [∀ i, SampleableType (pSpec.Challenge i)]
  {σ τ : Type}
  [VCVCompatible StmtIn] [∀ i, VCVCompatible (pSpec.Challenge i)]

/-- Project an interactive full transcript onto the one-message Fiat-Shamir proof transcript: the
single `P_to_V` message is the bundle of interactive prover messages. -/
def msgProjFS (t : FullTranscript pSpec) :
    FullTranscript (FiatShamirProtocolSpec (pSpec := pSpec)) :=
  fun | ⟨0, _⟩ => t.messages

/-- **Basic Fiat-Shamir HVZK transfer, reduced to the coupling kernel.**

Given the coupling identity — that the honest Fiat-Shamir transcript distribution equals the
interactive honest transcript distribution projected onto its messages (`msgProjFS`) — the basic
Fiat-Shamir transform preserves perfect HVZK, with the *explicit* simulator `msgProjFS <$> sim`
obtained from the interactive simulator `sim`.

No `sorry`/extra axioms: the coupling is supplied as an explicit hypothesis, exactly mirroring the
residual-consumer discipline used throughout `FiatShamir/Basic.lean`. Discharging `coupling` for the
canonical (uniformly-sampling) Fiat-Shamir challenge implementation closes
`fiatShamir_hvzkTransferResidual` (and, via `ZKResidualBridge`, the statistical residual at
`ε = 0`). -/
theorem fiatShamir_hvzkTransfer_of_coupling
    (init : ProbComp σ) (impl : QueryImpl oSpec (StateT σ ProbComp))
    (fsInit : ProbComp τ)
    (fsImpl : QueryImpl (oSpec + fsChallengeOracle StmtIn pSpec) (StateT τ ProbComp))
    (rel : Set (StmtIn × WitIn))
    (R : Reduction oSpec StmtIn WitIn StmtOut WitOut pSpec)
    (coupling : ∀ stmt wit, (stmt, wit) ∈ rel →
      evalDist (msgProjFS <$> honestTranscriptDist init impl R stmt wit)
        = evalDist (honestTranscriptDist fsInit fsImpl R.fiatShamir stmt wit)) :
    fiatShamir_hvzkTransferResidual init impl fsInit fsImpl rel R := by
  intro hHVZK
  obtain ⟨sim, hsim⟩ := hHVZK
  refine ⟨fun stmt => msgProjFS <$> sim stmt, fun stmt wit hmem => ?_⟩
  rw [evalDist_map, hsim stmt wit hmem, ← evalDist_map]
  exact coupling stmt wit hmem

end Reduction

#print axioms Reduction.msgProjFS
#print axioms Reduction.fiatShamir_hvzkTransfer_of_coupling

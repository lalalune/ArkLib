/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/

import ArkLib.ProofSystem.Spartan.ComposedCompletenessFinal
import ArkLib.ProofSystem.Spartan.ComposedCompletenessLeaves

/-!
# Spartan composed PIOP perfect completeness with claim — final assembly (issue #114)

This file discharges the **target-carrying** composed completeness obligation
`composedCompletenessWithClaimResidual` at the composition
`(composedPIOP_Rc …).append (prependClaim …)`.

**Why this `Rc` and not `composedPIOPWithClaim_Rc`:** the residual is parameterized over the
composed reduction (any `Rc : OracleReduction … pSpecC` qualifies). The in-tree
`composedPIOPWithClaim_Rc` nests `prependClaim` at the *innermost* position
(`… (finalCheck.append prependClaim)`), while the proven base apex
`composedCompletenessResidual_proven` is about the 8-fold `composedPIOP_Rc`. Reduction
`append` is **not definitionally associative** (the protocol-spec `Fin.vappend` nests
differently), so the outer-append composition here is a *different* (equally valid) witness:
the empty-seam keystone applies directly to it, with no re-derivation of the seven inner
seams. A proof for the right-nested `composedPIOPWithClaim_Rc` variant would require
re-running the full seam chain with `finalCheck.append prependClaim` as the deepest block —
deliberately not duplicated here.
-/

open OracleComp OracleSpec ProtocolSpec

namespace Spartan.Spec.Bricks

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 4000000
set_option synthInstance.maxSize 512
set_option linter.unusedSectionVars false

variable {R : Type 0} [CommRing R] [IsDomain R] [Fintype R] [DecidableEq R] [Inhabited R]
  [SampleableType R] [VCVCompatible R] (pp : PublicParams)
  {ι : Type} (oSpec : OracleSpec ι) [oSpec.Fintype] [oSpec.Inhabited]
  {σ : Type} {init : ProbComp σ} {impl : QueryImpl oSpec (StateT σ ProbComp)}

/-- `AppendCoherent` for the composed 8-fold verifier. `composedPIOP_Rc` is a plain `def`
(non-reducible), so the chaining instance `AppendCoherent.oracleReductionAppend` cannot fire
on it directly; expose it via `inferInstanceAs` on the syntactic fold (defeq at default
transparency), where the chain fires from the declared leaf instances. -/
instance instComposedPIOPRcVerifierAppendCoherent :
    OracleVerifier.Append.AppendCoherent (composedPIOP_Rc (R := R) pp oSpec).verifier :=
  inferInstanceAs (OracleVerifier.Append.AppendCoherent
    ((oracleReduction.firstMessage R pp oSpec).append <|
      (oracleReduction.firstChallenge R pp oSpec).append <|
      (firstSumcheckReduction pp oSpec).append <|
      (oracleReduction.sendEvalClaim R pp oSpec).append <|
      (oracleReduction.linearCombination R pp oSpec).append <|
      (prependRLCTarget pp oSpec).append <|
      (secondSumcheckReduction pp oSpec).append <|
      (finalCheck R pp oSpec)).verifier)

/-- **Target-carrying composed Spartan PIOP perfect completeness, fully discharged
(issue #114)**, at the outer-append composition `(composedPIOP_Rc …).append (prependClaim …)`:
the proven 8-fold completeness apex followed by the proven 0-round claim-slot adapter, glued
by the empty-seam keystone, with the output relation relaxed to the residual's
`finalCheckWithClaimRelOut` (= `Set.univ`). Only the standard honest-implementation side
conditions remain as inputs. -/
theorem composedCompletenessWithClaimResidual_proven
    (hm : 0 < pp.ℓ_m) (hn : 0 < pp.ℓ_n)
    (hInit : NeverFail init)
    (hImplSupp : ∀ {β} (q : OracleQuery oSpec β) s,
      Prod.fst <$> support ((QueryImpl.mapQuery impl q).run s)
        = support (liftM q : OracleComp oSpec β))
    (himplSP : ∀ (t : oSpec.Domain) (s : σ) (x : oSpec.Range t × σ),
      x ∈ support ((impl t).run s) → x.2 = s)
    (himplNF : ∀ (t : oSpec.Domain) (s : σ), Pr[⊥ | (impl t).run s] = 0) :
    composedCompletenessWithClaimResidual R pp oSpec
      ((composedPIOP_Rc pp oSpec).append (prependClaim pp oSpec)) init impl := by
  have h_base := composedCompletenessResidual_proven (R := R) pp oSpec hm hn hInit hImplSupp
    himplSP himplNF
  have h_claim := prependClaim_perfectCompleteness (R := R) (pp := pp) (oSpec := oSpec)
    (init := init) (impl := impl) (finalCheckRelOut R pp)
  unfold composedCompletenessWithClaimResidual
  -- the per-index and bundled challenge-oracle instances for the empty-seam keystone
  haveI : ∀ j, Fintype ((composedPSpec (R := R) pp).Challenge j) := c0F pp
  haveI : ∀ j, Inhabited ((composedPSpec (R := R) pp).Challenge j) := c0I pp
  haveI := ProtocolSpec.challengeOracle_fintype (composedPSpec (R := R) pp)
  haveI := ProtocolSpec.challengeOracle_inhabited (composedPSpec (R := R) pp)
  haveI := ProtocolSpec.challengeOracle_fintype
    ((composedPSpec (R := R) pp) ++ₚ (!p[] : ProtocolSpec 0))
  haveI := ProtocolSpec.challengeOracle_inhabited
    ((composedPSpec (R := R) pp) ++ₚ (!p[] : ProtocolSpec 0))
  haveI := ProtocolSpec.challengeOracle_fintype (!p[] : ProtocolSpec 0)
  haveI := ProtocolSpec.challengeOracle_inhabited (!p[] : ProtocolSpec 0)
  have h := OracleReduction.append_perfectCompleteness_keystone_empty_114
    (composedPIOP_Rc pp oSpec) (prependClaim pp oSpec) h_base h_claim hInit hImplSupp
  exact Reduction.completeness_relOut_mono init impl
    (Set.subset_univ _) h

end Spartan.Spec.Bricks

-- Axiom check
#print axioms Spartan.Spec.Bricks.composedCompletenessWithClaimResidual_proven

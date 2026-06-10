/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/

import ArkLib.ProofSystem.Spartan.ComposedCompletenessFinal
import ArkLib.ProofSystem.Spartan.ComposedCompletenessLeaves

/-!
# Spartan composed PIOP perfect completeness with claim — final assembly

This file discharges the target-carrying composed completeness obligation.
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

theorem composedCompletenessWithClaimResidual_proven
    (hm : 0 < pp.ℓ_m) (hn : 0 < pp.ℓ_n)
    (hInit : NeverFail init)
    (hImplSupp : ∀ {β} (q : OracleQuery oSpec β) s,
      Prod.fst <$> support ((QueryImpl.mapQuery impl q).run s)
        = support (liftM q : OracleComp oSpec β))
    (himplSP : ∀ (t : oSpec.Domain) (s : σ) (x : oSpec.Range t × σ),
      x ∈ support ((impl t).run s) → x.2 = s)
    (himplNF : ∀ (t : oSpec.Domain) (s : σ), Pr[⊥ | (impl t).run s] = 0) :
    composedCompletenessWithClaimResidual R pp oSpec (composedPIOPWithClaim_Rc pp oSpec) init impl := by
  have h_base := composedCompletenessResidual_proven (R := R) pp oSpec hm hn hInit hImplSupp
    himplSP himplNF
  have h_claim := prependClaim_perfectCompleteness (R := R) (pp := pp) (oSpec := oSpec)
    (init := init) (impl := impl) (finalCheckRelOut R pp)
  unfold composedCompletenessWithClaimResidual
  unfold composedPIOPWithClaim_Rc
  exact OracleReduction.append_perfectCompleteness_keystone_empty_114
    (composedPIOP_Rc pp oSpec) (prependClaim pp oSpec) h_base h_claim hInit hImplSupp

end Spartan.Spec.Bricks

-- Axiom checks
#print axioms Spartan.Spec.Bricks.composedCompletenessWithClaimResidual_proven

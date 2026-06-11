/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/

import ArkLib.ProofSystem.Spartan.TightComposedFullComplete
import ArkLib.ProofSystem.Spartan.ComposedCompletenessFinal
import ArkLib.ProofSystem.Spartan.TightFirstCompleteness
import ArkLib.ProofSystem.Spartan.TightMidCompleteness
import ArkLib.ProofSystem.Spartan.TightSecondBinding
import ArkLib.ProofSystem.Spartan.FinalCheckTightComplete

/-!
# The tight composed completeness, fully discharged (issue #329, B7 capstone)

The instantiated headline: perfect completeness of `composedPIOPTightFull_Rc` — the same
reduction as the KS apex `composedTightFull_rbrKnowledgeSoundness` — from the real input
relation `spartanRelIn` (R1CS satisfiability) to the tight terminal relation `tightFinalRelOut`
(`e₂ = eval r_y ℳ` **and** the first-terminal binding identity), with **no leaf hypotheses**:
every per-phase completeness is an in-tree machine-checked theorem, threaded along the tight
honest relation chain

  `spartanRelIn → firstMessageRelOut → firstSumcheckRelInBF (= firstSumcheckWithTargetRelIn)
   → firstSumcheckWithTargetRelOutEnriched → tightSendEvalClaimRelOut
   → tightLinearCombinationRelOut → secondSumcheckWithTargetRbrRelIn ∩ binding
   → secondSumcheckWithTargetRelOutEnriched ∩ binding (= tightFinalRelOut) → tightFinalRelOut`.

Completeness and round-by-round knowledge soundness now meet at the same endpoints on the same
reduction: with the KS apex this closes the acceptance criteria of issue #329 in both
directions.

The two seam welds beyond the leaves are definitional:
* `firstSumcheckRelInBF ⊆ firstSumcheckWithTargetRelIn` — identical `setOf` bodies;
* `secondSumcheckWithTargetRelOutEnriched ∩ binding = tightFinalRelOut` — the enriched conjunct
  is the first conjunct of `tightFinalRelOut` and the pass-through binding is the second.
-/

open OracleComp OracleSpec ProtocolSpec

namespace Spartan.Spec.Bricks

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 4000000
set_option linter.unusedSectionVars false

noncomputable section

variable {R : Type 0} [CommRing R] [IsDomain R] [Fintype R] [DecidableEq R] [Inhabited R]
  [SampleableType R] [VCVCompatible R] (pp : PublicParams)
  {ι : Type} (oSpec : OracleSpec ι) [oSpec.Fintype] [oSpec.Inhabited]
  {σ : Type} {init : ProbComp σ} {impl : QueryImpl oSpec (StateT σ ProbComp)}

/-- **Seam 2→3 weld:** the bridge-free first-sum-check input relation coincides with the
target-carrying first-sum-check input relation (identical `setOf` bodies — both are plain R1CS
satisfiability of the oracle-held witness). -/
theorem firstSumcheckRelInBF_subset_withTargetRelIn :
    firstSumcheckRelInBF (R := R) pp ⊆ Spartan.Spec.firstSumcheckWithTargetRelIn (R := R) pp :=
  fun _ hx => hx

/-- **Seam 8 weld:** the binding-conjoined enriched carried-second output relation is exactly
the tight terminal relation: the enriched conjunct (`e₂ = eval r_y ℳ`) is `tightFinalRelOut`'s
first conjunct, and the carried binding is its second. -/
theorem enrichedBinding_subset_tightFinalRelOut :
    ((Spartan.Spec.secondSumcheckWithTargetRelOutEnriched (R := R) pp)
        ∩ {y | y.1 ∈ bindingAtSecondOut (R := R) pp})
      ⊆ tightFinalRelOut (R := R) pp :=
  fun _ hx => ⟨hx.1, hx.2⟩

/-- **The tight composed Spartan PIOP is perfectly complete, fully discharged (issue #329).**
From the real `spartanRelIn` to the tight terminal `tightFinalRelOut`, on the same reduction as
the KS apex, with no leaf hypotheses — only the standard honest execution-model side
conditions. -/
theorem composedTightFull_perfectCompleteness
    (hm : 0 < pp.ℓ_m) (hn : 0 < pp.ℓ_n)
    (hInit : NeverFail init)
    (hImplSupp : ∀ {β} (q : OracleQuery oSpec β) s,
      Prod.fst <$> support ((QueryImpl.mapQuery impl q).run s)
        = support (liftM q : OracleComp oSpec β))
    (himplSP : ∀ (t : oSpec.Domain) (s : σ) (x : oSpec.Range t × σ),
      x ∈ support ((impl t).run s) → x.2 = s)
    (himplNF : ∀ (t : oSpec.Domain) (s : σ), Pr[⊥ | (impl t).run s] = 0) :
    (composedPIOPTightFull_Rc (R := R) pp oSpec).perfectCompleteness init impl
      (spartanRelIn R pp) (tightFinalRelOut (R := R) pp) := by
  -- h₃ at the welded input relation.
  have h₃ : (Spartan.Spec.firstSumcheckReductionWithTarget pp oSpec).perfectCompleteness
      init impl (firstSumcheckRelInBF (R := R) pp)
      (Spartan.Spec.firstSumcheckWithTargetRelOutEnriched (R := R) pp) := by
    have h := Spartan.Spec.firstSumcheckWithTarget_perfectCompleteness_enriched
      (R := R) (pp := pp) (oSpec := oSpec) (init := init) (impl := impl) hInit hImplSupp
    unfold OracleReduction.perfectCompleteness at h ⊢
    exact Reduction.completeness_relIn_mono init impl
      (firstSumcheckRelInBF_subset_withTargetRelIn pp) h
  -- h₇ at the welded endpoints: the binding-conjoined enriched leaf, output welded into
  -- `tightFinalRelOut` by `enrichedBinding_subset_tightFinalRelOut`.
  have h₇ : (Spartan.Spec.secondSumcheckReductionWithTarget pp oSpec).perfectCompleteness
      init impl
      ((Spartan.Spec.secondSumcheckWithTargetRbrRelIn (R := R) pp oSpec)
        ∩ {x | x.1 ∈ bindingAtSecondIn (R := R) pp})
      (tightFinalRelOut (R := R) pp) := by
    have h := secondSumcheckWithTarget_perfectCompleteness_enrichedBinding
      (R := R) (pp := pp) (oSpec := oSpec) (init := init) (impl := impl) hInit hImplSupp
    unfold OracleReduction.perfectCompleteness at h ⊢
    exact Reduction.completeness_relOut_mono init impl
      (enrichedBinding_subset_tightFinalRelOut pp) h
  exact composedPIOPTightFull_perfectCompleteness_of_leaves pp oSpec hm hn
    (SendSingleWitness.oracleReduction_completeness (oSpec := oSpec)
      (Statement := Statement R pp) (OStatement := OracleStatement R pp)
      (Witness := Witness R pp) (init := init) (impl := impl)
      (oRelIn := spartanRelIn R pp) hInit)
    (firstChallenge_perfectCompleteness_consumer pp oSpec)
    h₃
    (sendEvalClaimWithTarget_perfectCompleteness_tight pp oSpec)
    (linearCombinationWithTarget_perfectCompleteness_tight pp oSpec)
    (prependRLCTargetWithTarget_perfectCompleteness_tight pp oSpec)
    h₇
    (finalCheckTight_perfectCompleteness pp oSpec)
    hInit hImplSupp himplSP himplNF

end

end Spartan.Spec.Bricks

-- Axiom audit: must report only `[propext, Classical.choice, Quot.sound]` (no `sorryAx`).
#print axioms Spartan.Spec.Bricks.composedTightFull_perfectCompleteness

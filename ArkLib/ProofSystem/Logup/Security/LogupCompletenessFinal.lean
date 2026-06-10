/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.ProofSystem.Logup.Security.LogupCompletenessWired
import ArkLib.ProofSystem.Logup.Security.SumcheckCompletenessUncond
import ArkLib.ProofSystem.Logup.Security.LogupSoundnessMsgSeam

/-!
# LogUp Protocol 2 completeness — final end-to-end assembly (issue #13)

Combines the three proven pillars into a single end-to-end completeness statement:

* `logup_completeness_wired` (`LogupCompletenessWired.lean`) — the full LogUp oracle-reduction
  completeness from `{hInit, hSumcheck, seam-direction facts, honest-impl side conditions}`, with
  the append-composition residual discharged by the proven non-perfect message-seam append
  keystone (`append_completeness_msg`).
* `sumcheckCompletenessResidual_holds_uncondInner` (`SumcheckCompletenessUncond.lean`) — the
  embedded sumcheck phase's perfect completeness, unconditional in the inner protocol (via the
  proven `CubeFiber` faithfulness), modulo only the honest-support condition `hHonest` and the
  standard data facts `hInit`/`hImplSupp`.
* the structural seam facts `logupSumcheck_length_pos` / `logup_seam_dir` /
  `logupSumcheckPSpec_first_dir` (`LogupSoundnessMsgSeam.lean`) — discharged outright from
  `0 < n`.

The result: the genuine `(logupOracleReduction).completeness init impl (inputRelation F n M)
outputRelation (logupCompletenessError F n)`, from only

* `hn : 0 < n` — non-degenerate table;
* `hHonest` — the honest-support convention (the after-outer statement carries the honest
  multiplicity/helper oracles and avoids poles, i.e. what completeness asserts about honest runs);
* `hInit : NeverFail init` and `hImplSupp` — standard data facts on the shared-oracle state; and
* `himplSP`/`himplNF`/`himplVB` — the standard honest-implementation side conditions
  (state-preserving, never-failing, value-state-blind), all vacuous for `oSpec = []ₒ`.

No `sorry`, no new axioms; the axiom audit at the bottom must print
`[propext, Classical.choice, Quot.sound]` with no `sorryAx`.
-/

open OracleComp OracleSpec ProtocolSpec

namespace Logup

noncomputable section

variable {ι : Type} (oSpec : OracleSpec ι) [oSpec.Fintype] [oSpec.Inhabited]
variable (F : Type) [Field F] [Fintype F] [DecidableEq F] [Inhabited F] [SampleableType F]
  [Fact ((-1 : F) ≠ 1)]
variable (n M : ℕ) (params : ProtocolParams M)
variable {σ : Type} (init : ProbComp σ) (impl : QueryImpl oSpec (StateT σ ProbComp))

/-- **LogUp Protocol 2 completeness, end-to-end (issue #13).** The full LogUp oracle reduction is
complete with error `logupCompletenessError F n`, from only the non-degeneracy `0 < n`, the
honest-support convention, and the standard data / honest-implementation side conditions. -/
theorem logup_completeness_final
    (hn : 0 < n)
    (hHonest :
      ∀ (stmtIn : StmtAfterOuter F n M params × (∀ i, OStmtAfterOuter F n M params i)),
        ∃ (stmtIn₀ : StmtIn F n M) (oStmtIn₀ : ∀ i, OStmtIn F n M i),
          (((stmtIn₀, oStmtIn₀), ()) ∈ inputRelation F n M) ∧
          (∀ u : Hypercube n,
            stmtIn.1.xChallenge + evalOnHypercube (tableOracle oStmtIn₀) u ≠ 0) ∧
          stmtIn.2 =
            (fun
              | .input i => oStmtIn₀ i
              | .multiplicity => honestMultiplicity oStmtIn₀
              | .helpers => honestHelpers params oStmtIn₀ stmtIn.1.xChallenge))
    (hInit : NeverFail init)
    (hImplSupp : ∀ {β} (q : OracleQuery oSpec β) s,
      Prod.fst <$> support ((QueryImpl.mapQuery impl q).run s)
        = support (liftM q : OracleComp oSpec β))
    (himplSP : ∀ (t : oSpec.Domain) (s : σ) (x : oSpec.Range t × σ),
      x ∈ support ((impl t).run s) → x.2 = s)
    (himplNF : ∀ (t : oSpec.Domain) (s : σ), Pr[⊥ | (impl t).run s] = 0)
    (himplVB : ∀ (t : oSpec.Domain) (s s' : σ),
      evalDist ((impl t).run' s) = evalDist ((impl t).run' s')) :
    (logupOracleReduction oSpec F n M params).completeness init impl
      (inputRelation F n M) outputRelation (logupCompletenessError F n) :=
  logup_completeness_wired oSpec F n M params init impl hInit
    (sumcheckCompletenessResidual_holds_uncondInner oSpec F n M params init impl
      hHonest hInit hImplSupp)
    (logupSumcheck_length_pos n hn)
    (logup_seam_dir F n M params hn)
    (logupSumcheckPSpec_first_dir F n M params hn)
    himplSP himplNF himplVB

end

end Logup

/- Axiom audit: must be [propext, Classical.choice, Quot.sound] with NO sorryAx. -/
#print axioms Logup.logup_completeness_final

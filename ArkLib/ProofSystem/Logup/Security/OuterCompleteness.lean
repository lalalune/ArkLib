import ArkLib.ProofSystem.Logup.Security.Completeness
import ArkLib.OracleReduction.Completeness
import ArkLib.ProofSystem.Logup.Security.OuterRun

open scoped NNReal ENNReal
open OracleComp ProtocolSpec

set_option maxHeartbeats 1600000
set_option linter.unusedSectionVars false

namespace Logup

/-- **Completeness from a complement-zero predicate and a failure bound (general, axiom-clean).**

If the event's complement has probability `0` (i.e. the predicate `p` holds on *every successful*
outcome of `mx`) and the failure probability `Pr[⊥ | mx]` is at most `err`, then the event
probability is at least `1 - err`.  Proof: `probEvent_compl` gives
`Pr[p] + Pr[¬p] = 1 - Pr[⊥]`; with `Pr[¬p] = 0` this is `Pr[p] = 1 - Pr[⊥] ≥ 1 - err`.

This is the *probability core* of the outer LogUp completeness obligation
(`OuterCompletenessRunResidual`): because `midRelation = Set.univ` and the honest prover/verifier
agree on every accepting transcript, the completeness predicate `prvStmtOut = stmtOut` holds on
every successful run (so its complement has probability `0`), and the run's failure event is exactly
the table-pole event bounded by `probEvent_pole_le` / `probEvent_outerVerify_reject_le`.  With this
lemma, the remaining content of `OuterCompletenessRunResidual` is exactly those two run-level
facts (`Pr[¬p] = 0` and `probFailure ≤ logupCompletenessError`), with all probability arithmetic
discharged. -/
theorem probEvent_ge_one_sub_of_compl_zero {m : Type → Type} [Monad m] [HasEvalSPMF m] {α : Type}
    (mx : m α) (p : α → Prop) (err : ℝ≥0∞)
    (hA : Pr[fun x => ¬ p x | mx] = 0) (hB : Pr[⊥ | mx] ≤ err) :
    Pr[p | mx] ≥ 1 - err := by
  have key : Pr[p | mx] = 1 - Pr[⊥ | mx] := by
    rw [← probEvent_compl mx p, hA, add_zero]
  rw [key]
  exact tsub_le_tsub_left hB 1

/-- Completeness from the two concrete run-level facts exposed by `probEvent_ge_one_sub_of_compl_zero`.

For each valid input, it is enough to show that the complement of the completeness predicate has
probability `0` on the simulated run and that the run's failure probability is bounded by the claimed
error. This is the generic adapter that lets the outer LogUp proof name those two obligations
directly instead of restating the whole `Reduction.completenessFromRun` event. -/
theorem completenessFromRun_of_compl_zero_failure_bound
    {StmtIn WitIn StmtOut WitOut : Type}
    {ιᵣ : Type} {runSpec : OracleSpec ιᵣ} {σᵣ : Type} {Trace : Type}
    (runInit : ProbComp σᵣ)
    (runImpl : QueryImpl runSpec (StateT σᵣ ProbComp))
    (relIn : Set (StmtIn × WitIn))
    (relOut : Set (StmtOut × WitOut))
    (run : (stmtIn : StmtIn) → (witIn : WitIn) →
      OptionT (OracleComp runSpec) ((Trace × StmtOut × WitOut) × StmtOut))
    (completenessError : ℝ≥0)
    (hComplZero :
      ∀ stmtIn witIn,
        (stmtIn, witIn) ∈ relIn →
          Pr[fun ⟨⟨_, (prvStmtOut, witOut)⟩, stmtOut⟩ =>
              ¬ ((stmtOut, witOut) ∈ relOut ∧ prvStmtOut = stmtOut) |
            OptionT.mk do
              (simulateQ runImpl (run stmtIn witIn).run).run' (← runInit)] = 0)
    (hFailure :
      ∀ stmtIn witIn,
        (stmtIn, witIn) ∈ relIn →
          Pr[⊥ | OptionT.mk do
              (simulateQ runImpl (run stmtIn witIn).run).run' (← runInit)]
            ≤ (completenessError : ℝ≥0∞)) :
    Reduction.completenessFromRun runInit runImpl relIn relOut run completenessError := by
  intro stmtIn witIn hRel
  exact probEvent_ge_one_sub_of_compl_zero
    (OptionT.mk do
      (simulateQ runImpl (run stmtIn witIn).run).run' (← runInit))
    (fun ⟨⟨_, (prvStmtOut, witOut)⟩, stmtOut⟩ =>
      (stmtOut, witOut) ∈ relOut ∧ prvStmtOut = stmtOut)
    (completenessError : ℝ≥0∞)
    (hComplZero stmtIn witIn hRel)
    (hFailure stmtIn witIn hRel)

section OuterCompleteness

variable {ι : Type} (oSpec : OracleSpec ι)
variable (F : Type) [Field F] [Fintype F] [DecidableEq F] [Fact ((-1 : F) ≠ 1)]
  [SampleableType F]
variable (n M : ℕ)
variable (params : ProtocolParams M)
variable {σ : Type} (init : ProbComp σ) (impl : QueryImpl oSpec (StateT σ ProbComp))

local instance : Inhabited F := ⟨0⟩

/-- Result type of the standard outer-completeness run experiment. -/
abbrev OuterCompletenessRunResult :=
  (((outerPSpec F n params).FullTranscript ×
      (StmtAfterOuter F n M params × (∀ i, OStmtAfterOuter F n M params i)) × Unit) ×
    StmtAfterOuter F n M params × (∀ i, OStmtAfterOuter F n M params i))

/-- The standard outer-completeness run experiment after simulating verifier challenges. -/
noncomputable def outerCompletenessRunComp
    (stmtIn : StmtIn F n M × (∀ i, OStmtIn F n M i))
    (witIn : WitIn F n M params) :
    OptionT ProbComp (OuterCompletenessRunResult F n M params) :=
  OptionT.mk do
    (simulateQ (QueryImpl.addLift impl challengeQueryImpl)
      (((outerOracleReduction oSpec F n M params).toReduction.run stmtIn witIn).run) :
        StateT σ ProbComp (Option (OuterCompletenessRunResult F n M params))).run' (← init)

-- OptionT-level collapse (no outer .run): applies directly inside Reduction.run's bind.
example {ι : Type} {oSpec : OracleSpec ι} {α β γ : Type} (pr : α) (sv : β) (e : γ) (P : Prop) [Decidable P] :
    (do
      let stmtOut ← (liftM (((fun a => (a, e)) <$> (if P then pure sv else (failure : OptionT (OracleComp oSpec) β))).run)
          : OptionT (OracleComp oSpec) (Option (β × γ)))
      Prod.mk pr <$> stmtOut.getM)
      = (if P then pure (pr, (sv, e)) else failure) := by
  by_cases h : P
  · rw [if_pos h, if_pos h]; rfl
  · rw [if_neg h, if_neg h]; rfl

lemma OptionT_collapse_lemma {ι : Type} {oSpec : OracleSpec ι} {α β γ : Type} (pr : α) (sv : β) (e : γ) (P : Prop) [Decidable P] :
    (do
      let stmtOut ← (liftM (((fun a => (a, e)) <$> (if P then pure sv else (failure : OptionT (OracleComp oSpec) β))).run)
          : OptionT (OracleComp oSpec) (Option (β × γ)))
      Prod.mk pr <$> stmtOut.getM)
      = (if P then pure (pr, (sv, e)) else failure) := by
  by_cases h : P
  · rw [if_pos h, if_pos h]; rfl
  · rw [if_neg h, if_neg h]; rfl

/-- Honest residual for the unfinished outer LogUp completeness run-unfolding.

The verifier-side pole bound is already proved in `OuterAcceptance.lean`, and
`OptionT_collapse_lemma` above records the local verifier-tail simplification that the previous
proof attempt used. The remaining work is the full prover-run marginal calculation: unfold
`Reduction.run (outerOracleReduction ...)`, show the `x` challenge supplied to the verifier is
uniform, and transport the `none` output probability to the pole event. This is a real
probability/formalization obligation, so this module keeps it as a named `Prop` rather than a
broken theorem body. -/
def OuterCompletenessRunResidual : Prop :=
  NeverFail init →
    (outerOracleReduction oSpec F n M params).completeness init impl
      (inputRelation F n M) (midRelation F n M params) (logupCompletenessError F n)

/-- Two explicit run-level facts that imply the outer completeness residual.

The first says every successful standard outer run satisfies the completeness predicate. The second
says the only failed runs have probability bounded by `logupCompletenessError`. This is the precise
front door for the remaining run-unfolding/marginal calculation. -/
def OuterCompletenessRunFactsResidual : Prop :=
  NeverFail init →
    (∀ stmtIn : StmtIn F n M × (∀ i, OStmtIn F n M i),
      ∀ witIn : WitIn F n M params,
        (stmtIn, witIn) ∈ inputRelation F n M →
          Pr[fun ⟨⟨_, (prvStmtOut, witOut)⟩, stmtOut⟩ =>
              ¬ ((stmtOut, witOut) ∈ midRelation F n M params ∧ prvStmtOut = stmtOut) |
            outerCompletenessRunComp oSpec F n M params init impl stmtIn witIn] = 0) ∧
    (∀ stmtIn : StmtIn F n M × (∀ i, OStmtIn F n M i),
      ∀ witIn : WitIn F n M params,
        (stmtIn, witIn) ∈ inputRelation F n M →
          Pr[⊥ | outerCompletenessRunComp oSpec F n M params init impl stmtIn witIn]
            ≤ (logupCompletenessError F n : ℝ≥0∞))

/-- The explicit complement-zero/failure-bound run facts discharge the existing outer completeness
run residual. -/
theorem outer_completeness_of_runFacts
    (h : OuterCompletenessRunFactsResidual (oSpec := oSpec) F n M params init impl)
    (hInit : NeverFail init) :
    (outerOracleReduction oSpec F n M params).completeness init impl
      (inputRelation F n M) (midRelation F n M params) (logupCompletenessError F n) := by
  obtain ⟨hComplZero, hFailure⟩ := h hInit
  unfold OracleReduction.completeness Reduction.completeness
  exact completenessFromRun_of_compl_zero_failure_bound init
    (QueryImpl.addLift impl challengeQueryImpl)
    (inputRelation F n M) (midRelation F n M params)
    ((outerOracleReduction oSpec F n M params).toReduction.run)
    (logupCompletenessError F n)
    hComplZero hFailure

/-- Consumer for the honest outer LogUp completeness run-unfolding residual. -/
theorem outer_completeness_of_runResidual
    (h : OuterCompletenessRunResidual oSpec F n M params init impl) (hInit : NeverFail init) :
    (outerOracleReduction oSpec F n M params).completeness init impl
      (inputRelation F n M) (midRelation F n M params) (logupCompletenessError F n) :=
  h hInit

/-- The residual is definitionally the outer completeness theorem under `NeverFail init`. -/
theorem outerCompletenessRunResidual_iff :
    OuterCompletenessRunResidual oSpec F n M params init impl ↔
      (NeverFail init →
        (outerOracleReduction oSpec F n M params).completeness init impl
          (inputRelation F n M) (midRelation F n M params) (logupCompletenessError F n)) :=
  Iff.rfl

end OuterCompleteness

end Logup

/- Axiom audit for the honest outer completeness frontier. -/
#print axioms Logup.OptionT_collapse_lemma
#print axioms Logup.OuterCompletenessRunResidual
#print axioms Logup.OuterCompletenessRunFactsResidual
#print axioms Logup.completenessFromRun_of_compl_zero_failure_bound
#print axioms Logup.outer_completeness_of_runFacts
#print axioms Logup.outer_completeness_of_runResidual
#print axioms Logup.outerCompletenessRunResidual_iff

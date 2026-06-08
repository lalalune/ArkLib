import ArkLib.ProofSystem.Logup.Security.Completeness
import ArkLib.OracleReduction.Completeness
import ArkLib.OracleReduction.Security.RoundByRound
import ArkLib.ProofSystem.Logup.Security.OuterRun
import ArkLib.ProofSystem.Logup.Security.OuterAcceptance
import ArkLib.OracleReduction.RunUnroll

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

/-- **Run-unfold brick for the 4-round outer prover (foundational, axiom-clean).**

The honest outer LogUp prover runs the fixed 4-round protocol (P→V multiplicity, V→P `x`, P→V
helpers, V→P batching).  This lemma peels its full `runToRound (Fin.last 4)` into the first
prover step (`processRound 0` on the seeded input state — the round-0 multiplicity message)
followed by the continuation `continueFromTo 1 → last` that folds the remaining three rounds.

It is the structural front door for the still-open prover-run marginal calculation inside
`OuterCompletenessRunFactsResidual`: with the run in this `bind` form, the round-1 `x` challenge
is exposed at the seam so its uniform marginal can be transported to the table-pole event.

Proof: the symmetric form of the generic `processRound_zero_continueFromTo_eq_runToRound_last`
(`OracleReduction/Execution.lean`), instantiated at this protocol.  Note this is the *only*
sound way to unfold the run here: a naive `rw` peel of `runToRound (Fin.last 4)` round-by-round
hits a non-type-correct motive (the `Transcript`/`PrvState` types depend on the `Fin` round
index), exactly the `Fin.succ`/`Fin.castSucc` mismatch the `continueFromTo` machinery exists to
route around. -/
theorem outerProver_runToRound_last_peel
    (stmtIn : StmtIn F n M × (∀ i, OStmtIn F n M i))
    (witIn : WitIn F n M params) :
    (outerProver oSpec F n M params).runToRound (Fin.last 4) stmtIn witIn
      = (outerProver oSpec F n M params).processRound (⟨0, by omega⟩ : Fin 4)
            (pure ((default : (outerPSpec F n params).Transcript (⟨0, by omega⟩ : Fin 5)),
                   (outerProver oSpec F n M params).input (stmtIn, witIn)))
          >>= (outerProver oSpec F n M params).continueFromTo stmtIn witIn
                (⟨0, by omega⟩ : Fin 4).succ (Fin.last 4) :=
  (Prover.processRound_zero_continueFromTo_eq_runToRound_last (by omega)
    (outerProver oSpec F n M params) stmtIn witIn).symm

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

set_option linter.unusedSimpArgs false in
/-- **Closed form of the outer honest prover's full run (`runToRound (Fin.last 4)`).**

The outer LogUp prover has four rounds (`P→V` multiplicity, `V→P` challenge `x`, `P→V` helpers,
`V→P` batch). Unfolding `runToRound` round-by-round (peeling with the message/challenge round
lemmas of `Execution.lean`, chained bottom-up with `simp only` to tolerate the dependent `Fin`
motive) reduces the entire run to a `do`-block containing **exactly two** `getChallenge` samples —
the `x` challenge at round 1 and the `batch` challenge at round 3 — with every prover step pure.
The final prover state is the record `(oStmt, x, batch)` carried into `outerProver.output`.

This is the load-bearing prover-side structural fact for outer-phase completeness: composed with
the verifier's pole-scan collapse (`OuterRun.lean`), it exposes that the only randomness in the
outer phase is the two uniform challenge samples. -/
theorem outerProver_runToRound_closed_form
    (stmtIn : StmtIn F n M × (∀ i, OStmtIn F n M i))
    (witIn : WitIn F n M params) :
    (outerProver oSpec F n M params).runToRound (Fin.last 4) stmtIn witIn = (do
      let m₀ ← (outerProver oSpec F n M params).sendMessage ⟨0, rfl⟩
                  ((outerProver oSpec F n M params).input (stmtIn, witIn))
      let x ← (outerPSpec F n params).getChallenge ⟨1, rfl⟩
      let r₁ ← (outerProver oSpec F n M params).receiveChallenge ⟨1, rfl⟩ m₀.2
      let m₂ ← (outerProver oSpec F n M params).sendMessage ⟨2, rfl⟩ (r₁ x)
      let batch ← (outerPSpec F n params).getChallenge ⟨3, rfl⟩
      let r₃ ← (outerProver oSpec F n M params).receiveChallenge ⟨3, rfl⟩ m₂.2
      return ⟨((default : (outerPSpec F n params).Transcript 0).concat m₀.1).concat x
                |>.concat m₂.1 |>.concat batch, r₃ batch⟩) := by
  -- Direction facts (all `rfl` on this fixed protocol spec).
  have d0 : (outerPSpec F n params).dir (0 : Fin 4) = Direction.P_to_V := rfl
  have d1 : (outerPSpec F n params).dir (1 : Fin 4) = Direction.V_to_P := rfl
  have d2 : (outerPSpec F n params).dir (2 : Fin 4) = Direction.P_to_V := rfl
  have d3 : (outerPSpec F n params).dir (3 : Fin 4) = Direction.V_to_P := rfl
  -- Round 0 (message): runToRound 1 from the prover-first base.
  have h0 := Prover.runToRound_succ_message (n := 4) (0 : Fin 4) stmtIn witIn
    (outerProver oSpec F n M params) d0
  simp only [Fin.castSucc_mk, Fin.succ_mk, Nat.reduceAdd,
    Prover.runToRound_zero_of_prover_first, bind_assoc, pure_bind] at h0
  -- Round 1 (challenge x).
  have h1 := Prover.runToRound_succ_challenge (n := 4) (1 : Fin 4) stmtIn witIn
    (outerProver oSpec F n M params) d1
  simp only [Fin.castSucc_mk, Fin.succ_mk, Nat.reduceAdd, h0, bind_assoc] at h1
  -- Round 2 (message helpers).
  have h2 := Prover.runToRound_succ_message (n := 4) (2 : Fin 4) stmtIn witIn
    (outerProver oSpec F n M params) d2
  simp only [Fin.castSucc_mk, Fin.succ_mk, Nat.reduceAdd, h1, bind_assoc] at h2
  -- Round 3 (challenge batch).
  have h3 := Prover.runToRound_succ_challenge (n := 4) (3 : Fin 4) stmtIn witIn
    (outerProver oSpec F n M params) d3
  simp only [Fin.castSucc_mk, Fin.succ_mk, Nat.reduceAdd, h2, bind_assoc] at h3
  -- `Fin.last 4 = (3 : Fin 4).succ`, so `h3` is the run to `Fin.last 4`.
  exact h3

/-- **Closed form of the outer honest prover's *full* run (`Prover.run`).**

`Prover.run` is `runToRound (Fin.last 4)` followed by `output` (`run_eq_runToRound_last`). Plugging in
the banked `outerProver_runToRound_closed_form` exposes the entire prover run as a `do`-block with
**exactly two** `getChallenge` samples (the `x` challenge at round 1 and the `batch` challenge at
round 3), every other prover step pure, ending in the prover's `output` step applied to the final
state `r₃ batch`. This is the prover-side half of the simulated outer-reduction run. -/
theorem outerProver_run_closed_form
    (stmtIn : StmtIn F n M × (∀ i, OStmtIn F n M i))
    (witIn : WitIn F n M params) :
    (outerProver oSpec F n M params).run stmtIn witIn = (do
      let m₀ ← (outerProver oSpec F n M params).sendMessage ⟨0, rfl⟩
                  ((outerProver oSpec F n M params).input (stmtIn, witIn))
      let x ← (outerPSpec F n params).getChallenge ⟨1, rfl⟩
      let r₁ ← (outerProver oSpec F n M params).receiveChallenge ⟨1, rfl⟩ m₀.2
      let m₂ ← (outerProver oSpec F n M params).sendMessage ⟨2, rfl⟩ (r₁ x)
      let batch ← (outerPSpec F n params).getChallenge ⟨3, rfl⟩
      let r₃ ← (outerProver oSpec F n M params).receiveChallenge ⟨3, rfl⟩ m₂.2
      let out ← (outerProver oSpec F n M params).output (r₃ batch)
      return ⟨((default : (outerPSpec F n params).Transcript 0).concat m₀.1).concat x
                |>.concat m₂.1 |>.concat batch, out⟩) := by
  rw [Prover.run_eq_runToRound_last, outerProver_runToRound_closed_form]
  simp only [bind_assoc, pure_bind]

/-- **Closed form of the full outer oracle-reduction run (`toReduction.run`).**

`Reduction.run` first runs the prover, then lifts the verifier over the produced transcript. The outer
oracle reduction's prover/verifier are *definitionally* `outerProver`/`outerVerifier`, so its
`toReduction.run` is the explicit `Reduction.run` do-block over those two: run the prover, lift the
verifier over the produced transcript, and project the verdict. Composed with the banked
`outerProver_run_closed_form`, the prover head reduces to the two-challenge closed form (the `x`
sample at round 1, the `batch` sample at round 3, every other prover step pure), so the only
randomness in the run is the two uniform challenge samples — exactly what the simulated experiment
(`outerCompletenessRunComp`) resolves through `challengeQueryImpl`. -/
theorem outerReduction_run_closed_form
    (stmtIn : StmtIn F n M × (∀ i, OStmtIn F n M i))
    (witIn : WitIn F n M params) :
    (outerOracleReduction oSpec F n M params).toReduction.run stmtIn witIn = (do
      let proverResult ← liftM ((outerProver oSpec F n M params).run stmtIn witIn)
      let stmtOut ← liftM
        ((outerVerifier oSpec F n M params).toVerifier.run stmtIn proverResult.1).run
      return ⟨proverResult, ← stmtOut.getM⟩) := by
  rfl


/-- **Challenge-sample collapse for the simulated outer run (foundational, axiom-clean).**

Simulating an outer-phase challenge query (`getChallenge i`) through the lifted challenge oracle
implementation (`challengeQueryImpl`, the right summand of `addLift impl challengeQueryImpl`) resolves
to a single uniform sample `$ᵗ (Challenge i)`. This is the load-bearing brick that turns each of the
honest outer prover's two `getChallenge` calls (the round-1 `x` and round-3 `batch`) — exposed by
`outerProver_run_closed_form` — into a plain uniform draw once the run is pushed through
`simulateQ (addLift impl challengeQueryImpl)`, leaving the two challenge samples as the *only*
randomness of the simulated outer experiment. It is the challenge-side counterpart of the
verifier-side `simulateQ_outerVerify_eq` collapse, and feeds the round-1 marginal calculation that
transports `x` to the table-pole event bounded by `probEvent_outerVerify_reject_le`. -/
theorem getChallenge_simulateQ_eq (i : (outerPSpec F n params).ChallengeIdx) :
    simulateQ (QueryImpl.liftTarget (StateT σ ProbComp)
        (challengeQueryImpl (pSpec := outerPSpec F n params)))
      ((outerPSpec F n params).getChallenge i)
      = (liftM ($ᵗ ((outerPSpec F n params).Challenge i)) :
          StateT σ ProbComp ((outerPSpec F n params).Challenge i)) := by
  unfold ProtocolSpec.getChallenge
  erw [simulateQ_spec_query]
  rfl

/-- **Transcript challenge readback for the closed-form outer run (foundational, axiom-clean).**

The closed-form prover transcript is the 4-fold `Transcript.concat` (`Fin.snoc`) chain
`((((default).concat m₀).concat x).concat m₂).concat batch`.  The outer verifier reads its two
challenges off this transcript via `chalX`/`chalBatch` (`= transcript ⟨1,rfl⟩` / `transcript ⟨3,rfl⟩`),
while the honest prover's output record uses the received challenges `x`/`batch` directly.  This
lemma settles that they coincide: each `getChallenge` sample is read back unchanged at its own
round index.  Pure finite `Fin.snoc` computation (the last `snoc` for `batch` at index `3 = last`,
and `x` at `1 = castSucc²` peeled through the inner `snoc`s). -/
theorem outerProver_transcript_challenge_readback
    (m₀ : (outerPSpec F n params).Message ⟨0, rfl⟩)
    (x : (outerPSpec F n params).Challenge ⟨1, rfl⟩)
    (m₂ : (outerPSpec F n params).Message ⟨2, rfl⟩)
    (batch : (outerPSpec F n params).Challenge ⟨3, rfl⟩) :
    chalX F n M params
        (((((default : (outerPSpec F n params).Transcript 0).concat m₀).concat x).concat m₂).concat
            batch).challenges = x ∧
    chalBatch F n M params
        (((((default : (outerPSpec F n params).Transcript 0).concat m₀).concat x).concat m₂).concat
            batch).challenges = batch := by
  constructor
  · simp only [chalX, FullTranscript.challenges, Transcript.concat, Fin.isValue]
    rfl
  · simp only [chalBatch, FullTranscript.challenges, Transcript.concat, Fin.isValue]
    rfl

/-- **Transcript message readback for the closed-form outer run (foundational, axiom-clean).**

Sibling of `outerProver_transcript_challenge_readback` on the message side. The closed-form prover
transcript is the 4-fold `Transcript.concat` (`Fin.snoc`) chain
`((((default).concat m₀).concat x).concat m₂).concat batch`. The outer verifier reads the two prover
messages off this transcript to build its output oracle statement via `embed`
(`.multiplicity → messages ⟨0⟩`, `.helpers → messages ⟨2⟩`), while the honest prover's output oracle
statement uses the sent messages `m₀`/`m₂` directly. This lemma settles that they coincide: each sent
message is read back unchanged at its own round index — the message-side structural fact for the
prover/verifier output-statement agreement (`prvStmtOut = stmtOut`) inside
`OuterCompletenessRunFactsResidual`. Pure finite `Fin.snoc` computation (`m₂` at index `2`, and `m₀`
at index `0` peeled through the inner `snoc`s). -/
theorem outerProver_transcript_message_readback
    (m₀ : (outerPSpec F n params).Message ⟨0, rfl⟩)
    (x : (outerPSpec F n params).Challenge ⟨1, rfl⟩)
    (m₂ : (outerPSpec F n params).Message ⟨2, rfl⟩)
    (batch : (outerPSpec F n params).Challenge ⟨3, rfl⟩) :
    (((((default : (outerPSpec F n params).Transcript 0).concat m₀).concat x).concat m₂).concat
            batch).messages (⟨0, rfl⟩ : (outerPSpec F n params).MessageIdx) = m₀ ∧
    (((((default : (outerPSpec F n params).Transcript 0).concat m₀).concat x).concat m₂).concat
            batch).messages (⟨2, rfl⟩ : (outerPSpec F n params).MessageIdx) = m₂ := by
  constructor
  · simp only [FullTranscript.messages, Transcript.concat, Fin.isValue]
    rfl
  · simp only [FullTranscript.messages, Transcript.concat, Fin.isValue]
    rfl

/-- **Outer verifier output oracle-statement agreement (foundational, axiom-clean).**

The outer verifier recomputes its output oracle statements off the transcript via `embed`
(`.input i → .inl i` passthrough, `.multiplicity → .inr ⟨0⟩`, `.helpers → .inr ⟨2⟩`) through the
dependent `hEq`/`embed` transport of `OracleVerifier.run`.  Given the transcript carries the honest
prover's round-0/round-2 messages (`honestMultiplicity oStmt` / `honestHelpers params oStmt x` — as
exposed by `outerProver_transcript_message_readback` on the closed-form run), the verifier's output
oracle-statement function coincides *exactly* with the honest prover's output oracle-statement
function (`outerProver.output`).  This is the oracle-statement half of the prover/verifier
output-statement agreement (`prvStmtOut = stmtOut`), the complement-zero content of
`OuterCompletenessRunFactsResidual`; the statement-record half is `outerProver_transcript_challenge_readback`.

The outerVerifier's `embed`/`hEq` are concrete `rfl` on each `OuterOracleIdx` constructor, so the
`hEq i ▸ h ▸` transports compute away under `cases i`. -/
theorem outerVerifier_oStmtOut_eq
    (oStmt : ∀ i, OStmtIn F n M i)
    (transcript : (outerPSpec F n params).FullTranscript)
    (x : F)
    (hm : transcript.messages (⟨0, rfl⟩ : (outerPSpec F n params).MessageIdx)
            = honestMultiplicity oStmt)
    (hh : transcript.messages (⟨2, rfl⟩ : (outerPSpec F n params).MessageIdx)
            = honestHelpers params oStmt x) :
    (fun i => match h : (outerVerifier oSpec F n M params).embed i with
        | .inl j => ((outerVerifier oSpec F n M params).hEq i ▸ h ▸ oStmt j :
            OStmtAfterOuter F n M params i)
        | .inr j => ((outerVerifier oSpec F n M params).hEq i ▸ h ▸ transcript.messages j :
            OStmtAfterOuter F n M params i))
      = (fun
          | .input i => oStmt i
          | .multiplicity => honestMultiplicity oStmt
          | .helpers => honestHelpers params oStmt x) := by
  funext i
  cases i with
  | input j => rfl
  | multiplicity => simpa using hm
  | helpers => simpa using hh

/-- **Honest outer prover/verifier output-pair agreement (foundational, axiom-clean).**

The single `prvStmtOut = stmtOut` value-fact, gluing the two banked agreement halves: given the
closed-form transcript carries the honest challenges (`x`/`batch`, via
`outerProver_transcript_challenge_readback`) and the honest messages
(`honestMultiplicity`/`honestHelpers`, via `outerProver_transcript_message_readback`), the honest
prover's output statement pair (`outerProver.output` on the final state `(oStmt, x, batch)`) equals
the pair the verifier recomputes from the same transcript — the statement record read off the
challenges (`chalX`/`chalBatch`) and the oracle statements read via `embed`. This is exactly the
pointwise per-state agreement consumed by
`probEvent_outerCompletenessRunComp_compl_eq_zero_of_perState` (the complement-zero / Fact 1
obligation of `OuterCompletenessRunFactsResidual`). -/
theorem outerProver_output_pair_eq_verifier_recompute
    (oStmt : ∀ i, OStmtIn F n M i)
    (x : F)
    (batch : BatchingChallenge F n params.numGroups)
    (transcript : (outerPSpec F n params).FullTranscript)
    (hx : chalX F n M params transcript.challenges = x)
    (hb : chalBatch F n M params transcript.challenges = batch)
    (hm : transcript.messages (⟨0, rfl⟩ : (outerPSpec F n params).MessageIdx)
            = honestMultiplicity oStmt)
    (hh : transcript.messages (⟨2, rfl⟩ : (outerPSpec F n params).MessageIdx)
            = honestHelpers params oStmt x) :
    (show StmtAfterOuter F n M params × (∀ i, OStmtAfterOuter F n M params i) from
      ({ xChallenge := x, zChallenge := batch.1, batchingScalars := batch.2 },
       fun
        | .input i => oStmt i
        | .multiplicity => honestMultiplicity oStmt
        | .helpers => honestHelpers params oStmt x))
      = ({ xChallenge := chalX F n M params transcript.challenges,
           zChallenge := (chalBatch F n M params transcript.challenges).1,
           batchingScalars := (chalBatch F n M params transcript.challenges).2 },
         fun i => match h : (outerVerifier oSpec F n M params).embed i with
           | .inl j => ((outerVerifier oSpec F n M params).hEq i ▸ h ▸ oStmt j :
               OStmtAfterOuter F n M params i)
           | .inr j => ((outerVerifier oSpec F n M params).hEq i ▸ h ▸ transcript.messages j :
               OStmtAfterOuter F n M params i)) := by
  rw [hx, hb]
  refine Prod.ext rfl ?_
  exact (outerVerifier_oStmtOut_eq oSpec F n M params oStmt transcript x hm hh).symm

set_option maxHeartbeats 3200000 in
/-- **Outer-completeness failure bound reduced to the per-(initial-state) pole event (axiom-clean).**

The standard outer-run failure probability is bounded by `logupCompletenessError` *given* the
per-initial-state fact that the simulated reduction run returns `none` (its only failure mode, the
verifier rejecting the sampled `x`-challenge) with probability at most that error.

This discharges all of the run-level probability plumbing — the `OptionT.mk` failure split
(`OptionT.probFailure_mk`: bare `⊥` is `0` in `ProbComp`, so failure surfaces only as `none`) and the
average over the never-failing `init` state (`probEvent_bind_le_of_forall_le`) — leaving exactly the
per-state pole obligation.  That remaining obligation is the simulated-verifier-run collapse to
`¬ outerVerifyAccepts` marginalised over the uniform `x`, bounded by `probEvent_outerVerify_reject_le`. -/
theorem probFailure_outerCompletenessRunComp_le_of_perStateNone
    (stmtIn : StmtIn F n M × (∀ i, OStmtIn F n M i))
    (witIn : WitIn F n M params)
    (hPole : ∀ s : σ,
      Pr[= none | ((simulateQ (QueryImpl.addLift impl challengeQueryImpl)
          (((outerOracleReduction oSpec F n M params).toReduction.run stmtIn witIn).run) :
            StateT σ ProbComp (Option (OuterCompletenessRunResult F n M params))).run' s)]
        ≤ (logupCompletenessError F n : ℝ≥0∞)) :
    Pr[⊥ | outerCompletenessRunComp oSpec F n M params init impl stmtIn witIn]
      ≤ (logupCompletenessError F n : ℝ≥0∞) := by
  unfold outerCompletenessRunComp
  rw [OptionT.probFailure_mk]
  refine le_trans (b := 0 + (logupCompletenessError F n : ℝ≥0∞)) ?_ (by rw [zero_add])
  gcongr ?_ + ?_
  · simp [HasEvalPMF.probFailure_eq_zero]
  · rw [← probEvent_eq_eq_probOutput]
    refine probEvent_bind_le_of_forall_le (fun s _ => ?_)
    rw [probEvent_eq_eq_probOutput]
    exact hPole s

set_option maxHeartbeats 3200000 in
/-- **Outer-completeness complement-zero reduced to the per-(initial-state) agreement (axiom-clean).**

The completeness predicate (`midRelation = Set.univ`, so `(stmtOut, witOut) ∈ midRelation ∧
prvStmtOut = stmtOut` collapses to `prvStmtOut = stmtOut`) has complement probability `0` on the
standard outer run, *given* the per-initial-state fact that its complement is `0` on the simulated
reduction run.

This discharges the run-level plumbing sorry-free: the `OptionT.mk` event collapse
(`probEvent_optionT_mk_eq_elim`) and the split over the `init` state (`probEvent_bind_eq_tsum` +
`ENNReal.tsum_eq_zero`).  The remaining per-state obligation is that on every successful simulated run
the honest prover's output statement equals the verifier's recomputed one — exactly the
`outerProver_transcript_challenge_readback` / `..._message_readback` agreement. -/
theorem probEvent_outerCompletenessRunComp_compl_eq_zero_of_perState
    (stmtIn : StmtIn F n M × (∀ i, OStmtIn F n M i))
    (witIn : WitIn F n M params)
    (hAgree : ∀ s : σ,
      Pr[fun ⟨⟨_, (prvStmtOut, witOut)⟩, stmtOut⟩ =>
          ¬ ((stmtOut, witOut) ∈ midRelation F n M params ∧ prvStmtOut = stmtOut) |
        (OptionT.mk ((simulateQ (QueryImpl.addLift impl challengeQueryImpl)
            (((outerOracleReduction oSpec F n M params).toReduction.run stmtIn witIn).run) :
              StateT σ ProbComp (Option (OuterCompletenessRunResult F n M params))).run' s)
          : OptionT ProbComp (OuterCompletenessRunResult F n M params))] = 0) :
    Pr[fun ⟨⟨_, (prvStmtOut, witOut)⟩, stmtOut⟩ =>
        ¬ ((stmtOut, witOut) ∈ midRelation F n M params ∧ prvStmtOut = stmtOut) |
      outerCompletenessRunComp oSpec F n M params init impl stmtIn witIn] = 0 := by
  unfold outerCompletenessRunComp
  rw [Verifier.StateFunction.probEvent_optionT_mk_eq_elim, probEvent_bind_eq_tsum]
  refine ENNReal.tsum_eq_zero.mpr (fun s => ?_)
  rw [← Verifier.StateFunction.probEvent_optionT_mk_eq_elim, hAgree s, mul_zero]

/-- **`OptionT`-over-`OracleComp` run-of-lift law.** Running the `OptionT`-lift of a never-failing
`OracleComp` maps every output to `some`. (`OptionT.lift a = OptionT.mk (some <$> a)`.) -/
theorem optionT_run_lift {ι' : Type} {spec : OracleSpec ι'} {α : Type}
    (a : OracleComp spec α) :
    (liftM a : OptionT (OracleComp spec) α).run = Option.some <$> a := rfl

/-- **`OptionT`-over-`OracleComp` run-of-bind law.** The base computation of an `OptionT` bind runs
the first stage, then on `some` runs the second stage (threaded) and on `none` short-circuits. -/
theorem optionT_run_bind {ι' : Type} {spec : OracleSpec ι'} {α β : Type}
    (x : OptionT (OracleComp spec) α) (f : α → OptionT (OracleComp spec) β) :
    (x >>= f).run = x.run >>= fun o =>
      match o with | some a => (f a).run | none => pure none := rfl

/-- **`OptionT` lift-bind-run collapse.** Since the lifted stage never fails, binding it then running
collapses to running the base then the (run of the) continuation — the structural primitive for
peeling a never-failing head off an `OptionT (OracleComp _)` run. -/
theorem optionT_lift_bind_run {ι' : Type} {spec : OracleSpec ι'} {α β : Type}
    (a : OracleComp spec α) (b : α → OptionT (OracleComp spec) β) :
    ((liftM a >>= b : OptionT (OracleComp spec) β)).run = a >>= fun x => (b x).run := by
  rw [optionT_run_bind, optionT_run_lift, ← bind_pure_comp, bind_assoc]
  simp only [pure_bind]

/-- **Outer verifier rejection bound over the protocol's own challenge measure.**

`probEvent_outerVerify_reject_le` bounds the rejection probability when `x` is drawn from
`uniformSample F`.  The marginal produced by `ChallengeCoherence.probEvent_run'_…_getChallenge_bind`
instead measures against `$ᵗ ((outerPSpec …).Challenge ⟨1, rfl⟩)` — uniform sampling over the
protocol's *own* challenge type at round `⟨1⟩`.  Those two measures coincide: `Challenge ⟨1, rfl⟩` is
definitionally `F`, and `probEvent_uniformSample` evaluates either measure to the same
`Fintype.card`-based ratio, which is independent of the (non-defeq) `SampleableType` instance carried
along.  This is the bridge that lets the per-state pole obligation cite the verifier-side bound. -/
theorem probEvent_outerVerify_reject_challenge_le (oStmt : ∀ i, OStmtIn F n M i)
    [SampleableType ((outerPSpec F n params).Challenge ⟨1, rfl⟩)] :
    Pr[(fun c => ¬ outerVerifyAccepts F n M oStmt c) |
        ($ᵗ ((outerPSpec F n params).Challenge ⟨1, rfl⟩))]
      ≤ (logupCompletenessError F n : ℝ≥0∞) := by
  classical
  haveI hfin : Fintype ((outerPSpec F n params).Challenge ⟨1, rfl⟩) :=
    (inferInstance : Fintype F)
  have hTy : (outerPSpec F n params).Challenge ⟨1, rfl⟩ = F := rfl
  refine le_trans (le_of_eq ?_) (probEvent_outerVerify_reject_le (oStmt := oStmt))
  rw [probEvent_uniformSample, probEvent_uniformSample]
  convert rfl using 2
  · rw [← Fintype.card_subtype, ← Fintype.card_subtype]
    exact congrArg Nat.cast
      (Fintype.card_congr (Equiv.subtypeEquiv (Equiv.cast hTy.symm) (fun _ => Iff.rfl)))
  · exact congrArg Nat.cast (Fintype.card_congr (Equiv.cast hTy.symm))

/-- **Embedded-verifier accept collapse.** On a transcript whose `x`-challenge is accepted
(`outerVerifyAccepts`), the outer reduction's embedded (plain) verifier run is a pure successful
output: its `OptionT.run` is `pure (some …)`, so it never fails (`none`). This is the verifier-side
half of the per-state accept-zero step in `outer_perState_none_le` — a direct repackaging of the
pole-scan collapse `simulateQ_outerVerify_eq` under the named acceptance predicate. -/
theorem outerVerifier_run_accept_eq_pure
    (stmtIn : StmtIn F n M × (∀ i, OStmtIn F n M i))
    (tr : FullTranscript (outerPSpec F n params))
    (hacc : outerVerifyAccepts F n M stmtIn.2 (chalX F n M params tr.challenges)) :
    ∃ v, (Verifier.run stmtIn tr (outerVerifier oSpec F n M params).toVerifier).run
      = (pure (some v) : OracleComp oSpec
          (Option (StmtAfterOuter F n M params
            × (∀ i, OStmtAfterOuter F n M params i)))) := by
  classical
  refine ⟨(show StmtAfterOuter F n M params × (∀ i, OStmtAfterOuter F n M params i) from
          ({ xChallenge := chalX F n M params tr.challenges,
             zChallenge := (chalBatch F n M params tr.challenges).1,
             batchingScalars := (chalBatch F n M params tr.challenges).2 },
           fun i => match h : (outerVerifier oSpec F n M params).embed i with
             | Sum.inl j => ((outerVerifier oSpec F n M params).hEq i ▸ h ▸ stmtIn.2 j :
                 OStmtAfterOuter F n M params i)
             | Sum.inr j => ((outerVerifier oSpec F n M params).hEq i ▸ h ▸ tr.messages j :
                 OStmtAfterOuter F n M params i))), ?_⟩
  show ((outerVerifier oSpec F n M params).toVerifier.verify stmtIn tr).run = _
  unfold OracleVerifier.toVerifier
  simp only
  rw [simulateQ_outerVerify_eq]
  rw [if_pos (show (∀ (u : Hypercube n),
      chalX F n M params tr.challenges + evalOnHypercube (tableOracle stmtIn.2) u ≠ 0) from hacc)]
  rw [pure_bind, OptionT.run_pure]
  refine congrArg (fun z => pure (some z)) ?_
  refine Prod.ext rfl ?_
  funext i
  cases i <;> rfl

set_option maxHeartbeats 3200000 in
/-- **Per-(initial-state) pole bound for the simulated outer run (DEV — accept-zero pending).**

Discharges the `hPole` obligation of `probFailure_outerCompletenessRunComp_le_of_perStateNone`: the
simulated reduction run returns `none` with probability at most `logupCompletenessError`.  Peels the
never-failing prover head (`optionT_lift_bind_run` + `outerProver_run_closed_form`), marginalises the
round-1 `x`-challenge (`probEvent_run'_simulateQ_addLift_getChallenge_bind`), and bounds the resulting
weighted sum by the verifier rejection event via `probEvent_outerVerify_reject_challenge_le`.  The
per-`c` split: on accept the run never fails (accept-zero, pending); on reject the failure probability
is trivially `≤ 1`. -/
theorem outer_perState_none_le
    (stmtIn : StmtIn F n M × (∀ i, OStmtIn F n M i))
    (witIn : WitIn F n M params)
    (s : σ) :
    Pr[= none | ((simulateQ (QueryImpl.addLift impl challengeQueryImpl)
        (((outerOracleReduction oSpec F n M params).toReduction.run stmtIn witIn).run) :
          StateT σ ProbComp (Option (OuterCompletenessRunResult F n M params))).run' s)]
      ≤ (logupCompletenessError F n : ℝ≥0∞) := by
  classical
  haveI : Inhabited F := ⟨0⟩
  haveI : SampleableType ((outerPSpec F n params).Challenge ⟨1, rfl⟩) :=
    instOuterPSpecChallengeSampleable ⟨1, rfl⟩
  rw [outerReduction_run_closed_form, optionT_lift_bind_run, outerProver_run_closed_form]
  simp only [outerProver, bind_pure_comp, pure_bind, map_pure, bind_assoc, liftM_pure]
  rw [← probEvent_eq_eq_probOutput,
    ChallengeCoherence.probEvent_run'_simulateQ_addLift_getChallenge_bind]
  refine le_trans ?_
    (probEvent_outerVerify_reject_challenge_le (params := params) (oStmt := stmtIn.2))
  rw [probEvent_eq_tsum_ite]
  refine ENNReal.tsum_le_tsum (fun c => ?_)
  by_cases hacc : outerVerifyAccepts F n M stmtIn.2 c
  · -- On an accepting challenge `c`, the simulated verifier run returns `some` (never fails): the
    -- batch `⟨3⟩` challenge marginalises out and `simulateQ_outerVerify_eq` collapses the verifier to
    -- `pure …`.  Pending: the verifier-collapse-under-`simulateQ`/`OptionT`/`StateT` layering.
    rw [if_neg (not_not.mpr hacc)]
    refine nonpos_iff_eq_zero.mpr ?_
    rw [mul_eq_zero]
    right
    rw [probEvent_eq_zero_iff]
    intro y hy hynone
    subst hynone
    -- `none` survives the simulated run only if it is already in the (un-simulated) run's support.
    have hsub := _root_.support_simulateQ_run'_subset (impl.addLift challengeQueryImpl) _ s hy
    rw [support_bind] at hsub
    simp only [Set.mem_iUnion, exists_prop] at hsub
    obtain ⟨x, hx, hxnone⟩ := hsub
    rw [support_map] at hx
    obtain ⟨a, _, rfl⟩ := hx
    -- The transcript built here carries `c` as its round-1 challenge (`readback`), so the embedded
    -- verifier accepts and its run is a pure `some` — leaving no `none` in the support.
    obtain ⟨v, hv⟩ := outerVerifier_run_accept_eq_pure oSpec F n M params stmtIn _
      ((outerProver_transcript_challenge_readback
          (m₀ := honestMultiplicity stmtIn.2) (x := c)
          (m₂ := honestHelpers params stmtIn.2 c) (batch := a)).1.symm ▸ hacc)
    rw [optionT_run_bind, hv] at hxnone
    simp only [liftM_pure, OptionT.run_pure, pure_bind, Option.getM] at hxnone
    rw [← bind_pure_comp, optionT_run_bind, OptionT.run_pure, pure_bind] at hxnone
    simp only [OptionT.run_pure, support_pure, Set.mem_singleton_iff, reduceCtorEq] at hxnone
  · rw [if_pos hacc]
    refine le_trans (mul_le_mul' (le_refl _) (d := 1) ?_) ?_
    · exact probEvent_le_one
    · rw [mul_one]
      exact le_of_eq rfl

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
#print axioms Logup.outerProver_runToRound_closed_form
#print axioms Logup.outerProver_run_closed_form
#print axioms Logup.outerReduction_run_closed_form
#print axioms Logup.getChallenge_simulateQ_eq
#print axioms Logup.probEvent_outerVerify_reject_challenge_le

import ArkLib.OracleReduction.Basic
import ArkLib.Data.Fin.Basic
import ArkLib.ToVCVio.OracleComp.EvalDist

/-!
  # Execution Semantics of Interactive Oracle Reductions

  We define what it means to execute an interactive oracle reduction, and prove some basic
  properties.
-/

open OracleComp OracleSpec SubSpec ProtocolSpec

universe u v

-- namespace loggingOracle

-- variable {ι : Type u} {spec : OracleSpec ι} {α β : Type u}

-- @[simp]
-- theorem impl_run {i : ι} {t : spec.domain i} :
--     (loggingOracle.impl (query i t)).run = (do let u ← query i t; return (u, [⟨i, ⟨t, u⟩⟩])) :=
--   rfl

-- @[simp]
-- theorem simulateQ_map_fst (oa : OracleComp spec α) :
--     Prod.fst <$> (simulateQ loggingOracle oa).run = oa := by
--   induction oa using OracleComp.induction with
--   | pure a => simp
--   | query_bind i t oa ih => simp [simulateQ_bind, ih]
--   | failure => simp

-- @[simp]
-- theorem simulateQ_bind_fst (oa : OracleComp spec α) (f : α → OracleComp spec β) :
--     (do let a ← (simulateQ loggingOracle oa).run; f a.1) = oa >>= f := by
--   induction oa using OracleComp.induction with
--   | pure a => simp
--   | query_bind i t oa ih => simp [simulateQ_bind, ih]
--   | failure => simp

-- /-- We often have to specify `oa` and `f` for this to be applied -/
-- theorem simulateQ_bind_fst_comp (oa : OracleComp spec α) (f : α → OracleComp spec β) :
--     (do let a ← (simulateQ loggingOracle oa).run; f a.1) = (do let a ← oa; f a) := by
--   induction oa using OracleComp.induction with
--   | pure a => simp
--   | query_bind i t oa ih => simp [simulateQ_bind, ih]
--   | failure => simp

-- /-- Ideally, this theorem can also compare the logs of the two oracle computations.

-- For this to work, we need an extra function mapping `superSpec.QueryLog` to `spec.QueryLog`.

-- This function always exists if `superSpec` is `spec + something`, and extensions thereof, but may
-- not be guaranteed to exist in general, if we just have the current fields in the type class. -/
-- @[simp]
-- theorem simulateQ_run_liftComp_fst {ι' : Type u} {superSpec : OracleSpec ι'}
--     (oa : OracleComp spec α) [SubSpec spec superSpec] :
--       Prod.fst <$> (simulateQ loggingOracle oa).run.liftComp superSpec =
--         Prod.fst <$> (simulateQ loggingOracle (oa.liftComp superSpec)).run := by
--   induction oa using OracleComp.induction with
--   | pure a => simp
--   | query_bind i t oa ih => simp [simulateQ_bind, ih]
--   | failure => simp

-- end loggingOracle

section Execution

variable {ι : Type} {oSpec : OracleSpec ι}
  {StmtIn : Type} {ιₛᵢ : Type} {OStmtIn : ιₛᵢ → Type} [Oₛᵢ : ∀ i, OracleInterface (OStmtIn i)]
 {WitIn : Type}
  {StmtOut : Type} {ιₛₒ : Type} {OStmtOut : ιₛₒ → Type} {WitOut : Type}
  {n : ℕ} {pSpec : ProtocolSpec n}

namespace Prover

/--
Prover's function for processing the next round, given the current result of the previous round, and
a function for getting the challenge.
-/
@[inline, specialize]
def processRound (j : Fin n)
    (prover : Prover oSpec StmtIn WitIn StmtOut WitOut pSpec)
    (currentResult : OracleComp (oSpec + [pSpec.Challenge]ₒ)
      (pSpec.Transcript j.castSucc × prover.PrvState j.castSucc)) :
      OracleComp (oSpec + [pSpec.Challenge]ₒ)
        (pSpec.Transcript j.succ × prover.PrvState j.succ) := do
  let ⟨transcript, state⟩ ← currentResult
  match hDir : pSpec.dir j with
  | .V_to_P => do
    let challenge ← pSpec.getChallenge ⟨j, hDir⟩
    letI newState := (← prover.receiveChallenge ⟨j, hDir⟩ state) challenge
    return ⟨transcript.concat challenge, newState⟩
  | .P_to_V => do
    let ⟨msg, newState⟩ ← prover.sendMessage ⟨j, hDir⟩ state
    return ⟨transcript.concat msg, newState⟩

/-- Run the prover in an interactive reduction up to round index `i`, via first inputting the
  statement and witness, and then processing each round up to round `i`. Returns the transcript up
  to round `i`, and the prover's state after round `i`.
-/
@[inline, specialize]
def runToRound (i : Fin (n + 1))
    (stmt : StmtIn) (wit : WitIn) (prover : Prover oSpec StmtIn WitIn StmtOut WitOut pSpec) :
      OracleComp (oSpec + [pSpec.Challenge]ₒ) (pSpec.Transcript i × prover.PrvState i) :=
  Fin.induction
    (pure ⟨default, prover.input (stmt, wit)⟩)
    (prover.processRound)
    i

/-- Run the prover in an interactive reduction up to round `i`, logging all the queries made by the
  prover. Returns the transcript up to that round, the prover's state after that round, and the
  log of the prover's oracle queries. This basically just wraps `runToRound` with a logging
  oracle.
-/
@[inline, specialize]
def runWithLogToRound (i : Fin (n + 1))
    (stmt : StmtIn) (wit : WitIn) (prover : Prover oSpec StmtIn WitIn StmtOut WitOut pSpec) :
      OracleComp (oSpec + [pSpec.Challenge]ₒ)
        ((pSpec.Transcript i × prover.PrvState i) × QueryLog (oSpec + [pSpec.Challenge]ₒ)) :=
  WriterT.run (simulateQ loggingOracle (prover.runToRound i stmt wit))

private lemma fst_map_simulateQ_loggingOracle_run {ι : Type} {spec : OracleSpec ι} {α : Type}
    (oa : OracleComp spec α) :
    Prod.fst <$> WriterT.run (simulateQ loggingOracle oa) = oa := by
  exact loggingOracle.fst_map_run_simulateQ oa

@[simp]
lemma runWithLogToRound_discard_log_eq_runToRound (i : Fin (n + 1))
    (stmt : StmtIn) (wit : WitIn) (prover : Prover oSpec StmtIn WitIn StmtOut WitOut pSpec) :
      Prod.fst <$> prover.runWithLogToRound i stmt wit =
        prover.runToRound i stmt wit := by
  simp [runWithLogToRound, runToRound]

/-- Run the prover in an interactive reduction. Returns the output statement and witness, and the
  transcript. See `runWithLog` for a version that additionally returns the log of the
  prover's oracle queries.
-/
@[inline, specialize]
def run (stmt : StmtIn) (wit : WitIn)
    (prover : Prover oSpec StmtIn WitIn StmtOut WitOut pSpec) :
      OracleComp (oSpec + [pSpec.Challenge]ₒ) (FullTranscript pSpec × StmtOut × WitOut) := do
  let ⟨transcript, state⟩ ← prover.runToRound (Fin.last n) stmt wit
  return ⟨transcript, ← prover.output state⟩

/-- Run the prover in an interactive reduction, logging all the queries made by the prover. Returns
  the transcript, the output statement and witness, and the log of the prover's oracle queries.

Note: this is just a wrapper around `run` that logs the queries made by the prover.
-/
@[inline, specialize]
def runWithLog (stmt : StmtIn) (wit : WitIn)
    (prover : Prover oSpec StmtIn WitIn StmtOut WitOut pSpec) :
      OracleComp (oSpec + [pSpec.Challenge]ₒ)
        ((FullTranscript pSpec × StmtOut × WitOut) × QueryLog (oSpec + [pSpec.Challenge]ₒ)) :=
  (simulateQ loggingOracle (prover.run stmt wit)).run

@[simp]
lemma runWithLog_discard_log_eq_run (stmt : StmtIn) (wit : WitIn)
    (prover : Prover oSpec StmtIn WitIn StmtOut WitOut pSpec) :
      Prod.fst <$> prover.runWithLog stmt wit = prover.run stmt wit := by
  simp [runWithLog]

end Prover

private lemma fst_map_liftComp_simulateQ_loggingOracle_run {ι τ : Type}
    {spec : OracleSpec ι} {superSpec : OracleSpec τ} {α : Type}
    [MonadLiftT (OracleQuery spec) (OracleQuery superSpec)]
    (oa : OracleComp spec α) :
    Prod.fst <$> (WriterT.run (simulateQ loggingOracle oa)).liftComp superSpec =
      oa.liftComp superSpec := by
  rw [← OracleComp.liftComp_map]
  exact congrArg (fun x => x.liftComp superSpec)
    (loggingOracle.fst_map_run_simulateQ oa)

/-- Run the (non-oracle) verifier in an interactive reduction. It takes in the input statement and
  the transcript, and return the output statement.
-/
@[inline, specialize, reducible]
def Verifier.run (stmt : StmtIn) (transcript : FullTranscript pSpec)
    (verifier : Verifier oSpec StmtIn StmtOut pSpec) : OptionT (OracleComp oSpec) StmtOut :=
  verifier.verify stmt transcript

/-- Run the oracle verifier in the interactive protocol. Returns the verifier's output, including
    both the output statement and oracle statements, and the log of queries made by the verifier.
-/
@[inline, specialize]
def OracleVerifier.run [Oₘ : ∀ i, OracleInterface (pSpec.Message i)]
    (stmt : StmtIn) (oStmtIn : ∀ i, OStmtIn i) (transcript : FullTranscript pSpec)
    (verifier : OracleVerifier oSpec StmtIn OStmtIn StmtOut OStmtOut pSpec) :
      OptionT (OracleComp oSpec) (StmtOut × (∀ i, OStmtOut i)) := do
  let f := OracleInterface.simOracle2 oSpec oStmtIn transcript.messages
  let stmtOut ← simulateQ f (verifier.verify stmt transcript.challenges)
  let oStmtOut : ∀ i, OStmtOut i := fun i => match h : verifier.embed i with
    | .inl j => (verifier.hEq i ▸ h ▸ oStmtIn j : OStmtOut i)
    | .inr j => (verifier.hEq i ▸ h ▸ transcript.messages j : OStmtOut i)
  return ⟨stmtOut, oStmtOut⟩

/-- Running an oracle verifier then is equal to running its non-oracle counterpart -/
@[simp]
theorem OracleVerifier.run_eq_run_verifier [Oₘ : ∀ i, OracleInterface (pSpec.Message i)]
    {stmt : StmtIn} {oStmt : ∀ i, OStmtIn i} {transcript : FullTranscript pSpec}
    {verifier : OracleVerifier oSpec StmtIn OStmtIn StmtOut OStmtOut pSpec} :
      verifier.run stmt oStmt transcript =
        verifier.toVerifier.run ⟨stmt, oStmt⟩ transcript := by
  simp only [OracleVerifier.run, OracleVerifier.toVerifier, Verifier.run]
  rfl

/-- An execution of an interactive reduction on a given initial statement and witness. Consists of
  first running the prover, and then the verifier. Returns the full transcript, the output statement
  and witness from the prover, and the output statement from the verifier.

  See `Reduction.runWithLog` for a version that additionally returns the logs of the prover's and
  the verifier's oracle queries.
-/
@[inline, specialize]
def Reduction.run (stmt : StmtIn) (wit : WitIn)
    (reduction : Reduction oSpec StmtIn WitIn StmtOut WitOut pSpec) :
      OptionT (OracleComp (oSpec + [pSpec.Challenge]ₒ))
        ((FullTranscript pSpec × StmtOut × WitOut) × StmtOut) := do
  -- `ctxOut` contains both the output statement and witness after running the prover
  let proverResult ← reduction.prover.run stmt wit
  let stmtOut ← liftM (reduction.verifier.run stmt proverResult.1).run
  return ⟨proverResult, ← stmtOut.getM⟩

/-- Run a reduction and return only the verifier's output statement, discarding the full transcript
  and prover witness. Useful when only the final verdict matters (e.g. for `Proof`s). -/
def Reduction.verdict (stmt : StmtIn) (wit : WitIn)
    (reduction : Reduction oSpec StmtIn WitIn StmtOut WitOut pSpec) :
      OptionT (OracleComp (oSpec + [pSpec.Challenge]ₒ)) StmtOut := do
  let ⟨_, stmtOut⟩ ← reduction.run stmt wit
  return stmtOut

/-- Running `Reduction.verdict` is running the reduction and projecting the verdict. -/
lemma Reduction.verdict_run_eq_map_run
    (reduction : Reduction oSpec StmtIn WitIn StmtOut WitOut pSpec)
    (stmt : StmtIn) (wit : WitIn) :
    (reduction.verdict stmt wit).run =
      Option.map (fun result : (FullTranscript pSpec × StmtOut × WitOut) × StmtOut =>
        result.2) <$> (reduction.run stmt wit).run := by
  simp [Reduction.verdict, OptionT.run_map]

/-- Run a reduction on `L` instances (given by indexed statements and witnesses), and sequence the
  full successful run results. Returns `none` if any instance fails, otherwise returns a function
  from indices to the full run data. -/
def Reduction.allRuns {L : ℕ}
    (stmts : Fin L → StmtIn) (wits : Fin L → WitIn)
    (reduction : Reduction oSpec StmtIn WitIn StmtOut WitOut pSpec) :
      OracleComp (oSpec + [pSpec.Challenge]ₒ)
        (Option (Fin L → ((FullTranscript pSpec × StmtOut × WitOut) × StmtOut))) := do
  let results ← (Vector.ofFn id).mapM fun i => (reduction.run (stmts i) (wits i)).run
  return (results.mapM id).map fun v => fun i => v[i]

/-- Run a reduction on `L` instances and project each successful full run result through `extract`.
  Returns `none` if any instance fails, otherwise returns the indexed extracted outputs. -/
def Reduction.allOutputs {L : ℕ} {α : Type}
    (extract : ((FullTranscript pSpec × StmtOut × WitOut) × StmtOut) → α)
    (stmts : Fin L → StmtIn) (wits : Fin L → WitIn)
    (reduction : Reduction oSpec StmtIn WitIn StmtOut WitOut pSpec) :
      OracleComp (oSpec + [pSpec.Challenge]ₒ) (Option (Fin L → α)) := do
  let results ← reduction.allRuns stmts wits
  return results.map fun resultOf => fun i => extract (resultOf i)

/-- Run a reduction on `L` instances (given by indexed statements and witnesses), and sequence the
  results. Returns `none` if any instance fails, otherwise returns a function from indices to
  the verifier's output statements. -/
def Reduction.allVerdicts {L : ℕ}
    (stmts : Fin L → StmtIn) (wits : Fin L → WitIn)
    (reduction : Reduction oSpec StmtIn WitIn StmtOut WitOut pSpec) :
      OracleComp (oSpec + [pSpec.Challenge]ₒ) (Option (Fin L → StmtOut)) := do
  let results ← (Vector.ofFn id).mapM fun i => (reduction.verdict (stmts i) (wits i)).run
  return (results.mapM id).map fun v => fun i => v[i]

/-- `allVerdicts` has the same distribution as `allOutputs` with a projection retaining the
  verifier output as the first component; it differs only by a pure post-map. -/
lemma Reduction.allVerdicts_eq_map_allOutputs_fst {L : ℕ} {β : Type}
    (extract : ((FullTranscript pSpec × StmtOut × WitOut) × StmtOut) → β)
    (stmts : Fin L → StmtIn) (wits : Fin L → WitIn)
    (reduction : Reduction oSpec StmtIn WitIn StmtOut WitOut pSpec) :
    reduction.allVerdicts stmts wits =
      (Option.map (fun resultOf => fun i => (resultOf i).1)) <$>
        reduction.allOutputs (fun result => (result.2, extract result)) stmts wits := by
  unfold Reduction.allVerdicts Reduction.allOutputs Reduction.allRuns
  simp only [map_eq_bind_pure_comp, bind_assoc, pure_bind, Function.comp_apply]
  rw [Vector.mapM_bind_map_eq
    (v := Vector.ofFn (id : Fin L → Fin L))
    (f₁ := fun i => (reduction.verdict (stmts i) (wits i)).run)
    (f₂ := fun i => (reduction.run (stmts i) (wits i)).run)
    (g := Option.map (fun result : (FullTranscript pSpec × StmtOut × WitOut) × StmtOut =>
      result.2))
    (post₁ := fun results =>
      pure ((results.mapM id).map fun v => fun i => v[i]))
    (post₂ := fun results =>
      pure (Option.map (fun resultOf => fun i => (resultOf i).1)
        (Option.map (fun resultOf => fun i => ((resultOf i).2, extract (resultOf i)))
          (Option.map (fun v => fun i => v[i]) (results.mapM id)))))]
  · intro i
    exact Reduction.verdict_run_eq_map_run reduction (stmts i) (wits i)
  · intro results
    congr 1
    rw [Vector.mapM_id_option_map_comm]
    cases h : results.mapM id with
    | none => simp
    | some v =>
        simp only [Option.map_some, Option.some.injEq]
        funext i
        simp

lemma Reduction.support_allOutputs_index
    {StmtIn WitIn StmtOut WitOut α : Type} {n : ℕ} {pSpec : ProtocolSpec n} {L : ℕ}
    (extract : ((FullTranscript pSpec × StmtOut × WitOut) × StmtOut) → α)
    (stmts : Fin L → StmtIn) (wits : Fin L → WitIn)
    (reduction : Reduction oSpec StmtIn WitIn StmtOut WitOut pSpec)
    {y : Option (Fin L → α)}
    (hy : y ∈ support (reduction.allOutputs extract stmts wits))
    {resultOf : Fin L → α} (hy_eq : y = some resultOf) (i : Fin L) :
      ∃ result, some result ∈ support (reduction.run (stmts i) (wits i)).run ∧
        extract result = resultOf i := by
  unfold Reduction.allOutputs at hy
  rw [mem_support_bind_iff] at hy
  obtain ⟨runsOpt, hrunsOpt, hy_mem⟩ := hy
  rw [mem_support_pure_iff] at hy_mem
  rw [hy_eq] at hy_mem
  cases hruns : runsOpt with
  | none => simp [hruns] at hy_mem
  | some runOf =>
      simp only [hruns, Option.map_some, Option.some.injEq] at hy_mem
      unfold Reduction.allRuns at hrunsOpt
      rw [mem_support_bind_iff] at hrunsOpt
      obtain ⟨results, hresults, hrunsOpt⟩ := hrunsOpt
      rw [mem_support_pure_iff] at hrunsOpt
      cases hseq : results.mapM id with
      | none => simp [hseq, hruns] at hrunsOpt
      | some results' =>
          simp only [hseq, Option.map_some] at hrunsOpt
          rw [hruns] at hrunsOpt
          simp only [Option.some.injEq] at hrunsOpt
          have hidx : results[i] = some results'[i] :=
            Vector.mapM_id_some_index hseq i
          refine ⟨results'[i], ?_, ?_⟩
          · simpa [hidx] using
              OracleComp.support_ofFn_mapM_index
                (fun i => (reduction.run (stmts i) (wits i)).run) hresults i
          · have hrunOf_i := congrFun hrunsOpt i
            have hresult_i := congrFun hy_mem i
            rw [hresult_i, hrunOf_i]

/-- If a reduction's verifier is a pure function `f` of the input statement and full transcript,
    then the verifier output of any complete result in the support of `Reduction.run` equals
    `f stmt td` applied to the input statement and the produced transcript. -/
lemma Reduction.support_run_pure_verifier
    {StmtIn WitIn StmtOut WitOut : Type}
    {n : ℕ} {pSpec : ProtocolSpec n}
    (reduction : Reduction oSpec StmtIn WitIn StmtOut WitOut pSpec)
    (f : StmtIn → FullTranscript pSpec → StmtOut)
    (hf : ∀ stmt td,
      reduction.verifier.verify stmt td =
        (pure (f stmt td) : OptionT (OracleComp oSpec) StmtOut))
    (stmt : StmtIn) (wit : WitIn)
    {y : Option ((FullTranscript pSpec × StmtOut × WitOut) × StmtOut)}
    (hy : y ∈ support (reduction.run stmt wit).run)
    {td : FullTranscript pSpec} {prv : StmtOut × WitOut} {vOut : StmtOut}
    (heq : y = some ((td, prv), vOut)) : vOut = f stmt td := by
  rw [heq] at hy
  unfold Reduction.run at hy
  simp only [OptionT.run_bind, Option.elimM] at hy
  rw [mem_support_bind_iff] at hy
  obtain ⟨proverResultOpt, _hprover, hy⟩ := hy
  cases proverResultOpt with
  | none =>
      exfalso
      simp at hy
  | some proverResult =>
      simp only [Option.elim_some] at hy
      rw [mem_support_bind_iff] at hy
      obtain ⟨stmtOutOpt, hstmtOutOpt, hy⟩ := hy
      simp only [ChallengeIdx, Challenge, Verifier.run, hf, OptionT.run_pure, liftM_pure,
        support_pure, Set.mem_singleton_iff] at hstmtOutOpt
      subst stmtOutOpt
      simp only [Option.elim_some, Option.getM_some, OptionT.run_pure] at hy
      injection hy with hpair
      have htd : td = proverResult.1 := congrArg Prod.fst (congrArg Prod.fst hpair)
      have hvOut : vOut = f stmt proverResult.1 := congrArg Prod.snd hpair
      rw [htd]
      exact hvOut

/-- **Verifier-verdict transport for the soundness game.**  Any *accepting* support point of the
    simulated reduction run — i.e. `some x` in the support of
    `(simulateQ (impl.addLift challengeQueryImpl) (reduction.run stmt wit).run).run' s` — has its
    verifier verdict `x.2` reachable as a support point of the *verifier game*
    `(simulateQ impl (reduction.verifier.run stmt x.1.1)).run' s'` on the *realized* transcript
    `x.1.1`, for some intermediate state `s'`.

    This is the support-level bridge consumed by `rbrSoundness_implies_soundness` (obligation A): it
    ties a soundness-game support point's transcript `x.1.1` to its verdict `x.2`, exactly as
    `StateFunction.toFun_full` requires.  The proof walks the `OptionT`/`StateT` bind chain of
    `Reduction.run` (prover lift, then the verifier `OptionT` verdict, then `getM`), and collapses the
    `impl.addLift challengeQueryImpl` simulation of the `oSpec`-only verifier `verify` back to
    `simulateQ impl` via `QueryImpl.simulateQ_add_liftComp_left`. -/
theorem Reduction.support_run_verdict
    {StmtIn WitIn StmtOut WitOut : Type} {n : ℕ} {pSpec : ProtocolSpec n}
    [∀ i, SampleableType (pSpec.Challenge i)] {σ : Type}
    (reduction : Reduction oSpec StmtIn WitIn StmtOut WitOut pSpec)
    (impl : QueryImpl oSpec (StateT σ ProbComp)) (s : σ)
    (stmt : StmtIn) (wit : WitIn)
    (x : (FullTranscript pSpec × StmtOut × WitOut) × StmtOut)
    (hx : some x ∈ support
      (StateT.run' (simulateQ (impl.addLift challengeQueryImpl : QueryImpl _ (StateT σ ProbComp))
        (reduction.run stmt wit).run) s)) :
    ∃ s', some x.2 ∈ support
      (StateT.run' (simulateQ impl (reduction.verifier.run stmt x.1.1)) s') := by
  unfold Reduction.run at hx
  simp only [OptionT.run_bind, Option.elimM, simulateQ_bind, StateT.run'_eq, StateT.run_bind,
    support_bind, Set.mem_iUnion, support_map, Set.mem_image] at hx
  obtain ⟨⟨pOpt, s1⟩, hp_mem, hx⟩ := hx
  subst hx
  obtain ⟨⟨iOpt, is⟩, _hi_mem, hverif⟩ := hp_mem
  simp only at hverif
  cases iOpt with
  | none => simp only [Option.elim_none, simulateQ_pure, StateT.run_pure, support_pure,
      Set.mem_singleton_iff, Prod.mk.injEq, reduceCtorEq, false_and] at hverif
  | some pr =>
    simp only [Option.elim_some, Verifier.run, simulateQ_bind, StateT.run_bind,
      support_bind, Set.mem_iUnion] at hverif
    obtain ⟨⟨vOpt, vs⟩, hv_mem, hgetM⟩ := hverif
    simp only at hgetM
    cases vOpt with
    | none => simp only [Option.elim_none, simulateQ_pure, StateT.run_pure, support_pure,
        Set.mem_singleton_iff, Prod.mk.injEq, reduceCtorEq, false_and] at hgetM
    | some v =>
      cases v with
      | none => simp [Option.getM] at hgetM
      | some w =>
        simp only [Option.getM_some, OptionT.run_pure, pure_bind, Option.elim_some,
          simulateQ_pure, StateT.run_pure, support_pure, Set.mem_singleton_iff,
          Prod.mk.injEq] at hgetM
        obtain ⟨hxeq, _⟩ := hgetM
        have hxeq' : x = (pr, w) := Option.some.inj hxeq
        have hx1 : x.1 = pr := congrArg Prod.fst hxeq'
        have hx2 : x.2 = w := congrArg Prod.snd hxeq'
        refine ⟨is, ?_⟩
        rw [hx2, hx1, Verifier.run]
        rw [show ((liftM ((reduction.verifier.verify stmt pr.1).run) :
              OptionT (OracleComp (oSpec + [pSpec.Challenge]ₒ)) (Option StmtOut)).run)
            = (Option.some <$> OracleComp.liftComp
                ((reduction.verifier.verify stmt pr.1).run) (oSpec + [pSpec.Challenge]ₒ)) from by
              conv_lhs => dsimp only [liftM, MonadLiftT.monadLift, MonadLift.monadLift]
              simp only [OptionT.run_mk, OptionT.lift]
              erw [simulateQ_bind]
              simp only [simulateQ_pure, ← map_eq_pure_bind]
              rfl] at hv_mem
        rw [simulateQ_map, QueryImpl.addLift_def, QueryImpl.simulateQ_add_liftComp_left,
          QueryImpl.liftTarget_self, StateT.run_map, support_map, Set.mem_image] at hv_mem
        obtain ⟨⟨a, s'⟩, hmem, heq⟩ := hv_mem
        simp only [Prod.mk.injEq, Option.some.injEq] at heq
        obtain ⟨ha, _hs⟩ := heq
        show some w ∈ support (StateT.run' (simulateQ impl
          (reduction.verifier.verify stmt pr.1).run) is)
        rw [StateT.run'_eq, support_map, Set.mem_image]
        exact ⟨(a, s'), hmem, by rw [ha]⟩

/-- **State-preserving prover simulation.**  The implementation `impl` (lifted to the challenge
    spec) is *state-preserving* for `init` over `reduction` if running the prover phase (and the
    whole reduction) from any `init`-supported start state leaves the resulting verifier-game start
    state again in `support init`.

    Concretely, this is the witness condition produced by `support_run_verdict`: it asks that the
    POST-PROVER simulation state `s'` (from which the verifier's verdict is drawn) can be taken in
    `support init`.  This holds in the standard cryptographic setting — e.g. when `σ` is a
    subsingleton, when `impl` is stateless, or when the prover's `oSpec` queries are answered in a
    distribution/`support init`-preserving way (the challenge oracle never touches `σ`).  It FAILS
    for an arbitrary stateful `impl`, where a malicious prover can steer `σ` outside `support init`
    (see the FRONTIER NOTE below). -/
def Reduction.StatePreserving
    {StmtIn WitIn StmtOut WitOut : Type} {n : ℕ} {pSpec : ProtocolSpec n}
    [∀ i, SampleableType (pSpec.Challenge i)] {σ : Type}
    (reduction : Reduction oSpec StmtIn WitIn StmtOut WitOut pSpec)
    (init : ProbComp σ) (impl : QueryImpl oSpec (StateT σ ProbComp)) : Prop :=
  ∀ (stmt : StmtIn) (wit : WitIn) (s : σ), s ∈ support init →
    ∀ x : (FullTranscript pSpec × StmtOut × WitOut) × StmtOut,
      some x ∈ support
        (StateT.run' (simulateQ (impl.addLift challengeQueryImpl : QueryImpl _ (StateT σ ProbComp))
          (reduction.run stmt wit).run) s) →
      ∃ s' ∈ support init, some x.2 ∈ support
        (StateT.run' (simulateQ impl (reduction.verifier.run stmt x.1.1)) s')

/-- **Verdict reachability from a fresh `init` sample (state-preserving impl).**  Under
    `Reduction.StatePreserving`, an *accepting* support point `x` of the soundness game (run from a
    start state `s ∈ support init`) has its verifier verdict `x.2` reachable from a FRESH `init`
    sample on the realized transcript `x.1.1`.  This is exactly the shape that
    `StateFunction.toFun_full`'s contrapositive consumes (its probability event is over
    `OptionT.mk do (simulateQ impl (verifier.run stmt tr)).run' (← init)`), with the (A) state-
    threading gap discharged by the state-preservation hypothesis. -/
theorem Reduction.mem_support_verdict_init_of_statePreserving
    {StmtIn WitIn StmtOut WitOut : Type} {n : ℕ} {pSpec : ProtocolSpec n}
    [∀ i, SampleableType (pSpec.Challenge i)] {σ : Type}
    (reduction : Reduction oSpec StmtIn WitIn StmtOut WitOut pSpec)
    (init : ProbComp σ) (impl : QueryImpl oSpec (StateT σ ProbComp))
    (hPres : reduction.StatePreserving init impl)
    (stmt : StmtIn) (wit : WitIn) (s : σ) (hs : s ∈ support init)
    (x : (FullTranscript pSpec × StmtOut × WitOut) × StmtOut)
    (hx : some x ∈ support
      (StateT.run' (simulateQ (impl.addLift challengeQueryImpl : QueryImpl _ (StateT σ ProbComp))
        (reduction.run stmt wit).run) s)) :
    x.2 ∈ support
      (OptionT.mk (do
        (simulateQ impl (reduction.verifier.run stmt x.1.1)).run' (← init))
        : OptionT ProbComp StmtOut) := by
  obtain ⟨s', hs', hverdict⟩ := hPres stmt wit s hs x hx
  rw [OptionT.mem_support_iff]
  simp only [OptionT.run_mk, mem_support_bind_iff]
  exact ⟨s', hs', hverdict⟩

/-- An execution of an interactive reduction on a given initial statement and witness. Consists of
  first running the prover, and then the verifier. Returns the full transcript, the output statement
  and witness from the prover, and the output statement from the verifier, along with the logs of
  the prover's and the verifier's oracle queries.
-/
@[inline, specialize]
def Reduction.runWithLog (stmt : StmtIn) (wit : WitIn)
    (reduction : Reduction oSpec StmtIn WitIn StmtOut WitOut pSpec) :
      OptionT (OracleComp (oSpec + [pSpec.Challenge]ₒ))
        (((FullTranscript pSpec × StmtOut × WitOut) × StmtOut) ×
          QueryLog (oSpec + [pSpec.Challenge]ₒ) × QueryLog oSpec) := do
  -- `ctxOut` contains both the output statement and witness after running the prover
  let ⟨proverResult, proveQueryLog⟩ ← reduction.prover.runWithLog stmt wit
  let ⟨stmtOut, verifyQueryLog⟩ ←
    liftM (simulateQ loggingOracle (reduction.verifier.run stmt proverResult.1)).run
  return ⟨⟨proverResult, ← stmtOut.getM⟩, proveQueryLog, verifyQueryLog⟩

/-- Map over the first component of a monadic product by pairing it with a fixed value. -/
private lemma Monad.map_of_prod_fst_eq_prod_fst {m : Type u → Type v} [Monad m] [LawfulMonad m]
    {α β γ : Type u} (ma : m (α × β)) (c : γ) :
    (fun a => (c, a.1)) <$> ma = Prod.mk c <$> Prod.fst <$> ma := by
  simp only [Functor.map_map]

/-- In OptionT, lifting a pair-valued computation and projecting the first component
in the continuation equals lifting the map and binding directly. -/
private lemma OptionT_liftM_bind_fst {m : Type → Type} [Monad m] [LawfulMonad m]
    {α β γ : Type} (x : m (α × β)) (f : α → OptionT m γ) :
    ((liftM x : OptionT m _) >>= fun p => f p.1) =
    (liftM (Prod.fst <$> x) : OptionT m _) >>= f := by
  rw [← bind_map_left]
  show (Prod.fst <$> monadLift x) >>= f = monadLift (Prod.fst <$> x) >>= f
  congr 1
  simp [liftM, MonadLift.monadLift, OptionT.lift, OptionT.mk,
    Functor.map_map, Function.comp]

/-- Logging the queries made by both parties do not change the output of the reduction -/
@[simp]
theorem Reduction.runWithLog_discard_logs_eq_run
    {stmt : StmtIn} {wit : WitIn}
    {reduction : Reduction oSpec StmtIn WitIn StmtOut WitOut pSpec} :
      Prod.fst <$>
        reduction.runWithLog stmt wit = reduction.run stmt wit := by
  simp only [Reduction.runWithLog, Reduction.run, map_bind, map_pure, Functor.map_map,
    Function.comp]
  have h1 := OptionT_liftM_bind_fst (m := OracleComp (oSpec + [pSpec.Challenge]ₒ))
    (Prover.runWithLog stmt wit reduction.prover)
    (fun proverResult =>
      liftM (simulateQ loggingOracle (Verifier.run stmt proverResult.1 reduction.verifier)).run
        >>= fun a_1 => (fun a_2 => (proverResult, a_2)) <$> a_1.1.getM)
  -- Prover logging elimination: use OptionT_liftM_bind_fst + Prover.runWithLog_discard_log_eq_run
  exact h1 ▸ by
    rw [Prover.runWithLog_discard_log_eq_run]
    congr 1; ext proverResult
    -- Verifier logging elimination by induction on the verifier computation
    generalize Verifier.run stmt proverResult.1 reduction.verifier = vc
    induction vc using OracleComp.induction with
    | pure a => simp [simulateQ_pure, WriterT.run_pure]; rfl
    | query_bind t oa ih =>
      simp only [run_simulateQ_loggingOracle_query_bind]
      simp [bind_map_left, ih, OptionT.run_bind, Option.elimM, bind_assoc, OptionT.run_map]
      -- Remaining: OptionT.run distributing through liftM + bind on RHS
      -- The RHS has OptionT.run (liftM (query t) >>= oa) which should equal
      -- query t >>= fun u => OptionT.run (oa u). This is monadLift_bind for OptionT SubSpec.
      rfl
  -- calc
  -- _ = (do
  --   let a ← (simulateQ loggingOracle proverRun).run
  --   (fun aFst : (pSpec.FullTranscript × StmtOut × WitOut) => (fun b => (aFst, Prod.fst b)) <$>
  --       (simulateQ loggingOracle (Verifier.run stmt aFst.1 reduction.verifier)).run.liftComp
  --         (oSpec + [pSpec.Challenge]ₒ)) a.1) := rfl
  -- _ = _ := by
    -- rw [loggingOracle.simulateQ_bind_fst_comp proverRun
    --   (fun a => (fun b => (a, Prod.fst b)) <$>
    --     (simulateQ loggingOracle (Verifier.run stmt a.1 reduction.verifier)).run.liftComp
    --       (oSpec + [pSpec.Challenge]ₒ))]
    -- congr
    -- ext proverResult
    -- rw [← Functor.map_map]
    -- simp


/-- Run an interactive oracle reduction. Returns the full transcript, the output statement and
  witness, the log of all prover's oracle queries, and the log of all verifier's oracle queries to
  the prover's messages and to the shared oracle.
-/
@[inline, specialize]
def OracleReduction.run [∀ i, OracleInterface (pSpec.Message i)]
    (stmt : StmtIn) (oStmt : ∀ i, OStmtIn i) (wit : WitIn)
    (reduction : OracleReduction oSpec StmtIn OStmtIn WitIn StmtOut OStmtOut WitOut pSpec) :
      OptionT (OracleComp (oSpec + [pSpec.Challenge]ₒ))
        ((FullTranscript pSpec × (StmtOut × ∀ i, OStmtOut i) × WitOut) ×
          (StmtOut × ∀ i, OStmtOut i)) := do
  let proverResult ← reduction.prover.run ⟨stmt, oStmt⟩ wit
  let stmtOut ← liftM (reduction.verifier.run stmt oStmt proverResult.1).run
  return ⟨proverResult, ← stmtOut.getM⟩

/-- Run an interactive oracle reduction. Returns the full transcript, the output statement and
  witness, the log of all prover's oracle queries, and the log of all verifier's oracle queries to
  the prover's messages and to the shared oracle.
-/
@[inline, specialize]
def OracleReduction.runWithLog [∀ i, OracleInterface (pSpec.Message i)]
    (stmt : StmtIn) (oStmt : ∀ i, OStmtIn i) (wit : WitIn)
    (reduction : OracleReduction oSpec StmtIn OStmtIn WitIn StmtOut OStmtOut WitOut pSpec) :
      OptionT (OracleComp (oSpec + [pSpec.Challenge]ₒ))
        ((FullTranscript pSpec × (StmtOut × ∀ i, OStmtOut i) × WitOut) ×
          (StmtOut × ∀ i, OStmtOut i) ×
            QueryLog (oSpec + [pSpec.Challenge]ₒ) × QueryLog oSpec) := do
  let ⟨proverResult, proveQueryLog⟩ ←
    (simulateQ loggingOracle (reduction.prover.run ⟨stmt, oStmt⟩ wit)).run
  let ⟨stmtOut, verifyQueryLog⟩ ←
    liftM (simulateQ loggingOracle (reduction.verifier.run stmt oStmt proverResult.1)).run
  return ⟨proverResult, ← stmtOut.getM, proveQueryLog, verifyQueryLog⟩

/-- Running an oracle reduction is equal to running its non-oracle counterpart -/
@[simp]
theorem OracleReduction.run_eq_run_reduction [∀ i, OracleInterface (pSpec.Message i)]
    {stmt : StmtIn} {oStmt : ∀ i, OStmtIn i} {wit : WitIn}
    {oracleReduction : OracleReduction oSpec StmtIn OStmtIn WitIn StmtOut OStmtOut WitOut pSpec} :
      oracleReduction.run stmt oStmt wit =
        oracleReduction.toReduction.run ⟨stmt, oStmt⟩ wit := by
  simp only [OracleReduction.run, Reduction.run, OracleVerifier.run_eq_run_verifier,
    OracleReduction.toReduction]

/-- Running an oracle reduction with logging of queries to the shared oracle is equal to running its
  non-oracle counterpart with logging of queries to the shared oracle -/
@[simp]
theorem OracleReduction.runWithLog_eq_runWithLog_reduction [∀ i, OracleInterface (pSpec.Message i)]
    {stmt : StmtIn} {oStmt : ∀ i, OStmtIn i} {wit : WitIn}
    {oracleReduction : OracleReduction oSpec StmtIn OStmtIn WitIn StmtOut OStmtOut WitOut pSpec} :
      oracleReduction.run stmt oStmt wit =
        oracleReduction.toReduction.run ⟨stmt, oStmt⟩ wit := by
  simp only [OracleReduction.run, Reduction.run, OracleVerifier.run_eq_run_verifier,
    OracleReduction.toReduction]

@[simp]
theorem Prover.runToRound_zero_of_prover_first
    (stmt : StmtIn) (wit : WitIn) (prover : Prover oSpec StmtIn WitIn StmtOut WitOut pSpec) :
      prover.runToRound 0 stmt wit = (pure (default, prover.input (stmt, wit))) := by
  simp [Prover.runToRound]

namespace Prover

/-! ### Prefix / marginal decomposition of `runToRound` over rounds

These additive lemmas relate the prover's full run to its per-round partial runs.  They are the
execution-level ingredients of the `rbrSoundness → soundness` implication (ArkLib#1): the
round-by-round soundness game speaks about `runToRound i.castSucc` followed by a *fresh* challenge,
whereas the soundness game speaks about the full `Reduction.run`.  The lemmas below expose the
single-round step `runToRound j.succ = processRound j (runToRound j.castSucc)` and, for a challenge
round, factor the run as "partial run, then sample a challenge, then receive it". -/

/-- **Single-round unfolding of `runToRound`.**  Running the prover up to round `j.succ` is the same
  as running it up to round `j.castSucc` and then processing round `j`.  This is the computational
  recursion of `runToRound`, made into a rewriting lemma via `Fin.induction_succ`. -/
theorem runToRound_succ (j : Fin n)
    (stmt : StmtIn) (wit : WitIn) (prover : Prover oSpec StmtIn WitIn StmtOut WitOut pSpec) :
    prover.runToRound j.succ stmt wit
      = prover.processRound j (prover.runToRound j.castSucc stmt wit) := by
  unfold runToRound
  rw [Fin.induction_succ]

/-- **`processRound` at a challenge (V_to_P) round.**  Specialization of `processRound` to a round
  `i` that is a challenge round (so `pSpec.dir i = .V_to_P`).  The dependent `match` on the round
  direction is discharged using the direction proof carried by the `ChallengeIdx`, exposing the
  clean "sample a challenge, then receive it" shape. -/
theorem processRound_challenge (i : pSpec.ChallengeIdx)
    (prover : Prover oSpec StmtIn WitIn StmtOut WitOut pSpec)
    (currentResult : OracleComp (oSpec + [pSpec.Challenge]ₒ)
      (pSpec.Transcript i.1.castSucc × prover.PrvState i.1.castSucc)) :
    prover.processRound i.1 currentResult = (do
      let ⟨transcript, state⟩ ← currentResult
      let challenge ← pSpec.getChallenge i
      let newState := (← prover.receiveChallenge i state) challenge
      return ⟨transcript.concat challenge, newState⟩) := by
  unfold processRound
  obtain ⟨j, hj⟩ := i
  simp only
  congr 1
  funext x
  split <;> rename_i hDir
  · rfl
  · rw [hj] at hDir; exact absurd hDir (by decide)

/-- **Transcript-marginal factorization at a challenge round.**  For a challenge round `i`, the
  transcript produced by running the prover up to round `i.succ` is distributed as: run up to round
  `i.castSucc`, sample a fresh challenge, *receive* it (the side effect is retained, it can only
  fail), and concatenate the challenge to the transcript.

  This is the exact bridge between the soundness game (which runs the prover to completion, hence
  through `receiveChallenge`) and the round-by-round soundness game (which runs only to
  `runToRound i.castSucc` and then samples a fresh challenge): the only difference is the trailing
  `receiveChallenge` step, whose effect on the resulting *transcript* is none (the transcript is
  already determined). -/
theorem fst_map_runToRound_succ_challenge (i : pSpec.ChallengeIdx)
    (stmt : StmtIn) (wit : WitIn) (prover : Prover oSpec StmtIn WitIn StmtOut WitOut pSpec) :
    (fun x => x.1) <$> prover.runToRound i.1.succ stmt wit
      = (do
          let ⟨transcript, state⟩ ← prover.runToRound i.1.castSucc stmt wit
          let challenge ← (pSpec.getChallenge i : OracleComp (oSpec + [pSpec.Challenge]ₒ) _)
          let _ ← prover.receiveChallenge i state
          return transcript.concat challenge) := by
  rw [runToRound_succ, processRound_challenge]
  simp only [map_bind, map_pure]

/-! ### Prover-run transcript-prefix consistency (keystone marginal bridge)

The round-by-round soundness game speaks about the round-`i.succ` transcript produced by
`runToRound i.succ`, while the soundness game runs the prover to completion (`runToRound (last n)`).
The geometric lemma below records the *value*-level fact that processing a later round only `snoc`s a
new entry onto the transcript and never alters earlier ones, so taking a round-`m` prefix discards
the appended entry.  (Note: this does NOT lift to a distributional equality between the full-run
prefix marginal and `runToRound m`, because the intervening `sendMessage`/`receiveChallenge` steps
can fail — only the failure-monotone `≤` direction holds; see the FRONTIER NOTE below.) -/

/-- **`Fin.take` of a `snoc` below the cut.**  Taking the first `m ≤ k` entries of `Fin.snoc T msg`
(a tuple of length `k + 1`) discards the appended `msg` and equals taking the first `m` entries of
`T`.  The geometric core of transcript-prefix preservation under `processRound`. -/
theorem fin_take_snoc_of_le {k m : ℕ} (hm : m ≤ k) {α : Fin (k + 1) → Sort*}
    (T : (i : Fin k) → α i.castSucc) (msg : α (Fin.last k)) :
    Fin.take m (by omega) (Fin.snoc T msg) = Fin.take m hm (fun i => T i) := by
  rw [← Fin.take_init m hm (Fin.snoc T msg), Fin.init_snoc]

/-! ### Round-range decomposition of `runToRound` (the keystone monadic bridge)

The round-by-round soundness game speaks about the round-`i.succ` transcript prefix, while the
soundness game runs the prover to completion (`runToRound (last n)`).  The keystone below factors the
full run as the partial run *up to any earlier round* `k` followed by a continuation that folds
`processRound` over the remaining rounds `k .. j-1`.  This is a plain `OracleComp` *equality* (the
continuation only `processRound`s further rounds; no probabilistic content), which is exactly the
shape `Verifier.StateFunction.probEvent_simulateQ_run'_bind_trailing_le` consumes to drop the
trailing rounds (and the verifier/`output` tail) while exposing the `runToRound k` prefix that
`fst_map_runToRound_succ_challenge` then rewrites into the round-by-round game shape. -/

/-- **Kleisli continuation folding `processRound` over rounds `k .. j-1`.**  Transforms a round-`k`
partial result `(transcript, state)` into the round-`j` partial run, by folding `processRound`.
Defined by `Fin.induction` on the *target* index `j`: when the running index reaches `k` exactly it
returns the supplied start `rk` (`pure`), and each subsequent `succ` step applies one more
`processRound`.  (The `j < k` branches are never used; for those the dependent-`Fin` base is filled
with the `runToRound 0` seed value, kept only to make the fold total.)  This is the data half of the
round-range decomposition `runToRound_eq_bind_continueFromTo`. -/
noncomputable def continueFromTo (prover : Prover oSpec StmtIn WitIn StmtOut WitOut pSpec)
    (stmt : StmtIn) (wit : WitIn) (k : Fin (n + 1)) :
    (j : Fin (n + 1)) →
      (pSpec.Transcript k × prover.PrvState k) →
        OracleComp (oSpec + [pSpec.Challenge]ₒ) (pSpec.Transcript j × prover.PrvState j) :=
  Fin.induction
    (motive := fun j => (pSpec.Transcript k × prover.PrvState k) →
        OracleComp (oSpec + [pSpec.Challenge]ₒ) (pSpec.Transcript j × prover.PrvState j))
    (fun rk => if h : (k : Fin (n + 1)) = 0 then h ▸ pure rk
               else pure (default, prover.input (stmt, wit)))
    (fun m prev rk =>
      if h : (k : Fin (n + 1)) = m.succ then h ▸ pure rk
      else prover.processRound m (prev rk))

/-- **`continueFromTo` step at a `succ` target that has not yet reached the start.**  When the target
`m.succ` is *strictly past* the start index `k` (`k ≠ m.succ`), the continuation applies one more
`processRound m` on top of the round-`m.castSucc` continuation. -/
theorem continueFromTo_succ_of_ne (prover : Prover oSpec StmtIn WitIn StmtOut WitOut pSpec)
    (stmt : StmtIn) (wit : WitIn) (k : Fin (n + 1)) (m : Fin n)
    (hne : (k : Fin (n + 1)) ≠ m.succ)
    (rk : pSpec.Transcript k × prover.PrvState k) :
    continueFromTo prover stmt wit k m.succ rk
      = prover.processRound m (continueFromTo prover stmt wit k m.castSucc rk) := by
  unfold continueFromTo
  rw [Fin.induction_succ]
  simp only [hne, ↓reduceDIte]

/-- **`continueFromTo` at the diagonal is the identity (`pure`).**  Continuing from round `k` to
round `k` returns the start result unchanged. -/
theorem continueFromTo_self (prover : Prover oSpec StmtIn WitIn StmtOut WitOut pSpec)
    (stmt : StmtIn) (wit : WitIn)
    (k : Fin (n + 1)) (rk : pSpec.Transcript k × prover.PrvState k) :
    continueFromTo prover stmt wit k k rk = pure rk := by
  unfold continueFromTo
  induction k using Fin.induction with
  | zero => simp [Fin.induction_zero]
  | succ m _ => simp [Fin.induction_succ]

/-- **`processRound` factors as a bind on its input.**  Since `processRound j cur` first runs `cur`
and then performs a round-`j` step depending only on `cur`'s output, it equals `cur >>= (round-j step
on a `pure`d result)`.  The monadic-associativity ingredient of the round-range decomposition. -/
theorem processRound_eq_bind (j : Fin n) (prover : Prover oSpec StmtIn WitIn StmtOut WitOut pSpec)
    (cur : OracleComp (oSpec + [pSpec.Challenge]ₒ)
      (pSpec.Transcript j.castSucc × prover.PrvState j.castSucc)) :
    prover.processRound j cur = cur >>= (fun r => prover.processRound j (pure r)) := by
  unfold processRound
  simp only [pure_bind]

/-- **Round-range decomposition of `runToRound` (THE keystone).**  For any earlier round `k ≤ j`, the
prover run up to round `j` equals the run up to round `k` followed by the continuation
`continueFromTo` that folds `processRound` over rounds `k .. j-1`.  A plain `OracleComp` equality,
proved by `Fin.induction` on `j` (with `k` fixed) via the single-round unfolding `runToRound_succ`,
the `processRound` bind-factorization `processRound_eq_bind`, and monad associativity.

This is the missing structural connective of the `rbrSoundness → soundness` probability bridge: with
`k := i.succ` and `j := Fin.last n` it exposes the round-`i.succ` prefix (whose transcript determines
the per-round flip event) as a `>>=`-prefix of the full run, to which the failure-monotone transport
`Verifier.StateFunction.probEvent_simulateQ_run'_bind_trailing_le` and the per-round factorization
`fst_map_runToRound_succ_challenge` then apply. -/
theorem runToRound_eq_bind_continueFromTo
    (prover : Prover oSpec StmtIn WitIn StmtOut WitOut pSpec)
    (stmt : StmtIn) (wit : WitIn) (k j : Fin (n + 1)) (hkj : k ≤ j) :
    prover.runToRound j stmt wit
      = prover.runToRound k stmt wit >>= continueFromTo prover stmt wit k j := by
  induction j using Fin.induction with
  | zero =>
    have hk0 : k = 0 := le_antisymm hkj (Fin.zero_le _)
    subst hk0
    conv_rhs => rw [show (continueFromTo prover stmt wit 0 0)
                      = (fun rk => pure rk) from funext (continueFromTo_self prover stmt wit 0)]
    rw [bind_pure]
  | succ m ih =>
    rcases eq_or_lt_of_le hkj with heq | hlt
    · subst heq
      conv_rhs => rw [show (continueFromTo prover stmt wit (m.succ) (m.succ))
                        = (fun rk => pure rk)
                          from funext (continueFromTo_self prover stmt wit _)]
      rw [bind_pure]
    · have hkm : k ≤ m.castSucc := by rw [Fin.le_castSucc_iff]; exact hlt
      have hne : (k : Fin (n + 1)) ≠ m.succ := ne_of_lt hlt
      rw [runToRound_succ, ih hkm]
      have hcont : continueFromTo prover stmt wit k m.succ
          = fun rk => prover.processRound m (continueFromTo prover stmt wit k m.castSucc rk) :=
        funext (fun rk => continueFromTo_succ_of_ne prover stmt wit k m hne rk)
      rw [hcont, processRound_eq_bind m prover
            (runToRound k stmt wit prover >>= continueFromTo prover stmt wit k m.castSucc),
          bind_assoc]
      refine bind_congr (fun rk => ?_)
      rw [← processRound_eq_bind]

/-- **`processRound` only `snoc`s: the `castSucc`-prefix is preserved.**  Every support point of
`processRound j cur` has its round-`j.succ` transcript's `j.castSucc`-prefix equal to the
corresponding `j.castSucc`-prefix of its `cur`-predecessor.  The single-step geometric core of
`continueFromTo`'s prefix stability (both branches `snoc` a new entry onto the running transcript). -/
theorem take_castSucc_processRound (j : Fin n)
    (prover : Prover oSpec StmtIn WitIn StmtOut WitOut pSpec)
    (cur : OracleComp (oSpec + [pSpec.Challenge]ₒ)
      (pSpec.Transcript j.castSucc × prover.PrvState j.castSucc))
    (r : pSpec.Transcript j.succ × prover.PrvState j.succ)
    (hr : r ∈ support (prover.processRound j cur)) :
    ∃ rprev ∈ support cur,
      Fin.take j.castSucc.val (by simp) r.1 = rprev.1 := by
  unfold processRound at hr
  rw [mem_support_bind_iff] at hr
  obtain ⟨rprev, hprev, hr⟩ := hr
  refine ⟨rprev, hprev, ?_⟩
  obtain ⟨tprev, sprev⟩ := rprev
  simp only at hr ⊢
  -- Both round directions `snoc` a new entry onto `tprev`; the `j.castSucc`-prefix is unchanged.
  have hsnoc : ∃ msg : pSpec.«Type» j, r.1 = Transcript.concat msg tprev := by
    split at hr
    · rename_i hDir
      simp only [bind_pure_comp, mem_support_bind_iff, support_map, Set.mem_image] at hr
      obtain ⟨ch, _, ⟨st, _, hr⟩⟩ := hr
      exact ⟨ch, by rw [← hr]⟩
    · rename_i hDir
      simp only [bind_pure_comp, support_map, Set.mem_image] at hr
      obtain ⟨⟨msg, st⟩, _, hr⟩ := hr
      exact ⟨msg, by rw [← hr]⟩
  obtain ⟨msg, hmsg⟩ := hsnoc
  rw [hmsg]
  -- `Fin.take j.val (Fin.snoc tprev msg) = tprev` (taking below the appended entry).
  funext k
  have hkv : k.val < j.val := by have h := k.isLt; simp only [Fin.val_castSucc] at h; exact h
  simp only [Transcript.concat, Fin.take_apply, Fin.snoc, Fin.val_castLE]
  rw [dif_pos hkv]
  apply cast_eq_iff_heq.mpr
  congr 1

/-- **`continueFromTo` preserves the round-`k` transcript prefix.**  Any support point of
`continueFromTo k j rk` (with `k ≤ j`) has its round-`j` transcript's round-`k` prefix equal to the
start transcript `rk.1`: the continuation only appends later-round entries (`processRound` `snoc`s),
never altering the round-`k` prefix.  This is the geometric fact (paired with the monadic keystone
`runToRound_eq_bind_continueFromTo`) that lets the soundness game's full-run transcript prefix at
round `k = i.succ` be read off `runToRound i.succ`, feeding the round-by-round game. -/
theorem take_continueFromTo (prover : Prover oSpec StmtIn WitIn StmtOut WitOut pSpec)
    (stmt : StmtIn) (wit : WitIn) (k : Fin (n + 1)) :
    ∀ (j : Fin (n + 1)) (hkj : k ≤ j) (rk : pSpec.Transcript k × prover.PrvState k)
      (r : pSpec.Transcript j × prover.PrvState j),
      r ∈ support (continueFromTo prover stmt wit k j rk) →
        Fin.take k.val (by exact (Fin.val_le_of_le hkj)) r.1 = rk.1 := by
  intro j
  induction j using Fin.induction with
  | zero =>
      intro hkj rk r hr
      have hk0 : k = 0 := le_antisymm hkj (Fin.zero_le _)
      subst hk0
      rw [continueFromTo_self] at hr
      rw [mem_support_pure_iff] at hr
      subst hr
      -- `Fin.take 0` of any transcript is the (subsingleton) empty round-0 transcript.
      funext i; exact absurd i.isLt (by simp)
  | succ m ih =>
      intro hkj rk r hr
      rcases eq_or_lt_of_le hkj with heq | hlt
      · subst heq
        rw [continueFromTo_self, mem_support_pure_iff] at hr
        subst hr
        -- `Fin.take k.val` of the round-`k` transcript `rk.1` is `rk.1` itself.
        exact Fin.take_eq_self _
      · have hkm : k ≤ m.castSucc := by rw [Fin.le_castSucc_iff]; exact hlt
        have hne : (k : Fin (n + 1)) ≠ m.succ := ne_of_lt hlt
        rw [continueFromTo_succ_of_ne prover stmt wit k m hne rk] at hr
        obtain ⟨rprev, hprev, htake⟩ := take_castSucc_processRound m prover _ r hr
        have hih := ih hkm rk rprev hprev
        rw [← hih, ← htake]
        -- `take k (take m.castSucc v) = take k v` (nested takes collapse), position-wise.
        funext idx
        rw [Fin.take_apply, Fin.take_apply, Fin.take_apply]
        congr 1

-- FRONTIER NOTE (rbrSoundness → soundness, probability bridge; ArkLib#1).
--
-- KEYSTONE STATUS: the round-range decomposition `runToRound_eq_bind_continueFromTo` (and its
-- supporting `continueFromTo` / `continueFromTo_self` / `continueFromTo_succ_of_ne` /
-- `processRound_eq_bind`, all axiom-clean, directly above) is now PROVEN.  With `k := i.succ`,
-- `j := Fin.last n` it rewrites `Prover.run` / `Reduction.run` so the round-`i.succ` prefix is an
-- explicit `>>=`-prefix of the full run (verified).  The structural connective the spine below
-- called for is therefore in place; what remains is purely the probability-plumbing transport.
--
-- The remaining gap is the *per-round distributional marginal* relating the full prover run's
-- round-`i.succ` transcript prefix to the round-by-round game's `runToRound i.castSucc`-then-fresh-
-- challenge form.  An earlier attempt formulated this as a *computation equality*
--   `(fun x => Fin.take m x.1) <$> runToRound j = (fun x => x.1) <$> runToRound ⟨m,_⟩`  (for m ≤ j),
-- proved by induction peeling one `processRound` at a time.  That equality is FALSE: at a P_to_V
-- (message) round `processRound` runs `prover.sendMessage`, and at a V_to_P (challenge) round it
-- runs `prover.receiveChallenge`, both of which return an `OracleComp oSpec _` that *can fail*.
-- Taking the round-`m` transcript prefix (with `m ≤ j.val`) discards the newly appended entry — see
-- the (kept, correct) geometric lemma `fin_take_snoc_of_le` above — but the failure mass of those
-- trailing steps remains.  Hence only the *failure-monotone* `≤` direction holds, not `=`.
--
-- The correct statement is therefore a `probEvent` inequality, threaded through
-- `simulateQ (impl.addLift challengeQueryImpl) … |>.run' (← init)`:
--   Pr[ p (Fin.take i.succ.val tr) | full run ] ≤ Pr[ p | rbr game i ]
-- whose proof spine is:
--   (1) peel rounds `i.succ … last n` off `runToRound (last n)` as trailing binds whose outputs do
--       not affect the round-`i.succ` prefix (geometry: `fin_take_snoc_of_le`), then drop them via
--       the failure-monotone trailing-bind lemma
--       `Verifier.StateFunction.probEvent_bind_trailing_le` (in RoundByRound.lean) — each dropped
--       step can only raise the event probability;
--   (2) the verifier phase and `prover.output` of `Reduction.run` are likewise trailing binds whose
--       failure only raises the prefix-event probability (same lemma);
--   (3) `fst_map_runToRound_succ_challenge` (above) rewrites the surviving `runToRound i.succ`
--       prefix into the rbr game's `runToRound i.castSucc >>= getChallenge` shape (the trailing
--       `receiveChallenge` there is dropped by the same failure-monotone step).
-- All three steps must be transported across `simulateQ … |>.run'` and the `(← init)` bind; the
-- `impl`/`init` thread identically through both games, so they are carried as an opaque common
-- prefix.  The reusable ingredients now in place: `fin_take_snoc_of_le` (here),
-- `probEvent_bind_trailing_le`, `exists_challenge_flip_of_full`, `probEvent_le_sum_of_imp_exists`
-- (RoundByRound.lean).  The missing connective is the `simulateQ`/`run'`/`init`-transport of the
-- failure-monotone step, i.e. a `probEvent_simulateQ_run'_bind_trailing_le` analogue for an
-- *arbitrary* (not distribution-preserving) `impl`.
--
-- ASSEMBLY UPDATE (2026-06-04, obligation A).  The *support-implication* half of
-- `rbrSoundness_implies_soundness` (frontier obligation (A): an accepting soundness-game support
-- point flips the state function at some challenge round) was assembled down to a SINGLE residual
-- obligation, which exposed a genuine **state-threading mismatch in the theorem as stated** (for an
-- *arbitrary stateful* `impl`):
--   • `Reduction.support_run_verdict` (above) was proven (axiom-clean): an accepting soundness-game
--     support point `some x ∈ support ((simulateQ pImpl (reduction.run …).run).run' s)` has its
--     verifier verdict `x.2 ∈ support ((simulateQ impl (verifier.run … x.1.1)).run' s')` for the
--     POST-PROVER state `s'` (the simulation state *after* the prover has run from the init sample
--     `s ∈ support init`).
--   • `StateFunction.toFun_full`'s contrapositive yields `Pr[· ∈ langOut | OptionT.mk do
--     (simulateQ impl (verifier.run … x.1.1)).run' (← init)] = 0`, i.e. NO verifier verdict
--     reachable from a FRESH `init` sample is in `langOut`.
--   • Closing (A) therefore reduces *exactly* to `s' ∈ support init` — but `s'` is the
--     post-prover state, which is NOT in `support init` whenever the (malicious) prover queries the
--     shared oracle `oSpec` (handled by `impl`, which mutates the `σ` state).  Only the challenge
--     oracle (`challengeQueryImpl : QueryImpl _ ProbComp`) leaves `σ` untouched.
-- Consequently `rbrSoundness_implies_soundness` is unprovable as stated for an arbitrary stateful
-- `impl`: a prover that steers the oracle state to make the verifier accept a bad statement from a
-- non-`init`-reachable state breaks soundness while round-by-round soundness (whose `toFun_full` is
-- a fresh-`init` statement) still holds.  The theorem closes once either (i) `toFun_full` is
-- strengthened to quantify over all starting states, or (ii) `impl` is constrained so the prover
-- simulation preserves `support init` (e.g. `σ` a subsingleton / stateless `impl`, or a
-- distribution-preserving challenge-only `impl` — cf. `probEvent_simulateQ_run'_eq`).  This is a
-- STATEMENT-level finding, recorded for the orchestrator; it is NOT closable by further plumbing.
-- Obligation (B) (the per-round bound `Pr[p i | game] ≤ rbrSoundnessError i`) does NOT have this
-- gap: both the soundness game and the rbr game thread `init` through the prover identically, so the
-- failure-monotone keystone transport (the spine above) applies per shared state `s`.

end Prover

end Execution

variable {ι : Type} {oSpec : OracleSpec ι}
  {StmtIn : Type} {ιₛᵢ : Type} {OStmtIn : ιₛᵢ → Type} [Oₛᵢ : ∀ i, OracleInterface (OStmtIn i)]
  {WitIn : Type}
  {StmtOut : Type} {ιₛₒ : Type} {OStmtOut : ιₛₒ → Type} [Oₛₒ : ∀ i, OracleInterface (OStmtOut i)]
  {WitOut : Type}
  {n : ℕ} {pSpec : ProtocolSpec n} [Oₘ : ∀ i, OracleInterface (pSpec.Message i)]

section Trivial

/-- Running the identity or trivial reduction results in the same input statement and witness, and
  empty transcript. -/
@[simp]
theorem Reduction.id_run (stmt : StmtIn) (wit : WitIn) :
    (Reduction.id : Reduction oSpec StmtIn WitIn _ _ _).run stmt wit =
      pure ⟨⟨default, stmt, wit⟩, stmt⟩ := by
  simp [Reduction.run, Reduction.id, Prover.run, Verifier.run, Prover.id, Verifier.id]
  rfl

/-- Running the identity or trivial reduction, with logging of queries to the shared oracle,
  results in the same input statement and witness, empty transcript, and empty query logs. -/
@[simp]
theorem Reduction.id_runWithLog (stmt : StmtIn) (wit : WitIn) :
    (Reduction.id : Reduction oSpec StmtIn WitIn _ _ _).runWithLog stmt wit =
      pure ⟨⟨⟨default, stmt, wit⟩, stmt⟩, [], []⟩ := by
  simp_all only [ChallengeIdx, Challenge]
  rfl

/-- Running the identity or trivial oracle reduction results in the same input statement, oracle
  statement, and witness. -/
@[simp]
theorem OracleReduction.id_run (stmt : StmtIn) (oStmt : ∀ i, OStmtIn i) (wit : WitIn) :
    (OracleReduction.id : OracleReduction oSpec StmtIn OStmtIn WitIn _ _ _ _).run stmt oStmt wit =
      pure ⟨⟨default, ⟨stmt, oStmt⟩, wit⟩, ⟨stmt, oStmt⟩⟩ := by
  simp_all only [ChallengeIdx, Challenge, run_eq_run_reduction, id_toReduction, Reduction.id_run]

/-- Running the identity or trivial oracle reduction results in the same input statement, oracle
  statement, and witness. -/
@[simp]
theorem OracleReduction.id_runWithLog (stmt : StmtIn) (oStmt : ∀ i, OStmtIn i) (wit : WitIn) :
    (OracleReduction.id : OracleReduction oSpec StmtIn OStmtIn WitIn _ _ _ _).runWithLog
      stmt oStmt wit = pure ⟨⟨default, ⟨stmt, oStmt⟩, wit⟩, ⟨stmt, oStmt⟩, [], []⟩ := by
  simp only [OracleReduction.runWithLog, OracleVerifier.run, Prover.run, OracleReduction.id,
    OracleProver.id, OracleVerifier.id, Prover.id,
    Prover.runToRound,
    monadLift_pure, pure_bind, Option.getM]
  rfl

end Trivial

section SingleMessage

/-! Simplification lemmas for protocols with a single message -/

variable {pSpec : ProtocolSpec 1}

@[simp]
theorem Prover.runToRound_one_of_prover_first [ProverOnly pSpec] (stmt : StmtIn) (wit : WitIn)
    (prover : Prover oSpec StmtIn WitIn StmtOut WitOut pSpec) :
      prover.runToRound 1 stmt wit = (do
        let state := prover.input (stmt, wit)
        let ⟨msg, state⟩ ← liftComp (prover.sendMessage ⟨0, by simp⟩ state) _
        return (fun i => match i with | ⟨0, _⟩ => msg, state)) := by
  simp [Prover.runToRound, Prover.processRound]
  have : pSpec.dir 0 = .P_to_V := by simp
  split <;> rename_i hDir
  · have : Direction.P_to_V = .V_to_P := by rw [← this, hDir]
    contradiction
  · congr; funext a; congr; simp [default, Transcript.concat]; funext i
    have : i = 0 := by aesop
    rw [this]; simp [Fin.snoc]

@[simp]
theorem Prover.runToRound_one_of_verifier_first [VerifierOnly pSpec] (stmt : StmtIn) (wit : WitIn)
    (prover : Prover oSpec StmtIn WitIn StmtOut WitOut pSpec) :
      prover.runToRound 1 stmt wit = (do
        let state := prover.input (stmt, wit)
        let challenge ← liftComp (pSpec.getChallenge ⟨0, by simp⟩) _
        letI newState := (← liftComp (prover.receiveChallenge ⟨0, by simp⟩ state) _) challenge
        return (fun i => match i with | ⟨0, _⟩ => challenge, newState)) := by
  simp [Prover.runToRound, Prover.processRound]
  have : pSpec.dir 0 = .V_to_P := by simp
  split <;> rename_i hDir
  · -- V_to_P case: this is what we want
    congr 1
    funext challenge
    congr 1
    funext f
    simp only [default, Transcript.concat, Prod.mk.injEq]
    constructor
    · funext ⟨i, hi⟩
      have h : i = 0 := by omega
      subst h
      simp [Fin.snoc]
    · trivial
  · -- P_to_V case: contradiction
    have : Direction.V_to_P = .P_to_V := by rw [← this, hDir]
    contradiction

@[simp]
theorem Prover.run_of_verifier_first [VerifierOnly pSpec] (stmt : StmtIn) (wit : WitIn)
    (prover : Prover oSpec StmtIn WitIn StmtOut WitOut pSpec) :
      prover.run stmt wit = (do
        let state := prover.input (stmt, wit)
        let challenge ← liftComp (pSpec.getChallenge ⟨0, by simp⟩) _
        let f ← liftComp (prover.receiveChallenge ⟨0, by simp⟩ state) _
        let ctxOut ← prover.output (f challenge)
        return ((fun i => match i with | ⟨0, _⟩ => challenge), ctxOut)) := by
  simp [Prover.run]; rfl

@[simp]
theorem Prover.run_of_prover_first [ProverOnly pSpec] (stmt : StmtIn) (wit : WitIn)
    (prover : Prover oSpec StmtIn WitIn StmtOut WitOut pSpec) :
      prover.run stmt wit = (do
        let state := prover.input (stmt, wit)
        let ⟨msg, state⟩ ← liftComp (prover.sendMessage ⟨0, by simp⟩ state) _
        let ctxOut ← prover.output state
        return ((fun i => match i with | ⟨0, _⟩ => msg), ctxOut)) := by
  simp [Prover.run]; rfl

-- @[simp]
theorem Reduction.run_of_prover_first [ProverOnly pSpec] (stmt : StmtIn) (wit : WitIn)
    (reduction : Reduction oSpec StmtIn WitIn StmtOut WitOut pSpec) :
      reduction.run stmt wit = (do
        let state := reduction.prover.input (stmt, wit)
        let ⟨msg, state⟩ ← (reduction.prover.sendMessage ⟨0, by simp⟩ state)
        let ctxOut ← reduction.prover.output state
        let transcript : pSpec.FullTranscript := fun i => match i with | ⟨0, _⟩ => msg
        let stmtOut ← (reduction.verifier.verify stmt transcript).run
        return (⟨transcript, ctxOut⟩, ← stmtOut.getM)) := by
  simp only [Reduction.run, Verifier.run]
  rw [Prover.run_of_prover_first]
  simp only [liftComp_eq_liftM, bind_assoc, pure_bind, monadLift_bind, monadLift_pure,
    monadLift_liftM_OptionT]

end SingleMessage

section Classes

variable {ι : Type} {oSpec : OracleSpec ι}
    {StmtIn WitIn StmtOut WitOut : Type}
    {pSpec : ProtocolSpec 2}

-- /-- Simplification of the prover's execution in a single-round, two-message protocol where the
--   prover speaks first -/
-- theorem Prover.run_of_isSingleRound [IsSingleRound pSpec] (stmt : StmtIn) (wit : WitIn)
--     (prover : Prover pSpec oSpec StmtIn WitIn StmtOut WitOut) :
--       prover.run stmt wit = (do
--         let state ← liftComp (prover.load stmt wit)
--         let ⟨⟨msg, state⟩, queryLog⟩ ← liftComp
--           (simulate loggingOracle ∅ (prover.sendMessage default state emptyTranscript))
--         let challenge ← query (Sum.inr default) ()
--         let state ← liftComp (prover.receiveChallenge default state transcript challenge)
--         let transcript := Transcript.mk2 msg challenge
--         let witOut := prover.output state
--         return (transcript, queryLog, witOut)) := by
--   simp [Prover.run, Prover.runToRound, Fin.reduceFinMk, Fin.val_two,
--     Fin.val_zero, Fin.coe_castSucc, Fin.val_succ, dir_apply, bind_pure_comp, getType_apply,
--     Fin.induction_two, Fin.val_one, pure_bind, map_bind, liftComp]
--   split <;> rename_i hDir0
--   · exfalso; simp only [prover_first, reduceCtorEq] at hDir0
--   split <;> rename_i hDir1
--   swap
--   · exfalso; simp only [verifier_last_of_two, reduceCtorEq] at hDir1
--   simp only [Functor.map_map, bind_map_left, default]
--   congr; funext x; congr; funext y;
--   simp only [Fin.isValue, map_bind, Functor.map_map, dir_apply, Fin.succ_one_eq_two,
--     Fin.succ_zero_eq_one, queryBind_inj', true_and, exists_const]
--   funext chal; simp [OracleSpec.append] at chal
--   congr; funext state; congr
--   rw [← Transcript.mk2_eq_toFull_snoc_snoc _ _]

-- theorem Reduction.run_of_isSingleRound [IsSingleRound pSpec]
--     (reduction : Reduction pSpec oSpec StmtIn WitIn StmtOut WitOut PrvState)
--     (stmt : StmtIn) (wit : WitIn) :
--       reduction.run stmt wit = do
end Classes

/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.OracleReduction.Execution
import ArkLib.OracleReduction.Security.Basic
import ArkLib.ToMathlib.OracleCompEvalDistBindComm

/-!
# Unrolled-run form of a reduction, and the ε-completeness characterization

`Reduction.run` is, by construction, "run the prover, then run the verifier". This file exposes the
*unrolled* form — run the prover round-by-round to the last round (`Prover.runToRound (Fin.last n)`),
extract the prover output, then run the verifier — as a plain monadic equality
(`Reduction.run_eq_unrolled`), and rewrites the (general, error-`ε`) completeness predicate through
it (`Reduction.completeness_iff_run_unrolled`).

This is the **`ε`-analogue** of the perfect-completeness unrolling
`unroll_n_message_reduction_perfectCompleteness` (`OracleReduction/Completeness.lean`): the perfect
version converts `Pr[…] = 1` into a *support*-level pure-logic statement (using `NeverFail` + the
implementation support condition), which is only valid at error `0`. The version here keeps the
`simulateQ`/`init` layer intact and merely exposes the round-by-round prover structure, so it applies
at any error `ε` — the form needed to then compute a protocol-specific acceptance probability (e.g.
the LogUp outer-phase pole-rejection bound) without first collapsing to `Pr = 1`.
-/

open OracleComp OracleSpec ProtocolSpec
open scoped NNReal ENNReal

namespace Reduction

variable {ι : Type} {oSpec : OracleSpec ι} {StmtIn WitIn StmtOut WitOut : Type}
  {n : ℕ} {pSpec : ProtocolSpec n} [∀ i, SampleableType (pSpec.Challenge i)]
  {σ : Type}

omit [∀ i, SampleableType (pSpec.Challenge i)] in
/-- **Unrolled form of `Reduction.run`.** Running a reduction equals: run the prover round-by-round
to the last round (`runToRound (Fin.last n)`), `liftComp` the prover's output extraction, run the
verifier on the produced transcript, and pair the prover output with the verifier's (extracted)
output statement. A plain monadic equality, independent of any probability assumptions. -/
theorem run_eq_unrolled (reduction : Reduction oSpec StmtIn WitIn StmtOut WitOut pSpec)
    (stmt : StmtIn) (wit : WitIn) :
    reduction.run stmt wit
      = (do
          let ⟨tr, st⟩ ← reduction.prover.runToRound (Fin.last n) stmt wit
          let out ← liftComp (reduction.prover.output st) (oSpec + [pSpec.Challenge]ₒ)
          let vStmt ← liftM (reduction.verifier.run stmt tr).run
          return ((tr, out), ← vStmt.getM)) := by
  unfold Reduction.run Prover.run
  simp only [bind_assoc, liftM_bind, bind_pure_comp, OracleComp.liftComp_eq_liftM,
    liftM_map, bind_map_left]

/-- **`ε`-completeness via the unrolled run.** The general (error-`ε`) completeness predicate of a
reduction is equivalent to the same acceptance-probability bound stated over the *unrolled* run
(prover-to-last-round, output, verifier). Obtained by rewriting `Reduction.run` through
`run_eq_unrolled` inside `completenessFromRun`; the `simulateQ`/`init` execution layer is preserved,
so this holds at every error `ε` (unlike the perfect-only support-collapsing unroll). -/
theorem completeness_iff_run_unrolled
    (init : ProbComp σ) (impl : QueryImpl oSpec (StateT σ ProbComp))
    (relIn : Set (StmtIn × WitIn)) (relOut : Set (StmtOut × WitOut))
    (reduction : Reduction oSpec StmtIn WitIn StmtOut WitOut pSpec)
    (completenessError : ℝ≥0) :
    reduction.completeness init impl relIn relOut completenessError ↔
      completenessFromRun init (QueryImpl.addLift impl challengeQueryImpl) relIn relOut
        (fun stmtIn witIn => (do
          let ⟨tr, st⟩ ← reduction.prover.runToRound (Fin.last n) stmtIn witIn
          let out ← liftComp (reduction.prover.output st) (oSpec + [pSpec.Challenge]ₒ)
          let vStmt ← liftM (reduction.verifier.run stmtIn tr).run
          return ((tr, out), ← vStmt.getM) :
            OptionT (OracleComp (oSpec + [pSpec.Challenge]ₒ))
              ((FullTranscript pSpec × StmtOut × WitOut) × StmtOut)))
        completenessError := by
  unfold Reduction.completeness
  simp only [run_eq_unrolled]

#print axioms run_eq_unrolled
#print axioms completeness_iff_run_unrolled

end Reduction

/-! ## Challenge-coherence for the standard interactive challenge oracle

The honest interactive execution answers the verifier's `getChallenge` queries with fresh uniform
samples (`challengeQueryImpl`), routed through `QueryImpl.addLift impl challengeQueryImpl` together
with the shared-oracle implementation `impl`. The two lemmas below push that challenge sampling out
of `simulateQ … |>.run'`, exposing the challenge as a `uniformSample`. This is the reusable
"FS-class" coherence step that downstream completeness/soundness probability computations need (e.g.
the LogUp outer-phase pole event depends only on the sampled challenge `x`). -/

namespace ChallengeCoherence

variable {ι : Type} {oSpec : OracleSpec ι} {n : ℕ} {pSpec : ProtocolSpec n}
  [∀ i, SampleableType (pSpec.Challenge i)] {σ β : Type}

/-- Simulating a single (lifted) `getChallenge i` under `QueryImpl.addLift impl challengeQueryImpl`
collapses to the lifted uniform sampler `liftM ($ᵗ pSpec.Challenge i)`: the challenge oracle ignores
the shared-oracle implementation and samples uniformly. -/
theorem simulateQ_addLift_getChallenge
    (impl : QueryImpl oSpec (StateT σ ProbComp))
    (i : pSpec.ChallengeIdx) :
    (simulateQ (QueryImpl.addLift impl challengeQueryImpl :
        QueryImpl (oSpec + [pSpec.Challenge]ₒ) (StateT σ ProbComp))
        (liftM (getChallenge pSpec i) :
          OracleComp (oSpec + [pSpec.Challenge]ₒ) (pSpec.Challenge i)))
      = (liftM ($ᵗ pSpec.Challenge i) : StateT σ ProbComp (pSpec.Challenge i)) := by
  rw [← OracleComp.liftComp_eq_liftM (mx := getChallenge pSpec i), QueryImpl.addLift]
  rw [QueryImpl.simulateQ_liftComp_right_eq_of_apply
        (QueryImpl.liftTarget (StateT σ ProbComp) impl
          + QueryImpl.liftTarget (StateT σ ProbComp) challengeQueryImpl)
        (QueryImpl.liftTarget (StateT σ ProbComp) challengeQueryImpl)
        (fun t => by rw [QueryImpl.add_apply_inr])]
  show simulateQ (QueryImpl.liftTarget (StateT σ ProbComp) challengeQueryImpl)
      (liftM (([pSpec.Challenge]ₒ).query ⟨i, ()⟩)) = _
  rw [simulateQ_spec_query, QueryImpl.liftTarget_apply]
  rfl

/-- **Challenge-coherence bind-exposure brick.** Running, under `simulateQ (addLift impl
challengeQueryImpl)` with state `s`, a `getChallenge`-then-`k` computation equals: sample the
challenge uniformly, then run `k` from the *same* state `s`. (The challenge oracle samples uniformly
and leaves the `σ`-state untouched.) This exposes the verifier's fresh challenge as a
`uniformSample` for probability computations — the reusable FS-class coherence step. -/
theorem run'_simulateQ_addLift_getChallenge_bind
    (impl : QueryImpl oSpec (StateT σ ProbComp)) (s : σ)
    (i : pSpec.ChallengeIdx)
    (k : pSpec.Challenge i → OracleComp (oSpec + [pSpec.Challenge]ₒ) β) :
    (simulateQ (QueryImpl.addLift impl challengeQueryImpl :
        QueryImpl (oSpec + [pSpec.Challenge]ₒ) (StateT σ ProbComp))
        ((liftM (getChallenge pSpec i) :
            OracleComp (oSpec + [pSpec.Challenge]ₒ) (pSpec.Challenge i)) >>= k)).run' s
      = ($ᵗ pSpec.Challenge i) >>= fun c =>
          (simulateQ (QueryImpl.addLift impl challengeQueryImpl :
            QueryImpl (oSpec + [pSpec.Challenge]ₒ) (StateT σ ProbComp)) (k c)).run' s := by
  rw [simulateQ_bind, simulateQ_addLift_getChallenge]
  rw [StateT.run'_eq, StateT.run_bind, StateT.run_monadLift]
  simp only [bind_assoc, pure_bind, map_bind, StateT.run'_eq, monadLift_self]

/-- Probability form of the challenge-coherence brick: the event probability of a
`getChallenge`-then-`k` run equals the uniform average over the challenge of `k`'s event
probability. This is the form a protocol-specific completeness bound consumes when its acceptance
event depends on a verifier challenge (e.g. the LogUp outer pole event in the sampled `x`). -/
theorem probEvent_run'_simulateQ_addLift_getChallenge_bind
    (impl : QueryImpl oSpec (StateT σ ProbComp)) (s : σ)
    (i : pSpec.ChallengeIdx)
    (k : pSpec.Challenge i → OracleComp (oSpec + [pSpec.Challenge]ₒ) β)
    (p : β → Prop) :
    Pr[p | (simulateQ (QueryImpl.addLift impl challengeQueryImpl :
        QueryImpl (oSpec + [pSpec.Challenge]ₒ) (StateT σ ProbComp))
        ((liftM (getChallenge pSpec i) :
            OracleComp (oSpec + [pSpec.Challenge]ₒ) (pSpec.Challenge i)) >>= k)).run' s]
      = ∑' c : pSpec.Challenge i,
          Pr[= c | ($ᵗ pSpec.Challenge i)] *
            Pr[p | (simulateQ (QueryImpl.addLift impl challengeQueryImpl :
              QueryImpl (oSpec + [pSpec.Challenge]ₒ) (StateT σ ProbComp)) (k c)).run' s] := by
  rw [run'_simulateQ_addLift_getChallenge_bind, probEvent_bind_eq_tsum]

#print axioms simulateQ_addLift_getChallenge
#print axioms run'_simulateQ_addLift_getChallenge_bind
#print axioms probEvent_run'_simulateQ_addLift_getChallenge_bind

end ChallengeCoherence

/-! ## `StateT`-valued `OptionT`-bind distribution under `simulateQ`

The codebase has `OptionT.simulateQ_{bind,pure,map,…}` for *`OracleComp`-valued* implementations, but
the interactive-execution semantics (`Reduction.completeness`) simulate with `QueryImpl.addLift impl
challengeQueryImpl`, whose target is `StateT σ ProbComp`. The lemma below is the missing `StateT`-valued
analogue of `OptionT.simulateQ_bind`: it distributes `simulateQ so` over the `OptionT.run` of a bind,
threading the simulation state across the seam. It is the coherence step that lets a completeness run
of the form `mx >>= my` (prover sample → verifier check) be analyzed stage-by-stage at the `run`-level. -/

namespace OptionTStateT

variable {ι : Type} {spec : OracleSpec ι} {σ α β : Type}

/-- **`StateT`-valued `OptionT`-bind distribution under `simulateQ`.** Running `simulateQ so` (for a
`StateT σ ProbComp`-valued `so`) over `(mx >>= my).run` distributes: run the first stage threading
the state, then `Option.elim` into the second stage from the threaded state (or short-circuit to
`none`). -/
theorem simulateQ_run_optionT_bind_run
    (so : QueryImpl spec (StateT σ ProbComp))
    (mx : OptionT (OracleComp spec) α) (my : α → OptionT (OracleComp spec) β) (s : σ) :
    (simulateQ so ((mx >>= my : OptionT (OracleComp spec) β)).run).run s
      = (simulateQ so mx.run).run s >>= fun p =>
          p.1.elim (pure (none, p.2)) (fun a => (simulateQ so (my a).run).run p.2) := by
  have hrun : ((mx >>= my : OptionT (OracleComp spec) β)).run
      = mx.run >>= fun o => match o with | some a => (my a).run | none => pure none := rfl
  rw [hrun, simulateQ_bind, StateT.run_bind]
  refine bind_congr fun p => ?_
  obtain ⟨o, s'⟩ := p
  cases o with
  | none => simp [simulateQ_pure, StateT.run_pure]
  | some a => rfl

#print axioms simulateQ_run_optionT_bind_run

/-- `run'`-level analogue of `simulateQ_run_optionT_bind_run`: distributing `simulateQ so` over the
`OptionT.run` of a bind, dropping the final state (`run'`). Directly matches the soundness/completeness
game shape `(simulateQ so X.run).run' s` (used to split such a game into its two stages for a
`probEvent`/`probFailure` union bound). -/
theorem simulateQ_run'_optionT_bind_run
    (so : QueryImpl spec (StateT σ ProbComp))
    (mx : OptionT (OracleComp spec) α) (my : α → OptionT (OracleComp spec) β) (s : σ) :
    (simulateQ so ((mx >>= my : OptionT (OracleComp spec) β)).run).run' s
      = (simulateQ so mx.run).run s >>= fun p =>
          p.1.elim (pure none) (fun a => (simulateQ so (my a).run).run' p.2) := by
  rw [StateT.run'_eq, simulateQ_run_optionT_bind_run, map_bind]
  refine bind_congr fun p => ?_
  obtain ⟨o, s'⟩ := p
  cases o with
  | none => simp [StateT.run'_eq]
  | some a => simp only [Option.elim_some, StateT.run'_eq]

#print axioms simulateQ_run'_optionT_bind_run

open scoped ENNReal in
/-- **Two-stage seam union bound (`ProbComp` level).** The core union bound for sequential-composition
soundness/completeness. For the game `init >>= fun s => (simulateQ so (mx >>= my).run).run' s`: if the
stage-1 bad event (`¬ Option.elim ·.1 True pg`) on the state-threaded stage-1 run is bounded by `e₁`,
and for every stage-1 success `(some a, s')` with `pg a` the stage-2 bad event (`¬ Option.elim · True qg`)
of `my a` run from `s'` is bounded by `e₂`, then the full game's stage-2 bad event is bounded by
`e₁ + e₂`. Combines `simulateQ_run'_optionT_bind_run` (stage split) with `probEvent_bind_le_add`.
Predicates are in `¬ Option.elim · True ·` (bad-event) form; `none` (failure) is never "bad". -/
theorem probComp_seam_union_le
    (init : ProbComp σ) (so : QueryImpl spec (StateT σ ProbComp))
    (mx : OptionT (OracleComp spec) α) (my : α → OptionT (OracleComp spec) β)
    (pg : α → Prop) (qg : β → Prop) (e₁ e₂ : ℝ≥0∞)
    (h₁ : Pr[fun r => ¬ Option.elim r.1 True pg
          | init >>= fun s => (simulateQ so mx.run).run s] ≤ e₁)
    (h₂ : ∀ a s', (some a, s') ∈ support (init >>= fun s => (simulateQ so mx.run).run s) → pg a →
          Pr[fun o => ¬ Option.elim o True qg
            | (simulateQ so (my a).run).run' s'] ≤ e₂) :
    Pr[fun o => ¬ Option.elim o True qg
        | init >>= fun s => (simulateQ so (mx >>= my).run).run' s] ≤ e₁ + e₂ := by
  classical
  have hgame : (init >>= fun s => (simulateQ so ((mx >>= my).run)).run' s)
      = (init >>= fun s => (simulateQ so mx.run).run s) >>= fun r =>
          r.1.elim (pure none) (fun a => (simulateQ so (my a).run).run' r.2) := by
    rw [bind_assoc]
    refine bind_congr fun s => ?_
    rw [simulateQ_run'_optionT_bind_run]
  rw [hgame]
  refine probEvent_bind_le_add
    (mx := init >>= fun s => (simulateQ so mx.run).run s)
    (p := fun (r : Option α × σ) => Option.elim r.1 True pg)
    (q := fun (o : Option β) => Option.elim o True qg) h₁ ?_
  rintro ⟨o, s'⟩ hmem hp
  cases o with
  | none => simp [probEvent_pure]
  | some a => exact h₂ a s' hmem hp

#print axioms probComp_seam_union_le

/-- **`simulateQ` preserves the `σ`-state on its support, when every query implementation does.**
Holds for `challengeQueryImpl` (which threads `σ` unchanged) and for empty `oSpec`. This is the
independence ingredient for the seam swap: a state-preserving prover stage cannot affect a later
verifier stage's `simulateQ` state, so the two stages commute distributionally
(`OracleComp.evalDist_bind_comm`). -/
theorem simulateQ_state_preserving
    (so : QueryImpl spec (StateT σ ProbComp))
    (hso : ∀ (t : spec.Domain) (s : σ) (x : spec.Range t × σ),
      x ∈ support ((so t).run s) → x.2 = s)
    {α : Type} (X : OracleComp spec α) (s : σ) :
    ∀ x ∈ support ((simulateQ so X).run s), x.2 = s := by
  induction X using OracleComp.inductionOn generalizing s with
  | pure a =>
    intro x hx
    simp only [simulateQ_pure, StateT.run_pure, support_pure, Set.mem_singleton_iff] at hx
    subst hx; rfl
  | query_bind t oa ih =>
    intro x hx
    simp only [simulateQ_bind, simulateQ_query, OracleQuery.input_query, OracleQuery.cont_query,
      id_map, StateT.run_bind, support_bind, Set.mem_iUnion] at hx
    obtain ⟨⟨u, s'⟩, hmem1, hmem2⟩ := hx
    have hs' : s' = s := hso t s ⟨u, s'⟩ hmem1
    exact hs' ▸ ih u s' x hmem2

#print axioms simulateQ_state_preserving

/-- **State-fixing for a simulated bind.** When the implementation preserves `σ`, the continuation of
a simulated bind runs from the *same* state `s` (not a threaded one), since the first stage leaves `σ`
unchanged. This is the step that makes the seam stages commute: after fixing all states to `s`, the
value-binds can be reordered by `bind_comm`/`evalDist_bind_comm`. -/
theorem simulateQ_run_bind_state_fixed
    (so : QueryImpl spec (StateT σ ProbComp))
    (hso : ∀ (t : spec.Domain) (s : σ) (x : spec.Range t × σ),
      x ∈ support ((so t).run s) → x.2 = s)
    {α β : Type} (A : OracleComp spec α) (g : α → OracleComp spec β) (s : σ) :
    (simulateQ so (A >>= g)).run s
      = (simulateQ so A).run s >>= fun p => (simulateQ so (g p.1)).run s := by
  rw [simulateQ_bind, StateT.run_bind]
  refine OracleComp.bind_congr_of_forall_mem_support _ (fun p hp => ?_)
  obtain ⟨a, s'⟩ := p
  rw [show s' = s from simulateQ_state_preserving so hso A s ⟨a, s'⟩ hp]

#print axioms simulateQ_run_bind_state_fixed

/-- **Seam stage swap.** Under state-preservation, two simulated stages `A`, `B` commute
distributionally: `simulateQ so (A >>= fun a => B >>= fun b => k a b)` has the same `run'`-distribution
as the `B`-then-`A` order. State-fixing (`simulateQ_run_bind_state_fixed`) makes all stages run from the
same `s`, then `SPMF.bind_comm` (unconditional) reorders. This is the `V₁↔snd` reorder used to apply
`probComp_seam_union_le` with stages matching `V₁`/`V₂` soundness for `appendSoundness`. -/
theorem evalDist_simulateQ_swap
    (so : QueryImpl spec (StateT σ ProbComp))
    (hso : ∀ (t : spec.Domain) (s : σ) (x : spec.Range t × σ),
      x ∈ support ((so t).run s) → x.2 = s)
    {α β γ : Type}
    (A : OracleComp spec α) (B : OracleComp spec β) (k : α → β → OracleComp spec γ) (s : σ) :
    evalDist ((simulateQ so (A >>= fun a => B >>= fun b => k a b)).run' s)
      = evalDist ((simulateQ so (B >>= fun b => A >>= fun a => k a b)).run' s) := by
  rw [StateT.run'_eq, StateT.run'_eq, evalDist_map, evalDist_map]
  congr 1
  simp only [simulateQ_run_bind_state_fixed so hso, evalDist_bind]
  exact SPMF.bind_comm _ _ _

#print axioms evalDist_simulateQ_swap

/-- **Elim-stage commute (bad-event level).** A never-failing plain stage `B` may be moved across an
`Option`-elim short-circuit without changing the probability of a `none`-false event `badpred`: running
`B` before the elim (always) vs inside the `some`-branch (only on success) agree on `badpred`, since the
`none` branch outputs `none` either way (where `badpred` is false). Bridges the full-evalDist stage swap
(`evalDist_simulateQ_swap`) to `probComp_seam_union_le`'s short-circuiting `mx >>= my` for
`appendSoundness`. -/
theorem probEvent_elim_comm {α γ β : Type}
    (mO : ProbComp (Option α)) (B : ProbComp γ)
    (C : α → γ → ProbComp (Option β)) (badpred : Option β → Prop) (hnone : ¬ badpred none) :
    Pr[badpred | mO >>= fun o => B >>= fun b => o.elim (pure none) (fun a => C a b)]
      = Pr[badpred | mO >>= fun o => o.elim (pure none) (fun a => B >>= fun b => C a b)] := by
  classical
  rw [probEvent_bind_eq_tsum, probEvent_bind_eq_tsum]
  refine tsum_congr fun o => ?_
  congr 1
  cases o with
  | none =>
    simp only [Option.elim_none]
    rw [probEvent_bind_eq_tsum]
    simp [probEvent_pure, hnone]
  | some a =>
    simp only [Option.elim_some]

#print axioms probEvent_elim_comm

/-- **Value-state-independence of a simulated run.** If every query implementation both preserves the
state (`hso`) and produces a value-distribution independent of the input state (`hvb`), then the whole
simulated computation's value-distribution (`run'`) is independent of the starting state. Holds for
`challengeQueryImpl` (uniform sample, `σ` untouched) and empty `oSpec`. Lets `probComp_seam_union_le`'s
per-threaded-state `h₂` be discharged by the verifier's (state-averaged) soundness, since every threaded
state gives the same value-distribution. -/
theorem evalDist_simulateQ_run'_state_indep
    (so : QueryImpl spec (StateT σ ProbComp))
    (hso : ∀ (t : spec.Domain) (s : σ) (x : spec.Range t × σ),
      x ∈ support ((so t).run s) → x.2 = s)
    (hvb : ∀ (t : spec.Domain) (s s' : σ),
      evalDist ((so t).run' s) = evalDist ((so t).run' s'))
    {α : Type} (X : OracleComp spec α) (s s' : σ) :
    evalDist ((simulateQ so X).run' s) = evalDist ((simulateQ so X).run' s') := by
  induction X using OracleComp.inductionOn generalizing s s' with
  | pure a => simp [simulateQ_pure, StateT.run'_eq, StateT.run_pure]
  | query_bind t oa ih =>
    have hq : ∀ r : σ, (simulateQ so (liftM (OracleSpec.query t))).run r = (so t).run r := by
      intro r; simp only [simulateQ_query, OracleQuery.input_query, OracleQuery.cont_query, id_map]
    have key : ∀ r : σ,
        evalDist ((simulateQ so (liftM (OracleSpec.query t) >>= oa)).run' r)
        = (evalDist ((so t).run' r)) >>= fun a => evalDist ((simulateQ so (oa a)).run' r) := by
      intro r
      rw [StateT.run'_eq, simulateQ_run_bind_state_fixed so hso (liftM (OracleSpec.query t)) oa r,
        hq r, map_bind, evalDist_bind,
        show (evalDist ((so t).run' r)) = (fun x => x.1) <$> evalDist ((so t).run r) from by
          rw [StateT.run'_eq, evalDist_map],
        bind_map_left]
      refine bind_congr fun p => ?_
      rw [StateT.run'_eq]
    rw [key s, key s', hvb t s s']
    refine bind_congr fun a => ?_
    rw [ih a s s']

#print axioms evalDist_simulateQ_run'_state_indep

section AddLiftBridges
open ProtocolSpec
variable {ι : Type} {oSpec : OracleSpec ι} {σ : Type} {n : ℕ} {pSpec : ProtocolSpec n}
  [∀ i, SampleableType (pSpec.Challenge i)]

/-- **`addLift impl challengeQueryImpl` is state-preserving when `impl` is.** The challenge half is a
`liftM` of a `ProbComp` (state untouched: `(liftM mx).run s = (·, s) <$> mx`); the `oSpec` half is `impl`
(state-preserving by hypothesis; vacuous when `oSpec = []ₒ`). Discharges the `hso` side-condition of the
seam toolkit for the actual soundness/completeness implementation `impl.addLift challengeQueryImpl`. -/
theorem addLift_state_preserving (impl : QueryImpl oSpec (StateT σ ProbComp))
    (himpl : ∀ (t : oSpec.Domain) (s : σ) (x : oSpec.Range t × σ),
      x ∈ support ((impl t).run s) → x.2 = s) :
    ∀ (t : (oSpec + [pSpec.Challenge]ₒ).Domain) (s : σ) (x : _ × σ),
      x ∈ support (((impl.addLift challengeQueryImpl :
        QueryImpl (oSpec + [pSpec.Challenge]ₒ) (StateT σ ProbComp)) t).run s) → x.2 = s := by
  rintro (t | t) s x hx
  · simp only [QueryImpl.addLift_def, QueryImpl.add_apply_inl, QueryImpl.liftTarget_apply,
      monadLift_self] at hx
    exact himpl t s x hx
  · simp only [QueryImpl.addLift_def, QueryImpl.add_apply_inr, QueryImpl.liftTarget_apply] at hx
    change x ∈ support ((fun a => (a, s)) <$> challengeQueryImpl t) at hx
    simp only [support_map, Set.mem_image] at hx
    obtain ⟨a, _, rfl⟩ := hx; rfl

/-- **`addLift impl challengeQueryImpl` is value-state-blind when `impl` is.** Discharges `hvb`. -/
theorem addLift_value_blind (impl : QueryImpl oSpec (StateT σ ProbComp))
    (himpl : ∀ (t : oSpec.Domain) (s s' : σ),
      evalDist ((impl t).run' s) = evalDist ((impl t).run' s')) :
    ∀ (t : (oSpec + [pSpec.Challenge]ₒ).Domain) (s s' : σ),
      evalDist (((impl.addLift challengeQueryImpl :
        QueryImpl (oSpec + [pSpec.Challenge]ₒ) (StateT σ ProbComp)) t).run' s)
        = evalDist (((impl.addLift challengeQueryImpl :
        QueryImpl (oSpec + [pSpec.Challenge]ₒ) (StateT σ ProbComp)) t).run' s') := by
  rintro (t | t) s s'
  · simp only [QueryImpl.addLift_def, QueryImpl.add_apply_inl, QueryImpl.liftTarget_apply,
      monadLift_self]
    exact himpl t s s'
  · have h : ∀ r : σ, evalDist (((impl.addLift challengeQueryImpl :
        QueryImpl (oSpec + [pSpec.Challenge]ₒ) (StateT σ ProbComp)) (Sum.inr t)).run' r)
        = evalDist (challengeQueryImpl t) := by
      intro r
      simp only [QueryImpl.addLift_def, QueryImpl.add_apply_inr, QueryImpl.liftTarget_apply]
      change evalDist ((fun a => a.1) <$> ((fun a => (a, r)) <$> challengeQueryImpl t)) = _
      simp [Functor.map_map]
    rw [h s, h s']

end AddLiftBridges

end OptionTStateT

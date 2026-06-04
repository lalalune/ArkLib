/-
Copyright (c) 2024-2025 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

import ArkLib.OracleReduction.LiftContext.Lens
import ArkLib.OracleReduction.Security.RoundByRound
import ArkLib.ToVCVio.EvalDist.Instances.OptionT
import ArkLib.ToVCVio.OracleComp.Coercions.SubSpec
-- import ArkLib.OracleReduction.Security.StateRestoration

/-!
  ## Lifting Reductions to Larger Contexts

  Sequential composition is usually not enough to represent oracle reductions in a modular way. We
  also need to formalize **virtual** oracle reductions, which lift reductions from one (virtual /
  inner) context into the another (real / outer) context.

  This is what is meant when we informally say "apply so-and-so protocol to this quantity (derived
  from the input statement & witness)".

  Put in other words, we define a mapping between the input-output interfaces of two (oracle)
  reductions, without changing anything about the underlying reductions.

  Recall that the input-output interface of an oracle reduction consists of:
  - Input: `OuterStmtIn : Type`, `OuterOStmtIn : ιₛᵢ → Type`, and `OuterWitIn : Type`
  - Output: `OuterStmtOut : Type`, `OuterOStmtOut : ιₛₒ → Type`, and `OuterWitOut : Type`

  The liftContext is defined as the following mappings of projections / lifts:

  - `projStmt : OuterStmtIn → InnerStmtIn`
  - `projOStmt : (simulation involving OuterOStmtIn to produce InnerOStmtIn)`
  - `projWit : OuterWitIn → InnerWitIn`
  - `liftStmt : OuterStmtIn × InnerStmtOut → OuterStmtOut`
  - `liftOStmt : (simulation involving InnerOStmtOut to produce OuterOStmtOut)`
  - `liftWit : OuterWitIn × InnerWitOut → OuterWitOut`

  Note that since completeness & soundness for oracle reductions are defined in terms of the same
  properties after converting to (non-oracle) reductions, we only need to focus our efforts on the
  non-oracle case.

  Note that this _exactly_ corresponds to lenses in programming languages / category theory. Namely,
  liftContext on the inputs correspond to a `view`/`get` operation (our "proj"), while liftContext
  on the output corresponds to a `modify`/`set` operation (our "lift").

  More precisely, the `proj/lift` operations correspond to a Lens between two monomial polyonmial
  functors: `OuterCtxIn y^ OuterCtxOut ⇆ InnerCtxIn y^ InnerCtxOut`.

  All the lens definitions are in `Lens.lean`. This file deals with the lens applied to reductions.
  See `OracleReduction.lean` for the application to oracle reduction.
-/

open OracleSpec OracleComp ProtocolSpec

open scoped NNReal

variable {n : ℕ} {pSpec : ProtocolSpec n} {ι : Type} {oSpec : OracleSpec ι}
  {OuterStmtIn OuterWitIn OuterStmtOut OuterWitOut : Type}
  {InnerStmtIn InnerWitIn InnerStmtOut InnerWitOut : Type}

/-- The outer prover after lifting invokes the inner prover on the projected input, and
  lifts the output -/
def Prover.liftContext
    (lens : Context.Lens OuterStmtIn OuterStmtOut InnerStmtIn InnerStmtOut
                        OuterWitIn OuterWitOut InnerWitIn InnerWitOut)
    (P : Prover oSpec InnerStmtIn InnerWitIn InnerStmtOut InnerWitOut pSpec) :
      Prover oSpec OuterStmtIn OuterWitIn OuterStmtOut OuterWitOut pSpec where
  PrvState := fun i => P.PrvState i × OuterStmtIn × OuterWitIn
  input := fun ctxIn => ⟨P.input <| lens.proj ctxIn, ctxIn⟩
  sendMessage := fun i ⟨prvState, stmtIn, witIn⟩ => do
    let ⟨msg, prvState'⟩ ← P.sendMessage i prvState
    return ⟨msg, ⟨prvState', stmtIn, witIn⟩⟩
  receiveChallenge := fun i ⟨prvState, stmtIn, witIn⟩ => do
    let f ← P.receiveChallenge i prvState
    return fun chal => ⟨f chal, stmtIn, witIn⟩
  output := fun ⟨prvState, stmtIn, witIn⟩ => do
    let ⟨innerStmtOut, innerWitOut⟩ ← P.output prvState
    return lens.lift (stmtIn, witIn) (innerStmtOut, innerWitOut)

/-- The outer verifier after lifting invokes the inner verifier on the projected input, and
  lifts the output -/
def Verifier.liftContext
    (lens : Statement.Lens OuterStmtIn OuterStmtOut InnerStmtIn InnerStmtOut)
    (V : Verifier oSpec InnerStmtIn InnerStmtOut pSpec) :
      Verifier oSpec OuterStmtIn OuterStmtOut pSpec where
  verify := fun stmtIn transcript => do
    let innerStmtIn := lens.proj stmtIn
    let innerStmtOut ← V.verify innerStmtIn transcript
    return lens.lift stmtIn innerStmtOut

/-- The outer reduction after lifting is the combination of the lifting of the prover and
  verifier -/
def Reduction.liftContext
    (lens : Context.Lens OuterStmtIn OuterStmtOut InnerStmtIn InnerStmtOut
                        OuterWitIn OuterWitOut InnerWitIn InnerWitOut)
    (R : Reduction oSpec InnerStmtIn InnerWitIn InnerStmtOut InnerWitOut pSpec) :
      Reduction oSpec OuterStmtIn OuterWitIn OuterStmtOut OuterWitOut pSpec where
  prover := R.prover.liftContext lens
  verifier := R.verifier.liftContext lens.stmt

open Verifier in
/-- The outer extractor after lifting invokes the inner extractor on the projected input, and
  lifts the output -/
def Extractor.Straightline.liftContext
    (lens : Extractor.Lens OuterStmtIn OuterStmtOut InnerStmtIn InnerStmtOut
                        OuterWitIn OuterWitOut InnerWitIn InnerWitOut)
    (E : Extractor.Straightline oSpec InnerStmtIn InnerWitIn InnerWitOut pSpec) :
      Extractor.Straightline oSpec OuterStmtIn OuterWitIn OuterWitOut pSpec :=
  fun outerStmtIn outerWitOut fullTranscript proveQueryLog verifyQueryLog => do
    let ⟨innerStmtIn, innerWitOut⟩ := lens.proj (outerStmtIn, outerWitOut)
    let innerWitIn ← E innerStmtIn innerWitOut fullTranscript proveQueryLog verifyQueryLog
    return lens.wit.lift (outerStmtIn, outerWitOut) innerWitIn

open Verifier in
/-- The outer round-by-round extractor after lifting invokes the inner extractor on the projected
  input, and lifts the output -/
def Extractor.RoundByRound.liftContext
    {WitMid : Fin (n + 1) → Type}
    (lens : Extractor.Lens OuterStmtIn OuterStmtOut InnerStmtIn InnerStmtOut
                          OuterWitIn OuterWitOut InnerWitIn InnerWitOut)
    (hEqIn : WitMid 0 = OuterWitIn)
    (E : Extractor.RoundByRound oSpec InnerStmtIn InnerWitIn InnerWitOut pSpec WitMid) :
      Extractor.RoundByRound oSpec OuterStmtIn OuterWitIn OuterWitOut pSpec WitMid :=
  {
    eqIn := hEqIn
    extractMid := fun m outerStmtIn tr witMid =>
      E.extractMid m (lens.stmt.proj outerStmtIn) tr witMid
    extractOut := fun outerStmtIn tr outerWitOut =>
      E.extractOut (lens.stmt.proj outerStmtIn) tr
        (lens.wit.proj (outerStmtIn, outerWitOut))
  }

/-- Compatibility relation between the outer input statement and the inner output statement,
relative to a verifier.

We require that the inner output statement is a possible output of the verifier on the outer
input statement, for any given transcript. Note that we have to existentially quantify over
transcripts since we only reference the verifier, and there's no way to get the transcript without
a prover. -/
def Verifier.compatStatement
    (lens : Statement.Lens OuterStmtIn OuterStmtOut InnerStmtIn InnerStmtOut)
    (V : Verifier oSpec InnerStmtIn InnerStmtOut pSpec) :
      OuterStmtIn → InnerStmtOut → Prop :=
  fun outerStmtIn innerStmtOut =>
    ∃ transcript, innerStmtOut ∈ support (V.run (lens.proj outerStmtIn) transcript)

/-- Compatibility relation between the outer input context and the inner output context, relative
to a reduction.

We require that the inner output context (statement + witness) is a possible output of the reduction
on the outer input context (statement + witness). -/
def Reduction.compatContext
    (lens : Context.Lens OuterStmtIn OuterStmtOut InnerStmtIn InnerStmtOut
                        OuterWitIn OuterWitOut InnerWitIn InnerWitOut)
    (R : Reduction oSpec InnerStmtIn InnerWitIn InnerStmtOut InnerWitOut pSpec) :
      (OuterStmtIn × OuterWitIn) → (InnerStmtOut × InnerWitOut) → Prop :=
  fun outerCtxIn innerCtxOut =>
    innerCtxOut ∈
      (Prod.snd ∘ Prod.fst) ''
        support (R.run (lens.stmt.proj outerCtxIn.1) (lens.wit.proj outerCtxIn))

/-- Compatibility relation between the outer input witness and the inner output witness, relative to
  a straightline extractor.

We require that the inner output witness is a possible output of the straightline extractor on the
outer input witness, for a given input statement, transcript, and prover and verifier's query logs.
-/
def Extractor.Straightline.compatWit
    (lens : Extractor.Lens OuterStmtIn OuterStmtOut InnerStmtIn InnerStmtOut
                        OuterWitIn OuterWitOut InnerWitIn InnerWitOut)
    (E : Extractor.Straightline oSpec InnerStmtIn InnerWitIn InnerWitOut pSpec) :
      OuterStmtIn × OuterWitOut → InnerWitIn → Prop :=
  fun ⟨outerStmtIn, outerWitOut⟩ innerWitIn =>
    ∃ stmt tr logP logV, innerWitIn ∈
      support (E stmt (lens.wit.proj (outerStmtIn, outerWitOut)) tr logP logV)

/-- The outer state function after lifting invokes the inner state function on the projected
  input, and lifts the output -/
def Verifier.StateFunction.liftContext
    {σ : Type} {init : ProbComp σ} {impl : QueryImpl oSpec (StateT σ ProbComp)}
    (lens : Statement.Lens OuterStmtIn OuterStmtOut InnerStmtIn InnerStmtOut)
    (V : Verifier oSpec InnerStmtIn InnerStmtOut pSpec)
    (outerLangIn : Set OuterStmtIn) (outerLangOut : Set OuterStmtOut)
    (innerLangIn : Set InnerStmtIn) (innerLangOut : Set InnerStmtOut)
    [lensSound : lens.IsSound outerLangIn outerLangOut innerLangIn innerLangOut
      (V.compatStatement lens)]
    (stF : V.StateFunction init impl innerLangIn innerLangOut)
    (proj_state : ∀ outerStmtIn,
      outerStmtIn ∈ outerLangIn ↔ lens.proj outerStmtIn ∈ innerLangIn)
    (lift_state : ∀ outerStmtIn transcript,
      ¬ stF.toFun (.last n) (lens.proj outerStmtIn) transcript →
      Pr[(· ∈ outerLangOut) |
        OptionT.mk (do
          let s ← init
          (simulateQ impl ((V.liftContext lens).run outerStmtIn transcript)).run' s)] = 0) :
      (V.liftContext lens).StateFunction init impl outerLangIn outerLangOut
where
  toFun := fun m outerStmtIn transcript =>
    stF m (lens.proj outerStmtIn) transcript
  toFun_empty := fun stmt => by
    exact (proj_state stmt).trans (stF.toFun_empty (lens.proj stmt))
  toFun_next := fun m hDir outerStmtIn transcript hStmt msg =>
    stF.toFun_next m hDir (lens.proj outerStmtIn) transcript hStmt msg
  toFun_full := fun outerStmtIn transcript hStmt => by
    exact lift_state outerStmtIn transcript hStmt

section Theorems

/- Theorems about liftContext interacting with reduction execution and security properties -/

/-- Stateful simulation can only restrict the set of reachable outcomes: any value in the support
  of `(simulateQ so oa).run' s` is already in the support of `oa`.

  This holds for an arbitrary stateful oracle implementation `so` (even one that changes the
  target oracle spec), since `simulateQ` threads the computation along the original control flow,
  and `query t` has full support over its range. -/
theorem mem_support_simulateQ_run'_subset
    {ι ι' : Type} {spec : OracleSpec ι} {spec' : OracleSpec ι'} {σ' : Type} {τ : Type}
    (so : QueryImpl spec (StateT σ' (OracleComp spec')))
    (s : σ') (oa : OracleComp spec τ) (x : τ)
    (hx : x ∈ support ((simulateQ so oa).run' s)) : x ∈ support oa := by
  revert s
  induction oa using OracleComp.inductionOn with
  | pure y =>
      intro s hx
      simp only [simulateQ_pure, StateT.run'_eq, StateT.run_pure, support_map,
        support_pure, Set.image_singleton, Set.mem_singleton_iff] at hx
      simp [hx]
  | query_bind t mx ih =>
      intro s hx
      rw [simulateQ_bind, simulateQ_query] at hx
      simp only [OracleQuery.cont_query, id_map, OracleQuery.input_query,
        StateT.run'_eq, StateT.run_bind, support_map, support_bind, Set.mem_image,
        Set.mem_iUnion] at hx
      obtain ⟨⟨v, p⟩, ⟨⟨u, s'⟩, _, hmem⟩, hxv⟩ := hx
      simp only at hxv
      have hxmx : x ∈ support (mx u) := by
        apply ih u s'
        simp only [StateT.run'_eq, support_map, Set.mem_image]
        exact ⟨⟨v, p⟩, hmem, hxv⟩
      simp only [support_bind, support_query, Set.mem_iUnion]
      exact ⟨u, by simp, hxmx⟩

/-- Folding an output post-map `g` over an `OptionT ProbComp` computation of the form
  `OptionT.mk ((fun p => Option.map g p.1) <$> base)` into the event predicate: its `probEvent`
  of `P` equals the `probEvent` of `P ∘ g` over the unmapped `OptionT.mk ((fun p => p.1) <$> base)`.

  Used to relate the lifted reduction run (which post-composes the inner run with the output lens
  map) to the inner run. -/
theorem probEvent_optionT_mk_map_fst_map {α β γ : Type}
    (base : ProbComp (Option α × γ)) (g : α → β) (P : β → Prop) :
    Pr[P | (OptionT.mk ((fun p => Option.map g p.1) <$> base) : OptionT ProbComp β)] =
      Pr[P ∘ g | (OptionT.mk ((fun p => p.1) <$> base) : OptionT ProbComp α)] :=
  OptionT.probEvent_eq_of_run_map_eq _ _ g P
    (by simp only [OptionT.run_map, OptionT.run_mk, Functor.map_map, Function.comp_apply])

namespace Prover

/- Breaking down the intertwining of liftContext and prover execution -/

/-- Lifting the prover intertwines with the process round function -/
theorem liftContext_processRound
    {lens : Context.Lens OuterStmtIn OuterStmtOut InnerStmtIn InnerStmtOut
                        OuterWitIn OuterWitOut InnerWitIn InnerWitOut}
    {i : Fin n}
    {P : Prover oSpec InnerStmtIn InnerWitIn InnerStmtOut InnerWitOut pSpec}
    {resultRound : OracleComp (oSpec + [pSpec.Challenge]ₒ)
      (pSpec.Transcript i.castSucc × (P.liftContext lens).PrvState i.castSucc)} :
      (P.liftContext lens).processRound i resultRound
      = do
        let ⟨transcript, prvState, outerStmtIn, outerWitIn⟩ ← resultRound
        let ⟨newTranscript, newPrvState⟩ ← P.processRound i (do return ⟨transcript, prvState⟩)
        return ⟨newTranscript, ⟨newPrvState, outerStmtIn, outerWitIn⟩⟩ := by
  unfold processRound liftContext
  simp only [bind_pure_comp]
  congr 1; funext ⟨tr, ps, outerStmtIn', outerWitIn'⟩
  simp only [pure_bind]
  split <;> simp [Functor.map_map, Function.comp, liftM_map, map_bind,
    bind_assoc, pure_bind, bind_map_left, bind_pure_comp]


theorem liftContext_runToRound
    {lens : Context.Lens OuterStmtIn OuterStmtOut InnerStmtIn InnerStmtOut
                        OuterWitIn OuterWitOut InnerWitIn InnerWitOut}
    {outerStmtIn : OuterStmtIn} {outerWitIn : OuterWitIn} {i : Fin (n + 1)}
    (P : Prover oSpec InnerStmtIn InnerWitIn InnerStmtOut InnerWitOut pSpec) :
      (P.liftContext lens).runToRound i outerStmtIn outerWitIn
      = do
        let ⟨transcript, prvState⟩ ←
          (P.runToRound i).uncurry (lens.proj (outerStmtIn, outerWitIn))
        return ⟨transcript, ⟨prvState, outerStmtIn, outerWitIn⟩⟩ := by
  unfold runToRound Function.uncurry
  dsimp
  induction i using Fin.induction with
  | zero => simp [liftContext]
  | succ i ih =>
    simp only [Fin.induction_succ, ih, bind_pure_comp,
      liftContext_processRound, ChallengeIdx, bind_map_left, Prod.mk.eta]
    simp [processRound]

-- Requires more lemmas about `simulateQ` for logging oracles
theorem liftContext_runWithLogToRound
    {lens : Context.Lens OuterStmtIn OuterStmtOut InnerStmtIn InnerStmtOut
                        OuterWitIn OuterWitOut InnerWitIn InnerWitOut}
    {outerStmtIn : OuterStmtIn} {outerWitIn : OuterWitIn} {i : Fin (n + 1)}
    (P : Prover oSpec InnerStmtIn InnerWitIn InnerStmtOut InnerWitOut pSpec) :
      (P.liftContext lens).runWithLogToRound i outerStmtIn outerWitIn
      = do
        let ⟨⟨transcript, prvState⟩, queryLog⟩ ←
          (P.runWithLogToRound i).uncurry (lens.proj (outerStmtIn, outerWitIn))
        return ⟨⟨transcript, ⟨prvState, outerStmtIn, outerWitIn⟩⟩, queryLog⟩ := by
  unfold runWithLogToRound
  induction i using Fin.induction with
  | zero => simp [liftContext, Function.uncurry]
  | succ i ih => simp [liftContext_runToRound, Function.uncurry]

/-- Running the lifted outer prover is equivalent to running the inner prover on the projected
  input, and then integrating the output -/
theorem liftContext_run
    {lens : Context.Lens OuterStmtIn OuterStmtOut InnerStmtIn InnerStmtOut
                        OuterWitIn OuterWitOut InnerWitIn InnerWitOut}
    {outerStmtIn : OuterStmtIn} {outerWitIn : OuterWitIn}
    {P : Prover oSpec InnerStmtIn InnerWitIn InnerStmtOut InnerWitOut pSpec} :
      (P.liftContext lens).run outerStmtIn outerWitIn
      = do
        let ⟨fullTranscript, innerCtxOut⟩ ←
          P.run.uncurry (lens.proj (outerStmtIn, outerWitIn))
        return ⟨fullTranscript, lens.lift (outerStmtIn, outerWitIn) innerCtxOut⟩ := by
  simp only [run, liftContext_runToRound]
  simp [liftContext, Function.uncurry]

/-- Lifting the prover intertwines with logging queries of the prover -/
theorem liftContext_runWithLog
    {lens : Context.Lens OuterStmtIn OuterStmtOut InnerStmtIn InnerStmtOut
                        OuterWitIn OuterWitOut InnerWitIn InnerWitOut}
    {outerStmtIn : OuterStmtIn} {outerWitIn : OuterWitIn}
    {P : Prover oSpec InnerStmtIn InnerWitIn InnerStmtOut InnerWitOut pSpec} :
      (P.liftContext lens).runWithLog outerStmtIn outerWitIn
      = do
        let ⟨⟨fullTranscript, innerCtxOut⟩, queryLog⟩ ←
          P.runWithLog.uncurry (lens.proj (outerStmtIn, outerWitIn))
        return ⟨⟨fullTranscript, lens.lift (outerStmtIn, outerWitIn) innerCtxOut⟩, queryLog⟩ := by
  rw [runWithLog, liftContext_run]
  simp [Function.uncurry]
  congr

end Prover

namespace Reduction

theorem liftContext_run
    {lens : Context.Lens OuterStmtIn OuterStmtOut InnerStmtIn InnerStmtOut
                        OuterWitIn OuterWitOut InnerWitIn InnerWitOut}
    {outerStmtIn : OuterStmtIn} {outerWitIn : OuterWitIn}
    {R : Reduction oSpec InnerStmtIn InnerWitIn InnerStmtOut InnerWitOut pSpec} :
      (R.liftContext lens).run outerStmtIn outerWitIn = do
        let ⟨⟨fullTranscript, innerCtxOut⟩, verInnerStmtOut⟩ ←
          R.run.uncurry (lens.proj (outerStmtIn, outerWitIn))
        return ⟨⟨fullTranscript, lens.lift (outerStmtIn, outerWitIn) innerCtxOut⟩ ,
                lens.stmt.lift outerStmtIn verInnerStmtOut⟩ := by
  unfold run
  simp [liftContext, Prover.liftContext_run, Verifier.liftContext, Verifier.run, Function.uncurry]
  congr 1; funext ⟨_, _⟩; congr 1; funext a_1
  simp [Functor.map_map, Function.comp]
  cases a_1 <;> simp [Option.getM, map_pure]

theorem liftContext_runWithLog
    {lens : Context.Lens OuterStmtIn OuterStmtOut InnerStmtIn InnerStmtOut
                        OuterWitIn OuterWitOut InnerWitIn InnerWitOut}
    {outerStmtIn : OuterStmtIn} {outerWitIn : OuterWitIn}
    {R : Reduction oSpec InnerStmtIn InnerWitIn InnerStmtOut InnerWitOut pSpec} :
      (R.liftContext lens).runWithLog outerStmtIn outerWitIn = do
        let ⟨⟨⟨fullTranscript, innerCtxOut⟩, verInnerStmtOut⟩, queryLog⟩ ←
          R.runWithLog.uncurry (lens.proj (outerStmtIn, outerWitIn))
        return ⟨⟨⟨fullTranscript, lens.lift (outerStmtIn, outerWitIn) innerCtxOut⟩,
                lens.stmt.lift outerStmtIn verInnerStmtOut⟩, queryLog⟩ := by
  unfold runWithLog
  simp only [liftContext, Prover.liftContext_runWithLog, Verifier.liftContext, Verifier.run,
    Function.uncurry, liftM_map, map_bind, bind_map_left, bind_pure_comp]
  refine bind_congr fun a => ?_
  -- The lifted verifier post-composes the inner verify with `lens.stmt.lift`; this is an
  -- `OptionT`-level map, definitionally an `Option.map` at the `OracleComp` level.  Push it
  -- through `simulateQ loggingOracle` and `WriterT.run`, then fold it into the final result map.
  conv_lhs =>
    rw [show (lens.stmt.lift outerStmtIn <$> R.verifier.verify (lens.stmt.proj outerStmtIn) a.1.1
          : OptionT (OracleComp oSpec) OuterStmtOut)
        = (Option.map (lens.stmt.lift outerStmtIn) <$>
            R.verifier.verify (lens.stmt.proj outerStmtIn) a.1.1
          : OracleComp oSpec (Option OuterStmtOut)) from OptionT.run_map _ _]
  rw [simulateQ_map, WriterT.run_map]
  simp only [liftM_map, Functor.map_map, Statement.Lens.proj]
  rw [bind_map_left]
  refine bind_congr fun b => ?_
  cases h : b.1 with
  | none => simp only [Option.map_none, Option.getM_none, h, map_failure]
  | some v => simp only [Option.map_some, Option.getM_some, h, map_pure]

end Reduction

variable [∀ i, SampleableType (pSpec.Challenge i)]
  {σ : Type} {init : ProbComp σ} {impl : QueryImpl oSpec (StateT σ ProbComp)}
  {outerRelIn : Set (OuterStmtIn × OuterWitIn)} {outerRelOut : Set (OuterStmtOut × OuterWitOut)}
  {innerRelIn : Set (InnerStmtIn × InnerWitIn)} {innerRelOut : Set (InnerStmtOut × InnerWitOut)}

namespace Reduction

variable
    {R : Reduction oSpec InnerStmtIn InnerWitIn InnerStmtOut InnerWitOut pSpec}
    {completenessError : ℝ≥0}
    {lens : Context.Lens OuterStmtIn OuterStmtOut InnerStmtIn InnerStmtOut
                          OuterWitIn OuterWitOut InnerWitIn InnerWitOut}
    [lensComplete : lens.IsComplete outerRelIn innerRelIn outerRelOut innerRelOut
      (R.compatContext lens)]

/-- Lifting the reduction preserves completeness, assuming the lens satisfies its completeness
  conditions
-/
theorem liftContext_completeness
    (h : R.completeness init impl innerRelIn innerRelOut completenessError) :
      (R.liftContext lens).completeness init impl outerRelIn outerRelOut completenessError := by
  unfold completeness at h ⊢
  intro outerStmtIn outerWitIn hRelIn
  have hR := h (lens.stmt.proj outerStmtIn) (lens.wit.proj (outerStmtIn, outerWitIn))
    (lensComplete.proj_complete _ _ hRelIn)
  rw [Reduction.liftContext_run]
  refine le_trans hR ?_
  -- Normalise both computations to maps of the common `init`-then-simulate base computation.
  -- The LHS is then `Pr[P_inner | (fun p => p.1) <$> base]` and the RHS is
  -- `Pr[P_outer | (fun p => Option.map f p.1) <$> base]`, where `f` is the output lens map.
  simp only [Function.uncurry, Context.Lens.proj, bind_pure_comp, OptionT.run_map, simulateQ_map,
    StateT.run'_eq, StateT.run_map, map_bind, Functor.map_map, ← map_bind]
  -- Fold the output lens map `f` into the RHS predicate.
  rw [probEvent_optionT_mk_map_fst_map]
  -- Both `probEvent`s are now over the same computation; reduce to a support-aware pointwise
  -- implication and discharge it with the lens completeness law.
  refine _root_.probEvent_mono ?_
  rintro ⟨⟨innerTr, innerStmtPrv, innerWit⟩, innerStmtVer⟩ hSupport ⟨hRelOut, hVer⟩
  -- `hVer : innerStmtPrv = innerStmtVer`: the prover & verifier output statements agree.
  simp only [Function.comp_apply] at hVer ⊢
  subst hVer
  refine ⟨?_, rfl⟩
  -- Goal: the lifted output context satisfies `outerRelOut`.  Apply the lens completeness law.
  refine lensComplete.lift_complete outerStmtIn outerWitIn innerStmtPrv innerWit ?_ hRelIn hRelOut
  -- Compatibility witness: the inner output context is reachable by the inner reduction run.
  simp only [OptionT.mem_support_iff, OptionT.run_mk, mem_support_bind_iff, support_map,
    Set.mem_image] at hSupport
  obtain ⟨x, ⟨s, _hs, hmem⟩, hx1⟩ := hSupport
  have hsub := mem_support_simulateQ_run'_subset (impl.addLift challengeQueryImpl) s
    (Reduction.run (lens.stmt.proj outerStmtIn)
      (lens.wit.proj (outerStmtIn, outerWitIn)) R).run x.1
    (by simp only [StateT.run'_eq, support_map, Set.mem_image]; exact ⟨x, hmem, rfl⟩)
  rw [hx1] at hsub
  rw [Reduction.compatContext]
  simp only [Set.mem_image, Function.comp_apply]
  refine ⟨((innerTr, innerStmtPrv, innerWit), innerStmtPrv), ?_, rfl⟩
  rwa [← OptionT.mem_support_iff] at hsub

theorem liftContext_perfectCompleteness
    (h : R.perfectCompleteness init impl innerRelIn innerRelOut) :
      (R.liftContext lens).perfectCompleteness init impl outerRelIn outerRelOut := by
  exact liftContext_completeness h

-- Can't turn the above into an instance because Lean needs to synthesize `innerRelIn` and
-- `innerRelOut` out of thin air.

-- instance [Reduction.IsComplete innerRelIn innerRelOut R completenessError] :
--     R.liftContext.IsComplete outerRelIn outerRelOut completenessError :=
--   ⟨R.liftContext.completeness⟩

-- instance [R.IsPerfectComplete relIn relOut] :
--     R.liftContext.IsPerfectComplete relIn relOut :=
--   ⟨fun _ => R.liftContext.perfectCompleteness _ _ _⟩

end Reduction

namespace Verifier

/-- The inner malicious prover obtained from an outer prover by fixing the outer input
context and forgetting the output statement; used to transfer soundness across a
statement lens. (A transparent `def` — using `have` inside the proof would make the
record body definitionally opaque and break the run-factoring lemma below.) -/
private def _fixContext [Inhabited InnerStmtOut]
    {WitIn WitOut : Type}
    (outerP : Prover oSpec OuterStmtIn WitIn OuterStmtOut WitOut pSpec)
    (outerStmtIn : OuterStmtIn) (outerWitIn : WitIn) :
      Prover oSpec InnerStmtIn WitIn InnerStmtOut WitOut pSpec where
  PrvState := outerP.PrvState
  input := fun _ => outerP.input (outerStmtIn, outerWitIn)
  sendMessage := outerP.sendMessage
  receiveChallenge := outerP.receiveChallenge
  output := fun state => do
    let ⟨_, outerWitOut⟩ ← outerP.output state
    return ⟨default, outerWitOut⟩

/-- The fixed-context inner prover's run is the outer prover's run with the output
statement forgotten. -/
private lemma _fixContext_run [Inhabited InnerStmtOut]
    {WitIn WitOut : Type}
    (outerP : Prover oSpec OuterStmtIn WitIn OuterStmtOut WitOut pSpec)
    (outerStmtIn : OuterStmtIn) (outerWitIn : WitIn) (innerStmtIn : InnerStmtIn) :
      Prover.run innerStmtIn outerWitIn
          (_fixContext (InnerStmtOut := InnerStmtOut) outerP outerStmtIn outerWitIn) =
        (fun x => ⟨x.1, default, x.2.2⟩) <$> Prover.run outerStmtIn outerWitIn outerP := by
  have hRTR : ∀ i, Prover.runToRound i innerStmtIn outerWitIn
      (_fixContext (InnerStmtOut := InnerStmtOut) outerP outerStmtIn outerWitIn) =
        Prover.runToRound i outerStmtIn outerWitIn outerP := fun _ => rfl
  simp only [Prover.run, hRTR, _fixContext, map_bind, bind_pure_comp, Functor.map_map,
    liftM_map]
  rfl

/-- Lifting the reduction preserves soundness, assuming the lens satisfies its soundness
  conditions -/
theorem liftContext_soundness [Inhabited InnerStmtOut]
    {outerLangIn : Set OuterStmtIn} {outerLangOut : Set OuterStmtOut}
    {innerLangIn : Set InnerStmtIn} {innerLangOut : Set InnerStmtOut}
    {soundnessError : ℝ≥0}
    {lens : Statement.Lens OuterStmtIn OuterStmtOut InnerStmtIn InnerStmtOut}
    (V : Verifier oSpec InnerStmtIn InnerStmtOut pSpec)
    -- NOTE: figure out the right compatibility relation for the IsSound condition
    [lensSound : lens.IsSound outerLangIn outerLangOut innerLangIn innerLangOut
      (V.compatStatement lens)]
    (h : V.soundness init impl innerLangIn innerLangOut soundnessError) :
      (V.liftContext lens).soundness init impl outerLangIn outerLangOut soundnessError := by
  unfold soundness Reduction.run at h ⊢
  -- Note: there is no distinction between `Outer` and `Inner` here
  intro WitIn WitOut outerWitIn outerP outerStmtIn hOuterStmtIn
  simp at h ⊢
  have hProj : lens.proj outerStmtIn ∉ innerLangIn :=
    lensSound.proj_sound _ hOuterStmtIn
  have hSound := h WitIn WitOut outerWitIn
    (_fixContext (InnerStmtOut := InnerStmtOut) outerP outerStmtIn outerWitIn)
    (lens.proj outerStmtIn) hProj
  refine le_trans ?_ hSound
  rw [_fixContext_run]
  simp only [Verifier.liftContext, Verifier.run, Function.uncurry, bind_pure_comp,
    OptionT.run_map, simulateQ_map, StateT.run'_eq, StateT.run_map, map_bind,
    Functor.map_map, liftM_map, ← map_bind]
  -- `getM.run` is just `pure`, collapsing the output-plumbing stage on both sides
  have hGetMRun : ∀ {α : Type} (o : Option α),
      (Option.getM (m := OptionT (OracleComp (oSpec + [pSpec.Challenge]ₒ))) o).run = pure o := by
    intro _ o; cases o <;> rfl
  -- push the lift-map through `Option.elimM`'s source
  have hElimM_map : ∀ {m : Type → Type} [Monad m] [LawfulMonad m] {α β γ : Type}
      (x : m (Option α)) (g : α → β) (y : m γ) (f : β → m γ),
      Option.elimM (Option.map g <$> x) y f = Option.elimM x y (f ∘ g) := by
    intro m _ _ α β γ x g y f
    simp only [Option.elimM, bind_map_left]
    exact bind_congr fun o => by cases o <;> rfl
  simp only [hGetMRun, hElimM_map, simulateQ_pure, Function.comp_def, Option.map_map]
  -- normalize pure values and push the prover-output-forgetting map into the continuation
  simp only [map_pure, bind_map_left]
  -- hoist a uniform value-map out of the elim-chain
  have hMapElim : ∀ {α β γ : Type} {m : Type → Type} [Monad m] [LawfulMonad m]
      (src : m (Option α)) (g : β → γ) (h : α → Option β),
      Option.elimM src (pure none) (fun a => pure (Option.map g (h a))) =
        (Option.map g) <$> Option.elimM src (pure none) (fun a => pure (h a)) := by
    intro α β γ m _ _ src g h
    simp only [Option.elimM, map_bind]
    exact bind_congr fun o => by cases o <;> simp
  -- factor both continuations' values through the common pairing `Option.map (Prod.mk x.1)`
  have hLval : ∀ (t : pSpec.FullTranscript × OuterStmtOut × WitOut) (z : Option InnerStmtOut),
      Option.map (Prod.mk t) (Option.map (lens.lift outerStmtIn) z) =
        Option.map (Prod.map id (lens.lift outerStmtIn)) (Option.map (Prod.mk t) z) := by
    intro t z; cases z <;> rfl
  have hRval : ∀ (t : pSpec.FullTranscript × OuterStmtOut × WitOut) (z : Option InnerStmtOut),
      Option.map (Prod.mk (t.1, (default : InnerStmtOut), t.2.2)) z =
        Option.map (Prod.map (fun t' : pSpec.FullTranscript × OuterStmtOut × WitOut =>
          (t'.1, (default : InnerStmtOut), t'.2.2)) id) (Option.map (Prod.mk t) z) := by
    intro t z; cases z <;> rfl
  simp only [hLval, hRval, hMapElim, StateT.run_map, Functor.map_map]
  -- Both sides are now uniform value-maps over the SAME identity-pairing core game:
  -- the outer prover interacting with the inner verifier, outputting ⟨prover-triple, inner stmt⟩.
  set core : OptionT ProbComp
      ((pSpec.FullTranscript × OuterStmtOut × WitOut) × InnerStmtOut) :=
    ((liftM init : OptionT ProbComp σ) >>= fun x0 => (liftM ((simulateQ (impl + QueryImpl.liftTarget (StateT σ ProbComp) challengeQueryImpl) (Prover.run outerStmtIn outerWitIn outerP)).run x0) : OptionT ProbComp _) >>= fun x => OptionT.mk ((fun a => Option.map (Prod.mk x.1) a.1) <$> (Option.elimM (simulateQ (impl + QueryImpl.liftTarget (StateT σ ProbComp) challengeQueryImpl) ((liftM ((V.verify (lens.proj outerStmtIn) x.1.1).run) : OptionT (OracleComp (oSpec + [pSpec.Challenge]ₒ)) (Option InnerStmtOut)).run)) (pure none) (fun a => pure a)).run x.2)) with hcore
  have hL : (Prod.map id (lens.lift outerStmtIn) <$> core :
      OptionT ProbComp ((pSpec.FullTranscript × OuterStmtOut × WitOut) × OuterStmtOut))
      = ((liftM init : OptionT ProbComp σ) >>= fun x0 => (liftM ((simulateQ (impl + QueryImpl.liftTarget (StateT σ ProbComp) challengeQueryImpl) (Prover.run outerStmtIn outerWitIn outerP)).run x0) : OptionT ProbComp _) >>= fun x => OptionT.mk ((fun a => Option.map (Prod.map id (lens.lift outerStmtIn)) (Option.map (Prod.mk x.1) a.1)) <$> (Option.elimM (simulateQ (impl + QueryImpl.liftTarget (StateT σ ProbComp) challengeQueryImpl) ((liftM ((V.verify (lens.proj outerStmtIn) x.1.1).run) : OptionT (OracleComp (oSpec + [pSpec.Challenge]ₒ)) (Option InnerStmtOut)).run)) (pure none) (fun a => pure a)).run x.2)) := by
    rw [hcore]
    simp only [map_bind]
    refine bind_congr fun x0 => bind_congr fun x => ?_
    apply OptionT.ext
    simp only [OptionT.run_map, OptionT.run_mk, Functor.map_map]
  have hR : ((Prod.map (fun t' : pSpec.FullTranscript × OuterStmtOut × WitOut =>
        (t'.1, (default : InnerStmtOut), t'.2.2)) id) <$> core :
      OptionT ProbComp ((pSpec.FullTranscript × InnerStmtOut × WitOut) × InnerStmtOut))
      = ((liftM init : OptionT ProbComp σ) >>= fun x0 => (liftM ((simulateQ (impl + QueryImpl.liftTarget (StateT σ ProbComp) challengeQueryImpl) (Prover.run outerStmtIn outerWitIn outerP)).run x0) : OptionT ProbComp _) >>= fun a => OptionT.mk ((fun a_1 => Option.map (Prod.map (fun t' : pSpec.FullTranscript × OuterStmtOut × WitOut => (t'.1, (default : InnerStmtOut), t'.2.2)) id) (Option.map (Prod.mk a.1) a_1.1)) <$> (Option.elimM (simulateQ (impl + QueryImpl.liftTarget (StateT σ ProbComp) challengeQueryImpl) ((liftM ((V.verify (lens.proj outerStmtIn) a.1.1).run) : OptionT (OracleComp (oSpec + [pSpec.Challenge]ₒ)) (Option InnerStmtOut)).run)) (pure none) (fun a => pure a)).run a.2)) := by
    rw [hcore]
    simp only [map_bind]
    refine bind_congr fun x0 => bind_congr fun x => ?_
    apply OptionT.ext
    simp only [OptionT.run_map, OptionT.run_mk, Functor.map_map]
  rw [← hL, ← hR, probEvent_map, probEvent_map]
  -- same base computation: compare events pointwise on the support
  refine _root_.probEvent_mono ?_
  rintro ⟨tOut, innerStmtOut⟩ hSupport hOut
  simp only [Function.comp_apply, Prod.map_apply, id_eq] at hOut ⊢
  -- contrapose through the lens soundness law; its compatibility witness comes from the
  -- fact that `innerStmtOut` is reachable by the inner verifier on the run's transcript
  by_contra hIn
  refine absurd hOut (lensSound.lift_sound outerStmtIn innerStmtOut ?_ hIn)
  -- extract the compatibility witness from the support of the core game
  rw [hcore] at hSupport
  simp only [Option.elimM, mem_support_bind_iff, StateT.run_bind, support_map,
    Set.mem_image, Prod.exists, OptionT.run_lift, OptionT.run_mk] at hSupport
  obtain ⟨x0, hx0, tr, so, wo, st, hProv, hLast⟩ := hSupport
  simp only [OptionT.mem_support_iff, OptionT.run_mk, support_map, Set.mem_image,
    mem_support_bind_iff, Prod.exists] at hLast
  obtain ⟨a, b, ⟨a1, b1, hVerSup, hElim⟩, hMapEq⟩ := hLast
  -- the pairing map forces `a = some innerStmtOut`
  rcases a with _ | v
  · simp at hMapEq
  simp only [Option.map_some, Option.some_inj, Prod.mk.injEq] at hMapEq
  obtain ⟨hTr, hV⟩ := hMapEq
  subst hV
  -- the elim stage forces `a1 = some (some innerStmtOut)`
  rcases a1 with _ | w
  · simp at hElim
  · simp only [Option.elim_some] at hElim
    have hw : some v = w ∧ b = b1 := by
      simpa using hElim
    obtain ⟨rfl, rfl⟩ := hw.symm.imp Eq.symm Eq.symm
    -- strip the simulation: the verify value is in the support of the lifted verifier run
    have h1 : some (some v) ∈
        support ((simulateQ (impl + QueryImpl.liftTarget (StateT σ ProbComp)
          challengeQueryImpl) ((liftM ((V.verify (lens.proj outerStmtIn) tr).run) :
            OptionT (OracleComp (oSpec + [pSpec.Challenge]ₒ)) (Option InnerStmtOut)).run)).run' st) := by
      simp only [StateT.run'_eq, support_map, Set.mem_image]
      exact ⟨_, hVerSup, rfl⟩
    have h2 := mem_support_simulateQ_run'_subset _ _ _ _ h1
    -- unlift back to the verifier's own run
    refine ⟨tr, ?_⟩
    rw [Verifier.run]
    rw [OptionT.mem_support_iff]
    refine OracleComp.mem_support_of_mem_support_liftComp
      (superSpec := oSpec + [pSpec.Challenge]ₒ) _ _ ?_
    have h3 : ((liftM ((V.verify (lens.proj outerStmtIn) tr).run) :
        OptionT (OracleComp (oSpec + [pSpec.Challenge]ₒ)) (Option InnerStmtOut)).run)
        = some <$> (OracleComp.liftComp ((V.verify (lens.proj outerStmtIn) tr).run)
            (oSpec + [pSpec.Challenge]ₒ)) := by
      show simulateQ _ ((OptionT.lift ((V.verify (lens.proj outerStmtIn) tr).run)).run) = _
      rw [show ((OptionT.lift ((V.verify (lens.proj outerStmtIn) tr).run) :
        OptionT (OracleComp oSpec) (Option InnerStmtOut)).run)
        = some <$> ((V.verify (lens.proj outerStmtIn) tr).run) from rfl]
      rw [simulateQ_map]
      rfl
    rw [h3, support_map] at h2
    obtain ⟨y, hy, hEq⟩ := h2
    obtain rfl : y = some v := by simpa using hEq
    exact hy

/-
  Lifting the reduction preserves knowledge soundness, assuming the lens satisfies its knowledge
  soundness conditions

  Note: since knowledge soundness is defined existentially in terms of the extractor, we also cannot
  impose any meaningful compatibility conditions on the witnesses (outer output & inner input),
  hence `compatWit` field is just always true

  (future extensions may define lifting relative to a particular extractor, if needed)
-/
theorem liftContext_knowledgeSoundness [Inhabited InnerStmtOut] [Inhabited InnerWitIn]
    {outerRelIn : Set (OuterStmtIn × OuterWitIn)} {outerRelOut : Set (OuterStmtOut × OuterWitOut)}
    {innerRelIn : Set (InnerStmtIn × InnerWitIn)} {innerRelOut : Set (InnerStmtOut × InnerWitOut)}
    {knowledgeError : ℝ≥0}
    {stmtLens : Statement.Lens OuterStmtIn OuterStmtOut InnerStmtIn InnerStmtOut}
    {witLens : Witness.InvLens OuterStmtIn OuterWitIn OuterWitOut InnerWitIn InnerWitOut}
    (V : Verifier oSpec InnerStmtIn InnerStmtOut pSpec)
    [lensKS : Extractor.Lens.IsKnowledgeSound outerRelIn innerRelIn outerRelOut innerRelOut
      (V.compatStatement stmtLens) (fun _ _ => True) ⟨stmtLens, witLens⟩]
    (h : V.knowledgeSoundness init impl innerRelIn innerRelOut knowledgeError) :
      (V.liftContext stmtLens).knowledgeSoundness init impl outerRelIn outerRelOut
        knowledgeError := by
  unfold knowledgeSoundness at h ⊢
  obtain ⟨E, h'⟩ := h
  refine ⟨E.liftContext ⟨stmtLens, witLens⟩, ?_⟩
  intro outerStmtIn outerWitIn outerP
  simp [Extractor.Straightline.liftContext]
  let innerP : Prover oSpec InnerStmtIn InnerWitIn InnerStmtOut InnerWitOut pSpec :=
    {
      PrvState := outerP.PrvState
      input := fun _ => outerP.input (outerStmtIn, outerWitIn)
      sendMessage := outerP.sendMessage
      receiveChallenge := outerP.receiveChallenge
      output := fun state => do
        let ⟨outerStmtOut, outerWitOut⟩ ← outerP.output state
        return ⟨default, witLens.proj (outerStmtIn, outerWitOut)⟩
    }
  have h_innerP_input {innerStmtIn} {innerWitIn} :
      innerP.input (innerStmtIn, innerWitIn) = outerP.input (outerStmtIn, outerWitIn) := rfl
  simp at h'
  have hR := h' (stmtLens.proj outerStmtIn) default innerP
  simp at hR
  simp [Reduction.runWithLog, Verifier.liftContext, Verifier.run] at hR ⊢
  have h_innerP_runWithLog {innerStmtIn} {innerWitIn} :
      innerP.runWithLog innerStmtIn innerWitIn
      = do
        let ⟨⟨transcript, ⟨_, outerWitOut⟩⟩, rest⟩ ← outerP.runWithLog outerStmtIn outerWitIn
        return ⟨⟨transcript, ⟨default, witLens.proj (outerStmtIn, outerWitOut)⟩⟩, rest⟩ := by
    sorry
  refine le_trans ?_ hR
  -- Massage the two `probEvent`s so that they have the same base computation `oa`?
  simp [h_innerP_runWithLog]
  -- apply probEvent_mono ?_
  sorry

/-
  Lifting the reduction preserves round-by-round soundness, assuming the lens satisfies its
  soundness conditions
-/
theorem liftContext_rbr_soundness [Inhabited InnerStmtOut]
    {outerLangIn : Set OuterStmtIn} {outerLangOut : Set OuterStmtOut}
    {innerLangIn : Set InnerStmtIn} {innerLangOut : Set InnerStmtOut}
    {rbrSoundnessError : pSpec.ChallengeIdx → ℝ≥0}
    {lens : Statement.Lens OuterStmtIn OuterStmtOut InnerStmtIn InnerStmtOut}
    (V : Verifier oSpec InnerStmtIn InnerStmtOut pSpec)
    -- NOTE: figure out the right compatibility relation for the IsSound condition
    [lensSound : lens.IsSound outerLangIn outerLangOut innerLangIn innerLangOut
      (V.compatStatement lens)]
    (h : V.rbrSoundness init impl innerLangIn innerLangOut rbrSoundnessError) :
      (V.liftContext lens).rbrSoundness init impl outerLangIn outerLangOut rbrSoundnessError := by
  unfold rbrSoundness at h ⊢
  obtain ⟨stF, h⟩ := h
  simp at h ⊢
  refine ⟨by
    sorry, ?_⟩
  intro outerStmtIn hOuterStmtIn WitIn WitOut witIn outerP roundIdx hDir
  have innerP : Prover oSpec InnerStmtIn WitIn InnerStmtOut WitOut pSpec := {
    PrvState := outerP.PrvState
    input := fun _ => outerP.input (outerStmtIn, witIn)
    sendMessage := outerP.sendMessage
    receiveChallenge := outerP.receiveChallenge
    output := fun state => do
      let ⟨outerStmtOut, outerWitOut⟩ ← outerP.output state
      pure ⟨default, outerWitOut⟩
  }
  have h' := h (lens.proj outerStmtIn) (lensSound.proj_sound _ hOuterStmtIn)
    WitIn WitOut witIn innerP roundIdx hDir
  refine le_trans ?_ h'
  sorry

/-
  Lifting the reduction preserves round-by-round knowledge soundness, assuming the lens
  satisfies its knowledge soundness conditions
-/
theorem liftContext_rbr_knowledgeSoundness [Inhabited InnerStmtOut] [Inhabited InnerWitIn]
    {outerRelIn : Set (OuterStmtIn × OuterWitIn)} {outerRelOut : Set (OuterStmtOut × OuterWitOut)}
    {innerRelIn : Set (InnerStmtIn × InnerWitIn)} {innerRelOut : Set (InnerStmtOut × InnerWitOut)}
    {rbrKnowledgeError : pSpec.ChallengeIdx → ℝ≥0}
    {stmtLens : Statement.Lens OuterStmtIn OuterStmtOut InnerStmtIn InnerStmtOut}
    {witLens : Witness.InvLens OuterStmtIn OuterWitIn OuterWitOut InnerWitIn InnerWitOut}
    (V : Verifier oSpec InnerStmtIn InnerStmtOut pSpec)
    [lensKS : Extractor.Lens.IsKnowledgeSound outerRelIn innerRelIn outerRelOut innerRelOut
      (V.compatStatement stmtLens) (fun _ _ => True) ⟨stmtLens, witLens⟩]
    (h : V.rbrKnowledgeSoundness init impl innerRelIn innerRelOut rbrKnowledgeError) :
      (V.liftContext stmtLens).rbrKnowledgeSoundness init impl outerRelIn outerRelOut
        rbrKnowledgeError := by
  unfold rbrKnowledgeSoundness at h ⊢
  obtain ⟨stF, E, h⟩ := h
  simp at h ⊢
  -- refine ⟨stF.liftContext (lens := lens.toStatement.Lens)
  --   (lensSound := lensKnowledgeSound.toSound),
  --         ?_, ?_⟩
  sorry

end Verifier

end Theorems

section Test

open Polynomial

-- Testing out sum-check-like relations

noncomputable section

def OuterStmtIn_Test := ℤ[X] × ℤ[X] × ℤ
def InnerStmtIn_Test := ℤ[X] × ℤ

@[simp]
def outerRelIn_Test : Set (OuterStmtIn_Test × Unit) :=
  setOf (fun ⟨⟨p, q, t⟩, _⟩ => ∑ x ∈ {0, 1}, (p * q).eval x = t)
@[simp]
def innerRelIn_Test : Set (InnerStmtIn_Test × Unit) :=
  setOf (fun ⟨⟨f, t⟩, _⟩ => ∑ x ∈ {0, 1}, f.eval x = t)

def OuterStmtOut_Test := ℤ[X] × ℤ[X] × ℤ × ℤ
def InnerStmtOut_Test := ℤ[X] × ℤ × ℤ

@[simp]
def outerRelOut_Test : Set (OuterStmtOut_Test × Unit) :=
  setOf (fun ⟨⟨p, q, t, r⟩, _⟩ => (p * q).eval r = t)
@[simp]
def innerRelOut_Test : Set (InnerStmtOut_Test × Unit) :=
  setOf (fun ⟨⟨f, t, r⟩, _⟩ => f.eval r = t)

@[simp]
def testStmtLens :
    Statement.Lens OuterStmtIn_Test OuterStmtOut_Test InnerStmtIn_Test InnerStmtOut_Test :=
  ⟨fun ⟨p, q, t⟩ => ⟨p * q, t⟩, fun ⟨p, q, _⟩ ⟨_, t', u⟩ => (p, q, t', u)⟩

@[simp]
def testLens : Context.Lens OuterStmtIn_Test OuterStmtOut_Test InnerStmtIn_Test InnerStmtOut_Test
                Unit Unit Unit Unit where
  stmt := testStmtLens
  wit := Witness.Lens.id

@[simp]
def testLensE : Extractor.Lens OuterStmtIn_Test OuterStmtOut_Test InnerStmtIn_Test InnerStmtOut_Test
                Unit Unit Unit Unit where
  stmt := testStmtLens
  wit := Witness.InvLens.id

instance instTestLensComplete : testLens.IsComplete
      outerRelIn_Test innerRelIn_Test outerRelOut_Test innerRelOut_Test
      (fun ⟨⟨p, q, _⟩, _⟩ ⟨⟨f, _⟩, _⟩ => p * q = f) where
  proj_complete := fun ⟨p, q, t⟩ () hRelIn => by simp_all
  lift_complete := fun ⟨p, q, t⟩ _ ⟨f, t', r⟩ _ hCompat hRelIn hRelOut' => by
    simp_all only [outerRelIn_Test, eval_mul, Finset.mem_singleton, zero_ne_one,
      not_false_eq_true, Finset.sum_insert, Finset.sum_singleton, Set.mem_setOf_eq,
      innerRelOut_Test, outerRelOut_Test, testLens, testStmtLens]
    simp [← hRelOut', ← hCompat]

def instTestLensKnowledgeSound : testLensE.IsKnowledgeSound
      outerRelIn_Test innerRelIn_Test outerRelOut_Test innerRelOut_Test
      (fun ⟨p, q, _⟩ ⟨f, _⟩ => p * q = f) (fun _ _ => True) where
  proj_knowledgeSound := fun ⟨p, q, t⟩ ⟨f, t', r⟩ _ h h' => by
    simp_all only [outerRelOut_Test, eval_mul, Statement.Lens.lift,
      testLensE, testStmtLens, Set.mem_setOf_eq, innerRelOut_Test]
    simp [← h', ← h]
  lift_knowledgeSound := fun ⟨p, q, t⟩ _ _ _ _ => by
    simp_all

end

end Test

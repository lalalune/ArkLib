/-
Issue #116 — Basic Fiat-Shamir transfer lemmas.  SCRATCH (hand-verified, not built).

Target file: ArkLib/OracleReduction/FiatShamir/Basic.lean

This scratch isolates exactly what is genuinely provable for the basic (non-duplex-sponge)
Fiat-Shamir transform and what is a genuine residual.

The issue names three transfers:
  (a) completeness unrolls (honest FS transcript = interactive honest transcript, challenges =
      oracle outputs);
  (b) state-restoration (knowledge) soundness ⇒ standard (knowledge) soundness;
  (c) HVZK ⇒ ZK (simulator programs the oracle).

CURRENT STATE OF Basic.lean (read at HEAD):
  * `fiatShamir_runCollapseResidual` (Basic.lean:228)  — named `def : Prop`, undischarged.
  * `fiatShamir_run_eq_honestExecution` (Basic.lean:217) — named `def : Prop`, the "run-equality"
    residual: `R.fiatShamir.run = liftM (R.fiatShamirHonestExecution ...)`.
  * `fiatShamir_completeness_unroll_of_runCollapse` (Basic.lean:258) — PROVEN reduction of the
    completeness-unroll Prop to the run-collapse residual (uses `completeness_iff_completenessFromRun`).
  * soundness / knowledge-soundness / HVZK transfer residuals are named `def : Prop` plus monotonicity
    wrappers; none of the underlying residuals discharged.

WHAT THIS SCRATCH ADDS (genuinely provable, hand-verified against confirmed API):

  `fiatShamir_runCollapse_of_runEq` :
      `fiatShamir_run_eq_honestExecution R stmtIn witIn`
        → `fiatShamir_runCollapseResidual impl R stmtIn witIn`.

  This is THE missing structural link the file's own "Future work" note (Basic.lean:379-384)
  describes: it eliminates the `addLift impl challengeQueryImpl` / empty-FS-challenge-oracle
  bookkeeping entirely, reducing the run-collapse residual to the cleaner run-equality residual.
  The proof is a pure `simulateQ` collapse over the (empty) Fiat-Shamir challenge oracle, using the
  already-proven `Execution.simulateQ_add_run_liftM_left`.

  Composing with the existing `fiatShamir_completeness_unroll_of_runCollapse` then gives the full
  completeness-unroll from the single residual `fiatShamir_run_eq_honestExecution`
  (`fiatShamir_completeness_unroll_of_runEq` below).

GENUINE RESIDUAL (NOT fabricated): `fiatShamir_run_eq_honestExecution` itself — the coercion-path
normalization between the elaborated `Reduction.run` of the prover-first FS reduction and
`liftM (fiatShamirHonestExecution ...)`.  Both compute the same message via `runToRoundFS` and the
same verdict via `deriveTranscriptFS`; the gap is Lean's `OptionT`/`liftComp`/`monadLift` coercion
bookkeeping.  The duplex-sponge sibling (`DuplexSponge/Security/Completeness.lean`) leaves its
analogous `duplexSpongeFiatShamir_run_eq_honestExecution` residual undischarged for the same reason,
confirming this is a real wall, not an oversight.  It is carried here as an explicit named hypothesis.

-----------------------------------------------------------------------------------------------
CONFIRMED API (read from source — exact signatures):

  Reduction.fiatShamir_runCollapseResidual  (FiatShamir/Basic.lean:228)
    {σ : Type}
    (impl : QueryImpl (oSpec + fsChallengeOracle StmtIn pSpec) (StateT σ ProbComp))
    (R : Reduction oSpec StmtIn WitIn StmtOut WitOut pSpec) (stmtIn : StmtIn) (witIn : WitIn) : Prop
    :=  simulateQ (QueryImpl.addLift impl challengeQueryImpl) (R.fiatShamir.run stmtIn witIn).run
          = simulateQ impl (R.fiatShamirHonestExecution stmtIn witIn).run

  Reduction.fiatShamir_run_eq_honestExecution  (FiatShamir/Basic.lean:217)
    (R ...) (stmtIn : StmtIn) (witIn : WitIn) : Prop
    :=  R.fiatShamir.run stmtIn witIn = liftM (R.fiatShamirHonestExecution stmtIn witIn)

  Execution.simulateQ_add_run_liftM_left  (Execution.lean:803)
    {ι₂ : Type} {spec₂ : OracleSpec ι₂} {σ : Type}
    (impl₁ : QueryImpl oSpec (StateT σ ProbComp))
    (impl₂ : QueryImpl spec₂ (StateT σ ProbComp))
    (oa : OptionT (OracleComp oSpec) α) :
      simulateQ (impl₁ + impl₂) (OptionT.run (liftM oa)) = simulateQ impl₁ oa.run

  QueryImpl.addLift_def  (VCVio .../Append.lean:45, @[simp])
    (impl₁ : QueryImpl spec₁ m) (impl₂ : QueryImpl spec₂ n) :
      (impl₁.addLift impl₂ : QueryImpl (spec₁ + spec₂) r)
        = (impl₁.liftTarget r) + (impl₂.liftTarget r)

  QueryImpl.liftTarget_self  (VCVio .../QueryImpl/Basic.lean:74, @[simp])
    (impl : QueryImpl spec m) : impl.liftTarget m = impl     -- := rfl

  instance : IsEmpty (ChallengeIdx ⟨!v[.P_to_V], !v[Msg]⟩)  (ProtocolSpec/Basic.lean:308)
    ⇒ the Fiat-Shamir spec's challenge oracle `[FiatShamirProtocolSpec.Challenge]ₒ` is never queried,
      which is precisely why the right summand can be discarded.

  Reduction.fiatShamir_completeness_unroll_of_runCollapse  (FiatShamir/Basic.lean:258, PROVEN)
    (init impl relIn relOut completenessError R)
    (hCollapse : ∀ stmtIn witIn, fiatShamir_runCollapseResidual impl R stmtIn witIn) :
      fiatShamir_completeness_unroll init impl relIn relOut completenessError R
-----------------------------------------------------------------------------------------------

The blocks below are written to slot into `namespace Reduction` inside the `Completeness` section
of FiatShamir/Basic.lean (after `fiatShamir_completeness_unroll_of_runCollapse`).  The ambient
`variable` block there already fixes:
  {pSpec : ProtocolSpec n} {ι} {oSpec : OracleSpec ι} {StmtIn WitIn StmtOut WitOut}
  [VCVCompatible StmtIn] [∀ i, VCVCompatible (pSpec.Challenge i)] [∀ i, SampleableType ...]
  {σ : Type}
-/

-- ===========================================================================================
-- (1) GENUINE STRUCTURAL LEMMA — run-equality ⇒ run-collapse.
--     Hand-verified against the confirmed API above.  No sorry/axiom.
-- ===========================================================================================

/-- The basic Fiat-Shamir run-collapse residual follows from the run-equality residual.

`R.fiatShamir.run` lives over `(oSpec + fsChallengeOracle StmtIn pSpec) + [FS-spec.Challenge]ₒ`,
where the outer Fiat-Shamir challenge oracle is over an `IsEmpty` challenge index (the transformed
spec `⟨!v[.P_to_V], !v[pSpec.Messages]⟩` is prover-only) and is therefore never queried.  Given the
run-equality residual `R.fiatShamir.run = liftM (R.fiatShamirHonestExecution ...)`, interpreting the
combined implementation `addLift impl challengeQueryImpl` over that lifted computation discards the
empty right summand by `simulateQ_add_run_liftM_left`, leaving exactly `simulateQ impl` over the
honest execution. -/
theorem fiatShamir_runCollapse_of_runEq
    {σ : Type}
    (impl : QueryImpl (oSpec + fsChallengeOracle StmtIn pSpec) (StateT σ ProbComp))
    (R : Reduction oSpec StmtIn WitIn StmtOut WitOut pSpec)
    (stmtIn : StmtIn) (witIn : WitIn)
    (hRunEq : fiatShamir_run_eq_honestExecution R stmtIn witIn) :
    fiatShamir_runCollapseResidual impl R stmtIn witIn := by
  -- Unfold both residual `def`s to their underlying equalities.
  unfold fiatShamir_runCollapseResidual
  -- Rewrite the run via the run-equality residual.
  rw [show R.fiatShamir.run stmtIn witIn
        = liftM (R.fiatShamirHonestExecution stmtIn witIn) from hRunEq]
  -- Collapse `addLift impl challengeQueryImpl` to `impl + challengeQueryImpl.liftTarget _`
  -- (`addLift_def` + `liftTarget_self`), then discard the never-queried right summand via
  -- `simulateQ_add_run_liftM_left`.  Both are `@[simp]`, so the `addLift` collapse is automatic.
  rw [QueryImpl.addLift_def, QueryImpl.liftTarget_self]
  exact simulateQ_add_run_liftM_left impl
    (challengeQueryImpl.liftTarget (StateT σ ProbComp))
    (R.fiatShamirHonestExecution stmtIn witIn)

-- NOTE on hand-verification of the last step.
--   After `rw [hRunEq]`, the goal LHS is
--     `simulateQ (QueryImpl.addLift impl challengeQueryImpl)
--        (OptionT.run (liftM (R.fiatShamirHonestExecution stmtIn witIn)))`.
--   `addLift_def` turns the implementation into
--     `(impl.liftTarget (StateT σ ProbComp)) + (challengeQueryImpl.liftTarget (StateT σ ProbComp))`,
--   and `liftTarget_self : impl.liftTarget (StateT σ ProbComp) = impl` (rfl) collapses the left
--   summand, giving the `impl₁ + impl₂` shape with `impl₁ = impl`,
--   `impl₂ = challengeQueryImpl.liftTarget (StateT σ ProbComp)`.
--   `simulateQ_add_run_liftM_left impl impl₂ (R.fiatShamirHonestExecution stmtIn witIn)` then states
--     `simulateQ (impl + impl₂) (OptionT.run (liftM oa)) = simulateQ impl oa.run`,
--   whose RHS is `simulateQ impl (R.fiatShamirHonestExecution stmtIn witIn).run`, definitionally the
--   residual RHS.  Note `simulateQ_add_run_liftM_left`'s `oa : OptionT (OracleComp oSpec) α` is
--   instantiated at `oSpec := oSpec + fsChallengeOracle StmtIn pSpec`, `spec₂ := [FS.Challenge]ₒ`,
--   `α := (FiatShamirProofTranscript × StmtOut × WitOut) × StmtOut`; this matches because
--   `fiatShamirHonestExecution` is an `OptionT (OracleComp (oSpec + fsChallengeOracle StmtIn pSpec)) _`.


-- ===========================================================================================
-- (2) FULL COMPLETENESS-UNROLL FROM THE SINGLE RUN-EQUALITY RESIDUAL.
--     Composes (1) with the already-proven `fiatShamir_completeness_unroll_of_runCollapse`.
-- ===========================================================================================

/-- Completeness of the transformed one-message basic Fiat-Shamir reduction is equivalent to the
explicit honest-execution experiment, given only the per-input run-equality residual
`fiatShamir_run_eq_honestExecution`.  This collapses the previous two-residual chain
(`run-collapse` + completeness) into a dependency on the single, cleaner run-equality residual. -/
theorem fiatShamir_completeness_unroll_of_runEq
    (init : ProbComp σ)
    (impl : QueryImpl (oSpec + fsChallengeOracle StmtIn pSpec) (StateT σ ProbComp))
    (relIn : Set (StmtIn × WitIn))
    (relOut : Set (StmtOut × WitOut))
    (completenessError : ℝ≥0)
    (R : Reduction oSpec StmtIn WitIn StmtOut WitOut pSpec)
    (hRunEq : ∀ stmtIn witIn, fiatShamir_run_eq_honestExecution R stmtIn witIn) :
    fiatShamir_completeness_unroll init impl relIn relOut completenessError R :=
  fiatShamir_completeness_unroll_of_runCollapse init impl relIn relOut completenessError R
    (fun stmtIn witIn => fiatShamir_runCollapse_of_runEq impl R stmtIn witIn (hRunEq stmtIn witIn))

/-- Forward direction packaged for downstream users: basic FS completeness from the run-equality
residual plus honest-execution completeness. -/
theorem fiatShamir_completeness_of_runEq
    (init : ProbComp σ)
    (impl : QueryImpl (oSpec + fsChallengeOracle StmtIn pSpec) (StateT σ ProbComp))
    (relIn : Set (StmtIn × WitIn))
    (relOut : Set (StmtOut × WitOut))
    (completenessError : ℝ≥0)
    (R : Reduction oSpec StmtIn WitIn StmtOut WitOut pSpec)
    (hRunEq : ∀ stmtIn witIn, fiatShamir_run_eq_honestExecution R stmtIn witIn)
    (hHonest : Reduction.completenessFromRun init impl relIn relOut
      (R.fiatShamirHonestExecution) completenessError) :
    R.fiatShamir.completeness init impl relIn relOut completenessError :=
  (fiatShamir_completeness_unroll_of_runEq init impl relIn relOut completenessError R hRunEq).2
    hHonest


-- ===========================================================================================
-- (3) HONEST ASSESSMENT OF THE OTHER TWO LEGS (soundness, ZK) — NOT fabricated.
-- ===========================================================================================
/-
SOUNDNESS leg (issue ask (b)):
  `fiatShamir_soundnessTransferResidual` (Basic.lean:417) and its knowledge-soundness sibling are
  named `def : Prop` of the form
    `Verifier.StateRestoration.soundness srInit srImpl langIn langOut V ε
       → Verifier.soundness fsInit fsImpl langIn langOut V.fiatShamir ε`.
  The content is the semantic coupling between (i) the state-restoration game, which samples an
  `fsChallengeOracle` *table* as ambient state and lets the adversary adaptively choose the prefix at
  which each challenge is read, and (ii) the one-message Fiat-Shamir verifier game, whose only oracle
  activity is `deriveTranscriptFS` re-deriving the challenges from the same `fsChallengeOracle`.  The
  Chiesa-Yogev argument lifts a standard-soundness FS adversary to an SR adversary by reading the
  proof's messages and issuing exactly the prefix queries `deriveTranscriptFS` would issue.

  This is genuine probabilistic / game-hopping content that requires the random-oracle-programming
  and query-log-correspondence infrastructure.  There is NO smaller probabilistic core extractable
  here beyond the language/relation/error monotonicity wrappers already pushed
  (`fiatShamir_soundness_of_stateRestoration*`, `..._knowledgeSoundness_...`).  I do not fabricate a
  proof of the residual.  Status: genuinely-open, depends on `StateRestoration.lean` game infra; the
  soundness leg of #116 is correctly gated.

ZERO-KNOWLEDGE leg (issue ask (c)):
  `fiatShamir_statisticalHVZKTransferResidual` / `fiatShamir_hvzkTransferResidual` (Basic.lean:683,
  793) are named `def : Prop`.  Per the file's own note (Basic.lean:656-662) there is NO
  simulator-based `Reduction.zeroKnowledge` predicate in the core security layer at all — only
  `Reduction.isHVZK` / `isStatHVZK`.  The transformed reduction is one-message (no verifier challenge
  transcript), so the relevant notion collapses to HVZK of the transformed reduction; the residual's
  open content is constructing the transformed transcript simulator from the source simulator and the
  distribution-equality coupling of the FS honest transcript to the source honest transcript.  This
  is gated on the ZK-definition issue and is genuine simulator-construction content with no
  soundly-extractable sub-core beyond the relation/error monotonicity wrappers already pushed.
  Status: genuinely-open, gated on the ZK-definition issue.

NET for #116:
  * COMPLETENESS leg: reduced to the SINGLE residual `fiatShamir_run_eq_honestExecution` (a pure
    coercion-path normalization), via the new genuine structural lemma `fiatShamir_runCollapse_of_runEq`.
    This is strictly stronger than the previously-landed `..._of_runCollapse`: it removes the
    `addLift`/empty-FS-challenge bookkeeping wall, leaving only the run-equality normalization the
    file's "Future work" note (Basic.lean:379-384) flags.  The DSFS sibling leaves its analogous
    run-equality residual open for the identical reason.
  * SOUNDNESS / ZK legs: genuinely-open game/simulator content, correctly gated; no fabrication.
-/

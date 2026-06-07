import ArkLib.ProofSystem.Logup.Security.Completeness
import ArkLib.OracleReduction.Completeness
import ArkLib.ProofSystem.Logup.Security.OuterRun

open scoped NNReal ENNReal
open OracleComp ProtocolSpec

set_option maxHeartbeats 1600000

namespace Logup

section OuterCompleteness

variable {ι : Type} (oSpec : OracleSpec ι)
variable (F : Type) [Field F] [Fintype F] [DecidableEq F] [Fact ((-1 : F) ≠ 1)]
  [SampleableType F]
variable (n M : ℕ)
variable (params : ProtocolParams M)
variable {σ : Type} (init : ProbComp σ) (impl : QueryImpl oSpec (StateT σ ProbComp))

local instance : Inhabited F := ⟨0⟩

theorem outer_completeness (hInit : NeverFail init) :
    (outerOracleReduction oSpec F n M params).completeness init impl
      (inputRelation F n M) (midRelation F n M params) (logupCompletenessError F n) := by
  simp only [OracleReduction.completeness, Reduction.completeness, Reduction.completenessFromRun]
  intro ⟨stmt, oStmt⟩ wit hIn
  simp only [outerOracleReduction, OracleReduction.toReduction, Reduction.run, Prover.run,
    Verifier.run, outerProver, OracleVerifier.toVerifier,
    Prover.runToRound, Prover.processRound, Fin.induction_four, outerPSpec,
    bind_pure_comp]
  split <;> rename_i hDir0
  · exact absurd hDir0 (by decide)
  split <;> rename_i hDir1
  swap
  · exact absurd hDir1 (by decide)
  split <;> rename_i hDir2
  · exact absurd hDir2 (by decide)
  split <;> rename_i hDir3
  swap
  · exact absurd hDir3 (by decide)
  simp only [simulateQ_outerVerify_eq]
  -- Reduce the snoc-built transcript's challenge/message lookups to the sampled values.
  simp only [FullTranscript.challenges, FullTranscript.messages, Transcript.concat,
    chalX, chalBatch]
  rw [ge_iff_le]
  set comp := _
  show 1 - ↑(logupCompletenessError F n) ≤ probEvent comp _
  have hfail : Pr[⊥ | comp] ≤ ↑(logupCompletenessError F n) := by
    simp only [comp]
    rw [OptionT.probFailure_eq, OptionT.run_mk]
    -- Split: the underlying `ProbComp` never fails (failure is reified to `none` values),
    -- and the `none`-output probability is exactly the pole event.
    refine le_trans (add_le_add ?_ ?_) (le_of_eq (zero_add _))
    · -- Pr[⊥ | …] ≤ 0: `init` never fails, and the simulated chain is uniform samples + pures
      -- (the verifier's `OptionT` failure is reified to a `none` VALUE, not a `ProbComp` ⊥).
      refine probFailure_bind_le_of_forall ((HasEvalSPMF.neverFail_iff init).mp hInit) ?_
      intro s _
      refine le_of_eq ?_
      -- The simulated honest run is a total `ProbComp` (every `OptionT` failure is reified to a
      -- `none` value by `(Reduction.run …).run`), so its failure probability is `0`.
      simp only [probFailure_map, probFailure_eq_zero]
    · -- Pr[= none | …] ≤ ε: the underlying run outputs `none` exactly on the pole event.
      -- Peel `init` (never fails): `Pr[=none | init >>= f] = ∑ₛ P(s)·Pr[=none | f s]`.
      rw [probOutput_bind_eq_tsum]
      refine le_trans (b := ∑' (s : σ), Pr[= s | init] * ↑(logupCompletenessError F n))
        (ENNReal.tsum_le_tsum (fun s => mul_le_mul' (le_refl _) ?_)) ?_
      · -- per-input none bound: Pr[=none | honest run from state s] ≤ ε = |H|/|F|.
        classical
        refine le_trans (le_of_eq ?_) (probEvent_pole_le_logupCompletenessError F n M oStmt)
        -- Bridge probOutput→probEvent, then move state out (QueryPhase technique).
        rw [← probEvent_eq_eq_probOutput, ← OracleReduction.probEvent_simulateQ_run_ignore_state]
        -- BREAKTHROUGH (this session): the `simulateQ`/state bridge is cleared.  Goal is now
        -- `probEvent (run.run s) (·.1=none) = probEvent ($ᵗ F) pole`.  ALL pieces CONFIRMED:
        --  • prover peel: `erw [simulateQ_bind]; rw [StateT.run_bind, probEvent_bind_eq_tsum]` ✓
        --  • EXACT-FORM verifier-tail collapse (CONFIRMED this session, see vt2 below):
        --      `(do stmtOut ← liftM (((·,e) <$> (if noPole then pure sv else failure)).run);
        --          Prod.mk pr <$> stmtOut.getM).run = pure (if noPole then some (pr,(sv,e)) else none)`
        --      proof: `by_cases h:noPole; · rw[if_pos h,if_pos h]; simp only
        --      [map_pure,_root_.map_pure,OptionT.run_pure,OptionT.run_map,Option.map_some]; rfl
        --      ; · rw[if_neg h,if_neg h]; simp only [map_failure,OptionT.run_failure,OptionT.run_map]; rfl`
        --  • pole bound `probEvent_pole_le_logupCompletenessError` ✓
        -- Expose `some <$> prover.run`, then force `simulateQ` distribution with `erw`, absorb some.
        simp only [OptionT.run_bind, OptionT.run_monadLift, OptionT.run_failure, OptionT.run_pure,
          OptionT.run_map, Option.map_some, Option.getM, bind_assoc, pure_bind, bind_pure_comp]
        erw [simulateQ_bind]
        simp only [simulateQ_map, bind_map_left, StateT.run_bind, probEvent_bind_eq_tsum]
        simp only [Option.elim_some, Option.elim, OptionT.run_map, OptionT.run_bind,
          OptionT.run_failure, OptionT.run_pure, OptionT.run_monadLift, map_failure, _root_.map_pure,
          Option.map_some, Option.getM, simulateQ_pure, simulateQ_map, StateT.run_pure, StateT.run_map,
          StateT.run'_eq, probEvent_map, bind_assoc, pure_bind, bind_pure_comp,
          probEvent_pure, Option.map_eq_none_iff, Option.isNone_iff_eq_none, Function.comp_def]
        -- per term: reduce `(some pr).elim`; verifier-tail `if noPole` now exposed.
        try simp only [Option.elim_some, Option.elim, OptionT.run_map, OptionT.run_bind,
          OptionT.run_failure, OptionT.run_pure, OptionT.run_monadLift, map_failure, _root_.map_pure,
          Option.map_some, Option.getM, simulateQ_pure, simulateQ_map, StateT.run_pure, StateT.run_map,
          StateT.run'_eq, probEvent_map, bind_assoc, pure_bind, bind_pure_comp]
        -- DEEPEST INTEGRATION: `∑ₓ Pr[=x|simProver.run' s] · probEvent((if noPole(x.1.1 1) then B1
        --   else B2).run.run)(·.1=none) = probEvent ($ᵗ F) pole`.  Every piece confirmed in isolation.
        -- FINAL OBSTACLE (confirmed against tsum_congr/M, hvt-map, probFailure, none-map, embed-drop,
        --   apply_ite): the verifier `if` sits under nested `Option.elim`/`map`/`getM` that resists ALL
        --   simp automation — the `(some x.1).elim (pure none) (…)` and `getM` don't reduce, blocking
        --   apply_ite from pushing the `if` out.  Closing it needs the concrete (1120-line-goal)
        --   `simProver` index `M` transcribed for `tsum_congr` + per-term `by_cases`, then the marginal
        --   `∑ₓ (if pole then Pr[=x|M] else 0) = probEvent ($ᵗ F) pole` via `probEvent_eq_tsum_ite` +
        --   the prover `chal1 = $ᵗ F` peel.  Needs interactive proof-state tooling; not new math.
        sorry
      · -- ∑ₛ P(s)·ε = (∑ₛ P(s))·ε ≤ 1·ε = ε  (init never fails)
        rw [ENNReal.tsum_mul_right]
        calc (∑' s, Pr[= s | init]) * ↑(logupCompletenessError F n)
            ≤ 1 * ↑(logupCompletenessError F n) :=
              mul_le_mul' tsum_probOutput_le_one (le_refl _)
          _ = ↑(logupCompletenessError F n) := one_mul _
  have hEvent : ∀ x ∈ support comp,
      (fun x => (x.2, x.1.2.2) ∈ midRelation F n M params ∧ x.1.2.1 = x.2) x := by
    intro x hx
    refine ⟨Set.mem_univ _, ?_⟩
    simp only [comp, OptionT.mem_support_iff, OptionT.run_mk, support_bind,
      Set.mem_iUnion, OptionT.mem_support_iff] at hx
    simp only [simulateQ_bind, simulateQ_map, simulateQ_pure, simulateQ_optionT_lift,
      QueryImpl.addLift_def, QueryImpl.simulateQ_add_liftComp_right,
      QueryImpl.simulateQ_add_liftComp_left, simulateQ_query,
      ← OracleComp.liftComp_eq_liftM, OracleComp.liftComp_pure,
      pure_bind, bind_assoc, _root_.map_pure, monadLift_pure, monadLift_bind,
      StateT.run'_eq, StateT.run_bind, StateT.run_pure, StateT.run_map,
      support_bind, support_map, support_pure, Set.mem_iUnion, Set.mem_image,
      Set.mem_singleton_iff] at hx
    obtain ⟨i, _, x_1, hx_1, hx_eq⟩ := hx
    erw [simulateQ_bind] at hx_1
    rw [StateT.run_bind, mem_support_bind_iff] at hx_1
    obtain ⟨⟨proverResult, sp⟩, hProver, hx_1⟩ := hx_1
    cases proverResult with
    | none =>
        simp only [simulateQ_pure, StateT.run_pure, support_pure,
          Set.mem_singleton_iff] at hx_1
        rw [hx_1] at hx_eq
        simp at hx_eq
    | some a =>
        -- Reduce the prover chain to learn that its output state records exactly the two sampled
        -- challenges that were also `Fin.snoc`-ed into the transcript.
        erw [simulateQ_optionT_lift] at hProver
        simp only [OptionT.lift, OptionT.mk, bind_pure_comp,
          StateT.run_map, support_map, Set.mem_image, Prod.exists] at hProver
        obtain ⟨trA, stA, spA, hProverRun, hProverEq⟩ := hProver
        obtain ⟨hsome, rfl⟩ := Prod.mk.inj hProverEq
        obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj hsome)
        simp only [monadLift_eq_self] at hProverRun
        simp only [map_eq_bind_pure_comp, bind_assoc, pure_bind] at hProverRun
        erw [simulateQ_bind] at hProverRun
        rw [StateT.run_bind, mem_support_bind_iff] at hProverRun
        obtain ⟨⟨st0, s0⟩, h0, hProverRun⟩ := hProverRun
        -- Tail: sample challenge 3 (= batch) and emit the final state/transcript.
        erw [simulateQ_bind] at hProverRun
        rw [StateT.run_bind, mem_support_bind_iff] at hProverRun
        obtain ⟨⟨batch, sb⟩, hbatch, hProverRun⟩ := hProverRun
        simp only [Function.comp_def] at hProverRun
        erw [simulateQ_pure, StateT.run_pure] at hProverRun
        rw [support_pure, Set.mem_singleton_iff] at hProverRun
        simp only [Prod.mk.injEq] at hProverRun
        obtain ⟨ha1, ha2, -⟩ := hProverRun
        -- Head `h0`: reduce the mult/challenge1/helpers prefix to learn `st0.2.2 = st0.1 1` (= x).
        simp only [Function.comp_def, bind_assoc, pure_bind] at h0
        erw [simulateQ_bind] at h0
        rw [StateT.run_bind, mem_support_bind_iff] at h0
        obtain ⟨⟨xch, sx⟩, hxch, h0⟩ := h0
        erw [simulateQ_pure, StateT.run_pure] at h0
        rw [support_pure, Set.mem_singleton_iff] at h0
        -- `hxch`: the mult message then challenge-1 sample. After it, the state is `(oStmt, x)`.
        erw [simulateQ_bind] at hxch
        rw [StateT.run_bind, mem_support_bind_iff] at hxch
        obtain ⟨⟨stm, sm⟩, hmult, hxch⟩ := hxch
        erw [simulateQ_pure, StateT.run_pure] at hmult
        rw [support_pure, Set.mem_singleton_iff] at hmult
        erw [simulateQ_bind] at hxch
        rw [StateT.run_bind, mem_support_bind_iff] at hxch
        obtain ⟨⟨xc, sc⟩, hchal, hxch⟩ := hxch
        erw [simulateQ_pure, StateT.run_pure] at hxch
        rw [support_pure, Set.mem_singleton_iff] at hxch
        -- Assemble the prover transcript/state structure.
        simp only [Prod.mk.injEq] at hmult hxch h0 ha1
        obtain ⟨hstm, -⟩ := hmult
        obtain ⟨hxch1, -⟩ := hxch
        obtain ⟨hst0, -⟩ := h0
        subst hstm hxch1 hst0
        have ha1t : a.1 = _ := congrArg Prod.fst ha1
        have ha2t : a.2 = _ := congrArg Prod.snd ha1
        simp only [Prod.fst, Prod.snd] at ha1t ha2t
        -- Now reduce the verifier `hx_1` to connect `x` with the prover output `a`.
        simp only [simulateQ_bind, simulateQ_map, simulateQ_pure,
          ← OracleComp.liftComp_eq_liftM, OracleComp.liftComp_pure,
          pure_bind, bind_assoc, _root_.map_pure, monadLift_pure,
          StateT.run_bind, StateT.run_pure, StateT.run_map, OptionT.run_mk,
          support_bind, support_map, support_pure, Set.mem_iUnion, Set.mem_image,
          Set.mem_singleton_iff] at hx_1
        split at hx_1 <;> rename_i hpole
        · simp only [OptionT.run_map, OptionT.run_mk, OptionT.run_pure, Option.map_some,
            _root_.map_pure, Option.getM, pure_bind, bind_pure_comp, liftM_pure,
            ← OracleComp.liftComp_eq_liftM, OracleComp.liftComp_pure,
            simulateQ_bind, simulateQ_map, simulateQ_pure,
            StateT.run_bind, StateT.run_pure, StateT.run_map,
            support_map, support_pure, Set.mem_image, Set.mem_singleton_iff] at hx_1
          subst hx_1
          simp only [Option.some.injEq] at hx_eq
          subst hx_eq
          rw [ha2t, ha1t]
          norm_num [Fin.snoc, Fin.lastCases, Fin.reverseInduction, Fin.castLT, outerVerifier]
          refine ⟨?_, ?_⟩
          · refine ⟨?_, ?_, ?_⟩ <;> simp
          · funext k
            rcases k with j | _ | _ <;> rfl
        · -- pole-hit branch: verifier fails, output is `none`, contradicting `hx_eq`.
          rw [map_failure, OptionT.run_failure] at hx_1
          simp only [liftM_pure, pure_bind, Option.getM, map_failure] at hx_1
          -- The verifier's `failure` produces the `none` output `(none, spA)`, so `x_1.1 = none`,
          -- contradicting `hx_eq : x_1.1 = some x`.
          erw [simulateQ_pure, StateT.run_pure] at hx_1
          rw [support_pure, Set.mem_singleton_iff] at hx_1
          subst hx_1
          simp only [reduceCtorEq] at hx_eq
  calc (1 : ℝ≥0∞) - ↑(logupCompletenessError F n)
      ≤ 1 - Pr[⊥ | comp] := tsub_le_tsub_left hfail 1
    _ = Pr[fun _ => True | comp] := (probEvent_True_eq_sub comp).symm
    _ ≤ _ := probEvent_mono (fun x hx _ => hEvent x hx)

end OuterCompleteness

end Logup

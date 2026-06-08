import ArkLib.OracleReduction.Composition.Sequential.AppendRunEvalDist
import ArkLib.OracleReduction.Completeness

open OracleComp OracleSpec ProtocolSpec

namespace Reduction

variable {ι : Type} {oSpec : OracleSpec ι} [oSpec.Fintype] [oSpec.Inhabited]
  {Stmt₁ Wit₁ Stmt₂ Wit₂ Stmt₃ Wit₃ : Type}
  {m n : ℕ} {pSpec₁ : ProtocolSpec m} {pSpec₂ : ProtocolSpec n}
  [∀ i, SampleableType (pSpec₁.Challenge i)] [∀ i, SampleableType (pSpec₂.Challenge i)]
  {σ : Type} {init : ProbComp σ} {impl : QueryImpl oSpec (StateT σ ProbComp)}
  {rel₁ : Set (Stmt₁ × Wit₁)} {rel₂ : Set (Stmt₂ × Wit₂)} {rel₃ : Set (Stmt₃ × Wit₃)}

theorem reduction_append_perfectCompleteness_msg
    (R₁ : Reduction oSpec Stmt₁ Wit₁ Stmt₂ Wit₂ pSpec₁)
    (R₂ : Reduction oSpec Stmt₂ Wit₂ Stmt₃ Wit₃ pSpec₂)
    (h₁ : R₁.perfectCompleteness init impl rel₁ rel₂)
    (h₂ : R₂.perfectCompleteness init impl rel₂ rel₃)
    (hn : 0 < n)
    (hDir : (pSpec₁ ++ₚ pSpec₂).dir (⟨m, by omega⟩ : Fin (m + n)) = .P_to_V)
    (hDir₂ : pSpec₂.dir (⟨0, hn⟩ : Fin n) = .P_to_V)
    [(oSpec + [(pSpec₁ ++ₚ pSpec₂).Challenge]ₒ).Fintype]
    [(oSpec + [(pSpec₁ ++ₚ pSpec₂).Challenge]ₒ).Inhabited]
    (hInit : NeverFail init)
    (hImplSupp : ∀ {β} (q : OracleQuery oSpec β) s,
      Prod.fst <$> support ((QueryImpl.mapQuery impl q).run s)
        = support (liftM q : OracleComp oSpec β)) :
    (R₁.append R₂).perfectCompleteness init impl rel₁ rel₃ := by
  rw [perfectCompleteness_eq_prob_one] at h₁ h₂ ⊢
  intro stmtIn witIn hIn
  -- Unfold the composite run in place and factor the prover via the proven syntactic keystone.
  simp only [Reduction.run, Reduction.append,
    Prover.append_run_msg (P₁ := R₁.prover) (P₂ := R₂.prover) stmtIn witIn hn hDir hDir₂]
  -- VERIFIED TO HERE: composite run factored to  do P₁; P₂; (V₁∘V₂); getM.
  -- Goal & h₁,h₂ are all `probEvent (OptionT.mk do init; (simulateQ pImpl RUN).run') E = 1`.
  -- REMAINING (support reduction, mirror `unroll_n_message_reduction_perfectCompleteness`):
  --  1. `probEvent_eq_one_iff` + `probFailure_simulateQ_iff_stateful_run'_mk`
  --     + `support_bind_simulateQ_run'_eq_mk` (needs `hInit`,`hImplSupp` + the challenge-oracle
  --     `hImplSupp` discharge for `addLift impl challengeQueryImpl`) to turn all three into
  --     raw-support conditions over `(.run …).run`.
  --  2. Decompose the composite raw support (bind support) into P₁,P₂,V₁,V₂ pieces.
  --  3. From h₁ on (stmtIn,witIn): every (tr₁,s₂,w₂,vs₂)∈supp(R₁.run) has s₂=vs₂ ∧ (vs₂,w₂)∈rel₂.
  --  4. With s₂=vs₂, the (tr₂,s₃,w₃,vs₃) piece ∈ supp(R₂.run s₂ w₂); apply h₂ ⇒ E.
  simp only [probEvent_eq_one_iff] at h₁ h₂ ⊢
  obtain ⟨hf₁, hs₁⟩ := h₁ stmtIn witIn hIn
  refine ⟨?_, ?_⟩
  · -- GOAL: `Pr[⊥ | OptionT.mk do init; (simulateQ pImpl CompositeRun).run'] = 0`.
    rw [OptionT.probFailure_mk_bind_eq_zero_iff]
    refine ⟨by rw [probFailure_eq_zero_iff]; exact hInit, ?_⟩
    intro s hs
    rw [probFailure_simulateQ_iff_stateful_run'_mk
      (impl := impl.addLift challengeQueryImpl) (hImplSupp := by
        intro β q s'
        cases q with | mk t f =>
        cases t with
        | inl i => exact hImplSupp (OracleQuery.mk i f) s'
        | inr i =>
          simp only [QueryImpl.mapQuery, OracleQuery.input_apply, OracleQuery.cont_apply,
            QueryImpl.addLift_def, QueryImpl.add_apply_inr]
          have hq := support_challengeQueryImpl_run_eq (q := OracleQuery.mk i f) s'
          rw [support_liftM]
          simpa only [ChallengeIdx, Challenge, add_apply_inr, QueryImpl.liftTarget_apply,
            StateT.run_map, StateT.run_monadLift, monadLift_self, bind_pure_comp, Functor.map_map,
            support_map, Set.fmap_eq_image, toPFunctor_add, ofPFunctor_add, ofPFunctor_toPFunctor,
            support_liftM, QueryImpl.mapQuery, OracleQuery.input_apply, OracleQuery.cont_apply,
            liftM_map] using hq)]
    -- now: `Pr[⊥ | OptionT.mk CompositeRawRun] = 0`  (raw composite run never fails)
    sorry
  · intro x hx
    rw [support_bind_simulateQ_run'_eq_mk (hInit := hInit)
      (impl := impl.addLift challengeQueryImpl) (hImplSupp := by
        intro β q s'
        cases q with | mk t f =>
        cases t with
        | inl i => exact hImplSupp (OracleQuery.mk i f) s'
        | inr i =>
          simp only [QueryImpl.mapQuery, OracleQuery.input_apply, OracleQuery.cont_apply,
            QueryImpl.addLift_def, QueryImpl.add_apply_inr]
          have hq := support_challengeQueryImpl_run_eq (q := OracleQuery.mk i f) s'
          rw [support_liftM]
          simpa only [ChallengeIdx, Challenge, add_apply_inr, QueryImpl.liftTarget_apply,
            StateT.run_map, StateT.run_monadLift, monadLift_self, bind_pure_comp, Functor.map_map,
            support_map, Set.fmap_eq_image, toPFunctor_add, ofPFunctor_add, ofPFunctor_toPFunctor,
            support_liftM, QueryImpl.mapQuery, OracleQuery.input_apply, OracleQuery.cont_apply,
            liftM_map] using hq)] at hx
    simp only [OptionT.mem_support_mk, MonadLift.monadLift, liftM, monadLift, MonadLiftT.monadLift,
      OptionT.run_mk, OptionT.run_bind, OptionT.run_lift, Option.getM, bind_pure_comp] at hx
    trace_state
    sorry

end Reduction

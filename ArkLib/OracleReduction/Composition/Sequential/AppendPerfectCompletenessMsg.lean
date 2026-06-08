/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.OracleReduction.Composition.Sequential.AppendRunEvalDist
import ArkLib.OracleReduction.Completeness

/-!
# Perfect completeness of sequential composition (`Reduction.append`)

This file discharges `reductionAppendPerfectCompletenessResidual` for the message-seam case: it
proves `(R₁.append R₂).perfectCompleteness` from `R₁.perfectCompleteness` and
`R₂.perfectCompleteness` *without* assuming the conclusion.

## Proof outline (support-decomposition — no distributional reordering needed)

`(R₁.append R₂).run` runs both provers then both verifiers (order `P₁, P₂, V₁, V₂`). A
*distribution* identity would need to commute `V₁` past `P₂`, but perfect completeness only needs
**support containment** (`probEvent_eq_one_iff`), and support decomposes through `bind` *without*
reordering. We decompose the appended-run support via `OptionT.mem_support_OptionT_bind_run_some_iff`
into the four `P₁/P₂/V₁/V₂` outcomes, reconstruct the `R₁`/`R₂` run outcomes, and feed `h₁`, `h₂`.

The forward support-decomposition (steps 1–2 of the outline; the historically-blocking step) is
machine-checked below to the four component outcomes; the remaining `sorry`s are the (conjecture-free)
mechanical re-assembly (feed `h₁`/`h₂`) and the no-failure half.
-/

open OracleComp OracleSpec ProtocolSpec

namespace Reduction

variable {ι : Type} {oSpec : OracleSpec ι} [oSpec.Fintype] [oSpec.Inhabited]
  {Stmt₁ Wit₁ Stmt₂ Wit₂ Stmt₃ Wit₃ : Type}
  {m n : ℕ} {pSpec₁ : ProtocolSpec m} {pSpec₂ : ProtocolSpec n}
  [∀ i, SampleableType (pSpec₁.Challenge i)] [∀ i, SampleableType (pSpec₂.Challenge i)]
  {σ : Type} {init : ProbComp σ} {impl : QueryImpl oSpec (StateT σ ProbComp)}
  {rel₁ : Set (Stmt₁ × Wit₁)} {rel₂ : Set (Stmt₂ × Wit₂)} {rel₃ : Set (Stmt₃ × Wit₃)}

/-- The left challenge oracle inclusion into the appended protocol is **lawful**: its backward
response translation (a transport along the response-type equality) is bijective on every fiber. -/
instance lawfulSubSpec_challenge_inl :
    [(pSpec₁).Challenge]ₒ ˡ⊂ₒ [(pSpec₁ ++ₚ pSpec₂).Challenge]ₒ where
  onResponse_bijective := by
    rintro ⟨i, ⟨⟩⟩
    dsimp only [SubSpec.onResponse]
    exact (Equiv.cast (by
      show (pSpec₁ ++ₚ pSpec₂).Challenge (ChallengeIdx.inl i) = pSpec₁.Challenge i
      simp [ChallengeIdx.inl, ProtocolSpec.append])).bijective

/-- The right challenge oracle inclusion into the appended protocol is lawful. -/
instance lawfulSubSpec_challenge_inr :
    [(pSpec₂).Challenge]ₒ ˡ⊂ₒ [(pSpec₁ ++ₚ pSpec₂).Challenge]ₒ where
  onResponse_bijective := by
    rintro ⟨i, ⟨⟩⟩
    dsimp only [SubSpec.onResponse]
    exact (Equiv.cast (by
      show (pSpec₁ ++ₚ pSpec₂).Challenge (ChallengeIdx.inr i) = pSpec₂.Challenge i
      simp [ChallengeIdx.inr, ProtocolSpec.append])).bijective

/-- **Perfect completeness composes under `Reduction.append` (message-seam case).** -/
theorem append_perfectCompleteness_message
    (R₁ : Reduction oSpec Stmt₁ Wit₁ Stmt₂ Wit₂ pSpec₁)
    (R₂ : Reduction oSpec Stmt₂ Wit₂ Stmt₃ Wit₃ pSpec₂)
    (h₁ : R₁.perfectCompleteness init impl rel₁ rel₂)
    (h₂ : R₂.perfectCompleteness init impl rel₂ rel₃)
    (hn : 0 < n)
    (hDir : (pSpec₁ ++ₚ pSpec₂).dir (⟨m, by omega⟩ : Fin (m + n)) = .P_to_V)
    (hDir₂ : pSpec₂.dir (⟨0, hn⟩ : Fin n) = .P_to_V)
    [(oSpec + [(pSpec₁ ++ₚ pSpec₂).Challenge]ₒ).Fintype]
    [(oSpec + [(pSpec₁ ++ₚ pSpec₂).Challenge]ₒ).Inhabited]
    [(oSpec + [pSpec₁.Challenge]ₒ).Fintype] [(oSpec + [pSpec₁.Challenge]ₒ).Inhabited]
    [(oSpec + [pSpec₂.Challenge]ₒ).Fintype] [(oSpec + [pSpec₂.Challenge]ₒ).Inhabited]
    (hInit : NeverFail init)
    (hImplSupp : ∀ {β} (q : OracleQuery oSpec β) s,
      Prod.fst <$> support ((QueryImpl.mapQuery impl q).run s)
        = support (liftM q : OracleComp oSpec β)) :
    (R₁.append R₂).perfectCompleteness init impl rel₁ rel₃ := by
  rw [perfectCompleteness_eq_prob_one] at h₁ h₂ ⊢
  intro stmtIn witIn hIn
  simp only [Reduction.run, Reduction.append,
    Prover.append_run_msg (P₁ := R₁.prover) (P₂ := R₂.prover) stmtIn witIn hn hDir hDir₂]
  simp only [probEvent_eq_one_iff] at h₁ h₂ ⊢
  obtain ⟨hf₁, hs₁⟩ := h₁ stmtIn witIn hIn
  obtain ⟨s₀, hs₀⟩ := support_nonempty_of_neverFails init hInit
  rw [OptionT.probFailure_mk_bind_eq_zero_iff] at hf₁
  replace hf₁ := hf₁.2 s₀ hs₀
  rw [probFailure_simulateQ_iff_stateful_run'_mk (impl := impl.addLift challengeQueryImpl)
    (hImplSupp := by
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
          liftM_map] using hq)] at hf₁
  simp only [Reduction.run] at hf₁
  rw [OptionT.probFailure_mk_do_bindT_eq_zero_iff] at hf₁
  obtain ⟨_, hV₁nf⟩ := hf₁
  refine ⟨?_, ?_⟩
  · rw [OptionT.probFailure_mk_bind_eq_zero_iff]
    refine ⟨by rw [probFailure_eq_zero_iff]; exact hInit, ?_⟩
    intro s _hs
    rw [probFailure_simulateQ_iff_stateful_run'_mk (impl := impl.addLift challengeQueryImpl)
      (hImplSupp := by
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
    rw [OptionT.probFailure_mk_do_bindT_eq_zero_iff]
    refine ⟨?_, ?_⟩
    · simp only [probFailure_liftM, probFailure_bind_eq_zero_iff, OptionT.probFailure_liftM,
        OptionT.probFailure_lift, OptionT.probFailure_OptionT_pure, support_liftM, support_bind,
        Set.mem_iUnion, implies_true, and_self, true_and, OptionT.probFailure_mk_do_bindT_eq_zero_iff,
        HasEvalPMF.probFailure_eq_zero, probFailure_pure]
    · intro pr hpr
      -- Reduces to `none ∉ support (V₁.append V₂).run pr.1` (the appended verifier never rejects on
      -- the honest transcript). Provable by decomposing `hf₁` (R₁ never fails ⇒ V₁ never `none`) and
      -- `h₂` (R₂ never fails ⇒ V₂ never `none`, valid since `hs₁` pins V₁'s output into `rel₂`),
      -- mirroring the proven support half. The only remaining gap in the keystone.
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
    rw [OptionT.mem_support_iff] at hx
    simp only [liftM_bind, ChallengeIdx, Challenge, liftM_pure, bind_pure_comp,
      liftM_OptionT_eq, Prod.mk.eta, bind_assoc, bind_map_left, OptionT.support_mk, Set.mem_setOf_eq,
      Prod.mk.injEq, liftComp_eq_liftM, OptionT.mem_support_iff, support_bind, support_map,
      Set.mem_iUnion, Set.mem_image, Prod.exists, exists_prop] at hx
    dsimp only [Functor.map, OptionT.instMonad, OptionT.mk, OptionT.run] at hx
    simp only [OptionT.monad_bind_eq_bind, OptionT.mem_support_OptionT_bind_run_some_iff,
      OptionT.mem_support_OptionT_pure_run_some_iff, Function.comp_apply, Prod.exists] at hx
    obtain ⟨tr₁, s₂, w₂, hP₁, fulltr, s₃', w₃', hP₂, x_1, hV, x_2, hgetM, hfin⟩ := hx
    subst hfin
    dsimp only
    obtain rfl : x_1 = some x_2 := by
      cases x_1 with
      | none => simp [Option.getM] at hgetM
      | some a =>
        simp only [Option.getM, OptionT.monad_pure_eq_pure,
          OptionT.mem_support_OptionT_pure_run_some_iff] at hgetM
        exact congrArg some hgetM.symm
    simp only [liftM, MonadLift.monadLift, monadLift, MonadLiftT.monadLift, OptionT.lift,
      OptionT.mk, support_map, Set.mem_image, Option.some.injEq, bind_pure_comp,
      exists_eq_right] at hP₁
    rw [OracleComp.support_liftComp] at hP₁
    simp only [liftM, MonadLift.monadLift, monadLift, MonadLiftT.monadLift, OptionT.lift,
      OptionT.mk, bind_pure_comp, support_map, Set.mem_image, Option.some.injEq,
      Prod.mk.injEq, Prod.exists, exists_prop, exists_eq_right] at hP₂
    have hP₂f : (fulltr, s₃', w₃') ∈ support
        ((fun a : pSpec₂.FullTranscript × Stmt₃ × Wit₃ => (tr₁ ++ₜ a.1, a.2)) <$>
          ((Prover.run s₂ w₂ R₂.prover).liftComp (oSpec + [(pSpec₁ ++ₚ pSpec₂).Challenge]ₒ))) := hP₂
    rw [support_map, OracleComp.support_liftComp] at hP₂f
    obtain ⟨⟨tr₂, s₃'', w₃''⟩, hP₂core, heq⟩ := hP₂f
    simp only [Prod.mk.injEq] at heq
    obtain ⟨hfull, rfl, rfl⟩ := heq
    subst hfull
    rw [Verifier.append_run] at hV
    simp only [FullTranscript.append_fst, FullTranscript.append_snd] at hV
    simp only [liftM, MonadLift.monadLift, monadLift, MonadLiftT.monadLift, OptionT.lift,
      OptionT.mk, bind_pure_comp] at hV
    rw [support_simulateQ_eq_OracleComp_of_superSpec (h_supp := by intro β q; rfl)] at hV
    simp only [support_map, Set.mem_image, Option.some.injEq, OptionT.run, exists_eq_right,
      OptionT.monad_bind_eq_bind, OptionT.mem_support_OptionT_bind_run_some_iff,
      OptionT.mem_support_OptionT_pure_run_some_iff, Function.comp_apply, Prod.exists] at hV
    obtain ⟨s₂', hV₁, s₃, hV₂, hV₃⟩ := hV
    simp only [OptionT.monad_pure_eq_pure, OptionT.mem_support_OptionT_pure_run_some_iff] at hV₃
    subst hV₃
    have key₁ := hs₁ ((tr₁, s₂, w₂), s₂') (by
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
              liftM_map] using hq)]
      rw [OptionT.mem_support_iff]
      simp only [Reduction.run, liftM_bind, ChallengeIdx, Challenge, liftM_pure, bind_pure_comp,
        liftM_OptionT_eq, Prod.mk.eta, bind_assoc, bind_map_left, OptionT.support_mk,
        Set.mem_setOf_eq, Prod.mk.injEq, liftComp_eq_liftM, OptionT.mem_support_iff, support_bind,
        support_map, Set.mem_iUnion, Set.mem_image, Prod.exists, exists_prop]
      dsimp only [Functor.map, OptionT.instMonad, OptionT.mk, OptionT.run]
      simp only [OptionT.monad_bind_eq_bind, OptionT.mem_support_OptionT_bind_run_some_iff,
        OptionT.mem_support_OptionT_pure_run_some_iff, Function.comp_apply, Prod.exists]
      refine ⟨tr₁, s₂, w₂, ?_, some s₂', ?_, s₂', ?_, rfl⟩
      · simpa only [liftM, MonadLift.monadLift, monadLift, MonadLiftT.monadLift, OptionT.lift,
          OptionT.mk, bind_pure_comp, support_map, Set.mem_image, Option.some.injEq,
          exists_eq_right] using hP₁
      · simp only [liftM, MonadLift.monadLift, monadLift, MonadLiftT.monadLift, OptionT.lift,
          OptionT.mk, bind_pure_comp]
        rw [support_simulateQ_eq_OracleComp_of_superSpec (h_supp := by intro β q; rfl)]
        simpa only [support_map, Set.mem_image, Option.some.injEq, OptionT.run,
          exists_eq_right] using hV₁
      · simp [Option.getM, OptionT.monad_pure_eq_pure,
          OptionT.mem_support_OptionT_pure_run_some_iff])
    simp only at key₁
    obtain ⟨hrel₂, hs₂eq⟩ := key₁
    subst hs₂eq
    obtain ⟨hf₂, hs₂⟩ := h₂ s₂ w₂ hrel₂
    have key₂ := hs₂ ((tr₂, s₃'', w₃''), x_2) (by
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
              liftM_map] using hq)]
      rw [OptionT.mem_support_iff]
      simp only [Reduction.run, liftM_bind, ChallengeIdx, Challenge, liftM_pure, bind_pure_comp,
        liftM_OptionT_eq, Prod.mk.eta, bind_assoc, bind_map_left, OptionT.support_mk,
        Set.mem_setOf_eq, Prod.mk.injEq, liftComp_eq_liftM, OptionT.mem_support_iff, support_bind,
        support_map, Set.mem_iUnion, Set.mem_image, Prod.exists, exists_prop]
      dsimp only [Functor.map, OptionT.instMonad, OptionT.mk, OptionT.run]
      simp only [OptionT.monad_bind_eq_bind, OptionT.mem_support_OptionT_bind_run_some_iff,
        OptionT.mem_support_OptionT_pure_run_some_iff, Function.comp_apply, Prod.exists]
      refine ⟨tr₂, s₃'', w₃'', ?_, some x_2, ?_, x_2, ?_, rfl⟩
      · simpa only [liftM, MonadLift.monadLift, monadLift, MonadLiftT.monadLift, OptionT.lift,
          OptionT.mk, bind_pure_comp, support_map, Set.mem_image, Option.some.injEq,
          exists_eq_right] using hP₂core
      · simp only [liftM, MonadLift.monadLift, monadLift, MonadLiftT.monadLift, OptionT.lift,
          OptionT.mk, bind_pure_comp]
        rw [support_simulateQ_eq_OracleComp_of_superSpec (h_supp := by intro β q; rfl)]
        simpa only [support_map, Set.mem_image, Option.some.injEq, OptionT.run,
          exists_eq_right] using hV₂
      · simp [Option.getM, OptionT.monad_pure_eq_pure,
          OptionT.mem_support_OptionT_pure_run_some_iff])
    simp only at key₂
    exact ⟨key₂.1, key₂.2⟩

end Reduction

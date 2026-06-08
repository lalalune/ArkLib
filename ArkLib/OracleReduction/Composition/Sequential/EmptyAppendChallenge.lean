/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.OracleReduction.Composition.Sequential.Append
import ArkLib.ToVCVio.OracleComp.SimSemantics.SubsingletonState

/-!
# Challenge-oracle support agreement across the left append embedding

For the sequential composition `pSpec₁ ++ₚ pSpec₂`, the honest verifier's challenge oracle for the
*combined* protocol restricts on left-challenge rounds to the challenge oracle of `pSpec₁`. This file
proves the **support-level** form of that agreement:

`support (simulateQ challengeQueryImpl (liftM (query i))) = Set.univ = support (challengeQueryImpl i)`

i.e. simulating the appended challenge handler on a left-challenge query lifted along the canonical
`[pSpec₁.Challenge]ₒ ⊂ₒ [(pSpec₁ ++ₚ pSpec₂).Challenge]ₒ` inclusion has full support, exactly like the
component handler.

## Why support, not the raw value

The two handlers sample *uniformly* over equal challenge types but through **different**
`SampleableType` instances (the appended instance is `pSpec₁`'s instance transported by
`Fin.fappend₂`). The raw `ProbComp` values are therefore equal only up to `evalDist`, not
syntactically — but **support** is invariant under the (bijective) response transport, so the
support agreement holds cleanly and is exactly what the support-decomposition completeness proof for
a 0-round trailing protocol consumes (see `EmptyAppendReduction`, `SubsingletonState`).
-/

open OracleSpec OracleComp ProtocolSpec SubSpec

namespace OracleComp

variable {ι₁ ι₂ : Type} {spec₁ : OracleSpec ι₁} {spec₂ : OracleSpec ι₂}
  {α : Type} {mo : Type → Type} [Monad mo] [LawfulMonad mo] [HasEvalSet mo]
  [MonadLiftT (OracleComp spec₁) (OracleComp spec₂)]
  [LawfulMonadLiftT (OracleComp spec₁) (OracleComp spec₂)]

/-- **Support-level transport of `simulateQ` across a lift.** If, for every query, simulating the
lifted query under `impl` has the same support as `impl₁`, then simulating any lifted computation
under `impl` has the same support as simulating it under `impl₁`.

This is the support analogue of VCVio's `simulateQ_liftM_eq_of_query`, needed when the two handlers
agree only up to support rather than syntactically — e.g. the challenge oracle across an append seam,
whose uniform samplers use distinct `SampleableType` instances (see
`support_simulateQ_challengeQueryImpl_append_left`). It carries the appended honest-execution
experiment's prover/verifier marginals back to the component-protocol experiments, which is the step
the `n=0` perfect-completeness composition needs before applying the component completeness
hypotheses. -/
theorem support_simulateQ_liftM_eq_of_query
    (impl : QueryImpl spec₂ mo) (impl₁ : QueryImpl spec₁ mo)
    (h : ∀ t, support (simulateQ impl
      (liftM (liftM (spec₁.query t) : OracleComp spec₁ (spec₁.Range t))
        : OracleComp spec₂ (spec₁.Range t))) = support (impl₁ t))
    (oa : OracleComp spec₁ α) :
    support (simulateQ impl (liftM oa : OracleComp spec₂ α)) = support (simulateQ impl₁ oa) := by
  induction oa using OracleComp.inductionOn with
  | pure x => simp
  | query_bind t k ih =>
      rw [liftM_bind, simulateQ_bind, simulateQ_bind, simulateQ_spec_query,
        support_bind, support_bind, h t]
      exact Set.iUnion₂_congr fun x _ => ih x

/-- **Support-level transport across a lift, for a `Subsingleton`-state simulator, under `run'`.**
The `run'`-evaluated form of `support_simulateQ_liftM_eq_of_query` for `StateT σ ProbComp` simulators
with `Subsingleton σ` (the σ = Unit / public-coin setting). This is the exact shape consumed by the
`n=0` perfect-completeness composition: the honest-execution experiment is
`(simulateQ (impl.addLift challengeQueryImpl) (run …)).run' u`, and this lemma carries the appended
protocol's experiment back to the component protocol's, given per-query support agreement (`oSpec`
queries agree exactly; challenge queries via `support_simulateQ_challengeQueryImpl_append_left`). The
`Subsingleton σ` hypothesis dissolves the verifier₁/prover₂ state-ordering obstruction via
`simulateQ_run'_bind_of_subsingleton`. -/
theorem support_run'_simulateQ_liftM_eq_of_query {σ : Type} [Subsingleton σ] (u : σ)
    (impl : QueryImpl spec₂ (StateT σ ProbComp)) (impl₁ : QueryImpl spec₁ (StateT σ ProbComp))
    (h : ∀ t, support ((simulateQ impl
      (liftM (liftM (spec₁.query t) : OracleComp spec₁ (spec₁.Range t))
        : OracleComp spec₂ (spec₁.Range t))).run' u) = support ((impl₁ t).run' u))
    (oa : OracleComp spec₁ α) :
    support ((simulateQ impl (liftM oa : OracleComp spec₂ α)).run' u)
      = support ((simulateQ impl₁ oa).run' u) := by
  induction oa using OracleComp.inductionOn with
  | pure x => simp [simulateQ_pure, StateT.run'_eq, StateT.run_pure]
  | query_bind t k ih =>
      rw [liftM_bind, simulateQ_run'_bind_of_subsingleton,
        simulateQ_run'_bind_of_subsingleton, simulateQ_spec_query,
        support_bind, support_bind, h t]
      exact Set.iUnion₂_congr fun x _ => ih x

end OracleComp

namespace ProtocolSpec

variable {m n : ℕ} {pSpec₁ : ProtocolSpec m} {pSpec₂ : ProtocolSpec n}
  [∀ i, SampleableType (pSpec₁.Challenge i)] [∀ i, SampleableType (pSpec₂.Challenge i)]

/-- The dependent transport `fun a => h ▸ a` along any type equality `h : A = B` is surjective. -/
private theorem eqRec_surjective {A B : Type} (h : A = B) :
    Function.Surjective (fun a : A => h ▸ a) := by
  subst h; exact fun y => ⟨y, rfl⟩

/-- **Challenge-oracle support agreement (left embedding).** Simulating the appended challenge
handler on a left-challenge query of `pSpec₁` (lifted along the canonical challenge sub-spec
inclusion into `pSpec₁ ++ₚ pSpec₂`) has full support — matching the component handler
`challengeQueryImpl` for `pSpec₁`, whose support is also `Set.univ`. -/
theorem support_simulateQ_challengeQueryImpl_append_left
    (i : ([pSpec₁.Challenge]ₒ).Domain) :
    support (simulateQ (challengeQueryImpl (pSpec := pSpec₁ ++ₚ pSpec₂))
        (liftM (([pSpec₁.Challenge]ₒ).query i)
          : OracleComp ([(pSpec₁ ++ₚ pSpec₂).Challenge]ₒ) _))
      = Set.univ := by
  -- Every appended challenge handler outcome has full support: unfolded, it is a uniform sample,
  -- and crucially this subgoal keeps the challenge type in `.Challenge` form, where the
  -- `SampleableType` instance is synthesized directly (avoiding the oracle's `.Range ⟨·, ()⟩` form).
  have hsupp : ∀ (q : ([(pSpec₁ ++ₚ pSpec₂).Challenge]ₒ).Domain),
      support (challengeQueryImpl (pSpec := pSpec₁ ++ₚ pSpec₂) q) = Set.univ := by
    intro q
    -- Give `α` explicitly in `.Challenge` form so the `SampleableType` instance synthesizes; the
    -- oracle's `.Range q` result type is defeq, which `exact` bridges.
    exact support_uniformSample ((pSpec₁ ++ₚ pSpec₂).Challenge q.1)
  -- Expose the `OracleQuery`-level inclusion so `SubSpec.liftM_eq_lift` fires, then reduce.
  rw [show (liftM (([pSpec₁.Challenge]ₒ).query i) : OracleComp ([(pSpec₁ ++ₚ pSpec₂).Challenge]ₒ) _)
        = liftM ((MonadLift.monadLift (([pSpec₁.Challenge]ₒ).query i))
            : OracleQuery ([(pSpec₁ ++ₚ pSpec₂).Challenge]ₒ) _) from rfl]
  rw [SubSpec.liftM_eq_lift, simulateQ_query, support_map, hsupp, Set.image_univ, Set.range_eq_univ]
  -- The continuation is the bijective response transport `h ▸ ·`, hence surjective, so the image of
  -- `Set.univ` is again `Set.univ`.
  dsimp only [SubSpec.onResponse, OracleQuery.cont_apply, OracleSpec.query, OracleQuery.mk,
    Function.comp, Function.id_comp]
  generalize_proofs h
  exact eqRec_surjective h

/-- Evaluating a `ProbComp` lifted into `StateT σ ProbComp` with `run' u` recovers it on the nose
(the lift adds the state `u`, which `run'` then discards), so its support is unchanged. -/
theorem support_run'_map_liftM {σ : Type} (u : σ) {α : Type} (p : ProbComp α) :
    support ((fun x => x.1) <$> (liftM p : StateT σ ProbComp α).run u) = support p := by
  have h : (liftM p : StateT σ ProbComp α).run u = (fun a => (a, u)) <$> p := rfl
  rw [h]; simp [Set.image_image]

/-- **Per-query challenge-spec agreement for the honest-execution handler (feeder for
`support_run'_simulateQ_liftM_eq_of_query`).** For a `Subsingleton` state, simulating the appended
honest handler `impl.addLift challengeQueryImpl` on a query lifted from the component challenge spec
has the same `run' u`-support as the component handler. `oSpec` queries agree exactly (the widening
fixes the left summand); challenge queries route into the appended challenge oracle, which has full
support by `support_simulateQ_challengeQueryImpl_append_left`. This discharges the `h` hypothesis of
`OracleComp.support_run'_simulateQ_liftM_eq_of_query`, so the appended honest experiment's
prover/verifier marginals transport back to the component-protocol experiments. -/
theorem support_run'_simulateQ_addLift_challenge_query_eq
    {ιₒ : Type} {oSpec : OracleSpec ιₒ} {σ : Type} [Subsingleton σ] (u : σ)
    (impl : QueryImpl oSpec (StateT σ ProbComp))
    (t : (oSpec + [pSpec₁.Challenge]ₒ).Domain) :
    support ((simulateQ ((impl.addLift challengeQueryImpl :
        QueryImpl (oSpec + [(pSpec₁ ++ₚ pSpec₂).Challenge]ₒ) (StateT σ ProbComp)))
      (liftM (liftM ((oSpec + [pSpec₁.Challenge]ₒ).query t)
        : OracleComp (oSpec + [pSpec₁.Challenge]ₒ) _)
        : OracleComp (oSpec + [(pSpec₁ ++ₚ pSpec₂).Challenge]ₒ) _)).run' u)
      = support (((impl.addLift challengeQueryImpl :
        QueryImpl (oSpec + [pSpec₁.Challenge]ₒ) (StateT σ ProbComp)) t).run' u) := by
  rcases t with t | t
  · -- `oSpec` query: the widening fixes the left summand, so the lift is the same query in the
    -- appended spec, and both honest handlers restrict to `impl` there.
    rw [show (liftM (liftM ((oSpec + [pSpec₁.Challenge]ₒ).query (Sum.inl t))
          : OracleComp (oSpec + [pSpec₁.Challenge]ₒ) _)
          : OracleComp (oSpec + [(pSpec₁ ++ₚ pSpec₂).Challenge]ₒ) _)
        = liftM ((oSpec + [(pSpec₁ ++ₚ pSpec₂).Challenge]ₒ).query (Sum.inl t)) from rfl]
    simp [simulateQ_spec_query, QueryImpl.addLift_def, QueryImpl.add_apply_inl,
      QueryImpl.liftTarget_self]
  · -- challenge query: both sides have full support.
    rw [show support (((impl.addLift challengeQueryImpl :
        QueryImpl (oSpec + [pSpec₁.Challenge]ₒ) (StateT σ ProbComp)) (Sum.inr t)).run' u) = Set.univ from by
      simp only [QueryImpl.addLift_def, QueryImpl.add_apply_inr, QueryImpl.liftTarget, StateT.run'_eq]
      refine (support_run'_map_liftM u (challengeQueryImpl t)).trans ?_
      rw [challengeQueryImpl]
      exact support_uniformSample (pSpec₁.Challenge t.1)]
    -- LHS: the widened `inr` query is the challenge query lifted into the appended challenge oracle;
    -- route through `simulateQ_add_liftComp_right` to reuse the challenge support agreement.
    simp only [StateT.run'_eq]
    rw [show (liftM (liftM ((oSpec + [pSpec₁.Challenge]ₒ).query (Sum.inr t))
          : OracleComp (oSpec + [pSpec₁.Challenge]ₒ) _)
          : OracleComp (oSpec + [(pSpec₁ ++ₚ pSpec₂).Challenge]ₒ) _)
        = OracleComp.liftComp (liftM (([pSpec₁.Challenge]ₒ).query t)
            : OracleComp ([(pSpec₁ ++ₚ pSpec₂).Challenge]ₒ) _)
            (oSpec + [(pSpec₁ ++ₚ pSpec₂).Challenge]ₒ) from rfl]
    rw [QueryImpl.addLift_def]
    erw [QueryImpl.simulateQ_add_liftComp_right]
    rw [simulateQ_liftTarget, support_run'_map_liftM u]
    exact support_simulateQ_challengeQueryImpl_append_left t

end ProtocolSpec

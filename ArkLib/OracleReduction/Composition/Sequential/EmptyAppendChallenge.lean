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

end ProtocolSpec

/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.OracleReduction.Composition.Sequential.Append
import ArkLib.OracleReduction.Security.Basic

/-!
# Challenge-oracle restriction for the sequential-composition seam (issue #13)

The malicious-prover seam decomposition (`Prover.fst`/`Prover.snd`, `run_seam_factor`) expresses an
arbitrary prover over `pSpec₁ ++ₚ pSpec₂` as its two phases, but each phase's run is `liftM`-ed into
the *combined* challenge oracle `[(pSpec₁ ++ₚ pSpec₂).Challenge]ₒ`. The per-phase soundness games
(`V₁.soundness`, `V₂.soundness`), by contrast, run each phase under its *own* challenge oracle
(`[pSpec₁.Challenge]ₒ`, `[pSpec₂.Challenge]ₒ`). Bridging the two requires showing that simulating a
`pSpec₁`-phase computation under the combined challenge handler agrees (in distribution) with
simulating it under `pSpec₁`'s handler.

This file proves the **per-query agreement** `hquery_evalDist` — the single hypothesis that the
free-monad induction (VCVio's `simulateQ_liftM_eq_of_query`, and its `evalDist` twin) reduces the
whole restriction to. All the cast-heavy content is concentrated here:

* base-oracle (`Sum.inl`) queries hit the *same* shared-oracle implementation `impl`;
* challenge (`Sum.inr`) queries agree because the combined challenge oracle, restricted along the
  challenge `SubSpec` `[pSpec₁.Challenge]ₒ ⊂ₒ [(pSpec₁ ++ₚ pSpec₂).Challenge]ₒ`, samples uniformly
  from a type *equal* to `pSpec₁`'s challenge type — the `SubSpec`'s response map is a bijection
  (`lawfulChallengeSubSpec`), so the uniform distributions coincide.

This machinery is shared with the completeness keystone (`#113`), which is gated on the same seam
split. Everything here is axiom-clean (`propext`/`Classical.choice`/`Quot.sound` only).
-/

open OracleComp ProtocolSpec OracleSpec
open scoped NNReal ENNReal

namespace ArkLib.SeamChallengeRestriction

universe u

set_option maxHeartbeats 1200000

variable {α β γ : Type}

/-- **Uniform sampling pushed along a bijection.** For a bijection `f : α → β`, the pushforward of
the uniform sample on `α` is the uniform sample on `β` — even though the two `SampleableType`
instances are independent. (Follows from VCVio's `probOutput_map_bijective_uniform_cross` by
`probOutput`-extensionality.) -/
theorem evalDist_map_bijective_uniformSample
    [SampleableType α] [SampleableType β] [Finite α]
    (f : α → β) (hf : Function.Bijective f) :
    evalDist (f <$> ($ᵗ α : ProbComp α)) = evalDist ($ᵗ β : ProbComp β) := by
  refine evalDist_ext (fun y => ?_)
  exact probOutput_map_bijective_uniform_cross (α := α) (β := β) f hf y

/-- **State-paired bijection-uniform transport.** The `(·, s)`-paired form, matching the seam's
challenge case once the `StateT.run` layer is exposed: the fresh challenge is sampled (via the
bijective `SubSpec` response map) and paired with the unchanged shared-oracle state `s`. -/
theorem evalDist_pairMap_bijective_uniformSample
    [SampleableType α] [SampleableType β] [Finite α]
    (cont : α → β) (s : γ) (hf : Function.Bijective cont) :
    evalDist ((fun a => (cont a, s)) <$> ($ᵗ α : ProbComp α))
      = evalDist ((fun a => (a, s)) <$> ($ᵗ β : ProbComp β)) := by
  rw [show (fun a => (cont a, s)) = (fun b => (b, s)) ∘ cont from rfl, comp_map]
  exact evalDist_map_eq_of_evalDist_eq (evalDist_map_bijective_uniformSample cont hf) (fun x => (x, s))

variable {m n : ℕ} {pSpec₁ : ProtocolSpec m} {pSpec₂ : ProtocolSpec n}

/-- **The left challenge `SubSpec` is lawful.** A query to challenge round `i` of `pSpec₁` is
forwarded to round `ChallengeIdx.inl i` of `pSpec₁ ++ₚ pSpec₂`, transporting the response along the
type equality `range_challenge_append_inl` — which is a *cast*, hence bijective on every fiber. This
is what makes the combined-oracle uniform challenge map onto `pSpec₁`'s uniform challenge. -/
instance lawfulChallengeSubSpec :
    [pSpec₁.Challenge]ₒ ˡ⊂ₒ [(pSpec₁ ++ₚ pSpec₂).Challenge]ₒ where
  onResponse_bijective t := cast_bijective _

/-- **Per-query agreement at the seam (`evalDist`).** Simulating a single (doubly-lifted) base-or-
challenge query of `oSpec + [pSpec₁.Challenge]ₒ` under the *combined* challenge handler
`impl.addLift challengeQueryImpl[pSpec₁ ++ₚ pSpec₂]` yields the same distribution as the `pSpec₁`
handler `impl.addLift challengeQueryImpl[pSpec₁]`. This is the hypothesis that the free-monad
induction (`simulateQ_liftM_eq_of_query` / its `evalDist` twin) needs to lift the agreement from
single queries to whole phase-1 computations, completing the seam's challenge-oracle restriction. -/
theorem hquery_evalDist {ι : Type} {oSpec : OracleSpec ι}
    [∀ i, SampleableType (pSpec₁.Challenge i)]
    [∀ i, SampleableType ((pSpec₁ ++ₚ pSpec₂).Challenge i)]
    [[pSpec₁.Challenge]ₒ.Fintype] [[pSpec₁.Challenge]ₒ.Inhabited]
    [[(pSpec₁ ++ₚ pSpec₂).Challenge]ₒ.Fintype] [[(pSpec₁ ++ₚ pSpec₂).Challenge]ₒ.Inhabited]
    {σ : Type} (impl : QueryImpl oSpec (StateT σ ProbComp))
    (t : (oSpec + [pSpec₁.Challenge]ₒ).Domain) (s : σ) :
    evalDist ((simulateQ
        ((impl.addLift (challengeQueryImpl (pSpec := pSpec₁ ++ₚ pSpec₂))) :
          QueryImpl _ (StateT σ ProbComp))
        (liftM (liftM (OracleSpec.query t) :
            OracleComp (oSpec + [pSpec₁.Challenge]ₒ) ((oSpec + [pSpec₁.Challenge]ₒ).Range t))
          : OracleComp (oSpec + [(pSpec₁ ++ₚ pSpec₂).Challenge]ₒ) _)).run s)
      = evalDist ((((impl.addLift (challengeQueryImpl (pSpec := pSpec₁))) :
          QueryImpl _ (StateT σ ProbComp)) t).run s) := by
  rcases t with o | c
  · -- Base-oracle query: both handlers run the *same* `impl o` (no cast).
    have hL : simulateQ
        ((impl.addLift (challengeQueryImpl (pSpec := pSpec₁ ++ₚ pSpec₂))) :
          QueryImpl _ (StateT σ ProbComp))
        (liftM (liftM (OracleSpec.query (Sum.inl o)) :
            OracleComp (oSpec + [pSpec₁.Challenge]ₒ) ((oSpec + [pSpec₁.Challenge]ₒ).Range (Sum.inl o)))
          : OracleComp (oSpec + [(pSpec₁ ++ₚ pSpec₂).Challenge]ₒ) _) = impl o := by
      change simulateQ _ (liftM (liftM (OracleSpec.query (Sum.inl o)) :
          OracleQuery (oSpec + [(pSpec₁ ++ₚ pSpec₂).Challenge]ₒ) _)) = _
      simp [simulateQ_query, OracleQuery.liftM_right_add_right_add_query, QueryImpl.addLift_def,
        QueryImpl.add_apply_inl, QueryImpl.liftTarget_apply, OracleSpec.query]
    have hR : ((impl.addLift (challengeQueryImpl (pSpec := pSpec₁))) :
        QueryImpl _ (StateT σ ProbComp)) (Sum.inl o) = impl o := by
      simp [QueryImpl.addLift_def, QueryImpl.add_apply_inl, QueryImpl.liftTarget_apply]
    rw [hL, hR]
  · -- Challenge query: combined-oracle uniform challenge maps onto `pSpec₁`'s via the bijective
    -- (cast) `SubSpec` response map; the shared-oracle state `s` is untouched.
    change evalDist ((simulateQ
        ((impl.addLift (challengeQueryImpl (pSpec := pSpec₁ ++ₚ pSpec₂))) :
          QueryImpl _ (StateT σ ProbComp))
        (liftM (liftM (OracleSpec.query (Sum.inr c)) :
          OracleQuery (oSpec + [(pSpec₁ ++ₚ pSpec₂).Challenge]ₒ) _))).run s) = _
    simp only [simulateQ_query, OracleQuery.liftM_right_add_right_add_def,
      OracleQuery.liftM_add_right_def, QueryImpl.addLift_def, QueryImpl.add_apply_inr,
      QueryImpl.liftTarget_apply, challengeQueryImpl, OracleSpec.query,
      OracleQuery.input_apply, OracleQuery.cont_apply]
    simp [StateT.run_map, evalDist_map]
    have hbij : Function.Bijective (liftM (OracleQuery.mk c id) :
        OracleQuery [(pSpec₁ ++ₚ pSpec₂).Challenge]ₒ ([pSpec₁.Challenge]ₒ.Range c)).cont := by
      first
        | exact cast_bijective _
        | exact eqRec_bijective _
        | exact eq_mpr_bijective _
    rw [← evalDist_map, ← evalDist_map]
    convert evalDist_pairMap_bijective_uniformSample _ s hbij using 2

/-- **`evalDist` lifting of per-query agreement to whole computations.** The `evalDist`-and-`run`
twin of VCVio's `simulateQ_liftM_eq_of_query`: if two handlers `h` (over the larger oracle `M₀`) and
`h₁` (over the sub-oracle `I₀`) agree *per lifted query* in distribution (`hq`), then simulating any
`I₀`-computation `oa` lifted into `M₀` under `h` agrees in distribution with simulating `oa` directly
under `h₁`. Free-monad induction; the per-query hypothesis is discharged by `hquery_evalDist`. -/
theorem evalDist_simulateQ_liftM_run_eq_of_query
    {ιᵢ ιₘ : Type} {I₀ : OracleSpec ιᵢ} {M₀ : OracleSpec ιₘ} {σ' : Type}
    [MonadLiftT (OracleComp I₀) (OracleComp M₀)] [LawfulMonadLiftT (OracleComp I₀) (OracleComp M₀)]
    (h : QueryImpl M₀ (StateT σ' ProbComp)) (h₁ : QueryImpl I₀ (StateT σ' ProbComp))
    (hq : ∀ (t : I₀.Domain) (s : σ'),
      evalDist ((simulateQ h (liftM (liftM (I₀.query t) :
        OracleComp I₀ (I₀.Range t)) : OracleComp M₀ (I₀.Range t))).run s) = evalDist ((h₁ t).run s))
    {δ : Type} (oa : OracleComp I₀ δ) (s : σ') :
    evalDist ((simulateQ h (liftM oa : OracleComp M₀ δ)).run s)
      = evalDist ((simulateQ h₁ oa).run s) := by
  induction oa using OracleComp.inductionOn generalizing s with
  | pure x => simp [simulateQ_pure, StateT.run_pure]
  | query_bind t k ih =>
      have hq1 : simulateQ h₁ (liftM (I₀.query t) : OracleComp I₀ (I₀.Range t)) = h₁ t := by
        simp [simulateQ_query]
      rw [liftM_bind, simulateQ_bind, StateT.run_bind, simulateQ_bind, StateT.run_bind, hq1,
          evalDist_bind, evalDist_bind, hq t s]
      refine bind_congr ?_
      rintro ⟨a, s'⟩
      exact ih a s'

end ArkLib.SeamChallengeRestriction

#print axioms ArkLib.SeamChallengeRestriction.evalDist_simulateQ_liftM_run_eq_of_query
#print axioms ArkLib.SeamChallengeRestriction.hquery_evalDist

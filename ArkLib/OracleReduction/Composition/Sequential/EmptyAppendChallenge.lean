/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.OracleReduction.Composition.Sequential.Append

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

namespace ProtocolSpec

variable {m n : ℕ} {pSpec₁ : ProtocolSpec m} {pSpec₂ : ProtocolSpec n}
  [∀ i, SampleableType (pSpec₁.Challenge i)] [∀ i, SampleableType (pSpec₂.Challenge i)]

/-- Transporting forward along `h` then back along `h.symm` is the identity. -/
private theorem eqRec_eqRec_symm {A B : Type} (h : A = B) (y : B) :
    h ▸ (h.symm ▸ y : A) = y := by
  subst h; rfl

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
  -- Expose the `OracleQuery`-level inclusion so `SubSpec.liftM_eq_lift` fires.
  rw [show (liftM (([pSpec₁.Challenge]ₒ).query i) : OracleComp ([(pSpec₁ ++ₚ pSpec₂).Challenge]ₒ) _)
        = liftM ((MonadLift.monadLift (([pSpec₁.Challenge]ₒ).query i))
            : OracleQuery ([(pSpec₁ ++ₚ pSpec₂).Challenge]ₒ) _) from rfl]
  rw [SubSpec.liftM_eq_lift, simulateQ_query, support_map, challengeQueryImpl]
  -- Reduce the lens action and query projections, then collapse the support of the (full-support)
  -- uniform sample, all in one pass so `support_uniformSample` fires on the reduced form. The
  -- continuation is the bijective response transport `h ▸ ·`, so its image of `Set.univ` is again
  -- `Set.univ`.
  simp only [SubSpec.onQuery, SubSpec.onResponse, OracleQuery.input_apply, OracleQuery.cont_apply,
    OracleSpec.query, OracleQuery.mk, Function.id_comp]
  apply Set.eq_univ_of_forall
  intro y
  rw [Set.mem_image]
  generalize_proofs h
  -- The appended challenge's `SampleableType` instance is keyed on `.Challenge`; the oracle's
  -- `.Range ⟨·, ()⟩` form is defeq, so bridge it explicitly for `mem_support_uniformSample`.
  haveI : SampleableType ([(pSpec₁ ++ₚ pSpec₂).Challenge]ₒ.Range ⟨ChallengeIdx.inl i.fst, ()⟩) :=
    inferInstanceAs (SampleableType ((pSpec₁ ++ₚ pSpec₂).Challenge (ChallengeIdx.inl i.fst)))
  exact ⟨h.symm ▸ y, mem_support_uniformSample _, eqRec_eqRec_symm h y⟩

end ProtocolSpec

/-
Copyright (c) 2025 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/

import ArkLib.ProofSystem.Plonk.Basic
import ArkLib.ProofSystem.Plonk.PermutationCheck
import ArkLib.OracleReduction.Composition.Sequential.Append

/-!
# Plonk Check Composition

This file packages the existing Plonk gate check with a post-gate permutation check.

The second phase consumes the gate-check output `(cs, w)`, sends the extended wire assignment
computed from `w`, and verifies both that the sent extended assignment is pointwise the extension
of `w` and that it satisfies the copy-constraint permutation.
-/

noncomputable section

namespace Plonk

open OracleComp OracleSpec ProtocolSpec

section Composition

variable (𝓡 : Type) [CommRing 𝓡] [DecidableEq 𝓡] (numWires numGates : ℕ)

/-- The extended assignment message agrees pointwise with the extension of the gate witness. -/
@[reducible]
def ExtendedWireAssignmentMatches
    (cs : Plonk.ConstraintSystem 𝓡 numWires numGates)
    (w : Fin numWires → 𝓡) (f : Fin (3 * numGates) → 𝓡) : Prop :=
  ∀ j, f j =
    extendWireAssignment (𝓡 := 𝓡) (numWires := numWires) (numGates := numGates) cs w j

/-- Permutation phase specialized to the statement produced by the gate check. -/
@[reducible]
def permCheckAfterGateProver :
    Prover []ₒ
      (Plonk.ConstraintSystem 𝓡 numWires numGates × (Fin numWires → 𝓡)) Unit
      (Plonk.ConstraintSystem 𝓡 numWires numGates × (Fin numWires → 𝓡)) Unit
      (permCheckPSpec 𝓡 numGates) where
  PrvState
  | 0 => Plonk.ConstraintSystem 𝓡 numWires numGates × (Fin numWires → 𝓡)
  | 1 => Plonk.ConstraintSystem 𝓡 numWires numGates × (Fin numWires → 𝓡)
  input := fun ⟨stmt, _⟩ => stmt
  sendMessage := fun | ⟨0, _⟩ => fun ⟨cs, w⟩ =>
    pure <|
      (extendWireAssignment (𝓡 := 𝓡) (numWires := numWires) (numGates := numGates) cs w,
        ⟨cs, w⟩)
  receiveChallenge | ⟨0, h⟩ => nomatch h
  output := fun stmt => pure (stmt, ())

/-- Verifier for the post-gate permutation phase. -/
@[reducible]
def permCheckAfterGateVerifier :
    Verifier []ₒ
      (Plonk.ConstraintSystem 𝓡 numWires numGates × (Fin numWires → 𝓡))
      (Plonk.ConstraintSystem 𝓡 numWires numGates × (Fin numWires → 𝓡))
      (permCheckPSpec 𝓡 numGates) where
  verify := fun ⟨cs, w⟩ transcript =>
    let f : Fin (3 * numGates) → 𝓡 := transcript 0
    if ExtendedWireAssignmentMatches 𝓡 numWires numGates cs w f ∧
      CopyConstraintsSatisfied f cs.perm then
      pure ⟨cs, w⟩
    else
      failure

omit [CommRing 𝓡] in
theorem permCheckAfterGateVerifier_verify_eq
    (stmt : Plonk.ConstraintSystem 𝓡 numWires numGates × (Fin numWires → 𝓡))
    (transcript : FullTranscript (permCheckPSpec 𝓡 numGates)) :
    (permCheckAfterGateVerifier (𝓡 := 𝓡) (numWires := numWires)
      (numGates := numGates)).verify stmt transcript =
      if ExtendedWireAssignmentMatches 𝓡 numWires numGates stmt.1 stmt.2 (transcript 0) ∧
          CopyConstraintsSatisfied (transcript 0) stmt.1.perm then
        pure stmt
      else
        failure := by
  rcases stmt with ⟨cs, w⟩
  rfl

omit [CommRing 𝓡] in
theorem permCheckAfterGateVerifier_mem_support_iff
    (stmt : Plonk.ConstraintSystem 𝓡 numWires numGates × (Fin numWires → 𝓡))
    (transcript : FullTranscript (permCheckPSpec 𝓡 numGates))
    (out : Plonk.ConstraintSystem 𝓡 numWires numGates × (Fin numWires → 𝓡)) :
    some out ∈ support
      ((permCheckAfterGateVerifier (𝓡 := 𝓡) (numWires := numWires)
        (numGates := numGates)).verify stmt transcript).run ↔
      ExtendedWireAssignmentMatches 𝓡 numWires numGates stmt.1 stmt.2 (transcript 0) ∧
        CopyConstraintsSatisfied (transcript 0) stmt.1.perm ∧ out = stmt := by
  rw [permCheckAfterGateVerifier_verify_eq]
  by_cases hMatch :
      ExtendedWireAssignmentMatches 𝓡 numWires numGates stmt.1 stmt.2 (transcript 0)
  · by_cases hCopy : CopyConstraintsSatisfied (transcript 0) stmt.1.perm
    · rw [if_pos ⟨hMatch, hCopy⟩]
      constructor
      · intro hout
        exact ⟨hMatch, hCopy, by simpa using hout⟩
      · intro h
        simp [h.2.2]
    · rw [if_neg (by intro h; exact hCopy h.2)]
      simp [hCopy]
  · rw [if_neg (by intro h; exact hMatch h.1)]
    simp [hMatch]

/-- Reduction for the post-gate permutation phase. -/
@[reducible]
def permCheckAfterGateReduction :
    Reduction []ₒ
      (Plonk.ConstraintSystem 𝓡 numWires numGates × (Fin numWires → 𝓡)) Unit
      (Plonk.ConstraintSystem 𝓡 numWires numGates × (Fin numWires → 𝓡)) Unit
      (permCheckPSpec 𝓡 numGates) where
  prover := permCheckAfterGateProver 𝓡 numWires numGates
  verifier := permCheckAfterGateVerifier 𝓡 numWires numGates

/-- Two-message Plonk check protocol: gate assignment, then extended permutation assignment. -/
@[reducible]
def plonkCheckPSpec : ProtocolSpec 2 :=
  gateCheckPSpec 𝓡 numWires ++ₚ permCheckPSpec 𝓡 numGates

@[reducible]
def plonkCheckProver :
    Prover []ₒ
      (Plonk.ConstraintSystem 𝓡 numWires numGates) (Fin numWires → 𝓡)
      (Plonk.ConstraintSystem 𝓡 numWires numGates × (Fin numWires → 𝓡)) Unit
      (plonkCheckPSpec 𝓡 numWires numGates) :=
  Prover.append
    (gateCheckProver (𝓡 := 𝓡) (numWires := numWires) (numGates := numGates))
    (permCheckAfterGateProver 𝓡 numWires numGates)

@[reducible]
def plonkCheckVerifier :
    Verifier []ₒ
      (Plonk.ConstraintSystem 𝓡 numWires numGates)
      (Plonk.ConstraintSystem 𝓡 numWires numGates × (Fin numWires → 𝓡))
      (plonkCheckPSpec 𝓡 numWires numGates) :=
  Verifier.append
    (gateCheckVerifier (𝓡 := 𝓡) (numWires := numWires) (numGates := numGates))
    (permCheckAfterGateVerifier 𝓡 numWires numGates)

@[reducible]
def plonkCheckReduction :
    Reduction []ₒ
      (Plonk.ConstraintSystem 𝓡 numWires numGates) (Fin numWires → 𝓡)
      (Plonk.ConstraintSystem 𝓡 numWires numGates × (Fin numWires → 𝓡)) Unit
      (plonkCheckPSpec 𝓡 numWires numGates) where
  prover := plonkCheckProver 𝓡 numWires numGates
  verifier := plonkCheckVerifier 𝓡 numWires numGates

theorem plonkCheckReduction_eq_append :
    plonkCheckReduction 𝓡 numWires numGates =
      Reduction.append
        (gateCheckReduction (𝓡 := 𝓡) (numWires := numWires) (numGates := numGates))
        (permCheckAfterGateReduction 𝓡 numWires numGates) := rfl

@[reducible, simp]
def plonkCheckRel :
    Set (Plonk.ConstraintSystem 𝓡 numWires numGates × (Fin numWires → 𝓡)) :=
  { p | p.1.accepts p.2 ∧
      CopyConstraintsSatisfied
        (extendWireAssignment (𝓡 := 𝓡) (numWires := numWires)
          (numGates := numGates) p.1 p.2) p.1.perm }

@[reducible, simp]
def plonkCheckRelIn :
    Set (Plonk.ConstraintSystem 𝓡 numWires numGates × (Fin numWires → 𝓡)) :=
  plonkCheckRel 𝓡 numWires numGates

@[reducible, simp]
def plonkCheckRelOut :
    Set ((Plonk.ConstraintSystem 𝓡 numWires numGates × (Fin numWires → 𝓡)) × Unit) :=
  Prod.fst ⁻¹' plonkCheckRel 𝓡 numWires numGates

@[reducible, simp]
def plonkCheckLangIn :
    Set (Plonk.ConstraintSystem 𝓡 numWires numGates) :=
  { cs | ∃ w : Fin numWires → 𝓡, (cs, w) ∈ plonkCheckRel 𝓡 numWires numGates }

@[reducible, simp]
def plonkCheckLangOut :
    Set (Plonk.ConstraintSystem 𝓡 numWires numGates × (Fin numWires → 𝓡)) :=
  plonkCheckRel 𝓡 numWires numGates

variable {σ : Type} (init : ProbComp σ) (impl : QueryImpl []ₒ (StateT σ ProbComp))

/-- The post-gate permutation verifier has zero-error round-by-round soundness for the full
gate-and-copy language on its `(cs, w)` statement. The verifier returns only the input statement,
so any accepted output in `plonkCheckLangOut` immediately puts the input statement in the same
language. -/
theorem permCheckAfterGateVerifier_rbrSoundness :
    (permCheckAfterGateVerifier (𝓡 := 𝓡) (numWires := numWires)
      (numGates := numGates)).rbrSoundness init impl
        (plonkCheckLangOut 𝓡 numWires numGates)
        (plonkCheckLangOut 𝓡 numWires numGates) 0 := by
  refine ⟨{
    toFun := fun _ stmt _ => stmt ∈ plonkCheckLangOut 𝓡 numWires numGates
    toFun_empty := fun _ => Iff.rfl
    toFun_next := fun _ _ _ _ h _ => h
    toFun_full := fun stmt tr hstmt => by
      rcases stmt with ⟨cs, w⟩
      exact ?_
  }, ?_⟩
  · rw [probEvent_eq_zero_iff]
    intro out hout houtLang
    rw [OptionT.mem_support_iff] at hout
    simp only [OptionT.run_mk, support_bind, Set.mem_iUnion] at hout
    obtain ⟨s, _, hout⟩ := hout
    by_cases hAccept :
        ExtendedWireAssignmentMatches 𝓡 numWires numGates cs w (tr 0) ∧
          CopyConstraintsSatisfied (tr 0) cs.perm
    · have hrun :
          (simulateQ impl
            ((permCheckAfterGateVerifier (𝓡 := 𝓡) (numWires := numWires)
              (numGates := numGates)).run (cs, w) tr)).run' s =
            pure (some (cs, w)) := by
        simp only [Verifier.run]
        rw [if_pos hAccept]
        rw [simulateQ_pure]
        change Prod.fst <$> (pure (some (cs, w)) : StateT σ ProbComp
          (Option (Plonk.ConstraintSystem 𝓡 numWires numGates × (Fin numWires → 𝓡)))).run s =
          pure (some (cs, w))
        rw [StateT.run_pure]
        simp [map_pure]
      rw [hrun] at hout
      simp only [support_pure, Set.mem_singleton_iff, Option.some.injEq] at hout
      subst out
      exact hstmt houtLang
    · have hrun :
          (simulateQ impl
            ((permCheckAfterGateVerifier (𝓡 := 𝓡) (numWires := numWires)
              (numGates := numGates)).run (cs, w) tr)).run' s =
            pure none := by
        simp only [Verifier.run]
        rw [if_neg hAccept]
        rw [simulateQ_pure]
        change Prod.fst <$> (pure none : StateT σ ProbComp
          (Option (Plonk.ConstraintSystem 𝓡 numWires numGates × (Fin numWires → 𝓡)))).run s =
          pure none
        rw [StateT.run_pure]
        simp [map_pure]
      rw [hrun] at hout
      simp at hout
  · intro _ _ _ _ _ _ ⟨⟨0, _⟩, hdir⟩
    exact absurd hdir (by simp)

#print axioms Plonk.permCheckAfterGateVerifier_verify_eq
#print axioms Plonk.permCheckAfterGateVerifier_mem_support_iff
#print axioms Plonk.plonkCheckReduction_eq_append
#print axioms Plonk.plonkCheckRel
#print axioms Plonk.plonkCheckLangIn
#print axioms Plonk.plonkCheckLangOut
#print axioms Plonk.permCheckAfterGateVerifier_rbrSoundness

end Composition

end Plonk

end

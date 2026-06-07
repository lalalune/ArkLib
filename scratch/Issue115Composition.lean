import ArkLib.ProofSystem.Plonk.Basic
import ArkLib.ProofSystem.Plonk.PermutationCheck
import ArkLib.OracleReduction.Composition.Sequential.Append

noncomputable section

namespace Plonk

open OracleComp OracleSpec ProtocolSpec

section Composition

variable (𝓡 : Type) [CommRing 𝓡] [DecidableEq 𝓡] (numWires numGates : ℕ)

@[reducible]
def ExtendedWireAssignmentMatches
    (cs : Plonk.ConstraintSystem 𝓡 numWires numGates)
    (w : Fin numWires → 𝓡) (f : Fin (3 * numGates) → 𝓡) : Prop :=
  ∀ j, f j =
    extendWireAssignment (𝓡 := 𝓡) (numWires := numWires) (numGates := numGates) cs w j

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

@[reducible]
def permCheckAfterGateReduction :
    Reduction []ₒ
      (Plonk.ConstraintSystem 𝓡 numWires numGates × (Fin numWires → 𝓡)) Unit
      (Plonk.ConstraintSystem 𝓡 numWires numGates × (Fin numWires → 𝓡)) Unit
      (permCheckPSpec 𝓡 numGates) where
  prover := permCheckAfterGateProver 𝓡 numWires numGates
  verifier := permCheckAfterGateVerifier 𝓡 numWires numGates

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

#print axioms Plonk.permCheckAfterGateVerifier_verify_eq
#print axioms Plonk.permCheckAfterGateVerifier_mem_support_iff
#print axioms Plonk.plonkCheckReduction_eq_append
#print axioms Plonk.plonkCheckRel
#print axioms Plonk.plonkCheckLangIn
#print axioms Plonk.plonkCheckLangOut

end Composition

end Plonk

end

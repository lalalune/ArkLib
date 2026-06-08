import ArkLib.OracleReduction.Composition.Sequential.Append

open OracleSpec OracleComp ProtocolSpec

namespace Prover

variable {ι : Type} {oSpec : OracleSpec ι} {Stmt₁ Wit₁ Stmt₂ Wit₂ Stmt₃ Wit₃ : Type}
  {m : ℕ} {pSpec₁ : ProtocolSpec m} {pSpec₂ : ProtocolSpec 0}
  (P₁ : Prover oSpec Stmt₁ Wit₁ Stmt₂ Wit₂ pSpec₁)
  (P₂ : Prover oSpec Stmt₂ Wit₂ Stmt₃ Wit₃ pSpec₂)

/-- For an empty trailing protocol, the appended prover's state at the last round is `P₁`'s last
state. -/
theorem append_PrvState_last_empty :
    (P₁.append P₂).PrvState (Fin.last (m + 0)) = P₁.PrvState (Fin.last m) := by
  have h := append_PrvState_castLE (P₁ := P₁) (P₂ := P₂) (Fin.last m)
  rwa [show ((Fin.last m).castLE (by omega) : Fin (m + 0 + 1)) = Fin.last (m + 0) from by
    ext; simp] at h

/-- The appended prover's `output` for an empty trailing protocol: run `P₁`'s output, feed it to
`P₂`'s input, then `P₂`'s output. -/
theorem append_output_empty (state : (P₁.append P₂).PrvState (Fin.last (m + 0))) :
    (P₁.append P₂).output state
      = (do
          let ctx ← P₁.output (cast (append_PrvState_last_empty P₁ P₂) state)
          P₂.output (P₂.input ctx)) := by
  show (P₁.append P₂).output state = _
  unfold Prover.append
  simp only [Nat.add_zero, dif_pos]
  rfl

/-- Running a prover over the empty protocol: it has no rounds, so it just maps input through
output, with the (unique) empty transcript. -/
theorem run_empty (s : Stmt₂) (w : Wit₂) :
    P₂.run s w
      = (do
          let ctx ← P₂.output (P₂.input (s, w))
          return ((default : pSpec₂.FullTranscript), ctx)) := by
  rw [run_eq_runToRound_last]
  simp only [Prover.runToRound]
  have h_last_eq_zero : (Fin.last 0) = (0 : Fin 1) := rfl
  rw! (castMode := .all) [h_last_eq_zero]
  simp only [Fin.induction_zero, pure_bind]
  rfl

/-- **The `n = 0` discharge of `appendRunRightResidual`.** -/
theorem appendRunRightResidual_holds_empty (stmt : Stmt₁) (wit : Wit₁) :
    appendRunRightResidual (P₁ := P₁) (P₂ := P₂) stmt wit := by
  unfold appendRunRightResidual
  have hcollapse :
      (Prover.runToRound (⟨m, by omega⟩ : Fin (m + 0 + 1)) stmt wit (P₁.append P₂) >>=
        (P₁.append P₂).continueFromTo stmt wit (⟨m, by omega⟩ : Fin (m + 0 + 1)) (Fin.last (m + 0)))
      = Prover.runToRound (⟨m, by omega⟩ : Fin (m + 0 + 1)) stmt wit (P₁.append P₂) := by
    have hcont : (P₁.append P₂).continueFromTo stmt wit (⟨m, by omega⟩ : Fin (m + 0 + 1))
        (Fin.last (m + 0)) = pure := by
      funext rk; exact continueFromTo_self _ _ _ _ rk
    rw [hcont]
    first
      | exact bind_pure _
      | simp only [bind_pure]
      | rw [bind_pure_comp, id_map']
      | simp [bind_pure_comp]
  simp only [hcollapse, run_eq_runToRound_last (prover := P₁), run_empty, append_output_empty,
    liftM_bind, bind_assoc]
  apply eq_of_heq
  have hseam := append_runToRound_seam (P₁ := P₁) (P₂ := P₂) (stmt := stmt) (wit := wit)
  refine bind_heq_congr rfl ?_ hseam ?_
  · sorry
  · intro a a' ha
    trace_state
    sorry

end Prover

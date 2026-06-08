import ArkLib.OracleReduction.Composition.Sequential.Append

open OracleSpec OracleComp ProtocolSpec

namespace Prover

variable {ι : Type} {oSpec : OracleSpec ι} {Stmt₁ Wit₁ Stmt₂ Wit₂ Stmt₃ Wit₃ : Type}
  {m : ℕ} {pSpec₁ : ProtocolSpec m} {pSpec₂ : ProtocolSpec 0}
  (P₁ : Prover oSpec Stmt₁ Wit₁ Stmt₂ Wit₂ pSpec₁)
  (P₂ : Prover oSpec Stmt₂ Wit₂ Stmt₃ Wit₃ pSpec₂)

theorem append_PrvState_last_empty :
    (P₁.append P₂).PrvState (Fin.last (m + 0)) = P₁.PrvState (Fin.last m) := by
  have h := append_PrvState_castLE (P₁ := P₁) (P₂ := P₂) (Fin.last m)
  rwa [show ((Fin.last m).castLE (by omega) : Fin (m + 0 + 1)) = Fin.last (m + 0) from by
    ext; simp] at h

theorem append_Transcript_last_empty :
    (pSpec₁ ++ₚ pSpec₂).Transcript (Fin.last (m + 0)) = pSpec₁.Transcript (Fin.last m) := by
  have h := append_Transcript_castLE (pSpec₁ := pSpec₁) (pSpec₂ := pSpec₂) (Fin.last m)
  rwa [show ((Fin.last m).castLE (by omega) : Fin (m + 0 + 1)) = Fin.last (m + 0) from by
    ext; simp] at h

theorem append_output_empty (state : (P₁.append P₂).PrvState (Fin.last (m + 0))) :
    (P₁.append P₂).output state
      = (do
          let ctx ← P₁.output (cast (append_PrvState_last_empty P₁ P₂) state)
          P₂.output (P₂.input ctx)) := by
  show (P₁.append P₂).output state = _
  unfold Prover.append
  simp only [Nat.add_zero, dif_pos]
  rfl

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

/-- **The `n = 0` discharge of `Prover.appendRunRightResidual`.** When the trailing protocol is
empty, the right-block continuation collapses (`continueFromTo_self`), the left block is the seam run
(`append_runToRound_seam`), and the output is the empty-append branch (`append_output_empty`); the
appended run then matches `P₁.run >>= P₂.run` with the empty trailing transcript. This is the
sequential-composition prover-run factoring for an empty second phase — the analogue of
`appendRunRightResidual_holds_msg` for `n = 0`. -/
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
    exact bind_pure _
  simp only [hcollapse, run_eq_runToRound_last (prover := P₁), run_empty, append_output_empty,
    liftM_bind, bind_assoc, liftM_pure, pure_bind]
  apply eq_of_heq
  have hseam := append_runToRound_seam (P₁ := P₁) (P₂ := P₂) (stmt := stmt) (wit := wit)
  refine bind_heq_congr
    (by rw [append_Transcript_last_empty, append_PrvState_last_empty]) rfl hseam
    (fun rSeam x hr => ?_)
  obtain ⟨ht, hs⟩ := prod_heq_split (append_Transcript_last_empty (pSpec₂ := pSpec₂))
    (append_PrvState_last_empty P₁ P₂) hr
  have hc2 : cast (append_PrvState_last_empty P₁ P₂) rSeam.2 = x.2 :=
    eq_of_heq ((cast_heq _ _).trans hs)
  rw [hc2]
  apply heq_of_eq
  have htr : rSeam.1 = x.1 ++ₜ (default : pSpec₂.FullTranscript) := by
    have hempty : (x.1 ++ₜ (default : pSpec₂.FullTranscript)) ≍ x.1 := by
      rw [← Transcript.appendRight_full]
      exact Transcript.appendRight_empty x.1
    exact eq_of_heq (ht.trans hempty.symm)
  rw [htr]
  have hLL : ∀ {α : Type} (c : OracleComp oSpec α),
      (liftM (liftM c : OracleComp (oSpec + [pSpec₁.Challenge]ₒ) α) :
        OracleComp (oSpec + [(pSpec₁ ++ₚ pSpec₂).Challenge]ₒ) α)
      = (liftM c : OracleComp (oSpec + [(pSpec₁ ++ₚ pSpec₂).Challenge]ₒ) α) := by
    intro α c
    simp only [← OracleComp.liftComp_eq_liftM]
    exact liftComp_liftComp (fun t => rfl) c
  simp only [hLL, Prod.mk.eta]

#print axioms appendRunRightResidual_holds_empty

end Prover

import ArkLib.OracleReduction.Composition.Sequential.AppendRunEvalDist
import ArkLib.OracleReduction.Completeness
open OracleComp OracleSpec ProtocolSpec
namespace Reduction
variable {ι : Type} {oSpec : OracleSpec ι} [oSpec.Fintype] [oSpec.Inhabited]
  {StmtIn WitIn StmtOut WitOut : Type} {n : ℕ} {pSpec : ProtocolSpec n}
theorem mem_support_run_of_prover_verifier
    (R : Reduction oSpec StmtIn WitIn StmtOut WitOut pSpec)
    (stmt : StmtIn) (wit : WitIn)
    (tr : FullTranscript pSpec) (prv : StmtOut × WitOut) (vout : StmtOut)
    (hP : (tr, prv) ∈ support (R.prover.run stmt wit))
    (hV : some vout ∈ support (OptionT.run (R.verifier.run stmt tr))) :
    some ((tr, prv), vout) ∈ support (OptionT.run (R.run stmt wit)) := by
  unfold Reduction.run
  simp only [OptionT.run_bind, Option.elimM, bind_assoc, mem_support_bind_iff]
  refine ⟨some (tr, prv), ?_, ?_⟩
  · show some (tr, prv) ∈ support (some <$> R.prover.run stmt wit)
    simp only [support_map, Set.mem_image, Option.some.injEq]; exact ⟨_, hP, rfl⟩
  · simp only [Option.elim_some, mem_support_bind_iff]
    refine ⟨some (some vout), ?_, ?_⟩
    · rw [OptionT.run_liftM_run, support_map,
        support_simulateQ_eq_OracleComp_of_superSpec _ _ (fun _ => rfl)]
      simp only [Set.mem_image, Option.some.injEq]
      exact ⟨some vout, hV, rfl⟩
    · simp only [Option.elim_some, Option.getM_some, OptionT.run_pure, OptionT.run_bind,
        pure_bind, support_pure, Set.mem_singleton_iff]
      rfl
end Reduction


namespace AppendKeystone

variable {ι : Type} {oSpec : OracleSpec ι} [oSpec.Fintype] [oSpec.Inhabited]
  {Stmt₁ Wit₁ Stmt₂ Wit₂ Stmt₃ Wit₃ : Type}
  {m n : ℕ} {pSpec₁ : ProtocolSpec m} {pSpec₂ : ProtocolSpec n}

/-- Forward decomposition into raw component prover/verifier outputs. -/
theorem mem_support_append_run_decompose
    (R₁ : Reduction oSpec Stmt₁ Wit₁ Stmt₂ Wit₂ pSpec₁)
    (R₂ : Reduction oSpec Stmt₂ Wit₂ Stmt₃ Wit₃ pSpec₂)
    (stmtIn : Stmt₁) (witIn : Wit₁)
    (hn : 0 < n)
    (hDir : (pSpec₁ ++ₚ pSpec₂).dir (⟨m, by omega⟩ : Fin (m + n)) = .P_to_V)
    (hDir₂ : pSpec₂.dir (⟨0, hn⟩ : Fin n) = .P_to_V)
    (x : (FullTranscript (pSpec₁ ++ₚ pSpec₂) × Stmt₃ × Wit₃) × Stmt₃)
    (hx : some x ∈ support ((R₁.append R₂).run stmtIn witIn).run) :
    ∃ (tr1 : FullTranscript pSpec₁) (s2 : Stmt₂) (w2 : Wit₂) (sv2 : Stmt₂)
      (tr2 : FullTranscript pSpec₂),
      (tr1, s2, w2) ∈ support (R₁.prover.run stmtIn witIn) ∧
      some sv2 ∈ support ((R₁.verifier.run stmtIn tr1).run) ∧
      (tr2, x.1.2.1, x.1.2.2) ∈ support (R₂.prover.run s2 w2) ∧
      some x.2 ∈ support ((R₂.verifier.run sv2 tr2).run) := by
  unfold Reduction.run at hx
  rw [show (R₁.append R₂).prover = R₁.prover.append R₂.prover from rfl,
    Prover.append_run_msg (P₁ := R₁.prover) (P₂ := R₂.prover) stmtIn witIn hn hDir hDir₂] at hx
  simp only [OptionT.run_bind, Option.elimM, bind_assoc, liftM_bind, mem_support_bind_iff,
    support_liftM, Set.mem_image] at hx
  obtain ⟨p1opt, hp1, hx⟩ := hx
  rcases p1opt with _ | ⟨tr1, s2, w2⟩
  · simp at hx
  · simp only [Option.elim, OptionT.run_bind, Option.elimM, bind_assoc, liftM_bind,
      mem_support_bind_iff, support_liftM, Set.mem_image, OptionT.run_pure, liftM_pure,
      bind_pure_comp, map_bind] at hx
    obtain ⟨p2opt, hp2, hx⟩ := hx
    rcases p2opt with _ | ⟨tr2, s3, w3⟩
    · simp at hx
    · simp only [Option.elim, pure_bind, OptionT.run_bind, Option.elimM, bind_assoc,
        mem_support_bind_iff] at hx
      rw [show (R₁.append R₂).verifier = R₁.verifier.append R₂.verifier from rfl,
        Verifier.append_run, ProtocolSpec.FullTranscript.append_fst, ProtocolSpec.FullTranscript.append_snd] at hx
      simp only [OptionT.run_bind, Option.elimM, bind_assoc, mem_support_bind_iff,
        liftM_bind, support_liftM, Set.mem_image] at hx
      obtain ⟨sv2opt, hsv2, hx⟩ := hx
      rcases sv2opt with _ | sv2
      · simp at hx
      · simp only [Option.elim, OptionT.run_bind, Option.elimM, bind_assoc, mem_support_bind_iff,
          OptionT.run_pure, liftM_pure, bind_pure_comp, map_bind, liftM_bind, support_liftM,
          Set.mem_image] at hx
        obtain ⟨sv3opt, hsv3, hx⟩ := hx
        rcases sv3opt with _ | sv3
        · simp at hx
        · simp only [Option.elim, Option.getM_some, OptionT.run_pure, map_pure, support_pure,
            Set.mem_singleton_iff, Option.some.injEq] at hx
          subst hx
          exact ⟨tr1, s2, w2, sv2, tr2, hp1, hsv2, hp2, hsv3⟩

end AppendKeystone

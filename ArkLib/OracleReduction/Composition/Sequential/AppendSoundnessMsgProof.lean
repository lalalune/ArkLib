/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.OracleReduction.Composition.Sequential.AppendSoundnessProof
import ArkLib.OracleReduction.RunUnroll

/-!
# Binary sequential-composition soundness (message seam) — `appendSoundnessResidual` discharge

This file assembles the verified seam-decomposition toolkit into the binary append-soundness
keystone for the **message-first seam** case (the case that arises in the BCS compiler, whose
opening phase opens with a commitment/opening prover message, and in LogUp Protocol 2). It targets
`Verifier.appendSoundnessResidual` — the deep, arbitrary-malicious-prover seam decomposition +
union bound shared across issues #13 / #25 / #62 / #433.

## Proof architecture (all bricks proven upstream)

1. **Run factoring.** `Prover.run_seam_factor` splits the arbitrary malicious prover into
   `prover.fst` / `prover.snd`; `Verifier.append_run` (`rfl`) splits `V₁.run ≫ V₂.run`. With
   `FullTranscript.append_fst/snd` and `OptionT.liftM_run_getM_bind` the appended soundness run
   refolds to the canonical seam chain `liftM FST ≫ liftM SND ≫ W1 ≫ W2`.
2. **Reorder** (`seam_swap_probEvent_eq`): commute the `snd` prover stage past the `V₁` verifier
   stage (state-preserving ⇒ distributionally independent) into the union-bound order.
3. **Union bound** (`probComp_seam_union_le`): the bad event `stmtOut ∈ lang₃` factors through the
   intermediate `stmt₂ ∈ lang₂`, giving `ε₁ + ε₂`.
4. **Stage bounds**: `V₁.soundness ε₁` on `prover.fstSound`, `V₂.soundness ε₂` on `prover.sndSound`.

The side conditions `himplSP` / `himplNF` are discharged for the honest interactive implementation
`impl.addLift challengeQueryImpl` by `addLift_state_preserving` / `addLift_neverFail`.
-/

open OracleComp OracleSpec ProtocolSpec OptionTStateT
open scoped ENNReal NNReal

universe u

namespace Verifier

variable {ι : Type} {oSpec : OracleSpec ι} {Stmt₁ Stmt₂ Stmt₃ : Type}
  {m n : ℕ} {pSpec₁ : ProtocolSpec m} {pSpec₂ : ProtocolSpec n}
  [∀ i, SampleableType (pSpec₁.Challenge i)] [∀ i, SampleableType (pSpec₂.Challenge i)]
  {σ : Type} {init : ProbComp σ} {impl : QueryImpl oSpec (StateT σ ProbComp)}

/-- **Binary sequential-composition soundness, message-seam case.** Reduces the appended-verifier
soundness experiment to the two per-phase soundness bounds via the verified seam toolkit. -/
theorem append_soundness_msg'
    [Inhabited Stmt₂]
    (V₁ : Verifier oSpec Stmt₁ Stmt₂ pSpec₁) (V₂ : Verifier oSpec Stmt₂ Stmt₃ pSpec₂)
    {lang₁ : Set Stmt₁} {lang₂ : Set Stmt₂} {lang₃ : Set Stmt₃} {ε₁ ε₂ : ℝ≥0}
    (h₁ : V₁.soundness init impl lang₁ lang₂ ε₁)
    (h₂ : V₂.soundness init impl lang₂ lang₃ ε₂)
    (hn : 0 < n)
    (hDir : (pSpec₁ ++ₚ pSpec₂).dir (⟨m, by omega⟩ : Fin (m + n)) = .P_to_V)
    (hDir₂ : pSpec₂.dir (⟨0, hn⟩ : Fin n) = .P_to_V)
    (himplSP : ∀ (t : oSpec.Domain) (s : σ) (x : oSpec.Range t × σ),
      x ∈ support ((impl t).run s) → x.2 = s)
    (himplNF : ∀ (t : oSpec.Domain) (s : σ), Pr[⊥ | (impl t).run s] = 0) :
    (V₁.append V₂).soundness init impl lang₁ lang₃ (ε₁ + ε₂) := by
  unfold Verifier.soundness
  intro WitIn WitOut witIn prover stmtIn hstmtIn
  intro pImpl
  rw [probEvent_optionT_mk_eq_elim]
  simp only [Reduction.run, Prover.run_seam_factor prover hn hDir hDir₂, Verifier.append_run]
  -- Refold to the canonical seam chain `liftM FST ≫ liftM SND ≫ W1 ≫ W2`.
  simp only [liftM_bind, bind_assoc, map_eq_pure_bind, liftM_map, bind_map_left,
    OptionT.liftM_run_getM_bind, liftM_pure, pure_bind,
    FullTranscript.append_fst, FullTranscript.append_snd]
  -- Bridge the bad-event predicate to the union-bound `¬·∈lang` form.
  rw [show (fun o : Option ((FullTranscript (pSpec₁ ++ₚ pSpec₂) × Stmt₃ × WitOut) × Stmt₃) =>
        o.elim False fun x => x.2 ∈ lang₃)
      = (fun o => ¬ Option.elim o True (fun d => d.2 ∉ lang₃)) from by
        funext o; cases o with
        | none => simp
        | some d => simp only [Option.elim_some, not_not]]
  -- Reorder (`snd` past `V₁`) + two-stage union bound: `stmtOut ∈ lang₃` factors through
  -- `stmt₂ ∈ lang₂`, giving `ε₁ + ε₂`. The goal is in `probComp_seam_swap_union_le`'s natural
  -- order, so all seam pieces are supplied explicitly (first-order; no HO-inference blowup).
  refine probComp_seam_swap_union_le init pImpl (addLift_state_preserving impl himplSP)
    (liftM (prover.fst.run stmtIn witIn))
    (fun x => liftM (prover.snd.run x.2.1 x.2.2))
    _ _
    (fun x s' => simulateQ_run_neverFail _ (addLift_neverFail impl himplNF) _ s')
    (fun s₂ => s₂ ∉ lang₂) (fun d : _ × Stmt₃ => d.2 ∉ lang₃) (ε₁ : ℝ≥0∞) (ε₂ : ℝ≥0∞) ?_ ?_
  · -- Phase-1 bound: `V₁.soundness ε₁` on the phase-1 soundness prover `prover.fstSound`.
    exact h₁ _ _ witIn (Prover.fstSound prover) stmtIn hstmtIn pImpl
  · -- Phase-2 bound: `V₂.soundness ε₂` on the phase-2 soundness prover `prover.sndSound`.
    intro p s' hp
    exact h₂ _ _ p.1.2.1 (Prover.sndSound prover) p.2 hp pImpl

end Verifier

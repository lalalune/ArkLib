/-
Copyright (c) 2024-2025 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/

import ArkLib.OracleReduction.Execution

/-!
# Helper bricks for sequential composition / context lifting of (oracle) reductions

This file collects small, fully-proven, axiom-clean bricks used by the security proofs in
`OracleReduction/Composition/Sequential/Append.lean` and `OracleReduction/LiftContext/Reduction.lean`.

Keeping them here (rather than inline) isolates the reusable support-transport reasoning from the
larger proofs and avoids re-deriving the `liftComp`-support equality each time.
-/

open OracleSpec OracleComp ProtocolSpec

variable {ι : Type} {oSpec : OracleSpec ι}

namespace OracleComp

/-- `OracleComp.liftComp` preserves the support: a value is reachable after lifting to a larger
oracle spec iff it is reachable in the original computation.  This is the support-level shadow of
`evalDist_liftComp` (which gives the full distributional equality). -/
theorem support_liftComp {τ : Type} {superSpec : OracleSpec τ} {α : Type}
    [MonadLift (OracleQuery oSpec) (OracleQuery superSpec)]
    (mx : OracleComp oSpec α) :
    support (OracleComp.liftComp mx superSpec) = support mx := by
  induction mx using OracleComp.inductionOn with
  | pure x => simp
  | query_bind t oa ih =>
      rw [OracleComp.liftComp_bind, OracleComp.liftComp_query]
      ext y
      simp only [support_bind, Set.mem_iUnion, support_map, Set.mem_image,
        OracleComp.support_query, Set.mem_univ, true_and, exists_eq, exists_const,
        OracleQuery.cont_query, OracleQuery.input_query, id_eq, ih]
      constructor
      · rintro ⟨i, -, hi⟩; exact ⟨i, hi⟩
      · rintro ⟨i, hi⟩; exact ⟨i, ⟨i, by simp, rfl⟩, hi⟩

end OracleComp

namespace Reduction

variable {StmtIn WitIn StmtOut WitOut : Type} {n : ℕ} {pSpec : ProtocolSpec n}

/-- The verifier's output statement of any complete result in the support of `Reduction.run` is
itself a reachable output of the verifier on the input statement and the produced full transcript.

This supplies the transcript witness for `Verifier.compatStatement`: the witness transcript is the
`proverResult.1` component of the run result.  The verifier sub-computation appears inside
`Reduction.run` as `liftM (verifier.run stmt td).run`; since `OracleComp.liftComp` preserves the
support (`OracleComp.support_liftComp`), reachability transfers back to the un-lifted
`verifier.run`. -/
theorem verifier_output_mem_run_support
    {reduction : Reduction oSpec StmtIn WitIn StmtOut WitOut pSpec}
    {stmt : StmtIn} {wit : WitIn}
    {x : (FullTranscript pSpec × StmtOut × WitOut) × StmtOut}
    (hx : some x ∈ support (reduction.run stmt wit).run) :
    x.2 ∈ support (reduction.verifier.run stmt x.1.1) := by
  rw [Reduction.run] at hx
  simp only [OptionT.run_bind, Option.elimM] at hx
  rw [mem_support_bind_iff] at hx
  obtain ⟨proverResultOpt, _hprover, hx⟩ := hx
  cases proverResultOpt with
  | none => simp at hx
  | some proverResult =>
      simp only [Option.elim_some, OptionT.run_bind, Option.elimM] at hx
      rw [mem_support_bind_iff] at hx
      obtain ⟨stmtOutOpt, hstmtOut, hx⟩ := hx
      -- `stmtOutOpt : Option (Option StmtOut)`: the outer `Option` is from the monadic bind value,
      -- the inner from the verifier's optional output.  Both must be `some` for `x` to be reachable.
      cases stmtOutOpt with
      | none => simp at hx
      | some vOutOpt =>
          cases vOutOpt with
          | none => simp [Option.getM] at hx
          | some vOut =>
              simp only [Option.elim_some, Option.getM_some, OptionT.run_pure, pure_bind,
                support_pure, Set.mem_singleton_iff, Option.some.injEq] at hx
              have hx2 : x.2 = vOut := congrArg Prod.snd hx
              have hx11 : x.1.1 = proverResult.1 := congrArg (Prod.fst ∘ Prod.fst) hx
              rw [hx2, hx11]
              -- Transfer reachability of `some vOut` from the lifted verifier run to the original.
              -- `hstmtOut : some (some vOut) ∈ support (liftM (V.run …).run).run`.  The lift is
              -- `OptionT.lift ∘ liftComp`, so `(liftM (V.run).run).run = some <$> liftComp (V.run).run`;
              -- `support_liftComp` removes the spec-lift, giving `some vOut ∈ support (V.run …).run`.
              rw [OptionT.mem_support_iff]
              have hLift := hstmtOut
              -- `liftM = monadLift`; expose the lift as `some <$> liftComp (V.run).run`.
              have hrun : (liftM (reduction.verifier.run stmt proverResult.1).run :
                    OptionT (OracleComp (oSpec + [pSpec.Challenge]ₒ)) (Option StmtOut)).run
                  = some <$> OracleComp.liftComp (reduction.verifier.run stmt proverResult.1).run
                      (oSpec + [pSpec.Challenge]ₒ) := by
                rw [liftComp_eq_liftM]; rfl
              rw [hrun, support_map, OracleComp.support_liftComp, Set.mem_image] at hLift
              obtain ⟨w, hw, hwEq⟩ := hLift
              rw [Option.some.injEq] at hwEq
              rwa [← hwEq]

end Reduction

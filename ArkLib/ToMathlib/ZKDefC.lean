/-
Copyright (c) 2024-2025 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/

import ArkLib.OracleReduction.Security.ZeroKnowledge

/-!
  # Migrated ZK Instance Scratch

  The Brick C zero-round identity HVZK instance has been promoted to
  `ArkLib.OracleReduction.Security.ZeroKnowledge`. This file remains as a compatibility re-export
  for existing scratch imports.
-/
<<<<<<< Updated upstream
=======

noncomputable section

open OracleComp OracleSpec ProtocolSpec
open scoped NNReal

namespace Reduction

variable {ι : Type} {oSpec : OracleSpec ι}
  {StmtIn WitIn : Type}
  {σ : Type}

/-- The simulator for the trivial reduction: ignore the statement and emit the unique empty
  transcript of the empty protocol specification. -/
def idTranscriptSimulator :
    TranscriptSimulator oSpec StmtIn (!p[] : ProtocolSpec 0) :=
  fun _ => pure default

/-- The underlying `ProbComp` of the honest transcript distribution of the trivial reduction is
  `init >>= fun _ => pure (some default)`: it samples the ambient state (from `init`) but, since the
  reduction has no messages and the verifier always accepts, deterministically returns the empty
  transcript `default`, *independent of the witness and of `impl`*. -/
theorem honestTranscriptDist_id_run
    (init : ProbComp σ) (impl : QueryImpl oSpec (StateT σ ProbComp))
    (stmtIn : StmtIn) (witIn : WitIn) :
    (honestTranscriptDist init impl
        (Reduction.id : Reduction oSpec StmtIn WitIn StmtIn WitIn !p[]) stmtIn witIn).run =
      init >>= fun _ => pure (some default) := by
  unfold honestTranscriptDist
  -- After `id_run`, the run is `pure ⟨⟨default, stmt, wit⟩, stmt⟩`; the transcript marginal is
  -- `pure (some default)`, `simulateQ` of a `pure` is `pure`, and `run'` discards the state.
  simp only [Reduction.id_run, map_pure, OptionT.run_pure, simulateQ_pure, StateT.run'_eq,
    OptionT.run_mk, StateT.run_pure, map_pure, bind_pure_comp]

/-- **Concrete perfect HVZK instance.**  The trivial / `DoNothing` reduction satisfies perfect
  honest-verifier zero-knowledge for *any* input relation, witnessed by `idTranscriptSimulator`.

  Proof: the honest transcript distribution samples `init` then deterministically returns the empty
  transcript; since `init` is a proper probability computation (no failure in `ProbComp`), its
  `evalDist` equals that of `pure default`, which is exactly the simulator's distribution. -/
theorem id_perfectHVZK
    (init : ProbComp σ) (impl : QueryImpl oSpec (StateT σ ProbComp))
    (rel : Set (StmtIn × WitIn)) :
    perfectHVZK init impl rel
      (Reduction.id : Reduction oSpec StmtIn WitIn StmtIn WitIn !p[])
      idTranscriptSimulator := by
  intro stmtIn witIn _
  -- Reduce both sides to `evalDist` on the underlying `ProbComp`.
  show evalDist (idTranscriptSimulator stmtIn) =
    evalDist (honestTranscriptDist init impl Reduction.id stmtIn witIn)
  rw [show (idTranscriptSimulator (oSpec := oSpec) (StmtIn := StmtIn) stmtIn) =
      (pure default : OptionT ProbComp (FullTranscript !p[])) from rfl]
  -- `evalDist` on `OptionT m` is `evalDist` of the underlying `m`-computation (`.run`).
  have hrun := honestTranscriptDist_id_run init impl stmtIn witIn
  -- Compare via the underlying ProbComp computations.
  rw [show evalDist (honestTranscriptDist init impl
        (Reduction.id : Reduction oSpec StmtIn WitIn StmtIn WitIn !p[]) stmtIn witIn) =
      evalDist ((honestTranscriptDist init impl
        (Reduction.id : Reduction oSpec StmtIn WitIn StmtIn WitIn !p[]) stmtIn witIn).run) from rfl]
  rw [show evalDist (pure default : OptionT ProbComp (FullTranscript !p[])) =
      evalDist ((pure default : OptionT ProbComp (FullTranscript !p[])).run) from rfl]
  rw [hrun, OptionT.run_pure]
  exact (evalDist_bind_const_of_no_failure init (pure (some default))).symm

/-- The trivial reduction is honest-verifier zero-knowledge for any relation. -/
theorem id_isHVZK
    (init : ProbComp σ) (impl : QueryImpl oSpec (StateT σ ProbComp))
    (rel : Set (StmtIn × WitIn)) :
    isHVZK init impl rel
      (Reduction.id : Reduction oSpec StmtIn WitIn StmtIn WitIn !p[]) :=
  ⟨idTranscriptSimulator, id_perfectHVZK init impl rel⟩

end Reduction
>>>>>>> Stashed changes

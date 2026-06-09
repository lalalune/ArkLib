/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.OracleReduction.Composition.Sequential.SeamDecompositionRun
import ArkLib.OracleReduction.Composition.Sequential.ChallengeSeamBridge
import ArkLib.OracleReduction.Composition.Sequential.SeamCompleteness

/-!
# Sequential-composition soundness: the seam stage-swap under a leading bind

This file builds toward `Verifier.append_soundness` (the soundness half of the #433 keystone). The
soundness experiment runs the malicious prover fully first (`fst` then `snd`), then the composed
verifier (`V₁` then `V₂`): order `fst, snd, V₁, V₂`. To apply the two-stage union bound
`probComp_seam_union_le` (the bad event `stmtOut ∈ lang₃` factors through the intermediate
`stmt₂ ∈ lang₂`) the experiment must be regrouped as `(fst ≫ V₁) ≫ (snd ≫ V₂)`: the `snd`
prover stage and the `V₁` verifier stage must be swapped.

Under a **state-preserving** oracle implementation (`hso`; the soundness analogue of the
completeness proof's `hImplSupp`, discharged for `impl.addLift challengeQueryImpl` by
`OptionTStateT.addLift_state_preserving`), the two stages are distributionally independent and
commute. `OptionTStateT.evalDist_simulateQ_swap` performs the top-level swap; this file lifts it
to a swap **under a leading bind** (the `fst` stage), which is the shape the appended run has.

## Verified reduction recipe (toward `Verifier.append_soundness`)

The appended soundness run reduces to the exact swap-canonical form. With
`so := impl.addLift challengeQueryImpl` and `hso := addLift_state_preserving impl himplSP`:

1. **Run factoring** (verified): for the malicious prover `prover` over `pSpec₁ ++ₚ pSpec₂`,
   `((Reduction.mk prover (V₁.append V₂)).run stmtIn witIn).run` rewrites — via
   `Reduction.run`, `Prover.run_seam_factor prover hn hDir hDir₂`, `Verifier.append_run`, and the
   `simp only` set
   `[OptionT.run_bind, bind_assoc, Option.elimM, map_bind, OptionT.run_liftM_run,
     OptionT.run_pure, Option.getM, liftM_bind, Option.elim_some, OptionT.run_mk, bind_pure_comp,
     OptionT.run_lift, OptionT.run_monadLift, monadLift_eq_self, bind_map_left, Functor.map_map,
     FullTranscript.append_fst, FullTranscript.append_snd]`
   — to the plain `OracleComp` chain
   `P >>= fun x => A x >>= fun a => B x >>= fun b => k x a b`, where
   `P = liftM (prover.fst.run stmtIn witIn)`, `A x = liftM (prover.snd.run x.2.1 x.2.2)`,
   `B x = simulateQ idLift (V₁.run stmtIn x.1).run` (the `Option Stmt₂` from `V₁`), and `k`
   short-circuits on `b`, runs `V₂`, and assembles the output. (The `append_fst`/`append_snd`
   rewrites make `B` depend only on `x`, the shape `evalDist_simulateQ_swap_under` requires.)
2. **Swap** (this file): `evalDist_simulateQ_swap_under so hso P A B k s` commutes `A` (snd) and `B`
   (V₁), giving `P >>= fun x => B x >>= fun b => A x >>= fun a => k x a b` — the clean
   `fst, V₁, snd, V₂` order.
3. **Elim-commute**: `OptionTStateT.probEvent_elim_comm` moves the never-failing `snd` stage into
   the `some`-branch of `V₁`'s short-circuit, matching `(mxClean >>= myClean).run` for
   `mxClean = fst ≫ V₁`, `myClean = snd ≫ V₂`.
4. **Union bound**: `OracleReduction.probComp_seam_union_le` on `mxClean >>= myClean` with
   `pg = (· ∉ lang₂)`, `qg = (· ∉ lang₃)`, reducing the two stage hypotheses to soundness
   (`h₁`/`h₂`) on `prover.fst`/`prover.snd` via the proven challenge-seam bridges.

Steps 1–2 are verified; 3–4 plus the two stage-soundness bounds remain. The deliverable carries
the state-preservation/value-blind `impl` side-conditions (`himplSP`, discharged for the actual
`impl.addLift challengeQueryImpl` by `addLift_state_preserving`) — the soundness analogue of the
completeness proof's `hImplSupp`.
-/

open OracleComp OracleSpec ProtocolSpec OptionTStateT
open scoped ENNReal

namespace OptionTStateT

variable {ι : Type} {spec : OracleSpec ι} {σ : Type}

/-- **Seam stage swap under a leading bind.** Generalises `evalDist_simulateQ_swap` to swap the two
inner stages `A`, `B` that sit underneath a leading stage `P` whose output `r` both inner stages may
depend on. Under state-preservation (`hso`) every stage runs from the same starting state, so the
`A`/`B` binds commute (`SPMF.bind_comm`). This is the exact shape of the appended soundness run:
`P = fst` prover, `A = snd` prover, `B = V₁`, and `k` finishes with `V₂` and the output. -/
theorem evalDist_simulateQ_swap_under
    (so : QueryImpl spec (StateT σ ProbComp))
    (hso : ∀ (t : spec.Domain) (s : σ) (x : spec.Range t × σ),
      x ∈ support ((so t).run s) → x.2 = s)
    {ρ α β γ : Type}
    (P : OracleComp spec ρ)
    (A : ρ → OracleComp spec α) (B : ρ → OracleComp spec β)
    (k : ρ → α → β → OracleComp spec γ) (s : σ) :
    evalDist ((simulateQ so (P >>= fun r => A r >>= fun a => B r >>= fun b => k r a b)).run' s)
      = evalDist ((simulateQ so (P >>= fun r => B r >>= fun b => A r >>= fun a => k r a b)).run' s)
        := by
  rw [StateT.run'_eq, StateT.run'_eq, evalDist_map, evalDist_map]
  congr 1
  simp only [simulateQ_run_bind_state_fixed so hso, evalDist_bind]
  refine bind_congr fun p => ?_
  exact SPMF.bind_comm _ _ _

end OptionTStateT

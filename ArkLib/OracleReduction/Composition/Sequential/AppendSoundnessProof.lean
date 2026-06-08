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
`stmt₂ ∈ lang₂`) the experiment must be regrouped as `(fst ≫ V₁) ≫ (snd ≫ V₂)`, i.e. the `snd`
prover stage and the `V₁` verifier stage must be swapped.

Under a **state-preserving** oracle implementation (`hso`; the soundness analogue of the
completeness proof's `hImplSupp`, discharged for `impl.addLift challengeQueryImpl` by
`OptionTStateT.addLift_state_preserving`), the two stages are distributionally independent and
commute. `OptionTStateT.evalDist_simulateQ_swap` performs the top-level swap; this file lifts it to a
swap **under a leading bind** (the `fst` stage), which is the shape the appended run actually has.
-/

open OracleComp OracleSpec ProtocolSpec OptionTStateT
open scoped ENNReal

namespace OptionTStateT

variable {ι : Type} {spec : OracleSpec ι} {σ : Type}

/-- **Seam stage swap under a leading bind.** Generalises `evalDist_simulateQ_swap` to swap the two
inner stages `A`, `B` that sit underneath a leading stage `P` whose output `r` both inner stages may
depend on. Under state-preservation (`hso`) every stage runs from the same starting state, so the
`A`/`B` binds commute (`SPMF.bind_comm`). This is the exact shape of the appended soundness run:
`P = fst` prover, `A = snd` prover, `B = V₁`, and `k` finishes with `V₂` and the output assembly. -/
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

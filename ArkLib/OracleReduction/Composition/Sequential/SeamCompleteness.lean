/-
Copyright (c) 2025 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import ArkLib.OracleReduction.RunUnroll

/-!
# Two-stage seam *completeness* union bound

This is the **completeness** counterpart of `probComp_seam_union_le` (the soundness two-stage seam
union bound in `RunUnroll.lean`). The difference is the failure convention: for *completeness* a
`none` (failed) output **does** count as a failure (the honest run is supposed to succeed), whereas
for soundness `none` is benign. Concretely the "good" predicates here are
`fun o => Option.elim o False g` — `none ↦ False` (so its complement `¬ Option.elim · False g` is the
*bad* event, and `none` is bad).

This is exactly the "standard two-stage success-probability union bound" that the message-seam
sequential-composition completeness keystone (`reduction_append_completeness` for the message seam)
consumes: once the appended *honest* reduction run is factored distributionally as `mx >>= my`
(stage 1 then stage 2, via `Prover.append_run_evalDist_msg` + `Verifier.append_run`), this lemma
discharges the probabilistic union bound `e₁ + e₂`.
-/

open OracleComp OracleSpec ProtocolSpec OptionTStateT
open scoped ENNReal

namespace OracleReduction

variable {ι : Type} {spec : OracleSpec ι} {σ α β : Type}

/-- **Two-stage seam completeness union bound (`ProbComp` level).** The completeness analogue of
`probComp_seam_union_le`: for the honest game
`init >>= fun s => (simulateQ so (mx >>= my).run).run' s`, if the stage-1 bad event
(`¬ Option.elim ·.1 False pg` — `none` *or* `¬ pg`) on the state-threaded stage-1 run is bounded by
`e₁`, and for every stage-1 success `(some a, s')` with `pg a` the stage-2 bad event
(`¬ Option.elim · False qg` — `none` *or* `¬ qg`) of `my a` run from `s'` is bounded by `e₂`, then
the full game's bad event is bounded by `e₁ + e₂`.

Combines `simulateQ_run'_optionT_bind_run` (the OptionT stage split) with `probEvent_bind_le_add`.
Predicates are in `¬ Option.elim · False ·` (bad-event) form; here `none` (failure) **is** bad, which
is the completeness convention. The stage-1 `none` branch is absorbed into `e₁` (it makes the good
predicate `pg` vacuously fail), so the per-success hypothesis `h₂` only fires on genuine
`(some a, s')` continuations. -/
theorem probComp_seam_completeness
    (init : ProbComp σ) (so : QueryImpl spec (StateT σ ProbComp))
    (mx : OptionT (OracleComp spec) α) (my : α → OptionT (OracleComp spec) β)
    (pg : α → Prop) (qg : β → Prop) (e₁ e₂ : ℝ≥0∞)
    (h₁ : Pr[fun r => ¬ Option.elim r.1 False pg
          | init >>= fun s => (simulateQ so mx.run).run s] ≤ e₁)
    (h₂ : ∀ a s', (some a, s') ∈ support (init >>= fun s => (simulateQ so mx.run).run s) → pg a →
          Pr[fun o => ¬ Option.elim o False qg
            | (simulateQ so (my a).run).run' s'] ≤ e₂) :
    Pr[fun o => ¬ Option.elim o False qg
        | init >>= fun s => (simulateQ so (mx >>= my).run).run' s] ≤ e₁ + e₂ := by
  classical
  have hgame : (init >>= fun s => (simulateQ so ((mx >>= my).run)).run' s)
      = (init >>= fun s => (simulateQ so mx.run).run s) >>= fun r =>
          r.1.elim (pure none) (fun a => (simulateQ so (my a).run).run' r.2) := by
    rw [bind_assoc]
    refine bind_congr fun s => ?_
    rw [simulateQ_run'_optionT_bind_run]
  rw [hgame]
  refine probEvent_bind_le_add
    (mx := init >>= fun s => (simulateQ so mx.run).run s)
    (p := fun (r : Option α × σ) => Option.elim r.1 False pg)
    (q := fun (o : Option β) => Option.elim o False qg) h₁ ?_
  rintro ⟨o, s'⟩ hmem hp
  cases o with
  | none => exact hp.elim
  | some a => exact h₂ a s' hmem hp

end OracleReduction

#print axioms OracleReduction.probComp_seam_completeness

/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.ProofSystem.Logup.Security.RbrToSoundBridge
import ArkLib.OracleReduction.RunUnroll
import ArkLib.OracleReduction.ProcessRoundSupport

/-!
# Discharging the MarginalBridge residual (issue #13)

Proof of `Verifier.MarginalBridge` (the rbr→soundness per-round marginal domination) from the
proven trailing-drop + union-bound infrastructure in `Security/RoundByRound.lean`, under the
single **state-preservation side condition** `hso` on the shared-oracle implementation (the same
side condition the sequential-composition seam toolkit `probComp_seam_swap_union_le` consumes,
dischargeable for the LogUp instantiations via `OptionTStateT.addLift_state_preserving`).

## Why `hso` is necessary (the statement is FALSE without it)

`StateFunction.toFun_full` bounds the verifier-accept probability only over runs started from a
*fresh* `init` state.  The full soundness run threads the implementation state from the prover
interaction into the verifier.  For a state-*mutating* `impl` the two need not agree: take
`σ := Bool`, `init := pure false`, an oracle answering with its current state and setting it to
`true`, a verifier accepting iff the answer is `true`, and a 1-round (`P_to_V`-only) protocol
whose malicious prover queries the oracle once.  Then the all-false state function satisfies
every `StateFunction` field (from `init` the verifier always rejects), `pSpec.ChallengeIdx` is
empty so `∑ i, rbrGameFlipProb … i = 0`, yet the full run accepts with probability `1`.  Hence
the unconditional `MarginalBridge` is false, and `hso` (every query implementation returns the
state it was given, on its support) is the honest minimal repair: it pins the post-prover state
back to the `init` sample, which is exactly the seam `toFun_full` needs.

## Structure

* `probEvent_simulateQ_run'_optionMap_const_trailing_le` — trailing drop for an `Option`-valued
  trailing stage whose successful value is constant in the trailing output (the verifier/`getM`
  tail of the soundness run, after marginalizing the event to the transcript).
* `Prover.continueFromTo_take_support` — the rounds after `k` preserve the round-`k` transcript
  prefix on the support (folds `processRound_support_restrict`).
* `Transcript.concat_take_eq` — taking back the length-`k` prefix of `concat` returns the input.
* `Verifier.reduction_run_run_nf` — `(Reduction.run …).run` in prover-stage/verifier-stage
  normal form with the only genuine `Option` short-circuit absorbed into an `Option.map`.
* `Verifier.fullRun_flip_marginal_le_rbrGameFlipProb` — the per-round trailing-drop core: the
  full-run flip marginal is dominated by the round-by-round game's flip probability
  (unconditional; no `hso` needed).
* `Verifier.marginalBridge_holds` — the assembly: union bound + first-crossing pigeonhole + the
  `hso`-gated `toFun_full` contradiction.
-/

noncomputable section

open OracleComp OracleSpec ProtocolSpec
open scoped NNReal ENNReal

section Bricks

variable {ι' : Type} {spec : OracleSpec ι'} {σ' : Type}

/-- **Trailing drop for an `Option`-valued trailing stage with prefix-constant success value.**
After the prefix `mx` produces `a`, the run executes a trailing (possibly-failing,
possibly-`none`-returning) `gb a` whose output is kept only through `Option.map (fun _ => h a)` —
i.e. the final *success* value is the prefix-determined `h a`, and the trailing stage contributes
only its success/failure verdict.  Dropping the trailing stage (and the `Option` layer) can only
raise the probability of an event that is `False` on `none`. -/
theorem probEvent_simulateQ_run'_optionMap_const_trailing_le {α β γ : Type}
    (so : QueryImpl spec (StateT σ' ProbComp)) (s : σ')
    (mx : OracleComp spec α) (gb : α → OracleComp spec (Option γ)) (h : α → β) (p : β → Prop) :
    Pr[fun o : Option β => o.elim False p |
        (simulateQ so (mx >>= fun a => gb a >>= fun og =>
          (pure (Option.map (fun _ => h a) og) : OracleComp spec (Option β)))).run' s]
      ≤ Pr[p | (simulateQ so (mx >>= fun a => (pure (h a) : OracleComp spec β))).run' s] := by
  classical
  simp only [simulateQ_bind]
  rw [StateT.run'_eq, StateT.run'_eq, StateT.run_bind, StateT.run_bind]
  rw [probEvent_map, probEvent_map]
  refine Verifier.StateFunction.probEvent_bind_mono_heteroEvent (fun pr _ => ?_)
  obtain ⟨a, s'⟩ := pr
  simp only [simulateQ_bind, simulateQ_pure, StateT.run_bind, StateT.run_pure]
  by_cases hpa : p (h a)
  · refine le_trans probEvent_le_one (le_of_eq ?_)
    rw [probEvent_pure_eq_indicator]
    simp [Set.indicator, Function.comp, hpa]
  · rw [probEvent_pure_eq_indicator]
    simp only [Set.indicator, Set.mem_setOf_eq, Function.comp_apply, hpa, if_false,
      nonpos_iff_eq_zero]
    rw [probEvent_eq_zero_iff]
    rintro ⟨o, s''⟩ ho
    rw [mem_support_bind_iff] at ho
    obtain ⟨q, _, hq⟩ := ho
    simp only [support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at hq
    obtain ⟨rfl, rfl⟩ := hq
    cases hq1 : q.1 with
    | none => simp [hq1]
    | some c => simp [hq1, hpa]

end Bricks

namespace Prover

variable {ι : Type} {oSpec : OracleSpec ι} {n : ℕ} {pSpec : ProtocolSpec n}
  {StmtIn WitIn StmtOut WitOut : Type}

/-- **The rounds after `k` preserve the round-`k` transcript prefix on the support.**  Folded
version of `processRound_support_restrict`: every support output of the continuation
`continueFromTo k j` (for `k ≤ j`) restricts, on the first `k` rounds, to the input transcript. -/
theorem continueFromTo_take_support
    (prover : Prover oSpec StmtIn WitIn StmtOut WitOut pSpec)
    (stmt : StmtIn) (wit : WitIn) (k j : Fin (n + 1)) (hkj : k ≤ j)
    (a : pSpec.Transcript k × prover.PrvState k)
    (b : pSpec.Transcript j × prover.PrvState j)
    (hb : b ∈ support (prover.continueFromTo stmt wit k j a)) :
    (b.1.take k.val (by exact_mod_cast hkj) : pSpec.Transcript k) = a.1 := by
  induction j using Fin.induction with
  | zero =>
    have hk0 : k = 0 := le_antisymm hkj (Fin.zero_le _)
    subst hk0
    exact Subsingleton.elim (α := pSpec.Transcript 0) _ _
  | succ m ih =>
    by_cases hk : k = m.succ
    · subst hk
      rw [continueFromTo_self, support_pure, Set.mem_singleton_iff] at hb
      subst hb
      rfl
    · have hk' : k ≤ m.castSucc := by
        rw [Fin.le_castSucc_iff]
        exact lt_of_le_of_ne hkj hk
      rw [continueFromTo_succ_of_ne prover stmt wit k m hk a] at hb
      obtain ⟨ts, hts, hpres⟩ := processRound_support_restrict m prover _ b hb
      have hIH := ih hk' ts hts
      funext jj
      have hidx := hpres (Fin.castLE (by exact_mod_cast hk') jj)
      have hIH' := congrFun hIH jj
      exact hidx.trans hIH'

end Prover

namespace ProtocolSpec.Transcript

variable {n : ℕ} {pSpec : ProtocolSpec n}

/-- Taking back the length-`i.castSucc` prefix of `concat` recovers the input transcript. -/
theorem concat_take_eq (i : Fin n) (t : Transcript i.castSucc pSpec) (ch : pSpec.«Type» i) :
    (((t.concat ch : Transcript i.succ pSpec)).take i.castSucc.val
        (by simp [Fin.le_def]) : Transcript i.castSucc pSpec) = t := by
  funext j
  exact Fin.snoc_castSucc (α := fun k : Fin (i.1 + 1) =>
    pSpec.«Type» (Fin.castLE i.succ.is_le k)) ch t j

end ProtocolSpec.Transcript

namespace Verifier

open StateFunction OptionTStateT Prover

variable {ι : Type} {oSpec : OracleSpec ι}
  {StmtIn StmtOut : Type} {n : ℕ} {pSpec : ProtocolSpec n}
  [∀ i, SampleableType (pSpec.Challenge i)]
  {σ : Type} {init : ProbComp σ} {impl : QueryImpl oSpec (StateT σ ProbComp)}

omit [∀ i, SampleableType (pSpec.Challenge i)] in
/-- **`(Reduction.run …).run` in two-stage normal form.**  The full soundness run is: the prover's
(plain, never-failing) run, then the (lifted) verifier run, with the only genuine `Option`
short-circuit (`getM`) absorbed into an `Option.map` of the final pairing. -/
theorem reduction_run_run_nf {WitIn WitOut : Type}
    (prover : Prover oSpec StmtIn WitIn StmtOut WitOut pSpec)
    (verifier : Verifier oSpec StmtIn StmtOut pSpec)
    (stmtIn : StmtIn) (witIn : WitIn) :
    ((Reduction.mk prover verifier).run stmtIn witIn).run
      = prover.run stmtIn witIn >>= fun pr =>
          (OracleComp.liftComp ((verifier.run stmtIn pr.1).run) (oSpec + [pSpec.Challenge]ₒ))
            >>= fun o =>
          (pure (o.map (fun v => (pr, v))) :
            OracleComp (oSpec + [pSpec.Challenge]ₒ)
              (Option ((FullTranscript pSpec × StmtOut × WitOut) × StmtOut))) := by
  rw [Reduction_run_def]
  simp only [OptionT.run_bind, Option.elimM, OptionTStateT.lift_run_elim, OptionT.run_pure]
  refine bind_congr fun x => bind_congr fun o => ?_
  cases o <;> rfl

end Verifier

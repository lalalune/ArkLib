/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.OracleReduction.Composition.Sequential.AppendRbrKnowledgeOracleLift

/-!
# The optionization reduction: failing-deterministic seams reduce to total-deterministic ones

The rbr (knowledge) soundness append keystone takes a *total* determinism witness
`hVerify : V₁ = ⟨fun stmt tr => pure (verify stmt tr)⟩`. RingSwitching's sumcheck-side verifiers are
**failing**-deterministic (`else failure`), so that witness is unavailable for the
`coreInteraction`/`full` seams.

This file implements the **optionization reduction** (issue #29): a failing-deterministic left
verifier `⟨fun s t => OptionT.mk (pure (verify? s t))⟩` (with `verify? : Stmt₁ → FullTranscript →
Option Stmt₂`) factors through the *total*-deterministic verifier over the optionized intermediate
statement `Option Stmt₂`, with the right phase lifted by `Verifier.optionLift` (fail on `none`,
defer on `some`). The appended verifiers are **equal** (`append_failingDet_eq_optionized`), so the
existing total-det keystone applies at the intermediate type `Option Stmt₂` — no re-threading of the
state-function chain, no protocol change.
-/

open OracleComp OracleSpec ProtocolSpec
open scoped ENNReal NNReal

universe u

namespace Verifier

variable {ι : Type} {oSpec : OracleSpec ι} {Stmt₁ Stmt₂ Stmt₃ : Type}
    {m n : ℕ} {pSpec₁ : ProtocolSpec m} {pSpec₂ : ProtocolSpec n}

/-- **Option-lift of a verifier.** Runs `V` on `some` inputs and fails on `none` — the right-phase
companion of the optionization reduction: a failing-deterministic left phase hands `V₂.optionLift`
its (possibly absent) intermediate statement. -/
def optionLift (V : Verifier oSpec Stmt₂ Stmt₃ pSpec₂) :
    Verifier oSpec (Option Stmt₂) Stmt₃ pSpec₂ :=
  ⟨fun s? tr => match s? with
    | none => failure
    | some s => V.verify s tr⟩

@[simp] theorem optionLift_verify_some (V : Verifier oSpec Stmt₂ Stmt₃ pSpec₂)
    (s : Stmt₂) (tr : pSpec₂.FullTranscript) :
    (V.optionLift).verify (some s) tr = V.verify s tr := rfl

@[simp] theorem optionLift_verify_none (V : Verifier oSpec Stmt₂ Stmt₃ pSpec₂)
    (tr : pSpec₂.FullTranscript) :
    (V.optionLift).verify (none : Option Stmt₂) tr = failure := rfl

/-- **The optionization seam-rewrite.** Appending a *failing*-deterministic left verifier to `V₂`
equals appending its *total*-deterministic optionization (the same `verify?`, now as an honest
output statement) to `V₂.optionLift`. This rewrites a failing-det seam into a total-det seam over
the intermediate type `Option Stmt₂`, where the rbr (knowledge) soundness append keystone's
`hVerify` is available. -/
theorem append_failingDet_eq_optionized
    (verify? : Stmt₁ → pSpec₁.FullTranscript → Option Stmt₂)
    (V₂ : Verifier oSpec Stmt₂ Stmt₃ pSpec₂) :
    Verifier.append (⟨fun s tr => OptionT.mk (pure (verify? s tr))⟩ :
        Verifier oSpec Stmt₁ Stmt₂ pSpec₁) V₂
      = Verifier.append (⟨fun s tr => pure (verify? s tr)⟩ :
          Verifier oSpec Stmt₁ (Option Stmt₂) pSpec₁) V₂.optionLift := by
  unfold Verifier.append
  congr 1
  funext s tr
  refine OptionT.ext ?_
  simp only [OptionT.run_bind, OptionT.run_mk, OptionT.run_pure, Option.elimM, pure_bind]
  cases h : verify? s tr.fst with
  | none => simp [optionLift]
  | some s₂ => simp [optionLift]

/-- The optionized intermediate relation: `(s?, w)` is related iff `s?` is `some s` with `(s, w)`
in the underlying relation. The `none` (failed-crossing) statement is related to nothing — it is
*doomed*, which is what makes the `optionLift` transports sound. -/
def optionRel {Stmt₂ Wit₂ : Type} (r : Set (Stmt₂ × Wit₂)) : Set (Option Stmt₂ × Wit₂) :=
  {p | ∃ s, p.1 = some s ∧ (s, p.2) ∈ r}

@[simp] theorem mem_optionRel_some {Stmt₂ Wit₂ : Type} {r : Set (Stmt₂ × Wit₂)}
    {s : Stmt₂} {w : Wit₂} : ((some s, w) ∈ optionRel r) ↔ (s, w) ∈ r := by
  simp [optionRel]

@[simp] theorem not_mem_optionRel_none {Stmt₂ Wit₂ : Type} {r : Set (Stmt₂ × Wit₂)}
    {w : Wit₂} : ((none, w) ∈ optionRel r) ↔ False := by
  simp [optionRel]

variable {Wit₂ Wit₃ : Type} {σ : Type} {init : ProbComp σ}
    {impl : QueryImpl oSpec (StateT σ ProbComp)}
    [∀ i, SampleableType (pSpec₂.Challenge i)]

/-- **Statement-precomposition of a prover.** Reindexes a prover over `Option Stmt₂`-statements to a
prover over `Stmt₂` by wrapping the input statement in `some`; all rounds and the output are
untouched, so all partial runs agree definitionally. -/
def _root_.Prover.someStmt {Stmt₃' Wit₃' : Type}
    (P : Prover oSpec (Option Stmt₂) Wit₂ Stmt₃' Wit₃' pSpec₂) :
    Prover oSpec Stmt₂ Wit₂ Stmt₃' Wit₃' pSpec₂ where
  PrvState := P.PrvState
  input := fun ctx => P.input (some ctx.1, ctx.2)
  sendMessage := P.sendMessage
  receiveChallenge := P.receiveChallenge
  output := P.output

@[simp] theorem _root_.Prover.someStmt_runWithLogToRound {Stmt₃' Wit₃' : Type}
    (P : Prover oSpec (Option Stmt₂) Wit₂ Stmt₃' Wit₃' pSpec₂)
    (i : Fin (n + 1)) (s : Stmt₂) (w : Wit₂) :
    (P.someStmt).runWithLogToRound i s w = P.runWithLogToRound i (some s) w := rfl

/-- **`optionLift` preserves round-by-round knowledge soundness** (with the optionized input
relation). The knowledge state function sends `none`-statement states to `False` (the failed
crossing is doomed); the extractor reads the `some`-component (with an `Inhabited` default on the
irrelevant `none` leg); the per-round bound at a `none` statement is the probability of an
event with a `False` conjunct, and at `some s` defers to the inner bound via statement
precomposition. -/
theorem optionLift_rbrKnowledgeSoundness [Inhabited Stmt₂]
    (V : Verifier oSpec Stmt₂ Stmt₃ pSpec₂)
    {rel₂ : Set (Stmt₂ × Wit₂)} {rel₃ : Set (Stmt₃ × Wit₃)}
    {err : pSpec₂.ChallengeIdx → ℝ≥0}
    (h : V.rbrKnowledgeSoundness init impl rel₂ rel₃ err) :
    (V.optionLift).rbrKnowledgeSoundness init impl (optionRel rel₂) rel₃ err := by
  obtain ⟨WitMid, E, kSF, hBound⟩ := h
  refine ⟨WitMid,
    { eqIn := E.eqIn
      extractMid := fun m s? tr w => E.extractMid m (s?.getD default) tr w
      extractOut := fun s? tr w => E.extractOut (s?.getD default) tr w },
    { toFun := fun m s? tr w => match s? with
        | some s => kSF.toFun m s tr w
        | none => False
      toFun_empty := fun s? w => by
        cases s? with
        | some s => simpa using kSF.toFun_empty s w
        | none => simp
      toFun_next := fun m hDir s? tr msg w hnext => by
        cases s? with
        | some s => exact kSF.toFun_next m hDir s tr msg w hnext
        | none => exact hnext.elim
      toFun_full := fun s? tr w hPos => by
        cases s? with
        | some s => exact kSF.toFun_full s tr w hPos
        | none =>
          -- `optionLift.run none = failure`: the run always yields `none`, so the acceptance
          -- probability is `0`, contradicting `hPos`.
          exfalso
          rw [gt_iff_lt, probEvent_pos_iff] at hPos
          obtain ⟨x, hx, -⟩ := hPos
          rw [OptionT.mem_support_iff] at hx
          simp only [OptionT.run_mk, support_bind, Set.mem_iUnion] at hx
          obtain ⟨s, -, hmem⟩ := hx
          -- the simulated `failure` run is definitionally the constant-`none` computation
          rw [show ((simulateQ impl ((V.optionLift).run (none : Option Stmt₂) tr)).run' s :
                ProbComp (Option Stmt₃))
              = pure none from rfl] at hmem
          simp at hmem },
    ?_⟩
  intro s? w P i
  cases s? with
  | none =>
    -- the flip event's second conjunct is `False` at a `none` statement: probability `0`.
    refine le_trans (le_of_eq (probEvent_eq_zero ?_)) (zero_le _)
    rintro ⟨tr, ch, log⟩ _
    rintro ⟨wm, -, hsucc⟩
    exact hsucc
  | some s =>
    -- precompose the prover and defer to the inner per-round bound at `s`.
    simpa using hBound s w P.someStmt i

end Verifier

-- Axiom audit: must report only `[propext, Classical.choice, Quot.sound]` (no `sorryAx`).
#print axioms Verifier.append_failingDet_eq_optionized
#print axioms Verifier.optionLift_rbrKnowledgeSoundness

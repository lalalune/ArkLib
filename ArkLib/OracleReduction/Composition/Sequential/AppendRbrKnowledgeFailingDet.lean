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

end Verifier

-- Axiom audit: must report only `[propext, Classical.choice, Quot.sound]` (no `sorryAx`).
#print axioms Verifier.append_failingDet_eq_optionized

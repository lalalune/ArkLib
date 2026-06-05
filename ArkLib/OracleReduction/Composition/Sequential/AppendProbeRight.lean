/-
Copyright (c) 2024-2025 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

import ArkLib.OracleReduction.Composition.Sequential.Append

/-! # PROBE (right block): scratch for the right half of `Prover.append_run`. -/

open OracleComp OracleSpec SubSpec ProtocolSpec

universe u v

variable {ι : Type} {oSpec : OracleSpec ι} {Stmt₁ Wit₁ Stmt₂ Wit₂ Stmt₃ Wit₃ : Type}
  {m n : ℕ} {pSpec₁ : ProtocolSpec m} {pSpec₂ : ProtocolSpec n}

namespace Prover

variable {P₁ : Prover oSpec Stmt₁ Wit₁ Stmt₂ Wit₂ pSpec₁}
    {P₂ : Prover oSpec Stmt₂ Wit₂ Stmt₃ Wit₃ pSpec₂}

/-- PrvState of the appended prover at a *right interior* round `m + 1 + k` (`k : Fin n`) equals
`P₂`'s state at round `k + 1`. -/
theorem append_PrvState_natAdd_succ (k : Fin n) :
    (P₁.append P₂).PrvState (Fin.natAdd (m + 1) k |>.cast (by omega)) = P₂.PrvState k.succ := by
  unfold Prover.append
  dsimp only [Function.comp_apply]
  rw [show (Fin.cast (by omega) (Fin.natAdd (m + 1) k |>.cast (by omega)) : Fin (m + 1 + n))
        = Fin.natAdd (m + 1) k from by ext; simp]
  rw [Fin.append_right]
  rfl

end Prover

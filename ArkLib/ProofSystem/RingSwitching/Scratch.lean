import ArkLib.ProofSystem.RingSwitching.Prelude
import ArkLib.ProofSystem.Sumcheck.Structured.SingleRound

open MvPolynomial Finset Sumcheck.Structured RingSwitching

namespace ScratchRS

set_option linter.style.longFile 0
set_option linter.unusedVariables false

variable {L : Type} [CommRing L] [Nontrivial L] [DecidableEq L]

-- (a) The witness-projection / structural-invariant compatibility.
-- projectToMidSumcheckPoly at i.castSucc, then fix the next variable to r', equals
-- projectToMidSumcheckPoly at i.succ with snoc challenges r'.
-- Note the type mismatch: LHS lives in ℓ - i.castSucc - 1, RHS in ℓ - i.succ.

-- Eval-level composition for fixFirstVariablesOfMQP: fix last `v` then last `1` more = fix last `v+1`.
-- Stated generically. The index arithmetic: (ℓ - v) - 1 vs ℓ - (v+1).
example (ℓ : ℕ) (poly : MvPolynomial (Fin ℓ) L) (v : Fin (ℓ + 1)) (hv : (v : ℕ) < ℓ)
    (challenges : Fin v → L) (r' : L) (x : Fin (ℓ - v - 1) → L) :
    eval x (fixFirstVariablesOfMQP (ℓ - v) ⟨1, by omega⟩
        (fixFirstVariablesOfMQP ℓ v poly challenges) (fun _ => r'))
      = eval (fun i : Fin (ℓ - (v+1)) => x (Fin.cast (by omega) i))
          (fixFirstVariablesOfMQP ℓ ⟨v+1, by omega⟩ poly (Fin.snoc challenges r')) := by
  rw [fixFirstVariablesOfMQP_eval (ℓ := ℓ - v) (v := ⟨1, by omega⟩)
    (poly := fixFirstVariablesOfMQP ℓ v poly challenges) (challenges := fun _ => r') (x := x)]
  trivial

end ScratchRS

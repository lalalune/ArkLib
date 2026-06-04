import ArkLib.ProofSystem.RingSwitching.Prelude
import ArkLib.ProofSystem.RingSwitching.Spec
import ArkLib.ProofSystem.Sumcheck.Structured.SingleRound

open OracleSpec OracleComp ProtocolSpec Finset Polynomial MvPolynomial
  Module TensorProduct Nat Matrix
open scoped NNReal
open Sumcheck.Structured

namespace RingSwitching.ScratchRSW
noncomputable section

variable (κ : ℕ) [NeZero κ]
variable (L : Type) [CommRing L] [Nontrivial L] [Fintype L] [DecidableEq L]
  [SampleableType L]
variable (K : Type) [CommRing K] [Fintype K] [DecidableEq K]
variable [Algebra K L]
variable (P : RingSwitchingProfile K L κ)
variable (ℓ ℓ' : ℕ) [NeZero ℓ] [NeZero ℓ']
variable (h_l : ℓ = ℓ' + κ)
variable (aOStmtIn : AbstractOStmtIn L ℓ')

-- Generic: `rename` along a `finCongr` whose endpoints are *propositionally* equal collapses to
-- identity. Proven by `Eq.rec` on the index equality (no syntactic `finCongr_refl` matching needed).
theorem rename_finCongr_self {a b : ℕ} (h : a = b) (p : MvPolynomial (Fin a) L) :
    rename (finCongr h) p = h ▸ p := by
  subst h
  show rename (finCongr (rfl : a = a)) p = p
  rw [show finCongr (rfl : a = a) = Equiv.refl (Fin a) from rfl, Equiv.coe_refl, rename_id]
  rfl

-- WITNESS-INVARIANT ADVANCE. Goal: from witIn.H = projectToMid t' m i.castSucc challenges,
-- show the honest advance witOut.H = fixFirstVariablesOfMQP (ℓ'-i) ⟨1⟩ witIn.H {r'}
-- equals projectToMid t' m i.succ (Fin.cons r' challenges) (as L⦃≤2⦄[X Fin (ℓ'-i.succ)]).
example (i : Fin ℓ')
    (t' m : MultilinearPoly L ℓ')
    (challenges : Fin i.castSucc → L) (r' : L) :
    (fixFirstVariablesOfMQP (ℓ := ℓ' - i) (v := ⟨1, by have := i.isLt; omega⟩)
      (H := (projectToMidSumcheckPoly (L := L) (ℓ := ℓ') (t := t') (m := m)
        (i := i.castSucc) (challenges := challenges)).val) (challenges := fun _ => r'))
      = (projectToMidSumcheckPoly (L := L) (ℓ := ℓ') (t := t') (m := m)
        (i := i.succ) (challenges := Fin.cons r' challenges)).val := by
  have hstep := RingSwitching.fixFirstVariablesOfMQP_projectToMid_step (L := L) ℓ' t' m i
    challenges r'
  rw [rename_finCongr_self] at hstep
  exact hstep

end
end RingSwitching.ScratchRSW

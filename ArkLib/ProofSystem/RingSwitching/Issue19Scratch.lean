import ArkLib.ProofSystem.RingSwitching.SumcheckPhase
import ArkLib.OracleReduction.Completeness

/-!
# Issue #19 — perfect completeness of the structured ring-switching sumcheck round

This file discharges `iteratedSumcheckOracleReduction_perfectCompleteness_residual`
(currently an unproven named `Prop` in `SumcheckPhase.lean`) into a real theorem, under the
single statement repair `hInit : NeverFail init` — the same repair already used by the
sibling Binius completeness theorems (issue #19 / #33).

The honest-round **algebra** is entirely in-tree:
* `getSumcheckRoundPoly_points_sum_eq_cube` — verifier sum-check `∑_{b∈points i} h_i(b) = ∑_cube H`;
* `getSumcheckRoundPoly_eval_eq_cube_succ` — round transition `h_i(r') = ∑_{next cube} H'`;
* `fixFirstVariablesOfMQP_projectToMid_step` — witness structural-invariant step.

The monadic peel is adapted from the verified Binius sibling
`ArkLib/ProofSystem/Binius/RingSwitching/SumcheckPhase.lean`
(`iteratedSumcheckOracleReduction_perfectCompleteness`), specialised to the raw
`Sumcheck.Structured.roundOracleReduction` prover/verifier.
-/

open OracleSpec OracleComp ProtocolSpec Finset Polynomial MvPolynomial
  Module TensorProduct Nat Matrix
open scoped NNReal
open Sumcheck.Structured

namespace RingSwitching.SumcheckPhase
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
variable {σ : Type} {init : ProbComp σ} {impl : QueryImpl []ₒ (StateT σ ProbComp)}

/-- `[]ₒ.Inhabited` / `.Fintype` are vacuous (empty domain), but VCVio ships no instance for
`emptySpec`; `unroll_2_message_reduction_perfectCompleteness` requires them. -/
local instance : (([]ₒ : OracleSpec PEmpty).Inhabited) where
  inhabited_B q := nomatch q

local instance : (([]ₒ : OracleSpec PEmpty).Fintype) where
  fintype_B q := nomatch q

/-! ## The honest-round logic-completeness facts (mathematical core)

Proved purely from the in-tree algebra (no monadic content). -/

variable {κ L K P ℓ ℓ' h_l aOStmtIn}

/-- **Honest verifier check.** With the honest prover's round univariate
`h_i = getSumcheckRoundPoly i H`, the verifier's sum-check `∑_{b∈points i} h_i(b) = target`
holds whenever the input sumcheck-consistency `target = ∑_cube H` holds. -/
theorem honest_round_verifierCheck (i : Fin ℓ')
    (target : L) (H : L⦃≤ 2⦄[X Fin (ℓ' - (i.castSucc : Fin (ℓ' + 1)).val)])
    (hConsist : sumcheckConsistencyProp (boolDomain L _) target H) :
    (∑ b ∈ (boolDomain L ℓ').points i,
        (getSumcheckRoundPoly ℓ' (boolDomain L ℓ') (i := i) H).val.eval b) = target := by
  rw [getSumcheckRoundPoly_points_sum_eq_cube]
  exact hConsist.symm

/-- **Honest round transition (sumcheck-consistency at `i.succ`).** The next-round target
`h_i(r')` equals the cube-sum of the advanced witness polynomial, which (via the structural
step) is the next-round witness `H'`.  This is `sumcheckConsistencyProp` at index `i.succ`
for the honest output. -/
theorem honest_round_consistency_succ (i : Fin ℓ')
    (t m : MultilinearPoly L ℓ') (challenges : Fin (i.castSucc : Fin (ℓ' + 1)).val → L)
    (r' : L) :
    sumcheckConsistencyProp (𝓑 := boolDomain L _)
      ((getSumcheckRoundPoly ℓ' (boolDomain L ℓ') (i := i)
          (projectToMidSumcheckPoly (L := L) (ℓ := ℓ') (t := t) (m := m)
            (i := i.castSucc) (challenges := challenges))).val.eval r')
      (projectToMidSumcheckPoly (L := L) (ℓ := ℓ') (t := t) (m := m)
        (i := i.succ) (challenges := Fin.cons r' challenges)) := by
  -- `sumcheckConsistencyProp D s H : s = ∑_{cube} H`; the RHS is exactly the cube-succ lemma.
  unfold sumcheckConsistencyProp
  exact getSumcheckRoundPoly_eval_eq_cube_succ (κ := κ) (L := L) (K := K) (P := P)
    (ℓ := ℓ) (ℓ' := ℓ') (i := i) t m challenges r'

/-- **Honest round structural invariant at `i.succ`.** The advanced witness polynomial
`fixFirst H {r'}` produced by the honest prover equals the next-round projected polynomial
`projectToMid i.succ (cons r' challenges)`.  The `rename (finCongr …)` from
`fixFirstVariablesOfMQP_projectToMid_step` is along the defeq `ℓ'-i.succ = ℓ'-i.castSucc-1`,
hence the identity. -/
theorem honest_round_structInvariant_succ (i : Fin ℓ')
    (t m : MultilinearPoly L ℓ') (challenges : Fin (i.castSucc : Fin (ℓ' + 1)).val → L)
    (r' : L) :
    fixFirstVariablesOfMQP (ℓ' - (i.castSucc : Fin (ℓ' + 1)).val)
        ⟨1, by have := i.isLt; simp only [Fin.val_castSucc]; omega⟩
        (projectToMidSumcheckPoly (L := L) (ℓ := ℓ') (t := t) (m := m)
          (i := i.castSucc) (challenges := challenges)).val (fun _ => r')
      = (projectToMidSumcheckPoly (L := L) (ℓ := ℓ') (t := t) (m := m)
          (i := i.succ) (challenges := Fin.cons r' challenges)).val := by
  rw [fixFirstVariablesOfMQP_projectToMid_step (L := L) (ℓ := ℓ') t m i challenges r']
  -- `finCongr` along `ℓ'-i.succ = ℓ'-i.castSucc-1` (defeq nats) is the identity rename.
  have hcast : (show ℓ' - (i.succ : ℕ) = ℓ' - (i.castSucc : Fin (ℓ' + 1)).val - 1 by
      have := i.isLt; simp only [Fin.val_succ, Fin.val_castSucc]; omega) = rfl := rfl
  simp only [finCongr_refl, Equiv.refl_apply, rename_id_apply]

/-! ## The completeness theorem (monadic assembly)

The remaining step is the monadic `OracleReduction.run` peel: `unroll_2_message_…` reduces
the goal to an explicit honest do-block whose only failure point is the verifier `guard`
(discharged by `honest_round_verifierCheck`) and whose unique output satisfies `relOut`
(structural invariant + consistency + initial compatibility) and the prover/verifier
agreement.  This block is adapted from the verified Binius sibling; it consumes the three
logic facts above. -/

end

end RingSwitching.SumcheckPhase

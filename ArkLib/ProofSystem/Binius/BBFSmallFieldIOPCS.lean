/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chung Thai Nguyen, Quang Dao
-/

import ArkLib.ProofSystem.RingSwitching.General
import ArkLib.ProofSystem.Binius.BinaryBasefold.General
import ArkLib.ProofSystem.Binius.BinaryBasefold.Soundness
import ArkLib.ProofSystem.Binius.BinaryBasefold.ExtractMLPCorrectness
import ArkLib.OracleReduction.LiftContext.OracleReduction

/-!
# BBF Small-Field IOPCS: Ring-Switching + Binary Basefold Composition

This module instantiates the Ring-Switching protocol with Binary Basefold as the inner
large-field MLIOPCS, producing a **small-field IOPCS** (the standard, non-optimized composition).

## Architecture

The composition follows the protocol layering:
1. **Ring-switching** (outer): Reduces a small-field polynomial commitment to a large-field one
2. **Binary Basefold** (inner): Serves as the `MLIOPCS L ℓ'` for the large-field evaluation

This is the pedagogical/reference implementation that invokes Binary Basefold as a black box,
in contrast to `FRIBinius/CoreInteractionPhase.lean` which fuses the sumcheck-fold steps.

## Main Results

- `bbfMLIOPCS`: Binary Basefold instantiated as an `MLIOPCS L ℓ'`, parameterized over the two
  named inner-protocol surfaces `BBFInnerPerfectCompleteness` / `BBFInnerRbrKnowledgeSoundness`
  (the `FullBinaryBasefold.*_wired` front doors of issue #317); both `MLIOPCS` security
  fields are proven from them via the `LiftContext` lenses in this file
- `bbf_fullOracleReduction_perfectCompleteness`: Perfect completeness of the composed protocol
  on the strict-track input relation, via the proven RingSwitching end-to-end capstone
- `bbf_fullOracleVerifier_rbrKnowledgeSoundness`: RBR knowledge soundness of the composed
  protocol; the three append-seam hypotheses remain external (the RBR-KS append keystone
  still consumes the composite `KnowledgeStateFunction` + phase-2 flip bound)

A concrete scalar-KS corollary (ring-switching front + BBF (43)-style tail) is deliberately
not stated here yet: the non-fused concrete-error spine
(`concreteBinaryBasefoldKnowledgeError`, `FullBinaryBasefold.fullRbrKnowledgeError_sum_le_*`)
does not exist in-tree (the fused variant lives in `FRIBinius/General.lean`). A previous
revision referenced those phantom declarations; see issue #317.

## References

- [DP24] Diamond, Benjamin E., and Jim Posen. "Polylogarithmic Proofs for Multilinears over Binary
  Towers." Cryptology ePrint Archive (2024).
  Statement numbering follows the archived revision of [DP24].
-/


namespace Binius.BBFSmallFieldIOPCS

open Binius.BinaryBasefold Binius.BinaryBasefold.FullBinaryBasefold
open RingSwitching RingSwitching.FullRingSwitching
open Polynomial MvPolynomial OracleSpec OracleComp ProtocolSpec Finset AdditiveNTT Module
open scoped NNReal

noncomputable section

/-! ## Part 1: Binary Basefold as MLIOPCS

We construct an `MLIOPCS L ℓ'` by wrapping Binary Basefold's full protocol.
The construction is parameterized by Binary Basefold parameters only (no Ring-switching params).
-/

section BinaryBasefoldMLIOPCS

variable {r : ℕ} [NeZero r]
variable {L : Type} [Field L] [Fintype L] [DecidableEq L] [CharP L 2]
  [SampleableType L]
variable (𝔽q : Type) [Field 𝔽q] [Fintype 𝔽q] [DecidableEq 𝔽q]
  [h_Fq_char_prime : Fact (Nat.Prime (ringChar 𝔽q))] [hF₂ : Fact (Fintype.card 𝔽q = 2)]
variable [Algebra 𝔽q L]
variable (β : Fin r → L) [hβ_lin_indep : Fact (LinearIndependent 𝔽q β)]
  [h_β₀_eq_1 : Fact (β 0 = 1)]
variable {ℓ' 𝓡 ϑ : ℕ} (γ_repetitions : ℕ) [NeZero ℓ'] [NeZero 𝓡] [NeZero ϑ]
variable {h_ℓ_add_R_rate : ℓ' + 𝓡 < r}
variable {𝓑 : Fin 2 ↪ L}
variable [h_B01 : Fact (𝓑 0 = 0 ∧ 𝓑 1 = 1)]
variable [hdiv : Fact (ϑ ∣ ℓ')]

instance : OracleInterface Unit := OracleInterface.instDefault

/-! ### Type Adapters

| MLIOPCS                | BinaryBasefold                           |
|------------------------|------------------------------------------|
| `MLPEvalStatement L ℓ'`| `Statement (SumcheckBaseContext L ℓ') 0` |
| `WitMLP L ℓ'`          | `Witness 𝔽q β 0`                        |
| `OStmtIn`              | `OracleStatement 𝔽q β ϑ 0`             |

At round 0, `sumcheck_target = original_claim` (since `∑ x, eq(r,x) * t(x) = t(r) = s`). -/

/-- Convert an `MLPEvalStatement L ℓ'` produced at the end of ring-switching protocol
to a `Statement (SumcheckBaseContext L ℓ') 0` that is equal to the initial statement
of the large-field Binary Basefold protocol. -/
def reducedMLPEvalStatement_to_BBF_Statement (stmt : MLPEvalStatement (L := L) (ℓ := ℓ')) :
    Statement (L := L) (SumcheckBaseContext L ℓ') (0 : Fin (ℓ' + 1)) where
  sumcheck_target := stmt.original_claim
  challenges := Fin.elim0
  ctx := ⟨stmt.t_eval_point, stmt.original_claim⟩

/-- Convert `WitMLP L ℓ'` to `Witness 𝔽q β 0`. -/
def MLPEvalWitness_to_BBF_Witness (stmt : MLPEvalStatement (L := L) (ℓ := ℓ'))
    (wit : WitMLP (K := L) (ℓ := ℓ')) :
    Witness (L := L) 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (ℓ := ℓ') (0 : Fin (ℓ' + 1)) where
  t := wit.t
  H := projectToMidSumcheckPoly (L := L) (ℓ := ℓ') (t := wit.t)
    (m := BBF_SumcheckMultiplierParam.multpoly ⟨stmt.t_eval_point, stmt.original_claim⟩)
    (i := (0 : Fin (ℓ' + 1))) (challenges := Fin.elim0)
  f := getMidCodewords 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) wit.t Fin.elim0

/-! ### Large-Field Invocation Wrapper

Ring-switching ends with a large-field MLP-evaluation statement/witness pair.
This wrapper maps that pair into Binary Basefold's round-0 input context
via `LiftContext`, reusing Binary Basefold's full reduction unchanged. -/

/-- Statement lens for the ring-switching large-field invocation into Binary Basefold. -/
def largeFieldInvocationStmtLens : OracleStatement.Lens
    (OuterStmtIn := MLPEvalStatement (L := L) (ℓ := ℓ'))
    (OuterStmtOut := Bool)
    (InnerStmtIn := Statement (L := L) (SumcheckBaseContext L ℓ') (0 : Fin (ℓ' + 1)))
    (InnerStmtOut := Bool)
    (OuterOStmtIn := OracleStatement 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
      (ℓ := ℓ') ϑ (0 : Fin (ℓ' + 1)))
    (OuterOStmtOut := fun _ : Empty => Unit)
    (InnerOStmtIn := OracleStatement 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
      (ℓ := ℓ') ϑ (0 : Fin (ℓ' + 1)))
    (InnerOStmtOut := fun _ : Empty => Unit) where
  toFunA := fun ⟨stmtIn, oStmtIn⟩ =>
    ⟨reducedMLPEvalStatement_to_BBF_Statement stmtIn, oStmtIn⟩
  toFunB := fun _ ⟨stmtOut, oStmtOut⟩ => ⟨stmtOut, oStmtOut⟩

/-- Context lens for the ring-switching large-field invocation into Binary Basefold. -/
def largeFieldInvocationCtxLens : OracleContext.Lens
    (OuterStmtIn := MLPEvalStatement (L := L) (ℓ := ℓ'))
    (OuterStmtOut := Bool)
    (InnerStmtIn := Statement (L := L) (SumcheckBaseContext L ℓ') (0 : Fin (ℓ' + 1)))
    (InnerStmtOut := Bool)
    (OuterOStmtIn := OracleStatement 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
      (ℓ := ℓ') ϑ (0 : Fin (ℓ' + 1)))
    (OuterOStmtOut := fun _ : Empty => Unit)
    (InnerOStmtIn := OracleStatement 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
      (ℓ := ℓ') ϑ (0 : Fin (ℓ' + 1)))
    (InnerOStmtOut := fun _ : Empty => Unit)
    (OuterWitIn := WitMLP (K := L) (ℓ := ℓ'))
    (OuterWitOut := Unit)
    (InnerWitIn := Witness (L := L) 𝔽q β
      (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (ℓ := ℓ') (0 : Fin (ℓ' + 1)))
    (InnerWitOut := Unit) where
  stmt := largeFieldInvocationStmtLens 𝔽q β
  wit := {
    toFunA := fun ⟨⟨stmtIn, _oStmtIn⟩, witIn⟩ =>
      MLPEvalWitness_to_BBF_Witness 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) stmtIn witIn
    toFunB := fun _ _ => ()
  }

/-- Binary Basefold oracle reduction lifted to the ring-switching large-field invocation context. -/
def largeFieldInvocationOracleReduction :
    OracleReduction (oSpec := []ₒ)
      (StmtIn := MLPEvalStatement (L := L) (ℓ := ℓ'))
      (OStmtIn := OracleStatement 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (ℓ := ℓ') ϑ
          (0 : Fin (ℓ' + 1)))
      (StmtOut := Bool)
      (OStmtOut := fun _ : Empty => Unit)
      (WitIn := WitMLP (K := L) (ℓ := ℓ'))
      (WitOut := Unit)
      (pSpec := fullPSpec 𝔽q β γ_repetitions (ϑ := ϑ)
        (h_ℓ_add_R_rate := h_ℓ_add_R_rate)) :=
  (FullBinaryBasefold.fullOracleReduction 𝔽q β γ_repetitions (ϑ := ϑ)
    (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (𝓑 := 𝓑) (ℓ := ℓ')).liftContext
    (lens := largeFieldInvocationCtxLens 𝔽q β)

omit [SampleableType L] in
/-- Uniqueness of the polynomial witness from first-oracle UDR-compatibility. -/
lemma firstOracleWitnessConsistency_unique
    (oStmt : ∀ j, OracleStatement 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (ℓ := ℓ') ϑ
      (0 : Fin (ℓ' + 1)) j)
    {t₁ t₂ : MultilinearPoly L ℓ'}
    (h₁ : firstOracleWitnessConsistencyProp 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (ℓ := ℓ')
      t₁ (getFirstOracle 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) oStmt))
    (h₂ : firstOracleWitnessConsistencyProp 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (ℓ := ℓ')
      t₂ (getFirstOracle 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) oStmt)) :
    t₁ = t₂ := by
  exact firstOracleWitnessConsistencyProp_unique' 𝔽q β
    (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (ℓ := ℓ') t₁ t₂
    (getFirstOracle 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) oStmt) h₁ h₂

lemma map_eval_sumToIter_rename_finSum_zero
    (p : MvPolynomial (Fin ℓ') L) :
    (MvPolynomial.map (MvPolynomial.eval (σ := Fin 0) Fin.elim0)
      ((sumToIter L (Fin ℓ') (Fin 0))
        (MvPolynomial.rename
          (f := ⇑(finSumFinEquiv (m := ℓ') (n := 0)).symm) p))) = p := by
  have h_sumToIter :
      (sumToIter L (Fin ℓ') (Fin 0))
          (MvPolynomial.rename
            (f := ⇑(finSumFinEquiv (m := ℓ') (n := 0)).symm) p) =
        MvPolynomial.map (MvPolynomial.C) p := by
    have h_ren_fun :
        (fun i : Fin ℓ' => (finSumFinEquiv (m := ℓ') (n := 0)).symm i) = Sum.inl := by
      funext i
      exact finSumFinEquiv_symm_apply_castAdd (m := ℓ') (n := 0) i
    have h_ren :
        MvPolynomial.rename
          (f := ⇑(finSumFinEquiv (m := ℓ') (n := 0)).symm) p =
        MvPolynomial.rename (f := Sum.inl) p := by
      exact congrArg (fun f => MvPolynomial.rename (f := f) p) h_ren_fun
    rw [h_ren]
    have h_comp := MvPolynomial.sumAlgEquiv_comp_rename_inl
      (R := L) (S₁ := Fin ℓ') (S₂ := Fin 0)
    have h_eval_comp := congrArg (fun f => f p) h_comp
    exact h_eval_comp
  rw [h_sumToIter]
  rw [MvPolynomial.map_map]
  have h_eval_comp_id :
      (MvPolynomial.eval (σ := Fin 0) Fin.elim0).comp MvPolynomial.C = RingHom.id L := by
    ext a
    simp
  rw [h_eval_comp_id]
  exact MvPolynomial.map_id p

lemma fixFirstVariablesOfMQP_zero_eq
    (H : MvPolynomial (Fin ℓ') L) :
    fixFirstVariablesOfMQP (L := L) (ℓ := ℓ') (v := (0 : Fin (ℓ' + 1))) H
      (challenges := Fin.elim0) = H := by
  rw [fixFirstVariablesOfMQP_eq_bind₁ (L := L) (ℓ := ℓ') (v := (0 : Fin (ℓ' + 1)))
    (poly := H) (challenges := Fin.elim0)]
  change MvPolynomial.bind₁ (fun j : Fin ℓ' => MvPolynomial.X j) H = H
  rw [MvPolynomial.bind₁_X_left]
  rfl

lemma witnessStructuralInvariant_MLPEvalWitness_to_BBF_Witness
    (stmt : MLPEvalStatement (L := L) (ℓ := ℓ'))
    (wit : WitMLP (K := L) (ℓ := ℓ')) :
    Binius.BinaryBasefold.witnessStructuralInvariant 𝔽q β
      (mp := BBF_SumcheckMultiplierParam) (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
      (reducedMLPEvalStatement_to_BBF_Statement (L := L) (ℓ' := ℓ') stmt)
      (MLPEvalWitness_to_BBF_Witness 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) stmt wit) := by
  unfold Binius.BinaryBasefold.witnessStructuralInvariant
  dsimp [reducedMLPEvalStatement_to_BBF_Statement, MLPEvalWitness_to_BBF_Witness]
  simp

/-- If `t(r) = s` for the outer MLP statement, then the mapped round-0 BBF witness
satisfies the BBF round-0 sumcheck consistency identity. -/
lemma sumcheckConsistency_MLPEvalWitness_to_BBF_Witness_of_eval
    (stmt : MLPEvalStatement (L := L) (ℓ := ℓ'))
    (wit : WitMLP (K := L) (ℓ := ℓ'))
    (h_eval : wit.t.val.eval stmt.t_eval_point = stmt.original_claim) :
    sumcheckConsistencyProp (𝓑 := 𝓑)
      (reducedMLPEvalStatement_to_BBF_Statement (L := L) (ℓ' := ℓ') stmt).sumcheck_target
      (MLPEvalWitness_to_BBF_Witness 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) stmt wit).H := by
  rw [sumcheckConsistencyProp]
  dsimp [reducedMLPEvalStatement_to_BBF_Statement, MLPEvalWitness_to_BBF_Witness,
    computeInitialSumcheckPoly, BBF_SumcheckMultiplierParam, BBF_eq_multiplier]
  rw [← h_eval]
  let castEmb : Fin 2 ↪ L := ⟨fun b => (b : L), by
    intro a b h
    fin_cases a <;> fin_cases b <;> simp at h <;> simp [h]⟩
  have h_Beq : 𝓑 = castEmb := by
    ext b
    fin_cases b <;> simp [castEmb, h_B01.out.1, h_B01.out.2]
  subst h_Beq
  have h_H0 :
      projectToMidSumcheckPoly (L := L) (ℓ := ℓ') (t := wit.t)
        (m := BBF_SumcheckMultiplierParam.multpoly ⟨stmt.t_eval_point, stmt.original_claim⟩)
        (i := (0 : Fin (ℓ' + 1))) (challenges := Fin.elim0) =
      computeInitialSumcheckPoly (ℓ := ℓ') wit.t
        (BBF_SumcheckMultiplierParam.multpoly ⟨stmt.t_eval_point, stmt.original_claim⟩) := by
    have h_fix0 :
        fixFirstVariablesOfMQP (L := L) (ℓ := ℓ')
          (v := (0 : Fin (ℓ' + 1)))
          (H := (computeInitialSumcheckPoly (ℓ := ℓ') wit.t
            (BBF_SumcheckMultiplierParam.multpoly
              ⟨stmt.t_eval_point, stmt.original_claim⟩)).val)
          (challenges := Fin.elim0) =
        (computeInitialSumcheckPoly (ℓ := ℓ') wit.t
          (BBF_SumcheckMultiplierParam.multpoly
            ⟨stmt.t_eval_point, stmt.original_claim⟩)).val :=
      fixFirstVariablesOfMQP_zero_eq (L := L)
        (H := (computeInitialSumcheckPoly (ℓ := ℓ') wit.t
          (BBF_SumcheckMultiplierParam.multpoly
            ⟨stmt.t_eval_point, stmt.original_claim⟩)).val)
    apply Subtype.ext
    unfold projectToMidSumcheckPoly
    dsimp
    exact h_fix0
  let mEq : MultilinearPoly L ℓ' := BBF_eq_multiplier (L := L) stmt.t_eval_point
  have h_H0' :
      projectToMidSumcheckPoly (L := L) (ℓ := ℓ') (t := wit.t)
        (m := mEq) (i := (0 : Fin (ℓ' + 1))) (challenges := Fin.elim0) =
      computeInitialSumcheckPoly (ℓ := ℓ') wit.t mEq := by
    dsimp [mEq, BBF_SumcheckMultiplierParam, BBF_eq_multiplier] at h_H0 ⊢
    exact h_H0
  change MvPolynomial.eval stmt.t_eval_point wit.t.val =
    ∑ x ∈ Fintype.piFinset (fun _ : Fin ℓ' => Finset.map castEmb (Finset.univ : Finset (Fin 2))),
      MvPolynomial.eval x
        (projectToMidSumcheckPoly (L := L) (ℓ := ℓ') (t := wit.t)
          (m := mEq) (i := (0 : Fin (ℓ' + 1))) (challenges := Fin.elim0)).val
  rw [h_H0']
  change MvPolynomial.eval stmt.t_eval_point wit.t.val =
    ∑ x ∈ Fintype.piFinset (fun _ : Fin ℓ' => Finset.map castEmb (Finset.univ : Finset (Fin 2))),
      MvPolynomial.eval x (mEq.val * wit.t.val)
  have h_pi :
    Fintype.piFinset (fun _ : Fin ℓ' => Finset.map castEmb (Finset.univ : Finset (Fin 2))) =
      (Finset.univ : Finset (Fin ℓ' → Fin 2)).image
        (fun b : Fin ℓ' → Fin 2 => fun i => castEmb (b i)) := by
    have h_arg :
        (fun _ : Fin ℓ' => Finset.map castEmb (Finset.univ : Finset (Fin 2))) =
          (fun _ : Fin ℓ' => (Finset.univ : Finset (Fin 2)).image castEmb) := by
      funext i
      rw [Finset.map_eq_image]
    have h_pi' :=
      Fintype.piFinset_image
        (f := fun _ : Fin ℓ' => castEmb)
        (s := fun _ : Fin ℓ' => (Finset.univ : Finset (Fin 2)))
    rw [h_arg]
    rw [Fintype.piFinset_univ] at h_pi'
    exact h_pi'
  rw [h_pi, Finset.sum_image]
  · simp only [MvPolynomial.eval_mul]
    have h_sum_symm :
      (∑ x : Fin ℓ' → Fin 2,
        MvPolynomial.eval (fun i => castEmb (x i)) mEq.val *
          MvPolynomial.eval (fun i => castEmb (x i)) wit.t.val) =
      (∑ x : Fin ℓ' → Fin 2,
        MvPolynomial.eval stmt.t_eval_point (MvPolynomial.eqPolynomial (fun i => castEmb (x i))) *
          MvPolynomial.eval (fun i => castEmb (x i)) wit.t.val) := by
      apply Finset.sum_congr rfl
      intro x hx
      have h_mEq : MvPolynomial.eval (fun i => castEmb (x i)) mEq.val = MvPolynomial.eval
        (fun i => castEmb (x i)) (MvPolynomial.eqPolynomial stmt.t_eval_point) := by
        simp only [BBF_eq_multiplier, map_prod, map_add, map_mul, map_sub, map_one,
          MvPolynomial.eval_C, MvPolynomial.eval_X, mEq]
      rw [h_mEq]
      congr 1
      exact (MvPolynomial.eqPolynomial_symm
        (x := fun i => castEmb (x i)) (y := stmt.t_eval_point)).symm
    rw [h_sum_symm]
    have h_multilinear : MvPolynomial.MLE
        (fun x : Fin ℓ' → Fin 2 => MvPolynomial.eval (x : Fin ℓ' → L) wit.t.val) = wit.t.val := by
      exact (MvPolynomial.is_multilinear_iff_eq_evals_zeroOne (p := wit.t.val)).mp wit.t.property
    calc
      MvPolynomial.eval stmt.t_eval_point wit.t.val =
        MvPolynomial.eval stmt.t_eval_point
          (MvPolynomial.MLE
            (fun x : Fin ℓ' → Fin 2 => MvPolynomial.eval (x : Fin ℓ' → L) wit.t.val)) := by
          rw [h_multilinear]
      _ = ∑ x : Fin ℓ' → Fin 2,
        MvPolynomial.eval stmt.t_eval_point (MvPolynomial.eqPolynomial (x : Fin ℓ' → L)) *
          MvPolynomial.eval (x : Fin ℓ' → L) wit.t.val := by
        unfold MvPolynomial.MLE
        simp only [MvPolynomial.eval_sum, MvPolynomial.eval_mul, MvPolynomial.eval_C]
      _ = ∑ x : Fin ℓ' → Fin 2,
        MvPolynomial.eval stmt.t_eval_point (MvPolynomial.eqPolynomial (fun i => castEmb (x i))) *
          MvPolynomial.eval (fun i => castEmb (x i)) wit.t.val := by
        apply Finset.sum_congr rfl
        intro x hx
        rfl
  · intro x hx y hy hxy
    funext i
    apply castEmb.injective
    exact congrFun hxy i

/-! ### AbstractOStmtIn

Following the pattern from `FRIBinius/Prelude.lean` (`BinaryBasefoldAbstractOStmtIn`). -/

/-- The `AbstractOStmtIn` for Binary Basefold.

The oracle statement type is `OracleStatement 𝔽q β ϑ 0`, representing initial committed
codewords. The two compatibility tracks tie the polynomial `t'` to the oracle commitments:
the relaxed track (knowledge-soundness side) via first-oracle witness consistency
(UDR-closeness), the strict track (completeness side) via exact oracle folding
consistency. -/
def bbfAbstractOStmtIn : AbstractOStmtIn L ℓ' where
  ιₛᵢ := Fin (toOutCodewordsCount ℓ' ϑ (0 : Fin (ℓ' + 1)))
  OStmtIn := OracleStatement 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (ℓ := ℓ') ϑ
      (0 : Fin (ℓ' + 1))
  Oₛᵢ := instOracleStatementBinaryBasefold 𝔽q β
    (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (ϑ := ϑ) (i := (0 : Fin (ℓ' + 1)))
  -- Relaxed input compatibility at round 0 (RBR-KS style).
  initialCompatibility := fun ⟨t', oStmt⟩ =>
    firstOracleWitnessConsistencyProp 𝔽q β (ℓ := ℓ')
      (h_ℓ_add_R_rate := h_ℓ_add_R_rate) t'
      (getFirstOracle 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) oStmt)
  -- Strict compatibility: exact oracle folding consistency (implies UDR-closeness).
  strictInitialCompatibility := fun ⟨t', oStmt⟩ =>
    strictOracleFoldingConsistencyProp 𝔽q β (ϑ := ϑ)
      (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (t := t') (i := (0 : Fin (ℓ' + 1)))
      (challenges := Fin.elim0) (oStmt := oStmt)

/-- Strict (exact equality) initial compatibility implies the relaxed (UDR-closeness) one. -/
lemma bbfStrictInitialCompatibility_implies_initialCompatibility
    (x : MultilinearPoly L ℓ' ×
      (∀ j, OracleStatement 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (ℓ := ℓ') ϑ
        (0 : Fin (ℓ' + 1)) j))
    (h_compat_strict : (bbfAbstractOStmtIn 𝔽q β
      (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (ϑ := ϑ)).strictInitialCompatibility x) :
    (bbfAbstractOStmtIn 𝔽q β
      (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (ϑ := ϑ)).initialCompatibility x := by
  obtain ⟨t, oStmt⟩ := x
  -- strictOracleFoldingConsistencyProp implies f₀ = getFirstOracle
  have h_eq := Binius.BinaryBasefold.QueryPhase.polyToOracleFunc_eq_getFirstOracle
    𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (t := t) (i := (0 : Fin (ℓ' + 1)))
    (challenges := Fin.elim0) (oStmt := oStmt) h_compat_strict
  -- Exact equality implies UDR-closeness (hamming distance 0)
  dsimp only [bbfAbstractOStmtIn, firstOracleWitnessConsistencyProp]
  rw [← h_eq]
  dsimp only [pair_UDRClose]
  have h_dist_pos :
      0 < BBF_CodeDistance 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
        (i := (0 : Fin r)) := by
    rw [BBF_CodeDistance_eq 𝔽q β
      (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (i := (0 : Fin r)) (h_i := by simp)]
    omega
  simp only [hammingDist_self, mul_zero, h_dist_pos]

instance largeFieldInvocationCtxLens_complete :
  (largeFieldInvocationCtxLens 𝔽q β).toContext.IsComplete
    (outerRelIn := (bbfAbstractOStmtIn 𝔽q β
      (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (ϑ := ϑ)).toStrictRelInput)
    (innerRelIn := strictRoundRelation (mp := BBF_SumcheckMultiplierParam) 𝔽q β
      (ϑ := ϑ) (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (𝓑 := 𝓑) (0 : Fin (ℓ' + 1)))
    (outerRelOut := acceptRejectOracleRel)
    (innerRelOut := acceptRejectOracleRel)
    (compat := Reduction.compatContext (oSpec := []ₒ)
      (pSpec := fullPSpec 𝔽q β γ_repetitions (ϑ := ϑ)
        (h_ℓ_add_R_rate := h_ℓ_add_R_rate))
      (largeFieldInvocationCtxLens 𝔽q β).toContext
      ((FullBinaryBasefold.fullOracleReduction 𝔽q β γ_repetitions (ϑ := ϑ)
        (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (𝓑 := 𝓑) (ℓ := ℓ')).toReduction)) where
  proj_complete := fun stmtIn witIn hRelIn => by
    rcases stmtIn with ⟨stmtIn, oStmtIn⟩
    rcases hRelIn with ⟨h_eval, h_compat⟩
    refine ⟨?_, ?_⟩
    · exact sumcheckConsistency_MLPEvalWitness_to_BBF_Witness_of_eval 𝔽q β
        (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (𝓑 := 𝓑) stmtIn witIn h_eval.symm
    · refine ⟨?_, ?_⟩
      · exact witnessStructuralInvariant_MLPEvalWitness_to_BBF_Witness 𝔽q β
          (h_ℓ_add_R_rate := h_ℓ_add_R_rate) stmtIn witIn
      · have h_compat' := h_compat
        dsimp [reducedMLPEvalStatement_to_BBF_Statement, strictOracleFoldingConsistencyProp]
          at h_compat' ⊢
        exact h_compat'
  lift_complete := fun outerStmtIn outerWitIn innerStmtOut innerWitOut hCompat hRelIn hRelOut => by
    cases innerWitOut
    dsimp [largeFieldInvocationCtxLens, largeFieldInvocationStmtLens] at hRelOut ⊢
    exact hRelOut

variable {σ : Type} {init : ProbComp σ} {impl : QueryImpl []ₒ (StateT σ ProbComp)}

/-- Perfect completeness of the lifted large-field invocation, **conditional on the inner
Binary Basefold full-protocol completeness** (`hBBFFullCompleteness`). That inner fact is the
lane-2 surface `FullBinaryBasefold.fullOracleReduction_perfectCompleteness_wired` (whose own
remaining hypothesis is the core-interaction phase completeness); it is threaded here rather
than assumed closed. The input relation is the **strict** track (`toStrictRelInput`): w.r.t.
the relaxed relation the statement is false (a δ-close-but-unequal committed oracle is caught
by the proximity test with positive probability). -/
theorem largeFieldInvocationOracleReduction_perfectCompleteness
    (hBBFFullCompleteness : OracleReduction.perfectCompleteness
      (oracleReduction := FullBinaryBasefold.fullOracleReduction 𝔽q β γ_repetitions
        (ϑ := ϑ) (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (𝓑 := 𝓑) (ℓ := ℓ'))
      (relIn := strictRoundRelation (mp := BBF_SumcheckMultiplierParam) 𝔽q β
        (ϑ := ϑ) (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (𝓑 := 𝓑) (0 : Fin (ℓ' + 1)))
      (relOut := acceptRejectOracleRel)
      (init := init)
      (impl := impl)) :
    OracleReduction.perfectCompleteness
    (oracleReduction := largeFieldInvocationOracleReduction 𝔽q β γ_repetitions (𝓑 := 𝓑))
    (relIn := (bbfAbstractOStmtIn 𝔽q β
      (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (ϑ := ϑ)).toStrictRelInput)
    (relOut := acceptRejectOracleRel)
    (init := init)
    (impl := impl) := by
  let innerReduction := FullBinaryBasefold.fullOracleReduction 𝔽q β γ_repetitions
    (ϑ := ϑ) (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (𝓑 := 𝓑) (ℓ := ℓ')
  letI : (largeFieldInvocationCtxLens 𝔽q β).toContext.IsComplete
      (outerRelIn := (bbfAbstractOStmtIn 𝔽q β
        (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (ϑ := ϑ)).toStrictRelInput)
      (innerRelIn := strictRoundRelation (mp := BBF_SumcheckMultiplierParam) 𝔽q β
        (ϑ := ϑ) (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (𝓑 := 𝓑) (0 : Fin (ℓ' + 1)))
      (outerRelOut := acceptRejectOracleRel)
      (innerRelOut := acceptRejectOracleRel)
      (compat := Reduction.compatContext (oSpec := []ₒ)
        (pSpec := fullPSpec 𝔽q β γ_repetitions (ϑ := ϑ)
          (h_ℓ_add_R_rate := h_ℓ_add_R_rate))
        (largeFieldInvocationCtxLens 𝔽q β).toContext
        innerReduction.toReduction) := by
    infer_instance
  have h_inner := hBBFFullCompleteness
  have h_lift :=
    (OracleReduction.liftContext_perfectCompleteness
      (R := innerReduction)
      (lens := largeFieldInvocationCtxLens 𝔽q β)
      (outerRelIn := (bbfAbstractOStmtIn 𝔽q β
        (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (ϑ := ϑ)).toStrictRelInput)
      (innerRelIn := strictRoundRelation (mp := BBF_SumcheckMultiplierParam) 𝔽q β
        (ϑ := ϑ) (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (𝓑 := 𝓑) (0 : Fin (ℓ' + 1)))
      (outerRelOut := acceptRejectOracleRel)
      (innerRelOut := acceptRejectOracleRel)
      (init := init)
      (impl := impl)
      h_inner)
  dsimp [largeFieldInvocationOracleReduction, innerReduction] at h_lift ⊢
  exact h_lift

lemma MLPEvalRelation_of_round0_local_and_structural
    (stmt : MLPEvalStatement (L := L) (ℓ := ℓ'))
    (wit : Witness (L := L) 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (ℓ := ℓ')
      (0 : Fin (ℓ' + 1)))
    (h_local : sumcheckConsistencyProp (𝓑 := 𝓑)
      (reducedMLPEvalStatement_to_BBF_Statement (L := L) (ℓ' := ℓ') stmt).sumcheck_target wit.H)
    (h_struct : Binius.BinaryBasefold.witnessStructuralInvariant 𝔽q β
      (mp := BBF_SumcheckMultiplierParam) (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
      (reducedMLPEvalStatement_to_BBF_Statement (L := L) (ℓ' := ℓ') stmt) wit) :
    wit.t.val.eval stmt.t_eval_point = stmt.original_claim := by
  let stmt_eval : MLPEvalStatement (L := L) (ℓ := ℓ') := {
    t_eval_point := stmt.t_eval_point
    original_claim := wit.t.val.eval stmt.t_eval_point
  }
  let wit_eval : WitMLP (K := L) (ℓ := ℓ') := { t := wit.t }
  have h_eval_stmt_eval : wit_eval.t.val.eval stmt_eval.t_eval_point
    = stmt_eval.original_claim := by rfl
  have h_local_eval :
      sumcheckConsistencyProp (𝓑 := 𝓑)
        (reducedMLPEvalStatement_to_BBF_Statement (L := L) (ℓ' := ℓ') stmt_eval).sumcheck_target
        (MLPEvalWitness_to_BBF_Witness 𝔽q β
          (h_ℓ_add_R_rate := h_ℓ_add_R_rate) stmt_eval wit_eval).H :=
    sumcheckConsistency_MLPEvalWitness_to_BBF_Witness_of_eval 𝔽q β
      (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (𝓑 := 𝓑) stmt_eval wit_eval h_eval_stmt_eval
  have h_H_eq :
      wit.H = (MLPEvalWitness_to_BBF_Witness 𝔽q β
        (h_ℓ_add_R_rate := h_ℓ_add_R_rate) stmt_eval wit_eval).H := by
    calc
      wit.H = projectToMidSumcheckPoly (L := L) (ℓ := ℓ') (t := wit.t)
          (m := BBF_SumcheckMultiplierParam.multpoly ⟨stmt.t_eval_point, stmt.original_claim⟩)
          (i := (0 : Fin (ℓ' + 1))) (challenges := Fin.elim0) := by
            have h_struct0 := h_struct.1
            dsimp [Binius.BinaryBasefold.witnessStructuralInvariant,
              reducedMLPEvalStatement_to_BBF_Statement] at h_struct0 ⊢
            exact h_struct0
      _ = projectToMidSumcheckPoly (L := L) (ℓ := ℓ') (t := wit.t)
          (m := BBF_SumcheckMultiplierParam.multpoly ⟨stmt_eval.t_eval_point,
            stmt_eval.original_claim⟩)
          (i := (0 : Fin (ℓ' + 1))) (challenges := Fin.elim0) := by
            simp [stmt_eval, BBF_SumcheckMultiplierParam, BBF_eq_multiplier]
      _ = (MLPEvalWitness_to_BBF_Witness 𝔽q β
          (h_ℓ_add_R_rate := h_ℓ_add_R_rate) stmt_eval wit_eval).H := by
            simp [MLPEvalWitness_to_BBF_Witness, wit_eval]
  have h_sum_eq_claim :
      stmt.original_claim = ∑ x ∈ (univ.map 𝓑) ^ᶠ (ℓ'),
        wit.H.val.eval x := by
    have h_local' := h_local
    dsimp [sumcheckConsistencyProp, reducedMLPEvalStatement_to_BBF_Statement] at h_local' ⊢
    exact h_local'
  have h_sum_eq_eval :
      wit.t.val.eval stmt.t_eval_point = ∑ x ∈ (univ.map 𝓑) ^ᶠ (ℓ'),
        wit.H.val.eval x := by
    have h_sum_eq_eval' :
        wit.t.val.eval stmt.t_eval_point = ∑ x ∈ (univ.map 𝓑) ^ᶠ (ℓ'),
          (MLPEvalWitness_to_BBF_Witness 𝔽q β
            (h_ℓ_add_R_rate := h_ℓ_add_R_rate) stmt_eval wit_eval).H.val.eval x := by
      have h_local_eval' := h_local_eval
      dsimp [sumcheckConsistencyProp, reducedMLPEvalStatement_to_BBF_Statement, stmt_eval]
        at h_local_eval' ⊢
      exact h_local_eval'
    have h_H_eval :
        (∑ x ∈ (univ.map 𝓑) ^ᶠ (ℓ'),
          (MLPEvalWitness_to_BBF_Witness 𝔽q β
            (h_ℓ_add_R_rate := h_ℓ_add_R_rate) stmt_eval wit_eval).H.val.eval x) =
        ∑ x ∈ (univ.map 𝓑) ^ᶠ (ℓ'), wit.H.val.eval x := by
      exact congrArg (fun H => ∑ x ∈ (univ.map 𝓑) ^ᶠ (ℓ'), H.val.eval x) h_H_eq.symm
    exact h_sum_eq_eval'.trans h_H_eval
  calc
    wit.t.val.eval stmt.t_eval_point = ∑ x ∈ (univ.map 𝓑) ^ᶠ (ℓ'), wit.H.val.eval x := h_sum_eq_eval
    _ = stmt.original_claim := h_sum_eq_claim.symm

/-- Extractor lens for lifting Binary Basefold RBR-KS to the large-field invocation wrapper. -/
def largeFieldInvocationExtractorLens : Extractor.Lens
    (OuterStmtIn := MLPEvalStatement (L := L) (ℓ := ℓ') ×
      (∀ j, OracleStatement 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (ℓ := ℓ') ϑ
        (0 : Fin (ℓ' + 1)) j))
    (OuterStmtOut := Bool × (∀ j : Empty, Unit))
    (InnerStmtIn := Statement (L := L) (SumcheckBaseContext L ℓ') (0 : Fin (ℓ' + 1)) ×
      (∀ j, OracleStatement 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (ℓ := ℓ') ϑ
        (0 : Fin (ℓ' + 1)) j))
    (InnerStmtOut := Bool × (∀ j : Empty, Unit))
    (OuterWitIn := WitMLP (K := L) (ℓ := ℓ'))
    (OuterWitOut := Unit)
    (InnerWitIn := Witness (L := L) 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (ℓ := ℓ')
      (0 : Fin (ℓ' + 1)))
    (InnerWitOut := Unit) where
  stmt := largeFieldInvocationStmtLens 𝔽q β
  wit := {
    toFunA := fun _ => ()
    toFunB := fun ⟨⟨_stmtIn, _oStmtIn⟩, _outerWitOut⟩ innerWitIn => ⟨innerWitIn.t⟩
  }

instance largeFieldInvocationExtractorLens_rbr_knowledge_soundness
    {compatStmt :
      (MLPEvalStatement (L := L) (ℓ := ℓ') ×
        (∀ i, OracleStatement 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (ℓ := ℓ') ϑ
          (0 : Fin (ℓ' + 1)) i)) →
      (Bool × (∀ i : Empty, Unit)) → Prop} :
    Extractor.Lens.IsKnowledgeSound
      (OuterStmtIn := MLPEvalStatement (L := L) (ℓ := ℓ') ×
        (∀ i, OracleStatement 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (ℓ := ℓ') ϑ
          (0 : Fin (ℓ' + 1)) i))
      (OuterStmtOut := Bool × (∀ i : Empty, Unit))
      (InnerStmtIn := Statement (L := L) (SumcheckBaseContext L ℓ') (0 : Fin (ℓ' + 1)) ×
        (∀ i, OracleStatement 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (ℓ := ℓ') ϑ
          (0 : Fin (ℓ' + 1)) i))
      (InnerStmtOut := Bool × (∀ i : Empty, Unit))
      (OuterWitIn := WitMLP (K := L) (ℓ := ℓ'))
      (OuterWitOut := Unit)
      (InnerWitIn := Witness (L := L) 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
        (ℓ := ℓ') (0 : Fin (ℓ' + 1)))
      (InnerWitOut := Unit)
      (outerRelIn := (bbfAbstractOStmtIn 𝔽q β
        (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (ϑ := ϑ)).toRelInput)
      (innerRelIn := roundRelation (mp := BBF_SumcheckMultiplierParam) 𝔽q β (ϑ := ϑ)
        (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (𝓑 := 𝓑) (0 : Fin (ℓ' + 1)))
      (outerRelOut := acceptRejectOracleRel)
      (innerRelOut := acceptRejectOracleRel)
      (compatStmt := compatStmt)
      (compatWit := fun _ _ => True)
      (lens := largeFieldInvocationExtractorLens 𝔽q β) where
  proj_knowledgeSound := by
    intro outerStmtIn innerStmtOut outerWitOut _ hOuter
    dsimp [largeFieldInvocationExtractorLens, largeFieldInvocationStmtLens] at hOuter ⊢
    exact hOuter
  lift_knowledgeSound := by
    intro outerStmtIn outerWitOut innerWitIn _ hInner
    rcases outerStmtIn with ⟨stmtIn, oStmtIn⟩
    have hInner' :
        roundRelationProp (mp := BBF_SumcheckMultiplierParam) 𝔽q β
          (ϑ := ϑ) (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (𝓑 := 𝓑)
          (0 : Fin (ℓ' + 1))
          ((reducedMLPEvalStatement_to_BBF_Statement (L := L) (ℓ' := ℓ') stmtIn,
            oStmtIn), innerWitIn) := by
      dsimp [roundRelation, Set.mem_setOf_eq] at hInner ⊢
      exact hInner
    unfold roundRelationProp Binius.BinaryBasefold.masterKStateProp at hInner'
    have h_no_bad :
        ¬ incrementalBadEventExistsProp 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
          (ϑ := ϑ) (stmtIdx := (0 : Fin (ℓ' + 1)))
          (oracleIdx := OracleFrontierIndex.mkFromStmtIdx (0 : Fin (ℓ' + 1)))
          (oStmt := oStmtIn)
          (challenges := (reducedMLPEvalStatement_to_BBF_Statement (L := L)
            (ℓ' := ℓ') stmtIn).challenges) := by
      intro h_bad
      rcases h_bad with ⟨j, hj⟩
      have hj0 : j = 0 := by
        apply Fin.eq_of_val_eq
        have hjlt : j.val < 1 := by
          have h_j_lt := j.isLt
          change j.val < toOutCodewordsCount ℓ' ϑ (0 : Fin (ℓ' + 1)) at h_j_lt
          rw [toOutCodewordsCountOf0] at h_j_lt
          exact h_j_lt
        exact Nat.lt_one_iff.mp hjlt
      subst hj0
      dsimp [oraclePositionToDomainIndex] at hj
      exact absurd hj (by
        apply BinaryBasefold.incrementalFoldingBadEvent_of_k_eq_0_is_false (𝔽q := 𝔽q) (β := β)
          (h_k := by
            simp only [Nat.zero_mod, zero_mul, tsub_self, zero_le, inf_of_le_right])
          (h_midIdx := by simp only [Nat.zero_mod, zero_mul, tsub_self, zero_le,
            inf_of_le_right, add_zero])
      )
    rcases hInner' with h_bad | h_good
    · exact (h_no_bad h_bad).elim
    · have h_local := h_good.1
      have h_struct := h_good.2.1
      have h_first := h_good.2.2.1
      refine ⟨?_, ?_⟩
      · exact MLPEvalRelation_of_round0_local_and_structural 𝔽q β
          (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (𝓑 := 𝓑)
          stmtIn innerWitIn h_local h_struct
      · have h_first' := h_first
        dsimp [bbfAbstractOStmtIn] at h_first' ⊢
        exact h_first'

/-! ### Challenge `Fintype`/`Inhabited` instances for the BBF protocol-spec tower

The RingSwitching end-to-end completeness capstone consumes
`[∀ i, Fintype (mlIOPCS.pSpec.Challenge i)]` and `[∀ i, Inhabited (…)]` (its run-semantics
keystone needs finite, inhabited challenge oracles), and `SampleableType` implies neither.
We register both chains for `fullPSpec`, mirroring the `SampleableType` chain in
`BinaryBasefold/Spec.lean`; leaf challenge types are `L` and `Fin γ → sDomain …`. -/

section ChallengeInstances

instance : ∀ j, Fintype ((pSpecFold (L := L)).Challenge j)
  | ⟨0, hj⟩ => by nomatch hj
  | ⟨1, _⟩ => inferInstanceAs (Fintype L)

instance : ∀ j, Inhabited ((pSpecFold (L := L)).Challenge j)
  | ⟨0, hj⟩ => by nomatch hj
  | ⟨1, _⟩ => ⟨(0 : L)⟩

instance : ∀ j, Fintype ((pSpecRelay).Challenge j)
  | ⟨x, _⟩ => x.elim0

instance : ∀ j, Inhabited ((pSpecRelay).Challenge j)
  | ⟨x, _⟩ => x.elim0

instance {i : Fin ℓ'} : ∀ j, Fintype ((pSpecCommit 𝔽q β
    (h_ℓ_add_R_rate := h_ℓ_add_R_rate) i).Challenge j)
  | ⟨0, hj⟩ => by nomatch hj

instance {i : Fin ℓ'} : ∀ j, Inhabited ((pSpecCommit 𝔽q β
    (h_ℓ_add_R_rate := h_ℓ_add_R_rate) i).Challenge j)
  | ⟨0, hj⟩ => by nomatch hj

instance : ∀ j, Fintype ((pSpecFoldRelay (L := L)).Challenge j) :=
  appendChallenge_fintype _ _

instance : ∀ j, Inhabited ((pSpecFoldRelay (L := L)).Challenge j) :=
  appendChallenge_inhabited _ _

instance {i : Fin ℓ'} : ∀ j, Fintype ((pSpecFoldCommit 𝔽q β
    (h_ℓ_add_R_rate := h_ℓ_add_R_rate) i).Challenge j) :=
  appendChallenge_fintype _ _

instance {i : Fin ℓ'} : ∀ j, Inhabited ((pSpecFoldCommit 𝔽q β
    (h_ℓ_add_R_rate := h_ℓ_add_R_rate) i).Challenge j) :=
  appendChallenge_inhabited _ _

instance {n : ℕ} : ∀ j, Fintype ((pSpecFoldRelaySequence (L := L) n).Challenge j) :=
  seqComposeChallenge_fintype _

instance {n : ℕ} : ∀ j, Inhabited ((pSpecFoldRelaySequence (L := L) n).Challenge j) :=
  seqComposeChallenge_inhabited _

instance {i : Fin (ℓ' / ϑ - 1)} : ∀ j, Fintype ((pSpecFullNonLastBlock 𝔽q β
    (h_ℓ_add_R_rate := h_ℓ_add_R_rate) i).Challenge j) :=
  appendChallenge_fintype _ _

instance {i : Fin (ℓ' / ϑ - 1)} : ∀ j, Inhabited ((pSpecFullNonLastBlock 𝔽q β
    (h_ℓ_add_R_rate := h_ℓ_add_R_rate) i).Challenge j) :=
  appendChallenge_inhabited _ _

instance : ∀ j, Fintype ((pSpecNonLastBlocks 𝔽q β (ϑ := ϑ)
    (h_ℓ_add_R_rate := h_ℓ_add_R_rate)).Challenge j) :=
  seqComposeChallenge_fintype _

instance : ∀ j, Inhabited ((pSpecNonLastBlocks 𝔽q β (ϑ := ϑ)
    (h_ℓ_add_R_rate := h_ℓ_add_R_rate)).Challenge j) :=
  seqComposeChallenge_inhabited _

instance : ∀ j, Fintype ((pSpecLastBlock (L := L) (ϑ := ϑ)).Challenge j) :=
  seqComposeChallenge_fintype _

instance : ∀ j, Inhabited ((pSpecLastBlock (L := L) (ϑ := ϑ)).Challenge j) :=
  seqComposeChallenge_inhabited _

instance : ∀ j, Fintype ((pSpecSumcheckFold 𝔽q β (ϑ := ϑ)
    (h_ℓ_add_R_rate := h_ℓ_add_R_rate)).Challenge j) :=
  appendChallenge_fintype _ _

instance : ∀ j, Inhabited ((pSpecSumcheckFold 𝔽q β (ϑ := ϑ)
    (h_ℓ_add_R_rate := h_ℓ_add_R_rate)).Challenge j) :=
  appendChallenge_inhabited _ _

instance : ∀ j, Fintype ((pSpecFinalSumcheckStep (L := L)).Challenge j)
  | ⟨0, _⟩ => inferInstanceAs (Fintype L)

instance : ∀ j, Inhabited ((pSpecFinalSumcheckStep (L := L)).Challenge j)
  | ⟨0, _⟩ => ⟨(0 : L)⟩

instance : ∀ j, Fintype ((pSpecCoreInteraction 𝔽q β (ϑ := ϑ)
    (h_ℓ_add_R_rate := h_ℓ_add_R_rate)).Challenge j) :=
  appendChallenge_fintype _ _

instance : ∀ j, Inhabited ((pSpecCoreInteraction 𝔽q β (ϑ := ϑ)
    (h_ℓ_add_R_rate := h_ℓ_add_R_rate)).Challenge j) :=
  appendChallenge_inhabited _ _

instance : ∀ j, Fintype ((pSpecQuery 𝔽q β γ_repetitions
    (h_ℓ_add_R_rate := h_ℓ_add_R_rate)).Challenge j)
  | ⟨0, _⟩ => by
    haveI : Fintype (sDomain 𝔽q β h_ℓ_add_R_rate 0) :=
      fintype_sDomain 𝔽q β h_ℓ_add_R_rate 0
    exact inferInstanceAs
      (Fintype (Fin γ_repetitions → sDomain 𝔽q β h_ℓ_add_R_rate 0))

instance : ∀ j, Inhabited ((pSpecQuery 𝔽q β γ_repetitions
    (h_ℓ_add_R_rate := h_ℓ_add_R_rate)).Challenge j)
  | ⟨0, _⟩ => ⟨fun _ => 0⟩

instance : ∀ j, Fintype ((fullPSpec 𝔽q β γ_repetitions (ϑ := ϑ)
    (h_ℓ_add_R_rate := h_ℓ_add_R_rate)).Challenge j) :=
  appendChallenge_fintype _ _

instance : ∀ j, Inhabited ((fullPSpec 𝔽q β γ_repetitions (ϑ := ϑ)
    (h_ℓ_add_R_rate := h_ℓ_add_R_rate)).Challenge j) :=
  appendChallenge_inhabited _ _

end ChallengeInstances

/-! ### MLIOPCS Instance -/

/-- **External surface (lane 2, #317): inner Binary Basefold full-protocol perfect
completeness.** Discharged by
`FullBinaryBasefold.fullOracleReduction_perfectCompleteness_wired` once its remaining
core-interaction completeness hypothesis is closed (the `coreInteraction ⋈ queryPhase` seam
and the query phase itself are already proven there). -/
abbrev BBFInnerPerfectCompleteness : Prop :=
  ∀ {σ : Type} {init : ProbComp σ} {impl : QueryImpl []ₒ (StateT σ ProbComp)},
    NeverFail init →
    OracleReduction.perfectCompleteness
      (oracleReduction := FullBinaryBasefold.fullOracleReduction 𝔽q β γ_repetitions
        (ϑ := ϑ) (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (𝓑 := 𝓑) (ℓ := ℓ'))
      (relIn := strictRoundRelation (mp := BBF_SumcheckMultiplierParam) 𝔽q β
        (ϑ := ϑ) (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (𝓑 := 𝓑) (0 : Fin (ℓ' + 1)))
      (relOut := acceptRejectOracleRel)
      (init := init) (impl := impl)

/-- **External surface (lane 2, #317): inner Binary Basefold full-protocol round-by-round
knowledge soundness.** Discharged by
`FullBinaryBasefold.fullOracleVerifier_rbrKnowledgeSoundness_wired` once its remaining
core-interaction RBR-KS hypothesis and the compiled core-interaction verifier
failing-determinism witness are closed (the seam keystone and the query phase are already
proven there). -/
abbrev BBFInnerRbrKnowledgeSoundness : Prop :=
  ∀ {σ : Type} {init : ProbComp σ} {impl : QueryImpl []ₒ (StateT σ ProbComp)},
    (FullBinaryBasefold.fullOracleVerifier 𝔽q β γ_repetitions (ϑ := ϑ) (𝓑 := 𝓑)
      (h_ℓ_add_R_rate := h_ℓ_add_R_rate)).rbrKnowledgeSoundness init impl
      (relIn := roundRelation (mp := BBF_SumcheckMultiplierParam) 𝔽q β (ϑ := ϑ)
        (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (𝓑 := 𝓑) (0 : Fin (ℓ' + 1)))
      (relOut := acceptRejectOracleRel)
      (rbrKnowledgeError := fullRbrKnowledgeError 𝔽q β γ_repetitions (ϑ := ϑ)
        (h_ℓ_add_R_rate := h_ℓ_add_R_rate))

/-- Binary Basefold as an `MLIOPCS L ℓ'`.

This wraps the full Binary Basefold protocol (core interaction + query phase)
as a multilinear polynomial commitment scheme over the large field `L`.

The two parameters are the inner Binary Basefold full-protocol security facts — the lane-2
front-door surfaces of issue #317:
* `hBBFComplete` discharges via `FullBinaryBasefold.fullOracleReduction_perfectCompleteness_wired`
  once its core-interaction completeness hypothesis is closed;
* `hBBFRbrKS` discharges via `FullBinaryBasefold.fullOracleVerifier_rbrKnowledgeSoundness_wired`
  once its core-interaction RBR-KS + verifier failing-determinism witnesses are closed.

Everything else (the context/extractor lenses, the strict/relaxed relation seams, and both
structure security fields) is proven here. -/
def bbfMLIOPCS
    (hBBFComplete : BBFInnerPerfectCompleteness 𝔽q β γ_repetitions
      (ϑ := ϑ) (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (𝓑 := 𝓑))
    (hBBFRbrKS : BBFInnerRbrKnowledgeSoundness 𝔽q β γ_repetitions
      (ϑ := ϑ) (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (𝓑 := 𝓑)) :
    MLIOPCS L ℓ' where
  toAbstractOStmtIn := bbfAbstractOStmtIn 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (ϑ := ϑ)
  numRounds := _  -- inferred from fullPSpec
  pSpec := fullPSpec 𝔽q β γ_repetitions (ϑ := ϑ) (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
  Oₘ := inferInstance
  O_challenges := inferInstance
  oracleReduction := largeFieldInvocationOracleReduction 𝔽q β γ_repetitions (𝓑 := 𝓑)
  perfectCompleteness := by
    intro σ init impl hInit
    exact largeFieldInvocationOracleReduction_perfectCompleteness 𝔽q β γ_repetitions (𝓑 := 𝓑)
      (init := init) (impl := impl) (hBBFComplete hInit)
  rbrKnowledgeError :=
    fullRbrKnowledgeError 𝔽q β γ_repetitions (ϑ := ϑ) (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
  rbrKnowledgeSoundness := by
    intro σ init impl
    have h_bbf := hBBFRbrKS (init := init) (impl := impl)
    letI :
        Inhabited (Witness (L := L) 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (ℓ := ℓ')
          (0 : Fin (ℓ' + 1))) := ⟨{
        t := 0
        H := 0
        f := fun _ => 0
      }⟩
    letI : ∀ i : Empty, Inhabited ((fun _ : Empty => Unit) i) := by
      intro i
      exact (i.elim)
    have h_lifted := OracleVerifier.liftContext_rbr_knowledgeSoundness
        (V := FullBinaryBasefold.fullOracleVerifier 𝔽q β γ_repetitions (ϑ := ϑ)
          (𝓑 := 𝓑) (h_ℓ_add_R_rate := h_ℓ_add_R_rate))
        (stmtLens := largeFieldInvocationStmtLens 𝔽q β)
        (witLens := (largeFieldInvocationExtractorLens 𝔽q β).wit)
        (lensKS := largeFieldInvocationExtractorLens_rbr_knowledge_soundness
          (𝔽q := 𝔽q) (β := β)
          (ϑ := ϑ) (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (𝓑 := 𝓑)
          (compatStmt := (FullBinaryBasefold.fullOracleVerifier 𝔽q β γ_repetitions (ϑ := ϑ)
            (𝓑 := 𝓑) (h_ℓ_add_R_rate := h_ℓ_add_R_rate)).toVerifier.compatStatement
            (largeFieldInvocationStmtLens 𝔽q β)))
        (h := by exact h_bbf)
    dsimp [largeFieldInvocationOracleReduction] at h_lifted ⊢
    exact h_lifted

end BinaryBasefoldMLIOPCS

/-! ## Part 2: End-to-End Composition

Compose Ring-switching with the Binary Basefold MLIOPCS using the existing
infrastructure in `RingSwitching/General.lean`.
-/

section Composition

variable {r : ℕ} [NeZero r]
variable {L : Type} [Field L] [Fintype L] [DecidableEq L] [CharP L 2]
  [SampleableType L]
variable (𝔽q : Type) [Field 𝔽q] [Fintype 𝔽q] [DecidableEq 𝔽q]
  [h_Fq_char_prime : Fact (Nat.Prime (ringChar 𝔽q))] [hF₂ : Fact (Fintype.card 𝔽q = 2)]
variable [Algebra 𝔽q L]
variable (β : Fin r → L) [hβ_lin_indep : Fact (LinearIndependent 𝔽q β)]
  [h_β₀_eq_1 : Fact (β 0 = 1)]
variable {ℓ' 𝓡 ϑ : ℕ} (γ_repetitions : ℕ) [NeZero ℓ'] [NeZero 𝓡] [NeZero ϑ]
variable {h_ℓ_add_R_rate : ℓ' + 𝓡 < r}
variable {𝓑 : Fin 2 ↪ L}
variable [h_B01 : Fact (𝓑 0 = 0 ∧ 𝓑 1 = 1)]
variable [hdiv : Fact (ϑ ∣ ℓ')]

-- Ring-switching variables
variable (κ : ℕ) [NeZero κ]
variable (K : Type) [Field K] [Fintype K] [DecidableEq K]
variable [Algebra K L]
variable (β_rs : Basis (Fin κ → Fin 2) K L)
variable (ℓ : ℕ) [NeZero ℓ]
variable (h_l : ℓ = ℓ' + κ)

variable {σ : Type} (init : ProbComp σ) {impl : QueryImpl []ₒ (StateT σ ProbComp)}

/-- Perfect completeness of the composed protocol:
Ring-switching + Binary Basefold as MLIOPCS, on the strict-track input relation.

Instantiates the proven end-to-end capstone
`FullRingSwitching.fullOracleReduction_perfectCompleteness` (every ring-switching-side
residual — per-round, batching, final-sumcheck, loop seqCompose, and the three append seams —
is discharged there) at `P := binaryTowerProfile κ K L β_rs` with the Binary Basefold MLIOPCS.

Remaining hypotheses, all named and external:
* `hBBFComplete` — inner Binary Basefold completeness (lane-2 #317 surface;
  `FullBinaryBasefold.fullOracleReduction_perfectCompleteness_wired` reduces it to the
  core-interaction phase completeness);
* `hBBFRbrKS` — inner Binary Basefold RBR-KS (needed only to *form* `bbfMLIOPCS`);
* `hMlnPos` / `hMlnDir` — the opening's message-seam facts (BBF `fullPSpec` has a positive
  number of rounds and opens with a prover message): concrete Fin-cast facts about the
  `seqCompose`/`++ₚ` protocol-spec tower, not security assumptions. -/
theorem bbf_fullOracleReduction_perfectCompleteness
    (hBBFComplete : BBFInnerPerfectCompleteness 𝔽q β γ_repetitions
      (ϑ := ϑ) (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (𝓑 := 𝓑))
    (hBBFRbrKS : BBFInnerRbrKnowledgeSoundness 𝔽q β γ_repetitions
      (ϑ := ϑ) (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (𝓑 := 𝓑))
    (hInit : NeverFail init)
    (hMlnPos : 0 < (bbfMLIOPCS 𝔽q β γ_repetitions (ϑ := ϑ)
      (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (𝓑 := 𝓑) hBBFComplete hBBFRbrKS).numRounds)
    (hMlnDir : (bbfMLIOPCS 𝔽q β γ_repetitions (ϑ := ϑ)
      (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (𝓑 := 𝓑) hBBFComplete hBBFRbrKS).pSpec.dir
        ⟨0, hMlnPos⟩ = .P_to_V) :
    OracleReduction.perfectCompleteness
      (oracleReduction := FullRingSwitching.fullOracleReduction κ L K
        (binaryTowerProfile κ K L β_rs) ℓ ℓ' h_l
        (bbfMLIOPCS 𝔽q β γ_repetitions (ϑ := ϑ)
          (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (𝓑 := 𝓑) hBBFComplete hBBFRbrKS))
      (relIn := BatchingPhase.batchingInputRelation κ L K
        (binaryTowerProfile κ K L β_rs) ℓ ℓ' h_l
        (bbfMLIOPCS 𝔽q β γ_repetitions (ϑ := ϑ)
          (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (𝓑 := 𝓑)
          hBBFComplete hBBFRbrKS).toAbstractOStmtIn.strictVariant)
      (relOut := acceptRejectOracleRel)
      (init := init) (impl := impl) :=
  FullRingSwitching.fullOracleReduction_perfectCompleteness κ L K
    (binaryTowerProfile κ K L β_rs) ℓ ℓ' h_l
    (bbfMLIOPCS 𝔽q β γ_repetitions (ϑ := ϑ)
      (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (𝓑 := 𝓑) hBBFComplete hBBFRbrKS)
    hInit hMlnPos hMlnDir

/-- RBR knowledge soundness of the composed protocol:
Ring-switching + Binary Basefold as MLIOPCS.

Instantiates `FullRingSwitching.fullOracleVerifier_rbrKnowledgeSoundness` at
`P := binaryTowerProfile κ K L β_rs` with the Binary Basefold MLIOPCS.

The three `rbrKnowledgeSoundness` seam hypotheses are the **append-composition surfaces** of
issue #317 (the loop⋈final, batching⋈core and batchingCore⋈opening seams at the RBR-KS
level): the generic append keystone (`Verifier.append_rbrKnowledgeSoundness_keystone`)
still consumes the composite `KnowledgeStateFunction` and the per-round phase-2 flip bound
as explicit inputs, so these seams do not yet ground out in proofs. Each hypothesis is
honest and strictly smaller than the conclusion (none is the full-stack statement —
`hFullAppendRbrKnowledgeSoundness` is the final-seam transport consumed as `hResidual` by
`OracleVerifier.append_rbrKnowledgeSoundness`). `hBBFComplete`/`hBBFRbrKS` are the lane-2
inner-protocol surfaces, needed to form `bbfMLIOPCS` (and `hBBFRbrKS` is genuinely consumed
as the opening's RBR-KS). -/
theorem bbf_fullOracleVerifier_rbrKnowledgeSoundness
    (hBBFComplete : BBFInnerPerfectCompleteness 𝔽q β γ_repetitions
      (ϑ := ϑ) (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (𝓑 := 𝓑))
    (hBBFRbrKS : BBFInnerRbrKnowledgeSoundness 𝔽q β γ_repetitions
      (ϑ := ϑ) (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (𝓑 := 𝓑))
    (hCoreInteractionAppendRbrKnowledgeSoundness :
      let mlio := bbfMLIOPCS 𝔽q β γ_repetitions (ϑ := ϑ)
        (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (𝓑 := 𝓑) hBBFComplete hBBFRbrKS
      (SumcheckPhase.coreInteractionOracleVerifier κ L K (binaryTowerProfile κ K L β_rs)
        ℓ ℓ' h_l mlio.toAbstractOStmtIn).rbrKnowledgeSoundness
        (init := init) (impl := impl)
        (relIn := sumcheckRoundRelation κ L K (binaryTowerProfile κ K L β_rs) ℓ ℓ' h_l
          mlio.toAbstractOStmtIn 0)
        (relOut := mlio.toAbstractOStmtIn.toRelInput)
        (rbrKnowledgeError :=
          SumcheckPhase.coreInteractionRbrKnowledgeError (L := L) (ℓ' := ℓ')))
    (hBatchingCoreAppendRbrKnowledgeSoundness :
      let mlio := bbfMLIOPCS 𝔽q β γ_repetitions (ϑ := ϑ)
        (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (𝓑 := 𝓑) hBBFComplete hBBFRbrKS
      (FullRingSwitching.batchingCoreVerifier κ L K (binaryTowerProfile κ K L β_rs)
        ℓ ℓ' h_l mlio).rbrKnowledgeSoundness
        (init := init) (impl := impl)
        (relIn := FullRingSwitching.fullInputRelation κ L K (binaryTowerProfile κ K L β_rs)
          ℓ ℓ' h_l mlio)
        (relOut := mlio.toRelInput)
        (rbrKnowledgeError := FullRingSwitching.batchingCoreRbrKnowledgeError κ L K
          (binaryTowerProfile κ K L β_rs) ℓ'))
    (hFullAppendRbrKnowledgeSoundness :
      let mlio := bbfMLIOPCS 𝔽q β γ_repetitions (ϑ := ϑ)
        (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (𝓑 := 𝓑) hBBFComplete hBBFRbrKS
      (FullRingSwitching.fullOracleVerifier κ L K (binaryTowerProfile κ K L β_rs)
        ℓ ℓ' h_l mlio).rbrKnowledgeSoundness
        (init := init) (impl := impl)
        (relIn := FullRingSwitching.fullInputRelation κ L K (binaryTowerProfile κ K L β_rs)
          ℓ ℓ' h_l mlio)
        (relOut := FullRingSwitching.fullOutputRelation)
        (rbrKnowledgeError := fun i => FullRingSwitching.fullRbrKnowledgeError κ L K
          (binaryTowerProfile κ K L β_rs) ℓ' mlio i)) :
    OracleVerifier.rbrKnowledgeSoundness
      (verifier := FullRingSwitching.fullOracleVerifier κ L K
        (binaryTowerProfile κ K L β_rs) ℓ ℓ' h_l
        (bbfMLIOPCS 𝔽q β γ_repetitions (ϑ := ϑ)
          (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (𝓑 := 𝓑) hBBFComplete hBBFRbrKS))
      (init := init) (impl := impl)
      (relIn := FullRingSwitching.fullInputRelation κ L K (binaryTowerProfile κ K L β_rs)
        ℓ ℓ' h_l
        (bbfMLIOPCS 𝔽q β γ_repetitions (ϑ := ϑ)
          (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (𝓑 := 𝓑) hBBFComplete hBBFRbrKS))
      (relOut := FullRingSwitching.fullOutputRelation)
      (rbrKnowledgeError := fun i => FullRingSwitching.fullRbrKnowledgeError κ L K
        (binaryTowerProfile κ K L β_rs) ℓ'
        (bbfMLIOPCS 𝔽q β γ_repetitions (ϑ := ϑ)
          (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (𝓑 := 𝓑) hBBFComplete hBBFRbrKS) i) :=
  FullRingSwitching.fullOracleVerifier_rbrKnowledgeSoundness κ L K
    (binaryTowerProfile κ K L β_rs) ℓ ℓ' h_l
    (bbfMLIOPCS 𝔽q β γ_repetitions (ϑ := ϑ)
      (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (𝓑 := 𝓑) hBBFComplete hBBFRbrKS)
    init
    hCoreInteractionAppendRbrKnowledgeSoundness
    hBatchingCoreAppendRbrKnowledgeSoundness
    hFullAppendRbrKnowledgeSoundness

end Composition

end
end Binius.BBFSmallFieldIOPCS

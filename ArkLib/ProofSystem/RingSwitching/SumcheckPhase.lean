/-
Copyright (c) 2025 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chung Thai Nguyen, Quang Dao
-/

import ArkLib.ProofSystem.RingSwitching.Prelude
import ArkLib.ProofSystem.RingSwitching.Spec
import ArkLib.OracleReduction.Composition.Sequential.General
import ArkLib.OracleReduction.Composition.Sequential.Append
import ArkLib.OracleReduction.Security.RoundByRound

open OracleSpec OracleComp ProtocolSpec Finset Polynomial MvPolynomial
  Module TensorProduct Nat Matrix
open scoped NNReal
open Sumcheck.Structured

/-!
# Ring-Switching Core Interaction Phase

This module implements the core interactive sumcheck phase of the ring-switching protocol.

### Iterated Sumcheck Steps
6. P and V execute the following loop:
   for `i ∈ {0, ..., ℓ'-1}` do
     P sends V the polynomial `hᵢ(X) := Σ_{w ∈ {0,1}^{ℓ'-i-1}} h(r'₀, ..., r'_{i-1}, X, w₀, ...,
     w_{ℓ'-i-2})`.
     V requires `sᵢ ?= hᵢ(0) + hᵢ(1)`. V samples `r'ᵢ ← L`, sets `s_{i+1} := hᵢ(r'ᵢ)`,
     and sends P `r'ᵢ`.

Each iteration of the loop constitutes a single round:
- Round i (for i = 1, ..., ℓ'):
  1. Prover sends sumcheck polynomial h_i(X) over large field L
  2. Verifier samples challenge α_i ∈ L
    - Prover & verifier updates state based on challenge

This is the core computational phase with ℓ' rounds, each with 2 messages, and is the main
source of RBR knowledge soundness error.

### Final Sumcheck Step
7. `P` computes `s' := t'(r'_0, ..., r'_{ℓ'-1})` and sends `V` `s'`.
8. `V` sets `e := eq̃(φ₀(r_κ), ..., φ₀(r_{ℓ-1}), φ₁(r'_0), ..., φ₁(r'_{ℓ'-1}))` and
    decomposes `e =: Σ_{u ∈ {0,1}^κ} β_u ⊗ e_u`.
9. `V` requires `s_{ℓ'} ?= (Σ_{u ∈ {0,1}^κ} eq̃(u_0, ..., u_{κ-1}, r''_0, ..., r''_{κ-1}) ⋅ e_u) ⋅ s'`.
-/

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

section IteratedSumcheckStep

/-! ## Per-round prover / verifier (re-exported from `Sumcheck.Structured.SingleRound`)

The per-round protocol code was lifted to `ArkLib.ProofSystem.Sumcheck.Structured.SingleRound`
as `round{PrvState, OracleProver, OracleVerifier, OracleReduction}`,
`getRoundProverFinalOutput`, and `roundKnowledgeError`, parameterized over a generic
`Context : Type` and `OStmtIn : ιₛᵢ → Type`.

For backwards compatibility, the wrappers below preserve the original autobound signature
(via the surrounding variable block — `κ L K ℓ ℓ' aOStmtIn`) by specializing
`Context := RingSwitchingBaseContext κ L K ℓ` and `OStmtIn := aOStmtIn.OStmtIn`. They keep
the `iteratedSumcheck*` names (these are what the sumcheck loop iterates over) and are
`@[reducible]` so that subsequent soundness proofs and the seqCompose loop can still
access fields like `.KnowledgeStateFunction` / `.rbrKnowledgeSoundness` through them. -/

-- Ring-switching uses the plain degree-2 round polynomial (`H = P · t`), so the wrappers pin
-- `d := 2` when specializing the degree-generic `Sumcheck.Structured.round*` definitions.

@[reducible]
def iteratedSumcheckPrvState (i : Fin ℓ') : Fin (2 + 1) → Type :=
  Sumcheck.Structured.roundPrvState (L := L) ℓ'
    (RingSwitchingBaseContext κ L K ℓ P) (OStmtIn := aOStmtIn.OStmtIn) (d := 2) i

@[reducible]
def getIteratedSumcheckProverFinalOutput (i : Fin ℓ')
    (finalPrvState : iteratedSumcheckPrvState κ L K P ℓ ℓ' aOStmtIn i 2) :
    ((Statement (L := L) (ℓ := ℓ') (RingSwitchingBaseContext κ L K ℓ P) i.succ
      × (∀ j, aOStmtIn.OStmtIn j)) × SumcheckWitness L ℓ' i.succ) :=
  Sumcheck.Structured.getRoundProverFinalOutput (L := L) ℓ'
    (RingSwitchingBaseContext κ L K ℓ P) (OStmtIn := aOStmtIn.OStmtIn) (d := 2) i finalPrvState

@[reducible]
def iteratedSumcheckOracleProver (i : Fin ℓ') :
  OracleProver (oSpec := []ₒ)
    (StmtIn := Statement (L := L) (ℓ := ℓ') (RingSwitchingBaseContext κ L K ℓ P) i.castSucc)
    (OStmtIn := aOStmtIn.OStmtIn)
    (WitIn := SumcheckWitness L ℓ' i.castSucc)
    (StmtOut := Statement (L := L) (ℓ := ℓ') (RingSwitchingBaseContext κ L K ℓ P) i.succ)
    (OStmtOut := aOStmtIn.OStmtIn)
    (WitOut := SumcheckWitness L ℓ' i.succ)
    (pSpec := pSpecSumcheckRound L) :=
  Sumcheck.Structured.roundOracleProver (L := L) ℓ' (boolDomain L ℓ')
    (RingSwitchingBaseContext κ L K ℓ P) (OStmtIn := aOStmtIn.OStmtIn) (d := 2) i

@[reducible]
def iteratedSumcheckOracleVerifier (i : Fin ℓ') :
  OracleVerifier
    (oSpec := []ₒ)
    (StmtIn := Statement (L := L) (ℓ := ℓ') (RingSwitchingBaseContext κ L K ℓ P) i.castSucc)
    (OStmtIn := aOStmtIn.OStmtIn)
    (StmtOut := Statement (L := L) (ℓ := ℓ') (RingSwitchingBaseContext κ L K ℓ P) i.succ)
    (OStmtOut := aOStmtIn.OStmtIn)
    (pSpec := pSpecSumcheckRound L) :=
  Sumcheck.Structured.roundOracleVerifier (L := L) ℓ' (boolDomain L ℓ')
    (RingSwitchingBaseContext κ L K ℓ P) (OStmtIn := aOStmtIn.OStmtIn) (d := 2) i

@[reducible]
def iteratedSumcheckOracleReduction (i : Fin ℓ') :
  OracleReduction (oSpec := []ₒ)
    (StmtIn := Statement (L := L) (ℓ := ℓ') (RingSwitchingBaseContext κ L K ℓ P) i.castSucc)
    (OStmtIn := aOStmtIn.OStmtIn)
    (WitIn := SumcheckWitness L ℓ' i.castSucc)
    (StmtOut := Statement (L := L) (ℓ := ℓ') (RingSwitchingBaseContext κ L K ℓ P) i.succ)
    (OStmtOut := aOStmtIn.OStmtIn)
    (WitOut := SumcheckWitness L ℓ' i.succ)
    (pSpec := pSpecSumcheckRound L) :=
  Sumcheck.Structured.roundOracleReduction (L := L) ℓ' (boolDomain L ℓ')
    (RingSwitchingBaseContext κ L K ℓ P) (OStmtIn := aOStmtIn.OStmtIn) (d := 2) i

variable {R : Type} [CommSemiring R] [DecidableEq R] [SampleableType R]
  {n : ℕ} {deg : ℕ} {m : ℕ} {D : Fin m ↪ R}

variable {σ : Type} {init : ProbComp σ} {impl : QueryImpl []ₒ (StateT σ ProbComp)}

omit [Fintype L] [Fintype K] [DecidableEq K] in
theorem iteratedSumcheckOracleReduction_perfectCompleteness (i : Fin ℓ') :
    OracleReduction.perfectCompleteness
      (pSpec := pSpecSumcheckRound L)
      (relIn := sumcheckRoundRelation κ L K P ℓ ℓ' h_l aOStmtIn i.castSucc)
      (relOut := sumcheckRoundRelation κ L K P ℓ ℓ' h_l aOStmtIn i.succ)
      (oracleReduction := iteratedSumcheckOracleReduction κ L K P ℓ ℓ' aOStmtIn i)
      (init := init)
      (impl := impl) := by
  unfold OracleReduction.perfectCompleteness
  intro stmtIn witIn h_relIn
  simp only
  -- WIP (algebra UNBLOCKED by the defect-#20 machinery repair; remaining work is the run-shape peel).
  -- After the coherent var-ordering repair in `Sumcheck.Structured.SingleRound`, the honest round is
  -- now fully consistent and the OUTPUT relation is *provable* (no false residual remains):
  --   • challenges accumulate via `Fin.cons r' stmtIn.challenges` in BOTH the prover
  --     (`getRoundProverFinalOutput`) and the verifier (`roundOracleVerifier`), matching the cons-form
  --     round transition `RingSwitching.fixFirstVariablesOfMQP_projectToMid_step`;
  --   • `witnessStructuralInvariant i.succ` then holds: `witOut.H = fixFirstVariablesOfMQP … witIn.H
  --     {r'}` and, from the relIn invariant `witIn.H = projectToMidSumcheckPoly … i.castSucc ch`, the
  --     cons-step lemma gives `witOut.H = (rename finCongr) (projectToMidSumcheckPoly … i.succ
  --     (Fin.cons r' ch))` — exactly what relOut demands (the old cons=snoc obstruction is GONE);
  --   • `sumcheckConsistencyProp i.succ` holds: the repaired `getSumcheckRoundPoly` marginalises the
  --     LAST variable, so `stmtOut.sumcheck_target = h_i.eval r' = ∑_{next cube} (fix-last witIn.H
  --     {r'}) = ∑_{cube} witOut.H` via `getSumcheckRoundPoly_eval_eq_sum_snoc` + `fixFirstVariablesOfMQP_eval`;
  --     the verifier's check `∑_{D.points i} h_i.eval b = sumcheck_target` discharges from the relIn
  --     `sumcheckConsistencyProp i.castSucc` (`h_i` is the variable-`(last)` marginal of `witIn.H`);
  --   • `initialCompatibility` carries over (`witOut.t' = witIn.t'`).
  -- REMAINING (mechanical, no math obstruction): peel the 2-message honest `OracleReduction.run`
  -- (`run_eq_run_reduction` → `Reduction.run`/`Prover.run`/`Verifier.run` → `runToRound`/`processRound`
  -- `Fin.induction_two`), collapse the verifier's `simOracle2` message-query (`simulateQ_simOracle2_query`)
  -- and the `guard`-emitting failure branch (defect-#21, now in `roundOracleVerifier`), then discharge
  -- the four KState conjuncts above. This is the same run-shape plumbing as the final-sumcheck
  -- completeness peel; deferred here as WIP to keep the build green after the machinery repair landed.
  sorry

open scoped NNReal

-- Lifted to `Sumcheck.Structured.roundKnowledgeError` (degree-neutral). Binius ring-switching is
-- the degree-2 case, so this Binius-local abbrev pins `d := 2`.
abbrev roundKnowledgeError (L : Type) [Fintype L] (ℓ : ℕ) (i : Fin ℓ) : NNReal :=
  Sumcheck.Structured.roundKnowledgeError L ℓ i 2

omit [NeZero κ] [Fintype L] [DecidableEq L] [SampleableType L] [NeZero ℓ] [NeZero ℓ'] in
/-- **Target (b): `getSumcheckRoundPoly` value as a cube sum (LAST-variable/`snoc` form, defect-#20
repair).** The round univariate `getSumcheckRoundPoly ℓ (boolDomain L ℓ) i H` evaluated at the
verifier challenge `r'` equals the sum, over the next round's Boolean cube
`(boolDomain.drop (i+1)).cube`, of the full round polynomial `H` with the **last** round variable
fixed to `r'` (via `Fin.snoc`) and the surviving coordinates ranging over the cube. Proven from the
marginal identity `roundPoly_eval_eq_sum_snoc` (Prelude). `curH` is `H` transported across the index
equality `ℓ-i.castSucc = (ℓ-i.castSucc-1)+1` (`getSumcheckRoundPoly`'s own internal `curH_cast`,
supplied via a `HEq`).

VARIABLE-CONVENTION NOTE (defect-#20). The repaired `getSumcheckRoundPoly` keeps the **last**
variable as the round indeterminate (`finSuccEquivNth L (Fin.last _)` ⇒ `Fin.snoc … r'`), matching
the witness advance `getRoundProverFinalOutput`'s `fixFirstVariablesOfMQP … {r'}` (which also fixes
the *last* surviving variable) and the `Fin.cons`-form round transition
`fixFirstVariablesOfMQP_projectToMid_step`. The previous variable-`0` form was inconsistent with the
end-consuming order of `projectToMidSumcheckPoly`; for an asymmetric `H` the two marginals differ
(verified `ZMod 7` counterexample in `RingSwitching.Prelude`'s `RoundTransition` note). -/
theorem getSumcheckRoundPoly_eval_eq_sum_snoc (i : Fin ℓ')
    (H : L⦃≤ 2⦄[X Fin (ℓ' - ↑i.castSucc)]) (r' : L)
    (curH : L[X Fin ((ℓ' - ↑i.castSucc - 1) + 1)]) (hcurH : HEq curH H.val) :
    (getSumcheckRoundPoly ℓ' (boolDomain L ℓ') (i := i) H).val.eval r'
      = ∑ x ∈ ((boolDomain L ℓ').drop (↑i.castSucc + 1)).cube,
          MvPolynomial.eval
            (Fin.snoc (Fin.append x (fun j => j.elim0) ∘ Fin.cast (by omega)) r') curH := by
  unfold getSumcheckRoundPoly
  dsimp only
  rw [RingSwitching.roundPoly_eval_eq_sum_snoc]
  refine Finset.sum_congr rfl fun x _ => ?_
  congr 1
  apply eq_of_heq
  -- `curH_cast` is `Eq.mpr _ H.val`, hence `HEq` to `H.val`; `curH` is also `HEq` to `H.val`.
  refine HEq.trans ?_ hcurH.symm
  exact cast_heq _ _

omit [NeZero κ] [Fintype L] [DecidableEq L] [SampleableType L] [NeZero ℓ] [NeZero ℓ'] in
/-- Renaming a polynomial along the canonical index `finCongr` of a (propositional) dimension
equality `a = b` is heterogeneously equal to the original polynomial. -/
private lemma rename_finCongr_heq {a b : ℕ} (h : a = b) (p : MvPolynomial (Fin a) L) :
    HEq (rename (finCongr h) p) p := by
  subst h
  rw [finCongr_refl, Equiv.coe_refl, rename_id_apply]

/-- **Verifier-check identity (defect-#20 last-variable form).** Summing the prover's round
univariate `getSumcheckRoundPoly ℓ' (boolDomain L ℓ') i H` over coordinate `i`'s Boolean domain
`{0,1}` recovers the full cube-sum of the round polynomial `H` over the round-`i.castSucc` Boolean
cube. This is the honest verifier's step-6 check: `∑_{b ∈ D.points i} h_i.eval b = ∑_{cube} H`, which
the input relation's `sumcheckConsistencyProp` equates to `stmtIn.sumcheck_target`.

The univariate keeps the **last** surviving variable as the indeterminate, so the marginal is the
`snoc` cube-telescoping `sum_cube_snoc`: splitting off coordinate `Fin.last` of the round cube
`(boolDomain L (ℓ' - i.castSucc)).cube` reproduces exactly the `b`-then-survivors structure of the
univariate's evaluation. Both the survivor cubes `((boolDomain L ℓ').drop (i.castSucc+1))` (used by
`getSumcheckRoundPoly`) and `(boolDomain L (ℓ'-i.castSucc)).init` (produced by `sum_cube_snoc`)
collapse to the *uniform* Boolean cube of equal dimension `ℓ'-i.castSucc-1`, so the heterogeneous
`drop`-vs-`init` index gap is harmless for the Boolean domain. -/
theorem getSumcheckRoundPoly_points_sum_eq_cube (i : Fin ℓ')
    (H : L⦃≤ 2⦄[X Fin (ℓ' - ↑i.castSucc)]) :
    ∑ b ∈ (boolDomain L ℓ').points i,
        (getSumcheckRoundPoly ℓ' (boolDomain L ℓ') (i := i) H).val.eval b
      = ∑ z ∈ (boolDomain L (ℓ' - ↑i.castSucc)).cube, H.val.eval z := by
  -- `ℓ' - i.castSucc = (ℓ'-i.castSucc-1) + 1` from `i.isLt`.
  have hn : ℓ' - ↑i.castSucc = (ℓ' - ↑i.castSucc - 1) + 1 := by
    have := i.2; simp only [Fin.val_castSucc]; omega
  -- `curH := rename (finCongr hn) H.val` is `H.val` reindexed to `Fin ((ℓ'-i.castSucc-1)+1)`; the
  -- rename keeps the polynomial (just relabels variables along the canonical `Fin.cast`).
  set curH : L[X Fin ((ℓ' - ↑i.castSucc - 1) + 1)] := rename (finCongr hn) H.val with hcurH_def
  have hHEq : HEq curH H.val := by
    rw [hcurH_def]; exact rename_finCongr_heq (h := hn) (p := H.val)
  -- (1) LHS: each round-univariate value is a survivor-cube snoc-sum (degree-generic lemma).
  rw [show (∑ b ∈ (boolDomain L ℓ').points i,
        (getSumcheckRoundPoly ℓ' (boolDomain L ℓ') (i := i) H).val.eval b)
      = ∑ b ∈ (boolDomain L ℓ').points i,
          ∑ x ∈ ((boolDomain L ℓ').drop (↑i.castSucc + 1)).cube,
            MvPolynomial.eval
              (Fin.snoc (Fin.append x (fun j => j.elim0) ∘ Fin.cast (by omega)) b) curH from
    Finset.sum_congr rfl fun b _ =>
      Sumcheck.Structured.getSumcheckRoundPoly_eval_eq_sum_snoc ℓ' (boolDomain L ℓ')
        i H b curH hHEq]
  -- (2) RHS: transport the cube-sum of `H` to `curH` over `Fin ((ℓ'-i.castSucc-1)+1)` via the
  -- variable-renaming `eval_rename`, then split off the last coordinate via `sum_cube_snoc`.
  have heval_curH : ∀ z : Fin ((ℓ' - ↑i.castSucc - 1) + 1) → L,
      curH.eval z = H.val.eval (z ∘ finCongr hn) := by
    intro z; rw [hcurH_def, eval_rename]
  rw [show (∑ z ∈ (boolDomain L (ℓ' - ↑i.castSucc)).cube, H.val.eval z)
      = ∑ z ∈ (boolDomain L ((ℓ' - ↑i.castSucc - 1) + 1)).cube, curH.eval z from by
    apply Finset.sum_nbij' (fun z => z ∘ finCongr hn.symm) (fun z => z ∘ finCongr hn)
    · intro z hz; simp only [SumcheckDomain.mem_cube] at hz ⊢; intro j; simpa using hz _
    · intro z hz; simp only [SumcheckDomain.mem_cube] at hz ⊢; intro j; simpa using hz _
    · intro z _; funext j; simp only [Function.comp_apply, finCongr_apply,
        Fin.cast_cast, Fin.cast_eq_self]
    · intro z _; funext j; simp only [Function.comp_apply, finCongr_apply,
        Fin.cast_cast, Fin.cast_eq_self]
    · intro z _
      rw [heval_curH]
      refine congrArg (fun pt => MvPolynomial.eval pt H.val) ?_
      funext j
      simp only [Function.comp_apply, finCongr_apply, Fin.cast_cast, Fin.cast_eq_self]]
  rw [SumcheckDomain.sum_cube_snoc (boolDomain L ((ℓ' - ↑i.castSucc - 1) + 1))
    (fun z => curH.eval z)]
  -- (3) Match the outer Boolean point-sum (`b`) and the inner survivor cube-sums.
  -- Outer index sets: `(boolDomain ℓ').points i = univ.map boolEmbedding = points last` (uniform).
  simp only [points_boolDomain]
  refine Finset.sum_congr rfl fun b _ => ?_
  -- Inner survivor cubes: `((boolDomain ℓ').drop (i+1))` and `(boolDomain (..)).init` are both the
  -- uniform Boolean cube of dimension `ℓ'-i.castSucc-1`. Reindex by the canonical `Fin.cast`.
  simp only [boolDomain, SumcheckDomain.init_uniform, SumcheckDomain.drop_uniform]
  -- `ℓ' - (i.castSucc+1) = ℓ' - i.castSucc - 1`, so both cubes are over the same dimension up to a
  -- `Fin.cast` reindex of the points; the snoc-survivor reconstruction `append x ∅ ∘ cast` matches.
  apply Finset.sum_nbij' (fun x => x ∘ Fin.cast (by omega)) (fun y => y ∘ Fin.cast (by omega))
  · intro x hx
    simp only [SumcheckDomain.mem_cube] at hx ⊢
    intro j
    simpa using hx (Fin.cast (by omega) j)
  · intro y hy
    simp only [SumcheckDomain.mem_cube] at hy ⊢
    intro j
    simpa using hy (Fin.cast (by omega) j)
  · intro x _; funext j; simp
  · intro y _; funext j; simp
  · intro x _
    -- The snoc-survivor reconstructions agree: `append x ∅ ∘ cast` and `x ∘ cast` coincide as the
    -- survivor point (the `Fin.append`-with-empty is just `x`, up to the harmless `Fin.cast`).
    refine congrArg (fun pt => MvPolynomial.eval pt curH) ?_
    funext j
    refine Fin.lastCases ?_ (fun j => ?_) j
    · simp only [Fin.snoc_last]
    · simp only [Fin.snoc_castSucc, Function.comp_apply]
      -- `Fin.append x ∅` at a left-side (cast) index is just `x` at the matching index: rewrite the
      -- `Fin.cast` index as a `Fin.castAdd 0` and apply `Fin.append_left`.
      rw [show (Fin.cast (by omega) j : Fin (ℓ' - (↑i.castSucc + 1) + 0))
            = Fin.castAdd 0 (Fin.cast (by omega) j) from Fin.ext rfl,
          Fin.append_left]
      exact congrArg x (Fin.ext rfl)

noncomputable def iteratedSumcheckRbrExtractor (i : Fin ℓ') :
  Extractor.RoundByRound []ₒ
    (StmtIn := (Statement (L := L) (ℓ := ℓ')
      (RingSwitchingBaseContext κ L K ℓ P) i.castSucc) × (∀ j, aOStmtIn.OStmtIn j))
    (WitIn := SumcheckWitness L ℓ' i.castSucc)
    (WitOut := SumcheckWitness L ℓ' i.succ)
    (pSpec := pSpecSumcheckRound L)
    (WitMid := fun _messageIdx => SumcheckWitness L ℓ' i.castSucc) where
  eqIn := rfl
  extractMid := fun _ _ _ witMidSucc => witMidSucc
  extractOut := fun ⟨stmtIn, oStmtIn⟩ fullTranscript witOut => by
    exact {
      t' := witOut.t',
      H := projectToMidSumcheckPoly (L := L) (ℓ := ℓ') (t := witOut.t')
        (m := (RingSwitching_SumcheckMultParam κ L K P ℓ ℓ' h_l).multpoly (ctx := stmtIn.ctx))
        (i := i.castSucc) (challenges := stmtIn.challenges)
    }

/-- This follows the KState of `foldKStateProp` -/
def iteratedSumcheckKStateProp (i : Fin ℓ') (m : Fin (2 + 1))
    (tr : Transcript m (pSpecSumcheckRound L))
    (stmt : Statement (L := L) (ℓ := ℓ') (RingSwitchingBaseContext κ L K ℓ P) i.castSucc)
    (witMid : SumcheckWitness L ℓ' i.castSucc)
    (oStmt : ∀ j, aOStmtIn.OStmtIn j) :
    Prop :=
  -- Ground-truth polynomial from witness
  let h_star : ↥L⦃≤ 2⦄[X] := getSumcheckRoundPoly ℓ' (boolDomain L ℓ') (i := i)
    (h := witMid.H)
  -- Checks available after message 1 (P -> V : hᵢ(X))
  let get_Hᵢ := fun (m: Fin (2 + 1)) (tr: Transcript m (pSpecSumcheckRound L)) (hm: 1 ≤ m.val) =>
    let ⟨msgsUpTo, _⟩ := Transcript.equivMessagesChallenges (k := m)
      (pSpec := pSpecSumcheckRound L) tr
    let i_msg1 : ((pSpecSumcheckRound L).take m m.is_le).MessageIdx :=
      ⟨⟨0, Nat.lt_of_succ_le hm⟩, by simp [pSpecSumcheckRound]; rfl⟩
    let h_i : L⦃≤ 2⦄[X] := msgsUpTo i_msg1
    h_i

  let get_rᵢ' := fun (m: Fin (2 + 1)) (tr: Transcript m (pSpecSumcheckRound L)) (hm: 2 ≤ m.val) =>
    let ⟨msgsUpTo, chalsUpTo⟩ := Transcript.equivMessagesChallenges (k := m)
      (pSpec := pSpecSumcheckRound L) tr
    let i_msg1 : ((pSpecSumcheckRound L).take m m.is_le).MessageIdx :=
      ⟨⟨0, Nat.lt_of_succ_le (Nat.le_trans (by decide) hm)⟩, by simp; rfl⟩
    let h_i : L⦃≤ 2⦄[X] := msgsUpTo i_msg1
    let i_msg2 : ((pSpecSumcheckRound L).take m m.is_le).ChallengeIdx :=
      ⟨⟨1, Nat.lt_of_succ_le hm⟩, by simp only [Nat.reduceAdd]; rfl⟩
    let r_i' : L := chalsUpTo i_msg2
    r_i'

  match m with
  | ⟨0, _⟩ => -- equiv s relIn
    RingSwitching.masterKStateProp κ L K P ℓ ℓ' h_l 
      aOStmtIn
      (stmtIdx := i.castSucc)
      (stmt := stmt) (oStmt := oStmt) (wit := witMid)
      (localChecks := True)
  | ⟨1, h1⟩ => -- P sends hᵢ(X)
    RingSwitching.masterKStateProp κ L K P ℓ ℓ' h_l aOStmtIn
      (stmtIdx := i.castSucc)
      (stmt := stmt) (oStmt := oStmt) (wit := witMid)
      (localChecks :=
        let h_i := get_Hᵢ (m := ⟨1, h1⟩) (tr := tr) (hm := by simp only [le_refl])
        let explicitVCheck :=
          (∑ b ∈ (boolDomain L ℓ').points i, h_i.val.eval b) = stmt.sumcheck_target
        let localizedRoundPolyCheck := h_i = h_star
        explicitVCheck ∧ localizedRoundPolyCheck
      )
  | ⟨2, h2⟩ => -- implied by (relOut + V's check)
    -- The bad-folding-event of `fᵢ` is also introduced internaly by `masterKStateProp`
    RingSwitching.masterKStateProp κ L K P ℓ ℓ' h_l aOStmtIn
      (stmtIdx := i.castSucc)
      (stmt := stmt) (oStmt := oStmt) (wit := witMid)
      (localChecks :=
        let h_i := get_Hᵢ (m := ⟨2, h2⟩) (tr := tr) (hm := by simp only [Nat.one_le_ofNat])
        let r_i' := get_rᵢ' (m := ⟨2, h2⟩) (tr := tr) (hm := by simp only [le_refl])
        let localizedRoundPolyCheck := h_i = h_star
        let nextSumcheckTargetCheck := -- this presents sumcheck of next round (sᵢ = s^*ᵢ)
          h_i.val.eval r_i' = h_star.val.eval r_i'
        localizedRoundPolyCheck ∧ nextSumcheckTargetCheck
      ) -- this holds the constraint for witOut in relOut

/-- Knowledge state function (KState) for single round -/
def iteratedSumcheckKnowledgeStateFunction (i : Fin ℓ') :
    (iteratedSumcheckOracleVerifier κ L K P ℓ ℓ' aOStmtIn i).KnowledgeStateFunction init impl
      (relIn := sumcheckRoundRelation κ L K P ℓ ℓ' h_l aOStmtIn i.castSucc)
      (relOut := sumcheckRoundRelation κ L K P ℓ ℓ' h_l aOStmtIn i.succ)
      (extractor := iteratedSumcheckRbrExtractor κ L K P ℓ ℓ' h_l aOStmtIn i) where
  toFun := fun m ⟨stmt, oStmt⟩ tr witMid =>
    iteratedSumcheckKStateProp κ L K P ℓ ℓ' h_l 
      (i := i) (m := m) (tr := tr) (stmt := stmt) (witMid := witMid) (oStmt := oStmt)
  toFun_empty := fun _ _ => by
    simp only [sumcheckRoundRelation, sumcheckRoundRelationProp, Fin.coe_castSucc, cast_eq,
      Set.mem_setOf_eq, iteratedSumcheckKStateProp, masterKStateProp, true_and]
  toFun_next := fun m hDir stmtIn tr msg witMid => by
    obtain ⟨stmt, oStmt⟩ := stmtIn
    fin_cases m
    · -- m = 0: succ = 1, castSucc = 0
      unfold iteratedSumcheckKStateProp
      simp only [masterKStateProp, iteratedSumcheckRbrExtractor, true_and]
      simp only [Fin.succ_mk, Fin.castSucc_mk, Fin.castAdd_mk]
      tauto
    · -- m = 1: dir 1 = V_to_P, contradicts hDir
      simp [pSpecSumcheckRound] at hDir
  toFun_full := fun ⟨stmtLast, oStmtLast⟩ tr witOut => by
    intro h_relOut
    simp at h_relOut
    rcases h_relOut with ⟨stmtOut, ⟨oStmtOut, h_conj⟩⟩
    have h_simulateQ := h_conj.1
    have h_SumcheckStepRelOut := h_conj.2
    set witLast := (iteratedSumcheckRbrExtractor κ L K P ℓ ℓ' h_l aOStmtIn i).extractOut
      ⟨stmtLast, oStmtLast⟩ tr witOut
    simp only [Fin.reduceLast, Fin.isValue]
    -- ⊢ iteratedSumcheckKStateProp … 2 tr stmtLast witLast oStmtLast  (index `Fin.last 2 = ⟨2,_⟩`)
    --
    -- STRUCTURAL ANALYSIS (lane-b, building on the now-closed final-sumcheck accept branch).
    -- The support-extraction front-end is the same as the closed `finalSumcheck…toFun_full`:
    --   `probEvent_pos_iff` → `OptionT.mem_support_iff` → `support_bind`/`Set.mem_iUnion`
    --   → collapse `simulateQ (simOracle2 …) (roundOracleVerifier.verify …)` to a deterministic
    --     `if sumcheck_check then stmtOutAccept else dummyStmt` (analog of
    --     `BatchingPhase.oracleVerifier_verify_collapse`, which must be BUILT for the 2-message
    --     `Sumcheck.Structured.roundOracleVerifier` — none exists yet) → `split`/`subst` the
    --     singleton support → transport `h_SumcheckStepRelOut`.
    --
    -- TWO WALLS (both shared with the final-sumcheck step; documented to save re-derivation):
    --   (1) INDEX/STRUCTURE MISMATCH (not a pure transport, unlike `BatchingPhase`'s #17). Here the
    --       index-⟨2⟩ KState is `masterKStateProp (stmtIdx := i.castSucc) (stmt := stmtLast)
    --       (localChecks := localizedRoundPolyCheck ∧ nextSumcheckTargetCheck)`, whereas
    --       `relOut = sumcheckRoundRelation … i.succ` is `masterKStateProp (stmtIdx := i.succ)
    --       (stmt := stmtOut)`. Different index AND statement: `h_SumcheckStepRelOut` must be
    --       RECONSTRUCTED into the round-local checks via the round-polynomial algebra (the
    --       `getSumcheckRoundPoly` cube-sum identity + `projectToNextSumcheckPoly` step), NOT
    --       transported verbatim. This is the multi-round analog of `finalSumcheck_cube0_sum_eq`.
    --   (2) ORIENTATION WALL — NOW RESOLVED by the defect-#21 machinery repair. The shared
    --       `Sumcheck.Structured.roundOracleVerifier` now emits `failure` (`guard`) on a failed
    --       sumcheck check (instead of a dummy `{sumcheck_target := 0, challenges := …}`), so the
    --       reject branch has no support element and is vacuous — the dummy can no longer lie in
    --       `relOut`. After the support-extraction front-end collapses the verifier run, the reject
    --       branch closes by `absurd` on the empty support; only the accept branch remains, which is
    --       wall (1).
    -- REMAINING after defect-#21: wall (1) (index/structure reconstruction of the index-⟨2⟩ KState
    -- from `h_SumcheckStepRelOut` via the round-polynomial cube-sum algebra) is independent of the
    -- verifier-failure repair and is still open; it needs the multi-round analog of
    -- `finalSumcheck_cube0_sum_eq` plus the run-shape peel. Left as WIP `sorry`.
    sorry

/-- RBR knowledge soundness for a single round oracle verifier -/
theorem iteratedSumcheckOracleVerifier_rbrKnowledgeSoundness [IsDomain L] (i : Fin ℓ') :
    (iteratedSumcheckOracleVerifier κ L K P ℓ ℓ' aOStmtIn i).rbrKnowledgeSoundness init impl
      (relIn := sumcheckRoundRelation κ L K P ℓ ℓ' h_l aOStmtIn i.castSucc)
      (relOut := sumcheckRoundRelation κ L K P ℓ ℓ' h_l aOStmtIn i.succ)
      (fun j => roundKnowledgeError L ℓ' i) := by
  use fun _ => SumcheckWitness L ℓ' i.castSucc
  use iteratedSumcheckRbrExtractor κ L K P ℓ ℓ' h_l aOStmtIn i
  use iteratedSumcheckKnowledgeStateFunction κ L K P ℓ ℓ' h_l aOStmtIn i
  intro stmtIn witIn prover j
  sorry

end IteratedSumcheckStep

section FinalSumcheckStep
/-!
## Final Sumcheck Step
-/

/-- `pSpecFinalSumcheck L` is a single prover-to-verifier message (no challenge). -/
instance : ProverOnly (pSpecFinalSumcheck L) where
  prover_first' := rfl

/-- The `instDefault` oracle answer is the message itself (`answer m () = m`). -/
@[simp] private lemma answer_instDefault' {M : Type _} (m : M) (q : Unit) :
    @OracleInterface.answer M OracleInterface.instDefault m q = m := rfl

/-- `simulateQ` commutes with `OptionT.pure` (no explicit empty-spec universes). -/
private theorem simulateQ_optionT_pure' {ιₐ ιᵦ : Type} {specₐ : OracleSpec ιₐ}
    {specᵦ : OracleSpec ιᵦ} {γ : Type} (impl : QueryImpl specₐ (OracleComp specᵦ)) (b : γ) :
    simulateQ impl (pure b : OptionT (OracleComp specₐ) γ)
      = (pure b : OptionT (OracleComp specᵦ) γ) := by
  rw [show (pure b : OptionT (OracleComp specₐ) γ) = OptionT.lift (pure b)
        from (OptionT.lift_pure b).symm]
  rw [simulateQ_optionT_lift, simulateQ_pure, OptionT.lift_pure]

/-- The prover for the final sumcheck step -/
noncomputable def finalSumcheckProver :
  OracleProver
    (oSpec := []ₒ)
    (StmtIn := Statement (L := L) (ℓ := ℓ') (RingSwitchingBaseContext κ L K ℓ P) (Fin.last ℓ'))
    (OStmtIn := aOStmtIn.OStmtIn)
    (WitIn := SumcheckWitness L ℓ' (Fin.last ℓ'))
    (StmtOut := MLPEvalStatement L ℓ')
    (OStmtOut := aOStmtIn.OStmtIn)
    (WitOut := WitMLP L ℓ')
    (pSpec := pSpecFinalSumcheck L) where
  PrvState := fun
    | 0 => Statement (L := L) (ℓ := ℓ') (RingSwitchingBaseContext κ L K ℓ P) (Fin.last ℓ')
      × (∀ j, aOStmtIn.OStmtIn j) × SumcheckWitness L ℓ' (Fin.last ℓ')
    | _ => Statement (L := L) (ℓ := ℓ') (RingSwitchingBaseContext κ L K ℓ P) (Fin.last ℓ')
      × (∀ j, aOStmtIn.OStmtIn j) × SumcheckWitness L ℓ' (Fin.last ℓ') × L
  input := fun ⟨⟨stmt, oStmt⟩, wit⟩ => (stmt, oStmt, wit)

  sendMessage
  | ⟨0, _⟩ => fun ⟨stmtIn, oStmtIn, witIn⟩ => do
    let s' : L := witIn.t'.val.eval stmtIn.challenges
    pure ⟨s', (stmtIn, oStmtIn, witIn, s')⟩

  receiveChallenge
  | ⟨0, h⟩ => nomatch h -- No challenges in this step

  output := fun ⟨stmtIn, oStmtIn, witIn, s'⟩ => do
    let stmtOut : MLPEvalStatement L ℓ' := {
      t_eval_point := stmtIn.challenges
      original_claim := s'
    }
    let witOut : WitMLP L ℓ' := {
      t := witIn.t'
    }
    pure (⟨stmtOut, oStmtIn⟩, witOut)

/-- The verifier for the final sumcheck step -/
noncomputable def finalSumcheckVerifier :
  OracleVerifier
    (oSpec := []ₒ)
    (StmtIn := Statement (L := L) (ℓ := ℓ') (RingSwitchingBaseContext κ L K ℓ P) (Fin.last ℓ'))
    (OStmtIn := aOStmtIn.OStmtIn)
    (StmtOut := MLPEvalStatement L ℓ')
    (OStmtOut := aOStmtIn.OStmtIn)
    (pSpec := pSpecFinalSumcheck L) where
  verify := fun stmtIn _ => do
    -- Get the final constant `c` from the prover's message
    let s' : L ← query (spec := [(pSpecFinalSumcheck L).Message]ₒ) ⟨⟨0, rfl⟩, ()⟩

    -- 8. `V` sets `e := eq̃(φ₀(r_κ), ..., φ₀(r_{ℓ-1}), φ₁(r'_0), ..., φ₁(r'_{ℓ'-1}))` and
    -- decomposes `e =: Σ_{u ∈ {0,1}^κ} β_u ⊗ e_u`.
    -- Then `V` computes the final eq value: `(Σ_{u ∈ {0,1}^κ} eq̃(u_0, ..., u_{κ-1},`
      -- `r''_0, ..., r''_{κ-1}) ⋅ e_u)`

    let eq_tilde_eval : L := compute_final_eq_value κ L K P ℓ ℓ' h_l
      stmtIn.ctx.t_eval_point stmtIn.challenges stmtIn.ctx.r_batching

    -- 9. `V` requires `s_{ℓ'} ?= (Σ_{u ∈ {0,1}^κ} eq̃(u_0, ..., u_{κ-1},`
      -- `r''_0, ..., r''_{κ-1}) ⋅ e_u) ⋅ s'`.
    unless stmtIn.sumcheck_target = eq_tilde_eval * s' do
      return { -- dummy stmtOut
        t_eval_point := 0,
        original_claim := 0,
      }

    -- Statement/protocol repair (defect #11): the *forwarded* MLP-evaluation claim is `t'(r') = s'`,
    -- so `original_claim := s'` (with `t_eval_point := r' = challenges`). The eq-scaled value
    -- `eq_tilde_eval * s'` is the verifier's *check* against `sumcheck_target` (step 9, the `unless`
    -- above), NOT the claim it hands to the large-field MLP-eval sub-protocol.
    --
    -- Derivation. The output relation `relOut = aOStmtIn.toRelInput` (`Prelude.toRelInput`/
    -- `MLPEvalRelation`) demands `stmtOut.original_claim = witOut.t.eval stmtOut.t_eval_point`. The
    -- honest prover sets `witOut.t := witIn.t'` and `t_eval_point := challenges`, and by definition
    -- `s' = witIn.t'.eval challenges`. Hence `relOut` holds *iff* `original_claim = s'`; emitting
    -- `eq_tilde_eval * s'` would require `eq_tilde_eval = 1` (false in general — `eq_tilde_eval`
    -- depends on `r, r', r''`), making both `(stmtOut, witOut) ∈ relOut` *and* the prior code's
    -- `prvStmtOut = stmtOut` (the prover already emits `s'`) unsatisfiable. Downstream
    -- `General.lean` consumes exactly this `mlIOPCS.toRelInput`, so `s'` is the contract-correct
    -- forwarded claim. This is the verifier-side of the #8/#10 family of soundness/protocol repairs;
    -- it aligns the verifier's deterministic output to the (already-correct) prover output `s'`.
    let stmtOut : MLPEvalStatement L ℓ' := {
      t_eval_point := stmtIn.challenges
      original_claim := s'
    }
    pure stmtOut

  embed := ⟨fun j => Sum.inl j, fun a b h => by cases h; rfl⟩
  hEq := fun _ => rfl

/-- The oracle reduction for the final sumcheck step -/
noncomputable def finalSumcheckOracleReduction :
  OracleReduction
    (oSpec := []ₒ)
    (StmtIn := Statement (L := L) (ℓ := ℓ') (RingSwitchingBaseContext κ L K ℓ P) (Fin.last ℓ'))
    (OStmtIn := aOStmtIn.OStmtIn)
    (WitIn := SumcheckWitness L ℓ' (Fin.last ℓ'))
    (StmtOut := MLPEvalStatement L ℓ')
    (OStmtOut := aOStmtIn.OStmtIn)
    (WitOut := WitMLP L ℓ')
    (pSpec := pSpecFinalSumcheck L) where
  prover := finalSumcheckProver κ L K P ℓ ℓ' aOStmtIn
  verifier := finalSumcheckVerifier κ L K P ℓ ℓ' h_l aOStmtIn

/-- **Final-sumcheck 0-cube sum identity (shared algebra).** The consistency sum of the projected
last-round polynomial over the 0-cube collapses to `compute_final_eq_value · t'(challenges)`. This is
the pure-algebra core shared by the completeness check (`finalSumcheck_check_of_relIn`) and the
round-by-round KState reconstruction (`finalSumcheckKnowledgeStateFunction.toFun_full`): the
consistency sum is over the 0-cube (`ℓ' - (Fin.last ℓ').val = 0`), collapsing to a single eval;
`fixFirstVariablesOfMQP_eval` rewrites the projected round polynomial evaluated at the empty point to
`(A_MLE · t')(challenges)`; and `A_MLE_eval_eq_compute_final_eq_value` rewrites `A_MLE(challenges) =
compute_final_eq_value`. -/
private lemma finalSumcheck_cube0_sum_eq [IsDomain L] [IsDomain K]
    (stmt : Statement (L := L) (ℓ := ℓ') (RingSwitchingBaseContext κ L K ℓ P) (Fin.last ℓ'))
    (t' : MultilinearPoly L ℓ') :
    (∑ x ∈ (boolDomain L (ℓ' - (Fin.last ℓ').val)).cube,
        (projectToMidSumcheckPoly (L := L) (ℓ := ℓ') (t := t')
          (m := (RingSwitching_SumcheckMultParam κ L K P ℓ ℓ' h_l).multpoly (ctx := stmt.ctx))
          (i := Fin.last ℓ') (challenges := stmt.challenges)).val.eval x)
      = compute_final_eq_value κ L K P ℓ ℓ' h_l stmt.ctx.t_eval_point stmt.challenges
          stmt.ctx.r_batching
        * t'.val.eval stmt.challenges := by
  -- Collapse the cube-0 sum to a single eval at the unique `Fin 0 → L` point.
  have hlast : ℓ' - (Fin.last ℓ').val = 0 := by simp
  haveI : IsEmpty (Fin (ℓ' - (Fin.last ℓ').val)) := by rw [hlast]; exact Fin.isEmpty
  haveI : Subsingleton (Fin (ℓ' - (Fin.last ℓ').val) → L) := inferInstance
  have hmem : (default : Fin (ℓ' - (Fin.last ℓ').val) → L)
      ∈ (boolDomain L (ℓ' - (Fin.last ℓ').val)).cube := by
    rw [SumcheckDomain.cube, Fintype.mem_piFinset]; exact isEmptyElim
  rw [Finset.sum_eq_single_of_mem (default : Fin (ℓ' - (Fin.last ℓ').val) → L) hmem
    (fun b _ hb => absurd (Subsingleton.elim b default) hb)]
  -- Unfold the projected round polynomial and push the eval through `fixFirstVariablesOfMQP`.
  unfold projectToMidSumcheckPoly computeInitialSumcheckPoly
  dsimp only
  rw [fixFirstVariablesOfMQP_eval, MvPolynomial.eval_mul]
  -- The recombined eval point equals `stmt.challenges` (the survivors side is `Fin 0`, empty).
  have hpt : (fun i : Fin ℓ' => Sum.elim (default : Fin (ℓ' - (Fin.last ℓ').val) → L)
        stmt.challenges
        (((finCongr (show ℓ' = ℓ' - (Fin.last ℓ').val + (Fin.last ℓ').val by simp)).trans
          (finSumFinEquiv (m := ℓ' - (Fin.last ℓ').val) (n := (Fin.last ℓ').val)).symm) i))
      = stmt.challenges := by
    funext i
    rw [Equiv.trans_apply]
    rw [show (finCongr (show ℓ' = ℓ' - (Fin.last ℓ').val + (Fin.last ℓ').val by simp)) i
        = Fin.natAdd (ℓ' - (Fin.last ℓ').val) (Fin.cast (by simp [Fin.val_last]) i) by
      apply Fin.ext
      simp only [Fin.val_natAdd, Fin.val_last, Nat.sub_self, Nat.zero_add]
      rfl]
    rw [finSumFinEquiv_symm_apply_natAdd, Sum.elim_inr]
    congr 1
  rw [hpt]
  -- `eval challenges A_MLE = compute_final_eq_value` closes the first factor.
  congr 1
  unfold RingSwitching_SumcheckMultParam
  dsimp only
  exact A_MLE_eval_eq_compute_final_eq_value (κ₀ := κ) (L₀ := L) (K₀ := K) P ℓ ℓ' h_l
    stmt.ctx.t_eval_point stmt.challenges stmt.ctx.r_batching

/-- **Final-sumcheck verifier-check algebra (defect-#10/#11 capstone).** From the input relation's
structural invariant + sumcheck consistency at the last round, the honest verifier's step-9 check
`sumcheck_target = compute_final_eq_value · s'` holds, where `s' = t'(challenges)`.

Derivation (scratch-verified): the consistency sum is over the 0-cube (`ℓ' - (Fin.last ℓ').val = 0`),
collapsing to a single eval; `fixFirstVariablesOfMQP_eval` rewrites the projected round polynomial
`H = projectToMidSumcheckPoly t' A_MLE (Fin.last ℓ') challenges` evaluated at the empty point to
`(A_MLE · t')(challenges)`; and `A_MLE_eval_eq_compute_final_eq_value` rewrites `A_MLE(challenges) =
compute_final_eq_value`. Requires `[IsDomain L] [IsDomain K]` (per the pre-approved statement repair,
in-file precedent on the sibling soundness theorems and the Prelude algebra layer). -/
private lemma finalSumcheck_check_of_relIn [IsDomain L] [IsDomain K]
    (stmt : Statement (L := L) (ℓ := ℓ') (RingSwitchingBaseContext κ L K ℓ P) (Fin.last ℓ'))
    (witIn : SumcheckWitness L ℓ' (Fin.last ℓ'))
    (hStruct : witIn.H = projectToMidSumcheckPoly (L := L) (ℓ := ℓ') (t := witIn.t')
      (m := (RingSwitching_SumcheckMultParam κ L K P ℓ ℓ' h_l).multpoly (ctx := stmt.ctx))
      (i := Fin.last ℓ') (challenges := stmt.challenges))
    (hConsist : sumcheckConsistencyProp (boolDomain L _) stmt.sumcheck_target witIn.H) :
    stmt.sumcheck_target
      = compute_final_eq_value κ L K P ℓ ℓ' h_l stmt.ctx.t_eval_point stmt.challenges
          stmt.ctx.r_batching
        * witIn.t'.val.eval stmt.challenges := by
  unfold sumcheckConsistencyProp at hConsist
  rw [hConsist, hStruct]
  exact finalSumcheck_cube0_sum_eq κ L K P ℓ ℓ' h_l stmt witIn.t'

/-- Perfect completeness for the final sumcheck step -/
theorem finalSumcheckOracleReduction_perfectCompleteness [IsDomain L] [IsDomain K] {σ : Type}
  (init : ProbComp σ)
  (impl : QueryImpl []ₒ (StateT σ ProbComp)) :
  OracleReduction.perfectCompleteness
    (pSpec := pSpecFinalSumcheck L)
    (relIn := sumcheckRoundRelation κ L K P ℓ ℓ' h_l aOStmtIn (Fin.last ℓ'))
    (relOut := aOStmtIn.toRelInput)
    (oracleReduction := finalSumcheckOracleReduction κ L K P ℓ ℓ' h_l aOStmtIn)
      (init := init) (impl := impl) := by
  -- The honest run is fully deterministic (`pSpecFinalSumcheck` = one P→V message, no challenge), so
  -- `Reduction.run_of_prover_first` collapses it; the verifier's single message-oracle query is read
  -- via `simulateQ_simOracle2_query` and the step-9 check passes by `finalSumcheck_check_of_relIn`.
  unfold OracleReduction.perfectCompleteness
  simp only [Reduction.perfectCompleteness, Reduction.completeness, ENNReal.coe_zero, tsub_zero]
  intro ⟨stmtIn, oStmtIn⟩ witIn h_relIn
  -- (1) ALGEBRA: from the input relation, the verifier's step-9 check passes.
  simp only [sumcheckRoundRelation, sumcheckRoundRelationProp, masterKStateProp,
    witnessStructuralInvariant, Set.mem_setOf_eq, true_and] at h_relIn
  obtain ⟨hStruct, hConsist, hCompat⟩ := h_relIn
  have hcheck : stmtIn.sumcheck_target
      = compute_final_eq_value κ L K P ℓ ℓ' h_l stmtIn.ctx.t_eval_point stmtIn.challenges
          stmtIn.ctx.r_batching * (MvPolynomial.eval stmtIn.challenges) witIn.t'.val :=
    finalSumcheck_check_of_relIn κ L K P ℓ ℓ' h_l stmtIn witIn hStruct hConsist
  -- (2) PLUMBING: resolve the deterministic run and the verifier's message-query collapse.
  rw [Reduction.run_of_prover_first]
  simp only [finalSumcheckOracleReduction, OracleReduction.toReduction, finalSumcheckProver,
    finalSumcheckVerifier, OracleVerifier.toVerifier, liftM, monadLift, MonadLiftT.monadLift,
    MonadLift.monadLift, pure_bind, bind_pure_comp]
  simp only [simulateQ_optionT_lift, simulateQ_pure, OptionT.lift_pure, pure_bind, OptionT.run_mk,
    bind_pure_comp, OptionT.run_lift, simulateQ_map, OptionT.run_bind, Option.elimM,
    map_pure, Option.elim_some, Option.elim_none, OptionT.run_pure]
  -- Collapse the inner verifier query (`s' = msgs ⟨0,_⟩ = eval challenges t'`).
  rw [simulateQ_optionT_bind, simulateQ_simOracle2_query]
  simp only [OptionT.lift_pure, pure_bind, FullTranscript.messages, apply_ite,
    simulateQ_optionT_lift, simulateQ_pure, OptionT.run_pure, OptionT.run_lift]
  erw [pure_bind]
  simp only [answer_instDefault', apply_ite, simulateQ_optionT_pure']
  rw [if_pos hcheck]
  simp only [map_pure, simulateQ_pure, Option.elimM, bind_pure_comp, Option.elim_some,
    Option.elim_none, StateT.run'_eq, OptionT.run_pure, Option.getM, pure_bind, Option.elim,
    StateT.run_map, StateT.run_pure, Option.map_some, Functor.map_map, Function.comp]
  rw [ge_iff_le, one_le_probEvent_iff, probEvent_eq_one_iff]
  refine ⟨?_, ?_⟩
  · -- No failure: the deterministic computation always produces `some`.
    rw [OptionT.probFailure_eq, OptionT.run_mk]
    simp only [probFailure_map, probFailure_eq_zero, zero_add]
    apply probOutput_eq_zero_of_not_mem_support
    simp only [support_map, Set.mem_image, not_exists, not_and]
    intro a _ h
    exact absurd h.symm (by simp)
  · -- Every output satisfies the event (relOut = toRelInput, and prvStmtOut = stmtOut).
    intro x hx
    rw [OptionT.mem_support_iff, OptionT.run_mk] at hx
    simp only [support_map, Set.mem_image] at hx
    obtain ⟨a, _, heq⟩ := hx
    rw [Option.some_inj] at heq
    subst heq
    refine ⟨?_, rfl⟩
    -- `(stmtOut, witOut) ∈ toRelInput`: MLPEvalRelation (`s' = t'(challenges)`) + initialCompatibility.
    simp only [AbstractOStmtIn.toRelInput, MLPEvalRelation, Set.mem_setOf_eq]
    exact ⟨rfl, hCompat⟩

/-- RBR knowledge error for the final sumcheck step -/
def finalSumcheckRbrKnowledgeError : ℝ≥0 := (1 : ℝ≥0) / (Fintype.card L)

/-- The round-by-round extractor for the final sumcheck step -/
noncomputable def finalSumcheckRbrExtractor :
  Extractor.RoundByRound []ₒ
    (StmtIn := Statement (L := L) (ℓ := ℓ') (RingSwitchingBaseContext κ L K ℓ P) (Fin.last ℓ')
      × (∀ j, aOStmtIn.OStmtIn j))
    (WitIn := SumcheckWitness L ℓ' (Fin.last ℓ'))
    (WitOut := WitMLP L ℓ')
    (pSpec := pSpecFinalSumcheck L)
    (WitMid := fun _m => SumcheckWitness L ℓ' (Fin.last ℓ')) where
  eqIn := rfl
  extractMid := fun _m ⟨_, _⟩ _trSucc witMidSucc => witMidSucc

  extractOut := fun ⟨stmtIn, _⟩ _tr witOut => {
    t' := witOut.t,
    H := projectToMidSumcheckPoly (L := L) (ℓ := ℓ') (t := witOut.t)
      (m := (RingSwitching_SumcheckMultParam κ L K P ℓ ℓ' h_l).multpoly (ctx := stmtIn.ctx))
      (i := Fin.last ℓ') (challenges := stmtIn.challenges)
  }

/- This follows the KState of `finalSumcheckKStateProp` in `BinaryBasefold`.
though the multiplier poly is different. -/
def finalSumcheckKStateProp {m : Fin (1 + 1)} (tr : Transcript m (pSpecFinalSumcheck L))
    (stmt : Statement (L := L) (ℓ := ℓ') (RingSwitchingBaseContext κ L K ℓ P) (Fin.last ℓ'))
    (witMid : SumcheckWitness L ℓ' (Fin.last ℓ'))
    (oStmt : ∀ j, aOStmtIn.OStmtIn j) : Prop :=
  match m with
  | ⟨0, _⟩ => -- same as relIn
    RingSwitching.masterKStateProp κ L K P ℓ ℓ' h_l aOStmtIn
      (stmtIdx := Fin.last ℓ')
      (stmt := stmt) (oStmt := oStmt) (wit := witMid)
      (localChecks := True)
  | ⟨1, _⟩ => -- implied by relOut + local checks via extractOut proofs
    let tr_so_far := (pSpecFinalSumcheck L).take 1 (by omega)
    let i_msg0 : tr_so_far.MessageIdx := ⟨⟨0, by omega⟩, rfl⟩
    let c : L := (ProtocolSpec.Transcript.equivMessagesChallenges (k := 1)
      (pSpec := pSpecFinalSumcheck L) tr).1 i_msg0

    let stmtOut : MLPEvalStatement L ℓ' := {
      t_eval_point := stmt.challenges,
      original_claim := c
    }
    let sumcheckFinalLocalCheck : Prop :=
      let eq_tilde_eval : L := compute_final_eq_value κ L K P ℓ ℓ' h_l
        stmt.ctx.t_eval_point stmt.challenges stmt.ctx.r_batching
      stmt.sumcheck_target = eq_tilde_eval * c

    let final_eval : Prop := witMid.t'.val.eval stmt.challenges = c
    -- The KState at the last index carries the *full* `masterKStateProp` (structural invariant +
    -- sumcheck consistency + initial compatibility) on top of the round-local checks. This is what
    -- makes `toFun_next` (recovering the index-0 `masterKStateProp` from the index-1 KState with the
    -- same `witMid`) provable: the index-0 prop requires `witnessStructuralInvariant` and
    -- `sumcheckConsistencyProp`, which would be unrecoverable from the bare local checks alone.
    RingSwitching.masterKStateProp κ L K P ℓ ℓ' h_l aOStmtIn
      (stmtIdx := Fin.last ℓ')
      (stmt := stmt) (oStmt := oStmt) (wit := witMid)
      (localChecks := sumcheckFinalLocalCheck ∧ final_eval)

/-- The knowledge state function for the final sumcheck step -/
noncomputable def finalSumcheckKnowledgeStateFunction [IsDomain L] [IsDomain K] {σ : Type}
    (init : ProbComp σ)
    (impl : QueryImpl []ₒ (StateT σ ProbComp)) :
    (finalSumcheckVerifier κ L K P ℓ ℓ' h_l aOStmtIn).KnowledgeStateFunction init impl
    (relIn := sumcheckRoundRelation κ L K P ℓ ℓ' h_l aOStmtIn (Fin.last ℓ'))
    (relOut := aOStmtIn.toRelInput)
    (extractor := finalSumcheckRbrExtractor κ L K P ℓ ℓ' h_l aOStmtIn)
  where
  toFun := fun m ⟨stmt, oStmt⟩ tr witMid =>
    finalSumcheckKStateProp κ L K P ℓ ℓ' h_l 
    (m := m) (tr := tr) (stmt := stmt) (witMid := witMid) (oStmt := oStmt)
  toFun_empty := fun stmt witMid => by
    simp only [sumcheckRoundRelation, sumcheckRoundRelationProp, Fin.val_last, cast_eq,
      Set.mem_setOf_eq, finalSumcheckKStateProp, masterKStateProp, true_and]
  toFun_next := fun m hDir stmt tr msg witMid h => by
    obtain ⟨stmt, oStmt⟩ := stmt
    fin_cases m
    -- `m.succ = ⟨1, _⟩` (the last index): `h` is the full `masterKStateProp` with the round-local
    -- checks. `m.castSucc = ⟨0, _⟩`: the goal is the same `masterKStateProp` with
    -- `localChecks := True`. `extractMid` returns `witMid` unchanged, so we drop the local checks.
    simp only [finalSumcheckKStateProp, masterKStateProp, true_and] at h ⊢
    exact ⟨h.2.1, h.2.2.1, h.2.2.2⟩
  toFun_full := fun stmt tr witOut h => by
    obtain ⟨stmt, oStmt⟩ := stmt
    -- Abbreviate the message the prover sent (the single P→V message of `pSpecFinalSumcheck`),
    -- matching the `equivMessagesChallenges` form used by `finalSumcheckKStateProp` at index `⟨1,_⟩`.
    set c : L := (ProtocolSpec.Transcript.equivMessagesChallenges (k := 1)
      (pSpec := pSpecFinalSumcheck L) tr).1 ⟨⟨0, Nat.zero_lt_one⟩, rfl⟩ with hc
    -- The message extracted by `equivMessagesChallenges` is just the transcript at index 0; the
    -- verifier run below reads `tr 0` directly, so pin this identity once and reuse it.
    have hc0 : c = tr (0 : Fin 1) := rfl
    -- (A) SUPPORT EXTRACTION: turn the `> 0` probability into a support element, then collapse the
    -- deterministic verifier run via the same `simulateQ_simOracle2_query` chain as completeness.
    rw [gt_iff_lt, probEvent_pos_iff] at h
    obtain ⟨⟨stmtOut, oStmtOut⟩, hx, hrel⟩ := h
    rw [OptionT.mem_support_iff] at hx
    simp only [OptionT.run_mk, support_bind, Set.mem_iUnion] at hx
    obtain ⟨s, _, hx⟩ := hx
    -- Collapse the inner verifier-run (`simulateQ (simOracle2 ...) (verify ...)`) to the closed `if`
    -- form, mirroring the completeness chain (`simulateQ_simOracle2_query` + `answer_instDefault'`).
    simp only [finalSumcheckVerifier, OracleVerifier.toVerifier, Verifier.run,
      bind_pure_comp] at hx
    rw [simulateQ_optionT_bind, simulateQ_simOracle2_query] at hx
    simp only [OptionT.lift_pure, FullTranscript.messages, apply_ite,
      simulateQ_optionT_lift, simulateQ_pure, OptionT.run_pure, OptionT.run_lift,
      answer_instDefault', simulateQ_optionT_pure', simulateQ_map, map_pure] at hx
    erw [pure_bind] at hx
    -- Rewrite the run's `tr 0` to the `equivMessagesChallenges` message `c` so the case split and the
    -- final KState reconstruction speak the same language. `hc0 : c = tr 0` is definitional.
    rw [show (tr (0 : Fin 1) : L) = c from hc0.symm] at hx
    -- (B) CASE SPLIT on the verifier's step-9 accept condition.
    by_cases hcheck : stmt.sumcheck_target
        = compute_final_eq_value κ L K P ℓ ℓ' h_l stmt.ctx.t_eval_point stmt.challenges
            stmt.ctx.r_batching * c
    · -- ACCEPT branch: the verifier outputs `stmtOut = {t_eval_point := challenges, original_claim
      -- := c}`; pin it from the support element.
      rw [if_pos hcheck] at hx
      -- The post-`if` run is `simulateQ impl (pure (stmtOut₀, oStmt))` with
      -- `stmtOut₀ = {t_eval_point := challenges, original_claim := c}`; its `run' s` support is the
      -- singleton `{some (stmtOut₀, oStmt)}`, so the support element pins `stmtOut = stmtOut₀`.
      simp only [map_pure, simulateQ_pure, StateT.run'_eq, StateT.run_pure, support_pure,
        Set.mem_singleton_iff, Option.some.injEq, Prod.mk.injEq] at hx
      obtain ⟨rfl, -⟩ := hx
      -- (C) ALGEBRA + KState reconstruction.
      -- `hrel` : `(stmtOut, witOut) ∈ toRelInput`, i.e. MLPEvalRelation + initialCompatibility.
      simp only [AbstractOStmtIn.toRelInput, MLPEvalRelation, Set.mem_setOf_eq] at hrel
      obtain ⟨hEval, hCompat⟩ := hrel
      -- `hEval : stmtOut.original_claim = witOut.t.eval stmtOut.t_eval_point`, with
      -- `stmtOut.original_claim = c` and `stmtOut.t_eval_point = stmt.challenges`.
      -- Now build the KState at the last index `⟨1,_⟩`.
      -- The KState index is `Fin.last 1 = ⟨1, _⟩` (the protocol's single, last message round); reduce
      -- the `match` to that branch before splitting into the four KState conjuncts.
      simp only [finalSumcheckKStateProp, masterKStateProp, witnessStructuralInvariant,
        finalSumcheckRbrExtractor, Fin.last, Fin.isValue, true_and]
      refine ⟨⟨?_, ?_⟩, ?_, ?_⟩
      · -- `sumcheckFinalLocalCheck`: `sumcheck_target = compute_final_eq_value · c`. `c` is the local
        -- abbreviation of the transcript message, exactly what `hcheck` states.
        exact hcheck
      · -- `final_eval`: `(MvPolynomial.eval challenges) witOut.t = c`, i.e. `hEval.symm`.
        exact hEval.symm
      · -- `sumcheckConsistencyProp`: `sumcheck_target = ∑_{0-cube} (projectToMidSumcheckPoly …).eval`.
        -- The 0-cube sum equals `compute_final_eq_value · witOut.t(challenges)` by the shared algebra
        -- lemma; `hcheck` (= `sumcheck_target = compute_final_eq_value · c`) and
        -- `hEval` (= `c = witOut.t(challenges)`) close it.
        unfold sumcheckConsistencyProp
        rw [hcheck, hEval]
        exact (finalSumcheck_cube0_sum_eq κ L K P ℓ ℓ' h_l stmt witOut.t).symm
      · -- `initialCompatibility ⟨witOut.t, oStmt⟩`.
        exact hCompat
    · -- REJECT branch: verifier returns the dummy `{t_eval_point := 0, original_claim := 0}`. The
      -- support element pins `stmtOut` to that dummy.
      rw [if_neg hcheck] at hx
      simp only [map_pure, simulateQ_pure, StateT.run'_eq, StateT.run_pure, support_pure,
        Set.mem_singleton_iff, Option.some.injEq, Prod.mk.injEq] at hx
      obtain ⟨rfl, -⟩ := hx
      -- ORIENTATION WALL (analog of the round-2 KState/failureState question flagged in
      -- `BatchingPhase`). After the dummy is pinned, the hypotheses are:
      --   `hcheck : ¬(sumcheck_target = compute_final_eq_value · c)`   (the verifier's check FAILED)
      --   `hrel   : ({0,0}, witOut) ∈ toRelInput`, i.e. `0 = witOut.t.eval 0 ∧ initialCompatibility`
      -- while the goal (the index-1 KState) REQUIRES `sumcheckFinalLocalCheck`, i.e. exactly
      -- `sumcheck_target = compute_final_eq_value · c` — which `hcheck` negates. So the reject branch
      -- is genuinely UNREACHABLE-as-vacuous only if the dummy cannot lie in `relOut`; but the dummy
      -- `{0,0}` IS in `relOut` whenever `witOut.t.eval 0 = 0` (a coincidence the prover can force).
      --
      -- ROOT CAUSE (verifier design, not a proof gap): `finalSumcheckVerifier` returns a *dummy
      -- statement* on a failed check (`unless … do return {0,0}`), whereas the round-by-round
      -- knowledge-soundness contract (and the `Sumcheck/Spec/SingleRound` template) requires the
      -- verifier to emit `failure` (`guard`/`OptionT` `none`) on a failed check, which makes the
      -- reject branch vacuous (no support element). The documented repair is to switch the reject to
      -- `failure`; this does not touch completeness (which only exercises the accept branch via
      -- `if_pos`). Deferred to keep this commit's accept-branch closure isolated and reviewable.
      sorry

/-- Round-by-round knowledge soundness for the final sumcheck step -/
theorem finalSumcheckOracleVerifier_rbrKnowledgeSoundness [Fintype L] [IsDomain L] [IsDomain K]
    {σ : Type}
    (init : ProbComp σ) (impl : QueryImpl []ₒ (StateT σ ProbComp)) :
    (finalSumcheckVerifier κ L K P ℓ ℓ' h_l aOStmtIn).rbrKnowledgeSoundness init impl
      (relIn := sumcheckRoundRelation κ L K P ℓ ℓ' h_l aOStmtIn (Fin.last ℓ'))
      (relOut := aOStmtIn.toRelInput)
      (rbrKnowledgeError := fun _ => finalSumcheckRbrKnowledgeError (L := L)) := by
  use (fun _ => SumcheckWitness L ℓ' (Fin.last ℓ'))
  use finalSumcheckRbrExtractor κ L K P ℓ ℓ' h_l aOStmtIn
  use finalSumcheckKnowledgeStateFunction κ L K P ℓ ℓ' h_l aOStmtIn init impl
  intro stmtIn witIn prover j
  -- `pSpecFinalSumcheck L` has a single `P_to_V` message and no challenges, so the
  -- challenge index `j` is vacuous: its defining proof `j.2 : dir j.1 = V_to_P` is absurd.
  exact absurd j.2 (by simp [pSpecFinalSumcheck])

end FinalSumcheckStep

section LargeFieldReduction

/-- Composed oracle verifier for the SumcheckStep (seqCompose over ℓ') -/
@[reducible]
def sumcheckLoopOracleVerifier :=
  OracleVerifier.seqCompose (m := ℓ') (oSpec := []ₒ)
    (pSpec := fun _ => pSpecSumcheckRound L)
    (OStmt := fun _ => aOStmtIn.OStmtIn)
    (Stmt := Statement (L := L) (ℓ := ℓ') (RingSwitchingBaseContext κ L K ℓ P))
    (V := fun (i: Fin ℓ') => iteratedSumcheckOracleVerifier κ L K P ℓ ℓ' aOStmtIn i)

/-- Composed oracle reduction for the SumcheckStep (seqCompose over ℓ') -/
@[reducible]
def sumcheckLoopOracleReduction :
  OracleReduction (oSpec := []ₒ)
    (StmtIn := Statement (L := L) (ℓ := ℓ') (RingSwitchingBaseContext κ L K ℓ P) 0)
    (OStmtIn := aOStmtIn.OStmtIn)
    (StmtOut := Statement (L := L) (ℓ := ℓ') (RingSwitchingBaseContext κ L K ℓ P) (Fin.last ℓ'))
    (OStmtOut := aOStmtIn.OStmtIn)
    (pSpec := pSpecSumcheckLoop L ℓ')
    (WitIn := SumcheckWitness L ℓ' 0)
    (WitOut := SumcheckWitness L ℓ' (Fin.last ℓ')) :=
  OracleReduction.seqCompose (m:=ℓ') (oSpec:=[]ₒ)
    (OStmt := fun _ => aOStmtIn.OStmtIn)
    (Stmt := Statement (L := L) (ℓ := ℓ') (RingSwitchingBaseContext κ L K ℓ P))
    (Wit := fun i => SumcheckWitness L ℓ' i)
    (R := fun (i: Fin ℓ') => iteratedSumcheckOracleReduction κ L K P ℓ ℓ' aOStmtIn i)

/-- Large-field reduction verifier: Sumcheck seqCompose, then append FinalSum -/
@[reducible]
def coreInteractionOracleVerifier :=
  OracleVerifier.append (oSpec:=[]ₒ)
    (V₁:=sumcheckLoopOracleVerifier κ L K P ℓ ℓ' aOStmtIn)
    (pSpec₁:=pSpecSumcheckLoop L ℓ')
    (V₂:=finalSumcheckVerifier κ L K P ℓ ℓ' h_l aOStmtIn)
    (pSpec₂:=pSpecFinalSumcheck L)

/-- Large-field reduction: Sumcheck seqCompose, then append FinalSum -/
@[reducible]
def coreInteractionOracleReduction :=
  OracleReduction.append
    (R₁ := sumcheckLoopOracleReduction κ L K P ℓ ℓ' aOStmtIn)
    (pSpec₁:=pSpecSumcheckLoop L ℓ')
    (R₂ := finalSumcheckOracleReduction κ L K P ℓ ℓ' h_l aOStmtIn)
    (pSpec₂:=pSpecFinalSumcheck L)

/-!
## RBR Knowledge Soundness Components for Single Round
-/

variable {σ : Type} {init : ProbComp σ} {impl : QueryImpl []ₒ (StateT σ ProbComp)}

/-- Perfect completeness for large-field reduction (Sumcheck ++ FinalSum) -/
theorem coreInteraction_perfectCompleteness [IsDomain L] [IsDomain K] :
  OracleReduction.perfectCompleteness
    (oracleReduction := coreInteractionOracleReduction κ L K P ℓ ℓ' h_l aOStmtIn)
    (StmtIn := Statement (L := L) (ℓ := ℓ') (RingSwitchingBaseContext κ L K ℓ P) 0)
    (OStmtIn := aOStmtIn.OStmtIn)
    (StmtOut := MLPEvalStatement L ℓ')
    (OStmtOut := aOStmtIn.OStmtIn)
    (WitIn := SumcheckWitness L ℓ' 0)
    (WitOut := WitMLP L ℓ')
    (relIn := sumcheckRoundRelation κ L K P ℓ ℓ' h_l aOStmtIn 0)
    (relOut := aOStmtIn.toRelInput)
    (init := init)
    (impl := impl) := by
  -- Follows from append_perfectCompleteness of interactionPhase and finalSumcheck
  apply OracleReduction.append_perfectCompleteness
  · apply OracleReduction.seqCompose_perfectCompleteness
      (rel := fun i => sumcheckRoundRelation κ L K P ℓ ℓ' h_l aOStmtIn i)
      (R := fun i => iteratedSumcheckOracleReduction κ L K P ℓ ℓ' aOStmtIn i)
      (h := fun i =>
        iteratedSumcheckOracleReduction_perfectCompleteness (κ:=κ) (L:=L) (K:=K)
          (P:=P) (ℓ:=ℓ) (ℓ':=ℓ') (h_l:=h_l) (aOStmtIn:=aOStmtIn)
          (init:=init) (impl:=impl) i
      )
  · exact finalSumcheckOracleReduction_perfectCompleteness (κ:=κ) (L:=L) (K:=K)
      (P:=P) (ℓ:=ℓ) (ℓ':=ℓ') (h_l:=h_l) (aOStmtIn:=aOStmtIn) (init:=init) (impl:=impl)

/-- Per-round knowledge error for the iterated sumcheck rounds. -/
def iteratedSumcheckRoundKnowledgeError (_ : Fin ℓ') : ℝ≥0 := (2 : ℝ≥0) / (Fintype.card L)

/-- standard sumcheck error -/
def coreInteractionRbrKnowledgeError (j : (pSpecCoreInteraction L ℓ').ChallengeIdx) : ℝ≥0 :=
  Sum.elim
    (f := fun i =>
      letI ij := seqComposeChallengeIdxToSigma i
      iteratedSumcheckRoundKnowledgeError L ℓ' ij.1)
    (g := fun _ => finalSumcheckRbrKnowledgeError (L := L))
    (ChallengeIdx.sumEquiv.symm j)

-- TODO: iteratedSumcheckLoop_rbrKnowledgeSoundness

/-- RBR knowledge soundness for large-field reduction (Sumcheck ++ FinalSum) -/
theorem coreInteraction_rbrKnowledgeSoundness [IsDomain L] [IsDomain K] :
  OracleVerifier.rbrKnowledgeSoundness
    (verifier := coreInteractionOracleVerifier κ L K P ℓ ℓ' h_l aOStmtIn)
    (StmtIn := Statement (L := L) (ℓ := ℓ') (RingSwitchingBaseContext κ L K ℓ P) 0)
    (OStmtIn := aOStmtIn.OStmtIn)
    (StmtOut := MLPEvalStatement L ℓ')
    (OStmtOut := aOStmtIn.OStmtIn)
    (WitIn := SumcheckWitness L ℓ' 0)
    (WitOut := WitMLP L ℓ')
    (init := init)
    (impl := impl)
    (relIn := sumcheckRoundRelation κ L K P ℓ ℓ' h_l aOStmtIn 0)
    (relOut := aOStmtIn.toRelInput)
    (rbrKnowledgeError := coreInteractionRbrKnowledgeError (L:=L) (ℓ':=ℓ')) := by
  apply OracleVerifier.append_rbrKnowledgeSoundness
    (init := init) (impl := impl)
    (rel₁ := sumcheckRoundRelation κ L K P ℓ ℓ' h_l aOStmtIn 0)
    (rel₂ := sumcheckRoundRelation κ L K P ℓ ℓ' h_l aOStmtIn (Fin.last ℓ'))
    (rel₃ := aOStmtIn.toRelInput)
    (V₁ := sumcheckLoopOracleVerifier κ L K P ℓ ℓ' aOStmtIn)
    (V₂ := finalSumcheckVerifier κ L K P ℓ ℓ' h_l aOStmtIn)
    (Oₛ₃ := by exact fun _ => OracleInterface.instDefault)
    (rbrKnowledgeError₁ := fun i =>
      letI ij := seqComposeChallengeIdxToSigma i
      iteratedSumcheckRoundKnowledgeError L ℓ' ij.1)
    (rbrKnowledgeError₂ := fun _ => finalSumcheckRbrKnowledgeError (L := L))
    (h₁ := by
      apply OracleVerifier.seqCompose_rbrKnowledgeSoundness
        (rel := fun i => sumcheckRoundRelation κ L K P ℓ ℓ' h_l aOStmtIn i)
        (V := fun i => iteratedSumcheckOracleVerifier κ L K P ℓ ℓ' aOStmtIn i)
        (rbrKnowledgeError := fun i _ => iteratedSumcheckRoundKnowledgeError L ℓ' i)
        (h := fun i =>
          iteratedSumcheckOracleVerifier_rbrKnowledgeSoundness (κ:=κ) (L:=L) (K:=K)
            (P:=P) (ℓ:=ℓ) (ℓ':=ℓ') (h_l:=h_l) (aOStmtIn:=aOStmtIn)
            (init:=init) (impl:=impl) i))
    (h₂ := by
      apply finalSumcheckOracleVerifier_rbrKnowledgeSoundness (κ:=κ) (L:=L) (K:=K)
        (P:=P) (ℓ:=ℓ) (ℓ':=ℓ') (h_l:=h_l) (aOStmtIn:=aOStmtIn)
        (init:=init) (impl:=impl))

end LargeFieldReduction
end
end RingSwitching.SumcheckPhase

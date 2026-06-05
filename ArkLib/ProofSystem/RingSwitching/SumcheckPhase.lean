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

/-! ## Shared `simulateQ`/`OptionT` collapse helpers

These small `rfl`/`OptionT.ext` lemmas are used by both the iterated-round and final-sumcheck
verifier-run collapses (the `toFun_full` support extractions and the completeness peel). They are
hoisted above both sections so the defect-#21 vacuous-REJECT discharge can reuse them. -/

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

/-- `simulateQ` commutes with `OptionT` `failure`, for an arbitrary lawful target monad `m` (so it
applies to both the inner `OracleComp`-valued and outer `StateT`-valued simulation passes).
Companion to `simulateQ_optionT_pure'`; discharges the defect-#21 vacuous REJECT branches. -/
private theorem simulateQ_optionT_failure' {ιₐ : Type} {specₐ : OracleSpec ιₐ}
    {m : Type → Type} [Monad m] [LawfulMonad m] {γ : Type} (impl : QueryImpl specₐ m) :
    simulateQ impl (failure : OptionT (OracleComp specₐ) γ) = (failure : OptionT m γ) := by
  rw [OracleComp.failure_def]
  apply OptionT.ext
  simp only [OptionT.run_mk, simulateQ_pure, OptionT.fail]
  rfl

/-- A map over `OptionT` `failure` is `failure`. -/
private theorem map_optionT_failure' {ιₐ : Type} {specₐ : OracleSpec ιₐ} {γ δ : Type}
    (f : γ → δ) :
    (f <$> (failure : OptionT (OracleComp specₐ) γ))
      = (failure : OptionT (OracleComp specₐ) δ) := by
  apply OptionT.ext
  rw [OptionT.run_map]
  show Option.map f <$> (pure none : OracleComp specₐ (Option γ))
    = (pure none : OracleComp specₐ (Option δ))
  rw [map_pure]
  rfl

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

/-- **Round-transition consistency (next-round cube form, defect-#20 last-variable).** The prover's
round univariate `getSumcheckRoundPoly i (projectToMidSumcheckPoly … i.castSucc challenges)`
evaluated at the verifier challenge `r'` equals the *next* round's cube sum of the advanced projected
polynomial `projectToMidSumcheckPoly … i.succ (Fin.cons r' challenges)`. This is the multi-round
analog of `finalSumcheck_cube0_sum_eq`: it relates `h_star.eval r'` (the next-round target produced
by the honest verifier) to `∑_cube witOut.H` (the next-round sumcheck consistency), and is the
load-bearing identity for the iterated KState's `nextSumcheckTargetCheck` reconstruction.

Derivation: `getSumcheckRoundPoly_eval_eq_sum_snoc` rewrites the LHS as a survivor-cube sum of the
round polynomial `H = projectToMid … i.castSucc challenges` with the *last* surviving variable fixed
to `r'` (via `Fin.snoc`); `fixFirstVariablesOfMQP_eval` (with `v := 1`) identifies that snoc-eval with
the survivor-eval of `fixFirstVariablesOfMQP (ℓ'-i.castSucc) ⟨1⟩ H {r'}`; the round-transition
`fixFirstVariablesOfMQP_projectToMid_step` rewrites that fixed-last poly as `rename (finCongr)
(projectToMid … i.succ (cons r' challenges)) = rename (finCongr) witOut.H`; finally `eval_rename` +
a `Fin.cast` reindex of the (uniform Boolean) survivor cube collapse the rename to the next-round
cube sum. -/
theorem getSumcheckRoundPoly_eval_eq_cube_succ (i : Fin ℓ')
    (t m : MultilinearPoly L ℓ') (challenges : Fin i.castSucc → L) (r' : L) :
    (getSumcheckRoundPoly ℓ' (boolDomain L ℓ') (i := i)
        (projectToMidSumcheckPoly (L := L) (ℓ := ℓ') (t := t) (m := m)
          (i := i.castSucc) (challenges := challenges))).val.eval r'
      = ∑ z ∈ (boolDomain L (ℓ' - ↑i.succ)).cube,
          (projectToMidSumcheckPoly (L := L) (ℓ := ℓ') (t := t) (m := m)
            (i := i.succ) (challenges := Fin.cons r' challenges)).val.eval z := by
  -- Abbreviate `H := witLast.H = projectToMid … i.castSucc challenges`.
  set H : L⦃≤ 2⦄[X Fin (ℓ' - ↑i.castSucc)] :=
    projectToMidSumcheckPoly (L := L) (ℓ := ℓ') (t := t) (m := m)
      (i := i.castSucc) (challenges := challenges) with hHdef
  -- `ℓ' - i.castSucc = (ℓ'-i.castSucc-1) + 1` from `i.isLt`.
  have hn : ℓ' - ↑i.castSucc = (ℓ' - ↑i.castSucc - 1) + 1 := by
    have := i.2; simp only [Fin.val_castSucc]; omega
  set curH : L[X Fin ((ℓ' - ↑i.castSucc - 1) + 1)] := rename (finCongr hn) H.val with hcurH_def
  have hHEq : HEq curH H.val := by
    rw [hcurH_def]; exact rename_finCongr_heq (h := hn) (p := H.val)
  -- (1) LHS: round univariate value as a survivor-cube snoc-sum (last-variable form).
  rw [getSumcheckRoundPoly_eval_eq_sum_snoc (i := i) (H := H) (r' := r') (curH := curH)
    (hcurH := hHEq)]
  -- (2) Rewrite each snoc-eval of `curH` back to an eval of `H` (via `eval_rename`), then to the
  -- survivor-eval of the *fixed-last* `H` (via `fixFirstVariablesOfMQP_eval` with `v := 1`).
  have hpos : 0 < ℓ' - ↑i.castSucc := by have := i.2; simp only [Fin.val_castSucc]; omega
  set v1 : Fin (ℓ' - ↑i.castSucc + 1) := ⟨1, by omega⟩ with hv1
  -- Survivor point of `fixFirstVariablesOfMQP _ v1` lives over `Fin ((ℓ'-i.castSucc) - v1)`; with
  -- `v1 = 1` this is the same dimension `ℓ'-i.castSucc-1` as the `curH` survivors.
  have hfix : ∀ x : Fin (ℓ' - (↑i.castSucc + 1)) → L,
      MvPolynomial.eval
          (Fin.snoc (Fin.append x (fun j => j.elim0) ∘ Fin.cast (by omega)) r') curH
        = MvPolynomial.eval
            (fun k : Fin ((ℓ' - ↑i.castSucc) - ↑v1) =>
              (Fin.append x (fun j => j.elim0) ∘ Fin.cast (by simp only [hv1]; omega)) k)
            (fixFirstVariablesOfMQP (ℓ' - ↑i.castSucc) v1 H.val (fun _ => r')) := by
    intro x
    -- `fixFirstVariablesOfMQP_eval` (v := v1): `eval y (fix-last H {r'}) = eval (recombine y {r'}) H`.
    rw [RingSwitching.fixFirstVariablesOfMQP_eval (L := L) (ℓ := ℓ' - ↑i.castSucc)
        v1 H.val (fun _ => r')
        (fun k : Fin ((ℓ' - ↑i.castSucc) - ↑v1) =>
          (Fin.append x (fun j => j.elim0) ∘ Fin.cast (by simp only [hv1]; omega)) k)]
    -- Both sides are `eval (·) H.val`; transport the snoc-eval of `curH` to `H` via `eval_rename`.
    rw [hcurH_def, eval_rename]
    refine congrArg (fun pt => MvPolynomial.eval pt H.val) ?_
    -- The recombined points agree coordinatewise: the survivors come from `x` and the single fixed
    -- coordinate is `r'`, in both the `Fin.snoc … r' ∘ finCongr` and the `Sum.elim … {r'}` forms.
    funext j
    -- LHS (after `eval_rename`): `(Fin.snoc … r') (Fin.cast hn j)`, `Fin.cast hn j : Fin (…-1+1)`.
    -- RHS (`fixFirstVariablesOfMQP_eval` recombine): classify `j` by the `finSumFinEquiv` split
    -- (`finSumFinEquiv_symm_dite`: split on `j < (ℓ'-i.castSucc) - v1`).
    simp only [Function.comp_apply, Equiv.trans_apply, finCongr_apply,
      RingSwitching.finSumFinEquiv_symm_dite, Fin.val_cast]
    by_cases hj : (j : ℕ) < ℓ' - ↑i.castSucc - 1
    · -- survivor coordinate: both sides read `x` at the matching index.
      rw [dif_pos (show (j : ℕ) < (ℓ' - ↑i.castSucc) - ↑v1 by simp only [hv1]; omega), Sum.elim_inl]
      simp only [show (Fin.cast hn j) = Fin.castSucc ⟨(j : ℕ), by omega⟩ from Fin.ext rfl,
        Fin.snoc_castSucc, Function.comp_apply, Fin.val_cast]
    · -- fixed coordinate (`j = ℓ'-i.castSucc-1`, the last): both sides read `r'`.
      have hjlast : (j : ℕ) = ℓ' - ↑i.castSucc - 1 := by have := j.2; omega
      rw [dif_neg (show ¬ (j : ℕ) < (ℓ' - ↑i.castSucc) - ↑v1 by simp only [hv1]; omega),
          Sum.elim_inr]
      simp only [show (Fin.cast hn j) = Fin.last (ℓ' - ↑i.castSucc - 1) from Fin.ext (by simp [hjlast]),
        Fin.snoc_last]
  rw [Finset.sum_congr rfl (fun x _ => hfix x)]
  -- (3) The fixed-last `H` is the advanced projected poly up to `rename (finCongr)`; rewrite via the
  -- round-transition step, then push `eval_rename` and reindex the survivor cube to the next cube.
  have hstep := RingSwitching.fixFirstVariablesOfMQP_projectToMid_step (L := L) (ℓ := ℓ') t m i
    challenges r'
  -- `hstep : fix-last (projectToMid i.castSucc ch) {r'} = rename (finCongr) (projectToMid i.succ …)`.
  rw [show (fixFirstVariablesOfMQP (ℓ' - ↑i.castSucc) ⟨1, by
              have := i.2; simp only [Fin.val_castSucc]; omega⟩ H.val (fun _ => r'))
        = (fixFirstVariablesOfMQP (ℓ' - ↑i.castSucc) ⟨1, by
              have := i.2; simp only [Fin.val_castSucc]; omega⟩
            (projectToMidSumcheckPoly (L := L) (ℓ := ℓ') (t := t) (m := m)
              (i := i.castSucc) (challenges := challenges)).val (fun _ => r')) from by rw [hHdef]]
  rw [hstep]
  -- Push `eval_rename` so each survivor eval is of the next-round projected poly directly.
  have hren : ∀ x : Fin (ℓ' - (↑i.castSucc + 1)) → L,
      MvPolynomial.eval (Fin.append x (fun j => j.elim0) ∘ Fin.cast (by omega))
          (rename (finCongr (show ℓ' - (↑i.succ : ℕ) = ℓ' - ↑i.castSucc - 1 by
              have := i.2; simp only [Fin.val_succ, Fin.val_castSucc]; omega))
            (projectToMidSumcheckPoly (L := L) (ℓ := ℓ') (t := t) (m := m)
              (i := i.succ) (challenges := Fin.cons r' challenges)).val)
        = MvPolynomial.eval
            ((Fin.append x (fun j => j.elim0) ∘ Fin.cast (by omega))
              ∘ finCongr (show ℓ' - (↑i.succ : ℕ) = ℓ' - ↑i.castSucc - 1 by
                have := i.2; simp only [Fin.val_succ, Fin.val_castSucc]; omega))
            (projectToMidSumcheckPoly (L := L) (ℓ := ℓ') (t := t) (m := m)
              (i := i.succ) (challenges := Fin.cons r' challenges)).val := by
    intro x; rw [eval_rename]
  rw [Finset.sum_congr rfl (fun x _ => hren x)]
  -- (4) Reindex the survivor cube `((boolDomain ℓ').drop (i+1)).cube` to the next-round cube
  -- `(boolDomain (ℓ'-i.succ)).cube`; both are the uniform Boolean cube of dimension `ℓ'-i.succ`.
  simp only [boolDomain, SumcheckDomain.drop_uniform]
  symm
  have hdim : ℓ' - (↑i.succ : ℕ) = ℓ' - (↑i.castSucc + 1) := by
    have := i.2; simp only [Fin.val_succ, Fin.val_castSucc]
  apply Finset.sum_nbij' (fun z => z ∘ Fin.cast hdim) (fun y => y ∘ Fin.cast hdim.symm)
  · intro z hz
    apply SumcheckDomain.mem_cube.2
    intro j
    exact by simpa using SumcheckDomain.mem_cube.1 hz (Fin.cast hdim j)
  · intro y hy
    apply SumcheckDomain.mem_cube.2
    intro j
    exact by simpa using SumcheckDomain.mem_cube.1 hy (Fin.cast hdim.symm j)
  · intro z _; funext j; simp
  · intro y _; funext j; simp
  · intro z _
    refine congrArg
      (fun pt => MvPolynomial.eval pt
        (projectToMidSumcheckPoly (L := L) (ℓ := ℓ') (t := t) (m := m)
          (i := i.succ) (challenges := Fin.cons r' challenges)).val) ?_
    funext j
    -- The recombined point `append (z ∘ cast) ∅ (cast (finCongr j))` reads `z` at the value-`j`
    -- index (the `Fin.append`-with-empty is the left part, and every cast preserves `.val`).
    simp only [Function.comp_apply, finCongr_apply, Fin.cast_cast]
    rw [show (Fin.cast (show ℓ' - (↑i.succ : ℕ) = ℓ' - (↑i.castSucc + 1) + 0 by
              have := i.2; simp only [Fin.val_succ, Fin.val_castSucc]; omega) j)
          = Fin.castAdd 0 (Fin.cast hdim j) from Fin.ext rfl,
        Fin.append_left, Function.comp_apply]
    exact congrArg z (Fin.ext (by simp only [Fin.val_cast]))
  -- The `getSumcheckRoundPoly_eval_eq_sum_snoc` rewrite leaves its (conclusion-irrelevant) autobound
  -- `ℕ` parameters as trailing metavariable goals; any `ℕ` discharges them (the lemma's statement is
  -- independent of them).
  all_goals exact ℓ'


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
  rw [Reduction.perfectCompleteness_eq_prob_one]
  intro ⟨stmtIn, oStmtIn⟩ witIn h_relIn
  -- (ALGEBRA) Unpack the input relation's master KState conjuncts at round `i.castSucc`.
  simp only [sumcheckRoundRelation, sumcheckRoundRelationProp, masterKStateProp,
    witnessStructuralInvariant, sumcheckConsistencyProp, Set.mem_setOf_eq, true_and] at h_relIn
  obtain ⟨hStruct, hConsist, hCompat⟩ := h_relIn
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
  -- (PLUMBING) Peel the 2-message honest oracle-reduction run.  `OracleReduction.perfectCompleteness`
  -- = `Reduction.perfectCompleteness … .toReduction`; unfold the reduction and the prover's
  -- `runToRound` over `Fin.induction_two`, then resolve the two round-direction matches.
  simp only [iteratedSumcheckOracleReduction, OracleReduction.toReduction,
    Sumcheck.Structured.roundOracleReduction, Reduction.run,
    Sumcheck.Structured.roundOracleProver, Sumcheck.Structured.roundOracleVerifier,
    Prover.run, Prover.runToRound, Fin.induction_two, Prover.processRound,
    OracleVerifier.toVerifier, Verifier.run, pSpecSumcheckRound]
  -- Round 0 = `P_to_V` (prover sends `h_i = getSumcheckRoundPoly ℓ' (boolDomain L ℓ') i witIn.H`),
  -- round 1 = `V_to_P` (verifier samples `r'`); both direction matches collapse cleanly.
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
    Matrix.cons_val_fin_one, reduceCtorEq]
  -- WIP — RUN IS NOW FULLY UNFOLDED + DIRECTION-RESOLVED (verified `trace_state`). The honest run is:
  --   P→V `h_i := getSumcheckRoundPoly ℓ' (boolDomain L ℓ') i witIn.H`;
  --   V samples `r' ← L` (the single probabilistic step);
  --   prover output `getRoundProverFinalOutput … 2 i` (witOut.H = `fixFirstVariablesOfMQP (ℓ'-i) ⟨1⟩
  --     witIn.H {r'}`, stmtOut.challenges = `Fin.cons r' stmtIn.challenges`, target = `h_i.eval r'`);
  --   V reads the message via `simulateQ (simOracle2 …)`, runs `guard (∑ b ∈ (boolDomain L ℓ').points i,
  --     h_i.eval b = stmtIn.sumcheck_target)`, outputs stmtOut.
  -- Goal: `probEvent (…) = 1` over the uniform `r'` sample.
  --
  -- TWO REMAINING TASKS (both now mathematically UNBLOCKED; only mechanical):
  -- (1) PROBABILITY ENDGAME. Collapse the `simulateQ (simOracle2 …)` message-query
  --     (`simulateQ_simOracle2_query` + `answer_instDefault`), tie `proverResult.1.messages ⟨0⟩ = h_i`
  --     and `proverResult.1.challenges ⟨1⟩ = r'` from the transcript binds, then close
  --     `probEvent = 1` via `probEvent_eq_one_iff` over the uniform `r'`-sample (no-failure: the
  --     `guard` ALWAYS passes by `getSumcheckRoundPoly_points_sum_eq_cube` + `hConsist`; every output
  --     satisfies the predicate by task (2)). This is the single-challenge analog of the closed
  --     `finalSumcheckOracleReduction_perfectCompleteness` accept-branch peel (which has no challenge).
  -- (2) relOut DISCHARGE (the four master-KState conjuncts at index `i.succ`):
  --   • `witnessStructuralInvariant i.succ`: `witOut.H = projectToMidSumcheckPoly t' m i.succ
  --     (Fin.cons r' ch)`.  From `hStruct` (`witIn.H = projectToMid … i.castSucc ch`) and
  --     `RingSwitching.fixFirstVariablesOfMQP_projectToMid_step`, the honest `witOut.H` equals
  --     `rename (finCongr …) (projectToMid … i.succ (cons r' ch))`.  The residual `rename (finCongr)`
  --     is the index relabel `Fin (ℓ'-i.succ) ≃ Fin (ℓ'-i.castSucc-1)`; it must be reconciled with
  --     `getRoundProverFinalOutput`'s own internal `by omega` cast (HEq bookkeeping — same family as
  --     `rename_finCongr_heq`).
  --   • `sumcheckConsistencyProp i.succ`: `stmtOut.sumcheck_target (= h_i.eval r') = ∑_{cube(ℓ'-i.succ)}
  --     witOut.H`.  This is the single-point (`r'`) specialisation of the proven
  --     `getSumcheckRoundPoly_points_sum_eq_cube` chain: `h_i.eval r' = ∑_{survivors} eval (snoc · r')
  --     curH = ∑_{cube} (fixFirstVariablesOfMQP witIn.H {r'})` (via `getSumcheckRoundPoly_eval_eq_sum_snoc`
  --     + `fixFirstVariablesOfMQP_eval` + the `sum_cube_snoc` survivor reindex already used above).
  --   • the verifier `guard` (`∑ b ∈ points i, h_i.eval b = sumcheck_target`) is `hConsist` rewritten
  --     by `getSumcheckRoundPoly_points_sum_eq_cube` (PROVEN above).
  --   • `initialCompatibility ⟨witOut.t', oStmt⟩ = ⟨witIn.t', oStmt⟩` is `hCompat` (`witOut.t' = witIn.t'`).
  -- The verifier-check algebra (the genuinely #20-unblocked core) is DONE; what remains is the
  -- `OptionT`/`StateT`/`simulateQ` run-shape plumbing for a 2-message+1-challenge oracle reduction
  -- (no proven precedent in-repo — the only closed oracle-reduction completeness, final-sumcheck, has
  -- ZERO challenges) plus the HEq cast reconciliation in (2). Preserved as WIP per honest-completion.
  -- (A) VERIFIER CHECK: the honest round univariate `h_i := getSumcheckRoundPoly i witIn.H` satisfies
  -- the verifier's accept condition `∑_{points i} h_i(b) = stmtIn.sumcheck_target` via the cube
  -- identity `getSumcheckRoundPoly_points_sum_eq_cube` and the relIn `sumcheckConsistencyProp`.
  have hcheck : (∑ b ∈ (boolDomain L ℓ').points i,
      Polynomial.eval b (getSumcheckRoundPoly ℓ' (boolDomain L ℓ') (i := i) witIn.H).val)
      = stmtIn.sumcheck_target := by
    rw [getSumcheckRoundPoly_points_sum_eq_cube (i := i) (H := witIn.H), ← hConsist]
  -- (B) NEXT-ROUND CONSISTENCY (for every challenge `r'`): the next-round target `h_i.eval r'`
  -- equals the next cube-sum of the advanced witness `witOut.H = fixFirstVariablesOfMQP … {r'}`.
  -- This is `getSumcheckRoundPoly_eval_eq_cube_succ` instantiated at the honest witness.
  trace_state
  sorry

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

/-- **Iterated-round verifier-run collapse (defect-#21 guard form).** Under the message-oracle
simulation `simulateQ (simOracle2 …)`, the 2-message `roundOracleVerifier`
(= `iteratedSumcheckOracleVerifier`) reduces to a single deterministic `if`: on the sumcheck check
passing it `pure`s the accept statement (next-round target `h_i(r')`, challenges advanced by
`Fin.cons r'`), and on a failed check it emits `failure` (defect-#21) — so the reject branch has
*no* support element. This is the 2-message analog of
`BatchingPhase.oracleVerifier_verify_collapse`; the message query collapses via
`simulateQ_simOracle2_query` (+ `answer_instDefault'`), then `guard_eq`/`apply_ite` exposes the
`if`. `msgs ⟨0,_⟩` is the round univariate `h_i`, `chals ⟨1,_⟩` is the verifier challenge `r'`. -/
private lemma iteratedSumcheckOracleVerifier_verify_collapse (i : Fin ℓ')
    (stmt : Statement (L := L) (ℓ := ℓ') (RingSwitchingBaseContext κ L K ℓ P) i.castSucc)
    (oStmt : ∀ j, aOStmtIn.OStmtIn j)
    (tr : FullTranscript (pSpecSumcheckRound L)) :
    simulateQ (OracleInterface.simOracle2 []ₒ oStmt (FullTranscript.messages tr))
        ((iteratedSumcheckOracleVerifier κ L K P ℓ ℓ' aOStmtIn i).verify stmt
          (FullTranscript.challenges tr))
      = (if (∑ b ∈ (boolDomain L ℓ').points i, (FullTranscript.messages tr ⟨0, rfl⟩).val.eval b)
            = stmt.sumcheck_target then
           pure ({ ctx := stmt.ctx,
                   sumcheck_target := (FullTranscript.messages tr ⟨0, rfl⟩).val.eval
                     (FullTranscript.challenges tr ⟨1, rfl⟩),
                   challenges := Fin.cons (FullTranscript.challenges tr ⟨1, rfl⟩) stmt.challenges }
                 : Statement (L := L) (ℓ := ℓ') (RingSwitchingBaseContext κ L K ℓ P) i.succ)
         else failure
         : OptionT (OracleComp []ₒ) _) := by
  -- `iteratedSumcheckOracleVerifier = roundOracleVerifier` (a `@[reducible]` wrapper); unfold to
  -- the shared verify body and collapse the single message-oracle query.
  simp only [iteratedSumcheckOracleVerifier, Sumcheck.Structured.roundOracleVerifier]
  rw [simulateQ_optionT_bind, simulateQ_simOracle2_query]
  refine OptionT.ext ?_
  dsimp only [Sigma.fst, Sigma.snd]
  erw [OptionT.run_bind_lift]
  erw [pure_bind]
  -- `answer (instDefault) m () = m` makes the queried message the transcript message `h_i`; then
  -- `guard_eq` exposes the `if`, and `simulateQ`/`OptionT.run` push through the query-free parts.
  rw [answer_instDefault']
  simp only [guard_eq, apply_ite, map_pure, bind_pure_comp]
  by_cases hc : (∑ b ∈ (boolDomain L ℓ').points i, (FullTranscript.messages tr ⟨0, rfl⟩).val.eval b)
      = stmt.sumcheck_target
  · simp only [hc, if_true, reduceIte]
    erw [simulateQ_pure]
    rfl
  · simp only [hc, if_false, reduceIte]
    rw [map_optionT_failure', simulateQ_optionT_failure']

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
  | ⟨2, h2⟩ => -- implied by (relOut + V's check); the SOUNDNESS-CORRECT post-challenge KState.
    -- DEFECT-#22 (KState-redesign, counterexample-backed) — the post-challenge (index-⟨2⟩) KState must
    -- NOT carry `localizedRoundPolyCheck` (`h_i = h_star`) nor the master `sumcheckConsistencyProp`
    -- on the INPUT statement: a malicious prover may send `h_i ≠ h_star`, the honest verifier only
    -- checks `∑_b h_i(b) = stmtLast.sumcheck_target` (never `h_i = h_star`), so for an accepted run
    -- with `(stmtOut, witOut) ∈ relOut` neither `h_i = h_star` nor `stmtLast.sumcheck_target =
    -- ∑_cube witLast.H` is provable in `toFun_full` (the prior `masterKStateProp` form was therefore
    -- unclosable — the SAME wall as the open `BinaryBasefold.foldKStateProp`). The correct
    -- post-challenge invariant keeps only what relOut + the verifier check actually pin down:
    --   • `explicitVCheck`  — the verifier's accept condition `∑_b h_i(b) = stmtLast.sumcheck_target`
    --     (= `hcheck`, available on the accept branch);
    --   • `nextSumcheckTargetCheck` — `h_i.eval r' = h_star.eval r'` (derivable from relOut's
    --     consistency+structural at `i.succ` via `getSumcheckRoundPoly_eval_eq_cube_succ`);
    --   • `witnessStructuralInvariant` (true by the extractor's definition of `witLast.H`);
    --   • `initialCompatibility` (= `hCompat`).
    -- RBR knowledge soundness still closes at `2/|L|`: the bad event `¬kSF⟨1⟩ ∧ kSF⟨2⟩` forces
    -- `h_i ≠ h_star` (from `¬kSF⟨1⟩`, since `kSF⟨2⟩`'s struct+`explicitVCheck`+the cube identity make
    -- `h_i = h_star ⇒ kSF⟨1⟩`'s consistency, and `h_i = h_star` is `kSF⟨1⟩`'s remaining local check)
    -- yet `h_i.eval r' = h_star.eval r'` (from `kSF⟨2⟩`), i.e. `r'` is a root of the nonzero degree-≤2
    -- `h_i - h_star` — a Schwartz–Zippel `2/|L|` event. So this is strictly the soundness-faithful
    -- KState, not a weakening: index ⟨1⟩ retains the full `masterKStateProp + localizedRoundPolyCheck`.
    let h_i := get_Hᵢ (m := ⟨2, h2⟩) (tr := tr) (hm := by simp only [Nat.one_le_ofNat])
    let r_i' := get_rᵢ' (m := ⟨2, h2⟩) (tr := tr) (hm := by simp only [le_refl])
    let explicitVCheck :=
      (∑ b ∈ (boolDomain L ℓ').points i, h_i.val.eval b) = stmt.sumcheck_target
    let nextSumcheckTargetCheck := -- this presents sumcheck of next round (sᵢ = s^*ᵢ)
      h_i.val.eval r_i' = h_star.val.eval r_i'
    explicitVCheck ∧ nextSumcheckTargetCheck
      ∧ RingSwitching.witnessStructuralInvariant κ L K P ℓ ℓ' h_l stmt witMid
      ∧ aOStmtIn.initialCompatibility ⟨witMid.t', oStmt⟩

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
    -- (A) SUPPORT EXTRACTION (front-end, defect-#21 verifier-collapse). Turn the `> 0` probability
    -- into a support element and collapse the 2-message verifier run via the now-proven
    -- `iteratedSumcheckOracleVerifier_verify_collapse` (the analog of
    -- `BatchingPhase.oracleVerifier_verify_collapse`). The collapse's reject branch is `failure`
    -- (guard-emitting verifier), so on a failed sumcheck check the run has no support element.
    rw [gt_iff_lt, probEvent_pos_iff] at h_relOut
    obtain ⟨⟨stmtOut, oStmtOut⟩, hx, h_SumcheckStepRelOut⟩ := h_relOut
    rw [OptionT.mem_support_iff] at hx
    simp only [OptionT.run_mk, support_bind, Set.mem_iUnion] at hx
    obtain ⟨s, _, hx⟩ := hx
    set witLast := (iteratedSumcheckRbrExtractor κ L K P ℓ ℓ' h_l aOStmtIn i).extractOut
      ⟨stmtLast, oStmtLast⟩ tr witOut with hwitLast
    simp only [Fin.reduceLast, Fin.isValue]
    -- Collapse `simulateQ (simOracle2 …) (verify …)` to the deterministic `if sumcheck_check then
    -- pure stmtOutAccept else failure` (defect-#21), then peel `Verifier.run`/`toVerifier`.
    simp only [OracleVerifier.toVerifier, Verifier.run, bind_pure_comp,
      StateT.run'_eq, support_map, Set.mem_image, Prod.exists] at hx
    obtain ⟨val, s', hmem, heq⟩ := hx
    rw [iteratedSumcheckOracleVerifier_verify_collapse] at hmem
    -- (B) CASE SPLIT on the verifier's sumcheck check (`split` reads the `if` cond from `hmem`).
    split at hmem
    · -- ACCEPT branch: pin the deterministic output, then reconstruct the index-⟨2⟩ KState.
      rename_i hcheck
      simp only [bind_pure_comp, map_pure] at hmem
      erw [simulateQ_pure] at hmem
      simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff, Option.some.injEq,
        Prod.mk.injEq] at hmem
      obtain ⟨hval, -⟩ := hmem
      -- `heq : some val = some (stmtOut, oStmtOut)`; with `hval : val = (stmtOutAccept, oStmt)`,
      -- pin `stmtOut = stmtOutAccept` and `oStmtOut = oStmtLast`.
      rw [hval] at heq
      simp only [Option.some.injEq, Prod.mk.injEq] at heq
      obtain ⟨rfl, rfl⟩ := heq
      -- Reduce the index-⟨2⟩ KState (defect-#22 form) to its four conjuncts, and
      -- `h_SumcheckStepRelOut` (the verifier's accept output `(stmtOutAccept, witOut)` ∈ relOut at
      -- index `i.succ`) to its three (master-conjuncts at `i.succ`).
      unfold iteratedSumcheckKStateProp
      simp only [masterKStateProp, witnessStructuralInvariant, sumcheckRoundRelation,
        sumcheckRoundRelationProp, Set.mem_setOf_eq, sumcheckConsistencyProp]
        at h_SumcheckStepRelOut ⊢
      obtain ⟨-, hWitStruct, hConsistSucc, hCompat⟩ := h_SumcheckStepRelOut
      -- `witLast.H = projectToMid i.castSucc stmtLast.challenges` (extractor def) and `witLast.t' =
      -- witOut.t'`; pin them so the round-poly identity speaks `witLast`'s language.
      have hwitLastH : witLast.H = projectToMidSumcheckPoly (L := L) (ℓ := ℓ') (t := witOut.t')
          (m := (RingSwitching_SumcheckMultParam κ L K P ℓ ℓ' h_l).multpoly (ctx := stmtLast.ctx))
          (i := i.castSucc) (challenges := stmtLast.challenges) := rfl
      have hwitLastt : witLast.t' = witOut.t' := rfl
      -- `hcheck` is the verifier's accept condition `∑_b (msgs tr ⟨0⟩)(b) = stmtLast.sumcheck_target`.
      refine ⟨?_, ?_, rfl, hCompat⟩
      · -- `explicitVCheck` = the verifier's accept condition `hcheck`.
        exact hcheck
      · -- `nextSumcheckTargetCheck`: `h_i.eval r' = h_star.eval r'` with
        -- `h_star = getSumcheckRoundPoly i witLast.H`. The accept output pins
        -- `stmtOut.sumcheck_target = h_i.eval r'` and `stmtOut.challenges = Fin.cons r' stmtLast.…`;
        -- relOut's consistency `stmtOut.sumcheck_target = ∑_cube witOut.H` + structural
        -- `witOut.H = projectToMid i.succ (cons r' stmtLast.challenges)` give
        -- `h_i.eval r' = ∑_cube (projectToMid i.succ (cons r' …))`; and
        -- `h_star.eval r' = getSumcheckRoundPoly i (projectToMid i.castSucc …) .eval r'` equals the
        -- same next-round cube sum by `getSumcheckRoundPoly_eval_eq_cube_succ`.
        rw [hwitLastH,
          getSumcheckRoundPoly_eval_eq_cube_succ (i := i) (t := witOut.t')
            (m := (RingSwitching_SumcheckMultParam κ L K P ℓ ℓ' h_l).multpoly (ctx := stmtLast.ctx))
            (challenges := stmtLast.challenges) (r' := _)]
        -- Normalise the `equivMessagesChallenges` message/challenge extractions in BOTH the goal and
        -- `hConsistSucc`/`hWitStruct` to the bare transcript reads `tr ⟨0,_⟩` / `tr ⟨1,_⟩` (both
        -- `toMessagesUpTo`/`toChallengesUpTo` are just `tr` at the index), so they speak the same form.
        simp only [Transcript.equivMessagesChallenges, Equiv.coe_fn_mk,
          Transcript.toMessagesChallenges, Transcript.toMessagesUpTo, Transcript.toChallengesUpTo,
          FullTranscript.messages, FullTranscript.challenges, Fin.isValue]
          at hConsistSucc hWitStruct ⊢
        -- LHS `tr 0 .eval (tr 1) = stmtOut.sumcheck_target = ∑_cube witOut.H = ∑_cube (projectToMid
        -- i.succ stmtOut.challenges)`; `stmtOut.challenges = Fin.cons (tr 1) stmtLast.challenges`.
        rw [hWitStruct] at hConsistSucc
        -- The goal LHS `eval (tr ⟨1,_⟩) (tr ⟨0,_⟩)` and `hConsistSucc`'s `eval (tr 1) (tr 0)` are the
        -- same transcript reads (defeq `Fin 2` indices); `convert` closes the index encoding gap, and
        -- the resulting cube sums agree (same `projectToMid i.succ (cons (tr 1) stmtLast.challenges)`).
        convert hConsistSucc using 3 <;> apply Fin.ext <;> rfl
    · -- REJECT branch (defect-#21, NOW VACUOUS). On a failed check the verifier emits `failure`, so
      -- the run has no support element; `hmem`'s membership in `support failure` is contradictory.
      exfalso
      -- `(fun a => (a, oStmt)) <$> failure = failure` (`map_optionT_failure'`), `simulateQ` keeps
      -- it; then `failure.run s = pure (none, s)` has support without `some`.
      rw [map_optionT_failure', simulateQ_optionT_failure'] at hmem
      rw [show (failure : OptionT (StateT σ ProbComp) (Statement (L := L) (ℓ := ℓ')
            (RingSwitchingBaseContext κ L K ℓ P) i.succ × (∀ j, aOStmtIn.OStmtIn j)))
          = (pure none : StateT σ ProbComp _) from rfl] at hmem
      rw [StateT.run_pure] at hmem
      simp only [support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at hmem
      -- `hmem.1 : val = none` contradicts `heq : val = some (stmtOut, oStmtOut)`.
      rw [hmem.1] at heq
      exact absurd heq.symm (by simp)

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
  obtain ⟨stmt, oStmt⟩ := stmtIn
  -- The single challenge is at round index `1` (`pSpecSumcheckRound` = `[P_to_V, V_to_P]`).
  have hj : j = ⟨1, rfl⟩ := by
    obtain ⟨jv, hjdir⟩ := j
    match jv, hjdir with
    | ⟨0, _⟩, hjdir => simp [pSpecSumcheckRound] at hjdir
    | ⟨1, _⟩, _ => rfl
  subst hj
  -- ════════════════════════════════════════════════════════════════════════════════════════════
  -- SOUNDNESS WALL (defect-#22 KState UNJUSTIFIED at `2/|L|`). Discovered while attempting the
  -- per-transcript Schwartz–Zippel reduction. The redesigned post-challenge state `kSF⟨2⟩`
  -- (`iteratedSumcheckKStateProp` at `m = ⟨2⟩`) carries `h_star := getSumcheckRoundPoly i witMid.H`
  -- (lines 614-615), where `witMid` is the SAME object existentially quantified by the rbrKS bad
  -- event. The bad event (with `extractMid ⟨1⟩ … witMid = witMid` the identity) is
  --   `∃ witMid, ¬kSF⟨1⟩ stmt tr witMid ∧ kSF⟨2⟩ stmt (tr.concat r') witMid`,
  -- and `kSF⟨2⟩` constrains `witMid` ONLY by: struct (`witMid.H = projectToMid witMid.t'
  -- stmt.challenges`), `explicitVCheck` (`∑_b h_i(b) = stmt.sumcheck_target` — independent of
  -- `witMid`), `nextTarget` (`h_i(r') = getSumcheckRoundPoly i witMid.H .eval r'`), and the ABSTRACT
  -- `aOStmtIn.initialCompatibility ⟨witMid.t', oStmt⟩`. NOTHING pins `witMid.t'` (hence `witMid.H`,
  -- hence `h_star`) to a unique value: `initialCompatibility` is a free field of `AbstractOStmtIn`
  -- (Prelude:249-255) with no functional/uniqueness axiom, and the theorem quantifies over an
  -- arbitrary `aOStmtIn` (e.g. `initialCompatibility := True`).
  --
  -- Therefore the bad-challenge set is a UNION over the free `witMid.t'` of
  --   `roots(h_i - getSumcheckRoundPoly i (projectToMid witMid.t' stmt.challenges))`,
  -- NOT a single degree-≤2 root set. The `∃ witMid` lets the adversary pick `witMid.t'` AFTER seeing
  -- `r'`: whenever `t' ↦ getSumcheckRoundPoly i (projectToMid t' stmt.challenges) .eval r'` can hit
  -- `h_i(r')` with the resulting `h_star ≠ h_i` (generic for a permissive `initialCompatibility`),
  -- `r'` is bad. The Schwartz–Zippel `2/|L|` bound then FAILS (the bad set can be ~all of `L`).
  --
  -- CONSEQUENCE (honest-completion): the #22 KState redesign is NOT justified at error `2/|L|` for an
  -- arbitrary `aOStmtIn`. The cluster (redesign + toFun_full + this rbrKS) is NOT a verified unit.
  -- EXACT REMAINING OBLIGATION to justify the redesign, one of:
  --   (a) Add a uniqueness/soundness axiom to `AbstractOStmtIn` — e.g. `initialCompatibility` pins
  --       `t'` (`∀ t₁ t₂ oS, initialCompatibility ⟨t₁,oS⟩ → initialCompatibility ⟨t₂,oS⟩ → t₁ = t₂`)
  --       — so `h_star` is a fixed function of `(stmt, oStmt)`; then the union collapses to one
  --       degree-≤2 root set and the SZ bound holds (the algebra `getSumcheckRoundPoly_points_sum_…`
  --       + `card_roots` is ready). This CHANGES the relation interface (downstream re-proof).
  --   (b) Re-redesign `kSF⟨2⟩` to compute `h_star` from `(stmt, oStmt)` directly (not from
  --       `witMid.H`) AND prove the matching `toFun_full` (the prior `localizedRoundPolyCheck` form
  --       was unclosable — the #22 motivation — so this needs a genuinely new invariant, not a revert).
  -- Neither is a leaf proof; both are owner-interface decisions. Preserved per honest-completion:
  -- the redesign's `toFun_full` is sorry-free, but its justifying rbrKS is NOT — so per HOUSE RULES
  -- this redesign is reported as UNJUSTIFIED, not as a closure.
  sorry

end IteratedSumcheckStep

section FinalSumcheckStep
/-!
## Final Sumcheck Step
-/

/-- `pSpecFinalSumcheck L` is a single prover-to-verifier message (no challenge). -/
instance : ProverOnly (pSpecFinalSumcheck L) where
  prover_first' := rfl

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
    -- FAILURE-EMITTING VERIFIER (defect-#21 repair, mirroring `roundOracleVerifier`). On a failed
    -- step-9 check the verifier emits `failure` (`guard`, i.e. `OptionT` `none`) rather than a
    -- *dummy* accepting statement `{0, 0}`. The dummy let a maliciously-chosen `witOut` (with
    -- `witOut.t.eval 0 = 0`) lie in `relOut = toRelInput` while the KState local check
    -- `sumcheck_target = eq_tilde_eval * c` is FALSE, leaving the `toFun_full` REJECT branch
    -- unprovable (the dummy is reachable). With `guard` the reject branch has no support element,
    -- so it is vacuous and the knowledge-soundness contract (verifier signals rejection, never
    -- forwards a fake statement) holds. Completeness only exercises the accept branch (via
    -- `if_pos`), so this does not weaken `finalSumcheckOracleReduction_perfectCompleteness`.
    guard (stmtIn.sumcheck_target = eq_tilde_eval * s')

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
  -- `guard check` (defect-#21) `= if check then pure () else failure` (`guard_eq`); the trailing
  -- `pure () >>= fun _ => pure stmtOut` collapses to `pure stmtOut` (`pure_bind`), so the accept
  -- branch is identical to the prior `unless`-fallthrough. Select it via `hcheck`.
  simp only [answer_instDefault', guard_eq, apply_ite, simulateQ_optionT_pure', pure_bind]
  rw [if_pos hcheck]
  -- After selecting the accept branch the verify body is `pure () >>= fun _ => pure stmtOut`;
  -- collapse it through `simulateQ`/`OptionT` (`simulateQ_optionT_bind`/`_pure'`/`lift_pure`) so
  -- the inner run is a single `pure (some stmtOut)` and the `Option.elimM`/`getM` match reduces —
  -- the same `pure`-shaped normal form the prior dummy verifier produced.
  simp only [simulateQ_optionT_bind, simulateQ_optionT_lift, simulateQ_optionT_pure',
    OptionT.lift_pure, pure_bind, map_pure, simulateQ_pure, Option.elimM, bind_pure_comp,
    Option.elim_some, Option.elim_none, StateT.run'_eq, OptionT.run_pure, Option.getM, Option.elim,
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
    simp only [OptionT.lift_pure, FullTranscript.messages,
      OptionT.run_pure, OptionT.run_lift,
      answer_instDefault', simulateQ_optionT_pure', simulateQ_map, map_pure] at hx
    erw [pure_bind] at hx
    -- Rewrite the run's `tr 0` to the `equivMessagesChallenges` message `c` so the case split and the
    -- final KState reconstruction speak the same language. `hc0 : c = tr 0` is definitional.
    rw [show (tr (0 : Fin 1) : L) = c from hc0.symm] at hx
    -- `guard check` (defect-#21) `= if check then pure () else failure` (`guard_eq`); the map
    -- `(fun _ => stmtOut₀) <$> (·)` distributes over the `ite` (`apply_ite`), turning the
    -- verifier run into `if check then pure stmtOut₀ else (failure mapped)`. The reject branch
    -- maps `failure`, which stays `failure` (empty support), so it is VACUOUS.
    simp only [guard_eq, apply_ite, map_pure] at hx
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
    · -- REJECT branch (defect-#21 repair, NOW VACUOUS). On a failed step-9 check the
      -- guard-emitting `finalSumcheckVerifier` produces `failure` (`OptionT` `none`), not a dummy
      -- statement. Selecting the `if_neg` branch leaves the verifier run as
      -- `(fun _ => stmtOut₀) <$> (failure : OptionT …)`, which is `failure`; `simulateQ` keeps
      -- it and its `run'` support contains no `some`. So the support hypothesis
      -- `hx : some (stmtOut, oStmtOut) ∈ support …` is contradictory.
      --
      -- This is the verifier-design fix flagged in the prior WIP note: emitting a dummy let the
      -- dummy `{0,0}` lie in `relOut` whenever `witOut.t.eval 0 = 0` (prover-forceable), leaving
      -- the reject branch unprovable. With `guard`/`failure` the reject branch has no support
      -- element and is vacuous, matching the soundness contract (no fake statement is forwarded).
      exfalso
      rw [if_neg hcheck] at hx
      -- Propagate `failure` outward: `f <$> failure = failure` (`map_optionT_failure'`) and
      -- `simulateQ` commutes with `failure` (`simulateQ_optionT_failure'`). The verifier run is
      -- then `failure`, whose `run'` support is `{none}` (`= pure none`); `some _ ∈ supp` False.
      rw [map_optionT_failure', simulateQ_optionT_failure', map_optionT_failure',
        simulateQ_optionT_failure'] at hx
      -- `failure : OptionT (StateT σ ProbComp)` is `OptionT.fail = OptionT.mk (pure none)`;
      -- `run' … s` is then `pure none`, support `{none}`. `hx` claims `some _ ∈ {none}`: absurd.
      rw [show (failure : OptionT (StateT σ ProbComp) (MLPEvalStatement L ℓ'
            × (∀ j, aOStmtIn.OStmtIn j))) = (pure none : StateT σ ProbComp _) from rfl] at hx
      rw [StateT.run'_eq, StateT.run_pure] at hx
      simp only [map_pure, support_pure, Set.mem_singleton_iff] at hx
      exact absurd hx (by simp)

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

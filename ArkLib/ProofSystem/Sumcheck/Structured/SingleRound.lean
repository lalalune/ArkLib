/-
Copyright (c) 2025 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chung Thai Nguyen, Quang Dao
-/

import ArkLib.ProofSystem.Sumcheck.Structured
import ArkLib.ProofSystem.Sumcheck.Spec.SingleRound

/-!
# Structured (Witness-Mode) Sumcheck — Single-Round Primitives

This file collects single-round primitives for the structured (witness-mode) sumcheck:

- `getSumcheckRoundPoly` — derive the univariate `g_i(X)` sent by the prover from
  the multiquadratic round polynomial `H_i(X_i, ..., X_{ℓ-1})` by summing over the
  remaining boolean-hypercube directions.
- `pSpecSumcheckRound` — the two-message protocol spec for one round
  (`P_to_V : L⦃≤ d⦄[X]`, `V_to_P : L`; `d` defaults to 2), with `OracleInterface` /
  `SampleableType` instances.
- `roundPrvState`, `getRoundProverFinalOutput`, `roundOracleProver`, `roundOracleVerifier`,
  `roundOracleReduction` — the per-round prover / verifier / reduction, generic in a protocol
  `Context : Type` and external oracle statements `OStmtIn : ιₛᵢ → Type`. The outer protocol
  iterates these via `seqCompose`.
- `roundKnowledgeError` — the `2 / |L|` Schwartz–Zippel round error.

These were originally housed in `Binius.BinaryBasefold.Prelude`,
`RingSwitching.Spec`, and `RingSwitching.SumcheckPhase`. They are fully
generic (no binary-tower or ring-switching dependencies) and have been promoted here so
that future ring-switching protocols (Hachi, Galois-ring PCS) can reuse them without
depending on `Binius.*`. `RingSwitching.SumcheckPhase` retains thin `@[reducible]`
wrappers that specialize `Context` and `OStmtIn` back to the ring-switching types.
-/

namespace Sumcheck.Structured

open OracleSpec OracleComp ProtocolSpec Finset Polynomial MvPolynomial

noncomputable section

section RoundPoly

variable {L : Type} [CommRing L] (ℓ : ℕ) [NeZero ℓ] (D : SumcheckDomain L ℓ)

/-- Degree bound for the prover's round polynomial over an **arbitrary** summation set `S`.
This is the heterogeneous generalisation of `Spec.SingleRound.sumcheck_roundPoly_degreeLE`, which
fixes `S` to a uniform cube `(univ.map D) ^ᶠ (n - i)`. The per-round / hyperprism sumcheck sums over
heterogeneous cubes `(SumcheckDomain.drop …).cube`, so the degree bound must not depend on the shape
of `S` — and indeed it doesn't: each summand has degree `≤ deg` in the free variable, and a finite
sum preserves that. -/
theorem roundPoly_degreeLE_finset {R : Type*} [CommSemiring R] {n deg : ℕ} (i : Fin (n + 1))
    {challenges : Fin i.castSucc → R} {poly : R[X Fin (n + 1)]}
    (hp : poly ∈ R⦃≤ deg⦄[X Fin (n + 1)]) (S : Finset (Fin (n - i) → R)) :
    ∑ x ∈ S, poly ⸨X ⦃i⦄, challenges, x⸩' (by simp; omega) ∈ R⦃≤ deg⦄[X] := by
  refine mem_degreeLE.mpr ((degree_sum_le S _).trans (Finset.sup_le fun x _ => ?_))
  refine degree_map_le.trans (natDegree_le_iff_degree_le.mp ?_)
  rw [natDegree_finSuccEquivNth]
  exact degreeOf_le_iff.mpr fun m a ↦ hp a i

/- `H_i(X_i, ..., X_{ℓ-1})` -> `g_i(X)` derivation. Degree-generic: the round polynomial
`h` and the resulting univariate `g_i` share the degree bound `d` (inferred from `h`).

VARIABLE-CONVENTION REPAIR (defect-#20, counterexample-backed). This marginalises the **last**
surviving variable (index `ℓ - i.castSucc - 1`), keeping it as the round indeterminate `X`, and sums
over the Boolean cube of the *earlier* survivors `(D.drop (i+1)).cube`. The previous form
marginalised variable `0`, which is INCONSISTENT with the witness advance / structural invariant:
`projectToMidSumcheckPoly` and `fixFirstVariablesOfMQP` consume variables from the **end** (the
`Fin.cons`-form round transition `fixFirstVariablesOfMQP_projectToMid_step` fixes the *last*
surviving variable). Keeping variable `0` free while the witness advance fixes the *last* variable
makes the two marginals of an asymmetric `H` differ — the verified `ZMod 7` counterexample in the
`RoundTransition` section note of `RingSwitching.Prelude`. Marginalising the **last** variable here
(`Fin.last _` in the `⸨X ⦃·⦄, …⸩` notation) puts the round indeterminate on the *same* coordinate
that `getRoundProverFinalOutput`'s `fixFirstVariablesOfMQP … {r'}` fixes, so `h_i.eval r'` is the
next-round consistency sum of `witOut.H` (see `getSumcheckRoundPoly_eval_eq_sum_lastVar`). -/
def getSumcheckRoundPoly {d : ℕ} (i : Fin ℓ) (h : ↥L⦃≤ d⦄[X Fin (ℓ - ↑i.castSucc)])
    : L⦃≤ d⦄[X] := by
  have h_i_lt_ℓ : ℓ - ↑i.castSucc > 0 := by
    have hi := i.2
    exact Nat.zero_lt_sub_of_lt hi
  have h_count_eq : ℓ - ↑i.castSucc - 1 + 1 = ℓ - ↑i.castSucc := by
    omega
  let challenges : Fin 0 → L := fun (j : Fin 0) => j.elim0
  let curH_cast : L[X Fin ((ℓ - ↑i.castSucc - 1) + 1)] := by
    convert h.val
  let g := ∑ x ∈ (D.drop (↑i.castSucc + 1)).cube,
    curH_cast ⸨X ⦃Fin.last (ℓ - ↑i.castSucc - 1)⦄, x, challenges⸩' (by omega)
  exact ⟨g, by
    have h_in_degLE : curH_cast ∈ L⦃≤ d⦄[X Fin (ℓ - ↑i.castSucc - 1 + 1)] := by
      rw! (castMode := .all) [h_count_eq]
      dsimp only [Fin.val_castSucc, eq_mpr_eq_cast, curH_cast]
      rw [eqRec_eq_cast, cast_cast, cast_eq]
      exact h.property
    have h_deg_le_d : g ∈ L⦃≤ d⦄[X] := by
      simp only [g]
      -- Each summand `curH_cast ⸨X ⦃Fin.last⦄, x, ∅⸩` has degree `≤ d` in the free variable
      -- (`finSuccEquivNth` keeps the degree along the un-fixed coordinate), and a finite sum of
      -- such preserves the degree bound.
      have h_dof : ∀ j, MvPolynomial.degreeOf j curH_cast ≤ d :=
        (MvPolynomial.mem_restrictDegree_iff_degreeOf_le curH_cast d).mp h_in_degLE
      refine mem_degreeLE.mpr ((degree_sum_le _ _).trans (Finset.sup_le fun x _ => ?_))
      refine degree_map_le.trans (natDegree_le_iff_degree_le.mp ?_)
      rw [natDegree_finSuccEquivNth]
      exact h_dof (Fin.last (ℓ - ↑i.castSucc - 1))
    rw [mem_degreeLE] at h_deg_le_d ⊢
    exact h_deg_le_d
  ⟩

/-- **Round-univariate evaluation as a survivor-cube sum (last-variable / `snoc` form).** Evaluating
the prover's round univariate `getSumcheckRoundPoly ℓ D i h` at any point `r` equals the sum, over
the next round's survivor cube `(D.drop (i.castSucc+1)).cube`, of the full round polynomial `H = h`
with the **last** surviving variable fixed to `r` (via `Fin.snoc`). Proven from the marginal
identity
`RingSwitching.roundPoly_eval_eq_sum_snoc` (Prelude). `curH` is `h.val` transported across
`getSumcheckRoundPoly`'s internal index equality `ℓ-i.castSucc = (ℓ-i.castSucc-1)+1`, supplied via a
`HEq`. This is the degree-generic generalisation of `RingSwitching`'s boolDomain-specialised
`getSumcheckRoundPoly_eval_eq_sum_snoc`. -/
theorem getSumcheckRoundPoly_eval_eq_sum_snoc {d : ℕ} (i : Fin ℓ)
    (h : ↥L⦃≤ d⦄[X Fin (ℓ - ↑i.castSucc)]) (r : L)
    (curH : L[X Fin ((ℓ - ↑i.castSucc - 1) + 1)]) (hcurH : HEq curH h.val) :
    (getSumcheckRoundPoly ℓ D (i := i) h).val.eval r
      = ∑ x ∈ (D.drop (↑i.castSucc + 1)).cube,
          MvPolynomial.eval
            (Fin.snoc (Fin.append x (fun j => j.elim0) ∘ Fin.cast (by omega)) r) curH := by
  unfold getSumcheckRoundPoly
  dsimp only
  -- Marginal identity (last-variable form): evaluating the survivor-sum of partial evaluations at
  -- `r` equals the survivor-sum of `curH_cast` with the last variable fixed to `r` (`Fin.snoc`).
  rw [Polynomial.eval_finset_sum]
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [← eval_eq_eval_mv_eval_finSuccEquivNth, Fin.insertNth_last']
  -- Reconcile `getSumcheckRoundPoly`'s internal `curH_cast` (an `Eq.mpr _ h.val`, `HEq` to `h.val`)
  -- with the supplied `curH` (also `HEq` to `h.val`).
  congr 1
  apply eq_of_heq
  refine HEq.trans ?_ hcurH.symm
  exact cast_heq _ _

end RoundPoly

section ProtocolSpec

variable (L : Type) [Semiring L]

/-- Protocol spec for one round of the structured sumcheck:
P sends a degree-≤`d` univariate `h_i(X) ∈ L⦃≤ d⦄[X]`; V samples a challenge `r'_i ∈ L`.
`d` is explicit (no privileged instantiation): the `H = P · t` case passes `d := 2`, Hachi's
smallness check passes `d := 2b+1`. -/
@[reducible]
def pSpecSumcheckRound (d : ℕ) : ProtocolSpec 2 :=
  ⟨![Direction.P_to_V, Direction.V_to_P], ![L⦃≤ d⦄[X], L]⟩

instance {d : ℕ} : ∀ j, OracleInterface ((pSpecSumcheckRound L d).Message j)
  | ⟨0, _⟩ => OracleInterface.instDefault -- h_i(X) polynomial
  | ⟨1, _⟩ => OracleInterface.instDefault -- challenge r'_i

variable [Fintype L] [DecidableEq L] [SampleableType L]

instance {d : ℕ} : ∀ j, SampleableType ((pSpecSumcheckRound L d).Challenge j)
  | ⟨0, h0⟩ => by nomatch h0
  | ⟨1, _⟩ => by
    simp only [Challenge, Fin.isValue, Matrix.cons_val_one, Matrix.cons_val_fin_one]
    infer_instance

end ProtocolSpec

/-! ## Single round of the structured sumcheck

The per-round prover/verifier/reduction (one round; the outer protocol iterates them via
`seqCompose`). Generic in:
- the underlying carrier `L` (anything `CommRing`),
- the protocol context `Context : Type` (Binius RingSwitching plugs in
  `RingSwitchingBaseContext κ L K ℓ`; Hachi will plug in its own),
- the external oracle statements `OStmtIn : ιₛᵢ → Type` (Binius plugs in
  `aOStmtIn.OStmtIn`).

The state machine has three states per round:
- `0`: before any messages — input statement + oracle product + witness.
- `1`: after P sends `h_i(X)` — adds the univariate.
- `2`: after V samples `r'_i` — adds the challenge.

The error bound `roundKnowledgeError` is the standard `2 / |L|`
Schwartz–Zippel bound; it doesn't depend on `Context` or `OStmtIn`. -/

section SingleRound

variable {L : Type} [CommRing L] [DecidableEq L] (ℓ : ℕ) [NeZero ℓ] (D : SumcheckDomain L ℓ)
variable (Context : Type) {ιₛᵢ : Type} {OStmtIn : ιₛᵢ → Type}
  [Oₛᵢ : ∀ j, OracleInterface (OStmtIn j)]
-- Round-polynomial degree bound. `d = 2` for the `H = P · t` case (Binius, ring-switching);
-- `d = 2b+1` for Hachi's degree-`2b` smallness combinator. Threaded explicitly (Lean `variable`
-- has no default), so callers pass `(d := 2)` / `(d := 2b+1)`.
variable (d : ℕ)

/-- State machine for the per-round prover of the structured sumcheck.
- `0`: pre-message.
- `1`: after the prover has sent `h_i(X)` (a degree-`d` univariate).
- `2`: after the verifier has sampled `r'_i`. -/
def roundPrvState (i : Fin ℓ) : Fin (2 + 1) → Type := fun
  -- Initial : current witness x t_eval_point x challenges
  | ⟨0, _⟩ => (Statement (L := L) (ℓ := ℓ) Context i.castSucc
    × (∀ j, OStmtIn j)) × SumcheckWitness L ℓ i.castSucc d
  -- After sending h_i(X)
  | ⟨1, _⟩ => Statement (L := L) (ℓ := ℓ) Context i.castSucc
    × (∀ j, OStmtIn j) × SumcheckWitness L ℓ i.castSucc d × L⦃≤ d⦄[X]
  -- After receiving r'_i
  | _ => Statement (L := L) (ℓ := ℓ) Context i.castSucc ×
    (∀ j, OStmtIn j) ×
    SumcheckWitness L ℓ i.castSucc d × L⦃≤ d⦄[X] × L

/-- Compute the final per-round output (statement-out, oracle statement-out, witness-out)
from the after-challenge prover state. -/
def getRoundProverFinalOutput (i : Fin ℓ)
    (finalPrvState : roundPrvState (L := L) ℓ Context (OStmtIn := OStmtIn) d i 2) :
    ((Statement (L := L) (ℓ := ℓ) Context i.succ
      × (∀ j, OStmtIn j)) × SumcheckWitness L ℓ i.succ d)
  := by
  let (stmtIn, oStmtIn, witIn, h_i, r_i') := finalPrvState
  let newSumcheckTarget : L := h_i.val.eval r_i'
  -- Challenges accumulate via `Fin.cons` (defect-#20 repair): the fresh challenge `r'` lands at
  -- index `0` of the `Fin i.succ` challenge vector, matching the `Fin.cons`-form round transition
  -- `fixFirstVariablesOfMQP_projectToMid_step` consumed by the structural invariant. The previous
  -- `Fin.snoc` form put `r'` at the LAST index, which is inconsistent with `projectToMid`'s
  -- end-consuming order (verified counterexample in `RingSwitching.Prelude`'s `RoundTransition`).
  let stmtOut : Statement (L := L) (ℓ := ℓ) Context i.succ := {
    ctx := stmtIn.ctx,
    sumcheck_target := newSumcheckTarget,
    challenges := Fin.cons r_i' stmtIn.challenges
  }
  let challenges : Fin 1 → L := fun _ => r_i'
  let witOut : SumcheckWitness L ℓ i.succ d := by
    let projectedH := fixFirstVariablesOfMQP (ℓ := ℓ - i) (v := ⟨1, by omega⟩)
      (H := witIn.H.val) (challenges := challenges)
    exact {
      t' := witIn.t',
      H := ⟨projectedH, by
        have hp := witIn.H.property
        simpa using
          (fixFirstVariablesOfMQP_degreeLE (L := L) (ℓ := ℓ - i) (v := ⟨1, by omega⟩)
            (poly := witIn.H.val) (challenges := challenges) (deg := d) hp)
      ⟩
    }
  exact ⟨⟨stmtOut, oStmtIn⟩, witOut⟩

/-- The prover for the `i`-th round of the structured sumcheck.

`sendMessage 0` runs `getSumcheckRoundPoly` to derive the degree-`d` univariate `h_i(X)` from
the round polynomial `H_i`. `receiveChallenge 1` stores the verifier's challenge `r'_i`.
`output` advances the witness via `getRoundProverFinalOutput`. -/
def roundOracleProver (i : Fin ℓ) :
    OracleProver (oSpec := []ₒ)
    (StmtIn := Statement (L := L) (ℓ := ℓ) Context i.castSucc)
    (OStmtIn := OStmtIn)
    (WitIn := SumcheckWitness L ℓ i.castSucc d)
    (StmtOut := Statement (L := L) (ℓ := ℓ) Context i.succ)
    (OStmtOut := OStmtIn)
    (WitOut := SumcheckWitness L ℓ i.succ d)
    (pSpec := pSpecSumcheckRound L d) where

  PrvState := roundPrvState (L := L) ℓ Context (OStmtIn := OStmtIn) d i

  input := fun ⟨⟨stmt, oStmt⟩, wit⟩ => ((stmt, oStmt), wit)

  sendMessage -- There are 2 messages in the pSpec
  | ⟨0, _⟩ => fun ⟨⟨stmt, oStmt⟩, wit⟩ => do
    let curH : ↥L⦃≤ d⦄[X Fin (ℓ - ↑i.castSucc)] := wit.H
    let h_i : L⦃≤ d⦄[X] := by
      exact getSumcheckRoundPoly ℓ D (i := i) curH
    pure ⟨h_i, (stmt, oStmt, wit, h_i)⟩
  | ⟨1, _⟩ => by contradiction

  receiveChallenge
  | ⟨0, h⟩ => nomatch h -- i.e. contradiction
  | ⟨1, _⟩ => fun ⟨stmt, oStmt, wit, h_i⟩ => do
    pure (fun r_i' => (stmt, oStmt, wit, h_i, r_i'))

  output := fun finalPrvState =>
    let res :=
      getRoundProverFinalOutput (L := L) ℓ Context (OStmtIn := OStmtIn) d i finalPrvState
    pure res

/-- The oracle verifier for the `i`-th round of the structured sumcheck.

Receives the degree-`d` univariate `h_i(X)` from the prover, checks
`s_i ?= ∑ b ∈ D.points i, h_i(b)` (summing the round polynomial over coordinate `i`'s evaluation
domain, to match how the prover builds it; for the boolean hypercube this is `h_i(0) + h_i(1)`),
samples `r'_i ∈ L`, and outputs the updated statement with `s_{i+1} := h_i(r'_i)`. -/
def roundOracleVerifier (i : Fin ℓ) :
    OracleVerifier
    (oSpec := []ₒ)
    (StmtIn := Statement (L := L) (ℓ := ℓ) Context i.castSucc)
    (OStmtIn := OStmtIn)
    (StmtOut := Statement (L := L) (ℓ := ℓ) Context i.succ)
    (OStmtOut := OStmtIn)
    (pSpec := pSpecSumcheckRound L d) where

  verify := fun stmtIn pSpecChallenges => do
    -- Message 0: receive h_i(X) from prover.
    let h_i : L⦃≤ d⦄[X] ← query (spec := [(pSpecSumcheckRound L d).Message]ₒ)
      ⟨⟨0, rfl⟩, ()⟩
    -- Sumcheck check: s_i ?= ∑_{b ∈ D.points i} h_i(b), summing the round polynomial over the
    -- evaluation domain of coordinate `i` (for the boolean hypercube this is `h_i(0) + h_i(1)`).
    let sumcheck_check := (∑ b ∈ D.points i, h_i.val.eval b) = stmtIn.sumcheck_target
    -- FAILURE-EMITTING VERIFIER (defect-#21 repair): on a failed check the verifier emits `failure`
    -- (`guard`, i.e. `OptionT` `none`) rather than a *dummy* accepting statement. Emitting a dummy
    -- let a maliciously-chosen dummy lie in `relOut` while the round-by-round KState local check is
    -- false, leaving the `toFun_full` REJECT branch unprovable (the dummy is reachable). With
    -- `guard`, the reject branch has no support element, so the REJECT branch is vacuous and the
    -- knowledge-soundness contract (verifier signals rejection, never forwards a fake statement)
    -- holds. Completeness only ever exercises the accept branch, so this does not weaken it.
    guard sumcheck_check
    -- Message 1: V samples r'_i and sends it to P.
    let r_i' : L := pSpecChallenges ⟨1, rfl⟩
    -- Challenges accumulate via `Fin.cons` (defect-#20 repair); see `getRoundProverFinalOutput`.
    let stmtOut : Statement (L := L) (ℓ := ℓ) Context i.succ := {
      ctx := stmtIn.ctx,
      sumcheck_target := h_i.val.eval r_i',
      challenges := Fin.cons r_i' stmtIn.challenges
    }
    pure stmtOut
  embed := ⟨fun j => Sum.inl j, fun a b h => by cases h; rfl⟩
  hEq := fun _ => rfl

/-- The oracle reduction bundling the per-round prover and verifier. -/
def roundOracleReduction (i : Fin ℓ) :
    OracleReduction (oSpec := []ₒ)
    (StmtIn := Statement (L := L) (ℓ := ℓ) Context i.castSucc)
    (OStmtIn := OStmtIn)
    (WitIn := SumcheckWitness L ℓ i.castSucc d)
    (StmtOut := Statement (L := L) (ℓ := ℓ) Context i.succ)
    (OStmtOut := OStmtIn)
    (WitOut := SumcheckWitness L ℓ i.succ d)
    (pSpec := pSpecSumcheckRound L d) where
  prover := roundOracleProver (L := L) ℓ D Context (OStmtIn := OStmtIn) d i
  verifier := roundOracleVerifier (L := L) ℓ D Context (OStmtIn := OStmtIn) d i

/-- The structured per-round oracle verifier routes every output oracle straight to the unchanged
input oracle (`embed = Sum.inl`, `OStmtIn = OStmtOut`, `hEq = rfl`) and exposes no message oracle,
so
its `AppendCoherent` coherence holds by `rfl`. Needed to `seqCompose` the rounds (e.g. for the
ring-switching/Binius sumcheck loops). -/
instance instRoundOracleVerifierAppendCoherent [Oₛ : ∀ i, OracleInterface (OStmtIn i)] (i : Fin ℓ) :
    OracleVerifier.Append.AppendCoherent
      (roundOracleVerifier (L := L) ℓ D Context (OStmtIn := OStmtIn) d i) where
  hCohInl := fun a k h => by
    have : a = k := by
      simpa only [roundOracleVerifier, Function.Embedding.coeFn_mk, Sum.inl.injEq] using h
    subst this; rfl
  hCohInr := fun a k h => by
    simp only [roundOracleVerifier, Function.Embedding.coeFn_mk, reduceCtorEq] at h

/-- The structured per-round oracle *reduction*'s verifier is definitionally `roundOracleVerifier`,
so it inherits `AppendCoherent`. -/
instance instRoundOracleReductionAppendCoherent [Oₛ : ∀ i, OracleInterface (OStmtIn i)] (i : Fin ℓ) :
    OracleVerifier.Append.AppendCoherent
      (roundOracleReduction (L := L) ℓ D Context (OStmtIn := OStmtIn) d i).verifier :=
  instRoundOracleVerifierAppendCoherent (L := L) ℓ D Context (OStmtIn := OStmtIn) d i

end SingleRound

section RoundError

variable (L : Type) [Fintype L] (ℓ : ℕ)

/-- Round-by-round knowledge error for a single round of the structured sumcheck:
the Schwartz–Zippel bound `d / |L|` for a degree-`d` round polynomial. `d` is explicit. -/
def roundKnowledgeError (_ : Fin ℓ) (d : ℕ) : NNReal := (d : NNReal) / (Fintype.card L)

end RoundError

end

end Sumcheck.Structured

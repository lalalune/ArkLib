/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.ProofSystem.Spartan.Composition
import ArkLib.ProofSystem.Spartan.SecondSumcheckComplete

/-!
# Spartan composed-completeness leaves (#114)

The per-phase perfect-completeness facts and the honest RLC-target adapter needed by the
8-fold composed-PC assembly for `composedPIOP_Rc` / `composedPIOPWithClaim_Rc`:

* `linearCombination_perfectCompleteness` — the `linearCombination` phase (verifier-only
  1-round challenge);
* `sendEvalClaim_perfectCompleteness` — the `sendEvalClaim` phase (prover-only forwarder of the
  bundled eval-claim oracle);
* `prependSlot_perfectCompleteness` (+ `prependTarget` / `prependClaim` instances) — the 0-round
  statement-reshaping adapters of `Composition.lean`;
* the **honest RLC-target adapter** `prependRLCTarget` (the D1 design fix): unlike `prependTarget`
  (whose carried second-sumcheck target is hardwired `0`, Composition.lean), its prover/verifier
  emit the honest RLC `∑ idx, r_lc(idx) · claims(idx)` read from the bundled eval-claim oracle, and
  `prependRLCTargetRelOut_subset_secondSumcheckRelIn` shows its output relation refines
  `secondSumcheckRelIn` — repairing the relation chain for the composed completeness fold.

The remaining leaf is the `finalCheck` (`CheckClaim`) phase completeness, handled separately.
-/

open MvPolynomial OracleComp OracleSpec OracleQuery OracleInterface ProtocolSpec

namespace Spartan.Spec

variable {R : Type} [CommRing R] [IsDomain R] [Fintype R] [DecidableEq R] [SampleableType R]
  [VCVCompatible R] (pp : Spartan.PublicParams) {ι : Type} (oSpec : OracleSpec ι)

/-- The `linearCombination` challenge `LinearCombinationChallenge R = R1CS.MatrixIdx → R` is a
`SampleableType` (nonempty `Fintype`). Mirrors `Bricks.instSampleableTypeLinearCombinationChallenge`
in `Composition.lean`; restated here so the standalone check resolves the challenge instance. -/
noncomputable instance instSampleableTypeLinearCombinationChallenge' :
    SampleableType (LinearCombinationChallenge R) :=
  SampleableType.ofFintype (R1CS.MatrixIdx → R)

/-- Outer input relation of the `linearCombination` phase: R1CS satisfiability, carried through. -/
def linearCombinationRelIn :
    Set ((Statement.AfterSendEvalClaim R pp ×
        (∀ i, OracleStatement.AfterSendEvalClaim R pp i)) × Unit) :=
  { x | R1CS.relation R pp.toSizeR1CS x.1.1.2.2
      (fun idx => x.1.2 (.inr (.inl idx))) (x.1.2 (.inr (.inr 0))) }

/-- Outer output relation of the `linearCombination` phase: the same R1CS satisfiability, carried
through (the LC challenge `r` is recorded but irrelevant to satisfiability). -/
def linearCombinationRelOut :
    Set ((Statement.AfterLinearCombination R pp ×
        (∀ i, OracleStatement.AfterLinearCombination R pp i)) × Unit) :=
  { x | R1CS.relation R pp.toSizeR1CS x.1.1.2.2.2
      (fun idx => x.1.2 (.inr (.inl idx))) (x.1.2 (.inr (.inr 0))) }

instance instLinearCombinationVerifierOnly :
    VerifierOnly (⟨!v[.V_to_P], !v[LinearCombinationChallenge R]⟩ : ProtocolSpec 1) where
  verifier_first' := by simp

set_option linter.unusedSimpArgs false in
omit [IsDomain R] [DecidableEq R] [SampleableType R] in
theorem linearCombination_perfectCompleteness
    {σ : Type} {init : ProbComp σ} {impl : QueryImpl oSpec (StateT σ ProbComp)} :
    (oracleReduction.linearCombination R pp oSpec).perfectCompleteness init impl
      (linearCombinationRelIn (R := R) pp) (linearCombinationRelOut (R := R) pp) := by
  simp only [OracleReduction.perfectCompleteness, oracleReduction.linearCombination,
    linearCombinationRelIn, linearCombinationRelOut]
  simp only [Reduction.perfectCompleteness_eq_prob_one]
  intro ⟨stmt, oStmt⟩ wit hRelIn
  simp only [OracleReduction.toReduction, Reduction.run,
    Prover.run_of_verifier_first, linearCombinationProver, linearCombinationVerifier,
    OracleVerifier.toVerifier, Verifier.run]
  simp_rw [show (pure : _ → OptionT (OracleComp _) _) = fun x => (pure (some x) :
    OracleComp _ _) from rfl]
  simp only [← OracleComp.liftComp_eq_liftM, OracleComp.liftComp_pure,
    pure_bind, bind_assoc]
  erw [simulateQ_bind]
  erw [simulateQ_bind]
  simp only [QueryImpl.addLift_def, simulateQ_pure,
    QueryImpl.simulateQ_add_liftComp_right, QueryImpl.simulateQ_add_liftComp_left,
    simulateQ_query,
    ← OracleComp.liftComp_eq_liftM, OracleComp.liftComp_pure,
    pure_bind, bind_assoc, map_pure, monadLift_pure, monadLift_bind]
  erw [simulateQ_bind]
  simp only [QueryImpl.addLift_def, simulateQ_pure,
    QueryImpl.simulateQ_add_liftComp_right, QueryImpl.simulateQ_add_liftComp_left,
    simulateQ_query,
    ← OracleComp.liftComp_eq_liftM, OracleComp.liftComp_pure,
    pure_bind, bind_assoc, map_pure, monadLift_pure, monadLift_bind,
    OptionT.run_mk, OptionT.run_pure, OptionT.run_bind, OptionT.run,
    Option.getM, Option.bind_some, Option.elimM,
    FullTranscript.challenges, FullTranscript.messages, ChallengeIdx, Challenge]
  erw [simulateQ_query]
  simp only [Fin.isValue, Fin.vcons_of_one, ChallengeIdx,
    Challenge, ofPFunctor_toPFunctor, QueryImpl.liftTarget_self, MessageIdx,
    Message, bind_map_left, StateT.run'_eq, StateT.run_bind, map_bind, OptionT.mk_bind,
    Set.mem_setOf_eq, probEvent_eq_one_iff, probFailure_bind_eq_zero_iff,
    OptionT.probFailure_liftM, HasEvalPMF.probFailure_eq_zero, OptionT.support_liftM,
    Prod.forall, true_and, support_bind, Set.mem_iUnion, OptionT.mem_support_iff,
    OptionT.run_mk, support_map, Set.mem_image, Prod.exists, exists_and_right,
    exists_eq_right, exists_prop, forall_exists_index, and_imp, Prod.mk.injEq]
  constructor <;> intro <;> intro <;> intro <;> intro
  all_goals try erw [simulateQ_bind]
  all_goals simp only [MonadLift.monadLift, liftM, monadLift, MonadLiftT.monadLift]
  all_goals simp only [OracleComp.liftComp_pure, QueryImpl.simulateQ_add_liftComp_left,
    simulateQ_pure, simulateQ_id', pure_bind, bind_assoc, map_pure, monadLift_pure,
    OptionT.run_mk, OptionT.run_pure, OptionT.run_bind, OptionT.run,
    StateT.run'_eq, probFailure_eq_zero,
    support_pure, Set.mem_singleton_iff, Prod.eq_iff_fst_eq_snd_eq]
  all_goals try erw [simulateQ_pure]
  all_goals try simp_all only [simulateQ_pure, pure_bind, map_pure,
    OptionT.run_mk, OptionT.run_pure, OptionT.run_bind, OptionT.run,
    StateT.run'_eq, StateT.run_pure, probFailure_eq_zero,
    support_pure, support_map, Set.mem_singleton_iff, Set.mem_image,
    OptionT.probFailure_eq, probOutput_pure]
  · erw [simulateQ_bind, simulateQ_pure]
    simp only [pure_bind]
    erw [simulateQ_pure]
    simp [map_pure, OptionT.mk, probFailure_pure]
  · intro trFull lc fsc fc x1 oOut wOut lc2 fsc2 fc2 x2 oOut2 sI hsI rng
    erw [simulateQ_bind] at rng
    simp only [liftComp_eq_liftM, pure_bind, simulateQ_pure, OptionT.lift,
      OptionT.run_mk, map_pure] at rng
    erw [simulateQ_pure] at rng
    simp only [pure_bind, simulateQ_pure, support_pure, StateT.run, StateT.run',
      Set.mem_singleton_iff, Prod.mk.injEq] at rng
    obtain ⟨⟨⟨rfl, rfl⟩, rfl⟩, rfl⟩ := rng
    refine ⟨?_, ⟨rfl, rfl, rfl, rfl⟩, ?_⟩
    · simpa only [Set.mem_setOf_eq] using hRelIn
    · funext i
      rcases i with j | j <;> rfl

end Spartan.Spec

-- Axiom check
#print axioms Spartan.Spec.linearCombination_perfectCompleteness

open OracleComp OracleSpec ProtocolSpec OracleInterface Function

namespace Spartan.Spec

variable (R : Type) [CommRing R] [IsDomain R] [Fintype R] (pp : PublicParams)
variable {ι : Type} (oSpec : OracleSpec ι)
variable [SampleableType R]
variable {σ : Type} (init : ProbComp σ) (impl : QueryImpl oSpec (StateT σ ProbComp))

/-- Output relation for `sendEvalClaim` parameterized on an arbitrary input relation `relIn`
on `(AfterFirstSumcheck × OStmt) × Unit`. It holds for an output statement-oracle pair iff
(1) the underlying input pair (recovering the input oracle family from the `.inr` part of the
output oracle family) lies in `relIn`, and
(2) the bundled eval-claim oracle (`.inl 0`) equals the honest `evalClaimValue`. -/
@[reducible]
def sendEvalClaimRelOut
    (relIn : Set ((Statement.AfterFirstSumcheck R pp ×
        (∀ i, OracleStatement.AfterFirstSumcheck R pp i)) × Unit)) :
    Set ((Statement.AfterSendEvalClaim R pp ×
        (∀ i, OracleStatement.AfterSendEvalClaim R pp i)) × Unit) :=
  { x | ((x.1.1, fun j => x.1.2 (.inr j)), ()) ∈ relIn ∧
        x.1.2 (.inl 0) = evalClaimValue R pp x.1.1 (fun j => x.1.2 (.inr j)) }

set_option maxHeartbeats 1000000 in
omit [IsDomain R] [Fintype R] [SampleableType R] in
/-- The `sendEvalClaim` oracle reduction satisfies perfect completeness: from any input relation
`relIn`, it lands in `sendEvalClaimRelOut relIn`. The honest prover forwards the input oracles and
sends the bundled eval-claim `evalClaimValue`; the verifier performs no check, so the relation
pass-through and the eval-claim honesty are deterministic. -/
theorem sendEvalClaim_perfectCompleteness
    (relIn : Set ((Statement.AfterFirstSumcheck R pp ×
        (∀ i, OracleStatement.AfterFirstSumcheck R pp i)) × Unit)) :
    (oracleReduction.sendEvalClaim R pp oSpec).perfectCompleteness init impl
      relIn (sendEvalClaimRelOut R pp relIn) := by
  simp only [OracleReduction.perfectCompleteness, Reduction.perfectCompleteness,
    Reduction.completeness, Reduction.completenessFromRun, ENNReal.coe_zero, tsub_zero]
  intro ⟨stmt, oStmt⟩ wit hIn
  have _inst : ProverOnly (⟨!v[.P_to_V], !v[∀ i, EvalClaim R i]⟩ : ProtocolSpec 1) :=
    { prover_first' := by simp }
  simp only [OracleReduction.toReduction, oracleReduction.sendEvalClaim]
  rw [Reduction.run_of_prover_first]
  simp only [sendEvalClaimProver, sendEvalClaimVerifier, liftM_pure, pure_bind,
    bind_pure_comp, OracleVerifier.toVerifier]
  erw [simulateQ_pure]
  simp only [map_pure, StateT.run'_eq, StateT.run_pure]
  rw [ge_iff_le, one_le_probEvent_iff, probEvent_eq_one_iff]
  refine ⟨?_, ?_⟩
  · -- `probFailure = 0`: a `ProbComp` (`OracleComp unifSpec`) cannot fail and the appended
    -- `pure (some ·)` is total, so the failure probability is structurally zero.
    rw [OptionT.probFailure_eq, OptionT.run_mk]
    simp
  · intro x hx
    rw [OptionT.mem_support_iff, OptionT.run_mk] at hx
    simp only [support_bind, support_pure, Set.mem_iUnion, Set.mem_singleton_iff] at hx
    obtain ⟨s, _, hx⟩ := hx
    cases hx
    refine ⟨?_, ?_⟩
    · refine ⟨?_, ?_⟩
      · -- relation pass-through: input pair recovered from `.inr` part lands in `relIn`
        convert hIn using 2
      · -- eval-claim honesty: `.inl 0` slot equals the honest `evalClaimValue`
        rfl
    · -- prover output statement equals verifier output statement
      refine Prod.ext rfl ?_
      funext i
      rcases i with j | j <;> rfl

#print axioms sendEvalClaim_perfectCompleteness

end Spartan.Spec

open OracleComp OracleInterface ProtocolSpec Function

namespace Spartan.Spec.Bricks

noncomputable section

open scoped NNReal

variable (R : Type) [CommRing R] [IsDomain R] [Fintype R] [DecidableEq R] (pp : PublicParams)
variable {ι : Type} (oSpec : OracleSpec ι) [SampleableType R]
variable {ιₛ : Type}

/-- Output relation of a `prependSlot` step: input predicate with the prepended `(0,·)` stripped. -/
def prependSlotRelOut (Stmt : Type) (OStmt : ιₛ → Type) [∀ i, OracleInterface (OStmt i)]
    (rel : Set ((Stmt × (∀ i, OStmt i)) × Unit)) :
    Set (((R × Stmt) × (∀ i, OStmt i)) × Unit) :=
  { x | ((x.1.1.2, x.1.2), x.2) ∈ rel }

/-- The deterministic run of `prependSlot` is a single `pure` prepending `0`. -/
theorem prependSlot_run (Stmt : Type) (OStmt : ιₛ → Type) [∀ i, OracleInterface (OStmt i)]
    (stmt : Stmt) (oStmt : ∀ i, OStmt i) :
    (prependSlot (R := R) oSpec Stmt OStmt).toReduction.run (stmt, oStmt) () =
      (pure (((default : (!p[] : ProtocolSpec 0).FullTranscript),
               (((0 : R), stmt), oStmt), ()), (((0 : R), stmt), oStmt)) :
        OptionT (OracleComp _) _) := by
  simp only [prependSlot, prependSlotProver, prependSlotVerifier, OracleReduction.toReduction,
    Reduction.run, Prover.run, Verifier.run, OracleVerifier.toVerifier]
  simp only [map_pure, bind_pure_comp, liftM_pure, Option.map_some, Option.getM, Option.bind_some]
  rfl

/-- **prependSlot is perfectly complete.** (0-round adapter; deterministic, no queries.) -/
theorem prependSlot_perfectCompleteness (Stmt : Type) (OStmt : ιₛ → Type)
    [∀ i, OracleInterface (OStmt i)] {σ} {init : ProbComp σ}
    {impl : QueryImpl oSpec (StateT σ ProbComp)}
    (rel : Set ((Stmt × (∀ i, OStmt i)) × Unit)) :
    (prependSlot (R := R) oSpec Stmt OStmt).perfectCompleteness init impl
      rel (prependSlotRelOut R Stmt OStmt rel) := by
  unfold OracleReduction.perfectCompleteness
  simp only [Reduction.perfectCompleteness, Reduction.completeness, Reduction.completenessFromRun,
    ENNReal.coe_zero, tsub_zero]
  intro ⟨stmt, oStmt⟩ ⟨⟩ hIn
  simp only [prependSlot_run]
  rw [ge_iff_le, one_le_probEvent_iff, probEvent_eq_one_iff]
  refine ⟨?_, ?_⟩
  · rw [OptionT.probFailure_eq, OptionT.run_mk]
    simp only [probFailure_eq_zero, zero_add]
    apply probOutput_eq_zero_of_not_mem_support
    simp only [support_bind, Set.mem_iUnion, not_exists]
    intro s _
    change none ∈ _root_.support (StateT.run' (simulateQ _
        (pure (some (((default : (!p[] : ProtocolSpec 0).FullTranscript),
          (((0 : R), stmt), oStmt), ()), (((0 : R), stmt), oStmt))) : OracleComp _ _)) s) → False
    rw [simulateQ_pure]
    change none ∈ _root_.support (Prod.fst <$>
      (pure (some (((default : (!p[] : ProtocolSpec 0).FullTranscript),
        (((0 : R), stmt), oStmt), ()), (((0 : R), stmt), oStmt))) :
        StateT σ ProbComp _).run s) → False
    rw [StateT.run_pure]; simp [map_pure]
  · intro x hx
    rw [OptionT.mem_support_iff] at hx
    simp only [OptionT.run_mk, support_bind, Set.mem_iUnion] at hx
    obtain ⟨s, _, hx⟩ := hx
    change some x ∈ _root_.support (StateT.run' (simulateQ _
        (pure (some (((default : (!p[] : ProtocolSpec 0).FullTranscript),
          (((0 : R), stmt), oStmt), ()), (((0 : R), stmt), oStmt))) : OracleComp _ _)) s) at hx
    rw [simulateQ_pure] at hx
    change some x ∈ _root_.support (Prod.fst <$>
      (pure (some (((default : (!p[] : ProtocolSpec 0).FullTranscript),
        (((0 : R), stmt), oStmt), ()), (((0 : R), stmt), oStmt))) :
        StateT σ ProbComp _).run s) at hx
    rw [StateT.run_pure] at hx
    simp only [_root_.map_pure, _root_.support_pure, Set.mem_singleton_iff,
      Option.some.injEq, Prod.mk.injEq] at hx
    cases hx
    simp only [prependSlotRelOut, Set.mem_setOf_eq]
    exact ⟨hIn, trivial⟩

/-- **prependTarget is perfectly complete** (linearCombination→secondSumcheck adapter). -/
theorem prependTarget_perfectCompleteness {σ} {init : ProbComp σ}
    {impl : QueryImpl oSpec (StateT σ ProbComp)}
    (rel : Set ((Statement.AfterLinearCombination R pp ×
      (∀ i, OracleStatement.AfterLinearCombination R pp i)) × Unit)) :
    (prependTarget (R := R) pp oSpec).perfectCompleteness init impl
      rel (prependSlotRelOut R _ _ rel) :=
  prependSlot_perfectCompleteness R oSpec _ _ rel

/-- **prependClaim is perfectly complete** (terminal finalCheck→FinalClaimStatement adapter). -/
theorem prependClaim_perfectCompleteness {σ} {init : ProbComp σ}
    {impl : QueryImpl oSpec (StateT σ ProbComp)}
    (rel : Set ((FinalStatement R pp × (∀ i, FinalOracleStatement R pp i)) × Unit)) :
    (prependClaim (R := R) pp oSpec).perfectCompleteness init impl
      rel (prependSlotRelOut R _ _ rel) :=
  prependSlot_perfectCompleteness R oSpec _ _ rel

end

#print axioms prependSlot_perfectCompleteness
#print axioms prependTarget_perfectCompleteness
#print axioms prependClaim_perfectCompleteness

end Spartan.Spec.Bricks

open OracleComp OracleInterface ProtocolSpec Function
open MvPolynomial OracleComp Sumcheck
open scoped NNReal

namespace Spartan.Spec.Bricks

variable {R : Type} [CommRing R] [IsDomain R] [Fintype R] [DecidableEq R] [SampleableType R]
  (pp : Spartan.PublicParams) {ι : Type} (oSpec : OracleSpec ι)

/-! ## D1: honest RLC-target adapter `prependRLCTarget` (Spartan #114) -/

/-- The 0-round honest **RLC-target** oracle prover: emits the honest RLC
`∑ idx, r idx · v_idx` (reading the bundled eval-claim oracle `.inl 0` and the LC coefficients
`stmt.1`). Honest replacement for `prependSlotProver` (whose carried target is `0`). -/
noncomputable def prependRLCTargetProver :
    OracleProver oSpec
      (Statement.AfterLinearCombination R pp) (OracleStatement.AfterLinearCombination R pp) Unit
      (R × Statement.AfterLinearCombination R pp)
      (OracleStatement.AfterLinearCombination R pp) Unit !p[] where
  PrvState := fun _ =>
    Statement.AfterLinearCombination R pp ×
      (∀ i, OracleStatement.AfterLinearCombination R pp i)
  input := Prod.fst
  sendMessage := fun i => nomatch i
  receiveChallenge := fun i => nomatch i
  output := fun st =>
    pure (((∑ idx, st.1.1 idx * st.2 (.inl 0) idx, st.1), st.2), ())

/-- Direct combined-spec query of the bundled claim oracle `.inl 0` at index `idx`. -/
noncomputable def queryClaimDirect (idx : R1CS.MatrixIdx) :
    OracleComp (oSpec + ([OracleStatement.AfterLinearCombination R pp]ₒ
      + [(!p[] : ProtocolSpec 0).Message]ₒ)) R :=
  (OracleComp.lift <| OracleSpec.query
    (spec := oSpec + ([OracleStatement.AfterLinearCombination R pp]ₒ
      + [(!p[] : ProtocolSpec 0).Message]ₒ))
    (show (oSpec + ([OracleStatement.AfterLinearCombination R pp]ₒ
      + [(!p[] : ProtocolSpec 0).Message]ₒ)).Domain from
        Sum.inr (Sum.inl ⟨.inl 0, ⟨idx, ()⟩⟩)) :
    OracleComp _ R)

/-- The per-index step of the RLC verifier: query the claim oracle, return `(idx, v)`. -/
noncomputable def rlcStep (idx : R1CS.MatrixIdx) :
    OptionT (OracleComp (oSpec + ([OracleStatement.AfterLinearCombination R pp]ₒ
      + [(!p[] : ProtocolSpec 0).Message]ₒ))) (R1CS.MatrixIdx × R) := do
  let v ← liftM (queryClaimDirect pp oSpec idx)
  pure (idx, v)

/-- The honest RLC-target verifier: queries the bundled claim oracle for each matrix index and
emits `(∑ idx, r idx · v_idx, stmt)`. -/
noncomputable def prependRLCTargetVerifier :
    OracleVerifier oSpec
      (Statement.AfterLinearCombination R pp) (OracleStatement.AfterLinearCombination R pp)
      (R × Statement.AfterLinearCombination R pp)
      (OracleStatement.AfterLinearCombination R pp) !p[] where
  verify := fun stmt _ => do
    let claims ← (liftM ((Finset.univ : Finset R1CS.MatrixIdx).toList.mapM (rlcStep pp oSpec)) :
      OptionT (OracleComp _) (List (R1CS.MatrixIdx × R)))
    let rlc : R := (claims.map (fun p => stmt.1 p.1 * p.2)).sum
    pure (rlc, stmt)
  embed := Embedding.inl
  hEq := by intro i; simp

/-- The honest RLC-target oracle reduction (drop-in replacement for `prependTarget`). -/
noncomputable def prependRLCTarget :
    OracleReduction oSpec
      (Statement.AfterLinearCombination R pp) (OracleStatement.AfterLinearCombination R pp) Unit
      (R × Statement.AfterLinearCombination R pp)
      (OracleStatement.AfterLinearCombination R pp) Unit !p[] where
  prover := prependRLCTargetProver pp oSpec
  verifier := prependRLCTargetVerifier pp oSpec

instance instPrependRLCTargetVerifierAppendCoherent :
    OracleVerifier.Append.AppendCoherent (prependRLCTargetVerifier (R := R) pp oSpec) where
  hCohInl i k h := by
    simp only [prependRLCTargetVerifier, Function.Embedding.inl_apply] at h
    obtain rfl := Sum.inl.inj h
    rfl
  hCohInr i k h := by
    simp only [prependRLCTargetVerifier, Function.Embedding.inl_apply] at h
    cases h

/-! ### Output relation and the D1 inclusion fix -/

/-- **Output relation of the honest RLC-target adapter.** R1CS satisfiability carried through, the
bundled claim oracle `.inl 0` holds the honest `evalClaimValue` (the `sendEvalClaim` guarantee), and
the carried target equals the *stored* RLC `∑ idx, r idx · oStmt(.inl 0) idx`. -/
def prependRLCTargetRelOut :
    Set (((R × Statement.AfterLinearCombination R pp) ×
        (∀ i, OracleStatement.AfterLinearCombination R pp i)) × Unit) :=
  { x | R1CS.relation R pp.toSizeR1CS x.1.1.2.2.2.2
          (fun idx => x.1.2 (.inr (.inl idx))) (x.1.2 (.inr (.inr 0)))
        ∧ (∀ idx, x.1.2 (.inl 0) idx =
            evalClaimValue R pp x.1.1.2.2 (fun i => x.1.2 (.inr i)) idx)
        ∧ x.1.1.1 = ∑ idx, x.1.1.2.1 idx * x.1.2 (.inl 0) idx }

omit [IsDomain R] [Fintype R] [DecidableEq R] [SampleableType R] in
/-- **D1 key inclusion: the honest RLC-target output relation refines `secondSumcheckRelIn`.**
The stored-RLC carried target (`∑ r idx · oStmt(.inl 0) idx`) equals the `evalClaimValue`-RLC
required by `secondSumcheckRelIn`, once the bundled claim oracle holds the honest `evalClaimValue`.
This is the set-level fix for the `prependTarget` target-`0` mismatch (Composition.lean:109). -/
theorem prependRLCTargetRelOut_subset_secondSumcheckRelIn :
    prependRLCTargetRelOut (R := R) pp ⊆ secondSumcheckRelIn (R := R) pp := by
  rintro x ⟨hR1CS, hEval, ht⟩
  refine ⟨hR1CS, ?_⟩
  rw [ht]
  refine Finset.sum_congr rfl fun idx _ => ?_
  rw [hEval idx]

/-! ### Honest-run simulation of the RLC-target verifier -/

omit [IsDomain R] [Fintype R] [DecidableEq R] [SampleableType R] in
/-- A single claim-oracle query, simulated against the true oracle, returns the stored claim. -/
theorem simulateQ_queryClaimDirect
    (oStmt : ∀ i, OracleStatement.AfterLinearCombination R pp i)
    (msgs : ∀ i, (!p[] : ProtocolSpec 0).Message i) (idx : R1CS.MatrixIdx) :
    simulateQ (OracleInterface.simOracle2 oSpec oStmt msgs) (queryClaimDirect pp oSpec idx)
      = pure (oStmt (.inl 0) idx) := by
  unfold queryClaimDirect OracleInterface.simOracle2
  rw [simulateQ_query]
  simp only [QueryImpl.addLift_def, QueryImpl.id,
    OracleQuery.input_query, OracleQuery.cont_query,
    QueryImpl.add_apply_inr, QueryImpl.liftTarget_apply, simOracle0,
    OracleInterface.answer, _root_.map_pure, id_eq, liftM_pure]
  rfl

omit [IsDomain R] [Fintype R] [DecidableEq R] [SampleableType R] in
/-- One verifier step, simulated against the true oracle, returns `pure (some (idx, claim idx))`. -/
theorem simulateQ_rlcStep
    (oStmt : ∀ i, OracleStatement.AfterLinearCombination R pp i)
    (msgs : ∀ i, (!p[] : ProtocolSpec 0).Message i) (idx : R1CS.MatrixIdx) :
    simulateQ (OracleInterface.simOracle2 oSpec oStmt msgs)
      (rlcStep pp oSpec idx : OracleComp _ (Option (R1CS.MatrixIdx × R)))
      = (pure (some (idx, oStmt (.inl 0) idx))) := by
  show simulateQ (OracleInterface.simOracle2 oSpec oStmt msgs)
      ((liftM (queryClaimDirect pp oSpec idx) >>= fun v =>
        (pure (idx, v) : OptionT (OracleComp _) (R1CS.MatrixIdx × R))) :
        OptionT (OracleComp _) (R1CS.MatrixIdx × R)).run = _
  rw [simulateQ_optionT_bind']
  rw [show ((liftM (queryClaimDirect pp oSpec idx) :
      OptionT (OracleComp _) R)) = OptionT.lift (queryClaimDirect pp oSpec idx) from rfl]
  simp only [OptionT.run, simulateQ_optionT_lift, simulateQ_queryClaimDirect,
    OptionT.lift, OptionT.mk, simulateQ_bind, simulateQ_pure, bind_assoc, pure_bind, map_pure]
  rfl

omit [IsDomain R] [SampleableType R] in
/-- The honest RLC-target verifier, simulated against the true oracle, deterministically emits
`(∑ idx, r idx · oStmt(.inl 0) idx, stmt)`. -/
theorem simulateQ_prependRLCTargetVerifier
    (stmt : Statement.AfterLinearCombination R pp)
    (oStmt : ∀ i, OracleStatement.AfterLinearCombination R pp i)
    (msgs : ∀ i, (!p[] : ProtocolSpec 0).Message i)
    (chals : (!p[] : ProtocolSpec 0).Challenges) :
    simulateQ (OracleInterface.simOracle2 oSpec oStmt msgs)
      ((prependRLCTargetVerifier (R := R) pp oSpec).verify stmt chals
        : OracleComp _ (Option (R × Statement.AfterLinearCombination R pp)))
      = pure (some (∑ idx, stmt.1 idx * oStmt (.inl 0) idx, stmt)) := by
  show simulateQ (OracleInterface.simOracle2 oSpec oStmt msgs)
      ((liftM ((Finset.univ : Finset R1CS.MatrixIdx).toList.mapM (rlcStep pp oSpec)) >>=
        fun claims => (pure ((claims.map (fun p => stmt.1 p.1 * p.2)).sum, stmt) :
          OptionT (OracleComp _) (R × Statement.AfterLinearCombination R pp))) :
        OptionT (OracleComp _) (R × Statement.AfterLinearCombination R pp)).run = _
  rw [simulateQ_optionT_bind']
  rw [show ((liftM ((Finset.univ : Finset R1CS.MatrixIdx).toList.mapM (rlcStep pp oSpec)) :
      OptionT (OracleComp _) (List (R1CS.MatrixIdx × R)))) =
      ((Finset.univ : Finset R1CS.MatrixIdx).toList.mapM (rlcStep pp oSpec)) from rfl]
  erw [simulateQ_optionT_list_mapM_pure (OracleInterface.simOracle2 oSpec oStmt msgs)
      (rlcStep pp oSpec)
      (fun idx => ((idx, oStmt (.inl 0) idx) : R1CS.MatrixIdx × R)) _
      (fun idx => simulateQ_rlcStep pp oSpec oStmt msgs idx)]
  simp only [OptionT.run_pure, simulateQ_pure]
  refine Eq.trans (pure_bind _ _) (congrArg (fun z => pure (some (z, stmt))) ?_)
  rw [List.map_map,
    ← Finset.sum_map_toList Finset.univ (fun idx => stmt.1 idx * oStmt (.inl 0) idx)]
  rfl

#print axioms prependRLCTargetProver
#print axioms prependRLCTargetVerifier
#print axioms prependRLCTarget
#print axioms instPrependRLCTargetVerifierAppendCoherent
#print axioms prependRLCTargetRelOut_subset_secondSumcheckRelIn
#print axioms simulateQ_prependRLCTargetVerifier

end Spartan.Spec.Bricks

import ArkLib.ProofSystem.Stir.VectorChainCompleteness

/-!
# Issue #301 (STIR): the CHECKED final-block verifier + perfect completeness

`Stir/ChainProof.lean`'s `stirChainProof` packages the full vectorised STIR chain with the
always-`true` placeholder decision (`OracleReduction.toProof (fun _ => true)`). The WHIR
precedent (`Whir/CheckedVerifier.lean`) upgraded the placeholder by replacing the pure-`true`
verifier with one making REAL oracle queries. This file mirrors it for STIR's final
`[p, C_fin]` block:

* `stirFinalVectorVerifierChecked` — the final-block verifier that QUERIES the in-the-clear
  final word (the slot-0 prover message oracle) at the index determined by the repetition
  challenge, queries the incoming packed oracle at the same index, and accepts iff they agree
  (rejection = `OptionT` failure).
* The honest prover sends its incoming oracle AS the final word
  (`stirFinalVectorProverMid.sendMessage ⟨0,_⟩ = pure ⟨st.1.2 (), …⟩`), so the check holds
  BY CONSTRUCTION on the honest run.
* `stirFinalVectorReductionChecked_perfectCompleteness` — perfect completeness of the upgraded
  final block (the mirror of `stirFinalVectorReductionMid_perfectCompleteness`, with the new
  correctness leg discharging the check via the honest-prover equation).
-/

namespace StirIOP

namespace Round3

open OracleSpec OracleComp ProtocolSpec STIR ReedSolomon NNReal StirIOP.Round OracleReduction
open WhirIOP.Construction (packFiniteFunction unpackFiniteFunction unpack_packFiniteFunction)

set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false

variable {F : Type} [Field F] [Fintype F] [DecidableEq F] [SampleableType F]
variable {ι : Type} [Fintype ι] [DecidableEq ι] [Nonempty ι]

/-- A field is `VCVCompatible` (finite + inhabited via `0`); the `RoundVectorCompleteness`
idiom. -/
local instance : VCVCompatible F := { toFintype := inferInstance, toInhabited := ⟨0⟩ }

/-! ### The real check: query index, oracle queries, the checking computation -/

/-- **The query index determined by the repetition challenge**: the challenge field element is
mapped to a position of the packed final word (via the canonical enumeration of `F`, reduced
mod `|ι|`). -/
noncomputable def stirFinalQueryIndex (c : F) : Fin (Fintype.card ι) :=
  ⟨(Fintype.equivFin F c) % Fintype.card ι, Nat.mod_lt _ Fintype.card_pos⟩

/-- The repetition challenge `C_fin` read off its `Vector F 1` payload (the typed accessor:
the slot-1 challenge of the final vector spec IS a length-1 vector, definitionally). -/
def stirRepChallenge
    (chals : ((stirFinalVSpec ι F).toProtocolSpec F).Challenges) : Vector F 1 :=
  chals ⟨1, stirFinalVSpec_dir_one⟩

/-- The repetition-challenge field element. -/
def stirRepChallengePoint
    (chals : ((stirFinalVSpec ι F).toProtocolSpec F).Challenges) : F :=
  (stirRepChallenge chals).get 0

/-- Query the in-the-clear final word (the slot-0 prover message oracle) at position `k`. -/
noncomputable def askFinalWord (k : Fin (Fintype.card ι)) :
    OracleComp ([]ₒ + ([VOStmt ι F]ₒ +
      [((stirFinalVSpec ι F).toProtocolSpec F).Message]ₒ)) F :=
  liftM (OracleSpec.query
    (spec := [((stirFinalVSpec ι F).toProtocolSpec F).Message]ₒ)
    (⟨⟨0, stirFinalVSpec_dir_zero⟩, k⟩ :
      (Σ j, OracleInterface.Query (((stirFinalVSpec ι F).toProtocolSpec F).Message j))))

/-- Query the incoming packed oracle at position `k`. -/
noncomputable def askIncoming (k : Fin (Fintype.card ι)) :
    OracleComp ([]ₒ + ([VOStmt ι F]ₒ +
      [((stirFinalVSpec ι F).toProtocolSpec F).Message]ₒ)) F :=
  liftM (OracleSpec.query
    (spec := [VOStmt ι F]ₒ)
    (⟨(), k⟩ : (Σ i, OracleInterface.Query (VOStmt ι F i))))

/-- The honest answer of the final-word message oracle at position `k` (ascribed at `F`). -/
noncomputable def stirFinalWordAt
    (msgs : ∀ j, ((stirFinalVSpec ι F).toProtocolSpec F).Message j)
    (k : Fin (Fintype.card ι)) : F :=
  OracleInterface.answer (msgs ⟨0, stirFinalVSpec_dir_zero⟩) k

/-- The honest answer of the incoming packed oracle at position `k` (ascribed at `F`). -/
noncomputable def stirIncomingAt
    (oStmt : ∀ i, VOStmt ι F i) (k : Fin (Fintype.card ι)) : F :=
  OracleInterface.answer (oStmt ()) k

/-- **The checking computation of the final block** (underlying `Option`-valued computation of
the `OptionT` verifier): read the repetition challenge, query the final word AND the incoming
packed oracle at the index it determines, and accept (returning the output statement
`(pending randomness, repetition challenge)`) iff the two values agree. -/
noncomputable def stirFinalCheckedComp (r : F)
    (chals : ((stirFinalVSpec ι F).toProtocolSpec F).Challenges) :
    OracleComp ([]ₒ + ([VOStmt ι F]ₒ +
      [((stirFinalVSpec ι F).toProtocolSpec F).Message]ₒ)) (Option (F × F)) := do
  let vWord ← askFinalWord (stirFinalQueryIndex (stirRepChallengePoint chals))
  let vIn ← askIncoming (stirFinalQueryIndex (stirRepChallengePoint chals))
  if vWord = vIn
  then pure (some (r, stirRepChallengePoint chals))
  else pure none

/-- **The pure value of the checking computation** under the honest oracle implementation. -/
noncomputable def stirFinalCheckedAns
    (oStmt : ∀ i, VOStmt ι F i)
    (msgs : ∀ j, ((stirFinalVSpec ι F).toProtocolSpec F).Message j)
    (r : F) (chals : ((stirFinalVSpec ι F).toProtocolSpec F).Challenges) : Option (F × F) :=
  if stirFinalWordAt msgs (stirFinalQueryIndex (stirRepChallengePoint chals))
      = stirIncomingAt oStmt (stirFinalQueryIndex (stirRepChallengePoint chals))
  then some (r, stirRepChallengePoint chals)
  else none

/-! ### `simulateQ` collapse -/

/-- `simulateQ` collapse for the final-word query. -/
theorem simulateQ_askFinalWord
    (oStmt : ∀ i, VOStmt ι F i)
    (msgs : ∀ j, ((stirFinalVSpec ι F).toProtocolSpec F).Message j)
    (k : Fin (Fintype.card ι)) :
    simulateQ (OracleInterface.simOracle2 []ₒ oStmt msgs) (askFinalWord k)
      = (pure (stirFinalWordAt msgs k) : OracleComp []ₒ F) := rfl

/-- `simulateQ` collapse for the incoming-oracle query. -/
theorem simulateQ_askIncoming
    (oStmt : ∀ i, VOStmt ι F i)
    (msgs : ∀ j, ((stirFinalVSpec ι F).toProtocolSpec F).Message j)
    (k : Fin (Fintype.card ι)) :
    simulateQ (OracleInterface.simOracle2 []ₒ oStmt msgs) (askIncoming k)
      = (pure (stirIncomingAt oStmt k) : OracleComp []ₒ F) := rfl

/-- **Central collapse**: under the honest oracle implementation, the checking computation is
the pure computation of `stirFinalCheckedAns` (for ARBITRARY oracle/message values). -/
theorem simulateQ_stirFinalCheckedComp
    (oStmt : ∀ i, VOStmt ι F i)
    (msgs : ∀ j, ((stirFinalVSpec ι F).toProtocolSpec F).Message j)
    (r : F) (chals : ((stirFinalVSpec ι F).toProtocolSpec F).Challenges) :
    simulateQ (OracleInterface.simOracle2 []ₒ oStmt msgs) (stirFinalCheckedComp r chals)
      = (pure (stirFinalCheckedAns oStmt msgs r chals) : OracleComp []ₒ (Option (F × F))) := by
  unfold stirFinalCheckedComp stirFinalCheckedAns
  rw [simulateQ_bind, simulateQ_askFinalWord, pure_bind, simulateQ_bind, simulateQ_askIncoming,
    pure_bind]
  split <;> rw [simulateQ_pure]

/-! ### The honest prover passes the check BY CONSTRUCTION -/

/-- **The honest-transcript check lemma**: if the slot-0 final word IS the incoming packed
oracle (which is what `stirFinalVectorProverMid` sends, by construction), the checking decision
accepts and outputs `(pending randomness, repetition challenge)` — for EVERY challenge. -/
theorem stirFinalCheckedAns_honest
    (oStmt : ∀ i, VOStmt ι F i)
    (msgs : ∀ j, ((stirFinalVSpec ι F).toProtocolSpec F).Message j)
    (hmsg : msgs ⟨0, stirFinalVSpec_dir_zero⟩ = oStmt ())
    (r : F) (chals : ((stirFinalVSpec ι F).toProtocolSpec F).Challenges) :
    stirFinalCheckedAns oStmt msgs r chals
      = some (r, stirRepChallengePoint chals) := by
  have hcond : stirFinalWordAt msgs (stirFinalQueryIndex (stirRepChallengePoint chals))
      = stirIncomingAt oStmt (stirFinalQueryIndex (stirRepChallengePoint chals)) := by
    unfold stirFinalWordAt stirIncomingAt
    rw [hmsg]
    rfl
  unfold stirFinalCheckedAns
  rw [if_pos hcond]

/-- The final-word answer of an all-`c` (replicated) message family is `c`. -/
theorem stirFinalWordAt_replicate (c : F) (k : Fin (Fintype.card ι)) :
    stirFinalWordAt (F := F) (ι := ι)
      (fun j => Vector.replicate ((stirFinalVSpec ι F).length j.1) c) k = c := by
  show (Vector.replicate ((stirFinalVSpec ι F).length 0) c)[(k : ℕ)] = c
  exact Vector.getElem_replicate _

/-- The incoming-oracle answer of an all-`c` (replicated) packed oracle is `c`. -/
theorem stirIncomingAt_replicate (c : F) (k : Fin (Fintype.card ι)) :
    stirIncomingAt (F := F) (ι := ι)
      (fun _ => Vector.replicate (Fintype.card ι) c) k = c := by
  show (Vector.replicate (Fintype.card ι) c)[(k : ℕ)] = c
  exact Vector.getElem_replicate _

/-- **Non-vacuousness**: there are final words the checking verifier REJECTS (the all-zeros
incoming oracle against the all-ones final word), so the upgraded verifier is genuinely not
the always-accept placeholder. -/
theorem exists_stirFinalCheckedAns_eq_none :
    ∃ (oStmt : ∀ i, VOStmt ι F i)
      (msgs : ∀ j, ((stirFinalVSpec ι F).toProtocolSpec F).Message j)
      (r : F) (chals : ((stirFinalVSpec ι F).toProtocolSpec F).Challenges),
      stirFinalCheckedAns oStmt msgs r chals = none := by
  refine ⟨fun _ => Vector.replicate (Fintype.card ι) 0,
    fun j => Vector.replicate ((stirFinalVSpec ι F).length j.1) 1,
    0, fun i => Vector.replicate ((stirFinalVSpec ι F).length i.1) 0, ?_⟩
  unfold stirFinalCheckedAns
  rw [stirFinalWordAt_replicate, stirIncomingAt_replicate, if_neg one_ne_zero]

/-! ### The checked final-block verifier and reduction -/

/-- **The CHECKED mid-chain vectorised final verifier** (the upgrade of
`stirFinalVectorVerifierMid`): instead of accepting unconditionally, it queries the
in-the-clear final word at the index determined by the repetition challenge, queries the
incoming packed oracle at the same index, and accepts iff they agree (rejection = `OptionT`
failure). Same wire interface and output-oracle routing as the placeholder verifier. -/
noncomputable def stirFinalVectorVerifierChecked :
    OracleVerifier []ₒ F (VOStmt ι F) (F × F) (VOStmt ι F)
      ((stirFinalVSpec ι F).toProtocolSpec F) where
  verify := fun r chals => OptionT.mk (stirFinalCheckedComp r chals)
  embed := ⟨fun _ => Sum.inr ⟨0, stirFinalVSpec_dir_zero⟩, fun _ _ _ => rfl⟩
  hEq := fun _ => rfl

/-- **The CHECKED mid-chain vectorised final block** (`VOStmt → VOStmt`): the honest
`stirFinalVectorProverMid` against the checking verifier. -/
noncomputable def stirFinalVectorReductionChecked :
    OracleReduction []ₒ F (VOStmt ι F) Unit (F × F) (VOStmt ι F) Unit
      ((stirFinalVSpec ι F).toProtocolSpec F) where
  prover := stirFinalVectorProverMid
  verifier := stirFinalVectorVerifierChecked

instance instStirFinalVectorVerifierCheckedAppendCoherent :
    OracleVerifier.Append.AppendCoherent
      (stirFinalVectorVerifierChecked (ι := ι) (F := F)) where
  hCohInl := fun i k h => by
    exact absurd h (by simp [stirFinalVectorVerifierChecked])
  hCohInr := fun i k h => by
    have hk : k = ⟨0, stirFinalVSpec_dir_zero⟩ := by
      have := h.symm
      simp only [stirFinalVectorVerifierChecked, Function.Embedding.coeFn_mk] at this
      exact (Sum.inr.inj this)
    subst hk
    apply eq_of_heq
    refine HEq.trans ?_ (cast_heq _ _).symm
    rfl

instance instStirFinalVectorReductionCheckedAppendCoherent :
    OracleVerifier.Append.AppendCoherent
      (stirFinalVectorReductionChecked (ι := ι) (F := F)).verifier :=
  instStirFinalVectorVerifierCheckedAppendCoherent

/-! ### `simulateQ` collapse at the `OptionT` layer + the transcript-level honest lemma -/

/-- `simulateQ` collapse of the checked verify computation at the `OptionT` layer. -/
theorem simulateQ_optionT_stirFinalCheckedComp
    (oStmt : ∀ i, VOStmt ι F i)
    (msgs : ∀ j, ((stirFinalVSpec ι F).toProtocolSpec F).Message j)
    (r : F) (chals : ((stirFinalVSpec ι F).toProtocolSpec F).Challenges) :
    (simulateQ (OracleInterface.simOracle2 []ₒ oStmt msgs)
        (OptionT.mk (stirFinalCheckedComp r chals)) : OptionT (OracleComp []ₒ) (F × F))
      = OptionT.mk (pure (stirFinalCheckedAns oStmt msgs r chals)) := by
  show (simulateQ (OracleInterface.simOracle2 []ₒ oStmt msgs)
      (stirFinalCheckedComp r chals) : OracleComp []ₒ (Option (F × F)))
    = pure (stirFinalCheckedAns oStmt msgs r chals)
  exact simulateQ_stirFinalCheckedComp oStmt msgs r chals

/-- **The transcript-level honest-check lemma**: on the honest transcript — whose slot-0 final
word IS the incoming packed oracle, by construction of `stirFinalVectorProverMid` — the checked
verifier's full `toVerifier.verify` computation collapses to the `pure` output
`((pending randomness, repetition challenge), final-word oracle)`: the check PASSES. -/
theorem stirFinalVectorVerifierChecked_toVerifier_honest
    (stmtIn : F) (oStmtIn : ∀ i, VOStmt ι F i) (r1 : Vector F 1) :
    (stirFinalVectorVerifierChecked (ι := ι) (F := F)).toVerifier.verify (stmtIn, oStmtIn)
      (FullTranscript.mk2 (oStmtIn ()) r1)
      = pure ((stmtIn, r1.get 0), fun _ : Unit => oStmtIn ()) := by
  have h1 : (stirFinalVectorVerifierChecked (ι := ι) (F := F)).toVerifier.verify
      (stmtIn, oStmtIn) (FullTranscript.mk2 (oStmtIn ()) r1)
      = ((do
          let s ← (simulateQ (OracleInterface.simOracle2 []ₒ oStmtIn
                (FullTranscript.mk2 (oStmtIn ()) r1).messages)
              (OptionT.mk (stirFinalCheckedComp stmtIn
                (FullTranscript.mk2 (oStmtIn ()) r1).challenges))
              : OptionT (OracleComp []ₒ) (F × F))
          pure (s, fun _ : Unit => oStmtIn ()))
        : OptionT (OracleComp []ₒ) ((F × F) × ∀ i, VOStmt ι F i)) := rfl
  rw [h1, simulateQ_optionT_stirFinalCheckedComp,
    stirFinalCheckedAns_honest oStmtIn _ rfl]
  rfl

/-! ### Perfect completeness of the CHECKED final block -/

variable {σ : Type} (init : ProbComp σ) (impl : QueryImpl []ₒ (StateT σ ProbComp))

/-- Spec-lifting an `OptionT`-level `pure` is `pure` (definitional; the WHIR
`CheckedVerifier` helper). -/
private lemma liftComp_optionT_pure {ι₁ ι₂ : Type} {spec₁ : OracleSpec ι₁}
    {spec₂ : OracleSpec ι₂} [MonadLiftT (OracleQuery spec₁) (OracleQuery spec₂)]
    {α : Type} (y : α) :
    (OracleComp.liftComp (pure y : OptionT (OracleComp spec₁) α) spec₂ :
      OptionT (OracleComp spec₂) α) = pure y := rfl

/-- Defeq-extraction helper: membership of `v` in the `OptionT`-level support of the
`pure y >>= fun a => pure (some a)` computation (the shape the support-image simp leaves
behind, with the monad type degraded to `FreeM` form where no instance synthesis fires)
forces `v = y`. Stated via `OptionT.mk` so the inner bind elaborates at the `OracleComp`
level and application to the degraded hypothesis is a pure defeq cast. -/
private lemma eq_of_mem_support_optionT_pure_bind_some {ιx : Type} {spec : OracleSpec ιx}
    {β : Type} {y v : β}
    (h : v ∈ support (OptionT.mk
      ((pure y : OracleComp spec β) >>= fun a => pure (some a)))) : v = y := by
  have h' : some v ∈ support ((pure (some y)) : OracleComp spec (Option β)) := h
  simpa using h'

open scoped Classical in
set_option maxHeartbeats 1600000 in
/-- **Perfect completeness of the CHECKED mid-chain vectorised final `[p, C_fin]` block**
(`VOStmt → VOStmt`): the honest prover sends its incoming packed oracle in the clear as the
final word, so the checked verifier's query comparison
`finalWord[k] = incomingOracle[k]` holds BY CONSTRUCTION at every index — the new correctness
leg discharges the real check via the honest-prover equation
(`stirFinalCheckedAns_honest` + the transcript-level
`stirFinalVectorVerifierChecked_toVerifier_honest`), and the vector proximity relation
transfers verbatim, exactly as in `stirFinalVectorReductionMid_perfectCompleteness`. -/
theorem stirFinalVectorReductionChecked_perfectCompleteness (φ : ι ↪ F) (deg : ℕ) (δ : ℝ≥0)
    (hInit : NeverFail init) :
    OracleReduction.perfectCompleteness init impl
      (stirVOStmtRel F φ deg δ) (stirVOStmtRel (F × F) φ deg δ)
      (stirFinalVectorReductionChecked (ι := ι) (F := F)) := by
  rw [OracleReduction.unroll_2_message_reduction_perfectCompleteness
    (stirFinalVectorReductionChecked (ι := ι) (F := F))
    (stirVOStmtRel F φ deg δ) (stirVOStmtRel (F × F) φ deg δ) init impl hInit
    (by rfl) (by rfl)
    (by simp only [Set.fmap_eq_image, IsEmpty.forall_iff, implies_true])]
  intro stmtIn oStmtIn witIn h_relIn
  dsimp only [stirFinalVectorReductionChecked, stirFinalVectorProverMid, VOStmt, stirVOStmtRel]
  simp only [Fin.isValue, bind_pure_comp, pure_bind, bind_map_left, liftM_bind, liftM_map,
    Prod.mk.eta, bind_assoc, map_pure, liftComp_pure, liftM_pure, id_eq]
  simp only [stirFinalVectorVerifierChecked_toVerifier_honest]
  rw [probEvent_eq_one_iff]
  refine ⟨?_, ?_⟩
  · -- SAFETY: the run never fails (the check PASSES on the honest transcript)
    rw [probFailure_bind_eq_zero_iff]
    refine ⟨?_, fun α _hα => ?_⟩
    · simp only [probFailure_map, OptionT.probFailure_liftM, OptionT.probFailure_lift,
        _root_.probFailure_liftComp, HasEvalPMF.probFailure_eq_zero]
    · rw [probFailure_map, OptionT.probFailure_liftComp_of_OracleComp_Option]
      simp only [OptionT.run_pure, probFailure_pure, probOutput_pure, reduceCtorEq,
        if_false, add_zero, zero_add]
  · -- CORRECTNESS: the unique reachable output accepts and agrees (the check PASSED on the
    -- honest transcript, so the verifier's output is the deterministic `pure` value)
    intro x hx
    simp only [support_bind, Set.mem_iUnion, exists_prop] at hx
    obtain ⟨α, _hα, hx⟩ := hx
    rw [liftComp_optionT_pure] at hx
    simp only [OptionT.run_map, OptionT.run_pure, _root_.map_pure, Function.comp_apply,
      support_map, support_pure, Set.mem_image, Set.mem_singleton_iff,
      exists_eq_left, exists_eq_right] at hx
    obtain ⟨v, hv, hxx⟩ := hx
    have hveq := eq_of_mem_support_optionT_pure_bind_some hv
    subst hveq
    subst hxx
    exact ⟨h_relIn, rfl, rfl⟩

end Round3

end StirIOP

#print axioms StirIOP.Round3.simulateQ_stirFinalCheckedComp
#print axioms StirIOP.Round3.stirFinalCheckedAns_honest
#print axioms StirIOP.Round3.exists_stirFinalCheckedAns_eq_none
#print axioms StirIOP.Round3.stirFinalVectorVerifierChecked
#print axioms StirIOP.Round3.stirFinalVectorReductionChecked
#print axioms StirIOP.Round3.instStirFinalVectorReductionCheckedAppendCoherent
#print axioms StirIOP.Round3.simulateQ_optionT_stirFinalCheckedComp
#print axioms StirIOP.Round3.stirFinalVectorVerifierChecked_toVerifier_honest
#print axioms StirIOP.Round3.stirFinalVectorReductionChecked_perfectCompleteness

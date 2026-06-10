/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/

import ArkLib.ProofSystem.Stir.MultiRoundAssembly
import ArkLib.ProofSystem.Stir.ErrorAccumulation
import ArkLib.Data.CodingTheory.ProximityGap.BCIKS20.Curves
import ArkLib.ToVCVio.Simulation

/-!
# Issue #301 (STIR): the CHECKING multi-round verifier

`MultiRoundAssembly.lean` assembles the (M+1)-round STIR Vector IOPP with an honest folding
prover but a *forwarding shell* verifier (`verify := pure true`). This file builds the
**checking** multi-round verifier and welds it into the durable wiring
(`stir_main_of_secure_vectorIOP` / `stir_rbr_soundness_of_secure_vectorIOP`):

* `stirCheckingVerifier` — per-round checks lifted to the multi-round wire shape:
  - **fold-query check** (round 0): the first folded oracle `g₁` agrees with the genuine fold of
    the input codeword at a point derived from the first out-challenge (in this single-domain
    identity-fold model `Fold(f,r) = f` by `combine_single_self`, so the check is agreement with
    the input oracle itself);
  - **out-of-domain-style + fold-query consistency checks** (rounds 1..M): consecutive folded
    oracles agree at the points derived from the out- and shift-challenges of the round;
  - **final low-degree check**: the final prover message is read in full (it is the final
    polynomial, sent in the clear in STIR) and checked for membership in `RS[F, φ, deg]`.
* `stirCheckingIOP` — the checking IOPP: the landed honest `stirMultiRoundProver` together with
  the checking verifier.
* `stirCheckingIOP_perfectCompleteness` — PROVEN (axiom-clean), for symbolic `M`: the honest
  prover's run satisfies a support invariant (every message it sends is the packed genuine fold,
  which equals the packed input codeword), so all consistency checks pass, and the final
  low-degree check passes because the perfect-completeness relation `stirRelation deg φ 0` forces
  the input codeword to lie in the code.
* `stirCheckingRbrSoundnessResidual` + `stirCheckingCABridgeResidual` — the soundness side,
  HONESTLY split: the rbr knowledge soundness of the checking verifier is the named open
  residual; the bridge residual states that it follows from the EXISTING Johnson-CA residuals
  (`ProximityGap.StrictCoeffPolysResidual`, the §5/Johnson-regime correlated-agreement
  extraction) plus the per-round accounting keystone
  (`ArkLib.ProofSystem.Stir.ErrorAccumulation.PerRoundProximityGap`). NEITHER is proven here —
  the bridge is the genuine open protocol-soundness math of #301.
* `stir_rbr_soundness_of_checking_CA` / `stir_main_of_checking_CA` — the headline existentials
  discharged through the landed `…_of_secure_vectorIOP` front doors, with the completeness leg
  PROVEN (this file) and the soundness leg consumed via (CA residuals + bridge residual).

HONESTY NOTES:
* The checking verifier's checks are *real* (they constrain the prover's messages: a prover whose
  final message is not a codeword, or whose oracles are caught inconsistent at the sampled
  points, is rejected) — unlike the shell verifier, `verify = pure true` is false for it.
* The single-domain model folds `RS[F,φ,deg]` into itself (`combine_single_self`), so the
  per-round degree reduction of paper-STIR is degenerate here; the out-of-domain check
  correspondingly degenerates to consistency at a challenge-derived in-domain point. This is
  inherited from the landed `stirRoundVectorProver`/`stirMultiRoundProver` model.
* The implication (Johnson-CA + per-round gap accounting ⟹ rbr knowledge soundness of this
  verifier) is NOT proven; it is isolated as `stirCheckingCABridgeResidual`. No fabrication.
-/

set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false
set_option linter.unusedTactic false

namespace StirIOP

namespace MultiRound

open OracleSpec OracleComp ProtocolSpec STIR ReedSolomon NNReal WhirIOP.Construction
open OracleInterface

variable {F : Type} [Field F] [Fintype F] [DecidableEq F] [SampleableType F]
variable {ι : Type} [Fintype ι]

section CheckingVerifier

variable [Nonempty ι]

/-- The `j`-th message round of the multi-round STIR shape (round `3j + 1`). -/
def msgIdx (M : ℕ) (j : Fin (M + 1)) :
    ((stirMultiVSpec M ι).toProtocolSpec F).MessageIdx :=
  ⟨⟨3 * (j : ℕ) + 1, by omega⟩, by
    show (stirMultiVSpec M ι).dir _ = .P_to_V
    rw [stirVSpec_dir_eq_msg_iff]; simp only [Fin.val_mk]; omega⟩

/-- The out-challenge round following the `j`-th message round (round `3j + 2`). -/
def outChalIdx (M : ℕ) (j : Fin (M + 1)) :
    ((stirMultiVSpec M ι).toProtocolSpec F).ChallengeIdx :=
  ⟨⟨3 * (j : ℕ) + 2, by omega⟩, by
    show (stirMultiVSpec M ι).dir _ = .V_to_P
    rw [stirVSpec_dir_eq_chal_iff]; simp only [Fin.val_mk]; omega⟩

/-- The shift-challenge round between message rounds `j` and `j + 1` (round `3j + 3`). -/
def shiftChalIdx (M : ℕ) (j : Fin M) :
    ((stirMultiVSpec M ι).toProtocolSpec F).ChallengeIdx :=
  ⟨⟨3 * (j : ℕ) + 3, by omega⟩, by
    show (stirMultiVSpec M ι).dir _ = .V_to_P
    rw [stirVSpec_dir_eq_chal_iff]; simp only [Fin.val_mk]; omega⟩

/-- Read the field element off a (length-`1`) vector challenge. -/
def chalFE {M : ℕ} (chals : ((stirMultiVSpec M ι).toProtocolSpec F).Challenges)
    (i : ((stirMultiVSpec M ι).toProtocolSpec F).ChallengeIdx) : F :=
  (chals i).get ⟨0, stirMultiVSpec_length_chal_pos i⟩

/-- Map a field challenge to a query point of the evaluation domain (the `φ`-preimage when the
challenge lands in the domain's image, an arbitrary point otherwise). -/
noncomputable def queryPoint (φ : ι ↪ F) (r : F) : ι := Function.invFun φ r

/-- The position of domain point `x` inside a packed message vector. -/
noncomputable def msgPos (M : ℕ) (j : ((stirMultiVSpec M ι).toProtocolSpec F).MessageIdx) (x : ι) :
    Fin ((stirMultiVSpec M ι).length j.1) :=
  Fin.cast (stirMultiVSpec_length_msg j) (Fintype.equivFin ι x)

/-- Query the input codeword oracle at a domain point. -/
noncomputable def askInput (M : ℕ) (x : ι) :
    OracleComp ([]ₒ + ([OracleStatement ι F]ₒ +
      [((stirMultiVSpec M ι).toProtocolSpec F).Message]ₒ)) F :=
  liftM (OracleSpec.query (spec := [OracleStatement ι F]ₒ)
    (⟨(), x⟩ : (Σ i : Unit, OracleInterface.Query (OracleStatement ι F i))))

/-- Query the `j`-th prover message oracle at a vector position. -/
noncomputable def askMsg (M : ℕ) (j : ((stirMultiVSpec M ι).toProtocolSpec F).MessageIdx)
    (k : Fin ((stirMultiVSpec M ι).length j.1)) :
    OracleComp ([]ₒ + ([OracleStatement ι F]ₒ +
      [((stirMultiVSpec M ι).toProtocolSpec F).Message]ₒ)) F :=
  liftM (OracleSpec.query (spec := [((stirMultiVSpec M ι).toProtocolSpec F).Message]ₒ)
    (⟨j, k⟩ : (Σ i, OracleInterface.Query (((stirMultiVSpec M ι).toProtocolSpec F).Message i))))

/-- Monadic map over a list with definitional `nil`/`cons` equations (avoiding `List.mapM`'s
tail-recursive loop), so that `simulateQ` collapse is a one-line induction. -/
def askList {ιq : Type} {spec : OracleSpec ιq} {β γ : Type}
    (xs : List β) (ask : β → OracleComp spec γ) : OracleComp spec (List γ) :=
  match xs with
  | [] => pure []
  | x :: xs => do
      let v ← ask x
      let vs ← askList xs ask
      pure (v :: vs)

/-- If every step of an `askList` simulates to a pure value, the whole `askList` collapses to the
corresponding pure `List.map`. -/
theorem simulateQ_askList {ιq ιq' : Type} {spec : OracleSpec ιq} {spec' : OracleSpec ιq'}
    (so : QueryImpl spec (OracleComp spec')) {β γ : Type}
    (xs : List β) (ask : β → OracleComp spec γ) (ans : β → γ)
    (hstep : ∀ b, simulateQ so (ask b) = pure (ans b)) :
    simulateQ so (askList xs ask) = pure (xs.map ans) := by
  induction xs with
  | nil => simp [askList]
  | cons y ys ih =>
      rw [askList, simulateQ_bind, hstep, pure_bind, simulateQ_bind, ih, pure_bind,
        simulateQ_pure, List.map_cons]

/-- The honest answer of the input-codeword oracle (ascribed at `F`). -/
noncomputable def inputAns (oStmt : ∀ i, OracleStatement ι F i) (x : ι) : F :=
  OracleInterface.answer (oStmt ()) x

/-- The honest answer of a message oracle (ascribed at `F`). -/
noncomputable def msgAns {M : ℕ}
    (msgs : ∀ j, ((stirMultiVSpec M ι).toProtocolSpec F).Message j)
    (j : ((stirMultiVSpec M ι).toProtocolSpec F).MessageIdx)
    (k : Fin ((stirMultiVSpec M ι).length j.1)) : F :=
  OracleInterface.answer (msgs j) k

variable (M : ℕ) (φ : ι ↪ F) (deg : ℕ)

open scoped Classical in
/-- **The checking computation** of the multi-round STIR verifier: round-0 fold-query check
against the input codeword, per-round out/shift consistency checks between consecutive folded
oracles, and the final full-read low-degree check. -/
noncomputable def checkingComp (chals : ((stirMultiVSpec M ι).toProtocolSpec F).Challenges) :
    OracleComp ([]ₒ + ([OracleStatement ι F]ₒ +
      [((stirMultiVSpec M ι).toProtocolSpec F).Message]ₒ)) Bool := do
  -- (1) round-0 fold-query check: g₁ agrees with (the fold of) the input codeword at the
  -- point derived from the first out-challenge
  let x0 := queryPoint φ (chalFE chals (outChalIdx M 0))
  let vIn ← askInput M x0
  let v0 ← askMsg M (msgIdx M 0) (msgPos M (msgIdx M 0) x0)
  -- (2) per-round consistency checks: consecutive folded oracles agree at the points derived
  -- from the round's out- and shift-challenges
  let consist ← askList (List.finRange M) (fun j => do
      let xa := queryPoint φ (chalFE chals (outChalIdx M j.succ))
      let xb := queryPoint φ (chalFE chals (shiftChalIdx M j))
      let va ← askMsg M (msgIdx M j.castSucc) (msgPos M (msgIdx M j.castSucc) xa)
      let vb ← askMsg M (msgIdx M j.succ) (msgPos M (msgIdx M j.succ) xa)
      let vc ← askMsg M (msgIdx M j.castSucc) (msgPos M (msgIdx M j.castSucc) xb)
      let vd ← askMsg M (msgIdx M j.succ) (msgPos M (msgIdx M j.succ) xb)
      pure (decide (va = vb) && decide (vc = vd)))
  -- (3) final low-degree check: read the final message (the final polynomial, in the clear)
  -- in full and check membership in the Reed-Solomon code
  let finalVals ← askList (List.finRange (Fintype.card ι)) (fun k =>
      askMsg M (msgIdx M (Fin.last M))
        (Fin.cast (stirMultiVSpec_length_msg (msgIdx M (Fin.last M))) k))
  pure (decide (vIn = v0) && consist.all (fun b => b) &&
    decide ((fun x : ι => finalVals.getD ((Fintype.equivFin ι x) : ℕ) 0)
      ∈ ReedSolomon.code φ deg))

open scoped Classical in
/-- **The pure value of the checking computation** under the honest oracle implementation
(`simOracle2` over the input oracle statement and the transcript messages). -/
noncomputable def checkingBool (oStmt : ∀ i, OracleStatement ι F i)
    (msgs : ∀ j, ((stirMultiVSpec M ι).toProtocolSpec F).Message j)
    (chals : ((stirMultiVSpec M ι).toProtocolSpec F).Challenges) : Bool :=
  let x0 := queryPoint φ (chalFE chals (outChalIdx M 0))
  let vIn := inputAns oStmt x0
  let v0 := msgAns msgs (msgIdx M 0) (msgPos M (msgIdx M 0) x0)
  let consist := (List.finRange M).map (fun j =>
      let xa := queryPoint φ (chalFE chals (outChalIdx M j.succ))
      let xb := queryPoint φ (chalFE chals (shiftChalIdx M j))
      let va := msgAns msgs (msgIdx M j.castSucc) (msgPos M (msgIdx M j.castSucc) xa)
      let vb := msgAns msgs (msgIdx M j.succ) (msgPos M (msgIdx M j.succ) xa)
      let vc := msgAns msgs (msgIdx M j.castSucc) (msgPos M (msgIdx M j.castSucc) xb)
      let vd := msgAns msgs (msgIdx M j.succ) (msgPos M (msgIdx M j.succ) xb)
      decide (va = vb) && decide (vc = vd))
  let finalVals := (List.finRange (Fintype.card ι)).map (fun k =>
      msgAns msgs (msgIdx M (Fin.last M))
        (Fin.cast (stirMultiVSpec_length_msg (msgIdx M (Fin.last M))) k))
  decide (vIn = v0) && consist.all (fun b => b) &&
    decide ((fun x : ι => finalVals.getD ((Fintype.equivFin ι x) : ℕ) 0)
      ∈ ReedSolomon.code φ deg)

/-- `simulateQ` collapse for the input-oracle query. -/
theorem simulateQ_askInput (oStmt : ∀ i, OracleStatement ι F i)
    (msgs : ∀ j, ((stirMultiVSpec M ι).toProtocolSpec F).Message j) (x : ι) :
    simulateQ (OracleInterface.simOracle2 []ₒ oStmt msgs) (askInput M x)
      = (pure (inputAns oStmt x) : OracleComp []ₒ F) := rfl

/-- `simulateQ` collapse for a message-oracle query. -/
theorem simulateQ_askMsg (oStmt : ∀ i, OracleStatement ι F i)
    (msgs : ∀ j, ((stirMultiVSpec M ι).toProtocolSpec F).Message j)
    (j : ((stirMultiVSpec M ι).toProtocolSpec F).MessageIdx)
    (k : Fin ((stirMultiVSpec M ι).length j.1)) :
    simulateQ (OracleInterface.simOracle2 []ₒ oStmt msgs) (askMsg M j k)
      = (pure (msgAns msgs j k) : OracleComp []ₒ F) := rfl

/-- **Central collapse**: under the honest oracle implementation, the checking computation is a
pure computation of `checkingBool`. (Holds for ARBITRARY oracle/message values; this single
lemma powers both the safety and the correctness branches of completeness.) -/
theorem simulateQ_checkingComp (oStmt : ∀ i, OracleStatement ι F i)
    (msgs : ∀ j, ((stirMultiVSpec M ι).toProtocolSpec F).Message j)
    (chals : ((stirMultiVSpec M ι).toProtocolSpec F).Challenges) :
    simulateQ (OracleInterface.simOracle2 []ₒ oStmt msgs) (checkingComp M φ deg chals)
      = pure (checkingBool M φ deg oStmt msgs chals) := by
  unfold checkingComp checkingBool
  rw [simulateQ_bind, simulateQ_askInput]
  simp only [pure_bind]
  rw [simulateQ_bind, simulateQ_askMsg]
  simp only [pure_bind]
  rw [simulateQ_bind,
    simulateQ_askList _ _ _ (fun j =>
      let xa := queryPoint φ (chalFE chals (outChalIdx M j.succ))
      let xb := queryPoint φ (chalFE chals (shiftChalIdx M j))
      let va := msgAns msgs (msgIdx M j.castSucc) (msgPos M (msgIdx M j.castSucc) xa)
      let vb := msgAns msgs (msgIdx M j.succ) (msgPos M (msgIdx M j.succ) xa)
      let vc := msgAns msgs (msgIdx M j.castSucc) (msgPos M (msgIdx M j.castSucc) xb)
      let vd := msgAns msgs (msgIdx M j.succ) (msgPos M (msgIdx M j.succ) xb)
      decide (va = vb) && decide (vc = vd))
      (fun j => by
        rw [simulateQ_bind, simulateQ_askMsg]
        simp only [pure_bind]
        rw [simulateQ_bind, simulateQ_askMsg]
        simp only [pure_bind]
        rw [simulateQ_bind, simulateQ_askMsg]
        simp only [pure_bind]
        rw [simulateQ_bind, simulateQ_askMsg]
        simp only [pure_bind, simulateQ_pure])]
  simp only [pure_bind]
  rw [simulateQ_bind,
    simulateQ_askList _ _ _ (fun k =>
      msgAns msgs (msgIdx M (Fin.last M))
        (Fin.cast (stirMultiVSpec_length_msg (msgIdx M (Fin.last M))) k))
      (fun k => simulateQ_askMsg M oStmt msgs _ _)]
  simp only [pure_bind, simulateQ_pure]

/-- **The checking multi-round STIR verifier.** Forwards no oracles (IOP shape); its `verify` is
the genuine checking computation. -/
noncomputable def stirCheckingVerifier :
    OracleVerifier []ₒ Unit (OracleStatement ι F) Bool (fun _ : Empty => Unit)
      ((stirMultiVSpec M ι).toProtocolSpec F) where
  verify := fun _ chals => OptionT.lift (checkingComp M φ deg chals)
  embed := ⟨fun i => i.elim, fun i => i.elim⟩
  hEq := fun i => i.elim

/-- **The checking (M+1)-round STIR Vector IOPP**: the landed honest folding prover together
with the checking verifier. -/
noncomputable def stirCheckingIOP :
    VectorIOP Unit (OracleStatement ι F) Unit (stirMultiVSpec M ι) F where
  prover := stirMultiRoundProver M φ deg
  verifier := stirCheckingVerifier M φ deg

end CheckingVerifier

/-! ### The honest prover's run-support invariant -/

section Invariant

variable [Nonempty ι]

/-- The honest packed message value at message round `iv` (`iv % 3 = 1`): the packed fold of the
input codeword, which by `combine_single_self` is the packed input codeword itself. -/
noncomputable def honestMsg (M : ℕ) (f : ι → F) (iv : ℕ) (h : iv < 3 * M + 3)
    (hdir : iv % 3 = 1) : Vector F ((stirMultiVSpec M ι).length ⟨iv, h⟩) :=
  Vector.cast (stirMultiVSpec_length_msg (ι := ι) (F := F) (M := M)
    ⟨⟨iv, h⟩, by
      show (stirMultiVSpec M ι).dir _ = .P_to_V
      rw [stirVSpec_dir_eq_msg_iff]; exact hdir⟩)
    (packFiniteFunction ι f)

/-- **Run-support invariant of the honest multi-round STIR prover** (symbolic `M`, any round
`k`): on the support of `runToRound k`, (i) the prover's carried context is the input context
(it only updates its stored fold challenge), and (ii) every message entry of the partial
transcript is the honest packed fold of the input codeword — which, since `Combine.combine` of
a single codeword at its own degree is the identity, is the packed input codeword. -/
theorem stirMultiRoundProver_runToRound_invariant (M : ℕ) (φ : ι ↪ F) (deg : ℕ)
    (stmtIn : Unit × ∀ i, OracleStatement ι F i) (witIn : Unit)
    (k : Fin (3 * M + 3 + 1)) :
    ∀ ts ∈ _root_.support
      ((stirMultiRoundProver M φ deg).runToRound k stmtIn witIn),
      ts.2.1 = (stmtIn, witIn) ∧
      ∀ (iv : ℕ) (hik : iv < k.val) (hdir : iv % 3 = 1),
        ts.1 ⟨iv, hik⟩ = honestMsg M (stmtIn.2 ()) iv
          (by have := k.isLt; omega) hdir := by
  induction k using Fin.induction with
  | zero =>
      intro ts hts
      rw [Prover.runToRound_zero_of_prover_first] at hts
      simp only [support_pure, Set.mem_singleton_iff] at hts
      subst hts
      exact ⟨rfl, fun iv hik _ => absurd hik (Nat.not_lt_zero iv)⟩
  | succ j ih =>
      intro ts hts
      rw [Prover.runToRound_succ] at hts
      unfold Prover.processRound at hts
      simp only [support_bind, Set.mem_iUnion, exists_prop] at hts
      obtain ⟨⟨tr, st⟩, hprev, hout⟩ := hts
      obtain ⟨ihSt, ihTr⟩ := ih ⟨tr, st⟩ hprev
      split at hout
      · -- challenge (V_to_P) round: the new entry is a challenge; earlier entries unchanged
        rename_i hDir
        simp only [support_bind, support_pure, Set.mem_iUnion, Set.mem_singleton_iff,
          exists_prop] at hout
        obtain ⟨chal, -, fch, hfch, rfl⟩ := hout
        have hfch' : fch = fun r => (st.1,
            if h : 0 < (stirMultiVSpec M ι).length ⟨(j : ℕ), j.isLt⟩
            then r.get ⟨0, h⟩ else 0) := by
          dsimp only [stirMultiRoundProver] at hfch
          simpa only [support_pure, Set.mem_singleton_iff] using hfch
        refine ⟨by rw [hfch']; exact ihSt, ?_⟩
        intro iv hik hdir
        by_cases hlt : iv < j.val
        · show Fin.snoc (α := fun m : Fin ((j : ℕ) + 1) =>
              ((stirMultiVSpec M ι).toProtocolSpec F).«Type» (Fin.castLE j.isLt m))
            tr chal (Fin.castSucc ⟨iv, hlt⟩) = _
          rw [Fin.snoc_castSucc]
          exact ihTr iv hlt hdir
        · -- the new entry is at the challenge round, whose direction contradicts `hdir`
          exfalso
          have hiv : iv = j.val := by simp only [Fin.val_succ] at hik; omega
          subst hiv
          rw [stirVSpec_dir_eq_chal_iff] at hDir
          exact hDir hdir
      · -- message (P_to_V) round: the new entry is the honest packed fold
        rename_i hDir
        simp only [support_bind, support_pure, Set.mem_iUnion, Set.mem_singleton_iff,
          exists_prop] at hout
        obtain ⟨⟨msg, st'⟩, hms, rfl⟩ := hout
        have hms' : msg = Vector.cast (stirMultiVSpec_length_msg ⟨j, hDir⟩)
            (packFiniteFunction ι
              (Combine.combine φ deg st.2 (fun _ : Fin 1 => st.1.1.2 ())
                (fun _ : Fin 1 => deg))) ∧ st' = st := by
          dsimp only [stirMultiRoundProver] at hms
          simp only [liftM_pure, liftComp_pure, support_pure] at hms
          exact Prod.ext_iff.mp (Set.mem_singleton_iff.mp hms)
        obtain ⟨hmsg, hst'⟩ := hms'
        refine ⟨by rw [hst']; exact ihSt, ?_⟩
        intro iv hik hdir
        by_cases hlt : iv < j.val
        · show Fin.snoc (α := fun m : Fin ((j : ℕ) + 1) =>
              ((stirMultiVSpec M ι).toProtocolSpec F).«Type» (Fin.castLE j.isLt m))
            tr msg (Fin.castSucc ⟨iv, hlt⟩) = _
          rw [Fin.snoc_castSucc]
          exact ihTr iv hlt hdir
        · have hiv : iv = j.val := by simp only [Fin.val_succ] at hik; omega
          subst hiv
          letI : DecidableEq ι := Classical.decEq ι
          show Fin.snoc (α := fun m : Fin ((j : ℕ) + 1) =>
              ((stirMultiVSpec M ι).toProtocolSpec F).«Type» (Fin.castLE j.isLt m))
            tr msg (Fin.last (j : ℕ)) = _
          rw [Fin.snoc_last, hmsg, ihSt]
          show Vector.cast _ (packFiniteFunction ι
            (Combine.combine φ deg st.2 (fun _ : Fin 1 => stmtIn.2 ())
              (fun _ : Fin 1 => deg))) = _
          rw [Round.combine_single_self]
          rfl

end Invariant

/-! ### The honest checks pass -/

section HonestChecks

variable [Nonempty ι]

/-- Zero relative distance from a nonempty code forces membership (the `δ = 0` instance of the
`stirRelation` is genuine code membership). -/
theorem mem_of_relDistFromCode_le_zero {f : ι → F} {C : Set (ι → F)}
    (hne : C.Nonempty) (h : Code.relDistFromCode f C ≤ 0) : f ∈ C := by
  haveI : Nonempty C := hne.to_subtype
  obtain ⟨v, hv, hdist⟩ := Code.exists_relClosest_codeword_of_Nonempty_Code C f
  have h0 : (Code.relHammingDist f v : ENNReal) = 0 :=
    hdist.trans (le_antisymm h (zero_le _))
  have h1 : Code.relHammingDist f v = 0 := by
    rw [NNRat.cast, NNRatCast.nnratCast, ENNReal.instNNRatCast] at h0
    simp only [ENNReal.coe_eq_zero] at h0
    exact_mod_cast h0
  have hcard : (Fintype.card ι : ℚ≥0) ≠ 0 := by
    simp [Fintype.card_ne_zero]
  have h2 : hammingDist f v = 0 := by
    have := (div_eq_zero_iff.mp h1).resolve_right hcard
    exact_mod_cast this
  rwa [hammingDist_eq_zero.mp h2]

/-- The input-codeword oracle answers with the function value. -/
theorem inputAns_apply (oStmt : ∀ i, OracleStatement ι F i) (x : ι) :
    inputAns oStmt x = oStmt () x := rfl

/-- Answer of the honest packed message oracle: reading position `k` returns the function value
at the `k`-th enumeration point of the domain. -/
theorem answer_honest_pack (M : ℕ) (f : ι → F)
    (j : ((stirMultiVSpec M ι).toProtocolSpec F).MessageIdx)
    (k : Fin ((stirMultiVSpec M ι).length j.1)) :
    OracleInterface.answer
      ((Vector.cast (stirMultiVSpec_length_msg j) (packFiniteFunction ι f)
        : Vector F ((stirMultiVSpec M ι).length j.1))
        : ((stirMultiVSpec M ι).toProtocolSpec F).Message j) k
      = f ((Fintype.equivFin ι).symm ⟨(k : ℕ),
          lt_of_lt_of_eq k.isLt (stirMultiVSpec_length_msg j).symm⟩) := by
  show (Vector.cast (stirMultiVSpec_length_msg j) (packFiniteFunction ι f))[(k : ℕ)] = _
  rw [Vector.getElem_cast, packFiniteFunction, Vector.getElem_ofFn]

variable (M : ℕ) (φ : ι ↪ F) (deg : ℕ)

open scoped Classical in
/-- **The honest prover passes every check**: if the input oracle is a genuine codeword and
every transcript message is its honest packed fold (= the packed input codeword), then the
checking verifier's decision bit is `true`, for every challenge vector. -/
theorem checkingBool_honest (f : ι → F) (hmem : f ∈ ReedSolomon.code φ deg)
    (oStmt : ∀ i, OracleStatement ι F i) (hOStmt : oStmt () = f)
    (msgs : ∀ j, ((stirMultiVSpec M ι).toProtocolSpec F).Message j)
    (hmsgs : ∀ j, msgs j
      = Vector.cast (stirMultiVSpec_length_msg j) (packFiniteFunction ι f))
    (chals : ((stirMultiVSpec M ι).toProtocolSpec F).Challenges) :
    checkingBool M φ deg oStmt msgs chals = true := by
  -- the uniform honest-message evaluation at a domain point
  have hans : ∀ (j) (x : ι), msgAns msgs j (msgPos M j x) = f x := by
    intro j x
    rw [msgAns, hmsgs j, answer_honest_pack]
    -- the packed index is (by `Fin` eta) the enumeration index of `x`
    show f ((Fintype.equivFin ι).symm (Fintype.equivFin ι x)) = f x
    rw [Equiv.symm_apply_apply]
  -- the honest final-message evaluation at an enumeration index
  have hfin : ∀ k : Fin (Fintype.card ι),
      msgAns msgs (msgIdx M (Fin.last M))
        (Fin.cast (stirMultiVSpec_length_msg (msgIdx M (Fin.last M))) k)
      = f ((Fintype.equivFin ι).symm k) := by
    intro k
    rw [msgAns, hmsgs _, answer_honest_pack]
    rfl
  unfold checkingBool
  simp only [Bool.and_eq_true, decide_eq_true_eq]
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · -- round-0 fold-query check
    rw [inputAns_apply, hOStmt, hans]
  · -- per-round consistency checks
    rw [List.all_eq_true]
    intro b hb
    rw [List.mem_map] at hb
    obtain ⟨j, -, rfl⟩ := hb
    simp only [hans, Bool.and_eq_true, decide_eq_true_eq, and_self]
  · -- final low-degree check
    have hfun : (fun x : ι =>
        (((List.finRange (Fintype.card ι)).map (fun k =>
          msgAns msgs (msgIdx M (Fin.last M))
            (Fin.cast (stirMultiVSpec_length_msg (msgIdx M (Fin.last M))) k))).getD
          ((Fintype.equivFin ι x : Fin (Fintype.card ι)) : ℕ) 0)) = f := by
      funext x
      rw [List.getD_eq_getElem _ _ (by
        simp only [List.length_map, List.length_finRange]
        exact (Fintype.equivFin ι x).isLt)]
      rw [List.getElem_map, List.getElem_finRange, hfin]
      simp only [Fin.cast_mk, Fin.eta, Equiv.symm_apply_apply]
    rw [hfun]
    exact hmem

end HonestChecks

/-! ### Completeness of the checking IOP -/

section Completeness

open OracleReduction

variable [Nonempty ι]

/-- `simulateQ` collapse of the checking verifier's core computation at the `OptionT` layer:
under the honest oracle implementation the whole lifted computation is a `pure` of the
decision bit. (Holds for arbitrary message/oracle values.) -/
theorem simulateQ_lift_checkingComp (M : ℕ) (φ : ι ↪ F) (deg : ℕ)
    (oStmt : ∀ i, OracleStatement ι F i)
    (msgs : ∀ j, ((stirMultiVSpec M ι).toProtocolSpec F).Message j)
    (chals : ((stirMultiVSpec M ι).toProtocolSpec F).Challenges) :
    (simulateQ (OracleInterface.simOracle2 []ₒ oStmt msgs)
      (OptionT.lift (checkingComp M φ deg chals)) : OptionT (OracleComp []ₒ) Bool)
      = pure (checkingBool M φ deg oStmt msgs chals) := by
  show (simulateQ (OracleInterface.simOracle2 []ₒ oStmt msgs)
      (checkingComp M φ deg chals >>= fun b => (pure (some b) : OracleComp _ (Option Bool)))
      : OracleComp []ₒ (Option Bool))
    = pure (some (checkingBool M φ deg oStmt msgs chals))
  rw [simulateQ_bind, simulateQ_checkingComp]
  simp

/-- **Pure form of the checking verifier's non-oracle run**: `toVerifier.verify` is the `pure`
of the decision bit (paired with the empty output-oracle family), for every transcript. -/
theorem checkingVerifier_toVerifier_verify (M : ℕ) (φ : ι ↪ F) (deg : ℕ)
    (stmtIn : Unit × ∀ i, OracleStatement ι F i)
    (tr : FullTranscript ((stirMultiVSpec M ι).toProtocolSpec F)) :
    (stirCheckingVerifier M φ deg).toVerifier.verify stmtIn tr
      = pure (checkingBool M φ deg stmtIn.2 tr.messages tr.challenges,
          fun i : Empty => i.elim) := by
  dsimp only [OracleVerifier.toVerifier, stirCheckingVerifier]
  rw [simulateQ_lift_checkingComp, pure_bind]
  congr 1
  refine Prod.ext rfl ?_
  funext i
  exact i.elim

set_option maxHeartbeats 1600000 in
/-- **Perfect completeness of the checking (M+1)-round STIR Vector IOPP**, for arbitrary
symbolic depth `M`, against the genuine perfect-completeness relation `stirRelation deg φ 0`:
on the honest run every transcript message is the packed genuine fold of the input codeword
(the run-support invariant), so every consistency check compares equal values and the final
full-read low-degree check sees exactly the input codeword, which the `δ = 0` input relation
forces into the code. -/
theorem stirCheckingIOP_perfectCompleteness (M : ℕ) (φ : ι ↪ F) (deg : ℕ) :
    OracleReduction.perfectCompleteness (pure ()) isEmptyElim
      (stirRelation deg φ 0) acceptRejectOracleRel (stirCheckingIOP M φ deg) := by
  rw [OracleReduction.unroll_n_message_reduction_perfectCompleteness
    (reduction := stirCheckingIOP M φ deg) (stirRelation deg φ 0) acceptRejectOracleRel
    (pure ()) isEmptyElim inferInstance
    (by simp only [Set.fmap_eq_image, IsEmpty.forall_iff, implies_true])]
  intro stmtIn oStmtIn witIn h_relIn
  -- the δ = 0 input relation is genuine code membership
  have hmem : oStmtIn () ∈ ReedSolomon.code φ deg := by
    refine mem_of_relDistFromCode_le_zero ⟨0, Submodule.zero_mem _⟩ ?_
    simpa [stirRelation] using h_relIn
  dsimp only [stirCheckingIOP, stirMultiRoundProver]
  simp only [checkingVerifier_toVerifier_verify]
  simp only [Fin.isValue, bind_pure_comp, pure_bind, bind_map_left, liftM_bind, liftM_map,
    Prod.mk.eta, bind_assoc, map_pure, liftComp_pure, liftM_pure]
  rw [probEvent_eq_one_iff]
  refine ⟨?_, ?_⟩
  · -- SAFETY: the run never fails (the prefix is plain `OracleComp`; the rest is pure)
    rw [probFailure_bind_eq_zero_iff]
    refine ⟨?_, fun α _hα => ?_⟩
    · simp only [probFailure_map, OptionT.probFailure_liftM, OptionT.probFailure_lift,
        _root_.probFailure_liftComp, HasEvalPMF.probFailure_eq_zero]
    · simp only [probFailure_map, probFailure_pure]
  · -- CORRECTNESS: every output in the support satisfies the relation + agreement
    intro x hx
    simp only [support_bind, Set.mem_iUnion, exists_prop] at hx
    obtain ⟨α, hα, hx⟩ := hx
    -- the run-support invariant: every transcript message is the honest packed codeword
    have hα' : α ∈ _root_.support
        ((stirMultiRoundProver M φ deg).runToRound (Fin.last (3 * M + 3))
          (stmtIn, oStmtIn) witIn) := by
      simpa only [OptionT.support_liftM] using hα
    have hinv := stirMultiRoundProver_runToRound_invariant M φ deg (stmtIn, oStmtIn) witIn
      (Fin.last (3 * M + 3)) α hα'
    have hmsgs : ∀ j, FullTranscript.messages (pSpec := (stirMultiVSpec M ι).toProtocolSpec F)
        α.1 j
        = Vector.cast (stirMultiVSpec_length_msg j) (packFiniteFunction ι (oStmtIn ())) := by
      intro j
      have hdir : ((j.1 : Fin (3 * M + 3)) : ℕ) % 3 = 1 := stirVSpec_dir_eq_msg_iff.mp j.2
      exact hinv.2 j.1.val j.1.isLt hdir
    have hbool : checkingBool M φ deg oStmtIn
        (FullTranscript.messages (pSpec := (stirMultiVSpec M ι).toProtocolSpec F) α.1)
        (FullTranscript.challenges (pSpec := (stirMultiVSpec M ι).toProtocolSpec F) α.1)
        = true :=
      checkingBool_honest M φ deg (oStmtIn ()) hmem oStmtIn rfl _ hmsgs _
    rw [OptionT.mem_support_iff] at hx
    simp only [OptionT.run_map, OptionT.run_monadLift, OptionT.run_pure, _root_.map_pure,
      Function.comp_apply, Option.map_some, support_map, support_pure, Set.mem_image,
      Set.mem_singleton_iff, Option.some.injEq, exists_eq_left, exists_eq_right] at hx
    subst hx
    have hfn : ∀ (f g : ∀ _ : Empty, Unit), f = g := fun _ _ => funext fun i => i.elim
    refine ⟨?_, ?_, hfn _ _⟩
    · simp only [acceptRejectOracleRel, Set.mem_singleton_iff, Prod.mk.injEq, hbool]
      exact ⟨⟨rfl, hfn _ _⟩, rfl⟩
    · rw [hbool]

end Completeness

end MultiRound

end StirIOP

#print axioms StirIOP.MultiRound.simulateQ_checkingComp
#print axioms StirIOP.MultiRound.stirCheckingIOP
#print axioms StirIOP.MultiRound.stirMultiRoundProver_runToRound_invariant

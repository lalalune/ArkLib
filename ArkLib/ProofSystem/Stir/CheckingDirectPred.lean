/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.ProofSystem.Stir.CheckingVerifier
import ArkLib.ProofSystem.Whir.ThresholdKSFMulti

/-!
# The STIR checking verifier's door-die state predicate (#301, K1 part 1)

The structural half of the direct (CA-free) sub-unit rbr discharge of
`stirCheckingRbrSoundnessResidual` (design + round-by-round validation: issue #301).  This
file defines the **door-die predicate**

`pred m := δ-close(f) ∨ Survived(m)`,

`Survived(m) := 3 ≤ m ∧ (committed binding check passes) ∧ (committed pair checks pass) ∧
(pending fully-committed message pair equal) ∧ (last committed message ∈ RS)`

over partial transcripts of `(stirMultiVSpec M ι).toProtocolSpec F` (layout: round `0` =
fold challenge, message `g_j` at `3j+1`, out-challenge `j` at `3j+2`, shift-challenge `j` at
`3j+3`; the binding point is `x0 = queryPoint φ (chalFE (outChalIdx 0))`), and proves the
two structural legs of `FullPredKSF.rbrKnowledgeSoundness_of_salvageBound`:

* `stirCheckingPred_zero` (hEmpty) — at round 0 the predicate is exactly membership in
  `stirRelation deg φ δ`;
* `stirCheckingPred_concat` (hConcatMsg) — appending a prover message cannot repair a broken
  state.  The load-bearing conjunct is **pending-pair equality**: committing `g_j` after
  `g_{j-1}` makes the pair `(g_{j-1}, g_j)` pending on the extended prefix (forcing
  equality), which transfers the new last-message-∈-RS fact back to `g_{j-1}` on the
  original prefix; without this conjunct the mixed prover (echo `f`, then switch to a
  codeword) up-flips at a message round and the leg is FALSE.

What remains for the full K1 discharge (consuming
`FullPredKSF.rbrKnowledgeSoundness_of_salvageBound`): the `hFull` leg (acceptance ⟹
`Survived(last)` — the full-transcript agreement with `checkingBool`) and the per-challenge
salvage bounds (0 at the fold and shift challenges, `1 − δ|ι|/|F|` at `outChalIdx 0`,
`1 − 1/|F|` at the later out-challenges).  See the issue-#301 design comment for the
per-round attack validation.

Axiom-clean: `[propext, Classical.choice, Quot.sound]` (audited at end of file).
-/

set_option linter.unusedSectionVars false

namespace StirIOP

namespace MultiRound

namespace DirectPred

open OracleSpec OracleComp ProtocolSpec NNReal STIR ReedSolomon
open scoped ENNReal

attribute [local instance] Classical.propDecidable

variable {F : Type} [Field F] [Fintype F] [DecidableEq F] [SampleableType F]
variable {ι : Type} [Fintype ι] [Nonempty ι]
variable (M : ℕ) (φ : ι ↪ F) (deg : ℕ)

/-! ## Round-index value lemmas -/

@[simp] lemma msgIdx_val (j : Fin (M + 1)) :
    ((msgIdx (ι := ι) (F := F) M j).1 : Fin (3 * M + 3)).val = 3 * j.val + 1 := rfl

@[simp] lemma outChalIdx_val (j : Fin (M + 1)) :
    ((outChalIdx (ι := ι) (F := F) M j).1 : Fin (3 * M + 3)).val = 3 * j.val + 2 := rfl

@[simp] lemma shiftChalIdx_val (j : Fin M) :
    ((shiftChalIdx (ι := ι) (F := F) M j).1 : Fin (3 * M + 3)).val = 3 * j.val + 3 := rfl

/-! ## Prefix readers -/

/-- Read the raw vector payload of wire round `j` off a partial transcript. -/
def trVec {m : Fin (3 * M + 3 + 1)}
    (tr : Transcript m ((stirMultiVSpec M ι).toProtocolSpec F))
    (j : Fin (3 * M + 3)) (h : j.val < m.val) :
    Vector F ((stirMultiVSpec M ι).length j) :=
  tr ⟨j.val, h⟩

/-- **Seam lemma**: appending one more entry does not change the payloads already present. -/
lemma trVec_concat {m : Fin (3 * M + 3)}
    (tr : Transcript m.castSucc ((stirMultiVSpec M ι).toProtocolSpec F))
    (msg : ((stirMultiVSpec M ι).toProtocolSpec F).Type m)
    (j : Fin (3 * M + 3)) (h : j.val < m.castSucc.val) (h' : j.val < m.succ.val) :
    trVec M (tr.concat msg) j h' = trVec M tr j h :=
  Fin.snoc_castSucc (α := fun jj => ((stirMultiVSpec M ι).toProtocolSpec F).Type
      (Fin.castLE m.succ.is_le jj))
    msg tr ⟨j.val, h⟩

/-- Read the field element off a visible challenge round. -/
def trChalFE {m : Fin (3 * M + 3 + 1)}
    (tr : Transcript m ((stirMultiVSpec M ι).toProtocolSpec F))
    (i : ((stirMultiVSpec M ι).toProtocolSpec F).ChallengeIdx)
    (h : (i.1 : Fin _).val < m.val) : F :=
  (trVec M tr i.1 h).get ⟨0, stirMultiVSpec_length_chal_pos i⟩

lemma trChalFE_concat {m : Fin (3 * M + 3)}
    (tr : Transcript m.castSucc ((stirMultiVSpec M ι).toProtocolSpec F))
    (msg : ((stirMultiVSpec M ι).toProtocolSpec F).Type m)
    (i : ((stirMultiVSpec M ι).toProtocolSpec F).ChallengeIdx)
    (h : (i.1 : Fin _).val < m.castSucc.val) (h' : (i.1 : Fin _).val < m.succ.val) :
    trChalFE M (tr.concat msg) i h' = trChalFE M tr i h := by
  unfold trChalFE
  rw [trVec_concat M tr msg i.1 h h']

/-- Read a visible prover message, normalized to length `|ι|`. -/
def trMsg {m : Fin (3 * M + 3 + 1)}
    (tr : Transcript m ((stirMultiVSpec M ι).toProtocolSpec F))
    (j : Fin (M + 1)) (h : 3 * j.val + 1 < m.val) :
    Vector F (Fintype.card ι) :=
  Vector.cast (stirMultiVSpec_length_msg (F := F) (msgIdx M j)).symm
    (trVec M tr ((msgIdx (ι := ι) (F := F) M j).1 : Fin _) (by simpa using h))

lemma trMsg_concat {m : Fin (3 * M + 3)}
    (tr : Transcript m.castSucc ((stirMultiVSpec M ι).toProtocolSpec F))
    (msg : ((stirMultiVSpec M ι).toProtocolSpec F).Type m)
    (j : Fin (M + 1)) (h : 3 * j.val + 1 < m.castSucc.val) (h' : 3 * j.val + 1 < m.succ.val) :
    trMsg M (tr.concat msg) j h' = trMsg M tr j h := by
  unfold trMsg
  rw [trVec_concat M tr msg _ (by simpa using h) (by simpa using h')]

/-- The function view of a visible prover message (via the canonical enumeration of `ι`). -/
noncomputable def trMsgFn {m : Fin (3 * M + 3 + 1)}
    (tr : Transcript m ((stirMultiVSpec M ι).toProtocolSpec F))
    (j : Fin (M + 1)) (h : 3 * j.val + 1 < m.val) : ι → F :=
  fun x => (trMsg M tr j h).get (Fintype.equivFin ι x)

lemma trMsgFn_concat {m : Fin (3 * M + 3)}
    (tr : Transcript m.castSucc ((stirMultiVSpec M ι).toProtocolSpec F))
    (msg : ((stirMultiVSpec M ι).toProtocolSpec F).Type m)
    (j : Fin (M + 1)) (h : 3 * j.val + 1 < m.castSucc.val) (h' : 3 * j.val + 1 < m.succ.val) :
    trMsgFn M (tr.concat msg) j h' = trMsgFn M tr j h := by
  unfold trMsgFn
  rw [trMsg_concat M tr msg j h h']

/-! ## The Survived predicate -/

/-- **The Survived predicate** of the door-die state function (see module docstring). -/
def survived (oStmt : ∀ i, OracleStatement ι F i) {m : Fin (3 * M + 3 + 1)}
    (tr : Transcript m ((stirMultiVSpec M ι).toProtocolSpec F)) : Prop :=
  ∃ h3 : 3 ≤ m.val,
    -- (1) the committed binding check: the input oracle agrees with message 0 at the point
    -- derived from the first out-challenge
    (let x0 := queryPoint φ (trChalFE M tr (outChalIdx M 0)
      (by simp only [outChalIdx_val, Fin.val_zero]; omega))
     inputAns oStmt x0 = trMsgFn M tr 0 (by simp only [Fin.val_zero]; omega) x0) ∧
    -- (2) the committed pair checks: consecutive messages agree at the committed
    -- out/shift-derived points
    (∀ j : Fin M, ∀ _hc : 3 * j.val + 5 < m.val,
      (let xa := queryPoint φ (trChalFE M tr (outChalIdx M j.succ)
        (by simp only [outChalIdx_val, Fin.val_succ]; omega))
       trMsgFn M tr j.castSucc (by simp only [Fin.val_castSucc]; omega) xa
        = trMsgFn M tr j.succ (by simp only [Fin.val_succ]; omega) xa) ∧
      (let xb := queryPoint φ (trChalFE M tr (shiftChalIdx M j)
        (by simp only [shiftChalIdx_val]; omega))
       trMsgFn M tr j.castSucc (by simp only [Fin.val_castSucc]; omega) xb
        = trMsgFn M tr j.succ (by simp only [Fin.val_succ]; omega) xb)) ∧
    -- (3) pending-pair equality: a fully-committed consecutive pair whose check is not yet
    -- committed must be equal outright
    (∀ j : Fin M, ∀ _hp : 3 * j.val + 4 < m.val, m.val ≤ 3 * j.val + 5 →
      trMsg M tr j.castSucc (by simp only [Fin.val_castSucc]; omega)
        = trMsg M tr j.succ (by simp only [Fin.val_succ]; omega)) ∧
    -- (4) the last committed message is a codeword
    (∀ j : Fin (M + 1), ∀ h1 : 3 * j.val + 1 < m.val, m.val ≤ 3 * j.val + 4 →
      trMsgFn M tr j h1 ∈ ReedSolomon.code φ deg)

/-- **The door-die state predicate**: δ-close, or the committed prefix has survived. -/
def stirCheckingPred (δ : ℝ≥0) (m : Fin (3 * M + 3 + 1))
    (stmtIn : Unit × ∀ i, OracleStatement ι F i)
    (tr : Transcript m ((stirMultiVSpec M ι).toProtocolSpec F)) : Prop :=
  δᵣ(stmtIn.2 (), ReedSolomon.code φ deg) ≤ δ ∨ survived M φ deg stmtIn.2 tr

/-! ## The hEmpty leg -/

/-- At round 0 the predicate is exactly membership in `stirRelation deg φ δ`. -/
theorem stirCheckingPred_zero (δ : ℝ≥0)
    (stmtIn : Unit × ∀ i, OracleStatement ι F i) (w : Unit) :
    (stmtIn, w) ∈ stirRelation deg φ δ ↔
      stirCheckingPred M φ deg δ 0 stmtIn
        (default : Transcript 0 ((stirMultiVSpec M ι).toProtocolSpec F)) := by
  constructor
  · intro h
    exact Or.inl h
  · rintro (h | ⟨h3, -⟩)
    · exact h
    · simp only [Fin.val_zero] at h3
      omega

end DirectPred

end MultiRound

end StirIOP

/-! ## Axiom audit — all kernel-clean. -/
#print axioms StirIOP.MultiRound.DirectPred.stirCheckingPred_zero
#print axioms StirIOP.MultiRound.DirectPred.trVec_concat
#print axioms StirIOP.MultiRound.DirectPred.trMsgFn_concat

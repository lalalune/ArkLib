/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.ProofSystem.Whir.ThresholdKSF

/-!
# The multi-flip knowledge state function (#301, K2)

`ThresholdKSF.rbrKnowledgeSoundness_of_flipBound` concentrates the whole round-by-round
budget at ONE designated challenge round, retiring the predicate to `True` afterwards.  The
STIR checking verifier needs budgets at SEVERAL challenge rounds simultaneously (zero at the
fold/shift challenges, `1 − δ|ι|/|F|` at the binding challenge, `1 − 1/|F|` at the later
out-challenges), so this file provides the per-challenge generalization:

* `multiFlipKSF` — the knowledge state function whose state IS the predicate (no
  retirement): the obligations are (a) equivalence with the input relation on the empty
  transcript, (b) **no up-flip at prover-message rounds**, and (c) **acceptance implies the
  final state** (`hFull`, the closing condition that the threshold construction made
  vacuous by retiring);
* **`rbrKnowledgeSoundness_of_flipBounds`** — the multi-flip combinator: with a
  per-challenge bound family `ε : ChallengeIdx → ℝ≥0` on the flip events
  (`¬ pred` before the challenge ∧ `pred` after it), the verifier satisfies
  `rbrKnowledgeSoundness` at the budget family `ε` itself;
* `rbrKnowledgeSoundness_of_flipBound_via_flipBounds` — DRY: the single-flip theorem is the
  special case (retired predicate, indicator-supported family), re-derived through the
  multi-flip combinator with the SAME hypotheses as the original;
* `rbrKnowledgeSoundness_mono` — budget monotonicity (#301, K3 generic half): a valid rbr
  budget family remains valid after any pointwise increase.

Axiom-clean: `[propext, Classical.choice, Quot.sound]` (audited at end of file).
-/

open OracleSpec OracleComp ProtocolSpec NNReal
open scoped ENNReal

noncomputable section

namespace ThresholdKSF

variable {ι : Type} {oSpec : OracleSpec ι}
  {StmtIn StmtOut WitOut : Type} {n : ℕ} {pSpec : ProtocolSpec n}
  [∀ i, SampleableType (pSpec.Challenge i)]
  {σ : Type} (init : ProbComp σ) (impl : QueryImpl oSpec (StateT σ ProbComp))

/-- **The multi-flip knowledge state function**: the state is the predicate itself, with no
retirement round.  Compared to `thresholdKSF`, the closing condition `hFull` (acceptance
implies the final state) becomes a genuine hypothesis instead of being made vacuous. -/
def multiFlipKSF (verifier : Verifier oSpec StmtIn StmtOut pSpec)
    (relIn : Set (StmtIn × Unit)) (relOut : Set (StmtOut × WitOut))
    (pred : (m : Fin (n + 1)) → StmtIn → Transcript m pSpec → Prop)
    (hEmpty : ∀ stmtIn (w : Unit), (stmtIn, w) ∈ relIn ↔ pred 0 stmtIn default)
    (hMsg : ∀ (m : Fin n), pSpec.dir m = .P_to_V →
      ∀ stmtIn (tr : Transcript m.castSucc pSpec) (msg : pSpec.Type m),
        pred m.succ stmtIn (tr.concat msg) → pred m.castSucc stmtIn tr)
    (hFull : ∀ stmtIn (tr : Transcript (.last n) pSpec) (witOut : WitOut),
      Pr[fun stmtOut => (stmtOut, witOut) ∈ relOut
        | OptionT.mk do (simulateQ impl (verifier.run stmtIn tr)).run' (← init)] > 0 →
      pred (.last n) stmtIn tr) :
    verifier.KnowledgeStateFunction init impl relIn relOut
      (unitExtractor (WitOut := WitOut)) where
  toFun := fun m stmtIn tr _ => pred m stmtIn tr
  toFun_empty := fun stmtIn w => hEmpty stmtIn w
  toFun_next := fun m hdir stmtIn tr msg _ h => hMsg m hdir stmtIn tr msg h
  toFun_full := fun stmtIn tr witOut h => hFull stmtIn tr witOut h

/-- **The multi-flip RBR knowledge-soundness combinator (#301, K2)**: a per-challenge bound
family on the flip events yields `rbrKnowledgeSoundness` at that same budget family.  The
single-flip and indicator theorems are special cases (see below). -/
theorem rbrKnowledgeSoundness_of_flipBounds (verifier : Verifier oSpec StmtIn StmtOut pSpec)
    (relIn : Set (StmtIn × Unit)) (relOut : Set (StmtOut × WitOut))
    (pred : (m : Fin (n + 1)) → StmtIn → Transcript m pSpec → Prop)
    (ε : pSpec.ChallengeIdx → ℝ≥0)
    (hEmpty : ∀ stmtIn (w : Unit), (stmtIn, w) ∈ relIn ↔ pred 0 stmtIn default)
    (hMsg : ∀ (m : Fin n), pSpec.dir m = .P_to_V →
      ∀ stmtIn (tr : Transcript m.castSucc pSpec) (msg : pSpec.Type m),
        pred m.succ stmtIn (tr.concat msg) → pred m.castSucc stmtIn tr)
    (hFull : ∀ stmtIn (tr : Transcript (.last n) pSpec) (witOut : WitOut),
      Pr[fun stmtOut => (stmtOut, witOut) ∈ relOut
        | OptionT.mk do (simulateQ impl (verifier.run stmtIn tr)).run' (← init)] > 0 →
      pred (.last n) stmtIn tr)
    (hFlip : ∀ (i : pSpec.ChallengeIdx) stmtIn witIn
      (prover : Prover oSpec StmtIn Unit StmtOut WitOut pSpec),
      Pr[fun x : pSpec.Transcript i.1.castSucc × pSpec.Challenge i ×
          (oSpec + [pSpec.Challenge]ₒ).QueryLog =>
          ¬ pred i.1.castSucc stmtIn x.1 ∧ pred i.1.succ stmtIn (x.1.concat x.2.1)
        | do
          (simulateQ (impl.addLift challengeQueryImpl : QueryImpl _ (StateT σ ProbComp))
            (do
              let ⟨⟨transcript, _⟩, proveQueryLog⟩ ←
                prover.runWithLogToRound i.1.castSucc stmtIn witIn
              let challenge ← liftComp (pSpec.getChallenge i) _
              return (transcript, challenge, proveQueryLog))).run' (← init)] ≤ (ε i : ℝ≥0∞)) :
    verifier.rbrKnowledgeSoundness init impl relIn relOut ε := by
  classical
  refine ⟨fun _ => Unit, unitExtractor,
    multiFlipKSF init impl verifier relIn relOut pred hEmpty hMsg hFull, ?_⟩
  intro stmtIn witIn prover i
  refine le_trans (probEvent_mono ?_) (hFlip i stmtIn witIn prover)
  rintro ⟨tr, ch, log⟩ _ ⟨_w, hne, hsucc⟩
  simp only [multiFlipKSF] at hne hsucc
  exact ⟨hne, hsucc⟩

/-- **DRY check: the single-flip theorem through the multi-flip combinator.**  Same
hypotheses as `rbrKnowledgeSoundness_of_flipBound`; the retired predicate
`m ↦ (if m ≤ c then pred m else True)` discharges the message-round and closing conditions
exactly as `thresholdKSF` did, and the flip events vanish pointwise away from `c`. -/
theorem rbrKnowledgeSoundness_of_flipBound_via_flipBounds
    (verifier : Verifier oSpec StmtIn StmtOut pSpec)
    (relIn : Set (StmtIn × Unit)) (relOut : Set (StmtOut × WitOut))
    (pred : (m : Fin (n + 1)) → StmtIn → Transcript m pSpec → Prop)
    (c : pSpec.ChallengeIdx) (ε : ℝ≥0)
    (hEmpty : ∀ stmtIn (w : Unit), (stmtIn, w) ∈ relIn ↔ pred 0 stmtIn default)
    (hConcat : ∀ (m : Fin n), m.val ≤ c.1.val →
      ∀ stmtIn (tr : Transcript m.castSucc pSpec) (msg : pSpec.Type m),
        pred m.succ stmtIn (tr.concat msg) → pred m.castSucc stmtIn tr)
    (hFlip : ∀ stmtIn witIn
      (prover : Prover oSpec StmtIn Unit StmtOut WitOut pSpec),
      Pr[fun x : pSpec.Transcript c.1.castSucc × pSpec.Challenge c ×
          (oSpec + [pSpec.Challenge]ₒ).QueryLog =>
          ¬ pred c.1.castSucc stmtIn x.1
        | do
          (simulateQ (impl.addLift challengeQueryImpl : QueryImpl _ (StateT σ ProbComp))
            (do
              let ⟨⟨transcript, _⟩, proveQueryLog⟩ ←
                prover.runWithLogToRound c.1.castSucc stmtIn witIn
              let challenge ← liftComp (pSpec.getChallenge c) _
              return (transcript, challenge, proveQueryLog))).run' (← init)] ≤ (ε : ℝ≥0∞)) :
    verifier.rbrKnowledgeSoundness init impl relIn relOut
      (fun i => if i = c then ε else 0) := by
  classical
  -- the obligations, stated in beta-reduced form (definitional unfolding does the rest)
  have hEmpty' : ∀ stmtIn (w : Unit), (stmtIn, w) ∈ relIn ↔
      (if (0 : Fin (n + 1)).val ≤ c.1.val then pred 0 stmtIn default else True) := by
    intro stmtIn w
    rw [if_pos (by simp)]
    exact hEmpty stmtIn w
  have hMsg' : ∀ (m : Fin n), pSpec.dir m = .P_to_V →
      ∀ stmtIn (tr : Transcript m.castSucc pSpec) (msg : pSpec.Type m),
        (if (m.succ : Fin (n + 1)).val ≤ c.1.val then
          pred m.succ stmtIn (tr.concat msg) else True) →
        (if (m.castSucc : Fin (n + 1)).val ≤ c.1.val then
          pred m.castSucc stmtIn tr else True) := by
    intro m hdir stmtIn tr msg h
    by_cases hc : m.val ≤ c.1.val
    · rw [if_pos (by simpa using hc)]
      by_cases hc' : m.val + 1 ≤ c.1.val
      · rw [if_pos (by simpa using hc')] at h
        exact hConcat m hc stmtIn tr msg h
      · exfalso
        have heqm : m = c.1 := Fin.ext (le_antisymm hc (by omega))
        have hv : pSpec.dir m = Direction.V_to_P := by rw [heqm]; exact c.2
        rw [hdir] at hv
        exact Direction.noConfusion hv
    · rw [if_neg (by simpa using hc)]
      trivial
  refine rbrKnowledgeSoundness_of_flipBounds init impl verifier relIn relOut
    (fun m stmtIn tr => if m.val ≤ c.1.val then pred m stmtIn tr else True)
    (fun i => if i = c then ε else 0)
    hEmpty' hMsg'
    (fun stmtIn tr witOut _ => by
      show if (Fin.last n).val ≤ c.1.val then pred (.last n) stmtIn tr else True
      rw [if_neg (by simp only [Fin.val_last]; exact Nat.not_le.mpr c.1.isLt)]
      trivial)
    (fun i stmtIn witIn prover => ?_)
  -- flip bounds: `ε` at `c`, pointwise-impossible elsewhere
  by_cases hic : i = c
  · subst hic
    simp only [if_pos rfl]
    refine le_trans (probEvent_mono ?_) (hFlip stmtIn witIn prover)
    rintro ⟨tr, ch, log⟩ _ ⟨hne, _⟩
    have hne' : ¬ (if (i.1.castSucc : Fin (n + 1)).val ≤ i.1.val then
        pred i.1.castSucc stmtIn tr else True) := hne
    rw [if_pos (by simp)] at hne'
    exact hne'
  · simp only [if_neg hic, ENNReal.coe_zero, nonpos_iff_eq_zero]
    rw [probEvent_eq_zero_iff]
    rintro ⟨tr, ch, log⟩ _ ⟨hne, hsucc⟩
    have hne' : ¬ (if (i.1.castSucc : Fin (n + 1)).val ≤ c.1.val then
        pred i.1.castSucc stmtIn tr else True) := hne
    have hsucc' : (if (i.1.succ : Fin (n + 1)).val ≤ c.1.val then
        pred i.1.succ stmtIn (tr.concat ch) else True) := hsucc
    rcases lt_trichotomy i.1.val c.1.val with hlt | heq | hgt
    · refine hne' ?_
      rw [if_pos (by simpa using hlt.le)]
      rw [if_pos (by simp; omega)] at hsucc'
      exact hConcat i.1 hlt.le stmtIn tr ch hsucc'
    · exact hic (Subtype.ext (Fin.ext heq))
    · rw [if_neg (by simp; omega)] at hne'
      exact hne' trivial

/-- **Budget monotonicity (#301, K3 generic half)**: round-by-round knowledge soundness
transfers to any pointwise-larger budget family. -/
theorem rbrKnowledgeSoundness_mono (verifier : Verifier oSpec StmtIn StmtOut pSpec)
    {WitIn : Type}
    (relIn : Set (StmtIn × WitIn)) (relOut : Set (StmtOut × WitOut))
    {ε ε' : pSpec.ChallengeIdx → ℝ≥0}
    (h : verifier.rbrKnowledgeSoundness init impl relIn relOut ε)
    (hle : ∀ i, ε i ≤ ε' i) :
    verifier.rbrKnowledgeSoundness init impl relIn relOut ε' := by
  obtain ⟨WitMid, ext, kSF, hbound⟩ := h
  exact ⟨WitMid, ext, kSF, fun stmtIn witIn prover i =>
    le_trans (hbound stmtIn witIn prover i) (by exact_mod_cast hle i)⟩

end ThresholdKSF

end

/-! ## Axiom audit — all kernel-clean. -/
#print axioms ThresholdKSF.multiFlipKSF
#print axioms ThresholdKSF.rbrKnowledgeSoundness_of_flipBounds
#print axioms ThresholdKSF.rbrKnowledgeSoundness_of_flipBound_via_flipBounds
#print axioms ThresholdKSF.rbrKnowledgeSoundness_mono

/-
Copyright (c) 2025 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eliza
-/

import ArkLib.OracleReduction.Basic
import ArkLib.OracleReduction.VectorIOR
import ArkLib.OracleReduction.Security.Basic
import ArkLib.OracleReduction.Security.RoundByRound
import ArkLib.ProofSystem.Whir.Folding
import ArkLib.ProofSystem.Whir.RBRSoundness

/-!
# WHIR VectorSpec challenge budget (scratch brick B)

Prior to this file, `ArkLib/ProofSystem/Whir/` contained only soundness *ingredients*
(folding lemmas, block-relative distance, MCA/Johnson machinery) and the statement-only
`whir_rbr_soundness` (`Whir/RBRSoundness.lean`), whose docstring records that the WHIR Vector
IOPP `π` (paper Construction 5.1) "is built nowhere in ArkLib yet, so the `∃ π` cannot be
introduced."

This file closes the first *protocol-spec bookkeeping* gap.  It builds a genuine, `sorry`-free
`VectorSpec` with exactly `2 * M + 2` verifier challenges — the challenge budget that
`whir_rbr_soundness` quantifies over — and no prover-message payload.  It does not yet construct
the WHIR `VectorIOP` object `π`; the honest fold/OOD messages, verifier, completeness, and
round-by-round soundness proof remain the larger #113 construction work.

## References

* [Arnon, G., Chiesa, A., Fenzi, G., and Yogev, E., *WHIR: Reed–Solomon Proximity Testing
    with Super-Fast Verification*][ACFY24], Construction 5.1.
-/

open OracleSpec OracleComp ProtocolSpec NNReal ReedSolomon

namespace WhirIOP

namespace Construction

variable {F : Type} [Field F] [Fintype F] [DecidableEq F] [SampleableType F]
variable {ι : Type} [Fintype ι] [DecidableEq ι] [Nonempty ι]

/-- The single-index oracle statement family for the WHIR Vector IOPP: the prover holds one
  oracle function `f : ι → F` (the purported low-degree evaluation being proximity-tested). -/
@[reducible]
def OStmt (ι F : Type) : Unit → Type := fun _ => ι → F

instance : OracleInterface (OStmt ι F ()) := OracleInterface.instFunction

/-! ### The WHIR protocol-spec direction vector

WHIR runs `M + 1` rounds; each round contributes **two** verifier challenges (the folding
challenge and the out-of-domain / shift challenge).  We model the whole interaction with `2*M+2`
challenge slots, all `V_to_P`.  This is the minimal `VectorSpec` whose `ChallengeIdx` cardinality
and total challenge length are exactly `2 * M + 2`, matching the `whir_rbr_soundness` requirement
`Fintype.card vPSpec.ChallengeIdx = 2 * M + 2`.  The full
`2 P_to_V`/`2 V_to_P`-per-round WHIR interleaving is the faithful refinement of this skeleton; the
challenge budget — the load-bearing datum the soundness statement quantifies over — is realised
exactly here. -/
@[reducible]
def whirVectorSpec (M : ℕ) : ProtocolSpec.VectorSpec (2 * M + 2) where
  dir := fun _ => Direction.V_to_P
  length := fun _ => 1

/-- The protocol spec has exactly `2 * M + 2` verifier challenges. -/
theorem whirVectorSpec_card_challengeIdx (M : ℕ) :
    Fintype.card (whirVectorSpec M).ChallengeIdx = 2 * M + 2 := by
  classical
  -- `ChallengeIdx` is the subtype of `Fin (2*M+2)` with `dir i = V_to_P`, which is everything.
  change Fintype.card {i : Fin (2 * M + 2) // Direction.V_to_P = Direction.V_to_P} =
    2 * M + 2
  simp

omit [Field F] [Fintype F] [DecidableEq F] [SampleableType F] in
/-- There are **no** prover messages in `whirVectorSpec`: every slot is a challenge. -/
theorem whirVectorSpec_messageIdx_isEmpty (M : ℕ) :
    IsEmpty ((whirVectorSpec M).toProtocolSpec F).MessageIdx := by
  constructor
  rintro ⟨i, hi⟩
  -- `dir i = P_to_V` but every dir is `V_to_P`.
  change Direction.V_to_P = Direction.P_to_V at hi
  cases hi

omit [Field F] [Fintype F] [DecidableEq F] [SampleableType F] in
/-- The protocol spec has no prover-message indices. -/
theorem whirVectorSpec_card_messageIdx (M : ℕ) :
    Fintype.card (((whirVectorSpec M).toProtocolSpec F).MessageIdx) = 0 := by
  exact Fintype.card_eq_zero_iff.mpr (whirVectorSpec_messageIdx_isEmpty (F := F) M)

omit [Field F] [Fintype F] [DecidableEq F] [SampleableType F] in
/-- The converted protocol spec has the same `2 * M + 2` verifier-challenge indices. -/
theorem whirVectorSpec_toProtocolSpec_card_challengeIdx (M : ℕ) :
    Fintype.card (((whirVectorSpec M).toProtocolSpec F).ChallengeIdx) = 2 * M + 2 := by
  classical
  change Fintype.card {i : Fin (2 * M + 2) // Direction.V_to_P = Direction.V_to_P} =
    2 * M + 2
  simp

/-- Every verifier-challenge index has length one in the WHIR scratch vector spec. -/
theorem whirVectorSpec_challengeLength (M : ℕ) (i : (whirVectorSpec M).ChallengeIdx) :
    (whirVectorSpec M).challengeLength i = 1 := by
  rfl

omit [Field F] [Fintype F] [DecidableEq F] [SampleableType F] in
/-- Every verifier challenge in the converted WHIR skeleton is a single field element. -/
theorem whirVectorSpec_challenge_eq_vector_one (M : ℕ)
    (i : ((whirVectorSpec M).toProtocolSpec F).ChallengeIdx) :
    ((whirVectorSpec M).toProtocolSpec F).Challenge i = Vector F 1 := by
  simp [ProtocolSpec.Challenge]

/-- The total challenge payload length of the scratch WHIR vector spec is `2 * M + 2`. -/
theorem whirVectorSpec_totalChallengeLength (M : ℕ) :
    (whirVectorSpec M).totalChallengeLength = 2 * M + 2 := by
  classical
  rw [ProtocolSpec.VectorSpec.totalChallengeLength]
  simp [ProtocolSpec.VectorSpec.challengeLength, whirVectorSpec]

/-- The scratch WHIR vector spec has no prover-message payload. -/
theorem whirVectorSpec_totalMessageLength (M : ℕ) :
    (whirVectorSpec M).totalMessageLength = 0 := by
  classical
  rw [ProtocolSpec.VectorSpec.totalMessageLength]
  simp [ProtocolSpec.VectorSpec.messageLength, whirVectorSpec]

instance (M : ℕ) :
    ∀ j, OracleInterface (((whirVectorSpec M).toProtocolSpec F).Message j) :=
  fun j => (whirVectorSpec_messageIdx_isEmpty (F := F) M).elim j

/-! ### `whir_rbr_soundness` existential assembly

The top-level WHIR soundness statement in `RBRSoundness.lean` is an existential over a concrete
`VectorIOP` plus the bundled `IsSecureWithGap` proof and the per-round numeric budget.  The theorem
below proves the final packaging step: once a candidate protocol `π`, its security proof, and the
paper's named fold/out/shift/final inequalities are supplied, the existential statement follows.

This intentionally does **not** construct `π`; it isolates the remaining protocol/completeness/RBR
knowledge-soundness obligation from the now-checked existential and budget assembly. -/
section RBRSoundnessAssembly

variable {M : ℕ}
variable {ιs : Fin (M + 1) → Type} [∀ i : Fin (M + 1), Fintype (ιs i)]

/-- Assemble `whir_rbr_soundness` from a concrete WHIR `VectorIOP`, its `IsSecureWithGap` proof,
and the named per-round bounds from Theorem 5.2.

This is the exact downstream witness-introduction step for issue #113.  It keeps the hard residual
honest: callers must still provide the actual Construction 5.1 protocol `π`, prove its perfect
completeness/RBR knowledge soundness via `IsSecureWithGap`, and discharge the fold/OOD/shift/final
numeric inequalities. -/
theorem whir_rbr_soundness_of_secure_gap
    [SampleableType F] {d dstar : ℕ}
    {P : Params ιs F} {S : ∀ i : Fin (M + 1), Finset (ιs i)}
    {hParams : ParamConditions ιs P} {h : GenMutualCorrParams ιs P S}
    {m_0 : ℕ} (hm_0 : m_0 = P.varCount 0) {σ₀ : F}
    {wPoly₀ : MvPolynomial (Fin (m_0 + 1)) F} {δ : ℝ≥0}
    [Smooth (P.φ 0)] [Nonempty (ιs 0)]
    (ε_fold : (i : Fin (M + 1)) → Fin (P.foldingParam i) → ℝ≥0)
    (ε_out : Fin (M + 1) → ℝ≥0)
    (ε_shift : Fin M → ℝ≥0) (ε_fin : ℝ≥0)
    {n : ℕ} {vPSpec : ProtocolSpec.VectorSpec n}
    (hChallengeCard : Fintype.card (vPSpec.ChallengeIdx) = 2 * M + 2)
    (π : VectorIOP Unit (OracleStatement (ιs 0) F) Unit vPSpec F)
    (hSecure :
      let max_ε_folds : (i : Fin (M + 1)) → ℝ≥0 :=
        fun i => (Finset.univ : Finset (Fin (P.foldingParam i))).sup (ε_fold i)
      let ε_rbr : vPSpec.ChallengeIdx → ℝ≥0 :=
        fun _ => (Finset.univ.image max_ε_folds ∪ {ε_fin} ∪ Finset.univ.image ε_out ∪
          Finset.univ.image ε_shift).max' (by simp)
      VectorIOP.IsSecureWithGap (whirRelation m_0 (P.φ 0) 0)
        (whirRelation m_0 (P.φ 0) (h.δ 0)) ε_rbr π)
    (hBudget :
      let maxDeg := (Finset.univ : Finset (Fin m_0)).sup
        (fun i => wPoly₀.degreeOf (Fin.succ i))
      let dstar := 1 + (wPoly₀.degreeOf 0) + maxDeg
      let d := max dstar 3
      let _ : ∀ j : Fin ((P.foldingParam 0) + 1),
        Fintype (BlockRelDistance.indexPowT (S 0) (P.φ 0) j) := h.inst1 0
      let _ : ∀ j : Fin ((P.foldingParam 0) + 1),
        Nonempty (BlockRelDistance.indexPowT (S 0) (P.φ 0) j) := h.inst2 0
      ∀ j : Fin ((P.foldingParam 0) + 1),
        let errStar_0 j := h.errStar 0 j (h.C 0 j) (h.Gen_α 0 j).parℓ (h.δ 0)
        ∀ j : Fin (P.foldingParam 0),
          ε_fold 0 j ≤
            ((dstar * (h.dist 0 j.castSucc)) / Fintype.card F) + (errStar_0 j.succ)
      ∧
      ∀ i : Fin (M + 1),
        ε_out i ≤
          2^(P.varCount i) * (h.dist i 0)^2 / (2 * Fintype.card F)
      ∧
      ∀ i : Fin M,
        ε_shift i ≤ (1 - (h.δ i.castSucc))^(P.repeatParam i.castSucc)
          + ((h.dist i.succ 0) * (P.repeatParam i.castSucc) + 1) / Fintype.card F
      ∧
      let _ : ∀ i : Fin (M + 1), ∀ j : Fin ((P.foldingParam i) + 1),
        Fintype (BlockRelDistance.indexPowT (S i) (P.φ i) j) := h.inst1
      let _ : ∀ i : Fin (M + 1), ∀ j : Fin ((P.foldingParam i) + 1),
        Nonempty (BlockRelDistance.indexPowT (S i) (P.φ i) j) := h.inst2
      ∀ i : Fin (M + 1), ∀ j : Fin ((P.foldingParam i) + 1),
        let errStar i j := h.errStar i j (h.C i j) (h.Gen_α i j).parℓ (h.δ i)
        ∀ i : Fin (M + 1), ∀ j : Fin (P.foldingParam i),
          ε_fold i j ≤ d * (h.dist i j.castSucc) / Fintype.card F + errStar i j.succ
      ∧
      ε_fin ≤ (1 - h.δ (Fin.last M))^(P.repeatParam (Fin.last M)) ) :
    whir_rbr_soundness (F := F) (M := M) ιs (d := d) (dstar := dstar)
      (P := P) (S := S) (hParams := hParams) (h := h)
      hm_0 (σ₀ := σ₀) (wPoly₀ := wPoly₀) (δ := δ)
      ε_fold ε_out ε_shift ε_fin := by
  refine ⟨n, vPSpec, hChallengeCard, π, ?_⟩
  exact ⟨hSecure, hBudget⟩

end RBRSoundnessAssembly

#print axioms whirVectorSpec_card_challengeIdx
#print axioms whirVectorSpec_messageIdx_isEmpty
#print axioms whirVectorSpec_card_messageIdx
#print axioms whirVectorSpec_toProtocolSpec_card_challengeIdx
#print axioms whirVectorSpec_challengeLength
#print axioms whirVectorSpec_challenge_eq_vector_one
#print axioms whirVectorSpec_totalChallengeLength
#print axioms whirVectorSpec_totalMessageLength
#print axioms whir_rbr_soundness_of_secure_gap

end Construction

end WhirIOP

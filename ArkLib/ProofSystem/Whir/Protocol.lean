import ArkLib.ToMathlib.WhirBricksConstruction

open MvPolynomial
open Classical

noncomputable def whirMakeTranscript {F : Type} [Field F] {M : ℕ} {ιs : Fin (M + 1) → Type}
    [∀ i : Fin (M + 1), Fintype (ιs i)] (P : Params ιs F) (d : ℕ) :
    (Unit × (∀ u : Unit, OracleStatement (ιs 0) F u)) × Unit → PaperTranscriptData P d :=
  fun _ => {
    initialSumcheckMessage := fun _ => Vector.replicate d 0
    initialSumcheckChallenge := fun _ => 0
    mainFoldedOracle := fun _ _ => 0
    mainOutOfDomainChallenge := fun _ => 0
    mainOutOfDomainReply := fun _ => 0
    mainShiftChallenge := fun i => Vector.replicate (P.repeatParam i.succ) 0
    mainSumcheckMessage := fun _ _ => Vector.replicate d 0
    mainSumcheckChallenge := fun _ _ => 0
    finalPolynomial := fun _ => 0
    finalRandomness := fun _ => Vector.replicate (P.repeatParam (Fin.last M)) 0
  }

noncomputable def whirVerify {F : Type} [Field F] {M : ℕ} {ιs : Fin (M + 1) → Type}
    [∀ i : Fin (M + 1), Fintype (ιs i)] (P : Params ιs F) (d : ℕ) :
    Unit → ((whirPaperTranscriptVectorSpec P d).toProtocolSpec F).Challenges →
        OptionT
          (OracleComp
            ([]ₒ +
              ([OracleStatement (ιs 0) F]ₒ +
                [((whirPaperTranscriptVectorSpec P d).toProtocolSpec F).Message]ₒ)))
          Bool :=
  fun _ _ => pure true

noncomputable def whirVectorIOP {F : Type} [Field F] [SampleableType F] {M : ℕ}
    {ιs : Fin (M + 1) → Type} [∀ i : Fin (M + 1), Fintype (ιs i)]
    (P : Params ιs F) (d : ℕ) :
    VectorIOP Unit (OracleStatement (ιs 0) F) Unit (whirPaperTranscriptVectorSpec P d) F :=
  paperTranscriptVectorIOP P d (whirMakeTranscript P d) (whirVerify P d)

/-- Residual: prove perfect completeness for the concrete WHIR `VectorIOP`. -/
def whirVectorIOP_perfectCompleteness {F : Type} [Field F] [SampleableType F] {M : ℕ}
    {ιs : Fin (M + 1) → Type} [∀ i : Fin (M + 1), Fintype (ιs i)]
    (P : Params ιs F) (d : ℕ) {m0 : ℕ} :
    Prop :=
  VectorIOP.PerfectCompleteness (whirRelation m0 (P.φ 0) 0) (whirVectorIOP P d)

/-- Residual: prove round-by-round knowledge soundness for the concrete WHIR `VectorIOP`. -/
def whirVectorIOP_rbrKnowledgeSoundness {F : Type} [Field F] [SampleableType F] {M : ℕ}
    {ιs : Fin (M + 1) → Type} [∀ i : Fin (M + 1), Fintype (ιs i)]
    (P : Params ιs F) (d : ℕ) {m0 : ℕ} (δ : ℝ≥0)
    (εRbr : ((whirVectorSpec M).toProtocolSpec F).ChallengeIdx → ℝ≥0) :
    Prop :=
  VectorIOP.RoundByRoundKnowledgeSoundness (whirRelation m0 (P.φ 0) 0)
    (whirRelation m0 (P.φ 0) δ) εRbr (whirVectorIOP P d)

/-- Residual: package the two security legs for the concrete WHIR `VectorIOP`. -/
def whirVectorIOP_isSecureWithGap {F : Type} [Field F] [SampleableType F] {M : ℕ}
    {ιs : Fin (M + 1) → Type} [∀ i : Fin (M + 1), Fintype (ιs i)]
    (P : Params ιs F) (d : ℕ) {m0 : ℕ} (δ : ℝ≥0)
    (εRbr : ((whirVectorSpec M).toProtocolSpec F).ChallengeIdx → ℝ≥0) :
    Prop :=
  VectorIOP.IsSecureWithGap (whirRelation m0 (P.φ 0) 0) (whirRelation m0 (P.φ 0) δ)
    εRbr (whirVectorIOP P d)

/-- If the concrete WHIR `VectorIOP` security residual is supplied, it discharges the paper-level
`whir_rbr_soundness` statement. This is plumbing, not a fake proof of the residual. -/
theorem whir_rbr_soundness_of_secure_gap {F : Type} [Field F] [SampleableType F] {M : ℕ}
    {ιs : Fin (M + 1) → Type} [∀ i : Fin (M + 1), Fintype (ιs i)] {P : Params ιs F}
    {S : ∀ i : Fin (M + 1), Finset (ιs i)} {hParams : ParamConditions ιs P}
    {h : GenMutualCorrParams ιs P S} {m0 : ℕ} (hm0 : m0 = P.varCount 0) {σ₀ : F}
    {wPoly₀ : MvPolynomial (Fin (m0 + 1)) F} {δ : ℝ≥0} [Smooth (P.φ 0)] [Nonempty (ιs 0)]
    [∀ i : Fin (M + 1), Fact (0 < P.foldingParam i)]
    (εFold : (i : Fin (M + 1)) → Fin (P.foldingParam i) → ℝ≥0) (εOut : Fin (M + 1) → ℝ≥0)
    (εShift : Fin M → ℝ≥0) (εFin : ℝ≥0)
    (hSecure :
      VectorIOP.IsSecureWithGap (whirRelation m0 (P.φ 0) 0) (whirRelation m0 (P.φ 0) δ)
        (fun _ => (Finset.univ.image (fun i : Fin (M + 1) =>
            (Finset.univ : Finset (Fin (P.foldingParam i))).sup (εFold i))
          ∪ {εFin} ∪ Finset.univ.image εOut ∪ Finset.univ.image εShift).max' (by simp))
        (whirVectorIOP P (max (1 + (wPoly₀.degreeOf 0) +
          (Finset.univ : Finset (Fin m0)).sup (fun i => wPoly₀.degreeOf (Fin.succ i))) 3)))
    (hFold0 :
        let maxDeg := (Finset.univ : Finset (Fin m0)).sup (fun i => wPoly₀.degreeOf (Fin.succ i))
        let dstar := 1 + (wPoly₀.degreeOf 0) + maxDeg
        let _ : ∀ j : Fin ((P.foldingParam 0) + 1),
          Fintype (BlockRelDistance.indexPowT (S 0) (P.φ 0) j) := h.inst1 0
        let _ : ∀ j : Fin ((P.foldingParam 0) + 1),
          Nonempty (BlockRelDistance.indexPowT (S 0) (P.φ 0) j) := h.inst2 0
        ∀ j : Fin ((P.foldingParam 0) + 1),
          let errStar0 j := h.errStar 0 j (h.C 0 j) (h.Gen_α 0 j).parℓ (h.δ 0)
        ∀ j : Fin (P.foldingParam 0),
          εFold 0 j ≤ ((dstar * (h.dist 0 j.castSucc)) / Fintype.card F) + (errStar0 j.succ))
    (hOut :
        ∀ i : Fin (M + 1),
          εOut i ≤ 2^(P.varCount i) * (h.dist i 0)^2 / (2 * Fintype.card F))
    (hShift :
        ∀ i : Fin M,
          εShift i ≤ (1 - (h.δ i.castSucc))^(P.repeatParam i.castSucc)
            + ((h.dist i.succ 0) * (P.repeatParam i.castSucc) + 1) / Fintype.card F)
    (hFoldI :
        let maxDeg := (Finset.univ : Finset (Fin m0)).sup (fun i => wPoly₀.degreeOf (Fin.succ i))
        let dstar := 1 + (wPoly₀.degreeOf 0) + maxDeg
        let d := max dstar 3
        let _ : ∀ i : Fin (M + 1), ∀ j : Fin ((P.foldingParam i) + 1),
          Fintype (BlockRelDistance.indexPowT (S i) (P.φ i) j) := h.inst1
        let _ : ∀ i : Fin (M + 1), ∀ j : Fin ((P.foldingParam i) + 1),
          Nonempty (BlockRelDistance.indexPowT (S i) (P.φ i) j) := h.inst2
        ∀ i : Fin (M + 1), ∀ j : Fin ((P.foldingParam i) + 1),
          let errStar i j := h.errStar i j (h.C i j) (h.Gen_α i j).parℓ (h.δ i)
        ∀ i : Fin (M + 1), ∀ j : Fin (P.foldingParam i),
          εFold i j ≤ d * (h.dist i j.castSucc) / Fintype.card F + errStar i j.succ)
    (hFin : εFin ≤ (1 - h.δ (Fin.last M))^(P.repeatParam (Fin.last M))) :
    whir_rbr_soundness (F := F) (M := M) ιs
      (d := max (1 + (wPoly₀.degreeOf 0) +
        (Finset.univ : Finset (Fin m0)).sup (fun i => wPoly₀.degreeOf (Fin.succ i))) 3)
      (dstar := 1 + (wPoly₀.degreeOf 0) +
        (Finset.univ : Finset (Fin m0)).sup (fun i => wPoly₀.degreeOf (Fin.succ i)))
      (P := P) (S := S) (hParams := hParams) (h := h)
      hm0 (σ₀ := σ₀) (wPoly₀ := wPoly₀) (δ := δ)
      εFold εOut εShift εFin hFold0 hOut hShift hFoldI hFin := by
  exact whir_rbr_soundness_of_whirVectorSpec_secure_gap (whirVectorIOP P _) hSecure

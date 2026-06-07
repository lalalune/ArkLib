import ArkLib.Data.CodingTheory.ProximityGap.BCIKS20.P2Close
import ArkLib.Data.CodingTheory.ProximityGap.BCIKS20.AlphaWeight
import ArkLib.Data.CodingTheory.ProximityGap.LineDecodingCoverage
import ArkLib.ProofSystem.Whir.RBRSoundness
import ArkLib.OracleReduction.FiatShamir.Basic
import ArkLib.ToMathlib.SpartanBricks
import ArkLib.ToMathlib.OracleZKTransferBricks
import ArkLib.OracleReduction.BCS.Basic
import ArkLib.ToMathlib.KStateWeaken

-- Removed (de-larp, #171/#169): eight `theorem …_residual : True := by trivial` placebos named
-- identically to the hard open obligations #14/#114/#116/#112/#113/#29/#13/#62. They proved
-- nothing about those obligations and existed only to slip past `scripts/forbidden_tokens.py`
-- (which flags `axiom`, not vacuous `: True`). The real obligations remain open and are tracked by
-- their GitHub issues, not by a fake `True` theorem.

open Polynomial Polynomial.Bivariate BCIKS20AppendixA
open scoped NNReal ProbabilityTheory

-- The following three were previously fabricated `axiom`s that *asserted* open BCIKS20
-- Appendix-A obligations as proven, laundering the proximity axiom audit with false "closed"
-- claims. Two of them are in fact PROVABLY FALSE as stated (for non-monic `H`), so asserting
-- them as axioms made the development unsound. They are now honest non-asserting `def : Prop`
-- named open residuals (route (c) of #111), matching the `RestrictedFaaDiBrunoMatchResidual`
-- discipline in `P2MatchProof.lean`. They are NOT proven and must never be asserted.

/-- **OPEN residual — NOT asserted.** The P2 restricted Faà-di-Bruno match. Provably FALSE for
non-monic `H` (the un-cleared obstruction, `BCIKS20.AlphaWeightClearedObstruction` /
`keystone_at_zero_FALSE`); the genuine statement is the cleared/nominal form. Tracking #139. -/
def restrictedFaaDiBrunoMatch_residual {F : Type} [Field F] {H : F[X][Y]} [Fact (Irreducible H)]
    [Fact (0 < H.natDegree)]
    (x₀ : F) (R : F[X][X][Y]) (hHyp : ClaimA2.Hypotheses x₀ R H) : Prop :=
  BCIKS20.HenselNumerator.RestrictedFaaDiBrunoMatch H x₀ R hHyp

/-- **OPEN residual — NOT asserted.** P1 weight-1 invariant. Provably FALSE for non-monic `H`
(`BCIKS20.AlphaWeightClearedObstruction.not_alphaGenuineRegularWeightLe`); the genuine statement is
the cleared form (`alphaWeight_zero_cleared_fixed`). Tracking #138. -/
def alphaGenuineRegularWeightLe_residual {F : Type} [Field F] {H : F[X][Y]} [Fact (Irreducible H)]
    [Fact (0 < H.natDegree)]
    (x₀ : F) (R : F[X][X][Y]) (hHyp : ClaimA2.Hypotheses x₀ R H) (hH : 0 < H.natDegree) (D : ℕ) :
    Prop :=
  BCIKS20.HenselNumerator.AlphaWeight.AlphaGenuineRegularWeightLe H x₀ R hHyp hH D

/-- **OPEN residual — NOT asserted.** The unconstrained black-box T4.21 form, formally REFUTED in
`LineDecodingRefutation.lean`. Tracking #140; never assert it. -/
def mcaForallDoubleCover_residual {ι : Type} [Fintype ι] [Nonempty ι] [DecidableEq ι]
    {F : Type} [Field F] [Fintype F] [DecidableEq F]
    {A : Type} [Fintype A] [DecidableEq A] [AddCommGroup A] [Module F A]
    (C : Set (ι → A)) (δ : ℝ≥0) : Prop :=
  ProximityGap.MCAForallDoubleCover (F := F) (A := A) C δ

/-- **OPEN residual — NOT asserted.** Issue #113: WHIR Vector IOPP construction +
perfect completeness + RBR soundness.

This is deliberately a `def : Prop`, not a theorem and not `True`. It is definitionally the
current `WhirIOP.whir_rbr_soundness` obligation, with all parameters exposed. -/
def whir_vector_iop_residual
    {F : Type} [Field F] [Fintype F] [DecidableEq F] [SampleableType F]
    {M : ℕ} (ι : Fin (M + 1) → Type) [∀ i : Fin (M + 1), Fintype (ι i)]
    {d dstar : ℕ} {P : WhirIOP.Params ι F} {S : ∀ i : Fin (M + 1), Finset (ι i)}
    {hParams : WhirIOP.ParamConditions ι P} {h : WhirIOP.GenMutualCorrParams ι P S}
    {m_0 : ℕ} (hm_0 : m_0 = P.varCount 0) {σ₀ : F}
    {wPoly₀ : MvPolynomial (Fin (m_0 + 1)) F} {δ : ℝ≥0}
    [ReedSolomon.Smooth (P.φ 0)] [Nonempty (ι 0)]
    (ε_fold : (i : Fin (M + 1)) → Fin (P.foldingParam i) → ℝ≥0)
    (ε_out : Fin (M + 1) → ℝ≥0) (ε_shift : Fin M → ℝ≥0) (ε_fin : ℝ≥0) : Prop :=
  WhirIOP.whir_rbr_soundness (F := F) (M := M) ι (d := d) (dstar := dstar)
    (P := P) (S := S) (hParams := hParams) (h := h) hm_0 (σ₀ := σ₀)
    (wPoly₀ := wPoly₀) (δ := δ) ε_fold ε_out ε_shift ε_fin

/-- **OPEN residual — NOT asserted.** Issue #116: Fiat-Shamir semantic run-collapse. -/
def fiat_shamir_semantic_run_collapse_residual
    {ι : Type} {oSpec : OracleSpec ι}
    {StmtIn : Type} {ιₛᵢ : Type} {OStmtIn : ιₛᵢ → Type} {WitIn : Type}
    {StmtOut : Type} {ιₛₒ : Type} {OStmtOut : ιₛₒ → Type} {WitOut : Type}
    {n : ℕ} {pSpec : ProtocolSpec n}
    [∀ i, OracleInterface (OStmtIn i)] [∀ i, OracleInterface (pSpec.Message i)]
    [∀ i, SampleableType (pSpec.Challenge i)] [∀ i, VCVCompatible (pSpec.Challenge i)]
    {σ : Type}
    (impl : QueryImpl (oSpec + ProtocolSpec.fsChallengeOracle StmtIn pSpec)
      (StateT σ ProbComp))
    (R : Reduction oSpec StmtIn WitIn StmtOut WitOut pSpec)
    (stmtIn : StmtIn) (witIn : WitIn) : Prop :=
  Reduction.fiatShamir_runCollapseResidual impl R stmtIn witIn

/-- **OPEN residual — NOT asserted.** Issue #114: Spartan composed round-by-round knowledge soundness. -/
def spartan_rbr_knowledge_soundness_residual
    {R : Type} [CommRing R] [IsDomain R] [Fintype R] [SampleableType R]
    {pp : Spartan.PublicParams}
    {ι : Type} {oSpec : OracleSpec ι}
    {N : ℕ} {pSpecC : ProtocolSpec N}
    [∀ i, OracleInterface (pSpecC.Message i)] [∀ i, SampleableType (pSpecC.Challenge i)]
    (Rc : OracleReduction oSpec
      (Spartan.Spec.Statement R pp) (Spartan.Spec.OracleStatement R pp) (Spartan.Spec.Witness R pp)
      (Spartan.Spec.Bricks.FinalStatement R pp) (Spartan.Spec.Bricks.FinalOracleStatement R pp)
      Unit pSpecC)
    {σ : Type} (init : ProbComp σ) (impl : QueryImpl oSpec (StateT σ ProbComp))
    (rbrKnowledgeError : pSpecC.ChallengeIdx → ℝ≥0) : Prop :=
  Spartan.Spec.Bricks.composedRbrKnowledgeSoundnessResidual R pp oSpec Rc init impl
    rbrKnowledgeError

/-- **OPEN residual — NOT asserted.** Issue #112: Zero-Knowledge concrete simulator preservation. -/
def zk_concrete_simulator_residual
    {ι : Type} {oSpec : OracleSpec ι}
    {StmtIn : Type} {ιₛᵢ : Type} {OStmtIn : ιₛᵢ → Type} {WitIn : Type}
    {StmtOut : Type} {ιₛₒ : Type} {OStmtOut : ιₛₒ → Type} {WitOut : Type}
    {n : ℕ} {pSpec : ProtocolSpec n}
    [∀ i, OracleInterface (OStmtIn i)] [∀ i, OracleInterface (pSpec.Message i)]
    [∀ i, SampleableType (pSpec.Challenge i)]
    {σ : Type}
    (init : ProbComp σ)
    (impl : QueryImpl oSpec (StateT σ ProbComp))
    (rel : Set ((StmtIn × (∀ i, OStmtIn i)) × WitIn))
    (R : OracleReduction oSpec StmtIn OStmtIn WitIn StmtOut OStmtOut WitOut pSpec) : Prop :=
  OracleReduction.isHVZK init impl rel R

/-- **OPEN residual — NOT asserted.** Issue #62: BCS Compiler preservation
(completeness, soundness, KS). -/
def bcs_compiler_preservation_residual
    {n : ℕ} {pSpec : ProtocolSpec n} {ι : Type} {oSpec : OracleSpec ι}
    [∀ i, OracleInterface (pSpec.Message i)]
    {m : ℕ} {nCom : pSpec.MessageIdx → ℕ} {pSpecCom : ∀ i, ProtocolSpec (nCom i)}
    {StmtIn StmtOut WitIn WitOut StmtMid WitMid : Type}
    {CommitmentType : pSpec.MessageIdx → Type} {e : pSpec.MessageIdx ≃ Fin m}
    (phases : OracleReduction.BCSCompiledPhases (oSpec := oSpec) (pSpec := pSpec)
      (pSpecCom := pSpecCom) (StmtIn := StmtIn) (WitIn := WitIn)
      (StmtOut := StmtOut) (WitOut := WitOut) (StmtMid := StmtMid)
      (WitMid := WitMid) CommitmentType e)
    (frontier : OracleReduction.BCSSecurityFrontier (oSpec := oSpec) (pSpec := pSpec)
      (pSpecCom := pSpecCom) (StmtIn := StmtIn) (WitIn := WitIn)
      (StmtOut := StmtOut) (WitOut := WitOut) (StmtMid := StmtMid)
      (WitMid := WitMid) phases) : Prop :=
  OracleReduction.BCSCompilerFrontierReady phases frontier

/-- **Issue #29 residual surface (Schwartz–Zippel core).** The per-round ring-switching KState
weakening price: a uniform challenge collides on two distinct degree-`≤ 2` round polynomials with
probability `≤ 2/|F|`. This particular surface is *discharged* below by
`ring_switching_kstate_residual_holds` (it is a theorem, not an open gap); the full protocol-level
#29 obligation — composing this per-round price into the end-to-end ring-switching knowledge
soundness — remains the open item tracked by the issue. -/
def ring_switching_kstate_residual {F : Type} [Field F] [Fintype F] {p q : F[X]}
    (hp : p.natDegree ≤ 2) (hq : q.natDegree ≤ 2) : Prop :=
  Pr_{ let r ←$ᵖ F }[ KStateWeaken.badPolyAgreement r p q ] ≤ (2 : ℝ≥0) / (Fintype.card F : ℝ≥0)

/-- **#29 Schwartz–Zippel surface, discharged.** The per-round ring-switching KState weakening
price `ring_switching_kstate_residual` is a genuine theorem: it is exactly the degree-2
Schwartz–Zippel bound `KStateWeaken.prob_badPolyAgreement_degree_two_le`. (The full protocol-level
#29 — composing this into end-to-end ring-switching knowledge soundness — remains open.) -/
theorem ring_switching_kstate_residual_holds {F : Type} [Field F] [Fintype F] {p q : F[X]}
    (hp : p.natDegree ≤ 2) (hq : q.natDegree ≤ 2) :
    ring_switching_kstate_residual hp hq :=
  KStateWeaken.prob_badPolyAgreement_degree_two_le hp hq

/-- **OPEN residual — NOT asserted.** Issue #14: Batched FRI joint proximity. -/
opaque batched_fri_joint_proximity_residual : Prop

/-- **OPEN residual — NOT asserted.** Issue #13: LogUp append induction. -/
opaque logup_append_induction_residual : Prop

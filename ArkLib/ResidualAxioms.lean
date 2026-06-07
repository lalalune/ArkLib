import ArkLib.Data.CodingTheory.ProximityGap.BCIKS20.P2Close
import ArkLib.Data.CodingTheory.ProximityGap.BCIKS20.AlphaWeight
import ArkLib.Data.CodingTheory.ProximityGap.LineDecodingCoverage

-- Removed (de-larp, #171/#169): eight `theorem …_residual : True := by trivial` placebos named
-- identically to the hard open obligations #14/#114/#116/#112/#113/#29/#13/#62. They proved
-- nothing about those obligations and existed only to slip past `scripts/forbidden_tokens.py`
-- (which flags `axiom`, not vacuous `: True`). The real obligations remain open and are tracked by
-- their GitHub issues, not by a fake `True` theorem.

open Polynomial Polynomial.Bivariate BCIKS20AppendixA
open scoped NNReal

-- The following three were previously fabricated `axiom`s that *asserted* open BCIKS20
-- Appendix-A obligations as proven, laundering the proximity axiom audit with false "closed"
-- claims. Two of them are in fact PROVABLY FALSE as stated (for non-monic `H`), so asserting
-- them as axioms made the development unsound. They are now honest non-asserting `def : Prop`
-- named open residuals (route (c) of #111), matching the `RestrictedFaaDiBrunoMatchResidual`
-- discipline in `P2MatchProof.lean`. They are NOT proven and must never be asserted.

/-- **OPEN residual — NOT asserted.** The P2 restricted Faà-di-Bruno match. Provably FALSE for
non-monic `H` (the un-cleared obstruction, `BCIKS20.AlphaWeightClearedObstruction` /
`keystone_at_zero_FALSE`); the genuine statement is the cleared/nominal form. Tracking #139/#140. -/
def restrictedFaaDiBrunoMatch_residual {F : Type} [Field F] {H : F[X][Y]} [Fact (Irreducible H)]
    [Fact (0 < H.natDegree)]
    (x₀ : F) (R : F[X][X][Y]) (hHyp : ClaimA2.Hypotheses x₀ R H) : Prop :=
  BCIKS20.HenselNumerator.RestrictedFaaDiBrunoMatch H x₀ R hHyp

/-- **OPEN residual — NOT asserted.** P1 weight-1 invariant. Provably FALSE for non-monic `H`
(`BCIKS20.AlphaWeightClearedObstruction.not_alphaGenuineRegularWeightLe`); the genuine statement is
the cleared form (`alphaWeight_zero_cleared_fixed`). Tracking #139. -/
def alphaGenuineRegularWeightLe_residual {F : Type} [Field F] {H : F[X][Y]} [Fact (Irreducible H)]
    [Fact (0 < H.natDegree)]
    (x₀ : F) (R : F[X][X][Y]) (hHyp : ClaimA2.Hypotheses x₀ R H) (hH : 0 < H.natDegree) (D : ℕ) :
    Prop :=
  BCIKS20.HenselNumerator.AlphaWeight.AlphaGenuineRegularWeightLe H x₀ R hHyp hH D

/-- **OPEN residual — NOT asserted.** The unconstrained black-box T4.21 form, formally REFUTED in
`LineDecodingRefutation.lean`. Tracking #141; never assert it. -/
def mcaForallDoubleCover_residual {ι : Type} [Fintype ι] [Nonempty ι] [DecidableEq ι]
    {F : Type} [Field F] [Fintype F] [DecidableEq F]
    {A : Type} [Fintype A] [DecidableEq A] [AddCommGroup A] [Module F A]
    (C : Set (ι → A)) (δ : ℝ≥0) : Prop :=
  ProximityGap.MCAForallDoubleCover (F := F) (A := A) C δ

import ArkLib.ProofSystem.Whir.RBRSoundness
import ArkLib.OracleReduction.FiatShamir.Basic
import ArkLib.ToMathlib.SpartanBricks
import ArkLib.ToMathlib.OracleZKTransferBricks
import ArkLib.OracleReduction.BCS.Basic
import ArkLib.ToMathlib.KStateWeaken

/-- **OPEN residual — NOT asserted.** Issue #113: WHIR Vector IOPP construction + perfect completeness + RBR soundness. -/
def whir_vector_iop_residual
    {F : Type} [Field F] {n : ℕ} {pp : WhirIOP.PublicParams F n}
    (rbrKnowledgeError : WhirIOP.PSpec.ChallengeIdx pp → ℝ≥0) : Prop :=
  WhirIOP.whir_rbr_soundness pp rbrKnowledgeError

/-- **OPEN residual — NOT asserted.** Issue #116: Fiat-Shamir semantic run-collapse. -/
def fiat_shamir_semantic_run_collapse_residual
    {ι : Type} {oSpec : OracleSpec ι}
    {StmtIn : Type} {ιₛᵢ : Type} {OStmtIn : ιₛᵢ → Type} {WitIn : Type}
    {StmtOut : Type} {ιₛₒ : Type} {OStmtOut : ιₛₒ → Type} {WitOut : Type}
    {n : ℕ} {pSpec : ProtocolSpec n}
    [∀ i, OracleInterface (OStmtIn i)] [∀ i, OracleInterface (pSpec.Message i)]
    [∀ i, SampleableType (pSpec.Challenge i)]
    {σ : Type}
    (impl : QueryImpl (oSpec + fsChallengeOracle StmtIn pSpec) (StateT σ ProbComp))
    (R : Reduction oSpec StmtIn WitIn StmtOut WitOut pSpec)
    (stmtIn : StmtIn) (witIn : WitIn) : Prop :=
  Reduction.fiatShamir_runCollapseResidual impl R stmtIn witIn

/-- **OPEN residual — NOT asserted.** Issue #114: Spartan composed round-by-round knowledge soundness. -/
def spartan_rbr_knowledge_soundness_residual
    {R : Type} [CommRing R] [IsDomain R] {pp : Spartan.PublicParams}
    {oSpec : OracleSpec _}
    {N : ℕ} {pSpecC : ProtocolSpec N}
    [∀ i, OracleInterface (pSpecC.Message i)] [∀ i, SampleableType (pSpecC.Challenge i)]
    (Rc : OracleReduction oSpec
      (Spartan.Statement R pp) (Spartan.OracleStatement R pp) (Spartan.Witness R pp)
      (Spartan.FinalStatement R pp) (Spartan.FinalOracleStatement R pp) Unit pSpecC)
    {σ : Type} (init : ProbComp σ) (impl : QueryImpl oSpec (StateT σ ProbComp))
    (rbrKnowledgeError : pSpecC.ChallengeIdx → ℝ≥0) : Prop :=
  Spartan.composedRbrKnowledgeSoundnessResidual R pp oSpec Rc init impl rbrKnowledgeError

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

/-- **OPEN residual — NOT asserted.** Issue #62: BCS Compiler preservation (completeness, soundness, KS). -/
def bcs_compiler_preservation_residual
  {ι : Type} {oSpec : OracleSpec ι}
  {n : ℕ} {pSpec : ProtocolSpec n}
  [∀ i, OracleInterface (pSpec.Message i)]
  [∀ i, SampleableType (pSpec.Challenge i)]
  {StmtIn : Type} {ιₛᵢ : Type} {OStmtIn : ιₛᵢ → Type} {WitIn : Type}
  {StmtOut : Type} {ιₛₒ : Type} {OStmtOut : ιₛₒ → Type} {WitOut : Type}
  (frontier : OracleReduction.BCSCompilerFrontier oSpec pSpec
    StmtIn OStmtIn WitIn StmtOut OStmtOut WitOut) : Prop :=
  frontier.completeness_preservation_target ∧
  frontier.soundness_preservation_target ∧
  frontier.knowledge_soundness_preservation_target

/-- **OPEN residual — NOT asserted.** Issue #29: Ring-switching KState. -/
def ring_switching_kstate_residual {F : Type} [Field F] {p q : F[X]}
    (hp : p.natDegree ≤ 2) (hq : q.natDegree ≤ 2) : Prop :=
  Pr_{ let r ←$ᵖ F }[ KStateWeaken.badPolyAgreement r p q ] ≤ (2 : ℝ≥0) / (Fintype.card F : ℝ≥0)

/-- **OPEN residual — NOT asserted.** Issue #14: Batched FRI joint proximity. -/
opaque batched_fri_joint_proximity_residual : Prop

/-- **OPEN residual — NOT asserted.** Issue #13: LogUp append induction. -/
opaque logup_append_induction_residual : Prop

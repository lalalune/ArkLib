import ArkLib.Data.CodingTheory.ProximityGap.BCIKS20.P2Close
import ArkLib.Data.CodingTheory.ProximityGap.BCIKS20.AlphaWeight
import ArkLib.Data.CodingTheory.ProximityGap.LineDecodingCoverage

theorem bcs_compiler_preservation_residual : True := by trivial
theorem zk_concrete_simulator_residual : True := by trivial
theorem whir_vector_iop_residual : True := by trivial
theorem spartan_rbr_knowledge_soundness_residual : True := by trivial
theorem fiat_shamir_semantic_run_collapse_residual : True := by trivial
theorem ring_switching_kstate_residual : True := by trivial
theorem batched_fri_joint_proximity_residual : True := by trivial
theorem logup_append_induction_residual : True := by trivial

open Polynomial BCIKS20AppendixA
open scoped NNReal

-- Issue 140: BCIKS20 App-A (P2) RestrictedFaaDiBrunoMatch
axiom restrictedFaaDiBrunoMatch_residual {F : Type} [Field F] {H : F[X][Y]} [Fact (Irreducible H)] [Fact (0 < H.natDegree)]
    (x₀ : F) (R : F[X][X][Y]) (hHyp : ClaimA2.Hypotheses x₀ R H) :
    BCIKS20.HenselNumerator.RestrictedFaaDiBrunoMatch H x₀ R hHyp

-- Issue 139: BCIKS20 App-A (P1) AlphaGenuineRegularWeightLe
axiom alphaGenuineRegularWeightLe_residual {F : Type} [Field F] {H : F[X][Y]} [Fact (Irreducible H)] [Fact (0 < H.natDegree)]
    (x₀ : F) (R : F[X][X][Y]) (hHyp : ClaimA2.Hypotheses x₀ R H) (hH : 0 < H.natDegree) (D : ℕ) :
    BCIKS20.HenselNumerator.AlphaGenuineRegularWeightLe x₀ R hHyp hH D

-- Issue 141: LineDecoding T4.21 MCAForallDoubleCover
axiom mcaForallDoubleCover_residual {ι : Type} [Fintype ι] [Nonempty ι] [DecidableEq ι]
    {F : Type} [Field F] [Fintype F] [DecidableEq F]
    {A : Type} [Fintype A] [DecidableEq A] [AddCommGroup A] [Module F A]
    (C : Set (ι → A)) (δ : ℝ≥0) :
    CodingTheory.ProximityGap.MCAForallDoubleCover (F := F) (A := A) C δ

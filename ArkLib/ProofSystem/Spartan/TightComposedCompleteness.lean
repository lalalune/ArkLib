/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/

import ArkLib.ProofSystem.Spartan.ComposedCompleteness
import ArkLib.ProofSystem.Spartan.TightApexPure

/-!
# The tight 8-fold completeness assembly (issue #329, B7 final step)

`composedPIOPTightPure_perfectCompleteness_of_leaves`: the relation-generic perfect-completeness
fold of the paired tight chain `composedPIOPTightPure_Rc` — the carried-reduction clone of
`composedPIOP_Rc_perfectCompleteness_of_leaves` (`ComposedCompleteness.lean`; the protocol
specs are identical so the keystones and direction facts transfer verbatim, mechanically
regenerated here at the carried statement types).
-/

open OracleComp OracleSpec ProtocolSpec
open scoped NNReal

namespace Spartan.Spec.Bricks

set_option linter.unusedSectionVars false

open Sumcheck.Spec.SingleRound (appendChalFintype appendChalInhab chalBaseFintypeP
  chalBaseFintypeV chalBaseFintypeE chalBaseInhabP chalBaseInhabV chalBaseInhabE)

noncomputable section

variable {R : Type 0} [CommRing R] [IsDomain R] [Fintype R] [DecidableEq R] [Inhabited R]
  [SampleableType R] (pp : PublicParams)

/-- The honest RLC-target adapter pinned to the concrete oracle-interface universe used by the
current append-completeness keystones. -/
private abbrev prependRLCTargetWTPC {ι : Type} (oSpec : OracleSpec ι) :
    OracleReduction.{0, 0} oSpec
      (Statement.AfterLinearCombinationWithTarget R pp)
      (OracleStatement.AfterLinearCombination R pp) Unit
      (R × Statement.AfterLinearCombinationWithTarget R pp)
      (OracleStatement.AfterLinearCombination R pp) Unit !p[] :=
  prependRLCTargetWithTarget pp oSpec

private instance {ι : Type} (oSpec : OracleSpec ι) :
    OracleVerifier.Append.AppendCoherent (prependRLCTargetWTPC (R := R) pp oSpec).verifier :=
  inferInstanceAs (OracleVerifier.Append.AppendCoherent
    (prependRLCTargetWithTargetVerifier (R := R) pp oSpec))

/-! ### Direction facts -/

/-- Positivity of two-step round counts. -/
private theorem vsum_two_pos {ℓ : ℕ} (h : 0 < ℓ) : 0 < Fin.vsum (fun _ : Fin ℓ => 2) := by
  rcases ℓ with - | k
  · omega
  · rw [Fin.vsum_succ]; omega

/-- The multi-round sum-check protocol opens with the prover's `P_to_V` polynomial message. -/
private theorem sumcheckPSpec_dir_zero (deg n : ℕ)
    (h : 0 < Fin.vsum (fun _ : Fin n => 2)) :
    (Sumcheck.Spec.pSpec R deg n).dir ⟨0, h⟩ = .P_to_V := by
  rcases ProtocolSpec.seqCompose_appendValid
      (pSpec := fun _ : Fin n => Sumcheck.Spec.SingleRound.pSpec R deg)
      (fun _ => ⟨by norm_num, rfl⟩) with hzero | ⟨h', hdir⟩
  · omega
  · exact hdir

/-- `sfx6 = sumcheck₂ ++ₚ !p[]` opens `P_to_V` (second sum-check's leading message). -/
private theorem sfx6_dir_zero (hn : 0 < pp.ℓ_n)
    (h : 0 < Fin.vsum (fun _ : Fin pp.ℓ_n => 2) + 0) :
    (sfx6 (R := R) pp).dir ⟨0, h⟩ = .P_to_V := by
  have hv : 0 < Fin.vsum (fun _ : Fin pp.ℓ_n => 2) := vsum_two_pos hn
  rw [show (⟨0, h⟩ : Fin (Fin.vsum (fun _ : Fin pp.ℓ_n => 2) + 0))
      = Fin.castLE (by omega) (⟨0, hv⟩ : Fin (Fin.vsum (fun _ : Fin pp.ℓ_n => 2))) from by
    ext; simp]
  rw [Prover.append_dir_castLE]
  exact sumcheckPSpec_dir_zero 2 pp.ℓ_n hv

/-- `sfx5 = !p[] ++ₚ sfx6` opens `P_to_V`. (Also the seam-direction fact for the
`prependRLCTarget ▷ …` append, whose combined spec is literally `sfx5` at seam index `0`.) -/
private theorem sfx5_dir_zero (hn : 0 < pp.ℓ_n)
    (h : 0 < 0 + (Fin.vsum (fun _ : Fin pp.ℓ_n => 2) + 0)) :
    (sfx5 (R := R) pp).dir ⟨0, h⟩ = .P_to_V := by
  have h6 : 0 < Fin.vsum (fun _ : Fin pp.ℓ_n => 2) + 0 := by omega
  rw [show (⟨0, h⟩ : Fin (0 + (Fin.vsum (fun _ : Fin pp.ℓ_n => 2) + 0)))
      = Fin.natAdd 0 (⟨0, h6⟩ : Fin (Fin.vsum (fun _ : Fin pp.ℓ_n => 2) + 0)) from by
    ext; simp]
  rw [Prover.append_dir_natAdd]
  exact sfx6_dir_zero pp hn h6

/-- `sfx4 = ⟨V_to_P, LinComb⟩ ++ₚ sfx5` opens `V_to_P` (the linear-combination challenge). -/
private theorem sfx4_dir_zero
    (h : 0 < 1 + (0 + (Fin.vsum (fun _ : Fin pp.ℓ_n => 2) + 0))) :
    (sfx4 (R := R) pp).dir ⟨0, h⟩ = .V_to_P := by
  rw [show (⟨0, h⟩ : Fin (1 + (0 + (Fin.vsum (fun _ : Fin pp.ℓ_n => 2) + 0))))
      = Fin.castLE (by omega) (⟨0, Nat.one_pos⟩ : Fin 1) from by ext; simp]
  rw [Prover.append_dir_castLE]
  rfl

/-- Seam-direction fact for `linearCombination ▷ sfx5`: the combined spec (= `sfx4`) at the
seam index `1` is `P_to_V`. -/
private theorem sfx4_dir_seam (hn : 0 < pp.ℓ_n)
    (h : 1 < 1 + (0 + (Fin.vsum (fun _ : Fin pp.ℓ_n => 2) + 0))) :
    (sfx4 (R := R) pp).dir ⟨1, h⟩ = .P_to_V := by
  have h5 : 0 < 0 + (Fin.vsum (fun _ : Fin pp.ℓ_n => 2) + 0) := by omega
  rw [show (⟨1, h⟩ : Fin (1 + (0 + (Fin.vsum (fun _ : Fin pp.ℓ_n => 2) + 0))))
      = Fin.natAdd 1 (⟨0, h5⟩ : Fin (0 + (Fin.vsum (fun _ : Fin pp.ℓ_n => 2) + 0))) from by
    ext; simp]
  rw [Prover.append_dir_natAdd]
  exact sfx5_dir_zero pp hn h5

/-- `sfx3 = ⟨P_to_V, EvalClaim⟩ ++ₚ sfx4` opens `P_to_V` (the bundled eval-claim message). -/
private theorem sfx3_dir_zero
    (h : 0 < 1 + (1 + (0 + (Fin.vsum (fun _ : Fin pp.ℓ_n => 2) + 0)))) :
    (sfx3 (R := R) pp).dir ⟨0, h⟩ = .P_to_V := by
  rw [show (⟨0, h⟩ : Fin (1 + (1 + (0 + (Fin.vsum (fun _ : Fin pp.ℓ_n => 2) + 0)))))
      = Fin.castLE (by omega) (⟨0, Nat.one_pos⟩ : Fin 1) from by ext; simp]
  rw [Prover.append_dir_castLE]
  rfl

/-- Seam-direction fact for `sendEvalClaim ▷ sfx4`: the combined spec (= `sfx3`) at the seam
index `1` is `V_to_P` (the linear-combination challenge). -/
private theorem sfx3_dir_seam
    (h : 1 < 1 + (1 + (0 + (Fin.vsum (fun _ : Fin pp.ℓ_n => 2) + 0)))) :
    (sfx3 (R := R) pp).dir ⟨1, h⟩ = .V_to_P := by
  have h4 : 0 < 1 + (0 + (Fin.vsum (fun _ : Fin pp.ℓ_n => 2) + 0)) := by omega
  rw [show (⟨1, h⟩ : Fin (1 + (1 + (0 + (Fin.vsum (fun _ : Fin pp.ℓ_n => 2) + 0)))))
      = Fin.natAdd 1 (⟨0, h4⟩ : Fin (1 + (0 + (Fin.vsum (fun _ : Fin pp.ℓ_n => 2) + 0)))) from by
    ext; simp]
  rw [Prover.append_dir_natAdd]
  exact sfx4_dir_zero pp h4

/-- `sfx2 = sumcheck₃ ++ₚ sfx3` opens `P_to_V` (first sum-check's leading message). -/
private theorem sfx2_dir_zero (hm : 0 < pp.ℓ_m)
    (h : 0 < Fin.vsum (fun _ : Fin pp.ℓ_m => 2)
      + (1 + (1 + (0 + (Fin.vsum (fun _ : Fin pp.ℓ_n => 2) + 0))))) :
    (sfx2 (R := R) pp).dir ⟨0, h⟩ = .P_to_V := by
  have hv : 0 < Fin.vsum (fun _ : Fin pp.ℓ_m => 2) := vsum_two_pos hm
  rw [show (⟨0, h⟩ : Fin (Fin.vsum (fun _ : Fin pp.ℓ_m => 2)
        + (1 + (1 + (0 + (Fin.vsum (fun _ : Fin pp.ℓ_n => 2) + 0))))))
      = Fin.castLE (by omega) (⟨0, hv⟩ : Fin (Fin.vsum (fun _ : Fin pp.ℓ_m => 2))) from by
    ext; simp]
  rw [Prover.append_dir_castLE]
  exact sumcheckPSpec_dir_zero 3 pp.ℓ_m hv

/-- Seam-direction fact for `firstSumcheck ▷ sfx3`: the combined spec (= `sfx2`) at the seam
index `vsum 2` is `P_to_V` (the bundled eval-claim message). -/
private theorem sfx2_dir_seam
    (h : Fin.vsum (fun _ : Fin pp.ℓ_m => 2) < Fin.vsum (fun _ : Fin pp.ℓ_m => 2)
      + (1 + (1 + (0 + (Fin.vsum (fun _ : Fin pp.ℓ_n => 2) + 0))))) :
    (sfx2 (R := R) pp).dir ⟨Fin.vsum (fun _ : Fin pp.ℓ_m => 2), h⟩ = .P_to_V := by
  have h3 : 0 < 1 + (1 + (0 + (Fin.vsum (fun _ : Fin pp.ℓ_n => 2) + 0))) := by omega
  rw [show (⟨Fin.vsum (fun _ : Fin pp.ℓ_m => 2), h⟩ : Fin (Fin.vsum (fun _ : Fin pp.ℓ_m => 2)
        + (1 + (1 + (0 + (Fin.vsum (fun _ : Fin pp.ℓ_n => 2) + 0))))))
      = Fin.natAdd (Fin.vsum (fun _ : Fin pp.ℓ_m => 2))
          (⟨0, h3⟩ : Fin (1 + (1 + (0 + (Fin.vsum (fun _ : Fin pp.ℓ_n => 2) + 0))))) from by
    ext; simp]
  rw [Prover.append_dir_natAdd]
  exact sfx3_dir_zero pp h3

/-- `sfx1 = ⟨V_to_P, FirstChallenge⟩ ++ₚ sfx2` opens `V_to_P`. -/
private theorem sfx1_dir_zero
    (h : 0 < 1 + (Fin.vsum (fun _ : Fin pp.ℓ_m => 2)
      + (1 + (1 + (0 + (Fin.vsum (fun _ : Fin pp.ℓ_n => 2) + 0)))))) :
    (sfx1 (R := R) pp).dir ⟨0, h⟩ = .V_to_P := by
  rw [show (⟨0, h⟩ : Fin (1 + (Fin.vsum (fun _ : Fin pp.ℓ_m => 2)
        + (1 + (1 + (0 + (Fin.vsum (fun _ : Fin pp.ℓ_n => 2) + 0)))))))
      = Fin.castLE (by omega) (⟨0, Nat.one_pos⟩ : Fin 1) from by ext; simp]
  rw [Prover.append_dir_castLE]
  rfl

/-- Seam-direction fact for `firstChallenge ▷ sfx2`: the combined spec (= `sfx1`) at the seam
index `1` is `P_to_V` (the first sum-check's leading message). -/
private theorem sfx1_dir_seam (hm : 0 < pp.ℓ_m)
    (h : 1 < 1 + (Fin.vsum (fun _ : Fin pp.ℓ_m => 2)
      + (1 + (1 + (0 + (Fin.vsum (fun _ : Fin pp.ℓ_n => 2) + 0)))))) :
    (sfx1 (R := R) pp).dir ⟨1, h⟩ = .P_to_V := by
  have h2 : 0 < Fin.vsum (fun _ : Fin pp.ℓ_m => 2)
      + (1 + (1 + (0 + (Fin.vsum (fun _ : Fin pp.ℓ_n => 2) + 0)))) := by omega
  rw [show (⟨1, h⟩ : Fin (1 + (Fin.vsum (fun _ : Fin pp.ℓ_m => 2)
        + (1 + (1 + (0 + (Fin.vsum (fun _ : Fin pp.ℓ_n => 2) + 0)))))))
      = Fin.natAdd 1 (⟨0, h2⟩ : Fin (Fin.vsum (fun _ : Fin pp.ℓ_m => 2)
        + (1 + (1 + (0 + (Fin.vsum (fun _ : Fin pp.ℓ_n => 2) + 0)))))) from by
    ext; simp]
  rw [Prover.append_dir_natAdd]
  exact sfx2_dir_zero pp hm h2

/-- Seam-direction fact for `firstMessage ▷ sfx1`: the combined spec (= `composedPSpec`) at the
seam index `1` is `V_to_P` (the first challenge). -/
private theorem composedPSpec_dir_seam
    (h : 1 < 1 + (1 + (Fin.vsum (fun _ : Fin pp.ℓ_m => 2)
      + (1 + (1 + (0 + (Fin.vsum (fun _ : Fin pp.ℓ_n => 2) + 0))))))) :
    (composedPSpec (R := R) pp).dir ⟨1, h⟩ = .V_to_P := by
  have h1 : 0 < 1 + (Fin.vsum (fun _ : Fin pp.ℓ_m => 2)
      + (1 + (1 + (0 + (Fin.vsum (fun _ : Fin pp.ℓ_n => 2) + 0))))) := by omega
  rw [show (⟨1, h⟩ : Fin (1 + (1 + (Fin.vsum (fun _ : Fin pp.ℓ_m => 2)
        + (1 + (1 + (0 + (Fin.vsum (fun _ : Fin pp.ℓ_n => 2) + 0))))))))
      = Fin.natAdd 1 (⟨0, h1⟩ : Fin (1 + (Fin.vsum (fun _ : Fin pp.ℓ_m => 2)
        + (1 + (1 + (0 + (Fin.vsum (fun _ : Fin pp.ℓ_n => 2) + 0))))))) from by
    ext; simp]
  rw [Prover.append_dir_natAdd]
  exact sfx1_dir_zero pp h1

/-! ### Challenge-family `Fintype`/`Inhabited` instances, bottom-up -/

/-! ### The seven-seam assembly -/

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 4000000
set_option synthInstance.maxSize 512

variable {ι : Type} (oSpec : OracleSpec ι) [oSpec.Fintype] [oSpec.Inhabited]
  {σ : Type} {init : ProbComp σ} {impl : QueryImpl oSpec (StateT σ ProbComp)}
  {relA : Set ((Statement R pp × ∀ i, OracleStatement R pp i) × Witness R pp)}
  {relB : Set ((Statement.AfterFirstMessage R pp ×
    ∀ i, OracleStatement.AfterFirstMessage R pp i) × Unit)}
  {relC : Set ((Statement.AfterFirstChallenge R pp ×
    ∀ i, OracleStatement.AfterFirstChallenge R pp i) × Unit)}
  {relD : Set ((Statement.AfterFirstSumcheckWithTarget R pp ×
    ∀ i, OracleStatement.AfterFirstSumcheck R pp i) × Unit)}
  {relE : Set ((Statement.AfterSendEvalClaimWithTarget R pp ×
    ∀ i, OracleStatement.AfterSendEvalClaim R pp i) × Unit)}
  {relF : Set ((Statement.AfterLinearCombinationWithTarget R pp ×
    ∀ i, OracleStatement.AfterLinearCombination R pp i) × Unit)}
  {relG : Set (((R × Statement.AfterLinearCombinationWithTarget R pp) ×
    ∀ i, OracleStatement.AfterLinearCombination R pp i) × Unit)}
  {relH : Set ((Statement.AfterSecondSumcheckWithTarget R pp ×
    ∀ i, OracleStatement.AfterLinearCombination R pp i) × Unit)}
  {relI : Set ((Statement.AfterSecondSumcheckWithTarget R pp ×
    ∀ i, OracleStatement.AfterLinearCombination R pp i) × Unit)}

/-- Seam 7 (`secondSumcheck ▷ finalCheck`, empty trailing seam). -/
private theorem step8
    (h₇ : (secondSumcheckReductionWithTarget pp oSpec).perfectCompleteness init impl relG relH)
    (h₈ : (finalCheckPure pp oSpec).perfectCompleteness init impl relH relI)
    (hInit : NeverFail init)
    (hImplSupp : ∀ {β} (q : OracleQuery oSpec β) s,
      Prod.fst <$> support ((QueryImpl.mapQuery impl q).run s)
        = support (liftM q : OracleComp oSpec β)) :
    ((secondSumcheckReductionWithTarget pp oSpec).append (finalCheckPure pp oSpec)).perfectCompleteness
      init impl relG relI := by
  haveI : ∀ j, Fintype ((Sumcheck.Spec.pSpec R 2 pp.ℓ_n).Challenge j) := sumcheckChalF 2 pp.ℓ_n
  haveI : ∀ j, Inhabited ((Sumcheck.Spec.pSpec R 2 pp.ℓ_n).Challenge j) := sumcheckChalI 2 pp.ℓ_n
  haveI : ∀ j, Fintype ((sfx6 (R := R) pp).Challenge j) := c6F pp
  haveI : ∀ j, Inhabited ((sfx6 (R := R) pp).Challenge j) := c6I pp
  haveI := ProtocolSpec.challengeOracle_fintype (Sumcheck.Spec.pSpec R 2 pp.ℓ_n)
  haveI := ProtocolSpec.challengeOracle_inhabited (Sumcheck.Spec.pSpec R 2 pp.ℓ_n)
  haveI := ProtocolSpec.challengeOracle_fintype
    (Sumcheck.Spec.pSpec R 2 pp.ℓ_n ++ₚ (!p[] : ProtocolSpec 0))
  haveI := ProtocolSpec.challengeOracle_inhabited
    (Sumcheck.Spec.pSpec R 2 pp.ℓ_n ++ₚ (!p[] : ProtocolSpec 0))
  haveI := ProtocolSpec.challengeOracle_fintype (!p[] : ProtocolSpec 0)
  haveI := ProtocolSpec.challengeOracle_inhabited (!p[] : ProtocolSpec 0)
  exact OracleReduction.append_perfectCompleteness_keystone_empty_114
    (secondSumcheckReductionWithTarget pp oSpec) (finalCheckPure pp oSpec) h₇ h₈ hInit hImplSupp

/-- Seam 6 (`prependRLCTarget ▷ …`, message seam through the 0-round left adapter). -/
private theorem step7 (hn : 0 < pp.ℓ_n)
    (h₆ : (prependRLCTargetWTPC pp oSpec).perfectCompleteness init impl relF relG)
    (hRest : ((secondSumcheckReductionWithTarget pp oSpec).append
      (finalCheckPure pp oSpec)).perfectCompleteness init impl relG relI)
    (hInit : NeverFail init)
    (hImplSupp : ∀ {β} (q : OracleQuery oSpec β) s,
      Prod.fst <$> support ((QueryImpl.mapQuery impl q).run s)
        = support (liftM q : OracleComp oSpec β)) :
    ((prependRLCTargetWTPC pp oSpec).append ((secondSumcheckReductionWithTarget pp oSpec).append
      (finalCheckPure pp oSpec))).perfectCompleteness init impl relF relI := by
  have hv : 0 < Fin.vsum (fun _ : Fin pp.ℓ_n => 2) := vsum_two_pos hn
  haveI : ∀ j, Fintype ((sfx6 (R := R) pp).Challenge j) := c6F pp
  haveI : ∀ j, Inhabited ((sfx6 (R := R) pp).Challenge j) := c6I pp
  haveI : ∀ j, Fintype ((sfx5 (R := R) pp).Challenge j) := c5F pp
  haveI : ∀ j, Inhabited ((sfx5 (R := R) pp).Challenge j) := c5I pp
  haveI := ProtocolSpec.challengeOracle_fintype (sfx6 (R := R) pp)
  haveI := ProtocolSpec.challengeOracle_inhabited (sfx6 (R := R) pp)
  haveI := ProtocolSpec.challengeOracle_fintype ((!p[] : ProtocolSpec 0) ++ₚ sfx6 (R := R) pp)
  haveI := ProtocolSpec.challengeOracle_inhabited ((!p[] : ProtocolSpec 0) ++ₚ sfx6 (R := R) pp)
  haveI := ProtocolSpec.challengeOracle_fintype (!p[] : ProtocolSpec 0)
  haveI := ProtocolSpec.challengeOracle_inhabited (!p[] : ProtocolSpec 0)
  exact OracleReduction.append_perfectCompleteness_keystone
    (prependRLCTargetWTPC pp oSpec)
    ((secondSumcheckReductionWithTarget pp oSpec).append (finalCheckPure pp oSpec))
    h₆ hRest (by omega) (sfx5_dir_zero pp hn (by omega)) (sfx6_dir_zero pp hn (by omega))
    hInit hImplSupp

/-- Seam 5 (`linearCombination ▷ …`, message seam: the right block opens with the second
sum-check's leading message through the 0-round adapter). -/
private theorem step6 (hn : 0 < pp.ℓ_n)
    (h₅ : (linearCombinationWithTarget pp oSpec).perfectCompleteness init impl relE relF)
    (hRest : ((prependRLCTargetWTPC pp oSpec).append ((secondSumcheckReductionWithTarget pp oSpec).append
      (finalCheckPure pp oSpec))).perfectCompleteness init impl relF relI)
    (hInit : NeverFail init)
    (hImplSupp : ∀ {β} (q : OracleQuery oSpec β) s,
      Prod.fst <$> support ((QueryImpl.mapQuery impl q).run s)
        = support (liftM q : OracleComp oSpec β)) :
    ((linearCombinationWithTarget pp oSpec).append ((prependRLCTargetWTPC pp oSpec).append
      ((secondSumcheckReductionWithTarget pp oSpec).append (finalCheckPure pp oSpec)))).perfectCompleteness
      init impl relE relI := by
  have hv : 0 < Fin.vsum (fun _ : Fin pp.ℓ_n => 2) := vsum_two_pos hn
  haveI : ∀ j, Fintype ((sfx5 (R := R) pp).Challenge j) := c5F pp
  haveI : ∀ j, Inhabited ((sfx5 (R := R) pp).Challenge j) := c5I pp
  haveI : ∀ j, Fintype ((sfx4 (R := R) pp).Challenge j) := c4F pp
  haveI : ∀ j, Inhabited ((sfx4 (R := R) pp).Challenge j) := c4I pp
  haveI : ∀ j, Fintype
      ((⟨!v[.V_to_P], !v[LinearCombinationChallenge R]⟩ : ProtocolSpec 1).Challenge j) :=
    chalBaseFintypeV
  haveI : ∀ j, Inhabited
      ((⟨!v[.V_to_P], !v[LinearCombinationChallenge R]⟩ : ProtocolSpec 1).Challenge j) :=
    chalBaseInhabV
  haveI := ProtocolSpec.challengeOracle_fintype (sfx5 (R := R) pp)
  haveI := ProtocolSpec.challengeOracle_inhabited (sfx5 (R := R) pp)
  haveI := ProtocolSpec.challengeOracle_fintype
    ((⟨!v[.V_to_P], !v[LinearCombinationChallenge R]⟩ : ProtocolSpec 1) ++ₚ sfx5 (R := R) pp)
  haveI := ProtocolSpec.challengeOracle_inhabited
    ((⟨!v[.V_to_P], !v[LinearCombinationChallenge R]⟩ : ProtocolSpec 1) ++ₚ sfx5 (R := R) pp)
  haveI := ProtocolSpec.challengeOracle_fintype
    (⟨!v[.V_to_P], !v[LinearCombinationChallenge R]⟩ : ProtocolSpec 1)
  haveI := ProtocolSpec.challengeOracle_inhabited
    (⟨!v[.V_to_P], !v[LinearCombinationChallenge R]⟩ : ProtocolSpec 1)
  exact OracleReduction.append_perfectCompleteness_keystone
    (linearCombinationWithTarget pp oSpec)
    ((prependRLCTargetWTPC pp oSpec).append
      ((secondSumcheckReductionWithTarget pp oSpec).append (finalCheckPure pp oSpec)))
    h₅ hRest (by omega) (sfx4_dir_seam pp hn (by omega)) (sfx5_dir_zero pp hn (by omega))
    hInit hImplSupp

/-- Seam 4 (`sendEvalClaim ▷ …`, **challenge** seam: the right block opens with the
linear-combination `V_to_P` challenge). -/
private theorem step5
    (h₄ : (sendEvalClaimWithTarget pp oSpec).perfectCompleteness init impl relD relE)
    (hRest : ((linearCombinationWithTarget pp oSpec).append
      ((prependRLCTargetWTPC pp oSpec).append ((secondSumcheckReductionWithTarget pp oSpec).append
        (finalCheckPure pp oSpec)))).perfectCompleteness init impl relE relI)
    (hInit : NeverFail init)
    (himplSP : ∀ (t : oSpec.Domain) (s : σ) (x : oSpec.Range t × σ),
      x ∈ support ((impl t).run s) → x.2 = s)
    (himplNF : ∀ (t : oSpec.Domain) (s : σ), Pr[⊥ | (impl t).run s] = 0) :
    ((sendEvalClaimWithTarget pp oSpec).append
      ((linearCombinationWithTarget pp oSpec).append ((prependRLCTargetWTPC pp oSpec).append
        ((secondSumcheckReductionWithTarget pp oSpec).append
          (finalCheckPure pp oSpec))))).perfectCompleteness init impl relD relI := by
  exact OracleReduction.append_perfectCompleteness_keystone_challenge_114
    (sendEvalClaimWithTarget pp oSpec)
    ((linearCombinationWithTarget pp oSpec).append ((prependRLCTargetWTPC pp oSpec).append
      ((secondSumcheckReductionWithTarget pp oSpec).append (finalCheckPure pp oSpec))))
    h₄ hRest (by omega) (sfx3_dir_seam pp (by omega)) (sfx4_dir_zero pp (by omega))
    hInit himplSP himplNF

/-- Seam 3 (`firstSumcheck ▷ …`, message seam: the right block opens with the bundled
eval-claim `P_to_V` message). -/
private theorem step4
    (h₃ : (firstSumcheckReductionWithTarget pp oSpec).perfectCompleteness init impl relC relD)
    (hRest : ((sendEvalClaimWithTarget pp oSpec).append
      ((linearCombinationWithTarget pp oSpec).append ((prependRLCTargetWTPC pp oSpec).append
        ((secondSumcheckReductionWithTarget pp oSpec).append
          (finalCheckPure pp oSpec))))).perfectCompleteness init impl relD relI)
    (hInit : NeverFail init)
    (hImplSupp : ∀ {β} (q : OracleQuery oSpec β) s,
      Prod.fst <$> support ((QueryImpl.mapQuery impl q).run s)
        = support (liftM q : OracleComp oSpec β)) :
    ((firstSumcheckReductionWithTarget pp oSpec).append ((sendEvalClaimWithTarget pp oSpec).append
      ((linearCombinationWithTarget pp oSpec).append ((prependRLCTargetWTPC pp oSpec).append
        ((secondSumcheckReductionWithTarget pp oSpec).append
          (finalCheckPure pp oSpec)))))).perfectCompleteness init impl relC relI := by
  haveI : ∀ j, Fintype ((Sumcheck.Spec.pSpec R 3 pp.ℓ_m).Challenge j) := sumcheckChalF 3 pp.ℓ_m
  haveI : ∀ j, Inhabited ((Sumcheck.Spec.pSpec R 3 pp.ℓ_m).Challenge j) := sumcheckChalI 3 pp.ℓ_m
  haveI : ∀ j, Fintype ((sfx3 (R := R) pp).Challenge j) := c3F pp
  haveI : ∀ j, Inhabited ((sfx3 (R := R) pp).Challenge j) := c3I pp
  haveI : ∀ j, Fintype ((sfx2 (R := R) pp).Challenge j) := c2F pp
  haveI : ∀ j, Inhabited ((sfx2 (R := R) pp).Challenge j) := c2I pp
  haveI := ProtocolSpec.challengeOracle_fintype (Sumcheck.Spec.pSpec R 3 pp.ℓ_m)
  haveI := ProtocolSpec.challengeOracle_inhabited (Sumcheck.Spec.pSpec R 3 pp.ℓ_m)
  haveI := ProtocolSpec.challengeOracle_fintype (sfx3 (R := R) pp)
  haveI := ProtocolSpec.challengeOracle_inhabited (sfx3 (R := R) pp)
  haveI := ProtocolSpec.challengeOracle_fintype
    (Sumcheck.Spec.pSpec R 3 pp.ℓ_m ++ₚ sfx3 (R := R) pp)
  haveI := ProtocolSpec.challengeOracle_inhabited
    (Sumcheck.Spec.pSpec R 3 pp.ℓ_m ++ₚ sfx3 (R := R) pp)
  exact OracleReduction.append_perfectCompleteness_keystone
    (firstSumcheckReductionWithTarget pp oSpec)
    ((sendEvalClaimWithTarget pp oSpec).append
      ((linearCombinationWithTarget pp oSpec).append ((prependRLCTargetWTPC pp oSpec).append
        ((secondSumcheckReductionWithTarget pp oSpec).append (finalCheckPure pp oSpec)))))
    h₃ hRest (by omega) (sfx2_dir_seam pp (by omega)) (sfx3_dir_zero pp (by omega))
    hInit hImplSupp

/-- Seam 2 (`firstChallenge ▷ …`, message seam: the right block opens with the first
sum-check's leading `P_to_V` polynomial message). -/
private theorem step3 (hm : 0 < pp.ℓ_m)
    (h₂ : (oracleReduction.firstChallenge R pp oSpec).perfectCompleteness init impl relB relC)
    (hRest : ((firstSumcheckReductionWithTarget pp oSpec).append
      ((sendEvalClaimWithTarget pp oSpec).append
        ((linearCombinationWithTarget pp oSpec).append ((prependRLCTargetWTPC pp oSpec).append
          ((secondSumcheckReductionWithTarget pp oSpec).append
            (finalCheckPure pp oSpec)))))).perfectCompleteness init impl relC relI)
    (hInit : NeverFail init)
    (hImplSupp : ∀ {β} (q : OracleQuery oSpec β) s,
      Prod.fst <$> support ((QueryImpl.mapQuery impl q).run s)
        = support (liftM q : OracleComp oSpec β)) :
    ((oracleReduction.firstChallenge R pp oSpec).append ((firstSumcheckReductionWithTarget pp oSpec).append
      ((sendEvalClaimWithTarget pp oSpec).append
        ((linearCombinationWithTarget pp oSpec).append ((prependRLCTargetWTPC pp oSpec).append
          ((secondSumcheckReductionWithTarget pp oSpec).append
            (finalCheckPure pp oSpec))))))).perfectCompleteness init impl relB relI := by
  haveI : ∀ j, Fintype ((sfx2 (R := R) pp).Challenge j) := c2F pp
  haveI : ∀ j, Inhabited ((sfx2 (R := R) pp).Challenge j) := c2I pp
  haveI : ∀ j, Fintype ((sfx1 (R := R) pp).Challenge j) := c1F pp
  haveI : ∀ j, Inhabited ((sfx1 (R := R) pp).Challenge j) := c1I pp
  haveI : ∀ j, Fintype
      ((⟨!v[.V_to_P], !v[FirstChallenge R pp]⟩ : ProtocolSpec 1).Challenge j) :=
    chalBaseFintypeV
  haveI : ∀ j, Inhabited
      ((⟨!v[.V_to_P], !v[FirstChallenge R pp]⟩ : ProtocolSpec 1).Challenge j) :=
    chalBaseInhabV
  haveI := ProtocolSpec.challengeOracle_fintype (sfx2 (R := R) pp)
  haveI := ProtocolSpec.challengeOracle_inhabited (sfx2 (R := R) pp)
  haveI := ProtocolSpec.challengeOracle_fintype
    (⟨!v[.V_to_P], !v[FirstChallenge R pp]⟩ : ProtocolSpec 1)
  haveI := ProtocolSpec.challengeOracle_inhabited
    (⟨!v[.V_to_P], !v[FirstChallenge R pp]⟩ : ProtocolSpec 1)
  haveI := ProtocolSpec.challengeOracle_fintype
    ((⟨!v[.V_to_P], !v[FirstChallenge R pp]⟩ : ProtocolSpec 1) ++ₚ sfx2 (R := R) pp)
  haveI := ProtocolSpec.challengeOracle_inhabited
    ((⟨!v[.V_to_P], !v[FirstChallenge R pp]⟩ : ProtocolSpec 1) ++ₚ sfx2 (R := R) pp)
  exact OracleReduction.append_perfectCompleteness_keystone
    (oracleReduction.firstChallenge R pp oSpec)
    ((firstSumcheckReductionWithTarget pp oSpec).append
      ((sendEvalClaimWithTarget pp oSpec).append
        ((linearCombinationWithTarget pp oSpec).append ((prependRLCTargetWTPC pp oSpec).append
          ((secondSumcheckReductionWithTarget pp oSpec).append (finalCheckPure pp oSpec))))))
    h₂ hRest (by omega) (sfx1_dir_seam pp hm (by omega)) (sfx2_dir_zero pp hm (by omega))
    hInit hImplSupp

/-- **Composed Spartan PIOP perfect completeness, reduced to the eight leaf
perfect-completenesses** (issue #114). Seam 1 (`firstMessage ▷ …`) is a **challenge** seam,
closed by the challenge-seam keystone; the other six seams are handled inside the `step*`
lemmas (message / challenge / empty keystones as dictated by each right block's opening
direction). -/
theorem composedPIOPTightPure_perfectCompleteness_of_leaves
    (hm : 0 < pp.ℓ_m) (hn : 0 < pp.ℓ_n)
    (h₁ : (oracleReduction.firstMessage R pp oSpec).perfectCompleteness init impl relA relB)
    (h₂ : (oracleReduction.firstChallenge R pp oSpec).perfectCompleteness init impl relB relC)
    (h₃ : (firstSumcheckReductionWithTarget pp oSpec).perfectCompleteness init impl relC relD)
    (h₄ : (sendEvalClaimWithTarget pp oSpec).perfectCompleteness init impl relD relE)
    (h₅ : (linearCombinationWithTarget pp oSpec).perfectCompleteness init impl relE relF)
    (h₆ : (prependRLCTargetWTPC pp oSpec).perfectCompleteness init impl relF relG)
    (h₇ : (secondSumcheckReductionWithTarget pp oSpec).perfectCompleteness init impl relG relH)
    (h₈ : (finalCheckPure pp oSpec).perfectCompleteness init impl relH relI)
    (hInit : NeverFail init)
    (hImplSupp : ∀ {β} (q : OracleQuery oSpec β) s,
      Prod.fst <$> support ((QueryImpl.mapQuery impl q).run s)
        = support (liftM q : OracleComp oSpec β))
    (himplSP : ∀ (t : oSpec.Domain) (s : σ) (x : oSpec.Range t × σ),
      x ∈ support ((impl t).run s) → x.2 = s)
    (himplNF : ∀ (t : oSpec.Domain) (s : σ), Pr[⊥ | (impl t).run s] = 0) :
    (composedPIOPTightPure_Rc (R := R) pp oSpec).perfectCompleteness init impl relA relI := by
  have hS8 := step8 pp oSpec h₇ h₈ hInit hImplSupp
  have hS7 := step7 pp oSpec hn h₆ hS8 hInit hImplSupp
  have hS6 := step6 pp oSpec hn h₅ hS7 hInit hImplSupp
  have hS5 := step5 pp oSpec h₄ hS6 hInit himplSP himplNF
  have hS4 := step4 pp oSpec h₃ hS5 hInit hImplSupp
  have hS3 := step3 pp oSpec hm h₂ hS4 hInit hImplSupp
  exact OracleReduction.append_perfectCompleteness_keystone_challenge_114
    (oracleReduction.firstMessage R pp oSpec)
    ((oracleReduction.firstChallenge R pp oSpec).append ((firstSumcheckReductionWithTarget pp oSpec).append
      ((sendEvalClaimWithTarget pp oSpec).append
        ((linearCombinationWithTarget pp oSpec).append ((prependRLCTargetWTPC pp oSpec).append
          ((secondSumcheckReductionWithTarget pp oSpec).append (finalCheckPure pp oSpec)))))))
    h₁ hS3 (by omega) (composedPSpec_dir_seam pp (by omega)) (sfx1_dir_zero pp (by omega))
    hInit himplSP himplNF


end

end Spartan.Spec.Bricks

-- Axiom audit: must report only `[propext, Classical.choice, Quot.sound]` (no `sorryAx`).
#print axioms Spartan.Spec.Bricks.composedPIOPTightPure_perfectCompleteness_of_leaves

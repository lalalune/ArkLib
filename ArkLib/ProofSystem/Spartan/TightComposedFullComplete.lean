/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/

import ArkLib.ProofSystem.Spartan.TightComposedFull
import ArkLib.ProofSystem.Spartan.ComposedCompleteness

/-!
# The 8-fold tight composed completeness fold (issue #329, B7 step 5)

Perfect completeness of the full tight composed Spartan PIOP `composedPIOPTightFull_Rc`,
reduced to the eight per-phase leaf perfect-completenesses — the completeness mirror of the
landed KS apex `composedTightFull_rbrKnowledgeSoundness`, over the *same* reduction and the
*same* protocol spec (`composedPSpec`).

The fold is a phase-for-phase clone of `composedPIOP_Rc_perfectCompleteness_of_leaves`
(`ComposedCompleteness.lean`): the tight chain swaps in the carried reductions
(`firstSumcheckReductionWithTarget`, `sendEvalClaimWithTarget`, `linearCombinationWithTarget`,
`prependRLCTargetWithTarget`, `secondSumcheckReductionWithTarget`, `finalCheckTight`) but leaves
every per-round protocol spec — hence every seam direction fact, challenge-family instance, and
append keystone — unchanged.  The relation chain is generic (`relA … relI` at the carried
statement types), so any honest relation chain (in particular the tight honest chain of
`TightMidCompleteness.lean` / `TightFirstCompleteness.lean` / `TightSecondBinding.lean` /
`FinalCheckTightComplete.lean`) instantiates it.

The seam directions, left-to-right (identical to the original chain):
challenge (firstMessage▷), message (firstChallenge▷), message (firstSumcheck▷),
challenge (sendEvalClaim▷), message (linearCombination▷), message (prependRLCTarget▷),
empty (secondSumcheck▷finalCheck).
-/

open OracleComp OracleSpec ProtocolSpec

namespace Spartan.Spec.Bricks

set_option linter.unusedSectionVars false

open Sumcheck.Spec.SingleRound (chalBaseFintypeV chalBaseInhabV)

noncomputable section

variable {R : Type 0} [CommRing R] [IsDomain R] [Fintype R] [DecidableEq R] [Inhabited R]
  [SampleableType R] (pp : PublicParams)

/-! ### Direction facts (private clones; pSpec-identical to the original chain) -/

private theorem vsum_two_pos {ℓ : ℕ} (h : 0 < ℓ) : 0 < Fin.vsum (fun _ : Fin ℓ => 2) := by
  rcases ℓ with - | k
  · omega
  · rw [Fin.vsum_succ]; omega

private theorem sumcheckPSpec_dir_zero (deg n : ℕ)
    (h : 0 < Fin.vsum (fun _ : Fin n => 2)) :
    (Sumcheck.Spec.pSpec R deg n).dir ⟨0, h⟩ = .P_to_V := by
  rcases ProtocolSpec.seqCompose_appendValid
      (pSpec := fun _ : Fin n => Sumcheck.Spec.SingleRound.pSpec R deg)
      (fun _ => ⟨by norm_num, rfl⟩) with hzero | ⟨h', hdir⟩
  · omega
  · exact hdir

private theorem sfx6_dir_zero (hn : 0 < pp.ℓ_n)
    (h : 0 < Fin.vsum (fun _ : Fin pp.ℓ_n => 2) + 0) :
    (sfx6 (R := R) pp).dir ⟨0, h⟩ = .P_to_V := by
  have hv : 0 < Fin.vsum (fun _ : Fin pp.ℓ_n => 2) := vsum_two_pos hn
  rw [show (⟨0, h⟩ : Fin (Fin.vsum (fun _ : Fin pp.ℓ_n => 2) + 0))
      = Fin.castLE (by omega) (⟨0, hv⟩ : Fin (Fin.vsum (fun _ : Fin pp.ℓ_n => 2))) from by
    ext; simp]
  rw [Prover.append_dir_castLE]
  exact sumcheckPSpec_dir_zero 2 pp.ℓ_n hv

private theorem sfx5_dir_zero (hn : 0 < pp.ℓ_n)
    (h : 0 < 0 + (Fin.vsum (fun _ : Fin pp.ℓ_n => 2) + 0)) :
    (sfx5 (R := R) pp).dir ⟨0, h⟩ = .P_to_V := by
  have h6 : 0 < Fin.vsum (fun _ : Fin pp.ℓ_n => 2) + 0 := by omega
  rw [show (⟨0, h⟩ : Fin (0 + (Fin.vsum (fun _ : Fin pp.ℓ_n => 2) + 0)))
      = Fin.natAdd 0 (⟨0, h6⟩ : Fin (Fin.vsum (fun _ : Fin pp.ℓ_n => 2) + 0)) from by
    ext; simp]
  rw [Prover.append_dir_natAdd]
  exact sfx6_dir_zero pp hn h6

private theorem sfx4_dir_zero
    (h : 0 < 1 + (0 + (Fin.vsum (fun _ : Fin pp.ℓ_n => 2) + 0))) :
    (sfx4 (R := R) pp).dir ⟨0, h⟩ = .V_to_P := by
  rw [show (⟨0, h⟩ : Fin (1 + (0 + (Fin.vsum (fun _ : Fin pp.ℓ_n => 2) + 0))))
      = Fin.castLE (by omega) (⟨0, Nat.one_pos⟩ : Fin 1) from by ext; simp]
  rw [Prover.append_dir_castLE]
  rfl

private theorem sfx4_dir_seam (hn : 0 < pp.ℓ_n)
    (h : 1 < 1 + (0 + (Fin.vsum (fun _ : Fin pp.ℓ_n => 2) + 0))) :
    (sfx4 (R := R) pp).dir ⟨1, h⟩ = .P_to_V := by
  have h5 : 0 < 0 + (Fin.vsum (fun _ : Fin pp.ℓ_n => 2) + 0) := by omega
  rw [show (⟨1, h⟩ : Fin (1 + (0 + (Fin.vsum (fun _ : Fin pp.ℓ_n => 2) + 0))))
      = Fin.natAdd 1 (⟨0, h5⟩ : Fin (0 + (Fin.vsum (fun _ : Fin pp.ℓ_n => 2) + 0))) from by
    ext; simp]
  rw [Prover.append_dir_natAdd]
  exact sfx5_dir_zero pp hn h5

private theorem sfx3_dir_zero
    (h : 0 < 1 + (1 + (0 + (Fin.vsum (fun _ : Fin pp.ℓ_n => 2) + 0)))) :
    (sfx3 (R := R) pp).dir ⟨0, h⟩ = .P_to_V := by
  rw [show (⟨0, h⟩ : Fin (1 + (1 + (0 + (Fin.vsum (fun _ : Fin pp.ℓ_n => 2) + 0)))))
      = Fin.castLE (by omega) (⟨0, Nat.one_pos⟩ : Fin 1) from by ext; simp]
  rw [Prover.append_dir_castLE]
  rfl

private theorem sfx3_dir_seam
    (h : 1 < 1 + (1 + (0 + (Fin.vsum (fun _ : Fin pp.ℓ_n => 2) + 0)))) :
    (sfx3 (R := R) pp).dir ⟨1, h⟩ = .V_to_P := by
  have h4 : 0 < 1 + (0 + (Fin.vsum (fun _ : Fin pp.ℓ_n => 2) + 0)) := by omega
  rw [show (⟨1, h⟩ : Fin (1 + (1 + (0 + (Fin.vsum (fun _ : Fin pp.ℓ_n => 2) + 0)))))
      = Fin.natAdd 1 (⟨0, h4⟩ : Fin (1 + (0 + (Fin.vsum (fun _ : Fin pp.ℓ_n => 2) + 0)))) from by
    ext; simp]
  rw [Prover.append_dir_natAdd]
  exact sfx4_dir_zero pp h4

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

private theorem sfx1_dir_zero
    (h : 0 < 1 + (Fin.vsum (fun _ : Fin pp.ℓ_m => 2)
      + (1 + (1 + (0 + (Fin.vsum (fun _ : Fin pp.ℓ_n => 2) + 0)))))) :
    (sfx1 (R := R) pp).dir ⟨0, h⟩ = .V_to_P := by
  rw [show (⟨0, h⟩ : Fin (1 + (Fin.vsum (fun _ : Fin pp.ℓ_m => 2)
        + (1 + (1 + (0 + (Fin.vsum (fun _ : Fin pp.ℓ_n => 2) + 0)))))))
      = Fin.castLE (by omega) (⟨0, Nat.one_pos⟩ : Fin 1) from by ext; simp]
  rw [Prover.append_dir_castLE]
  rfl

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

/-! ### The seven-seam assembly at the carried reductions -/

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

/-- Seam 7 (`secondSumcheckWithTarget ▷ finalCheckTight`, empty trailing seam). -/
private theorem tcStep8
    (h₇ : (secondSumcheckReductionWithTarget pp oSpec).perfectCompleteness init impl relG relH)
    (h₈ : (finalCheckTight pp oSpec).perfectCompleteness init impl relH relI)
    (hInit : NeverFail init)
    (hImplSupp : ∀ {β} (q : OracleQuery oSpec β) s,
      Prod.fst <$> support ((QueryImpl.mapQuery impl q).run s)
        = support (liftM q : OracleComp oSpec β)) :
    ((secondSumcheckReductionWithTarget pp oSpec).append
      (finalCheckTight pp oSpec)).perfectCompleteness init impl relG relI := by
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
    (secondSumcheckReductionWithTarget pp oSpec) (finalCheckTight pp oSpec)
    h₇ h₈ hInit hImplSupp

/-- Seam 6 (`prependRLCTargetWithTarget ▷ …`, message seam). -/
private theorem tcStep7 (hn : 0 < pp.ℓ_n)
    (h₆ : (prependRLCTargetWithTarget pp oSpec).perfectCompleteness init impl relF relG)
    (hRest : ((secondSumcheckReductionWithTarget pp oSpec).append
      (finalCheckTight pp oSpec)).perfectCompleteness init impl relG relI)
    (hInit : NeverFail init)
    (hImplSupp : ∀ {β} (q : OracleQuery oSpec β) s,
      Prod.fst <$> support ((QueryImpl.mapQuery impl q).run s)
        = support (liftM q : OracleComp oSpec β)) :
    ((prependRLCTargetWithTarget pp oSpec).append
      ((secondSumcheckReductionWithTarget pp oSpec).append
        (finalCheckTight pp oSpec))).perfectCompleteness init impl relF relI := by
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
    (prependRLCTargetWithTarget pp oSpec)
    ((secondSumcheckReductionWithTarget pp oSpec).append (finalCheckTight pp oSpec))
    h₆ hRest (by omega) (sfx5_dir_zero pp hn (by omega)) (sfx6_dir_zero pp hn (by omega))
    hInit hImplSupp

/-- Seam 5 (`linearCombinationWithTarget ▷ …`, message seam). -/
private theorem tcStep6 (hn : 0 < pp.ℓ_n)
    (h₅ : (linearCombinationWithTarget pp oSpec).perfectCompleteness init impl relE relF)
    (hRest : ((prependRLCTargetWithTarget pp oSpec).append
      ((secondSumcheckReductionWithTarget pp oSpec).append
        (finalCheckTight pp oSpec))).perfectCompleteness init impl relF relI)
    (hInit : NeverFail init)
    (hImplSupp : ∀ {β} (q : OracleQuery oSpec β) s,
      Prod.fst <$> support ((QueryImpl.mapQuery impl q).run s)
        = support (liftM q : OracleComp oSpec β)) :
    ((linearCombinationWithTarget pp oSpec).append ((prependRLCTargetWithTarget pp oSpec).append
      ((secondSumcheckReductionWithTarget pp oSpec).append
        (finalCheckTight pp oSpec)))).perfectCompleteness init impl relE relI := by
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
    ((prependRLCTargetWithTarget pp oSpec).append
      ((secondSumcheckReductionWithTarget pp oSpec).append (finalCheckTight pp oSpec)))
    h₅ hRest (by omega) (sfx4_dir_seam pp hn (by omega)) (sfx5_dir_zero pp hn (by omega))
    hInit hImplSupp

/-- Seam 4 (`sendEvalClaimWithTarget ▷ …`, **challenge** seam). -/
private theorem tcStep5
    (h₄ : (sendEvalClaimWithTarget pp oSpec).perfectCompleteness init impl relD relE)
    (hRest : ((linearCombinationWithTarget pp oSpec).append
      ((prependRLCTargetWithTarget pp oSpec).append
        ((secondSumcheckReductionWithTarget pp oSpec).append
          (finalCheckTight pp oSpec)))).perfectCompleteness init impl relE relI)
    (hInit : NeverFail init)
    (himplSP : ∀ (t : oSpec.Domain) (s : σ) (x : oSpec.Range t × σ),
      x ∈ support ((impl t).run s) → x.2 = s)
    (himplNF : ∀ (t : oSpec.Domain) (s : σ), Pr[⊥ | (impl t).run s] = 0) :
    ((sendEvalClaimWithTarget pp oSpec).append
      ((linearCombinationWithTarget pp oSpec).append ((prependRLCTargetWithTarget pp oSpec).append
        ((secondSumcheckReductionWithTarget pp oSpec).append
          (finalCheckTight pp oSpec))))).perfectCompleteness init impl relD relI := by
  exact OracleReduction.append_perfectCompleteness_keystone_challenge_114
    (sendEvalClaimWithTarget pp oSpec)
    ((linearCombinationWithTarget pp oSpec).append ((prependRLCTargetWithTarget pp oSpec).append
      ((secondSumcheckReductionWithTarget pp oSpec).append (finalCheckTight pp oSpec))))
    h₄ hRest (by omega) (sfx3_dir_seam pp (by omega)) (sfx4_dir_zero pp (by omega))
    hInit himplSP himplNF

/-- Seam 3 (`firstSumcheckWithTarget ▷ …`, message seam). -/
private theorem tcStep4
    (h₃ : (firstSumcheckReductionWithTarget pp oSpec).perfectCompleteness init impl relC relD)
    (hRest : ((sendEvalClaimWithTarget pp oSpec).append
      ((linearCombinationWithTarget pp oSpec).append ((prependRLCTargetWithTarget pp oSpec).append
        ((secondSumcheckReductionWithTarget pp oSpec).append
          (finalCheckTight pp oSpec))))).perfectCompleteness init impl relD relI)
    (hInit : NeverFail init)
    (hImplSupp : ∀ {β} (q : OracleQuery oSpec β) s,
      Prod.fst <$> support ((QueryImpl.mapQuery impl q).run s)
        = support (liftM q : OracleComp oSpec β)) :
    ((firstSumcheckReductionWithTarget pp oSpec).append
      ((sendEvalClaimWithTarget pp oSpec).append
        ((linearCombinationWithTarget pp oSpec).append
          ((prependRLCTargetWithTarget pp oSpec).append
            ((secondSumcheckReductionWithTarget pp oSpec).append
              (finalCheckTight pp oSpec)))))).perfectCompleteness init impl relC relI := by
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
      ((linearCombinationWithTarget pp oSpec).append ((prependRLCTargetWithTarget pp oSpec).append
        ((secondSumcheckReductionWithTarget pp oSpec).append (finalCheckTight pp oSpec)))))
    h₃ hRest (by omega) (sfx2_dir_seam pp (by omega)) (sfx3_dir_zero pp (by omega))
    hInit hImplSupp

/-- Seam 2 (`firstChallenge ▷ …`, message seam). -/
private theorem tcStep3 (hm : 0 < pp.ℓ_m)
    (h₂ : (oracleReduction.firstChallenge R pp oSpec).perfectCompleteness init impl relB relC)
    (hRest : ((firstSumcheckReductionWithTarget pp oSpec).append
      ((sendEvalClaimWithTarget pp oSpec).append
        ((linearCombinationWithTarget pp oSpec).append
          ((prependRLCTargetWithTarget pp oSpec).append
            ((secondSumcheckReductionWithTarget pp oSpec).append
              (finalCheckTight pp oSpec)))))).perfectCompleteness init impl relC relI)
    (hInit : NeverFail init)
    (hImplSupp : ∀ {β} (q : OracleQuery oSpec β) s,
      Prod.fst <$> support ((QueryImpl.mapQuery impl q).run s)
        = support (liftM q : OracleComp oSpec β)) :
    ((oracleReduction.firstChallenge R pp oSpec).append
      ((firstSumcheckReductionWithTarget pp oSpec).append
        ((sendEvalClaimWithTarget pp oSpec).append
          ((linearCombinationWithTarget pp oSpec).append
            ((prependRLCTargetWithTarget pp oSpec).append
              ((secondSumcheckReductionWithTarget pp oSpec).append
                (finalCheckTight pp oSpec))))))).perfectCompleteness init impl relB relI := by
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
        ((linearCombinationWithTarget pp oSpec).append
          ((prependRLCTargetWithTarget pp oSpec).append
            ((secondSumcheckReductionWithTarget pp oSpec).append (finalCheckTight pp oSpec))))))
    h₂ hRest (by omega) (sfx1_dir_seam pp hm (by omega)) (sfx2_dir_zero pp hm (by omega))
    hInit hImplSupp

/-- **The 8-fold tight composed perfect-completeness fold (issue #329, B7 step 5).**  Perfect
completeness of `composedPIOPTightFull_Rc` — the same reduction as the KS apex
`composedTightFull_rbrKnowledgeSoundness` — from the eight per-phase leaf completenesses, along
any chain of intermediate relations at the carried statement types.  Seam 1 (`firstMessage ▷ …`)
is a challenge seam; the remaining six seams are handled in the `tcStep*` lemmas. -/
theorem composedPIOPTightFull_perfectCompleteness_of_leaves
    (hm : 0 < pp.ℓ_m) (hn : 0 < pp.ℓ_n)
    (h₁ : (oracleReduction.firstMessage R pp oSpec).perfectCompleteness init impl relA relB)
    (h₂ : (oracleReduction.firstChallenge R pp oSpec).perfectCompleteness init impl relB relC)
    (h₃ : (firstSumcheckReductionWithTarget pp oSpec).perfectCompleteness init impl relC relD)
    (h₄ : (sendEvalClaimWithTarget pp oSpec).perfectCompleteness init impl relD relE)
    (h₅ : (linearCombinationWithTarget pp oSpec).perfectCompleteness init impl relE relF)
    (h₆ : (prependRLCTargetWithTarget pp oSpec).perfectCompleteness init impl relF relG)
    (h₇ : (secondSumcheckReductionWithTarget pp oSpec).perfectCompleteness init impl relG relH)
    (h₈ : (finalCheckTight pp oSpec).perfectCompleteness init impl relH relI)
    (hInit : NeverFail init)
    (hImplSupp : ∀ {β} (q : OracleQuery oSpec β) s,
      Prod.fst <$> support ((QueryImpl.mapQuery impl q).run s)
        = support (liftM q : OracleComp oSpec β))
    (himplSP : ∀ (t : oSpec.Domain) (s : σ) (x : oSpec.Range t × σ),
      x ∈ support ((impl t).run s) → x.2 = s)
    (himplNF : ∀ (t : oSpec.Domain) (s : σ), Pr[⊥ | (impl t).run s] = 0) :
    (composedPIOPTightFull_Rc (R := R) pp oSpec).perfectCompleteness init impl relA relI := by
  have hS8 := tcStep8 pp oSpec h₇ h₈ hInit hImplSupp
  have hS7 := tcStep7 pp oSpec hn h₆ hS8 hInit hImplSupp
  have hS6 := tcStep6 pp oSpec hn h₅ hS7 hInit hImplSupp
  have hS5 := tcStep5 pp oSpec h₄ hS6 hInit himplSP himplNF
  have hS4 := tcStep4 pp oSpec h₃ hS5 hInit hImplSupp
  have hS3 := tcStep3 pp oSpec hm h₂ hS4 hInit hImplSupp
  exact OracleReduction.append_perfectCompleteness_keystone_challenge_114
    (oracleReduction.firstMessage R pp oSpec)
    ((oracleReduction.firstChallenge R pp oSpec).append
      ((firstSumcheckReductionWithTarget pp oSpec).append
        ((sendEvalClaimWithTarget pp oSpec).append
          ((linearCombinationWithTarget pp oSpec).append
            ((prependRLCTargetWithTarget pp oSpec).append
              ((secondSumcheckReductionWithTarget pp oSpec).append (finalCheckTight pp oSpec)))))))
    h₁ hS3 (by omega) (composedPSpec_dir_seam pp (by omega)) (sfx1_dir_zero pp (by omega))
    hInit himplSP himplNF

end

end Spartan.Spec.Bricks

-- Axiom audit: must report only `[propext, Classical.choice, Quot.sound]` (no `sorryAx`).
#print axioms Spartan.Spec.Bricks.composedPIOPTightFull_perfectCompleteness_of_leaves

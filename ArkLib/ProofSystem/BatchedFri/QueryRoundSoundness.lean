/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/

import ArkLib.ProofSystem.BatchedFri.QueryRoundProbability

/-!
# Batched FRI soundness adapters from query-round probability

`QueryRoundProbability.lean` discharges the Claim 8.2 query-round frontier from the
Mathlib-only probability theorem. This file routes that probability-space front door into the
Claim 8.3 full-domain query-lift and sequential-composition packaging from `Security.lean`.
-/

namespace Fri
section ProbabilitySoundnessAdapter

open scoped ENNReal NNReal BigOperators
open OracleComp OracleSpec ProtocolSpec ReedSolomon Domain
open NNReal Finset Function ProbabilityTheory

variable {𝔽 : Type} [NonBinaryField 𝔽] [Fintype 𝔽] [DecidableEq 𝔽] [Nontrivial 𝔽]
variable {n : ℕ} {k : ℕ}
variable {s : Fin (k + 1) → ℕ+} {d : ℕ+}
variable {ω : SmoothCosetFftDomain n 𝔽}
variable (domain_size_cond : (2 ^ (∑ i, (s i : ℕ))) * d ≤ 2 ^ n)

omit [Nontrivial 𝔽] in
/-- The proved probability-space query-round frontier supplies the Claim 8.3 full-domain
query-lift field, keeping the correlated-agreement bridge explicit. -/
theorem friSoundnessQueryLift_of_queryRoundProbabilityBoundAndBatchedFRIOracleLens
    {t m : ℕ}
    (f : Fin t.succ → (ω → 𝔽))
    (m_ge_3 : m ≥ 3)
    {ι : Type} [Fintype ι] [Nonempty ι]
    (G : Finset ι) (δ : ℝ≥0∞) (queries l : ℕ)
    (h_agreement :
      correlated_agreement_density
        (Fₛ (fun i x => f i ((subdomainZeroEquiv (n := n) (ω := ω)) x)))
        (ReedSolomon.code (⟨fun x => x, by simp⟩ : ω.subdomain 0 ↪ 𝔽) (2 ^ n))
      ≤
      (let ρ_sqrt :=
        ReedSolomon.sqrtRate
          (2 ^ n)
          (⟨fun x => x, by simp⟩ : ω ↪ 𝔽)
       ρ_sqrt * (1 + 1 / (2 * (m : ℝ≥0)))))
    {agreementBridge : Prop}
    (pieces_imply_claim :
      QueryRound.probabilityAcceptanceBound G δ queries →
      batchedFRIOracleLensReduction
        (n := n) (s := s) (d := d) (ω := ω)
        (domain_size_cond := domain_size_cond) l t →
      agreementBridge →
      fri_query_soundness (n := n) (ω := ω)
        (f := fun i x => f i ((subdomainZeroEquiv (n := n) (ω := ω)) x))
        (h_agreement := h_agreement) (m_ge_3 := m_ge_3))
    (h_agreementBridge : agreementBridge) :
    friSoundnessQueryLift (n := n) (ω := ω) f m_ge_3 := by
  unfold friSoundnessQueryLift
  exact
    fri_query_soundness_lift_subdomainZero_to_domain
      (n := n) (ω := ω) (f := f) h_agreement m_ge_3
      (fri_query_soundness_of_queryRoundProbabilityBoundAndBatchedFRIOracleLens
        (n := n) (s := s) (d := d) (ω := ω)
        (f := fun i x => f i ((subdomainZeroEquiv (n := n) (ω := ω)) x))
        h_agreement m_ge_3 G δ queries l domain_size_cond
        pieces_imply_claim h_agreementBridge)

omit [Nontrivial 𝔽] in
/-- Reassemble Claim 8.3 after discharging the query-lift field by the proved probability-space
query-round theorem and the concrete Batched FRI sequential-composition field. The remaining
frontiers are the correlated-agreement bridge and total-error accounting. -/
theorem fri_soundness_of_queryRoundProbabilityBoundAndBatchedFRIOracleLensAndSequentialComposition
    {t l m : ℕ}
    (f : Fin t.succ → (ω → 𝔽))
    (m_ge_3 : m ≥ 3)
    {ι : Type} [Fintype ι] [Nonempty ι]
    (G : Finset ι) (δ : ℝ≥0∞) (queries : ℕ)
    (h_agreement :
      correlated_agreement_density
        (Fₛ (fun i x => f i ((subdomainZeroEquiv (n := n) (ω := ω)) x)))
        (ReedSolomon.code (⟨fun x => x, by simp⟩ : ω.subdomain 0 ↪ 𝔽) (2 ^ n))
      ≤
      (let ρ_sqrt :=
        ReedSolomon.sqrtRate
          (2 ^ n)
          (⟨fun x => x, by simp⟩ : ω ↪ 𝔽)
       ρ_sqrt * (1 + 1 / (2 * (m : ℝ≥0)))))
    {σ : Type} (init : ProbComp σ) (impl : QueryImpl []ₒ (StateT σ ProbComp))
    [∀ i, SampleableType ((BatchedFri.Spec.BatchingRound.batchSpec 𝔽 t).Challenge i)]
    [∀ i, SampleableType ((Spec.pSpecFold (ω := ω) k s ++ₚ Spec.FinalFoldPhase.pSpec 𝔽 ++ₚ
      Spec.QueryRound.pSpec (ω := ω) l).Challenge i)]
    (lang₁ : Set (Unit × (∀ i, BatchedFri.Spec.OracleStatement t ω i)))
    (lang₂ : Set (((Fin t → 𝔽) × Spec.Statement 𝔽 (0 : Fin (k + 1))) ×
      (∀ i, BatchedFri.Spec.OracleStatement t ω i)))
    (lang₃ : Set (Spec.FinalStatement 𝔽 k × (∀ i, Spec.FinalOracleStatement s (ω := ω) i)))
    {batchError friError : ℝ≥0}
    (h_batch : OracleVerifier.soundness
      (init := init) (impl := impl)
      lang₁ lang₂
      (BatchedFri.Spec.BatchingRound.batchOracleReduction
        (F := 𝔽) (n := n) (ω := ω) s d t).verifier
      batchError)
    (h_fri : OracleVerifier.soundness
      (init := init) (impl := impl)
      lang₂ lang₃
      (BatchedFri.Spec.liftedFRI
        (F := 𝔽) (n := n) (ω := ω) k s d domain_size_cond l t).verifier
      friError)
    (h_residual : OracleVerifier.appendSoundnessResidual
      (init := init) (impl := impl)
      (BatchedFri.Spec.BatchingRound.batchOracleReduction
        (F := 𝔽) (n := n) (ω := ω) s d t).verifier
      (BatchedFri.Spec.liftedFRI
        (F := 𝔽) (n := n) (ω := ω) k s d domain_size_cond l t).verifier
      h_batch h_fri)
    {agreementBridge totalErrorAccounting : Prop}
    (query_pieces_imply_claim :
      QueryRound.probabilityAcceptanceBound G δ queries →
      batchedFRIOracleLensReduction
        (n := n) (s := s) (d := d) (ω := ω)
        (domain_size_cond := domain_size_cond) l t →
      agreementBridge →
      fri_query_soundness (n := n) (ω := ω)
        (f := fun i x => f i ((subdomainZeroEquiv (n := n) (ω := ω)) x))
        (h_agreement := h_agreement) (m_ge_3 := m_ge_3))
    (soundness_pieces_imply_claim :
      friSoundnessQueryLift (n := n) (ω := ω) f m_ge_3 →
      friSoundnessSequentialComposition
        (n := n) (s := s) (d := d) (ω := ω) (l := l)
        (domain_size_cond := domain_size_cond)
        init impl lang₁ lang₃ batchError friError →
      totalErrorAccounting →
      fri_soundness (n := n) (s := s) (d := d) (ω := ω) (l := l)
        (domain_size_cond := domain_size_cond) f m_ge_3)
    (h_agreementBridge : agreementBridge)
    (h_total : totalErrorAccounting) :
    fri_soundness (n := n) (s := s) (d := d) (ω := ω) (l := l)
      (domain_size_cond := domain_size_cond) f m_ge_3 := by
  let parts :=
    FriSoundnessParts.of_queryRoundDensityBoundAndBatchedFRIOracleLens
      (n := n) (s := s) (d := d) (ω := ω) (l := l)
      (domain_size_cond := domain_size_cond)
      f m_ge_3
      (friSoundnessSequentialComposition
        (n := n) (s := s) (d := d) (ω := ω) (l := l)
        (domain_size_cond := domain_size_cond)
        init impl lang₁ lang₃ batchError friError)
      totalErrorAccounting soundness_pieces_imply_claim
  exact fri_soundness_of_parts
    (n := n) (s := s) (d := d) (ω := ω) (l := l)
    (domain_size_cond := domain_size_cond) f m_ge_3 parts
    (friSoundnessQueryLift_of_queryRoundProbabilityBoundAndBatchedFRIOracleLens
      (n := n) (s := s) (d := d) (ω := ω)
      (domain_size_cond := domain_size_cond)
      f m_ge_3 G δ queries l h_agreement query_pieces_imply_claim h_agreementBridge)
    (friSoundnessSequentialComposition_of_append
      (n := n) (s := s) (d := d) (ω := ω) (l := l)
      (domain_size_cond := domain_size_cond)
      init impl lang₁ lang₂ lang₃ h_batch h_fri h_residual)
    h_total

set_option linter.style.longLine false in
#print axioms Fri.friSoundnessQueryLift_of_queryRoundProbabilityBoundAndBatchedFRIOracleLens
set_option linter.style.longLine false in
#print axioms Fri.fri_soundness_of_queryRoundProbabilityBoundAndBatchedFRIOracleLensAndSequentialComposition

end ProbabilitySoundnessAdapter
end Fri

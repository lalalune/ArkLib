/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/

import ArkLib.ProofSystem.BatchedFri.QueryRoundSoundness

/-!
# Batched FRI soundness adapters from RS-curve query routes

`QueryRoundProbability.lean` and `Security.lean` expose the query-level Batched FRI subdomain
Reed-Solomon polynomial-curve routes.  This companion module lifts those routes to the
full-domain Claim 8.3 surfaces without growing the near-cap query-round and security files.
-/

namespace Fri
section RSCurveSoundnessAdapter

open scoped ENNReal NNReal BigOperators
open OracleComp OracleSpec ProtocolSpec ReedSolomon Domain
open NNReal Finset Function ProbabilityTheory

variable {𝔽 : Type} [NonBinaryField 𝔽] [Fintype 𝔽] [DecidableEq 𝔽] [Nontrivial 𝔽]
variable {n : ℕ} {k : ℕ}
variable {s : Fin (k + 1) → ℕ+} {d : ℕ+}
variable {ω : SmoothCosetFftDomain n 𝔽}

/-- The fixed-radius RS polynomial-curve inputs for the probability-route Batched FRI wrappers.

This packages exactly the BCIKS20 polynomial-curve theorem inputs used by the query-level
`...AndRSCurve` route: strict coefficient-polynomial residual, boundary-probability residual,
square-root-radius side condition, and the polynomial-curve probability trigger. -/
def friRSCurveProbabilityInputs
    {t : ℕ} (f : Fin t.succ → (ω → 𝔽)) (m : ℕ) : Prop :=
  let rsDomain : ω.subdomain 0 ↪ 𝔽 := ⟨fun x => x, by simp⟩
  let u : Code.WordStack 𝔽 (Fin t.succ) (ω.subdomain 0) :=
    fun i x => f i ((subdomainZeroEquiv (n := n) (ω := ω)) x)
  let α_fri : ℝ≥0 :=
    let ρ_sqrt :=
      ReedSolomon.sqrtRate
        (2 ^ n)
        (⟨fun x => x, by simp⟩ : ω ↪ 𝔽)
    ρ_sqrt * (1 + 1 / (2 * (m : ℝ≥0)))
  let δ_fri : ℝ≥0 := 1 - α_fri
  ProximityGap.StrictCoeffPolysResidual
      (F := 𝔽) (ι := ω.subdomain 0) (k := t) (deg := 2 ^ n)
      (domain := rsDomain) (δ := δ_fri) ∧
    ProximityGap.BoundaryProbabilityResidual
      (F := 𝔽) (ι := ω.subdomain 0) (k := t) (deg := 2 ^ n)
      (domain := rsDomain) (δ := δ_fri) ∧
    δ_fri ≤ 1 - ReedSolomon.sqrtRate (2 ^ n) rsDomain ∧
    Pr_{let r ← $ᵖ 𝔽}[
      δᵣ(∑ i : Fin (t + 1), (r ^ (i : ℕ)) • u i,
        (ReedSolomon.code rsDomain (2 ^ n)).carrier) ≤ δ_fri] >
      t * ProximityGap.errorBound δ_fri (2 ^ n) rsDomain

/-- Probability-route Claim 8.3 query-lift specialized to the Batched FRI subdomain
Reed-Solomon polynomial-curve correlated-agreement theorem. -/
theorem friSoundnessQueryLift_of_queryRoundProbabilityBoundAndBatchedFRIOracleLensAndRSCurve
    {t m : ℕ}
    (f : Fin t.succ → (ω → 𝔽))
    (m_ge_3 : m ≥ 3)
    {ι : Type} [Fintype ι] [Nonempty ι]
    (G : Finset ι) (δ_query : ℝ≥0∞) (queries l : ℕ)
    (domain_size_cond : (2 ^ (∑ i, (s i : ℕ))) * d ≤ 2 ^ n)
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
    (h_rs : friRSCurveProbabilityInputs (n := n) (ω := ω) f m) :
    friSoundnessQueryLift (n := n) (ω := ω) f m_ge_3 := by
  let rsDomain : ω.subdomain 0 ↪ 𝔽 := ⟨fun x => x, by simp⟩
  let u : Code.WordStack 𝔽 (Fin t.succ) (ω.subdomain 0) :=
    fun i x => f i ((subdomainZeroEquiv (n := n) (ω := ω)) x)
  let α_fri : ℝ≥0 :=
    let ρ_sqrt :=
      ReedSolomon.sqrtRate
        (2 ^ n)
        (⟨fun x => x, by simp⟩ : ω ↪ 𝔽)
    ρ_sqrt * (1 + 1 / (2 * (m : ℝ≥0)))
  let δ_fri : ℝ≥0 := 1 - α_fri
  dsimp [friRSCurveProbabilityInputs] at h_rs
  rcases h_rs with ⟨hStrictCoeff, hBoundary, hδ, h_prob⟩
  have hStrictCoeff' :
      ProximityGap.StrictCoeffPolysResidual
        (F := 𝔽) (ι := ω.subdomain 0) (k := t) (deg := 2 ^ n)
        (domain := rsDomain) (δ := δ_fri) := by
    simpa [rsDomain, α_fri, δ_fri] using hStrictCoeff
  have hBoundary' :
      ProximityGap.BoundaryProbabilityResidual
        (F := 𝔽) (ι := ω.subdomain 0) (k := t) (deg := 2 ^ n)
        (domain := rsDomain) (δ := δ_fri) := by
    simpa [rsDomain, α_fri, δ_fri] using hBoundary
  have hδ' : δ_fri ≤ 1 - ReedSolomon.sqrtRate (2 ^ n) rsDomain := by
    simpa [rsDomain, α_fri, δ_fri] using hδ
  have h_prob' :
      Pr_{let r ← $ᵖ 𝔽}[
        δᵣ(∑ i : Fin (t + 1), (r ^ (i : ℕ)) • u i,
          (ReedSolomon.code rsDomain (2 ^ n)).carrier) ≤ δ_fri] >
        t * ProximityGap.errorBound δ_fri (2 ^ n) rsDomain := by
    simpa [rsDomain, u, α_fri, δ_fri] using h_prob
  unfold friSoundnessQueryLift
  exact
    fri_query_soundness_lift_subdomainZero_to_domain
      (n := n) (ω := ω) (f := f) h_agreement m_ge_3
      (fri_query_soundness_of_queryRoundProbabilityBoundAndBatchedFRIOracleLensAndRSCurve
        (n := n) (s := s) (d := d) (ω := ω)
        (f := fun i x => f i ((subdomainZeroEquiv (n := n) (ω := ω)) x))
        h_agreement m_ge_3 G δ_query queries l domain_size_cond
        (by simpa [rsDomain, α_fri, δ_fri] using hStrictCoeff')
        (by simpa [rsDomain, α_fri, δ_fri] using hBoundary')
        (by simpa [rsDomain, α_fri, δ_fri] using hδ')
        (by simpa [rsDomain, u, α_fri, δ_fri] using h_prob'))

/-- Probability-route Claim 8.3 residual specialized to the Batched FRI subdomain
Reed-Solomon polynomial-curve correlated-agreement theorem. -/
theorem fri_soundness_of_queryRoundProbabilityBoundAndBatchedFRIOracleLensAndRSCurve
    {t l m : ℕ}
    (f : Fin t.succ → (ω → 𝔽))
    (m_ge_3 : m ≥ 3)
    {ι : Type} [Fintype ι] [Nonempty ι]
    (G : Finset ι) (δ_query : ℝ≥0∞) (queries : ℕ)
    (domain_size_cond : (2 ^ (∑ i, (s i : ℕ))) * d ≤ 2 ^ n)
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
    (h_rs : friRSCurveProbabilityInputs (n := n) (ω := ω) f m) :
    fri_soundness (n := n) (s := s) (d := d) (ω := ω) (l := l)
      (domain_size_cond := domain_size_cond) f m_ge_3 := by
  exact
    fri_soundness_of_queryLift
      (n := n) (s := s) (d := d) (ω := ω) (domain_size_cond := domain_size_cond)
      f m_ge_3
      (friSoundnessQueryLift_of_queryRoundProbabilityBoundAndBatchedFRIOracleLensAndRSCurve
        (n := n) (s := s) (d := d) (ω := ω)
        f m_ge_3 G δ_query queries l domain_size_cond h_agreement h_rs)

/-- Raw full-domain Claim 8.2 conclusion from the Batched FRI subdomain Reed-Solomon
polynomial-curve probability-route wrapper. -/
theorem fri_jointAgreement_of_queryRoundProbabilityBoundAndBatchedFRIOracleLensAndRSCurve
    {t m : ℕ}
    (f : Fin t.succ → (ω → 𝔽))
    (m_ge_3 : m ≥ 3)
    {ι : Type} [Fintype ι] [Nonempty ι]
    (G : Finset ι) (δ_query : ℝ≥0∞) (queries l : ℕ)
    (domain_size_cond : (2 ^ (∑ i, (s i : ℕ))) * d ≤ 2 ^ n)
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
    (h_rs : friRSCurveProbabilityInputs (n := n) (ω := ω) f m) :
    Code.jointAgreement
      (F := 𝔽)
      (κ := Fin t.succ)
      (ι := ω)
      (C := (ReedSolomon.code (⟨fun x => x, by simp⟩ : ω ↪ 𝔽) (2 ^ n)).carrier)
      (δ :=
        let ρ_sqrt :=
          ReedSolomon.sqrtRate
            (2 ^ n)
            (⟨fun x => x, by simp⟩ : ω ↪ 𝔽)
        let α : ℝ≥0 := (ρ_sqrt * (1 + 1 / (2 * (m : ℝ≥0))))
        1 - α)
      (W := f) := by
  change friSoundnessQueryLift (n := n) (ω := ω) f m_ge_3
  exact
    friSoundnessQueryLift_of_queryRoundProbabilityBoundAndBatchedFRIOracleLensAndRSCurve
      (n := n) (s := s) (d := d) (ω := ω)
      f m_ge_3 G δ_query queries l domain_size_cond h_agreement h_rs

/-- The fixed-radius RS polynomial-curve inputs for the density-route Batched FRI wrappers.

This packages the BCIKS20 polynomial-curve theorem inputs used by the query-level `...AndRSCurve`
density route. -/
def friRSCurveDensityInputs {t : ℕ}
    (f : Fin t.succ → (ω → 𝔽)) (m : ℕ) : Prop :=
  let rsDomain : ω.subdomain 0 ↪ 𝔽 := ⟨fun x => x, by simp⟩
  let u : Code.WordStack 𝔽 (Fin t.succ) (ω.subdomain 0) :=
    fun i x => f i ((subdomainZeroEquiv (n := n) (ω := ω)) x)
  let α_fri : ℝ≥0 :=
    let ρ_sqrt :=
      ReedSolomon.sqrtRate
        (2 ^ n)
        (⟨fun x => x, by simp⟩ : ω ↪ 𝔽)
    ρ_sqrt * (1 + 1 / (2 * (m : ℝ≥0)))
  let δ_fri : ℝ≥0 := 1 - α_fri
  ProximityGap.StrictCoeffPolysResidual
      (F := 𝔽) (ι := ω.subdomain 0) (k := t) (deg := 2 ^ n)
      (domain := rsDomain) (δ := δ_fri) ∧
    ProximityGap.BoundaryProbabilityResidual
      (F := 𝔽) (ι := ω.subdomain 0) (k := t) (deg := 2 ^ n)
      (domain := rsDomain) (δ := δ_fri) ∧
    δ_fri ≤ 1 - ReedSolomon.sqrtRate (2 ^ n) rsDomain ∧
    Pr_{let r ← $ᵖ 𝔽}[
      δᵣ(∑ i : Fin (t + 1), (r ^ (i : ℕ)) • u i,
        (ReedSolomon.code rsDomain (2 ^ n)).carrier) ≤ δ_fri] >
      t * ProximityGap.errorBound δ_fri (2 ^ n) rsDomain

/-- Density-route Claim 8.3 query-lift specialized to the Batched FRI subdomain Reed-Solomon
polynomial-curve correlated-agreement theorem. -/
theorem friSoundnessQueryLift_of_queryRoundDensityBoundAndBatchedFRIOracleLensAndRSCurve
    {t m : ℕ}
    (f : Fin t.succ → (ω → 𝔽))
    (m_ge_3 : m ≥ 3)
    {ι : Type} [Fintype ι] [DecidableEq ι]
    (G : Finset ι) (δ_query : ℝ≥0) (queries l : ℕ)
    (domain_size_cond : (2 ^ (∑ i, (s i : ℕ))) * d ≤ 2 ^ n)
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
    (h_rs : friRSCurveDensityInputs (n := n) (ω := ω) f m) :
    friSoundnessQueryLift (n := n) (ω := ω) f m_ge_3 := by
  let rsDomain : ω.subdomain 0 ↪ 𝔽 := ⟨fun x => x, by simp⟩
  let u : Code.WordStack 𝔽 (Fin t.succ) (ω.subdomain 0) :=
    fun i x => f i ((subdomainZeroEquiv (n := n) (ω := ω)) x)
  let α_fri : ℝ≥0 :=
    let ρ_sqrt :=
      ReedSolomon.sqrtRate
        (2 ^ n)
        (⟨fun x => x, by simp⟩ : ω ↪ 𝔽)
    ρ_sqrt * (1 + 1 / (2 * (m : ℝ≥0)))
  let δ_fri : ℝ≥0 := 1 - α_fri
  dsimp [friRSCurveDensityInputs] at h_rs
  rcases h_rs with ⟨hStrictCoeff, hBoundary, hδ, h_prob⟩
  have hStrictCoeff' :
      ProximityGap.StrictCoeffPolysResidual
        (F := 𝔽) (ι := ω.subdomain 0) (k := t) (deg := 2 ^ n)
        (domain := rsDomain) (δ := δ_fri) := by
    simpa [rsDomain, α_fri, δ_fri] using hStrictCoeff
  have hBoundary' :
      ProximityGap.BoundaryProbabilityResidual
        (F := 𝔽) (ι := ω.subdomain 0) (k := t) (deg := 2 ^ n)
        (domain := rsDomain) (δ := δ_fri) := by
    simpa [rsDomain, α_fri, δ_fri] using hBoundary
  have hδ' : δ_fri ≤ 1 - ReedSolomon.sqrtRate (2 ^ n) rsDomain := by
    simpa [rsDomain, α_fri, δ_fri] using hδ
  have h_prob' :
      Pr_{let r ← $ᵖ 𝔽}[
        δᵣ(∑ i : Fin (t + 1), (r ^ (i : ℕ)) • u i,
          (ReedSolomon.code rsDomain (2 ^ n)).carrier) ≤ δ_fri] >
        t * ProximityGap.errorBound δ_fri (2 ^ n) rsDomain := by
    simpa [rsDomain, u, α_fri, δ_fri] using h_prob
  unfold friSoundnessQueryLift
  exact
    fri_query_soundness_lift_subdomainZero_to_domain
      (n := n) (ω := ω) (f := f) h_agreement m_ge_3
      (fri_query_soundness_of_queryRoundDensityBoundAndBatchedFRIOracleLensAndRSCurve
        (n := n) (s := s) (d := d) (ω := ω)
        (f := fun i x => f i ((subdomainZeroEquiv (n := n) (ω := ω)) x))
        h_agreement m_ge_3 G δ_query queries l domain_size_cond
        (by simpa [rsDomain, α_fri, δ_fri] using hStrictCoeff')
        (by simpa [rsDomain, α_fri, δ_fri] using hBoundary')
        (by simpa [rsDomain, α_fri, δ_fri] using hδ')
        (by simpa [rsDomain, u, α_fri, δ_fri] using h_prob'))

open ENNReal in
/-- Density-route Claim 8.3 residual specialized to the Batched FRI subdomain Reed-Solomon
polynomial-curve correlated-agreement theorem. -/
theorem fri_soundness_of_queryRoundDensityBoundAndBatchedFRIOracleLensAndRSCurve
    {t l m : ℕ}
    (f : Fin t.succ → (ω → 𝔽))
    (m_ge_3 : m ≥ 3)
    {ι : Type} [Fintype ι] [DecidableEq ι]
    (G : Finset ι) (δ_query : ℝ≥0) (queries : ℕ)
    (domain_size_cond : (2 ^ (∑ i, (s i : ℕ))) * d ≤ 2 ^ n)
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
    (h_rs : friRSCurveDensityInputs (n := n) (ω := ω) f m) :
    fri_soundness (n := n) (s := s) (d := d) (ω := ω) (l := l)
      (domain_size_cond := domain_size_cond) f m_ge_3 := by
  exact
    fri_soundness_of_queryLift
      (n := n) (s := s) (d := d) (ω := ω) (domain_size_cond := domain_size_cond)
      f m_ge_3
      (friSoundnessQueryLift_of_queryRoundDensityBoundAndBatchedFRIOracleLensAndRSCurve
        (n := n) (s := s) (d := d) (ω := ω)
        f m_ge_3 G δ_query queries l domain_size_cond h_agreement h_rs)

/-- Raw full-domain Claim 8.2 conclusion from the Batched FRI subdomain Reed-Solomon
polynomial-curve density-route wrapper. -/
theorem fri_jointAgreement_of_queryRoundDensityBoundAndBatchedFRIOracleLensAndRSCurve
    {t m : ℕ}
    (f : Fin t.succ → (ω → 𝔽))
    (m_ge_3 : m ≥ 3)
    {ι : Type} [Fintype ι] [DecidableEq ι]
    (G : Finset ι) (δ_query : ℝ≥0) (queries l : ℕ)
    (domain_size_cond : (2 ^ (∑ i, (s i : ℕ))) * d ≤ 2 ^ n)
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
    (h_rs : friRSCurveDensityInputs (n := n) (ω := ω) f m) :
    Code.jointAgreement
      (F := 𝔽)
      (κ := Fin t.succ)
      (ι := ω)
      (C := (ReedSolomon.code (⟨fun x => x, by simp⟩ : ω ↪ 𝔽) (2 ^ n)).carrier)
      (δ :=
        let ρ_sqrt :=
          ReedSolomon.sqrtRate
            (2 ^ n)
            (⟨fun x => x, by simp⟩ : ω ↪ 𝔽)
        let α : ℝ≥0 := (ρ_sqrt * (1 + 1 / (2 * (m : ℝ≥0))))
        1 - α)
      (W := f) := by
  change friSoundnessQueryLift (n := n) (ω := ω) f m_ge_3
  exact
    friSoundnessQueryLift_of_queryRoundDensityBoundAndBatchedFRIOracleLensAndRSCurve
      (n := n) (s := s) (d := d) (ω := ω)
      f m_ge_3 G δ_query queries l domain_size_cond h_agreement h_rs

set_option linter.style.longLine false in
#print axioms Fri.friRSCurveProbabilityInputs
set_option linter.style.longLine false in
#print axioms Fri.friSoundnessQueryLift_of_queryRoundProbabilityBoundAndBatchedFRIOracleLensAndRSCurve
set_option linter.style.longLine false in
#print axioms Fri.fri_soundness_of_queryRoundProbabilityBoundAndBatchedFRIOracleLensAndRSCurve
set_option linter.style.longLine false in
#print axioms Fri.fri_jointAgreement_of_queryRoundProbabilityBoundAndBatchedFRIOracleLensAndRSCurve
set_option linter.style.longLine false in
#print axioms Fri.friRSCurveDensityInputs
set_option linter.style.longLine false in
#print axioms Fri.friSoundnessQueryLift_of_queryRoundDensityBoundAndBatchedFRIOracleLensAndRSCurve
set_option linter.style.longLine false in
#print axioms Fri.fri_soundness_of_queryRoundDensityBoundAndBatchedFRIOracleLensAndRSCurve
set_option linter.style.longLine false in
#print axioms Fri.fri_jointAgreement_of_queryRoundDensityBoundAndBatchedFRIOracleLensAndRSCurve

end RSCurveSoundnessAdapter
end Fri

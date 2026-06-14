import ArkLib.Data.CodingTheory.ProximityGap.AdditiveEnergyBridge
import ArkLib.Data.CodingTheory.ProximityGap.SubgroupGaussSumFourthMoment
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
set_option linter.style.longLine false
set_option maxHeartbeats 1000000

/-!
# The sharp two-sided spectral characterization for the prize regime (#389)

Refining Conjecture C (`PrizeSpectralLevelSet`) with the EXACT additive energy `E₂(μ_n)=3n(n−1)`
(`addEnergy_eq_of_sidonModNeg`, the in-regime SidonModNeg property). For the smooth subgroup
`G = μ_n ⊆ F_q`, `η_b = Σ_{x∈G}ψ(b·x)`:

> **`prize_levelset_sharp`** (upper)  — `#{b : λ ≤ ‖η_b‖} · λ⁴ ≤ q · (3n²−3n)`.
> **`card_resonant_ge`** (lower, Paley–Zygmund) — `(q·n − λ²·q)² ≤ #{b : λ ≤ ‖η_b‖} · q·(3n²−3n)`.

Together these bracket the resonant-frequency count at the `√n` scale to `Θ(q)`: the upper bound
(`λ=√(c n)`) gives `≤ q·(3n²−3n)/(c²n²) = O(q/c²)`, the lower bound (`λ=√(θn)`, `θ<1`) gives
`≥ q·(1−θ)²·n/(3(n−1)) = Ω(q)`. So the second moment `√n` is genuinely TYPICAL of the spectrum —
a two-sided, in-regime, irrefutable characterization, PROVABLE conditional only on the in-regime
SidonModNeg property (the resultant-avoidance the prize-regime primes satisfy). Axiom-clean.
-/

open Finset
open ArkLib.ProximityGap.SubgroupGaussSumSecondMoment
open ArkLib.ProximityGap.SubgroupGaussSumFourthMoment
open ArkLib.ProximityGap.AdditiveEnergyBridge
open ArkLib.ProximityGap.AdditiveEnergySidonModNeg

namespace ArkLib.ProximityGap.PrizeSpectralLevelSetSharp

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

/-- The exact additive energy `E₂(G)=3n²−3n` cast to `ℝ`, for a SidonModNeg subgroup. -/
theorem addEnergy_cast {G : Finset F} (h2 : (2 : F) ≠ 0) (h0 : (0 : F) ∉ G)
    (hneg : ∀ x ∈ G, -x ∈ G) (hS : SidonModNeg G) :
    (addEnergy G : ℝ) = 3 * (G.card : ℝ) ^ 2 - 3 * (G.card : ℝ) := by
  have hE := addEnergy_eq_of_sidonModNeg h2 h0 hneg hS
  have hsq : G.card ≤ G.card ^ 2 := Nat.le_self_pow (by norm_num) G.card
  rw [hE, Nat.cast_sub (by omega)]
  push_cast
  ring

/-- **Sharp upper level-set (Conjecture C′).** Using the exact energy `E₂=3n²−3n`, the fourth-moment
Markov bound gives `#{b : λ ≤ ‖η_b‖} · λ⁴ ≤ q·(3n²−3n)` — sharper tail control than the second-moment
`λ²` bound, with the exact constant `3`. -/
theorem prize_levelset_sharp {ψ : AddChar F ℂ} (hψ : ψ.IsPrimitive) {G : Finset F}
    (h2 : (2 : F) ≠ 0) (h0 : (0 : F) ∉ G) (hneg : ∀ x ∈ G, -x ∈ G) (hS : SidonModNeg G)
    {lam : ℝ} (hlam : 0 ≤ lam) :
    ((univ.filter (fun b => lam ≤ ‖eta ψ G b‖)).card : ℝ) * lam ^ 4
      ≤ (Fintype.card F : ℝ) * (3 * (G.card : ℝ) ^ 2 - 3 * (G.card : ℝ)) := by
  set S := univ.filter (fun b => lam ≤ ‖eta ψ G b‖) with hSdef
  have h1 : (S.card : ℝ) * lam ^ 4 = ∑ _b ∈ S, lam ^ 4 := by rw [Finset.sum_const, nsmul_eq_mul]
  have h2' : ∑ _b ∈ S, lam ^ 4 ≤ ∑ b ∈ S, ‖eta ψ G b‖ ^ 4 :=
    Finset.sum_le_sum (fun b hb => pow_le_pow_left₀ hlam (Finset.mem_filter.mp hb).2 4)
  have h3 : ∑ b ∈ S, ‖eta ψ G b‖ ^ 4 ≤ ∑ b : F, ‖eta ψ G b‖ ^ 4 :=
    Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _) (fun b _ _ => by positivity)
  rw [h1]
  calc ∑ _b ∈ S, lam ^ 4
      ≤ ∑ b ∈ S, ‖eta ψ G b‖ ^ 4 := h2'
    _ ≤ ∑ b : F, ‖eta ψ G b‖ ^ 4 := h3
    _ = (Fintype.card F : ℝ) * addEnergy G := subgroup_gaussSum_fourthMoment hψ G
    _ = (Fintype.card F : ℝ) * (3 * (G.card : ℝ) ^ 2 - 3 * (G.card : ℝ)) := by
        rw [addEnergy_cast h2 h0 hneg hS]

/-- **Paley–Zygmund lower bound (matching, two-sided).** A positive density of frequencies are
resonant: `(q·n − λ²·q)² ≤ #{b : λ ≤ ‖η_b‖} · q·(3n²−3n)`. With `λ²=θn` (`θ<1`) this forces
`Ω(q)` resonant frequencies, matching the upper bound up to constants — the `√n` scale is typical. -/
theorem card_resonant_ge {ψ : AddChar F ℂ} (hψ : ψ.IsPrimitive) {G : Finset F}
    (h2 : (2 : F) ≠ 0) (h0 : (0 : F) ∉ G) (hneg : ∀ x ∈ G, -x ∈ G) (hS : SidonModNeg G)
    {lam : ℝ} (hle : lam ^ 2 ≤ (G.card : ℝ)) :
    ((Fintype.card F : ℝ) * (G.card : ℝ) - lam ^ 2 * (Fintype.card F : ℝ)) ^ 2
      ≤ ((univ.filter (fun b => lam ≤ ‖eta ψ G b‖)).card : ℝ)
          * ((Fintype.card F : ℝ) * (3 * (G.card : ℝ) ^ 2 - 3 * (G.card : ℝ))) := by
  classical
  set S := univ.filter (fun b => lam ≤ ‖eta ψ G b‖) with hSdef
  set A := ∑ b ∈ S, ‖eta ψ G b‖ ^ 2 with hAdef
  have hqnn : (0 : ℝ) ≤ (Fintype.card F : ℝ) := by positivity
  -- second moment splits over S and its complement
  have hsplit : A + ∑ b ∈ univ.filter (fun b => ¬ lam ≤ ‖eta ψ G b‖), ‖eta ψ G b‖ ^ 2
      = ∑ b : F, ‖eta ψ G b‖ ^ 2 :=
    Finset.sum_filter_add_sum_filter_not univ _ _
  have hsm : ∑ b : F, ‖eta ψ G b‖ ^ 2 = (Fintype.card F : ℝ) * (G.card : ℝ) :=
    subgroup_gaussSum_secondMoment hψ G
  -- complement contributes at most q·λ²
  have hcompl : ∑ b ∈ univ.filter (fun b => ¬ lam ≤ ‖eta ψ G b‖), ‖eta ψ G b‖ ^ 2
      ≤ (Fintype.card F : ℝ) * lam ^ 2 := by
    have hcard : ((univ.filter (fun b => ¬ lam ≤ ‖eta ψ G b‖)).card : ℝ) ≤ (Fintype.card F : ℝ) := by
      exact_mod_cast (Finset.card_filter_le univ _).trans_eq Finset.card_univ
    calc ∑ b ∈ univ.filter (fun b => ¬ lam ≤ ‖eta ψ G b‖), ‖eta ψ G b‖ ^ 2
        ≤ ∑ _b ∈ univ.filter (fun b => ¬ lam ≤ ‖eta ψ G b‖), lam ^ 2 := by
          apply Finset.sum_le_sum
          intro b hb
          have hlt : ‖eta ψ G b‖ < lam := not_le.mp (Finset.mem_filter.mp hb).2
          nlinarith [norm_nonneg (eta ψ G b)]
      _ = ((univ.filter (fun b => ¬ lam ≤ ‖eta ψ G b‖)).card : ℝ) * lam ^ 2 := by
          rw [Finset.sum_const, nsmul_eq_mul]
      _ ≤ (Fintype.card F : ℝ) * lam ^ 2 := by
          apply mul_le_mul_of_nonneg_right hcard (by positivity)
  -- hence A ≥ q·n − q·λ²
  have hA_ge : (Fintype.card F : ℝ) * (G.card : ℝ) - (Fintype.card F : ℝ) * lam ^ 2 ≤ A := by
    have h := hsplit; rw [hsm] at h; linarith [hcompl, h]
  -- Cauchy–Schwarz: A² ≤ |S|·∑_{b∈S}‖η_b‖⁴
  have hCS : A ^ 2 ≤ (S.card : ℝ) * ∑ b ∈ S, ‖eta ψ G b‖ ^ 4 := by
    have hcs := Finset.sum_mul_sq_le_sq_mul_sq S (fun _ => (1 : ℝ)) (fun b => ‖eta ψ G b‖ ^ 2)
    have e1 : (∑ b ∈ S, (1 : ℝ) * ‖eta ψ G b‖ ^ 2) = A := by simp [hAdef]
    have e2 : (∑ _b ∈ S, ((1 : ℝ)) ^ 2) = (S.card : ℝ) := by simp
    have e3 : (∑ b ∈ S, (‖eta ψ G b‖ ^ 2) ^ 2) = ∑ b ∈ S, ‖eta ψ G b‖ ^ 4 :=
      Finset.sum_congr rfl (fun b _ => by ring)
    rw [e1, e2, e3] at hcs
    exact hcs
  -- ∑_{b∈S}‖η_b‖⁴ ≤ q·(3n²−3n)
  have hext : ∑ b ∈ S, ‖eta ψ G b‖ ^ 4
      ≤ (Fintype.card F : ℝ) * (3 * (G.card : ℝ) ^ 2 - 3 * (G.card : ℝ)) := by
    have hsum : ∑ b : F, ‖eta ψ G b‖ ^ 4
        = (Fintype.card F : ℝ) * (3 * (G.card : ℝ) ^ 2 - 3 * (G.card : ℝ)) := by
      rw [subgroup_gaussSum_fourthMoment hψ G, addEnergy_cast h2 h0 hneg hS]
    calc ∑ b ∈ S, ‖eta ψ G b‖ ^ 4 ≤ ∑ b : F, ‖eta ψ G b‖ ^ 4 :=
          Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _) (fun b _ _ => by positivity)
      _ = (Fintype.card F : ℝ) * (3 * (G.card : ℝ) ^ 2 - 3 * (G.card : ℝ)) := hsum
  -- (q·n − q·λ²)² ≤ A²
  have hnn : (0 : ℝ) ≤ (Fintype.card F : ℝ) * (G.card : ℝ) - (Fintype.card F : ℝ) * lam ^ 2 := by
    have hnt : (0 : ℝ) ≤ (G.card : ℝ) - lam ^ 2 := by linarith
    nlinarith [mul_nonneg hqnn hnt]
  have hsq_le : ((Fintype.card F : ℝ) * (G.card : ℝ) - (Fintype.card F : ℝ) * lam ^ 2) ^ 2 ≤ A ^ 2 :=
    pow_le_pow_left₀ hnn hA_ge 2
  -- chain it all
  calc ((Fintype.card F : ℝ) * (G.card : ℝ) - lam ^ 2 * (Fintype.card F : ℝ)) ^ 2
      = ((Fintype.card F : ℝ) * (G.card : ℝ) - (Fintype.card F : ℝ) * lam ^ 2) ^ 2 := by ring
    _ ≤ A ^ 2 := hsq_le
    _ ≤ (S.card : ℝ) * ∑ b ∈ S, ‖eta ψ G b‖ ^ 4 := hCS
    _ ≤ (S.card : ℝ) * ((Fintype.card F : ℝ) * (3 * (G.card : ℝ) ^ 2 - 3 * (G.card : ℝ))) :=
        mul_le_mul_of_nonneg_left hext (by positivity)

end ArkLib.ProximityGap.PrizeSpectralLevelSetSharp

#print axioms ArkLib.ProximityGap.PrizeSpectralLevelSetSharp.prize_levelset_sharp
#print axioms ArkLib.ProximityGap.PrizeSpectralLevelSetSharp.card_resonant_ge

/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.SubgroupGaussSumMoment
import Mathlib.Tactic

set_option linter.style.longLine false

/-!
# Log-convexity of the subgroup Gauss-sum moment sequence (#389, #371)

The worst-case Shaw bound `max_{b≠0}‖η_b‖²` (`η_b = ∑_{y∈G} ψ(b·y)`) is approached from below by the
consecutive moment ratios `M_r/M_{r-1}` of `M_r := ∑_{b≠0}‖η_b‖^{2r}` (`exists_period_sq_ge_moment_ratio`
in `WorstPeriodMomentRatioLower`). This file proves those lower bounds form an **increasing** sequence:
the moment sequence `M_r` is **log-convex**,

> `gaussSum_moment_sq_le` :  `M_r² ≤ M_{r-1}·M_{r+1}`,   i.e.   `M_r/M_{r-1} ≤ M_{r+1}/M_r`,

so the reverse-Markov lower bounds on the worst period are monotone nondecreasing in `r` and converge
to the true `max_{b≠0}‖η_b‖²`. Pure Cauchy–Schwarz on the nonnegative sequence `a_b = ‖η_b‖²` — no
primitivity, no Weil, no open input. The energy form `energyR_moment_log_convex` transports it across
the proven identity `M_r = q·E_r − |G|^{2r}` to a statement purely about the additive energies:
`(q·E_r − |G|^{2r})² ≤ (q·E_{r-1} − |G|^{2(r-1)})·(q·E_{r+1} − |G|^{2(r+1)})`.

This is honest, irrefutable (a proven inequality), and sharpens the two-sided moment localization of
δ\*; it does not close the prize (the residual energy-ratio *growth law* at `r ≈ log(q/n)` is still W4).

Axiom-clean (`propext`, `Classical.choice`, `Quot.sound`); no `sorry`.
-/

open Finset
open ArkLib.ProximityGap.SubgroupGaussSumSecondMoment
open ArkLib.ProximityGap.SubgroupGaussSumMoment

namespace ArkLib.ProximityGap.SubgroupGaussSumMoment

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

/-- **Abstract log-convexity of a power-moment sum.** For `a ≥ 0` and `r ≥ 1`,
`(∑ a_i^r)² ≤ (∑ a_i^{r-1})·(∑ a_i^{r+1})` — Cauchy–Schwarz with `f = √(a^{r-1})`, `g = √(a^{r+1})`
(so `f·g = a^r`, `f² = a^{r-1}`, `g² = a^{r+1}`). -/
theorem sum_pow_sq_le {ι : Type*} (s : Finset ι) (a : ι → ℝ) (ha : ∀ i ∈ s, 0 ≤ a i)
    (r : ℕ) (hr : 1 ≤ r) :
    (∑ i ∈ s, a i ^ r) ^ 2 ≤ (∑ i ∈ s, a i ^ (r - 1)) * (∑ i ∈ s, a i ^ (r + 1)) := by
  classical
  set f : ι → ℝ := fun i => Real.sqrt (a i ^ (r - 1)) with hf
  set g : ι → ℝ := fun i => Real.sqrt (a i ^ (r + 1)) with hg
  have hfg : ∀ i ∈ s, f i * g i = a i ^ r := by
    intro i hi
    rw [hf, hg, ← Real.sqrt_mul (pow_nonneg (ha i hi) _), ← pow_add,
      show (r - 1) + (r + 1) = r * 2 by omega, pow_mul, Real.sqrt_sq (pow_nonneg (ha i hi) r)]
  have hf2 : ∀ i ∈ s, f i ^ 2 = a i ^ (r - 1) := by
    intro i hi; rw [hf]; exact Real.sq_sqrt (pow_nonneg (ha i hi) _)
  have hg2 : ∀ i ∈ s, g i ^ 2 = a i ^ (r + 1) := by
    intro i hi; rw [hg]; exact Real.sq_sqrt (pow_nonneg (ha i hi) _)
  have hcs := Finset.sum_mul_sq_le_sq_mul_sq s f g
  rw [Finset.sum_congr rfl hfg, Finset.sum_congr rfl hf2, Finset.sum_congr rfl hg2] at hcs
  exact hcs

/-- **Log-convexity of the subgroup-Gauss-sum moment sequence.** With `M_r := ∑_{b≠0} ‖η_b‖^{2r}`,
`M_r² ≤ M_{r-1}·M_{r+1}` for `r ≥ 1`. Pure Cauchy–Schwarz on `a_b = ‖η_b‖²`; no primitivity needed.
Equivalently the moment ratio `M_r/M_{r-1}` is monotone nondecreasing — so the reverse-Markov lower
bounds on `max_{b≠0}‖η_b‖²` increase toward the true worst period. -/
theorem gaussSum_moment_sq_le (ψ : AddChar F ℂ) (G : Finset F) (r : ℕ) (hr : 1 ≤ r) :
    (∑ b ∈ univ.erase (0 : F), ‖eta ψ G b‖ ^ (2 * r)) ^ 2
      ≤ (∑ b ∈ univ.erase (0 : F), ‖eta ψ G b‖ ^ (2 * (r - 1)))
        * (∑ b ∈ univ.erase (0 : F), ‖eta ψ G b‖ ^ (2 * (r + 1))) := by
  have hkey := sum_pow_sq_le (univ.erase (0 : F)) (fun b => ‖eta ψ G b‖ ^ 2)
    (fun b _ => by positivity) r hr
  have hpow : ∀ k : ℕ, ∀ b : F, (‖eta ψ G b‖ ^ 2) ^ k = ‖eta ψ G b‖ ^ (2 * k) := by
    intro k b; rw [← pow_mul, Nat.mul_comm]
  simp only [hpow] at hkey
  exact hkey

omit [Fintype F] [DecidableEq F] in
/-- `η_0 = |G|`, so `‖η_0‖^m = |G|^m`. -/
private theorem eta_zero_pow (ψ : AddChar F ℂ) (G : Finset F) (m : ℕ) :
    ‖eta ψ G (0 : F)‖ ^ m = (G.card : ℝ) ^ m := by
  have h0 : eta ψ G (0 : F) = (G.card : ℂ) := by simp [eta, AddChar.map_zero_eq_one]
  rw [h0, Complex.norm_natCast]

/-- **Log-convexity of the subgroup additive-energy moment sequence.** With the proven moment
identity `∑_b ‖η_b‖^{2r} = q·E_r`, peeling `η_0 = |G|` gives `M_r = q·E_r − |G|^{2r}`, and these
satisfy `M_r² ≤ M_{r-1}·M_{r+1}`:
`(q·E_r − |G|^{2r})² ≤ (q·E_{r-1} − |G|^{2(r-1)})·(q·E_{r+1} − |G|^{2(r+1)})`.
Equivalently the moment ratio `(q·E_r − |G|^{2r})/(q·E_{r-1} − |G|^{2(r-1)})` is monotone nondecreasing
in `r`: the reverse-Markov lower bounds on `max_{b≠0}‖η_b‖²` (`exists_period_sq_ge_moment_ratio`)
form an INCREASING sequence converging to the true worst period. No Weil, no open input. -/
theorem energyR_moment_log_convex {ψ : AddChar F ℂ} (hψ : ψ.IsPrimitive) (G : Finset F)
    (r : ℕ) (hr : 1 ≤ r) :
    ((Fintype.card F : ℝ) * rEnergy G r - (G.card : ℝ) ^ (2 * r)) ^ 2
      ≤ ((Fintype.card F : ℝ) * rEnergy G (r - 1) - (G.card : ℝ) ^ (2 * (r - 1)))
        * ((Fintype.card F : ℝ) * rEnergy G (r + 1) - (G.card : ℝ) ^ (2 * (r + 1))) := by
  have peel : ∀ k : ℕ, ∑ b ∈ univ.erase (0 : F), ‖eta ψ G b‖ ^ (2 * k)
      = (Fintype.card F : ℝ) * rEnergy G k - (G.card : ℝ) ^ (2 * k) := by
    intro k
    have hsplit := (Finset.add_sum_erase Finset.univ
      (fun b => ‖eta ψ G b‖ ^ (2 * k)) (Finset.mem_univ (0 : F))).symm
    rw [subgroup_gaussSum_moment hψ G k, eta_zero_pow ψ G (2 * k)] at hsplit
    linarith
  rw [← peel r, ← peel (r - 1), ← peel (r + 1)]
  exact gaussSum_moment_sq_le ψ G r hr

end ArkLib.ProximityGap.SubgroupGaussSumMoment

/-! ## Axiom audit -/
#print axioms ArkLib.ProximityGap.SubgroupGaussSumMoment.sum_pow_sq_le
#print axioms ArkLib.ProximityGap.SubgroupGaussSumMoment.gaussSum_moment_sq_le
#print axioms ArkLib.ProximityGap.SubgroupGaussSumMoment.energyR_moment_log_convex

/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.SubgroupGaussSumMoment

/-!
# The COSET-REDUCED moment bound for the subgroup Gauss-sum sup-norm (#389, #407)

`GaussPeriodMomentBound` bounds a single period by the *whole* `2r`-th moment via
`single_le_sum`: `‖η_b‖^{2r} ≤ ∑_{b'} ‖η_{b'}‖^{2r} = q·E_r`. That throws away the
**coset structure**: for a multiplicative subgroup `G = μ_n`, the period `η_b` is constant on
the `μ_n`-multiplication orbit `G·b` of `b` (`η_{ub} = η_b` for `u ∈ G`), and for `b ≠ 0` that
orbit has the full `n = |G|` elements. So the maximal value is attained at least `n` times, giving
the **`n`-fold sharper**

> `n · ‖η_b‖^{2r} ≤ ∑_{b'≠0} ‖η_{b'}‖^{2r} = q·E_r − n^{2r}`,  hence
> `‖η_b‖^{2r} ≤ (q·E_r − n^{2r}) / n`   for every `b ≠ 0`.

This is the **fixed-index floor's correct normalization** (#407 comment 4700823384, angle 5): the
extra factor `n` is exactly the `n^{1/2r}` that, after the `2r`-th root at the optimal depth
`r ≈ log m`, removes the spurious `√(log n / log m)` log-loss of the crude all-`b` bound and yields
`M ≤ ρ_r^{1/2r} · √(n log m)` with `ρ_r = (E_r/n − n^{2r-1}) / (r!·n^r)·…`. The sum is over the
`m = (q-1)/n` *cosets*, not `q` frequencies — that is what the `/n` records.

Hypotheses are exactly those of a finite multiplicative subgroup `G ⊆ F^×`:
`hbij : ∀ u ∈ G, G.image (u * ·) = G` (closure-as-bijection) and `h0 : 0 ∉ G`.

Axiom-clean. Issues #389, #407.
-/

open Finset AddChar
open ArkLib.ProximityGap.SubgroupGaussSumSecondMoment
open ArkLib.ProximityGap.SubgroupGaussSumMoment

namespace ArkLib.ProximityGap.GaussPeriodCosetReduction

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

omit [Fintype F] in
/-- **Period is constant on `μ_n`-multiplication orbits.** For `u ∈ G` (a subgroup, so `uG = G`),
`η_{ub} = η_b`: reindex the defining sum by the bijection `y ↦ uy` of `G`. -/
theorem eta_mul_left {ψ : AddChar F ℂ} {G : Finset F}
    (hbij : ∀ u ∈ G, G.image (fun y => u * y) = G) (h0 : (0 : F) ∉ G)
    {u : F} (hu : u ∈ G) (b : F) :
    eta ψ G (u * b) = eta ψ G b := by
  classical
  have hune : u ≠ 0 := fun h => h0 (h ▸ hu)
  calc eta ψ G (u * b)
      = ∑ y ∈ G, ψ (b * (u * y)) := by
        simp only [eta]; refine Finset.sum_congr rfl (fun y _ => ?_); congr 1; ring
    _ = ∑ z ∈ G.image (fun y => u * y), ψ (b * z) := by
        rw [Finset.sum_image]
        intro a _ c _ h; exact mul_left_cancel₀ hune h
    _ = ∑ z ∈ G, ψ (b * z) := by rw [hbij u hu]
    _ = eta ψ G b := rfl

omit [Fintype F] [DecidableEq F] in
/-- `η_0 = |G|` (every term is `ψ 0 = 1`). -/
theorem eta_zero {ψ : AddChar F ℂ} (G : Finset F) : eta ψ G 0 = (G.card : ℂ) := by
  simp only [eta, zero_mul, AddChar.map_zero_eq_one, Finset.sum_const, nsmul_eq_mul, mul_one]

/-- **The coset lower bound:** the maximal-value orbit `G·b₀` (size `|G|` when `b₀ ≠ 0`) forces
`|G| · ‖η_{b₀}‖^{2r} ≤ ∑_{b≠0} ‖η_b‖^{2r}`. -/
theorem card_mul_eta_pow_le_sum_erase {ψ : AddChar F ℂ} {G : Finset F}
    (hbij : ∀ u ∈ G, G.image (fun y => u * y) = G) (h0 : (0 : F) ∉ G)
    (r : ℕ) {b₀ : F} (hb₀ : b₀ ≠ 0) :
    (G.card : ℝ) * ‖eta ψ G b₀‖ ^ (2 * r)
      ≤ ∑ b ∈ Finset.univ.erase (0 : F), ‖eta ψ G b‖ ^ (2 * r) := by
  classical
  set O : Finset F := G.image (fun u => u * b₀) with hO
  have hinj : Function.Injective (fun u : F => u * b₀) := fun a c h => mul_right_cancel₀ hb₀ h
  have hcardO : O.card = G.card := by rw [hO, Finset.card_image_of_injective _ hinj]
  have hsub : O ⊆ Finset.univ.erase (0 : F) := by
    intro c hc
    obtain ⟨u, hu, rfl⟩ := Finset.mem_image.mp hc
    have hune : u ≠ 0 := fun h => h0 (h ▸ hu)
    exact Finset.mem_erase.mpr ⟨mul_ne_zero hune hb₀, Finset.mem_univ _⟩
  have hconst : ∀ c ∈ O, ‖eta ψ G c‖ ^ (2 * r) = ‖eta ψ G b₀‖ ^ (2 * r) := by
    intro c hc
    obtain ⟨u, hu, rfl⟩ := Finset.mem_image.mp hc
    rw [eta_mul_left hbij h0 hu]
  calc (G.card : ℝ) * ‖eta ψ G b₀‖ ^ (2 * r)
      = ∑ _c ∈ O, ‖eta ψ G b₀‖ ^ (2 * r) := by
        rw [Finset.sum_const, hcardO, nsmul_eq_mul]
    _ = ∑ c ∈ O, ‖eta ψ G c‖ ^ (2 * r) := Finset.sum_congr rfl (fun c hc => (hconst c hc).symm)
    _ ≤ ∑ b ∈ Finset.univ.erase (0 : F), ‖eta ψ G b‖ ^ (2 * r) :=
        Finset.sum_le_sum_of_subset_of_nonneg hsub (fun i _ _ => by positivity)

/-- **The coset-reduced moment bound.** For a finite multiplicative subgroup `G = μ_n` and every
`b₀ ≠ 0`,
`‖η_{b₀}‖^{2r} ≤ (q·E_r − n^{2r}) / n`,  `q = |F|`, `n = |G|`, `E_r` the `r`-fold additive energy.
This is the `n`-fold improvement of `GaussPeriodMomentBound.eta_pow_le_of_energyBound`
(`‖η_b‖^{2r} ≤ q·E_r`): the `/n` is the coset reduction (`m` cosets, not `q` frequencies). -/
theorem cosetReduced_eta_pow_le {ψ : AddChar F ℂ} (hψ : ψ.IsPrimitive) {G : Finset F}
    (hbij : ∀ u ∈ G, G.image (fun y => u * y) = G) (h0 : (0 : F) ∉ G) (hne : G.Nonempty)
    (r : ℕ) {b₀ : F} (hb₀ : b₀ ≠ 0) :
    ‖eta ψ G b₀‖ ^ (2 * r)
      ≤ ((Fintype.card F : ℝ) * rEnergy G r - (G.card : ℝ) ^ (2 * r)) / (G.card : ℝ) := by
  classical
  have hcardpos : 0 < (G.card : ℝ) := by exact_mod_cast Finset.card_pos.mpr hne
  have hmoment : ∑ b : F, ‖eta ψ G b‖ ^ (2 * r) = (Fintype.card F : ℝ) * rEnergy G r :=
    subgroup_gaussSum_moment hψ G r
  have heta0pow : ‖eta ψ G (0 : F)‖ ^ (2 * r) = (G.card : ℝ) ^ (2 * r) := by
    rw [eta_zero, Complex.norm_natCast]
  have hsum_erase : ∑ b ∈ Finset.univ.erase (0 : F), ‖eta ψ G b‖ ^ (2 * r)
      = (Fintype.card F : ℝ) * rEnergy G r - (G.card : ℝ) ^ (2 * r) := by
    rw [Finset.sum_erase_eq_sub (Finset.mem_univ 0), hmoment, heta0pow]
  have hbound := card_mul_eta_pow_le_sum_erase (ψ := ψ) hbij h0 r hb₀
  rw [hsum_erase] at hbound
  rw [le_div_iff₀ hcardpos, mul_comm]
  exact hbound

end ArkLib.ProximityGap.GaussPeriodCosetReduction

#print axioms ArkLib.ProximityGap.GaussPeriodCosetReduction.eta_mul_left
#print axioms ArkLib.ProximityGap.GaussPeriodCosetReduction.card_mul_eta_pow_le_sum_erase
#print axioms ArkLib.ProximityGap.GaussPeriodCosetReduction.cosetReduced_eta_pow_le

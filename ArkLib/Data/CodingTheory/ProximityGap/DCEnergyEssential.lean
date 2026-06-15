/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.DCSubtractedMoment
import ArkLib.Data.CodingTheory.ProximityGap.GaussPeriodMomentBound

/-!
# The DC term refutes the non-DC energy bound at the prize scale (#407, ★★ CORRECTION)

The in-tree `GaussPeriodMomentBound.GaussianEnergyBound G r : E_r(G) ≤ (2r−1)‼·|G|^r` (the raw,
non-DC-subtracted Wick bound) is the named open input of the in-tree non-DC moment→sup chain
(`eta_pow_le_of_energyBound`, `eta_le_optimized`). **It is FALSE in the prize regime.**

The reason is the **DC (principal-character) mass**: the `b=0` term of the full moment is
`‖η_0‖^{2r} = |G|^{2r}` (`DCSubtractedMoment.eta_zero`), so the full moment identity
`∑_b ‖η_b‖^{2r} = q·E_r` (`subgroup_gaussSum_moment`) forces

> **`energy_ge_dc`** — `E_r(G) ≥ |G|^{2r} / q`   (the raw energy is at least the DC term).

When the DC term itself exceeds Wick — `|G|^{2r}/q > (2r−1)‼·|G|^r`, equivalently
`|G|^r > q·(2r−1)‼` — the raw `GaussianEnergyBound` is **violated**:

> **`not_gaussianEnergyBound_of_card_pow_gt`** — `q·(2r−1)‼ < |G|^r ⟹ ¬ GaussianEnergyBound G r`.

The probe (`scripts/probes/probe_dc_essential.py`, `n=2^a`, `p=n⁴`, `r=⌊ln q⌋`) locates the
crossover at **`n = 64`**: `log(DC/Wick) = −6.2` (`n=8`), `+10.8` (`n=64`), `+135` (`n=2^12`),
`+1301` (`n=2^30`) — DC outgrows Wick unboundedly at the prize. So the non-DC chain's hypothesis
is not merely loose but **false for all `n ≥ 64` at the optimal order `r ≈ ln q`**, making
`eta_le_optimized` vacuous there.

**Net (constraint lemma):** the DC subtraction is *essential*. Only the DC-subtracted energy
`A_r = E_r − |G|^{2r}/q ≤ Wick` (the genuinely measured-true input, consumed by
`DCMomentSupBound.eta_pow_le_dc`) gives a non-vacuous prize reduction; any bound stated on the raw
`E_r ≤ Wick` is provably violated. This machine-checks the ★★ CORRECTION as an exact inequality.

Issue #407.
-/

open Finset AddChar
open ArkLib.ProximityGap.SubgroupGaussSumSecondMoment
open ArkLib.ProximityGap.SubgroupGaussSumMoment
open ArkLib.ProximityGap.DCSubtractedMoment
open ArkLib.ProximityGap.GaussPeriodMomentBound

namespace ArkLib.ProximityGap.DCEnergyEssential

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

/-- **DC lower bound on the raw energy.** The full moment `∑_b ‖η_b‖^{2r} = q·E_r` contains the DC
term `‖η_0‖^{2r} = |G|^{2r}`, and every other term is nonnegative, so `q·E_r ≥ |G|^{2r}`. -/
theorem q_mul_energy_ge_dc {ψ : AddChar F ℂ} (hψ : ψ.IsPrimitive) (G : Finset F) (r : ℕ) :
    (G.card : ℝ) ^ (2 * r) ≤ (Fintype.card F : ℝ) * (rEnergy G r : ℝ) := by
  have hnonneg : 0 ≤ ∑ b ∈ univ.erase (0 : F), ‖eta ψ G b‖ ^ (2 * r) :=
    Finset.sum_nonneg (fun b _ => by positivity)
  have hid := sum_nonzero_moment hψ G r
  linarith [hid, hnonneg]

/-- **DC lower bound on the energy itself.** Dividing by `q > 0`: `E_r(G) ≥ |G|^{2r}/q`. -/
theorem energy_ge_dc {ψ : AddChar F ℂ} (hψ : ψ.IsPrimitive) (G : Finset F) (r : ℕ)
    (hq : (0 : ℝ) < Fintype.card F) :
    (G.card : ℝ) ^ (2 * r) / (Fintype.card F : ℝ) ≤ (rEnergy G r : ℝ) := by
  rw [div_le_iff₀ hq]
  calc (G.card : ℝ) ^ (2 * r) ≤ (Fintype.card F : ℝ) * (rEnergy G r : ℝ) :=
        q_mul_energy_ge_dc hψ G r
    _ = (rEnergy G r : ℝ) * (Fintype.card F : ℝ) := mul_comm _ _

/-- **The DC term exceeds Wick ⟹ the raw energy bound is false.** If `|G|^{2r}/q > (2r−1)‼·|G|^r`
(the DC mass alone beats the Wick ceiling), then `GaussianEnergyBound G r` (the raw `E_r ≤ Wick`)
cannot hold, since `E_r ≥ |G|^{2r}/q`. -/
theorem not_gaussianEnergyBound_of_dc_gt_wick {ψ : AddChar F ℂ} (hψ : ψ.IsPrimitive)
    (G : Finset F) (r : ℕ) (hq : (0 : ℝ) < Fintype.card F)
    (hdc : (Nat.doubleFactorial (2 * r - 1) : ℝ) * (G.card : ℝ) ^ r
            < (G.card : ℝ) ^ (2 * r) / (Fintype.card F : ℝ)) :
    ¬ GaussianEnergyBound G r := by
  intro h
  have hge : (G.card : ℝ) ^ (2 * r) / (Fintype.card F : ℝ) ≤ (rEnergy G r : ℝ) :=
    energy_ge_dc hψ G r hq
  -- h : E_r ≤ Wick ; hge : DC ≤ E_r ; hdc : Wick < DC — contradiction.
  exact absurd (lt_of_lt_of_le hdc (le_trans hge h)) (lt_irrefl _)

/-- **Clean sufficient condition (prize-shaped).** `q·(2r−1)‼ < |G|^r` implies the DC term beats
Wick, hence refutes the raw energy bound. This is the algebraically clean trigger
`|G|^{2r}/q > (2r−1)‼·|G|^r ⟺ |G|^r > q·(2r−1)‼` (for `|G| > 0`), the form the probe measures via
`(n/2r)^r > q` (using `(2r−1)‼ ≤ (2r)^r`). -/
theorem not_gaussianEnergyBound_of_card_pow_gt {ψ : AddChar F ℂ} (hψ : ψ.IsPrimitive)
    (G : Finset F) (r : ℕ) (hq : (0 : ℝ) < Fintype.card F) (hG : (0 : ℝ) < G.card)
    (htrig : (Fintype.card F : ℝ) * (Nat.doubleFactorial (2 * r - 1) : ℝ) < (G.card : ℝ) ^ r) :
    ¬ GaussianEnergyBound G r := by
  apply not_gaussianEnergyBound_of_dc_gt_wick hψ G r hq
  -- want: Wick·|G|^r < |G|^{2r}/q  ⟸  q·Wick < |G|^r, then multiply by |G|^r>0 and divide by q>0.
  rw [lt_div_iff₀ hq]
  have hpow2 : (G.card : ℝ) ^ (2 * r) = (G.card : ℝ) ^ r * (G.card : ℝ) ^ r := by
    rw [two_mul, pow_add]
  have hGr : (0 : ℝ) < (G.card : ℝ) ^ r := pow_pos hG r
  calc (Nat.doubleFactorial (2 * r - 1) : ℝ) * (G.card : ℝ) ^ r * (Fintype.card F : ℝ)
      = ((Fintype.card F : ℝ) * (Nat.doubleFactorial (2 * r - 1) : ℝ)) * (G.card : ℝ) ^ r := by ring
    _ < (G.card : ℝ) ^ r * (G.card : ℝ) ^ r := by
        exact mul_lt_mul_of_pos_right htrig hGr
    _ = (G.card : ℝ) ^ (2 * r) := hpow2.symm

end ArkLib.ProximityGap.DCEnergyEssential

/-! ## Axiom audit -/
#print axioms ArkLib.ProximityGap.DCEnergyEssential.q_mul_energy_ge_dc
#print axioms ArkLib.ProximityGap.DCEnergyEssential.energy_ge_dc
#print axioms ArkLib.ProximityGap.DCEnergyEssential.not_gaussianEnergyBound_of_dc_gt_wick
#print axioms ArkLib.ProximityGap.DCEnergyEssential.not_gaussianEnergyBound_of_card_pow_gt

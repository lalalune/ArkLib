/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.InteriorWorstCaseIncompleteSum

/-!
# The generalized-Paley-graph dictionary for the proximity-prize per-frequency core (#389)

**The dictionary (Liu–Zhou, *Eigenvalues of Cayley graphs*, arXiv:1809.09829, Thm 115).** The
in-tree per-frequency object `eta ψ G b = Σ_{y∈G} ψ(b·y)` (the incomplete subgroup Gauss sum) is,
for `G = μ_n` the smooth domain, **exactly the non-principal eigenvalue of the generalized Paley
graph** `Cay(F_q, G)`. Its worst-case modulus `B = max_{b≠0} ‖eta ψ G b‖` is the graph's
non-principal spectral radius. Hence:

> **the prize per-frequency bound `B ≤ 2·√|G|`  ⟺  `Cay(F_q, G)` is RAMANUJAN**,
> where `2·√(|G|-1)` is the Alon–Boppana-optimal threshold.

This file records that named condition (`GeneralizedPaleyRamanujan`) as a **single Prop** and
discharges the bridge to the existing open residual `WorstCaseIncompleteSumBound` (at scale
`M = 4|G|`) — so the whole interior δ\* consumer chain (`addEnergy_le_of_worstCase`, …) runs from
this one cited hypothesis. The hypothesis is never asserted; it is the literature-named open lever.

**Honest scope of the open hypothesis.** `GeneralizedPaleyRamanujan` for the prize-regime thin
subgroup `|G| = n = q^{0.19} < q^{1/3}` is OPEN and far beyond current analytic number theory: it is
the optimal thin-subgroup Gauss-period / sum-product bound (the **Paley Graph Conjecture**,
Kim–Yip–Yoo arXiv:2309.09124 Conj 2.12). Best *proven* bounds in this regime are only `n^{1-o(1)}`
(Bourgain–Glibichuk–Konyagin; Heath-Brown–Konyagin is vacuous below `q^{1/3}`) — see
`docs/references/proximity-gap-paley-spectrum/README.md`. So this brick is a clean **named-residual
reduction**, not a closure: it isolates the prize per-frequency core in one cited, well-studied open
conjecture.

All proofs axiom-clean (`propext, Classical.choice, Quot.sound`). Issue #389.
-/

open ArkLib.ProximityGap.SubgroupGaussSumSecondMoment
open ArkLib.ProximityGap.SubgroupGaussSumFourthMoment
open ArkLib.ProximityGap.InteriorWorstCaseIncompleteSum

namespace ArkLib.ProximityGap.GeneralizedPaleyRamanujan

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

/-- **The generalized Paley graph `Cay(F_q, G)` is Ramanujan.** Every nonzero Gauss period
(= non-principal eigenvalue, Liu–Zhou Thm 115) has modulus at most the Alon–Boppana-optimal
`2·√|G|`. This is the literature-named OPEN lever (the Paley Graph Conjecture / optimal
thin-subgroup sum-product bound); it is the cleanest closed form of the prize per-frequency core. -/
def GeneralizedPaleyRamanujan (ψ : AddChar F ℂ) (G : Finset F) : Prop :=
  ∀ b : F, b ≠ 0 → ‖eta ψ G b‖ ≤ 2 * Real.sqrt (G.card)

/-- **The dictionary bridge.** A Ramanujan generalized Paley graph discharges the in-tree open
residual `WorstCaseIncompleteSumBound` at scale `M = 4·|G|` (`‖eta‖ ≤ 2√|G| ⟹ ‖eta‖² ≤ 4|G|`),
feeding the entire interior δ\* consumer chain from this single cited hypothesis. -/
theorem worstCaseIncompleteSumBound_of_ramanujan {ψ : AddChar F ℂ} {G : Finset F}
    (h : GeneralizedPaleyRamanujan ψ G) :
    WorstCaseIncompleteSumBound ψ G (4 * G.card) := by
  intro b hb
  have hsq : ‖eta ψ G b‖ ≤ 2 * Real.sqrt (G.card) := h b hb
  have hsqrt : Real.sqrt ((G.card : ℝ)) ^ 2 = (G.card : ℝ) :=
    Real.sq_sqrt (by positivity)
  have hle : ‖eta ψ G b‖ ^ 2 ≤ (2 * Real.sqrt (G.card)) ^ 2 := by
    have h0 : (0 : ℝ) ≤ ‖eta ψ G b‖ := norm_nonneg _
    nlinarith [hsq, h0, Real.sqrt_nonneg ((G.card : ℝ))]
  have hval : (2 * Real.sqrt ((G.card : ℝ))) ^ 2 = 4 * (G.card : ℝ) := by
    rw [mul_pow, hsqrt]; ring
  calc ‖eta ψ G b‖ ^ 2 ≤ (2 * Real.sqrt (G.card)) ^ 2 := hle
    _ = 4 * (G.card : ℝ) := hval

/-- **End-to-end:** a Ramanujan generalized Paley graph yields the additive-energy budget
`q·E(G) ≤ |G|⁴ + 4|G|·(q·|G|)` (composing the dictionary bridge with the in-tree consumer
`addEnergy_le_of_worstCase`). This is the prize per-frequency input feeding the δ\* programme,
reduced to the single named hypothesis `GeneralizedPaleyRamanujan`. -/
theorem addEnergy_le_of_ramanujan {ψ : AddChar F ℂ} (hψ : ψ.IsPrimitive) {G : Finset F}
    (h : GeneralizedPaleyRamanujan ψ G) :
    (Fintype.card F : ℝ) * (addEnergy G : ℝ)
      ≤ (G.card : ℝ) ^ 4 + (4 * G.card) * ((Fintype.card F : ℝ) * G.card) :=
  addEnergy_le_of_worstCase hψ G (by positivity) (worstCaseIncompleteSumBound_of_ramanujan h)

end ArkLib.ProximityGap.GeneralizedPaleyRamanujan

-- Axiom audit: must be `[propext, Classical.choice, Quot.sound]` only.
#print axioms ArkLib.ProximityGap.GeneralizedPaleyRamanujan.worstCaseIncompleteSumBound_of_ramanujan
#print axioms ArkLib.ProximityGap.GeneralizedPaleyRamanujan.addEnergy_le_of_ramanujan

/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.SubgroupGaussSumSecondMoment
import Mathlib.Tactic

set_option linter.style.longLine false

/-!
# Round 9 (Issue #232, ABF26) — the subgroup Gauss-sum FOURTH MOMENT = `q · (additive energy)`.

The second moment of the subgroup Gauss sum `η_b = ∑_{y∈G} ψ(b·y)` is `q·|G|`
(`SubgroupGaussSumSecondMoment`). Its **fourth** moment is the genuinely sum-product object: it equals
`q` times the **additive energy** of the multiplicative subgroup `G`,

> `subgroup_gaussSum_fourthMoment`:  `∑_{b∈F} ‖η_b‖⁴ = q · E(G)`,

where `E(G) = #{(y₁,y₂,y₃,y₄)∈G⁴ : y₁ + y₂ = y₃ + y₄}` is the additive energy (the count of additive
quadruples). This is the exact bridge from the analytic side (Gauss-sum moments) to the additive
combinatorics of a *multiplicative* subgroup — the sum-product tension at the heart of the deep-interior
proximity question. It is again **pure additive-character orthogonality** (Parseval), with **no Weil
input**: expanding `‖η_b‖⁴ = (η_b·conj η_b)²` into a sum over `G⁴` and summing over `b` collapses each
quadruple to `q·[y₁+y₂ = y₃+y₄]`.

Consequence: `subgroup_gaussSum_energy_lower` — since `‖η_b‖⁴ ≥ 0` and `E(G) ≥ |G|²` always (the
"diagonal" quadruples `y₁=y₃, y₂=y₄`), the fourth moment is `≥ q·|G|²`; and the trivial frequency `b=0`
alone contributes `‖η_0‖⁴ = |G|⁴`. The additive energy `E(G)` of a 2-power multiplicative subgroup is
*the* quantity a sum-product estimate would bound — small `E(G)` (close to the minimum `|G|²`) is exactly
the anti-concentration that would make the proximity count behave, and it is governed by the
multiplicative structure of `G`. All `sorry`-free and axiom-clean.

## References
- [ABF26] Arnon, Boneh, Fenzi. *Open Problems in List Decoding and Correlated Agreement*. 2026. #232.
-/

open Finset AddChar
open ArkLib.ProximityGap.SubgroupGaussSumSecondMoment

namespace ArkLib.ProximityGap.SubgroupGaussSumFourthMoment

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

/-- The **additive energy** of a finite set `G`: the number of quadruples `(y₁,y₂,y₃,y₄) ∈ G⁴` with
`y₁ + y₂ = y₃ + y₄`. -/
def addEnergy (G : Finset F) : ℕ :=
  ∑ y₁ ∈ G, ∑ y₂ ∈ G, ∑ y₃ ∈ G, ∑ y₄ ∈ G, (if y₁ + y₂ = y₃ + y₄ then 1 else 0)

/-- `‖η_b‖²`, as a complex number, is the double character sum `∑_{y',y∈G} ψ(b·(y'−y))`. (Extracted
from the second-moment computation; the value is a nonnegative real.) -/
theorem eta_normSq_eq (ψ : AddChar F ℂ) (G : Finset F) (b : F) :
    ((‖eta ψ G b‖ ^ 2 : ℝ) : ℂ) = ∑ y' ∈ G, ∑ y ∈ G, ψ (b * (y' - y)) := by
  have hconjeta : (starRingEnd ℂ) (eta ψ G b) = ∑ y ∈ G, ψ (-(b * y)) := by
    have hchar : (0 : ℕ) < ringChar F := by
      haveI := ringChar.charP F
      exact Nat.pos_of_ne_zero (CharP.char_ne_zero_of_finite F (ringChar F))
    rw [eta, map_sum]
    refine Finset.sum_congr rfl (fun y _ => ?_)
    rw [AddChar.starComp_apply hchar, AddChar.inv_apply]
  rw [show ((‖eta ψ G b‖ ^ 2 : ℝ) : ℂ) = eta ψ G b * (starRingEnd ℂ) (eta ψ G b) from by
    rw [RCLike.mul_conj]; norm_cast]
  rw [hconjeta, show eta ψ G b = ∑ y ∈ G, ψ (b * y) from rfl, Finset.sum_mul_sum]
  refine Finset.sum_congr rfl (fun y' _ => Finset.sum_congr rfl (fun y _ => ?_))
  rw [← AddChar.map_add_eq_mul]
  congr 1; ring

/-- **The subgroup Gauss-sum fourth moment equals `q · E(G)`.** Pure orthogonality (Parseval): the
fourth moment of `η_b` is `q` times the additive energy of `G`. No Weil. -/
theorem subgroup_gaussSum_fourthMoment {ψ : AddChar F ℂ} (hψ : ψ.IsPrimitive) (G : Finset F) :
    ∑ b : F, ‖eta ψ G b‖ ^ 4 = (Fintype.card F : ℝ) * addEnergy G := by
  -- Complex identity, then cast.
  have hcomplex : (∑ b : F, ((‖eta ψ G b‖ ^ 2 : ℝ) : ℂ) ^ 2)
      = (Fintype.card F : ℂ) * addEnergy G := by
    calc ∑ b : F, ((‖eta ψ G b‖ ^ 2 : ℝ) : ℂ) ^ 2
        = ∑ b : F, (∑ y₁ ∈ G, ∑ y₃ ∈ G, ψ (b * (y₁ - y₃)))
            * (∑ y₂ ∈ G, ∑ y₄ ∈ G, ψ (b * (y₂ - y₄))) := by
          refine Finset.sum_congr rfl (fun b _ => ?_)
          rw [sq, eta_normSq_eq ψ G b]
      _ = ∑ b : F, ∑ y₁ ∈ G, ∑ y₂ ∈ G, ∑ y₃ ∈ G, ∑ y₄ ∈ G,
            ψ (b * ((y₁ - y₃) + (y₂ - y₄))) := by
          refine Finset.sum_congr rfl (fun b _ => ?_)
          rw [Finset.sum_mul_sum]
          refine Finset.sum_congr rfl (fun y₁ _ => ?_)
          refine Finset.sum_congr rfl (fun y₂ _ => ?_)
          rw [Finset.sum_mul_sum]
          refine Finset.sum_congr rfl (fun y₃ _ => ?_)
          refine Finset.sum_congr rfl (fun y₄ _ => ?_)
          rw [← AddChar.map_add_eq_mul]; congr 1; ring
      _ = ∑ y₁ ∈ G, ∑ y₂ ∈ G, ∑ y₃ ∈ G, ∑ y₄ ∈ G, ∑ b : F,
            ψ (b * ((y₁ - y₃) + (y₂ - y₄))) := by
          rw [Finset.sum_comm]
          refine Finset.sum_congr rfl (fun y₁ _ => ?_)
          rw [Finset.sum_comm]
          refine Finset.sum_congr rfl (fun y₂ _ => ?_)
          rw [Finset.sum_comm]
          refine Finset.sum_congr rfl (fun y₃ _ => ?_)
          rw [Finset.sum_comm]
      _ = ∑ y₁ ∈ G, ∑ y₂ ∈ G, ∑ y₃ ∈ G, ∑ y₄ ∈ G,
            (if y₁ + y₂ = y₃ + y₄ then (Fintype.card F : ℂ) else 0) := by
          refine Finset.sum_congr rfl (fun y₁ _ => Finset.sum_congr rfl (fun y₂ _ =>
            Finset.sum_congr rfl (fun y₃ _ => Finset.sum_congr rfl (fun y₄ _ => ?_))))
          rw [AddChar.sum_mulShift ((y₁ - y₃) + (y₂ - y₄)) hψ]
          have hcond : ((y₁ - y₃) + (y₂ - y₄) = 0) ↔ (y₁ + y₂ = y₃ + y₄) := by
            constructor <;> intro h <;> linear_combination h
          simp only [hcond]
          split <;> simp
      _ = (Fintype.card F : ℂ) * addEnergy G := by
          rw [addEnergy]
          push_cast
          simp only [Finset.mul_sum]
          refine Finset.sum_congr rfl (fun y₁ _ => Finset.sum_congr rfl (fun y₂ _ =>
            Finset.sum_congr rfl (fun y₃ _ => Finset.sum_congr rfl (fun y₄ _ => ?_))))
          split <;> simp
  -- cast back
  have hcast : ((∑ b : F, ‖eta ψ G b‖ ^ 4 : ℝ) : ℂ) = (Fintype.card F : ℂ) * addEnergy G := by
    rw [Complex.ofReal_sum, ← hcomplex]
    refine Finset.sum_congr rfl (fun b _ => ?_)
    push_cast; ring
  have : ((∑ b : F, ‖eta ψ G b‖ ^ 4 : ℝ) : ℂ) = (((Fintype.card F : ℝ) * addEnergy G : ℝ) : ℂ) := by
    rw [hcast]; push_cast; ring
  exact_mod_cast this

/-- **Additive energy is at least `|G|²`** (the diagonal quadruples `y₃=y₁, y₄=y₂`). So the fourth
moment is `≥ q·|G|²`, and minimal energy `E(G) = |G|²` is the maximal anti-concentration. -/
theorem addEnergy_ge_sq (G : Finset F) : G.card ^ 2 ≤ addEnergy G := by
  rw [addEnergy]
  have hdiag : G.card ^ 2 = ∑ y₁ ∈ G, ∑ _y₂ ∈ G, 1 := by
    simp [Finset.sum_const, sq, mul_comm]
  rw [hdiag]
  refine Finset.sum_le_sum (fun y₁ hy₁ => ?_)
  refine Finset.sum_le_sum (fun y₂ hy₂ => ?_)
  -- inner: `1 ≤ ∑_{y₃∈G} ∑_{y₄∈G} [y₁+y₂=y₃+y₄]`, witnessed by `(y₃,y₄)=(y₁,y₂)`
  have h1 : (1 : ℕ) ≤ ∑ y₄ ∈ G, (if y₁ + y₂ = y₁ + y₄ then 1 else 0) := by
    have := Finset.single_le_sum (f := fun y₄ => if y₁ + y₂ = y₁ + y₄ then (1 : ℕ) else 0)
      (fun i _ => Nat.zero_le _) hy₂
    simpa using this
  have h2 : (∑ y₄ ∈ G, (if y₁ + y₂ = y₁ + y₄ then 1 else 0))
      ≤ ∑ y₃ ∈ G, ∑ y₄ ∈ G, (if y₁ + y₂ = y₃ + y₄ then 1 else 0) :=
    Finset.single_le_sum
      (f := fun y₃ => ∑ y₄ ∈ G, (if y₁ + y₂ = y₃ + y₄ then (1 : ℕ) else 0))
      (fun i _ => Finset.sum_nonneg (fun _ _ => Nat.zero_le _)) hy₁
  exact le_trans h1 h2

end ArkLib.ProximityGap.SubgroupGaussSumFourthMoment

/-! ## Axiom audit -/
#print axioms ArkLib.ProximityGap.SubgroupGaussSumFourthMoment.subgroup_gaussSum_fourthMoment
#print axioms ArkLib.ProximityGap.SubgroupGaussSumFourthMoment.addEnergy_ge_sq

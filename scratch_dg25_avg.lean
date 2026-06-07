import Mathlib.Data.ENNReal.Inv
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Module.Pi
import Mathlib.Data.Fintype.Pi
import Mathlib.Algebra.Group.Equiv.Basic

/-!
# Scratch: DG25 L4.19 covering-radius sampling — the generic averaging brick (algebra-only)

The mathematical heart of the covering-radius sampling lower bound (issue #77 / ABF26 L4.19 /
DG25 Thm 2.5), stated in raw `Finset.sum` / `(card)⁻¹` ENNReal form so it needs only core algebra
(no Probability/MeasureTheory/Analysis imports — robust to the shared-`.lake` olean churn).

`∑_{u₀} |ι→F|⁻¹ · (∑_{γ} |F|⁻¹ · [P (u₀ + γ•w)])  =  ∑_{u} |ι→F|⁻¹ · [P u]`

Intuition: averaging the line-event `P(u₀+γ•w)` over a uniform base word `u₀` (and slope `γ`)
re-uniformizes the sampled point. Integration (in `CapacityBounds.lean`) bridges the `Pr_{...}`
notation to these sums via `Pr_eq_tsum_indicator` + `tsum_fintype` + `uniformOfFintype_apply`,
then derives `epsCA ≥ ⨆_{u₀} body ≥ ∑ unif·body = Pr_u[…] ≥ ((q-1)/q)·Pr_u[…]`, choosing `w` beyond
the covering radius so `¬ jointProximity` holds for every `u₀`.
-/

open scoped NNReal ENNReal BigOperators

variable {F : Type} [Field F] [Fintype F] [DecidableEq F] [Nonempty F]
variable {ι : Type} [Fintype ι] [DecidableEq ι]

/-- **Translation-averaging identity (the DG25 L4.19 heart), ENNReal Finset form.** -/
lemma avg_line_indicator (P : (ι → F) → Prop) [DecidablePred P] (w : ι → F) :
    (∑ u₀ : ι → F, (Fintype.card (ι → F) : ℝ≥0∞)⁻¹ *
        ∑ γ : F, (Fintype.card F : ℝ≥0∞)⁻¹ * (if P (u₀ + γ • w) then (1 : ℝ≥0∞) else 0))
      = ∑ u : ι → F, (Fintype.card (ι → F) : ℝ≥0∞)⁻¹ * (if P u then (1 : ℝ≥0∞) else 0) := by
  classical
  -- distribute the outer constant into the γ-sum, then swap the two finite sums
  simp_rw [Finset.mul_sum]
  rw [Finset.sum_comm]
  -- translation invariance per slope γ: reindex u₀ ↦ u₀ + γ•w (a bijection)
  have tr : ∀ γ : F,
      (∑ u₀ : ι → F, (Fintype.card (ι → F) : ℝ≥0∞)⁻¹ *
          ((Fintype.card F : ℝ≥0∞)⁻¹ * (if P (u₀ + γ • w) then (1 : ℝ≥0∞) else 0)))
        = ∑ u₀ : ι → F, (Fintype.card (ι → F) : ℝ≥0∞)⁻¹ *
          ((Fintype.card F : ℝ≥0∞)⁻¹ * (if P u₀ then (1 : ℝ≥0∞) else 0)) := by
    intro γ
    exact Fintype.sum_equiv (Equiv.addRight (γ • w))
      (fun u₀ => (Fintype.card (ι → F) : ℝ≥0∞)⁻¹ *
        ((Fintype.card F : ℝ≥0∞)⁻¹ * (if P (u₀ + γ • w) then (1 : ℝ≥0∞) else 0)))
      (fun u => (Fintype.card (ι → F) : ℝ≥0∞)⁻¹ *
        ((Fintype.card F : ℝ≥0∞)⁻¹ * (if P u then (1 : ℝ≥0∞) else 0)))
      (fun u₀ => rfl)
  simp_rw [tr]
  -- the inner sum no longer depends on γ; collapse the γ-sum (|F| copies)
  rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, Finset.mul_sum]
  have hcard : (Fintype.card F : ℝ≥0∞) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  have htop : (Fintype.card F : ℝ≥0∞) ≠ ⊤ := ENNReal.natCast_ne_top _
  refine Finset.sum_congr rfl (fun u₀ _ => ?_)
  calc (Fintype.card F : ℝ≥0∞) * ((Fintype.card (ι → F) : ℝ≥0∞)⁻¹ *
          ((Fintype.card F : ℝ≥0∞)⁻¹ * (if P u₀ then (1 : ℝ≥0∞) else 0)))
      = (Fintype.card (ι → F) : ℝ≥0∞)⁻¹ *
          (((Fintype.card F : ℝ≥0∞) * (Fintype.card F : ℝ≥0∞)⁻¹) *
            (if P u₀ then (1 : ℝ≥0∞) else 0)) := by ring
    _ = (Fintype.card (ι → F) : ℝ≥0∞)⁻¹ * (if P u₀ then (1 : ℝ≥0∞) else 0) := by
          rw [ENNReal.mul_inv_cancel hcard htop, one_mul]

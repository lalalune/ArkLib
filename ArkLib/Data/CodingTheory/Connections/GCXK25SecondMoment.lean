import Mathlib.Algebra.Order.Chebyshev
import Mathlib.Data.Finset.Card
import Mathlib.Tactic

set_option linter.unusedSectionVars false
set_option linter.unusedDecidableInType false

/-! # GCXK25 second-moment counting core -/

namespace GCXK25SecondMoment

open Finset

variable {ι : Type*} [Fintype ι] [DecidableEq ι]
variable {κ : Type*} [DecidableEq κ]

/-- Per-coordinate multiplicity: how many of the sets `A α` (for `α ∈ T`) contain `x`. -/
noncomputable def mult (T : Finset κ) (A : κ → Finset ι) (x : ι) : ℕ :=
  (T.filter (fun α => x ∈ A α)).card

omit [Fintype ι] [DecidableEq κ] in
theorem mult_eq_sum (T : Finset κ) (A : κ → Finset ι) (x : ι) :
    mult T A x = ∑ α ∈ T, (if x ∈ A α then 1 else 0) := by
  classical
  unfold mult
  rw [← Finset.sum_filter]
  simp

theorem card_eq_sum_indicator (s : Finset ι) :
    s.card = ∑ x : ι, (if x ∈ s then 1 else 0) := by
  classical
  rw [← Finset.sum_filter]
  simp

/-- **Double counting (rows = columns).** Total size of the family equals the sum of
per-coordinate multiplicities. -/
theorem sum_card_eq_sum_mult (T : Finset κ) (A : κ → Finset ι) :
    ∑ α ∈ T, (A α).card = ∑ x : ι, mult T A x := by
  classical
  have hL : ∑ α ∈ T, (A α).card
      = ∑ α ∈ T, ∑ x : ι, (if x ∈ A α then 1 else 0) :=
    Finset.sum_congr rfl (fun α _ => card_eq_sum_indicator (A α))
  have hR : ∑ x : ι, mult T A x
      = ∑ x : ι, ∑ α ∈ T, (if x ∈ A α then 1 else 0) :=
    Finset.sum_congr rfl (fun x _ => mult_eq_sum T A x)
  rw [hL, hR, Finset.sum_comm]

end GCXK25SecondMoment

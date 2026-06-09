import ArkLib.Data.CodingTheory.ProximityGap.Assault_sumproduct

open Polynomial Finset
open ArkLib.ProximityGap.SumProduct
open ArkLib.CodingTheory.JohnsonSimplex

instance : Fact (Nat.Prime 5) := ⟨by norm_num⟩

noncomputable def D5 : Fin 5 ↪ ZMod 5 := ⟨fun i => ((i : ℕ) : ZMod 5), by
  intro a b h
  simp only at h
  have : (a.val : ZMod 5) = (b.val : ZMod 5) := h
  rw [ZMod.natCast_eq_natCast_iff, Nat.modEq_iff_dvd] at this
  -- |a.val - b.val| < 5 and divisible by 5 forces equality
  have hlt : (a.val : ℤ) - b.val < 5 ∧ (b.val : ℤ) - a.val < 5 := by
    constructor <;> [skip; skip] <;>
    · have := a.isLt; have := b.isLt; omega
  apply Fin.ext
  omega⟩

noncomputable def cw0 : Fin 5 → ZMod 5 := fun i => (dilate (1 : ZMod 5) (0 : (ZMod 5)[X])).eval (D5 i)

example :
    ((({cw0} : Finset (Fin 5 → ZMod 5)).card : ℝ) *
      ((5 : ℝ) ^ 2 - (Fintype.card (Fin 5) : ℝ) * (((2:ℕ) - 1 : ℕ) : ℝ)))
      ≤ (Fintype.card (Fin 5) : ℝ) ^ 2 := by
  refine dilated_list_johnson_bound_unchanged D5 2 (0 : Fin 5 → ZMod 5) 1 one_ne_zero
    {cw0} 5 ?_ ?_
  · intro cw hcw
    rw [Finset.mem_singleton] at hcw; subst hcw
    exact ⟨0, by simp, rfl⟩
  · intro cw hcw
    rw [Finset.mem_singleton] at hcw; subst hcw
    have hz : cw0 = (fun _ => (0 : ZMod 5)) := by
      funext i; simp [cw0, dilate_eval]
    rw [hz, agree_self]
    simp

example : (0:ℝ) < (5:ℝ)^2 - (5:ℝ) * (1:ℝ) := by norm_num

#print axioms D5
#print axioms cw0

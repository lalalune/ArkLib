import ArkLib.Data.CodingTheory.ProximityGap.Assault_sumproduct

open Polynomial Finset
open ArkLib.ProximityGap.SumProduct

-- Concrete domain F = ℚ, ι = Fin 3.
noncomputable def Dq : Fin 3 ↪ ℚ := ⟨fun i => (i : ℚ), by
  intro a b h
  simp only at h
  exact Fin.ext (by exact_mod_cast h)⟩

-- All hypotheses of pairwise_agree_dilate_le hold concretely (p = X, q = 0, k = 2, c = 1):
-- This is the SATURATING witness: p = X and q = 0 agree exactly at coordinate 0 (D 0 = 0),
-- so the agreement set is NONEMPTY (card = 1 = k-1). NOT vacuous.
example : (Finset.univ.filter
    (fun i => (dilate (1:ℚ) (X:ℚ[X])).eval (Dq i) = (dilate (1:ℚ) (0:ℚ[X])).eval (Dq i))).card ≤ 2 - 1 :=
  pairwise_agree_dilate_le (D := Dq) (k := 2) (c := 1) one_ne_zero
    (by simp [Polynomial.natDegree_X]) (by simp)
    (Polynomial.X_ne_zero)

-- Show the agreement set is EXACTLY {0} (nonempty, so the hypotheses are non-vacuously satisfiable
-- and the ≤ k-1 = 1 bound is TIGHT). We compute eval directly.
-- dilate 1 X = X.comp(C 1 * X) = X.comp(X) = X ; dilate 1 0 = 0.
-- eval (Dq i) X = (i:ℚ) ; eval (Dq i) 0 = 0. Agreement at i ⟺ (i:ℚ) = 0 ⟺ i = 0.
example : (Finset.univ.filter
    (fun i => (dilate (1:ℚ) (X:ℚ[X])).eval (Dq i) = (dilate (1:ℚ) (0:ℚ[X])).eval (Dq i)))
    = {(0 : Fin 3)} := by
  ext i
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton,
    dilate_eval, Polynomial.eval_X, Polynomial.eval_zero, one_mul]
  constructor
  · intro h
    -- Dq i = 0 means (i:ℚ) = 0 means i = 0
    have : (i : ℚ) = 0 := h
    fin_cases i <;> simp_all
  · intro h; subst h; rfl

-- Hence card = 1: nonempty agreement set, bound k-1 = 1 is saturated, NOT vacuous.
example : (Finset.univ.filter
    (fun i => (dilate (1:ℚ) (X:ℚ[X])).eval (Dq i) = (dilate (1:ℚ) (0:ℚ[X])).eval (Dq i))).card = 1 := by
  rw [show (Finset.univ.filter
    (fun i => (dilate (1:ℚ) (X:ℚ[X])).eval (Dq i) = (dilate (1:ℚ) (0:ℚ[X])).eval (Dq i)))
    = {(0 : Fin 3)} from by
      ext i
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton,
        dilate_eval, Polynomial.eval_X, Polynomial.eval_zero, one_mul]
      constructor
      · intro h; have : (i : ℚ) = 0 := h; fin_cases i <;> simp_all
      · intro h; subst h; rfl]
  simp

#print axioms Dq

import ArkLib.Data.CodingTheory.ReedSolomon.Folded

open Polynomial

namespace ScratchRefute

open ReedSolomon.Folded

/-- The full-injectivity claim `Function.Injective (frsEvalOnPoints domain s ω)` is FALSE:
the source `Polynomial F` is infinite-dimensional while the target `ι → Fin s → F` is
finite-dimensional, so the kernel is nonzero whenever the target is finite. Concretely the
vanishing polynomial over all fold points is a nonzero kernel element. -/
theorem full_injectivity_is_false
    {ι : Type} [Fintype ι] [DecidableEq ι] [Nonempty ι]
    {F : Type} [Field F] [DecidableEq F]
    (domain : ι ↪ F) (s : ℕ) (hs : 0 < s) (ω : F) (hω : ω ≠ 0) :
    ¬ Function.Injective (frsEvalOnPoints domain s ω) := by
  intro hinj
  -- The vanishing polynomial: product over all fold points of (X - point).
  -- It is nonzero (finite product of nonzero monics) but evaluates to 0 everywhere.
  classical
  -- Build the polynomial vanishing on every domain i * ω^j.
  let pts : Finset F := Finset.image (fun (q : ι × Fin s) => domain q.1 * ω ^ (q.2 : ℕ))
    Finset.univ
  let v : Polynomial F := ∏ a ∈ pts, (X - C a)
  have hv_ne : v ≠ 0 := by
    apply Finset.prod_ne_zero_iff.mpr
    intro a _
    exact X_sub_C_ne_zero a
  have hv_eval : ∀ (x : ι) (j : Fin s), v.eval (domain x * ω ^ (j : ℕ)) = 0 := by
    intro x j
    have hmem : domain x * ω ^ (j : ℕ) ∈ pts := by
      apply Finset.mem_image.mpr
      exact ⟨(x, j), Finset.mem_univ _, rfl⟩
    simp only [v, eval_prod]
    apply Finset.prod_eq_zero hmem
    simp
  have h0 : frsEvalOnPoints domain s ω v = frsEvalOnPoints domain s ω 0 := by
    rw [map_zero]
    ext x j
    simp only [frsEvalOnPoints, LinearMap.coe_mk, AddHom.coe_mk]
    exact hv_eval x j
  have := hinj h0
  exact hv_ne this

#print axioms full_injectivity_is_false

end ScratchRefute

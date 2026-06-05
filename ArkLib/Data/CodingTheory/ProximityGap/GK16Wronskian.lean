/-
GK16 Lemma 12, next layer: the *provable* direction of the folded-Wronskian
linear-independence criterion.

Building on `ArkLib.FRS.GK16.foldedWronskian` and `natDegree_foldedWronskian_le`
(ProximityPrizeLeaves.lean), we prove the easy direction of GK16 Lemma 12:

  if the folded Wronskian `det [ (P j)(ω^a · X) ]_{a,j}` is NONZERO, then the
  polynomials `P₀, …, P_{s-1}` are linearly independent over `F`.

Mathematical content (the "linear dependence ⟹ det = 0" half):
a linear dependence `∑ j, c j • P j = 0` (with `c ≠ 0`) makes the *columns* of
the dilation matrix `M a j = (P j).comp (q a)` linearly dependent over `F[X]`
(apply `(·).comp (q a)`, which is additive and fixes constants), hence the
matrix kills a nonzero `F[X]`-vector and `det M = 0`.

This is a standalone, self-contained restatement: the relevant pieces of
`ArkLib.FRS.GK16` are reproduced locally so the file compiles against Mathlib
only.  Axiom-clean, no `sorry`.
-/
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.LinearAlgebra.Matrix.ToLinearEquiv
import Mathlib.Algebra.Polynomial.Eval.Defs
import Mathlib.Algebra.Polynomial.Eval.SMul
import Mathlib.Algebra.Polynomial.Coeff
import Mathlib.LinearAlgebra.LinearIndependent.Lemmas

open Polynomial Matrix

namespace ArkLib.FRS.GK16

/-- A per-row dilation matrix: `M a j = (P j).comp (q a)`. -/
noncomputable def dilateMatrix {F : Type*} [CommRing F] {s : ℕ}
    (P : Fin s → F[X]) (q : Fin s → F[X]) : Matrix (Fin s) (Fin s) F[X] :=
  fun a j => (P j).comp (q a)

/-- **Folded Wronskian** (GK16 Definition 11, `t = s` case). With `q a = C (ω^a) * X`
this is `det [ (P j)(ω^a · X) ]_{a, j < s}`. -/
noncomputable def foldedWronskian {F : Type*} [CommRing F] {s : ℕ}
    (P : Fin s → F[X]) (ω : F) : F[X] :=
  (dilateMatrix P (fun a => Polynomial.C (ω ^ (a : ℕ)) * Polynomial.X)).det

/-- **Linear dependence kills the dilation determinant.**
If the columns `P` admit a nonzero `F`-linear dependence `∑ j, c j • P j = 0`,
then for any substitution functions `q`, the dilation determinant vanishes.
This is the engine behind the GK16 Lemma 12 criterion. -/
theorem det_dilateMatrix_eq_zero_of_dep {F : Type*} [Field F] {s : ℕ}
    (P : Fin s → F[X]) (q : Fin s → F[X])
    (c : Fin s → F) (hc : ∃ i, c i ≠ 0) (hdep : ∑ j, c j • P j = 0) :
    (dilateMatrix P q).det = 0 := by
  classical
  -- Lift the `F`-dependence to a nonzero `F[X]`-vector `v j = C (c j)`.
  set v : Fin s → F[X] := fun j => Polynomial.C (c j) with hv
  -- `v` is nonzero, witnessed by the index `i` with `c i ≠ 0`.
  have hv_ne : v ≠ 0 := by
    obtain ⟨i, hi⟩ := hc
    intro h
    apply hi
    have : v i = 0 := by rw [h]; rfl
    simpa [hv, Polynomial.C_eq_zero] using this
  -- The dilation matrix kills `v`: `(M *ᵥ v) a = (∑ j, c j • P j).comp (q a) = 0`.
  have hMv : (dilateMatrix P q) *ᵥ v = 0 := by
    funext a
    simp only [Matrix.mulVec, dotProduct, dilateMatrix, hv, Pi.zero_apply]
    -- ∑ j, (P j).comp (q a) * C (c j)  =  (∑ j, c j • P j).comp (q a) = 0
    have hcomp : ∑ j, (P j).comp (q a) * Polynomial.C (c j)
        = (∑ j, c j • P j).comp (q a) := by
      rw [Polynomial.sum_comp]
      refine Finset.sum_congr rfl (fun j _ => ?_)
      rw [Polynomial.smul_comp, Polynomial.smul_eq_C_mul, mul_comm]
    rw [hcomp, hdep, Polynomial.zero_comp]
  -- A nonzero kernel vector forces `det = 0`.
  exact (Matrix.exists_mulVec_eq_zero_iff.mp ⟨v, hv_ne, hMv⟩)

/-- **GK16 Lemma 12 (provable direction).**
If the folded Wronskian of `P₀, …, P_{s-1}` (with dilation parameter `ω`) is
nonzero, then `P` is linearly independent over `F`.

Contrapositive of `det_dilateMatrix_eq_zero_of_dep`: any `F`-linear dependence
would make the dilation determinant — hence the folded Wronskian — vanish. -/
theorem gk16_folded_wronskian_nonvanishing {F : Type*} [Field F] {s : ℕ}
    (P : Fin s → F[X]) (ω : F)
    (hW : foldedWronskian P ω ≠ 0) :
    LinearIndependent F P := by
  by_contra hdep
  rw [Fintype.not_linearIndependent_iff] at hdep
  obtain ⟨c, hsum, i, hi⟩ := hdep
  apply hW
  exact det_dilateMatrix_eq_zero_of_dep P _ c ⟨i, hi⟩ hsum

end ArkLib.FRS.GK16

-- Axiom audit (run via `#print axioms` below).
#print axioms ArkLib.FRS.GK16.gk16_folded_wronskian_nonvanishing

/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/

import Mathlib.RingTheory.Polynomial.Basic
import Mathlib.LinearAlgebra.FiniteDimensional.Defs
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.LinearAlgebra.Dimension.Constructions

/-!
# Dimension of the low-degree polynomial space

`Module.finrank R (Polynomial.degreeLT R k) = k`, via the canonical coefficient isomorphism
`Polynomial.degreeLTEquiv : degreeLT R k ≃ₗ[R] (Fin k → R)`.

This is the dimension count underlying polynomial interpolation and the Reed–Solomon / Berlekamp–
Welch / Polishchuk–Spielman existence arguments: the space of degree-`< k` polynomials is
`k`-dimensional, so a system with more constraints than `k` (or, bivariately, than the bidegree
dimension) has a nonzero solution.
-/

namespace Polynomial

variable {R : Type*} [DivisionRing R]

/-- The space of polynomials of degree `< k` over a division ring is `k`-dimensional. -/
@[simp]
theorem finrank_degreeLT (k : ℕ) : Module.finrank R (Polynomial.degreeLT R k) = k := by
  rw [(Polynomial.degreeLTEquiv R k).finrank_eq, Module.finrank_fintype_fun_eq_card,
    Fintype.card_fin]

end Polynomial

namespace Polynomial

variable {F : Type*} [Field F]

/-- **Bivariate (Y-degree ≤ 1) interpolation existence.**  Given `N` points `(xⱼ, yⱼ)` with
`N < 2m`, there is a nonzero pair of polynomials `(A, B)` of degree `< m` with
`A(xⱼ) + yⱼ · B(xⱼ) = 0` at every point.  This is the Polishchuk–Spielman / Berlekamp–Welch
existence engine: the pair-space `degreeLT m × degreeLT m` has dimension `2m`, the evaluation map to
`F^N` has rank `≤ N < 2m`, so its kernel is nontrivial.  Specialised to `A = −N₀`, `B = E`, `y = `
the received values, it yields the shared error-locator / key-equation solution behind the BCIKS20
proximity-gap bivariate lift. -/
theorem exists_bivariate_interpolant {J : Type*} [Fintype J] (m : ℕ) (x y : J → F)
    (hJ : Fintype.card J < 2 * m) :
    ∃ A B : F[X], A ∈ degreeLT F m ∧ B ∈ degreeLT F m ∧ (A ≠ 0 ∨ B ≠ 0) ∧
      ∀ j, A.eval (x j) + y j * B.eval (x j) = 0 := by
  classical
  haveI : FiniteDimensional F (degreeLT F m) :=
    LinearEquiv.finiteDimensional (degreeLTEquiv F m).symm
  -- the evaluation linear map `(A, B) ↦ (j ↦ A(xⱼ) + yⱼ·B(xⱼ))`
  let T : (degreeLT F m × degreeLT F m) →ₗ[F] (J → F) :=
    { toFun := fun AB j => AB.1.val.eval (x j) + y j * AB.2.val.eval (x j)
      map_add' := by
        intro a b; funext j
        simp only [Prod.fst_add, Prod.snd_add, Submodule.coe_add, eval_add, Pi.add_apply]
        ring
      map_smul' := by
        intro c a; funext j
        simp only [Prod.smul_fst, Prod.smul_snd, SetLike.val_smul, smul_eq_C_mul, eval_mul,
          eval_C, RingHom.id_apply, Pi.smul_apply, smul_eq_mul]
        ring }
  -- dimension count: `dim (J → F) = N < 2m = dim (degreeLT m × degreeLT m)`
  have hdim : Module.finrank F (J → F) < Module.finrank F (degreeLT F m × degreeLT F m) := by
    simp only [Module.finrank_prod, finrank_degreeLT, Module.finrank_fintype_fun_eq_card]
    omega
  -- hence the kernel is nontrivial
  have hker : LinearMap.ker T ≠ ⊥ := LinearMap.ker_ne_bot_of_finrank_lt hdim
  obtain ⟨AB, hABmem, hAB0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hker
  refine ⟨AB.1.val, AB.2.val, AB.1.property, AB.2.property, ?_, ?_⟩
  · -- `(A, B) ≠ 0` means `A ≠ 0 ∨ B ≠ 0`
    by_contra h
    push_neg at h
    apply hAB0
    have h1 : AB.1 = 0 := Subtype.ext h.1
    have h2 : AB.2 = 0 := Subtype.ext h.2
    exact Prod.ext h1 h2
  · intro j
    have := LinearMap.mem_ker.mp hABmem
    exact congrFun this j

end Polynomial

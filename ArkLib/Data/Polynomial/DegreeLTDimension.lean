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

/-- **Bivariate (Y-degree ≤ 1) interpolation existence, asymmetric degrees.**  Given `N` points
`(xⱼ, yⱼ)` with `N < d₀ + d₁`, there is a nonzero pair `(A, B)` with `deg A < d₀`, `deg B < d₁`, and
`A(xⱼ) + yⱼ · B(xⱼ) = 0` at every point.  This is the Polishchuk–Spielman / Berlekamp–Welch
existence engine: the pair-space `degreeLT d₀ × degreeLT d₁` has dimension `d₀ + d₁`, the evaluation
map to `F^N` has rank `≤ N < d₀ + d₁`, so its kernel is nontrivial.  With `d₁ = e+1` (locator `E :=
B`), `d₀ = k+e` (`N := −A`), and `y :=` received values, `A(αⱼ) + yⱼ E(αⱼ) = 0` is exactly the
Berlekamp–Welch key equation `E(αⱼ)·yⱼ = N(αⱼ)` — and `k + 2e + 1 > n` is the unique-decoding
condition.  This is the existence half of the BCIKS20 proximity-gap bivariate lift. -/
theorem exists_bivariate_interpolant {J : Type*} [Fintype J] (d₀ d₁ : ℕ) (x y : J → F)
    (hJ : Fintype.card J < d₀ + d₁) :
    ∃ A B : F[X], A ∈ degreeLT F d₀ ∧ B ∈ degreeLT F d₁ ∧ (A ≠ 0 ∨ B ≠ 0) ∧
      ∀ j, A.eval (x j) + y j * B.eval (x j) = 0 := by
  classical
  haveI : FiniteDimensional F (degreeLT F d₀) :=
    LinearEquiv.finiteDimensional (degreeLTEquiv F d₀).symm
  haveI : FiniteDimensional F (degreeLT F d₁) :=
    LinearEquiv.finiteDimensional (degreeLTEquiv F d₁).symm
  -- the evaluation linear map `(A, B) ↦ (j ↦ A(xⱼ) + yⱼ·B(xⱼ))`
  let T : (degreeLT F d₀ × degreeLT F d₁) →ₗ[F] (J → F) :=
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
  -- dimension count: `dim (J → F) = N < d₀ + d₁ = dim (degreeLT d₀ × degreeLT d₁)`
  have hdim : Module.finrank F (J → F) < Module.finrank F (degreeLT F d₀ × degreeLT F d₁) := by
    simp only [Module.finrank_prod, finrank_degreeLT, Module.finrank_fintype_fun_eq_card]
    omega
  -- hence the kernel is nontrivial
  have hker : LinearMap.ker T ≠ ⊥ := LinearMap.ker_ne_bot_of_finrank_lt hdim
  obtain ⟨AB, hABmem, hAB0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hker
  refine ⟨AB.1.val, AB.2.val, AB.1.property, AB.2.property, ?_, ?_⟩
  · by_contra h
    push_neg at h
    exact hAB0 (Prod.ext (Subtype.ext h.1) (Subtype.ext h.2))
  · intro j
    exact congrFun (LinearMap.mem_ker.mp hABmem) j

/-- **Berlekamp–Welch existence via the bivariate engine.**  At the unique-decoding rate
`k + 2e + 1 > n` (`n := |ι|`), for any word `y` there is a Berlekamp–Welch pair `(E, N)` — `E ≠ 0`,
`deg E < e + 1`, `deg N < k + e` — solving the key equation `E(αᵢ)·yᵢ = N(αᵢ)` on every coordinate.
A second, dimension-count proof of the key-equation existence (the explicit error-locator proof is
`ReedSolomon.berlekamp_welch_exists`), and the form that drives the bivariate proximity-gap lift. -/
theorem exists_berlekamp_welch {ι : Type*} [Fintype ι] (k e : ℕ) (α : ι ↪ F) (y : ι → F)
    (hn : Fintype.card ι < k + e + (e + 1)) :
    ∃ E N : F[X], E ≠ 0 ∧ E ∈ degreeLT F (e + 1) ∧ N ∈ degreeLT F (k + e) ∧
      ∀ i, E.eval (α i) * y i = N.eval (α i) := by
  obtain ⟨A, B, hA, hB, hAB0, hkey⟩ :=
    exists_bivariate_interpolant (k + e) (e + 1) (fun i => α i) y (by omega)
  -- `E := B` is nonzero: `B = 0` would force `A` (degree `< k+e ≤ n`) to vanish at `n` points
  have hB0 : B ≠ 0 := by
    rintro rfl
    rcases hAB0 with hA0 | hB0
    · -- `A(αᵢ) = 0` for all `i`; `A` has degree `< k+e` but `n ≥ k+e` distinct roots ⇒ `A = 0`
      apply hA0
      by_contra hAne
      have hroots : (Finset.univ.map α) ⊆ A.roots.toFinset := by
        intro z hz
        rw [Finset.mem_map] at hz; obtain ⟨i, _, rfl⟩ := hz
        rw [Multiset.mem_toFinset, mem_roots hAne, IsRoot.def]
        have := hkey i; simpa using this
      have h1 : Fintype.card ι ≤ A.natDegree := by
        calc Fintype.card ι = (Finset.univ.map α).card := by rw [Finset.card_map, Finset.card_univ]
          _ ≤ A.roots.toFinset.card := Finset.card_le_card hroots
          _ ≤ Multiset.card A.roots := Multiset.toFinset_card_le _
          _ ≤ A.natDegree := card_roots' _
      have h2 : A.natDegree < k + e := by
        rcases eq_or_ne A 0 with rfl | h; · simp_all
        exact (natDegree_lt_iff_degree_lt h).mpr (mem_degreeLT.mp hA)
      omega
    · exact hB0 rfl
  refine ⟨B, -A, hB0, hB, Submodule.neg_mem _ hA, ?_⟩
  intro i
  have := hkey i
  rw [eval_neg]; linear_combination -this

end Polynomial

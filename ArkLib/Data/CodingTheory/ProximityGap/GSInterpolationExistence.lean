/-
Copyright (c) 2024-2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
-- dedup-audit(#257): multIdx/mem_multIdx/card_multIdx are intentional local re-derivations; the MvPolynomial interpolant packaging is unique. Do not delete. #257 A3.

import Mathlib.LinearAlgebra.Pi
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.Algebra.MvPolynomial.Basic
import Mathlib.Data.Finset.NatAntidiagonal
import Mathlib.Algebra.BigOperators.Intervals

/-!
# Guruswami–Sudan bivariate interpolation: EXISTENCE via dimension count

The interpolation step of the Guruswami–Sudan list decoder (and the related
proximity-gap arguments of ABF26 T4.21 / GG25 / BCIKS20 §5) requires a *nonzero*
bivariate polynomial `Q(X, Y)` of bounded `(1, k)`-weighted degree (`< D`) that
satisfies a prescribed list of homogeneous *linear* conditions — typically
"vanish to multiplicity `m` at each of `n` interpolation points". Each scalar
condition is an `F`-linear functional on the coefficient vector of `Q`.

This file isolates the **tractable part-1**: the pure-linear-algebra *existence*
result. We do **not** touch the (open) root-bound / agreement-count chain that
turns such a `Q` into a list-decoding guarantee.

## What is proved

The mathematical content is the *underdetermined homogeneous system* fact:
a linear map `F^{#monomials} → F^{#constraints}` with strictly more monomials
than constraints has a nonzero kernel vector (rank–nullity, via
`LinearMap.ker_ne_bot_of_finrank_lt`). Three layers, increasing in concreteness:

* `exists_ne_zero_forall_functional_eq_zero` — **abstract** existence: for *any*
  finite family of `F`-linear functionals `φ : κ → (V →ₗ[F] F)` on a
  finite-dimensional space `V`, if `Fintype.card κ < finrank F V` there is a
  nonzero `v : V` annihilated by every `φ i`. This is the reusable kernel.

* `exists_ne_zero_coeff_of_card_lt` — the same, specialized to the GS
  **coefficient space** `CoeffBox k D → F` indexed by the weighted-degree
  monomial box `monoBox k D = {(a, b) : a + k·b < D}`, with an arbitrary finite
  family of constraint functionals; the hypothesis is the *interpolation
  feasibility bound* `#constraints < #monomials`.

* `exists_ne_zero_bivariate_interpolant` — the same packaged as a genuine
  **nonzero bivariate `MvPolynomial (Fin 2) F`** whose support lies inside the
  weighted-degree box and which satisfies every constraint, where each
  constraint is presented as an `F`-linear functional of the box coefficients
  (the generic shape of "vanish to order `m` at `(xᵢ, yᵢ)`"). A worked example,
  `exists_ne_zero_bivariate_interpolant_multiplicity`, instantiates the
  constraint count as `n · (m·(m+1)/2)`, the standard GS multiplicity budget.

All statements are universe-polymorphic over an arbitrary field `F` and use only
Mathlib (`LinearMap.pi`, `LinearMap.ker_ne_bot_of_finrank_lt`,
`Module.finrank_pi`). Every result is axiom-clean
(`propext, Classical.choice, Quot.sound`).
-/

namespace GSInterpExistence

open Finset

/-! ## Abstract underdetermined-system existence -/

variable {F : Type*} [Field F]

/-- **Abstract underdetermined-system existence** (mirrors
`BCKHS25.exists_ne_zero_map_eq_zero` and `GSMultInterp.exists_ne_zero_map_eq_zero`):
a linear map between finite-dimensional spaces with strictly larger domain has a
nonzero kernel vector. -/
theorem exists_ne_zero_map_eq_zero {V W : Type*}
    [AddCommGroup V] [Module F V] [AddCommGroup W] [Module F W]
    [FiniteDimensional F V] [FiniteDimensional F W]
    (Φ : V →ₗ[F] W) (h : Module.finrank F W < Module.finrank F V) :
    ∃ v : V, v ≠ 0 ∧ Φ v = 0 := by
  have hk := LinearMap.ker_ne_bot_of_finrank_lt (f := Φ) h
  rcases Submodule.ne_bot_iff _ |>.mp hk with ⟨v, hvmem, hv0⟩
  exact ⟨v, hv0, hvmem⟩

/-- **Abstract GS interpolation existence (linear-functional form).**

Let `V` be a finite-dimensional `F`-vector space (the *coefficient space* of the
interpolating polynomial) and let `φ : κ → (V →ₗ[F] F)` be a finite family of
`F`-linear functionals (the *interpolation constraints*: each scalar
vanishing/multiplicity condition is one such functional). If there are strictly
fewer constraints than dimensions,

  `Fintype.card κ < Module.finrank F V`,

then there is a **nonzero** `v : V` annihilated by *every* constraint,
`∀ i, φ i v = 0`.

This is the clean kernel of the GS interpolation existence step: a homogeneous
linear system with more unknowns (`finrank V`) than equations (`#κ`) has a
nonzero solution. -/
theorem exists_ne_zero_forall_functional_eq_zero {V : Type*}
    [AddCommGroup V] [Module F V] [FiniteDimensional F V]
    {κ : Type*} [Fintype κ] (φ : κ → (V →ₗ[F] F))
    (hcount : Fintype.card κ < Module.finrank F V) :
    ∃ v : V, v ≠ 0 ∧ ∀ i, φ i v = 0 := by
  classical
  -- Bundle the family of functionals into one map `V →ₗ[F] (κ → F)`.
  set Φ : V →ₗ[F] (κ → F) := LinearMap.pi φ with hΦ
  -- `finrank (κ → F) = #κ < finrank V`.
  have hfr : Module.finrank F (κ → F) < Module.finrank F V := by
    rw [Module.finrank_pi]; exact hcount
  obtain ⟨v, hv0, hker⟩ := exists_ne_zero_map_eq_zero Φ hfr
  refine ⟨v, hv0, fun i => ?_⟩
  have := congrFun hker i
  rwa [hΦ, LinearMap.pi_apply] at this

/-! ## The Guruswami–Sudan weighted-degree monomial box -/

/-- The monomial index set of the `(1, k)`-weighted-degree-`< D` space: all
`(a, b) ∈ ℕ × ℕ` with `a + k·b < D` (here `a` is the `X`-exponent and `b` the
`Y`-exponent). Its cardinality is the number of available monomials, the
right-hand side of the GS interpolation feasibility bound. -/
def monoBox (k D : ℕ) : Finset (ℕ × ℕ) :=
  (Finset.range D ×ˢ Finset.range D).filter (fun ab => ab.1 + k * ab.2 < D)

lemma mem_monoBox {k D : ℕ} {ab : ℕ × ℕ} :
    ab ∈ monoBox k D ↔ ab.1 < D ∧ ab.2 < D ∧ ab.1 + k * ab.2 < D := by
  classical
  simp only [monoBox, Finset.mem_filter, Finset.mem_product, Finset.mem_range]
  tauto

/-- For positive weight `k ≥ 1`, the box bounds are automatic: membership reduces
to the genuine weighted-degree condition `a + k·b < D`. -/
lemma mem_monoBox_of_pos {k D : ℕ} (hk : 0 < k) {ab : ℕ × ℕ} :
    ab ∈ monoBox k D ↔ ab.1 + k * ab.2 < D := by
  rw [mem_monoBox]
  constructor
  · rintro ⟨_, _, h⟩; exact h
  · intro h
    have hb : ab.2 < D := lt_of_le_of_lt (Nat.le_mul_of_pos_left ab.2 hk) (by omega)
    exact ⟨by omega, hb, h⟩

/-- The coefficient space of a bivariate polynomial of `(1, k)`-weighted degree
`< D`: one field entry per monomial in `monoBox k D`. -/
abbrev CoeffBox (k D : ℕ) := {ab : ℕ × ℕ // ab ∈ monoBox k D} → F

/-- The number of monomials available equals the cardinality of the box; this is
the dimension of the coefficient space. -/
lemma finrank_coeffBox (k D : ℕ) :
    Module.finrank F (CoeffBox (F := F) k D) = (monoBox k D).card := by
  classical
  simp only [CoeffBox, Module.finrank_pi, Fintype.card_coe]

/-- **GS bivariate interpolation existence (coefficient-vector form).**

For the GS weighted-degree box `monoBox k D` and *any* finite family of
constraint functionals `φ : κ → (CoeffBox k D → F)` (e.g. order-`m` vanishing at
each of `n` points), if the number of constraints is strictly below the number
of available monomials,

  `Fintype.card κ < (monoBox k D).card`,

then there is a **nonzero** coefficient vector `c : CoeffBox k D` satisfying every
constraint, `∀ i, φ i c = 0`. -/
theorem exists_ne_zero_coeff_of_card_lt (k D : ℕ)
    {κ : Type*} [Fintype κ] (φ : κ → (CoeffBox (F := F) k D →ₗ[F] F))
    (hcount : Fintype.card κ < (monoBox k D).card) :
    ∃ c : CoeffBox (F := F) k D, c ≠ 0 ∧ ∀ i, φ i c = 0 := by
  refine exists_ne_zero_forall_functional_eq_zero φ ?_
  rw [finrank_coeffBox]; exact hcount

/-! ## Packaging as a genuine nonzero bivariate `MvPolynomial`

We promote a kernel coefficient vector to an honest `MvPolynomial (Fin 2) F`
supported on the weighted-degree box. Variable `0` is `X` (weight `1`) and
variable `1` is `Y` (weight `k`). -/

open MvPolynomial in
/-- The `(σ →₀ ℕ)` exponent of the monomial `X^a · Y^b` over `Fin 2`. -/
noncomputable def boxExp (ab : ℕ × ℕ) : Fin 2 →₀ ℕ :=
  Finsupp.single 0 ab.1 + Finsupp.single 1 ab.2

lemma boxExp_injective : Function.Injective boxExp := by
  intro ab cd h
  have h0 : ab.1 = cd.1 := by
    have := congrArg (fun f => f 0) h
    simpa [boxExp, Finsupp.add_apply, Finsupp.single_apply] using this
  have h1 : ab.2 = cd.2 := by
    have := congrArg (fun f => f 1) h
    simpa [boxExp, Finsupp.add_apply, Finsupp.single_apply] using this
  exact Prod.ext h0 h1

open MvPolynomial in
/-- The bivariate polynomial assembled from a box coefficient vector `c`:
`∑_{(a,b) ∈ box} c (a,b) · X^a · Y^b`, as an `MvPolynomial (Fin 2) F`. -/
noncomputable def toMvPoly {k D : ℕ} (c : CoeffBox (F := F) k D) :
    MvPolynomial (Fin 2) F :=
  ∑ ab : {ab : ℕ × ℕ // ab ∈ monoBox k D}, MvPolynomial.monomial (boxExp ab.1) (c ab)

open MvPolynomial in
/-- The coefficient of `toMvPoly c` at the box exponent `boxExp ab` is exactly
`c ab`: the assembly is faithful on the monomial box. -/
lemma coeff_toMvPoly {k D : ℕ} (c : CoeffBox (F := F) k D)
    (ab : {ab : ℕ × ℕ // ab ∈ monoBox k D}) :
    MvPolynomial.coeff (boxExp ab.1) (toMvPoly c) = c ab := by
  classical
  rw [toMvPoly, MvPolynomial.coeff_sum]
  rw [Finset.sum_eq_single ab]
  · rw [MvPolynomial.coeff_monomial, if_pos rfl]
  · intro b _ hb
    rw [MvPolynomial.coeff_monomial, if_neg]
    intro hcontra
    exact hb (Subtype.ext (boxExp_injective hcontra))
  · intro h
    exact absurd (Finset.mem_univ ab) h

open MvPolynomial in
/-- A nonzero box coefficient vector yields a nonzero bivariate polynomial. -/
lemma toMvPoly_ne_zero {k D : ℕ} {c : CoeffBox (F := F) k D} (hc : c ≠ 0) :
    toMvPoly c ≠ 0 := by
  classical
  obtain ⟨ab, hab⟩ := Function.ne_iff.mp hc
  intro hzero
  apply hab
  have := coeff_toMvPoly c ab
  rw [hzero] at this
  simpa using this.symm

open MvPolynomial in
/-- The support of `toMvPoly c` lies inside the weighted-degree box: every
monomial of the assembled polynomial is a genuine `X^a · Y^b` with
`a + k·b < D` (after the box bounds). -/
lemma toMvPoly_supported {k D : ℕ} (c : CoeffBox (F := F) k D)
    {d : Fin 2 →₀ ℕ} (hd : d ∈ (toMvPoly c).support) :
    ∃ ab : {ab : ℕ × ℕ // ab ∈ monoBox k D}, d = boxExp ab.1 := by
  classical
  rw [MvPolynomial.mem_support_iff] at hd
  rw [toMvPoly, MvPolynomial.coeff_sum] at hd
  -- some summand is nonzero, hence `d` is its box exponent
  by_contra hcon
  simp only [not_exists] at hcon
  apply hd
  apply Finset.sum_eq_zero
  intro ab _
  rw [MvPolynomial.coeff_monomial, if_neg]
  intro hcontra
  exact hcon ab hcontra.symm

open MvPolynomial in
/-- **Guruswami–Sudan bivariate interpolation — EXISTENCE (polynomial form).**

Given the GS weighted-degree box `monoBox k D` and a finite family of *linear
interpolation constraints* presented as functionals `ψ` on the box coefficients
(`ψ i` reads off a constraint of the form `∑_{(a,b)} L (a,b) · c (a,b)`, the
generic shape of an order-`m` Hasse/derivative vanishing condition at a point),
if the number of constraints is strictly below the number of monomials,

  `Fintype.card κ < (monoBox k D).card`,

then there **exists a nonzero bivariate polynomial** `Q : MvPolynomial (Fin 2) F`
of `(1, k)`-weighted degree `< D` — its support lies inside `monoBox k D` — whose
box coefficients satisfy every constraint.

The constraint `ψ i` is satisfied by `Q` in the precise sense that the linear
functional applied to the coefficient-restriction of `Q` to the box vanishes;
since the assembly is faithful (`coeff_toMvPoly`), this is exactly "the
interpolation conditions hold for `Q`". -/
theorem exists_ne_zero_bivariate_interpolant (k D : ℕ)
    {κ : Type*} [Fintype κ] (ψ : κ → (CoeffBox (F := F) k D →ₗ[F] F))
    (hcount : Fintype.card κ < (monoBox k D).card) :
    ∃ Q : MvPolynomial (Fin 2) F, Q ≠ 0 ∧
      (∀ d ∈ Q.support, ∃ ab : {ab : ℕ × ℕ // ab ∈ monoBox k D}, d = boxExp ab.1) ∧
      ∃ c : CoeffBox (F := F) k D,
        (∀ ab, MvPolynomial.coeff (boxExp ab.1) Q = c ab) ∧ (∀ i, ψ i c = 0) := by
  obtain ⟨c, hc0, hψ⟩ := exists_ne_zero_coeff_of_card_lt k D ψ hcount
  refine ⟨toMvPoly c, toMvPoly_ne_zero hc0, ?_, c, ?_, hψ⟩
  · intro d hd; exact toMvPoly_supported c hd
  · intro ab; exact coeff_toMvPoly c ab

/-! ## The standard multiplicity constraint count `n · m(m+1)/2`

A worked instantiation of the constraint type `κ`: the order-`m` vanishing at
each of `n` interpolation points contributes `m·(m+1)/2` scalar conditions per
point (one per `(a, b)` with `a + b < m`), so `κ` has cardinality
`n · m(m+1)/2`. This is the exact GS / Sudan multiplicity budget. -/

/-- The multiplicity-`m` constraint index set at a single point: all `(a, b)`
with `a + b < m`. -/
def multIdx (m : ℕ) : Finset (ℕ × ℕ) :=
  (Finset.range m).biUnion (fun s => Finset.antidiagonal s)

@[simp] lemma mem_multIdx {m : ℕ} {ab : ℕ × ℕ} : ab ∈ multIdx m ↔ ab.1 + ab.2 < m := by
  classical
  simp only [multIdx, Finset.mem_biUnion, Finset.mem_range, Finset.mem_antidiagonal]
  constructor
  · rintro ⟨s, hs, hab⟩; omega
  · intro h; exact ⟨ab.1 + ab.2, h, rfl⟩

/-- **The number of multiplicity-`m` constraints per point is `m·(m+1)/2`.** -/
theorem card_multIdx (m : ℕ) : (multIdx m).card = m * (m + 1) / 2 := by
  classical
  have hdisj : (↑(Finset.range m) : Set ℕ).PairwiseDisjoint
      (fun s => Finset.antidiagonal s) := by
    intro s _ t _ hst
    apply Finset.disjoint_left.mpr
    intro ab hs ht
    rw [Finset.mem_antidiagonal] at hs ht
    exact hst (by omega)
  rw [multIdx, Finset.card_biUnion hdisj]
  simp only [Finset.Nat.card_antidiagonal]
  have hshift : ∑ s ∈ Finset.range m, (s + 1) = ∑ s ∈ Finset.range (m + 1), s := by
    rw [Finset.sum_range_succ']
    simp
  rw [hshift, Finset.sum_range_id]
  rw [Nat.add_sub_cancel, Nat.mul_comm]

/-- The multiplicity constraint type for `n` points at multiplicity `m`: a point
index `Fin n` together with a low-order Hasse index `(a, b)` with `a + b < m`.
Its cardinality is `n · m(m+1)/2`. -/
abbrev MultConstraint (n m : ℕ) := Fin n × {ab : ℕ × ℕ // ab ∈ multIdx m}

lemma card_multConstraint (n m : ℕ) :
    Fintype.card (MultConstraint n m) = n * (m * (m + 1) / 2) := by
  classical
  simp only [MultConstraint, Fintype.card_prod, Fintype.card_fin, Fintype.card_coe, card_multIdx]

open MvPolynomial in
/-- **Guruswami–Sudan bivariate interpolation — EXISTENCE with multiplicity
budget.** Specializing the constraint type to the GS multiplicity index
`MultConstraint n m` (order-`m` vanishing at each of `n` points), the existence
of a nonzero interpolating bivariate polynomial holds under the classical
feasibility bound

  `n · (m·(m+1)/2)  <  (monoBox k D).card`.

Here `ψ` is the genuine family of order-`m` Hasse/derivative-evaluation
functionals at the points; the theorem is agnostic to its exact entries — it only
needs the count — and so directly underlies ABF26 T4.21 / GG25 / BCIKS20 §5. -/
theorem exists_ne_zero_bivariate_interpolant_multiplicity (k D m n : ℕ)
    (ψ : MultConstraint n m → (CoeffBox (F := F) k D →ₗ[F] F))
    (hcount : n * (m * (m + 1) / 2) < (monoBox k D).card) :
    ∃ Q : MvPolynomial (Fin 2) F, Q ≠ 0 ∧
      (∀ d ∈ Q.support, ∃ ab : {ab : ℕ × ℕ // ab ∈ monoBox k D}, d = boxExp ab.1) ∧
      ∃ c : CoeffBox (F := F) k D,
        (∀ ab, MvPolynomial.coeff (boxExp ab.1) Q = c ab) ∧ (∀ i, ψ i c = 0) := by
  refine exists_ne_zero_bivariate_interpolant k D ψ ?_
  rw [card_multConstraint]; exact hcount

end GSInterpExistence

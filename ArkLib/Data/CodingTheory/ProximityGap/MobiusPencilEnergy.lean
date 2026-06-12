/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import Mathlib.GroupTheory.Perm.Basic
import Mathlib.GroupTheory.Perm.Cycle.Type
import Mathlib.Algebra.Group.Even
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Finset.Card
import Mathlib.GroupTheory.SpecificGroups.Cyclic.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset

/-!
# The Möbius pencil involution and its 2-orbit energy (#357, N1/C1 foundation)

The probe campaign identified **the Möbius-involution pencil energy** as the *only known
domain-separating invariant* for the proximity-gap threshold δ\* (the M3 census separates
smooth multiplicative subgroups from random evaluation domains, and the separation factors
through this statistic). This file builds its load-bearing core, axiom-clean.

For a finite **commutative** group `G` (the multiplicative evaluation subgroup `H ≤ F^×`) and a
parameter `b : G`, the *Möbius pencil involution* is

  `σ_b : G → G,   σ_b x = b · x⁻¹`

(the `a = 0` strip of the k=3 agreement pencil `(x−a)(y−a) = a²−b`, normalized: `x·y = b`).
Its fixed points are exactly the **square roots of `b`** (`x² = b`), and every non-fixed point
sits in a 2-orbit `{x, b·x⁻¹}`. The per-`b` 2-orbit count

  `t₂(b) = (|G| − #√b) / 2`

is the agreement-spectrum statistic that is `≈ n/2` on the `≈ n` subgroup pencils (so the
energy `Σ_b t₂(b)²` is `Θ(n³)`) yet thin for a random domain — the mechanism behind hypothesis
**N1** (`δ\*(H) = F(E₂(H)/n²)`) and connection **C1**.

Results:
- `mobiusInvol` : the involution as an `Equiv.Perm G`, with `mobiusInvol_involutive`.
- `mobiusInvol_apply_eq_self_iff` : `x` is fixed ⟺ `x² = b`.
- `t2`, `card_eq_two_mul_t2_add_fixed` : `|G| = 2·t₂(b) + #√b` (the orbit decomposition).
- `two_mul_t2_eq_support_card`, `card_eq_two_mul_t2_add_sqrtSet` : the exact finite-orbit
  form of the decomposition, using the cycle-type fact that an order-two permutation has even
  support.
- `t2_eq_card_sub_sqrtSet_card_div_two` : the exact normalizer-band statistic once the fixed
  point count is known; the empty/two-root cases give `t₂ = n/2` and `t₂ = (n-2)/2`.
- `card_image_univ_le_t2_add_sqrtSet` : a Möbius-invariant word has one value per 2-cycle plus
  fixed points; in cyclic groups this gives the half-dimension bound `≤ |G|/2 + 2`.

Axiom-clean: `[propext, Classical.choice, Quot.sound]` (see `#print axioms` at EOF).
-/

open Equiv

namespace ProximityGap.MobiusPencil

variable {G : Type*} [CommGroup G]

/-- The Möbius pencil involution `σ_b x = b · x⁻¹` on a commutative group, as a permutation.
It is its own inverse (commutativity: `(b·x⁻¹)⁻¹ = b⁻¹·x`, so `σ_b (σ_b x) = b·(b⁻¹·x) = x`). -/
def mobiusInvol (b : G) : Equiv.Perm G where
  toFun x := b * x⁻¹
  invFun x := b * x⁻¹
  left_inv x := by simp [mul_inv_rev]
  right_inv x := by simp [mul_inv_rev]

@[simp] lemma mobiusInvol_apply (b x : G) : mobiusInvol b x = b * x⁻¹ := rfl

/-- The Möbius involution is an involution. -/
theorem mobiusInvol_involutive (b : G) : Function.Involutive (mobiusInvol b) := by
  intro x; simp [mobiusInvol_apply, mul_inv_rev]

@[simp] lemma mobiusInvol_mobiusInvol (b x : G) :
    mobiusInvol b (mobiusInvol b x) = x := mobiusInvol_involutive b x

/-- `mobiusInvol b` squares to the identity permutation. -/
theorem mobiusInvol_sq (b : G) : (mobiusInvol b) * (mobiusInvol b) = 1 :=
  Equiv.Perm.ext (fun x => mobiusInvol_involutive b x)

/-- **Fixed points are square roots of `b`.** `σ_b x = x ⟺ x² = b`. -/
theorem mobiusInvol_apply_eq_self_iff {b x : G} : mobiusInvol b x = x ↔ x ^ 2 = b := by
  rw [mobiusInvol_apply, mul_inv_eq_iff_eq_mul, sq, eq_comm]

variable [Fintype G] [DecidableEq G]

/-- The set of square roots of `b` in `G` (the fixed points of `σ_b`). -/
def sqrtSet (b : G) : Finset G :=
  Finset.univ.filter (fun x => x ^ 2 = b)

@[simp] lemma mem_sqrtSet {b x : G} : x ∈ sqrtSet b ↔ x ^ 2 = b := by
  simp [sqrtSet]

/-- The square-root set is exactly the fixed-point set of `σ_b` (as a Finset). -/
theorem sqrtSet_eq_filter_fixed (b : G) :
    sqrtSet b = Finset.univ.filter (fun x => mobiusInvol b x = x) := by
  ext x
  simp only [sqrtSet, Finset.mem_filter, Finset.mem_univ, true_and,
    mobiusInvol_apply_eq_self_iff]

/-- **The orbit decomposition** `|G| = #√b + #{non-fixed}`. The non-fixed points are the
support of the involution `σ_b`; each lies in a 2-orbit `{x, b·x⁻¹}`. The 2-orbit count is
`t₂(b) = #{non-fixed}/2` (the pencil-energy summand). -/
theorem card_eq_sqrtSet_add_support (b : G) :
    Fintype.card G
      = (sqrtSet b).card + (Finset.univ.filter (fun x => mobiusInvol b x ≠ x)).card := by
  rw [sqrtSet_eq_filter_fixed, ← Finset.card_univ]
  simpa using
    (Finset.card_filter_add_card_filter_not (s := Finset.univ)
      (p := fun x => mobiusInvol b x = x)).symm

/-- The 2-orbit count of `σ_b` (the per-`b` Möbius pencil energy summand). -/
def t2 (b : G) : ℕ := (Finset.univ.filter (fun x => mobiusInvol b x ≠ x)).card / 2

/-- The support of `σ_b` (its non-fixed points) is closed under `σ_b` and fixed-point-free —
the structural fact that makes the 2-orbit pairing `x ↔ b·x⁻¹` well-defined (so `#support`
is even and `t₂(b) = #support/2`, the next brick). -/
theorem mobiusInvol_mapsTo_support (b : G) :
    ∀ x ∈ Finset.univ.filter (fun x => mobiusInvol b x ≠ x),
      mobiusInvol b x ∈ Finset.univ.filter (fun x => mobiusInvol b x ≠ x) := by
  intro x hx
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hx ⊢
  intro hcontra
  exact hx (by rw [← hcontra, mobiusInvol_mobiusInvol])

/-- The non-fixed support of the Möbius involution has even cardinality. -/
theorem mobiusInvol_support_card_even (b : G) :
    Even (Finset.univ.filter (fun x => mobiusInvol b x ≠ x)).card := by
  have hsupp : (mobiusInvol b).support
      = Finset.univ.filter (fun x => mobiusInvol b x ≠ x) := by
    ext x
    simp [Equiv.Perm.mem_support]
  have hdiv : 2 ∣ (mobiusInvol b).support.card :=
    Equiv.Perm.two_dvd_card_support (σ := mobiusInvol b) (mobiusInvol_sq b)
  rw [hsupp] at hdiv
  exact (even_iff_exists_two_nsmul _).2 hdiv

/-- The definition `t₂ = support.card / 2` is exact: the support consists of 2-cycles. -/
theorem two_mul_t2_eq_support_card (b : G) :
    2 * t2 b = (Finset.univ.filter (fun x => mobiusInvol b x ≠ x)).card := by
  unfold t2
  exact Nat.two_mul_div_two_of_even (mobiusInvol_support_card_even b)

/-- **Exact orbit decomposition.** The group is the disjoint union of fixed points (`√b`) and
two-cycles of `σ_b`, so `|G| = 2·t₂(b) + #√b`. -/
theorem card_eq_two_mul_t2_add_sqrtSet (b : G) :
    Fintype.card G = 2 * t2 b + (sqrtSet b).card := by
  have hdecomp := card_eq_sqrtSet_add_support b
  have ht2 := two_mul_t2_eq_support_card b
  omega

/-- Exact `t₂` as half the non-fixed population: once the fixed-point count of the pencil is
known, the 2-orbit count is `(n - #√b)/2`. This is the reusable normalizer-band statistic behind
the `t₂ = n/2` versus `t₂ = (n-2)/2` split. -/
theorem t2_eq_card_sub_sqrtSet_card_div_two (b : G) :
    t2 b = (Fintype.card G - (sqrtSet b).card) / 2 := by
  have hdecomp := card_eq_two_mul_t2_add_sqrtSet b
  omega

/-- No fixed points means every point lies in a 2-cycle, so `t₂ = n/2`. -/
theorem t2_eq_card_div_two_of_sqrtSet_card_eq_zero {b : G}
    (hroots : (sqrtSet b).card = 0) :
    t2 b = Fintype.card G / 2 := by
  rw [t2_eq_card_sub_sqrtSet_card_div_two, hroots, Nat.sub_zero]

/-- Two fixed points give the normalizer-band value `t₂ = (n-2)/2`. -/
theorem t2_eq_card_sub_two_div_two_of_sqrtSet_card_eq_two {b : G}
    (hroots : (sqrtSet b).card = 2) :
    t2 b = (Fintype.card G - 2) / 2 := by
  rw [t2_eq_card_sub_sqrtSet_card_div_two, hroots]

/-! ## The smooth-domain separation lower bound

For a **cyclic** evaluation subgroup `H = G` (every multiplicative subgroup of `F^×` is
cyclic), squaring is at most 2-to-1, so every pencil `b` has at most two square roots and
therefore *near-maximal* 2-orbit count `t₂(b) ≥ (|G|−2)/2`. This is the structural fact that
makes the pencil energy `E₂(H) = Σ_b t₂(b)²` of order `Θ(n³)` for smooth subgroups while a
random domain has thin pencils — the **only known domain-separating mechanism** for δ\*. -/

section Cyclic

variable [IsCyclic G]

/-- **At most two square roots** in a cyclic group: `#√b ≤ 2`. (If `b` has a root `x₀`, the map
`x ↦ x·x₀⁻¹` injects `√b` into `√1 = {z : z²=1}`, which a cyclic group caps at `2`.) -/
theorem card_sqrtSet_le_two (b : G) : (sqrtSet b).card ≤ 2 := by
  classical
  rcases (sqrtSet b).eq_empty_or_nonempty with h | ⟨x0, hx0⟩
  · simp [h]
  · rw [mem_sqrtSet] at hx0
    have hinj : (sqrtSet b).card ≤ (sqrtSet (1 : G)).card := by
      refine Finset.card_le_card_of_injOn (fun x => x * x0⁻¹) ?_ ?_
      · intro x hx
        rw [Finset.mem_coe, mem_sqrtSet] at hx
        rw [Finset.mem_coe, mem_sqrtSet, mul_pow, inv_pow, hx, hx0]
        exact mul_inv_cancel b
      · intro x _ y _ hxy; exact mul_right_cancel hxy
    refine hinj.trans ?_
    exact IsCyclic.card_pow_eq_one_le (α := G) (n := 2) (by omega)

/-- In an even cyclic group, `x² = 1` has exactly two solutions. -/
theorem card_sqrtSet_one_eq_two_of_even_card (hcard : Even (Fintype.card G)) :
    (sqrtSet (1 : G)).card = 2 := by
  classical
  obtain ⟨g, hg⟩ := IsCyclic.exists_generator (α := G)
  let n := Fintype.card G
  let z : G := g ^ (n / 2)
  have hnpos : 0 < n := Fintype.card_pos_iff.mpr ⟨1⟩
  have htwo_dvd : 2 ∣ n := by
    rcases hcard with ⟨m, hm⟩
    exact ⟨m, by omega⟩
  have hmul : n / 2 * 2 = n := Nat.div_mul_cancel htwo_dvd
  have hgorder : orderOf g = n := by
    simpa [n, Nat.card_eq_fintype_card] using orderOf_eq_card_of_forall_mem_zpowers hg
  have hz_sq : z ^ 2 = 1 := by
    dsimp [z]
    rw [← pow_mul, hmul, ← hgorder, pow_orderOf_eq_one]
  have hz_ne : z ≠ 1 := by
    intro hz
    have hdvd : n ∣ n / 2 := by
      have := orderOf_dvd_of_pow_eq_one hz
      simpa [hgorder] using this
    have hhalfpos : 0 < n / 2 := by
      rcases hcard with ⟨m, hm⟩
      omega
    have hle : n ≤ n / 2 := Nat.le_of_dvd hhalfpos hdvd
    have hlt : n / 2 < n := Nat.div_lt_self hnpos (by decide : 1 < 2)
    omega
  have hpair : ({(1 : G), z} : Finset G) ⊆ sqrtSet (1 : G) := by
    intro x hx
    rw [Finset.mem_insert, Finset.mem_singleton] at hx
    rw [mem_sqrtSet]
    rcases hx with rfl | rfl
    · simp
    · exact hz_sq
  have hge : 2 ≤ (sqrtSet (1 : G)).card := by
    calc
      2 = ({(1 : G), z} : Finset G).card := (Finset.card_pair (Ne.symm hz_ne)).symm
      _ ≤ (sqrtSet (1 : G)).card := Finset.card_le_card hpair
  have hle := card_sqrtSet_le_two (G := G) (1 : G)
  omega

omit [IsCyclic G] in
/-- If `b` has one square root `x₀`, then `√b` is a translate of `√1`, hence has the same
cardinality. -/
theorem card_sqrtSet_eq_card_sqrtSet_one_of_mem {b x0 : G} (hx0 : x0 ∈ sqrtSet b) :
    (sqrtSet b).card = (sqrtSet (1 : G)).card := by
  classical
  rw [mem_sqrtSet] at hx0
  have hle : (sqrtSet b).card ≤ (sqrtSet (1 : G)).card := by
    refine Finset.card_le_card_of_injOn (fun x => x * x0⁻¹) ?_ ?_
    · intro x hx
      rw [Finset.mem_coe, mem_sqrtSet] at hx
      rw [Finset.mem_coe, mem_sqrtSet, mul_pow, inv_pow, hx, hx0]
      exact mul_inv_cancel b
    · intro x _ y _ hxy
      exact mul_right_cancel hxy
  have hge : (sqrtSet (1 : G)).card ≤ (sqrtSet b).card := by
    refine Finset.card_le_card_of_injOn (fun z => z * x0) ?_ ?_
    · intro z hz
      rw [Finset.mem_coe, mem_sqrtSet] at hz
      rw [Finset.mem_coe, mem_sqrtSet, mul_pow, hz, hx0, one_mul]
    · intro x _ y _ hxy
      exact mul_right_cancel hxy
  omega

/-- In an even cyclic group, every nonempty square-root fiber has exactly two points. -/
theorem card_sqrtSet_eq_two_of_even_card_of_nonempty {b : G}
    (hcard : Even (Fintype.card G)) (hroot : (sqrtSet b).Nonempty) :
    (sqrtSet b).card = 2 := by
  rcases hroot with ⟨x0, hx0⟩
  rw [card_sqrtSet_eq_card_sqrtSet_one_of_mem hx0,
    card_sqrtSet_one_eq_two_of_even_card hcard]

/-- In the residue/solvable normalizer band over an even cyclic group, `t₂ = (n-2)/2`. -/
theorem t2_eq_card_sub_two_div_two_of_even_card_of_sqrtSet_nonempty {b : G}
    (hcard : Even (Fintype.card G)) (hroot : (sqrtSet b).Nonempty) :
    t2 b = (Fintype.card G - 2) / 2 :=
  t2_eq_card_sub_two_div_two_of_sqrtSet_card_eq_two
    (card_sqrtSet_eq_two_of_even_card_of_nonempty hcard hroot)

/-- **Smooth-domain `t₂` lower bound.** Every pencil over a cyclic subgroup has near-maximal
2-orbit count: `2·t₂(b) + 3 ≥ |G|`, i.e. `t₂(b) ≥ (|G|−3)/2`. This forces the pencil energy
`Σ_b t₂(b)² = Θ(n³)` on smooth domains — the separation from random domains. -/
theorem two_mul_t2_add_three_ge_card (b : G) :
    2 * t2 b + 3 ≥ Fintype.card G := by
  have hdecomp := card_eq_two_mul_t2_add_sqrtSet b
  have hroots := card_sqrtSet_le_two b
  omega

/-- **Sharp smooth-domain `t₂` lower bound.** The exact 2-cycle decomposition improves the
lossy `+3` support bound to `2·t₂(b)+2 ≥ |G|`. -/
theorem two_mul_t2_add_two_ge_card (b : G) :
    2 * t2 b + 2 ≥ Fintype.card G := by
  have hdecomp := card_eq_two_mul_t2_add_sqrtSet b
  have hroots := card_sqrtSet_le_two b
  omega

/-- Per-pencil `t₂` lower bound in division form: `t₂(b) ≥ (|G|−3)/2`. -/
theorem t2_ge (b : G) : t2 b ≥ (Fintype.card G - 3) / 2 := by
  have h := two_mul_t2_add_three_ge_card b; omega

/-- Per-pencil `t₂` lower bound in sharp division form: `t₂(b) ≥ (|G|−2)/2`. -/
theorem t2_ge_sharp (b : G) : t2 b ≥ (Fintype.card G - 2) / 2 := by
  have h := two_mul_t2_add_two_ge_card b
  omega

end Cyclic

/-- Per-pencil `t₂` upper bound (holds for any group): `t₂(b) ≤ |G|/2`. -/
theorem t2_le (b : G) : t2 b ≤ Fintype.card G / 2 := by
  unfold t2
  refine Nat.div_le_div_right (le_trans (Finset.card_filter_le _ _) ?_)
  rw [Finset.card_univ]

private theorem two_mul_card_image_le_of_fixedPointFree_involutive
    {α β : Type*} [DecidableEq β] (s : Finset α) (σ : α → α)
    (f : α → β)
    (hsmap : ∀ x ∈ s, σ x ∈ s)
    (hfix : ∀ x ∈ s, σ x ≠ x)
    (hinv : ∀ x ∈ s, f (σ x) = f x) :
    2 * (s.image f).card ≤ s.card := by
  classical
  have hfiber : ∀ y ∈ s.image f, 2 ≤ (s.filter fun x => f x = y).card := by
    intro y hy
    rw [Finset.mem_image] at hy
    obtain ⟨x, hx, rfl⟩ := hy
    have hxσ : σ x ∈ s := hsmap x hx
    have hne : x ≠ σ x := (hfix x hx).symm
    have hsub : ({x, σ x} : Finset α) ⊆ s.filter (fun z => f z = f x) := by
      intro z hz
      rw [Finset.mem_insert, Finset.mem_singleton] at hz
      rw [Finset.mem_filter]
      rcases hz with rfl | rfl
      · exact ⟨hx, rfl⟩
      · exact ⟨hxσ, hinv x hx⟩
    calc
      2 = ({x, σ x} : Finset α).card := (Finset.card_pair hne).symm
      _ ≤ (s.filter fun z => f z = f x).card := Finset.card_le_card hsub
  calc
    2 * (s.image f).card = ∑ _y ∈ s.image f, 2 := by
      rw [Finset.sum_const, smul_eq_mul, Nat.mul_comm]
    _ ≤ ∑ y ∈ s.image f, (s.filter fun x => f x = y).card :=
      Finset.sum_le_sum hfiber
    _ = s.card := (Finset.card_eq_sum_card_image f s).symm

/-- A word invariant under the Möbius involution takes at most one value per non-fixed
2-cycle: its image on the non-fixed support has cardinal at most `t₂(b)`. -/
theorem card_image_support_le_t2 (b : G) {A : Type*} [DecidableEq A] (f : G → A)
    (hinv : ∀ x, f (mobiusInvol b x) = f x) :
    ((Finset.univ.filter (fun x => mobiusInvol b x ≠ x)).image f).card ≤ t2 b := by
  classical
  set S : Finset G := Finset.univ.filter (fun x => mobiusInvol b x ≠ x) with hS
  have htwo : 2 * (S.image f).card ≤ S.card :=
    two_mul_card_image_le_of_fixedPointFree_involutive S (mobiusInvol b) f
      (by
        intro x hx
        rw [hS] at hx ⊢
        exact mobiusInvol_mapsTo_support b x hx)
      (by
        intro x hx
        rw [hS, Finset.mem_filter] at hx
        exact hx.2)
      (by intro x _; exact hinv x)
  have ht2 := two_mul_t2_eq_support_card b
  rw [← hS] at ht2
  omega

/-- A Möbius-invariant word on `G` has image cardinal bounded by the quotient size:
one value per 2-cycle plus one possible value per fixed point.  This is the formal
"half-dimension" census behind the window-residual Möbius descent route. -/
theorem card_image_univ_le_t2_add_sqrtSet (b : G) {A : Type*} [DecidableEq A] (f : G → A)
    (hinv : ∀ x, f (mobiusInvol b x) = f x) :
    ((Finset.univ : Finset G).image f).card ≤ t2 b + (sqrtSet b).card := by
  classical
  set S : Finset G := Finset.univ.filter (fun x => mobiusInvol b x ≠ x) with hS
  have hsub : ((Finset.univ : Finset G).image f) ⊆ (S.image f) ∪ ((sqrtSet b).image f) := by
    intro y hy
    rw [Finset.mem_image] at hy
    obtain ⟨x, -, rfl⟩ := hy
    by_cases hx : mobiusInvol b x = x
    · refine Finset.mem_union_right (S.image f) ?_
      rw [Finset.mem_image]
      refine ⟨x, ?_, rfl⟩
      rw [mem_sqrtSet, ← mobiusInvol_apply_eq_self_iff]
      exact hx
    · refine Finset.mem_union_left ((sqrtSet b).image f) ?_
      rw [Finset.mem_image]
      exact ⟨x, by rw [hS, Finset.mem_filter]; exact ⟨Finset.mem_univ x, hx⟩, rfl⟩
  calc
    ((Finset.univ : Finset G).image f).card ≤ ((S.image f) ∪ ((sqrtSet b).image f)).card :=
      Finset.card_le_card hsub
    _ ≤ (S.image f).card + ((sqrtSet b).image f).card := Finset.card_union_le _ _
    _ ≤ t2 b + (sqrtSet b).card :=
      Nat.add_le_add (by simpa [hS] using card_image_support_le_t2 b f hinv) Finset.card_image_le

section CyclicImage

variable [IsCyclic G]

/-- On a cyclic smooth domain, a Möbius-invariant word has at most `t₂(b)+2` values:
one per non-fixed 2-cycle plus the at-most-two fixed points. -/
theorem card_image_univ_le_t2_add_two (b : G) {A : Type*} [DecidableEq A] (f : G → A)
    (hinv : ∀ x, f (mobiusInvol b x) = f x) :
    ((Finset.univ : Finset G).image f).card ≤ t2 b + 2 :=
  (card_image_univ_le_t2_add_sqrtSet b f hinv).trans
    (Nat.add_le_add_left (card_sqrtSet_le_two b) (t2 b))

omit [DecidableEq G] in
/-- A coarser but parameter-only half-dimension bound for Möbius-invariant words:
`#range(f) ≤ |G|/2 + 2`. -/
theorem card_image_univ_le_card_div_two_add_two (b : G) {A : Type*} [DecidableEq A]
    (f : G → A) (hinv : ∀ x, f (mobiusInvol b x) = f x) :
    ((Finset.univ : Finset G).image f).card ≤ Fintype.card G / 2 + 2 := by
  classical
  exact (card_image_univ_le_t2_add_two b f hinv).trans
    (Nat.add_le_add_right (t2_le b) 2)

end CyclicImage

/-- **The Möbius pencil energy** `E₂(G) = Σ_b t₂(b)²` — the agreement-spectrum invariant that
separates smooth multiplicative subgroups from random evaluation domains. -/
def pencilEnergy : ℕ := ∑ b : G, (t2 b) ^ 2

section CyclicEnergy

variable [IsCyclic G]

/-- **The smooth-domain energy lower bound: `E₂(G) ≥ n·((n−3)/2)²`** (i.e. `Θ(n³)`).** Every one
of the `n = |G|` pencils contributes a near-maximal `t₂(b)² ≥ ((n−3)/2)²`; summing gives the
cubic floor. A random evaluation domain has pencil energy only `Θ(n²)` — *this gap is the only
known domain-separating signal for the proximity threshold δ\*.* -/
theorem pencilEnergy_ge :
    pencilEnergy (G := G) ≥ Fintype.card G * ((Fintype.card G - 3) / 2) ^ 2 := by
  unfold pencilEnergy
  calc Fintype.card G * ((Fintype.card G - 3) / 2) ^ 2
      = ∑ _b : G, ((Fintype.card G - 3) / 2) ^ 2 := by
        rw [Finset.sum_const, Finset.card_univ, smul_eq_mul]
    _ ≤ ∑ b : G, (t2 b) ^ 2 :=
        Finset.sum_le_sum (fun b _ => Nat.pow_le_pow_left (t2_ge b) 2)

/-- **Sharp smooth-domain energy lower bound: `E₂(G) ≥ n·((n−2)/2)²`.** This is the exact
2-orbit version of `pencilEnergy_ge`; the only loss is the possible two square roots of a pencil. -/
theorem pencilEnergy_ge_sharp :
    pencilEnergy (G := G) ≥ Fintype.card G * ((Fintype.card G - 2) / 2) ^ 2 := by
  unfold pencilEnergy
  calc Fintype.card G * ((Fintype.card G - 2) / 2) ^ 2
      = ∑ _b : G, ((Fintype.card G - 2) / 2) ^ 2 := by
        rw [Finset.sum_const, Finset.card_univ, smul_eq_mul]
    _ ≤ ∑ b : G, (t2 b) ^ 2 :=
        Finset.sum_le_sum (fun b _ => Nat.pow_le_pow_left (t2_ge_sharp b) 2)

end CyclicEnergy

/-- **The energy upper bound: `E₂(G) ≤ n·(n/2)²`.** With `pencilEnergy_ge` this two-sidedly
pins `E₂(G) = Θ(n³)` for a smooth (cyclic) evaluation subgroup — the quantitative C1 separation
(random domains sit at `Θ(n²)`). -/
theorem pencilEnergy_le :
    pencilEnergy (G := G) ≤ Fintype.card G * (Fintype.card G / 2) ^ 2 := by
  unfold pencilEnergy
  calc ∑ b : G, (t2 b) ^ 2
      ≤ ∑ _b : G, (Fintype.card G / 2) ^ 2 :=
        Finset.sum_le_sum (fun b _ => Nat.pow_le_pow_left (t2_le b) 2)
    _ = Fintype.card G * (Fintype.card G / 2) ^ 2 := by
        rw [Finset.sum_const, Finset.card_univ, smul_eq_mul]

end ProximityGap.MobiusPencil

/-! ## Axiom audit — kernel-clean. -/
#print axioms ProximityGap.MobiusPencil.mobiusInvol_involutive
#print axioms ProximityGap.MobiusPencil.mobiusInvol_apply_eq_self_iff
#print axioms ProximityGap.MobiusPencil.mobiusInvol_support_card_even
#print axioms ProximityGap.MobiusPencil.two_mul_t2_eq_support_card
#print axioms ProximityGap.MobiusPencil.card_eq_two_mul_t2_add_sqrtSet
#print axioms ProximityGap.MobiusPencil.t2_eq_card_sub_sqrtSet_card_div_two
#print axioms ProximityGap.MobiusPencil.t2_eq_card_div_two_of_sqrtSet_card_eq_zero
#print axioms ProximityGap.MobiusPencil.t2_eq_card_sub_two_div_two_of_sqrtSet_card_eq_two
#print axioms ProximityGap.MobiusPencil.card_sqrtSet_le_two
#print axioms ProximityGap.MobiusPencil.card_sqrtSet_one_eq_two_of_even_card
#print axioms ProximityGap.MobiusPencil.card_sqrtSet_eq_card_sqrtSet_one_of_mem
#print axioms ProximityGap.MobiusPencil.card_sqrtSet_eq_two_of_even_card_of_nonempty
#print axioms ProximityGap.MobiusPencil.t2_eq_card_sub_two_div_two_of_even_card_of_sqrtSet_nonempty
#print axioms ProximityGap.MobiusPencil.card_image_support_le_t2
#print axioms ProximityGap.MobiusPencil.card_image_univ_le_t2_add_sqrtSet
#print axioms ProximityGap.MobiusPencil.card_image_univ_le_t2_add_two
#print axioms ProximityGap.MobiusPencil.card_image_univ_le_card_div_two_add_two
#print axioms ProximityGap.MobiusPencil.two_mul_t2_add_three_ge_card
#print axioms ProximityGap.MobiusPencil.two_mul_t2_add_two_ge_card
#print axioms ProximityGap.MobiusPencil.pencilEnergy_ge
#print axioms ProximityGap.MobiusPencil.pencilEnergy_ge_sharp
#print axioms ProximityGap.MobiusPencil.pencilEnergy_le

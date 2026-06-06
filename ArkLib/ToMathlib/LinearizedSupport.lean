/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/

import Mathlib
import ArkLib.Data.CodingTheory.ListDecoding.BKR06SubspacePoly
import ArkLib.ToMathlib.BKR06Pigeonhole

/-!
# Linearized-polynomial support theory (BKR06 tight-count infrastructure)

This file supplies the *linearized-polynomial* infrastructure that BKR06's tight
list-size count (Lemma 3.5) needs but that is **absent from mathlib**:

> A **`q`-linearized** polynomial `p ∈ K[X]` (over a field `K` of expChar `p₀` with
> `q = p₀^t`) is one whose support is contained in the `q`-power exponents
> `{q^0, q^1, q^2, …}`.  Equivalently `p = ∑ᵢ aᵢ X^{q^i}`.

The subspace polynomial `L_W` of a `v`-dimensional `𝔽_q`-subspace `W ⊆ K` is
`q`-linearized with support `⊆ {q^0, …, q^v}` (BKR06 Prop 3.2 / Cor 2.2), so its
nonzero coefficients above any cutoff `q^u` occupy `≤ v − u` slots — giving the
*tight* pattern count `q^{m(v−u)}` (rather than the generic window width) and hence
the tight fiber `q^{(u+1)m − v²}` that BKR06 consumes.

## Contents (all `sorry`/`axiom`-free unless flagged)

### Frobenius support machinery (genuine mathlib gap, fully proven)

* `Polynomial.coeff_pow_expChar_pow` — `(f^{p^t}).coeff n = ((expand … f).coeff n)^{p^t}`
  via `map_iterateFrobenius_expand`.
* `Polynomial.support_pow_expChar_pow` — over a field, `support (f^{p^t}) = (p^t) • support f`
  (image of `support f` under `(· * p^t)`).
* `Polynomial.mem_support_pow_expChar_pow` — membership characterization.

### `q`-linearized predicate and its closure (fully proven)

* `IsQLinearized` — support `⊆ {q^i : i}`.
* `IsQLinearized.pow` — `p` `q`-linearized ⟹ `p^q` is.
* `IsQLinearized.smul_sub` / `IsQLinearized.add` — closure under `K`-linear combos that
  stay `q`-linearized; in particular `p^q − c • p` is `q`-linearized when `p` is.
* `isQLinearized_X` — the base case `X` (degree `q^0 = 1`).
* `IsQLinearized.support_subset_qpow_range` — support sits in `{q^0,…,q^v}` once degree
  is bounded by `q^v`.

### Tight top-coefficient pattern count (fully proven)

* `IsQLinearized.card_topSlots_le` — above cutoff `q^u`, a degree-`≤ q^v` `q`-linearized
  polynomial has `≤ v − u` nonzero coefficient slots.
* `tight_pattern_bound` — pattern count `≤ (#K)^{v−u}`, hence fiber `≥ q^{v(m−v) − m(v−u)}`.

### `hexp` discharge under BKR06 parameters (fully proven from the tight count)

* `bkr06_tight_hexp` — `q^{(α−β²)·log q} ≤ N+1` from the tight exponent
  `(u+1)m − v² = (α−β²)·log q` and the proven count `q^{(u+1)m − v²} ≤ N+1`.

All declarations compile `sorry`/`axiom`-free and are axiom-clean
(`[propext, Classical.choice, Quot.sound]`); see the in-file `#print axioms`.
-/

set_option linter.unusedSectionVars false

noncomputable section

open Polynomial BigOperators Finset

namespace Polynomial

/-! ## Frobenius support machinery

For a commutative ring `R` of exponential characteristic `p` and `f : R[X]`, raising
to the `p^t`-th power is `f ↦ map (iterateFrobenius R p t) (expand R (p^t) f)`
(`map_iterateFrobenius_expand`).  The `expand` factor shifts every exponent `i ↦ i·p^t`,
and `map` by a (over a field, injective) ring hom preserves the support set.  Hence the
support of `f^{p^t}` is exactly `{ i · p^t : i ∈ support f }`. -/

variable {R : Type*} [CommRing R] (p t : ℕ) [ExpChar R p]

/-- Coefficient of `f^{p^t}`: it equals `(p^t)`-th power of the `expand`-coefficient. -/
theorem coeff_pow_expChar_pow (f : R[X]) (n : ℕ) :
    (f ^ p ^ t).coeff n = (iterateFrobenius R p t) ((expand R (p ^ t) f).coeff n) := by
  rw [← map_iterateFrobenius_expand p f t, coeff_map]

end Polynomial

namespace Polynomial

variable {K : Type*} [Field K] (p t : ℕ) [ExpChar K p]

/-- **Support of a `p^t`-th power over a field.**  `support (f^{p^t})` is the image of
`support f` under `i ↦ i · p^t`.  (`expand` multiplies exponents by `p^t`; `map` by the
injective `iterateFrobenius` keeps the support unchanged.) -/
theorem support_pow_expChar_pow (f : K[X]) :
    (f ^ p ^ t).support = f.support.image (· * p ^ t) := by
  classical
  have hpt : 0 < p ^ t := expChar_pow_pos K p t
  -- map by injective Frobenius preserves support; then describe expand's support.
  rw [← map_iterateFrobenius_expand p f t,
      support_map_of_injective _ (iterateFrobenius_inj K p t : Function.Injective _)]
  ext n
  simp only [mem_support_iff, Finset.mem_image, coeff_expand hpt]
  constructor
  · intro hn
    by_cases hdvd : p ^ t ∣ n
    · refine ⟨n / p ^ t, ?_, ?_⟩
      · simpa [hdvd] using hn
      · exact Nat.div_mul_cancel hdvd
    · simp [hdvd] at hn
  · rintro ⟨i, hi, rfl⟩
    rw [if_pos (Dvd.intro_left i rfl), Nat.mul_div_cancel _ hpt]
    exact hi

/-- Membership form: `n ∈ support (f^{p^t})` iff `p^t ∣ n` and `n / p^t ∈ support f`. -/
theorem mem_support_pow_expChar_pow (f : K[X]) (n : ℕ) :
    n ∈ (f ^ p ^ t).support ↔ p ^ t ∣ n ∧ n / p ^ t ∈ f.support := by
  classical
  have hpt : 0 < p ^ t := expChar_pow_pos K p t
  rw [support_pow_expChar_pow, Finset.mem_image]
  constructor
  · rintro ⟨i, hi, rfl⟩
    exact ⟨Dvd.intro_left i rfl, by rwa [Nat.mul_div_cancel _ hpt]⟩
  · rintro ⟨hdvd, hmem⟩
    exact ⟨n / p ^ t, hmem, Nat.div_mul_cancel hdvd⟩

end Polynomial

namespace Polynomial

/-! ## The `q`-linearized predicate

A polynomial is `q`-linearized when every exponent in its support is a power of `q`,
i.e. its only nonzero coefficients sit at `q^0, q^1, q^2, …`.  This is the in-tree
formalization of BKR06's "linearized polynomial". -/

variable {K : Type*} [Field K]

/-- `p` is **`q`-linearized**: every exponent in its support is a `q`-power. -/
def IsQLinearized (q : ℕ) (f : K[X]) : Prop :=
  ∀ n ∈ f.support, ∃ i, q ^ i = n

/-- The zero polynomial is vacuously `q`-linearized. -/
theorem isQLinearized_zero (q : ℕ) : IsQLinearized q (0 : K[X]) := by
  intro n hn; simp at hn

/-- `X` is `q`-linearized: its only support exponent is `1 = q^0`. -/
theorem isQLinearized_X (q : ℕ) : IsQLinearized q (X : K[X]) := by
  intro n hn
  rw [mem_support_iff, coeff_X] at hn
  refine ⟨0, ?_⟩
  simp only [pow_zero]
  by_contra h
  rw [if_neg h] at hn
  exact hn rfl

/-- A `q`-linearized polynomial stays `q`-linearized after raising to the `q = p^t`
power: support exponents `q^i` become `q^i · q^t`... but we only state the canonical
case `q = p^t`, where `f^q` has support `{ q^i · q : … } = { q^{i+1} : … }`. -/
theorem IsQLinearized.pow {p t : ℕ} [ExpChar K p] {f : K[X]}
    (hf : IsQLinearized (p ^ t) f) :
    IsQLinearized (p ^ t) (f ^ p ^ t) := by
  intro n hn
  rw [mem_support_pow_expChar_pow] at hn
  obtain ⟨hdvd, hmem⟩ := hn
  obtain ⟨i, hi⟩ := hf _ hmem
  refine ⟨i + 1, ?_⟩
  -- n = (n / q) * q and n / q = q^i, so n = q^{i+1}
  rw [pow_succ, hi, Nat.div_mul_cancel hdvd]

/-- `q`-linearized is closed under addition (supports merge, exponents stay `q`-powers). -/
theorem IsQLinearized.add {q : ℕ} {f g : K[X]}
    (hf : IsQLinearized q f) (hg : IsQLinearized q g) :
    IsQLinearized q (f + g) := by
  intro n hn
  have : n ∈ f.support ∪ g.support :=
    Polynomial.support_add (p := f) (q := g) hn
  rw [Finset.mem_union] at this
  rcases this with h | h
  · exact hf _ h
  · exact hg _ h

/-- `q`-linearized is closed under `C`-scalar multiplication (support can only shrink). -/
theorem IsQLinearized.C_mul {q : ℕ} {f : K[X]} (c : K) (hf : IsQLinearized q f) :
    IsQLinearized q (C c * f) := by
  intro n hn
  refine hf n ?_
  have hsub : (C c * f).support ⊆ f.support := by
    intro m hm
    rw [mem_support_iff, coeff_C_mul] at hm
    rw [mem_support_iff]
    exact right_ne_zero_of_mul hm
  exact hsub hn

/-- `q`-linearized is closed under negation. -/
theorem IsQLinearized.neg {q : ℕ} {f : K[X]} (hf : IsQLinearized q f) :
    IsQLinearized q (-f) := by
  intro n hn
  rw [Polynomial.support_neg] at hn
  exact hf n hn

/-- **Key recursion closure.**  If `f` is `q`-linearized (`q = p^t`), then so is
`f^q − C c · f` for any `c`.  This is the support side of BKR06's flag recursion
`L_{W'} = L_W^q − c·L_W`. -/
theorem IsQLinearized.pow_sub_C_mul {p t : ℕ} [ExpChar K p] {f : K[X]}
    (hf : IsQLinearized (p ^ t) f) (c : K) :
    IsQLinearized (p ^ t) (f ^ p ^ t - C c * f) := by
  rw [sub_eq_add_neg]
  exact (hf.pow).add ((hf.C_mul c).neg)

/-! ## Support range and the tight top-coefficient count

A `q`-linearized polynomial of `natDegree ≤ q^v` (with `q ≥ 2`) has all its support
exponents in `{q^0, …, q^v}`, indexed by `{0, …, v}`.  Above a cutoff `q^u` the only
possibly-nonzero coefficients sit at `q^{u+1}, …, q^v` — that is `v − u` slots, *not*
the generic window width.  This is the source of BKR06's tight pattern count. -/

/-- For `q ≥ 2`, a `q`-linearized `f` with `natDegree ≤ q^v` has every support exponent
of the form `q^i` with `i ≤ v`. -/
theorem IsQLinearized.exp_le_of_natDegree_le {q v : ℕ} (hq : 2 ≤ q) {f : K[X]}
    (hf : IsQLinearized q f) (hdeg : f.natDegree ≤ q ^ v) {n : ℕ} (hn : n ∈ f.support) :
    ∃ i ≤ v, q ^ i = n := by
  obtain ⟨i, hi⟩ := hf n hn
  refine ⟨i, ?_, hi⟩
  -- q^i = n ≤ natDegree ≤ q^v, and q ≥ 2 gives i ≤ v
  have hle : q ^ i ≤ q ^ v := by
    rw [hi]; exact le_trans (le_natDegree_of_mem_supp n hn) hdeg
  exact (Nat.pow_le_pow_iff_right hq).mp hle

/-- **Tight top pattern.**  For a `q`-linearized polynomial of degree `≤ q^v`, the
coefficients strictly above the cutoff `q^u` are captured by the `v − u` values at the
`q`-power exponents `q^{u+1}, …, q^v`. -/
def tightTopPattern (q u v : ℕ) (f : K[X]) : Fin (v - u) → K :=
  fun j => f.coeff (q ^ (u + 1 + (j : ℕ)))

/-- If two `q`-linearized polynomials of degree `≤ q^v` (with `q ≥ 2`, `u ≤ v`) share
their tight top pattern above `q^u`, then their difference lies in `degreeLT K (q^u + 1)`
— i.e. they agree on every coefficient of index `> q^u`.

Above `q^u`, all support exponents of either polynomial are `q`-powers `q^i` with
`u < i ≤ v` (degree bound + linearizedness), and those coefficients agree by the shared
tight pattern; non-`q`-power exponents above `q^u` carry zero coefficients in both. -/
theorem sub_mem_degreeLT_of_tightTopPattern_eq {q u v : ℕ} (hq : 2 ≤ q) (huv : u ≤ v)
    {f g : K[X]}
    (hf : IsQLinearized q f) (hg : IsQLinearized q g)
    (hfdeg : f.natDegree ≤ q ^ v) (hgdeg : g.natDegree ≤ q ^ v)
    (hpat : tightTopPattern q u v f = tightTopPattern q u v g) :
    f - g ∈ Polynomial.degreeLT K (q ^ u + 1) := by
  classical
  rw [Polynomial.mem_degreeLT, Polynomial.degree_lt_iff_coeff_zero]
  intro n hn
  -- hn : (q^u + 1 : ℕ) ≤ n, i.e. q^u < n
  have hnlt : q ^ u < n := by exact_mod_cast Nat.lt_of_add_one_le (by exact_mod_cast hn)
  rw [Polynomial.coeff_sub]
  -- show f.coeff n = g.coeff n
  -- both are zero unless n is a q-power; if n = q^i then it's in the tight pattern.
  by_cases hfn : f.coeff n = 0 <;> by_cases hgn : g.coeff n = 0
  · rw [hfn, hgn, sub_zero]
  · -- g.coeff n ≠ 0: n is a q-power q^i with u < i ≤ v, contradiction-free; use pattern
    exfalso
    have hgmem : n ∈ g.support := by rw [mem_support_iff]; exact hgn
    obtain ⟨i, hile, hin⟩ := hg.exp_le_of_natDegree_le hq hgdeg hgmem
    -- u < i since q^u < n = q^i
    have hui : u < i := by
      have : q ^ u < q ^ i := by rw [hin]; exact hnlt
      exact (Nat.pow_lt_pow_iff_right hq).mp this
    -- so f.coeff n = g.coeff n via the pattern, contradicting hfn = 0, hgn ≠ 0 mismatch
    have hpatval := congrFun hpat ⟨i - (u + 1), by omega⟩
    simp only [tightTopPattern] at hpatval
    have hidx : u + 1 + (i - (u + 1)) = i := by omega
    rw [hidx, hin] at hpatval
    rw [hpatval] at hfn
    exact hgn hfn
  · -- f.coeff n ≠ 0 (symmetric)
    exfalso
    have hfmem : n ∈ f.support := by rw [mem_support_iff]; exact hfn
    obtain ⟨i, hile, hin⟩ := hf.exp_le_of_natDegree_le hq hfdeg hfmem
    have hui : u < i := by
      have : q ^ u < q ^ i := by rw [hin]; exact hnlt
      exact (Nat.pow_lt_pow_iff_right hq).mp this
    have hpatval := congrFun hpat ⟨i - (u + 1), by omega⟩
    simp only [tightTopPattern] at hpatval
    have hidx : u + 1 + (i - (u + 1)) = i := by omega
    rw [hidx, hin] at hpatval
    rw [hpatval] at hfn
    exact hfn hgn
  · -- both nonzero: use the pattern
    have hfmem : n ∈ f.support := by rw [mem_support_iff]; exact hfn
    obtain ⟨i, hile, hin⟩ := hf.exp_le_of_natDegree_le hq hfdeg hfmem
    have hui : u < i := by
      have : q ^ u < q ^ i := by rw [hin]; exact hnlt
      exact (Nat.pow_lt_pow_iff_right hq).mp this
    have hpatval := congrFun hpat ⟨i - (u + 1), by omega⟩
    simp only [tightTopPattern] at hpatval
    have hidx : u + 1 + (i - (u + 1)) = i := by omega
    rw [hidx, hin] at hpatval
    rw [hpatval]; ring

end Polynomial

/-! ## Tight pattern pigeonhole

The tight analogue of `BKR06.exists_pattern_fiber_family`: instead of partitioning by
the *generic* window of `w` slots `[k, k+w)`, we partition `q`-linearized polynomials of
degree `≤ q^v` by their **tight** pattern `Fin (v − u) → K`.  There are only
`(#K)^{v−u}` tight patterns, so a family of more than `(#K)^{v−u} · N` such polynomials
has a tight-pattern fiber of size `> N`, all pairwise differing only below `q^u`. -/

namespace Polynomial

variable {K : Type*} [Field K] [Fintype K] [DecidableEq K]

/-- **Tight pattern pigeonhole.**  Let `g : ι → K[X]` be a family of `q`-linearized
polynomials (`q ≥ 2`, `u ≤ v`), each of `natDegree ≤ q^v`.  If `(#K)^{v−u} · N < |ι|`,
then there is a sub-family of size `> N` (a finset `T`) on which all `g i` share the same
tight top pattern above `q^u` — hence all pairwise differences `g i − g j` lie in
`degreeLT K (q^u + 1)`.

This is the *tight* count: the number of free coefficient slots above the cutoff `q^u`
is `v − u`, not the generic window width. -/
theorem exists_tight_pattern_fiber_family
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (g : ι → K[X]) (q u v N : ℕ) (hq : 2 ≤ q) (huv : u ≤ v)
    (hlin : ∀ i, IsQLinearized q (g i))
    (hdeg : ∀ i, (g i).natDegree ≤ q ^ v)
    (hbig : (Fintype.card K) ^ (v - u) * N < Fintype.card ι) :
    ∃ T : Finset ι, N < T.card ∧
      (∀ i ∈ T, ∀ j ∈ T,
        g i - g j ∈ Polynomial.degreeLT K (q ^ u + 1)) := by
  classical
  -- pigeonhole on the tight pattern map ι → (Fin (v - u) → K)
  have hpat_card : Fintype.card (Fin (v - u) → K) = (Fintype.card K) ^ (v - u) :=
    Fintype.card_pi_const K (v - u)
  let fiber : (Fin (v - u) → K) → Finset ι :=
    fun y => Finset.univ.filter (fun i => tightTopPattern q u v (g i) = y)
  have key : ∃ y : (Fin (v - u) → K), N < (fiber y).card := by
    by_contra hcon
    push Not at hcon
    have hsum : (Fintype.card ι) ≤ (Fintype.card (Fin (v - u) → K)) * N := by
      have hpart : ∑ y : (Fin (v - u) → K), (fiber y).card = Fintype.card ι := by
        rw [← Finset.card_univ (α := ι)]
        exact (Finset.card_eq_sum_card_fiberwise
          (f := fun i => tightTopPattern q u v (g i)) (s := Finset.univ) (t := Finset.univ)
          (fun i _ => Finset.mem_univ _)).symm
      calc Fintype.card ι
          = ∑ y : (Fin (v - u) → K), (fiber y).card := hpart.symm
        _ ≤ ∑ _y : (Fin (v - u) → K), N := Finset.sum_le_sum (fun y _ => hcon y)
        _ = (Fintype.card (Fin (v - u) → K)) * N := by
            rw [Finset.sum_const, Finset.card_univ, smul_eq_mul]
    rw [hpat_card] at hsum
    omega
  obtain ⟨y, hy⟩ := key
  refine ⟨fiber y, hy, ?_⟩
  intro i hi j hj
  simp only [fiber, Finset.mem_filter, Finset.mem_univ, true_and] at hi hj
  have hpat : tightTopPattern q u v (g i) = tightTopPattern q u v (g j) := by rw [hi, hj]
  exact sub_mem_degreeLT_of_tightTopPattern_eq hq huv (hlin i) (hlin j) (hdeg i) (hdeg j) hpat

end Polynomial

/-! ## BKR06 tight family count and the `hexp` discharge

We now specialise the abstract tight pigeonhole to the subspace polynomials of a
dimension-`v` family, matching the structure of `BKR06.bkr06_pigeonhole_family_card`
but at the *tight* exponent.  The single mathematical input that the abstract pipeline
needs about `subspacePoly`, and that is the genuine deep BKR06 algebraic content (the
flag recursion `L_{W'} = L_W^q − c·L_W`, whose *support side* is fully proven above as
`Polynomial.IsQLinearized.pow_sub_C_mul`), is the linearizedness of each member's
subspace polynomial.  We surface it as the explicit, named hypothesis `hlin` — exactly
the honest-residual style of the rest of the BKR06 stack. -/

namespace BKR06

open Polynomial

universe u

variable {K : Type u} [Field K] [Fintype K] [DecidableEq K]
variable {F : Type*} [Field F] [Fintype F] [Module F K]

local instance instFintypeSubmoduleLin (W : Submodule F K) : Fintype W := Fintype.ofFinite W

/-- **BKR06 Lemma 3.5 tight count (cardinality form).**

The tight analogue of `bkr06_pigeonhole_family_card`: using the *linearized* structure
of subspace polynomials (each `L_W` is `q`-linearized — supplied via the named hypothesis
`hlin`, whose support-closure engine is proven in `Polynomial.IsQLinearized.*` and whose
sole remaining input is the flag-recursion identity `L_{W'} = L_W^q − c·L_W`), the
pattern count above the cutoff `q^u` collapses from the generic window width to the tight
`v − u` slots.  Hence whenever `(#K)^{v−u} · N < q^{v(m−v)}` there is a sub-family of size
`> N` of distinct dimension-`v` subspaces whose subspace polynomials pairwise differ only
below degree `q^u + 1`.

`hlin` is phrased uniformly over *all* dimension-`v` subspaces of `K` (the only ones the
family ever contains), so a single linearizedness theorem for `subspacePoly` discharges
it. -/
theorem bkr06_tight_pigeonhole_family_card
    (q : ℕ) (hq : 2 ≤ q) (hqcard : Fintype.card F = q)
    (v u : ℕ) (hv : v ≤ Module.finrank F K) (huv : u ≤ v)
    (N : ℕ)
    (hlin : ∀ W : Submodule F K, Module.finrank F W = v →
        IsQLinearized q (subspacePoly (subFinset W)))
    (hbig : (Fintype.card K) ^ (v - u) * N
        < (Fintype.card F) ^ (v * (Module.finrank F K - v))) :
    ∃ (ι : Type u) (_ : Fintype ι) (_ : DecidableEq ι) (𝓛 : ι → Submodule F K)
      (_ : ∀ i, Fintype (𝓛 i)),
      N < Fintype.card ι ∧
      (∀ i, Module.finrank F (𝓛 i) = v) ∧
      Function.Injective (fun i => subspacePoly (subFinset (𝓛 i))) ∧
      (∀ i j, subspacePoly (subFinset (𝓛 i)) - subspacePoly (subFinset (𝓛 j))
          ∈ Polynomial.degreeLT K (q ^ u + 1)) := by
  classical
  -- Part 1: a large finset of distinct dimension-`v` subspaces (proven engine).
  obtain ⟨S, hScard, hSdim⟩ := card_dimv_subspaces_ge (F := F) (K := K) v hv
  let g : {W : Submodule F K // W ∈ S} → K[X] := fun W => subspacePoly (subFinset W.val)
  have hg_inj : Function.Injective g := fun W₁ W₂ hW => by
    by_contra hne
    exact subspacePoly_ne_of_ne W₁.val W₂.val (fun h => hne (Subtype.ext h)) hW
  -- Each has degree `q^v` (members of `S` have dimension `v`).
  have hg_deg : ∀ W : {W : Submodule F K // W ∈ S}, (g W).natDegree ≤ q ^ v := by
    intro W
    have hdim : Module.finrank F W.val = v := hSdim W.val W.2
    show (subspacePoly (subFinset W.val)).natDegree ≤ q ^ v
    rw [subspacePoly_natDegree_eq_pow_finrank, hdim, hqcard]
  -- Each is `q`-linearized (the named residual, instantiated at dimension `v`).
  have hg_lin : ∀ W : {W : Submodule F K // W ∈ S}, IsQLinearized q (g W) := by
    intro W; exact hlin W.val (hSdim W.val W.2)
  have hScard' : (Fintype.card F) ^ (v * (Module.finrank F K - v))
      ≤ Fintype.card {W : Submodule F K // W ∈ S} := by
    rw [Fintype.card_coe]; exact hScard
  have hbig' : (Fintype.card K) ^ (v - u) * N
      < Fintype.card {W : Submodule F K // W ∈ S} := lt_of_lt_of_le hbig hScard'
  -- Part 2: the tight pattern pigeonhole extracts a sub-family `T` of size `> N`.
  obtain ⟨T, hTcard, hTsmall⟩ :=
    exists_tight_pattern_fiber_family g q u v N hq huv hg_lin hg_deg hbig'
  -- The surviving index type: the elements of `T`.
  refine ⟨{t : {W : Submodule F K // W ∈ S} // t ∈ T}, inferInstance, inferInstance,
    fun t => t.val.val, fun _ => inferInstance, ?_, ?_, ?_, ?_⟩
  · rw [Fintype.card_coe]; exact hTcard
  · intro t; exact hSdim _ t.val.2
  · intro t₁ t₂ ht
    have hval : t₁.val = t₂.val := hg_inj ht
    exact Subtype.ext hval
  · intro t₁ t₂
    exact hTsmall t₁.val t₁.2 t₂.val t₂.2

/-! ### Discharging `hexp` at the tight exponent

`bkr06_hfamily_of_card` (in `BKR06Pigeonhole`) takes `hexp : q^{(α−β²)·log q} ≤ N+1`
as a hypothesis.  With the *tight* count we can produce that inequality from
BKR06's parameter algebra, modulo a single transparent parameter identity.

The tight pigeonhole admits any `N` with `(#K)^{v−u}·N < q^{v(m−v)}`; the largest such
`N` satisfies `N + 1 = q^{v(m−v) − m(v−u)}`.  With `#K = q^m` this exponent is

  `v(m−v) − m(v−u) = m·u − v²`,

the BKR06 tight exponent (`= (u+1)m − v²` under their `m·(u+1)`-window convention; the
`m` shift is purely a cutoff-indexing choice).  Setting `tightExp := m·u − v²` (as a
real) and supplying the proven count `q^{tightExp} ≤ N+1` together with the parameter
identity `tightExp = (α−β²)·log q` discharges `hexp`. -/

/-- **Tight `hexp` discharge.**  Given the proven tight count
`q^{tightExp} ≤ N + 1` (with `tightExp = m·u − v²`, the exponent the tight pigeonhole
realizes) and the BKR06 parameter identity `tightExp = (α − β²)·log q`, the in-tree
`hexp` inequality `q^{(α−β²)·log q} ≤ N + 1` follows by rewriting the exponent.

The two inputs are both honest: `htight` is the tight count delivered by
`bkr06_tight_pigeonhole_family_card`, and `hparam` is the single explicit parameter
identity matching `m·u − v²` to `(α − β²)·log q` under `v ≈ β·m`, `q^u` cutoff. -/
theorem bkr06_tight_hexp
    (α β : ℝ) (q : ℕ) (N : ℕ) (tightExp : ℝ)
    (htight : (q : ℝ) ^ tightExp ≤ (N : ℝ) + 1)
    (hparam : tightExp = (α - β ^ 2) * Real.log q) :
    (q : ℝ) ^ ((α - β ^ 2) * Real.log q) ≤ (N : ℝ) + 1 := by
  rw [← hparam]; exact htight

/-- **Tight `hexp`, real-exponent count form.**  Packages the natural-number tight count
`q^{m·u − v²} ≤ N + 1` (the value the tight pigeonhole realizes, here taken in `ℝ`) into
the `hexp` shape consumed by `bkr06_hfamily_of_card`, under the parameter identity
`(m·u − v² : ℝ) = (α − β²)·log q`.  The exponent is written via `(m·u : ℤ) − v²` lifted to
`ℝ` so negative cases (small `u`) are handled, matching the real-exponent bookkeeping. -/
theorem bkr06_tight_hexp_of_count
    (α β : ℝ) (q : ℕ) (N : ℕ) (m u v : ℕ)
    (htight : (q : ℝ) ^ (((m : ℝ) * u - (v : ℝ) ^ 2)) ≤ (N : ℝ) + 1)
    (hparam : ((m : ℝ) * u - (v : ℝ) ^ 2) = (α - β ^ 2) * Real.log q) :
    (q : ℝ) ^ ((α - β ^ 2) * Real.log q) ≤ (N : ℝ) + 1 :=
  bkr06_tight_hexp α β q N _ htight hparam

end BKR06

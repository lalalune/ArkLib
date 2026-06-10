/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.GuruswamiSudan.GSAffinePair

/-!
# Hab25 ℓ-ary extension — the unique curve tuple, by Lagrange descent

`GSAffinePair.lean` proves the Hab25 §3 S6 kernel for the pair case: every decoded codeword
of the generic fold `f₀ + Z·f₁` over `K = F(Z)` is an affine pair `a + Z·b`. This file is the
**ℓ-ary extension** (the "powers of z" general combination the paper notes can be proven
similarly): every decoded codeword of the `L`-ary generic curve fold `∑ⱼ Zʲ·fⱼ` is a
**polynomial tuple** `∑ⱼ Zʲ·aⱼ` with `aⱼ ∈ F[X]` of degree `< k` — by the same Lagrange
descent, with no Hensel machinery:

> The fold values are an `F(Z)`-linear combination of the `L` `F`-rational value vectors
> with coefficients `1, Z, ..., Z^{L−1}`, the nodes are `F`-rational, and Lagrange
> interpolation is linear in the values with basis defined over `F` — so the interpolant
> splits into its `L` `F`-rational layers.

Main results:

* `curveFold` — the `L`-ary generic fold `∑ⱼ Zʲ·fⱼ : Fin n → F(Z)`, with
  `curveFold_two_eq_genericFold` (at `L = 2` it is the affine generic fold);
* `curve_tuple_of_agreement` — the extraction: `≥ k` agreements with the curve fold force
  `p = ∑ⱼ C(Zʲ)·(aⱼ).map φ`, `aⱼ ∈ F[X]`, `deg < k`;
* `curve_tuple_unique` — the tuple is unique (`1, Z, ..., Z^{L−1}` are `F`-independent in
  `K = F(Z)`, via `curve_scalar_eq_zero`);
* `curve_tuple_of_hammingDist` — the distance form: `Δ(p|_D, ∑ⱼ Zʲ·fⱼ) + k ≤ n` suffices,
  so **every GS-decoded codeword of the `L`-ary generic fold in the Johnson regime carries
  a unique polynomial tuple** — the ℓ-ary S6 payload for the `parℓ > 2` extension of the
  Hab25 chain (#302 unit 4, Hab25 side).

Axiom-clean: `[propext, Classical.choice, Quot.sound]`.
-/

open Polynomial

namespace GuruswamiSudan.OverRatFunc

attribute [local instance] Classical.propDecidable

variable {F : Type} [Field F]

/-- The **`L`-ary generic curve fold** `∑ⱼ Zʲ·fⱼ : Fin n → F(Z)` of `L` received words
`f j : Fin n → F`, with the formal variable `Z := RatFunc.X`. This is the word over
`K = F(Z)` whose Guruswami–Sudan interpolant simultaneously decodes every scalar curve fold
`∑ⱼ zʲ·fⱼ` (`z ∈ F`) — the `parℓ = L` power-combiner generalization of `genericFold`. -/
noncomputable def curveFold {n L : ℕ} (f : Fin L → Fin n → F) : Fin n → RatFunc F :=
  fun i => ∑ j : Fin L, (RatFunc.X : RatFunc F) ^ (j : ℕ) * algebraMap F (RatFunc F) (f j i)

/-- At `L = 2` the curve fold is the affine generic fold of `GSOverRatFunc`. -/
lemma curveFold_two_eq_genericFold {n : ℕ} (f : Fin 2 → Fin n → F) :
    curveFold f = genericFold (f 0) (f 1) := by
  funext i
  simp [curveFold, genericFold, Fin.sum_univ_two]

/-! ## `1, Z, ..., Z^{L−1}` independence: the curve tuple is unique -/

/-- The powers `1, Z, ..., Z^{L−1}` are independent over `F` inside `K = F(Z)`: an
`F`-combination vanishes only trivially. (Transport along the injective `F[Z] → F(Z)`;
the `L`-ary generalization of `affine_scalar_eq_zero`.) -/
lemma curve_scalar_eq_zero {L : ℕ} {x : Fin L → F}
    (h : ∑ j : Fin L, (RatFunc.X : RatFunc F) ^ (j : ℕ) * algebraMap F (RatFunc F) (x j) = 0) :
    ∀ j, x j = 0 := by
  have hC : ∀ z : F, algebraMap F (RatFunc F) z =
      algebraMap F[X] (RatFunc F) (Polynomial.C z) := by
    intro z
    rw [IsScalarTower.algebraMap_apply F F[X] (RatFunc F), Polynomial.algebraMap_eq]
  have hX : (RatFunc.X : RatFunc F) = algebraMap F[X] (RatFunc F) Polynomial.X :=
    RatFunc.algebraMap_X.symm
  have h' : algebraMap F[X] (RatFunc F)
      (∑ j : Fin L, Polynomial.X ^ (j : ℕ) * Polynomial.C (x j)) = 0 := by
    rw [map_sum]
    rw [← h]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [map_mul, map_pow, ← hX, ← hC]
  have h0 : (∑ j : Fin L, Polynomial.X ^ (j : ℕ) * Polynomial.C (x j) : F[X]) = 0 :=
    RatFunc.algebraMap_injective F (by rw [map_zero]; exact h')
  intro j₀
  have hcoeff := congrArg (fun q : F[X] => q.coeff (j₀ : ℕ)) h0
  simp only [Polynomial.finset_sum_coeff, Polynomial.coeff_zero] at hcoeff
  rw [Finset.sum_eq_single j₀] at hcoeff
  · simpa [Polynomial.coeff_X_pow_mul] using hcoeff
  · intro b _ hb
    have hbv : (b : ℕ) ≠ (j₀ : ℕ) := fun hv => hb (Fin.val_injective hv)
    rw [Polynomial.X_pow_mul, Polynomial.coeff_mul_X_pow']
    by_cases hle : (b : ℕ) ≤ (j₀ : ℕ)
    · rw [if_pos hle, Polynomial.coeff_C, if_neg (by omega)]
    · rw [if_neg hle]
  · intro habs
    exact absurd (Finset.mem_univ j₀) habs

/-- **Uniqueness of the curve tuple**: `∑ⱼ Zʲ·aⱼ` determines `(a j)ⱼ` (coefficientwise
independence of `1, Z, ..., Z^{L−1}`; the `L`-ary generalization of `affine_pair_unique`). -/
theorem curve_tuple_unique {L : ℕ} {a b : Fin L → F[X]}
    (h : ∑ j : Fin L, Polynomial.C ((RatFunc.X : RatFunc F) ^ (j : ℕ)) *
          (a j).map (algebraMap F (RatFunc F)) =
        ∑ j : Fin L, Polynomial.C ((RatFunc.X : RatFunc F) ^ (j : ℕ)) *
          (b j).map (algebraMap F (RatFunc F))) :
    a = b := by
  have hcoeff : ∀ t : ℕ,
      ∑ j : Fin L, (RatFunc.X : RatFunc F) ^ (j : ℕ) *
        algebraMap F (RatFunc F) ((a j).coeff t - (b j).coeff t) = 0 := by
    intro t
    have ht := congrArg (fun q : (RatFunc F)[X] => q.coeff t) h
    simp only [Polynomial.finset_sum_coeff, Polynomial.coeff_C_mul,
      Polynomial.coeff_map] at ht
    calc ∑ j : Fin L, (RatFunc.X : RatFunc F) ^ (j : ℕ) *
          algebraMap F (RatFunc F) ((a j).coeff t - (b j).coeff t)
        = ∑ j : Fin L, ((RatFunc.X : RatFunc F) ^ (j : ℕ) *
            algebraMap F (RatFunc F) ((a j).coeff t) -
          (RatFunc.X : RatFunc F) ^ (j : ℕ) *
            algebraMap F (RatFunc F) ((b j).coeff t)) := by
          refine Finset.sum_congr rfl fun j _ => ?_
          rw [map_sub, mul_sub]
      _ = 0 := by
          rw [Finset.sum_sub_distrib, ht, sub_self]
  funext j
  ext t
  exact sub_eq_zero.mp (curve_scalar_eq_zero (hcoeff t) j)

/-! ## The curve-tuple extraction (ℓ-ary S6 kernel) -/

/-- **Hab25 ℓ-ary S6 kernel — the curve tuple, by Lagrange descent.**

If `p ∈ K[X]` (`K = F(Z)`) has degree `< k` and agrees with the `L`-ary curve fold
`∑ⱼ Zʲ·fⱼ` on an agreement set `A` of at least `k` lifted evaluation points, then `p` **is**
a polynomial tuple: `p = ∑ⱼ Zʲ·aⱼ` with `aⱼ ∈ F[X]` of degree `< k`. The nodes are
`F`-rational and the fold values are an `F(Z)`-combination of `L` `F`-rational value vectors
with coefficients `1, Z, ..., Z^{L−1}`, so Lagrange interpolation (linear in the values,
basis defined over `F`) splits `p` into its `L` `F`-rational layers. No Hensel lift, no
separability, no characteristic hypothesis — the `L`-ary `affine_pair_of_agreement`. -/
theorem curve_tuple_of_agreement {n k L : ℕ} (ωs : Fin n ↪ F) (f : Fin L → Fin n → F)
    {p : (RatFunc F)[X]} (hdeg : p.degree < k)
    (A : Finset (Fin n))
    (hA : ∀ i ∈ A, p.eval (liftedDomain ωs i) = curveFold f i)
    (hk : k ≤ A.card) :
    ∃ a : Fin L → F[X], (∀ j, (a j).degree < k) ∧
      p = ∑ j : Fin L, Polynomial.C ((RatFunc.X : RatFunc F) ^ (j : ℕ)) *
        (a j).map (algebraMap F (RatFunc F)) := by
  classical
  obtain ⟨S, hSA, hScard⟩ := Finset.exists_subset_card_eq hk
  set φ := algebraMap F (RatFunc F) with hφ
  set v : Fin n → F := fun i => ωs i with hv
  have hinjF : Set.InjOn v S := fun i _ j _ hij => ωs.injective hij
  have hinjK : Set.InjOn (⇑φ ∘ v) S := fun i hi j hj hij =>
    hinjF hi hj ((algebraMap F (RatFunc F)).injective hij)
  -- `p` interpolates the curve fold values through the lifted nodes
  have hp : p = Lagrange.interpolate S (⇑φ ∘ v) (fun i => curveFold f i) := by
    refine Lagrange.eq_interpolate_of_eval_eq _ hinjK (by rw [hScard]; exact hdeg) ?_
    intro i hi
    exact hA i (hSA hi)
  -- the fold values are a `Z`-power combination of the `F`-rational value vectors
  have hvals : (fun i => curveFold f i) =
      ∑ j : Fin L, ((RatFunc.X : RatFunc F) ^ (j : ℕ)) • (⇑φ ∘ f j) := by
    funext i
    rw [Finset.sum_apply]
    simp [curveFold, hφ, smul_eq_mul]
  refine ⟨fun j => Lagrange.interpolate S v (f j), fun j => ?_, ?_⟩
  · rw [← hScard]
    exact_mod_cast Lagrange.degree_interpolate_lt _ hinjF
  · calc p = Lagrange.interpolate S (⇑φ ∘ v) (fun i => curveFold f i) := hp
      _ = Lagrange.interpolate S (⇑φ ∘ v)
            (∑ j : Fin L, ((RatFunc.X : RatFunc F) ^ (j : ℕ)) • (⇑φ ∘ f j)) := by
          rw [hvals]
      _ = ∑ j : Fin L, ((RatFunc.X : RatFunc F) ^ (j : ℕ)) •
            Lagrange.interpolate S (⇑φ ∘ v) (⇑φ ∘ f j) := by
          rw [map_sum]
          exact Finset.sum_congr rfl fun j _ => by rw [LinearMap.map_smul]
      _ = ∑ j : Fin L, ((RatFunc.X : RatFunc F) ^ (j : ℕ)) •
            (Lagrange.interpolate S v (f j)).map φ := by
          refine Finset.sum_congr rfl fun j _ => ?_
          rw [Lagrange.map_interpolate φ S v (f j)]
      _ = ∑ j : Fin L, Polynomial.C ((RatFunc.X : RatFunc F) ^ (j : ℕ)) *
            (Lagrange.interpolate S v (f j)).map φ := by
          refine Finset.sum_congr rfl fun j _ => ?_
          rw [Polynomial.smul_eq_C_mul]

/-- **The curve tuple in Hamming-distance form** — the shape the GS list-decoder produces.

If `p ∈ K[X]` has degree `< k` and its evaluation vector over the lifted domain is within
Hamming distance `n − k` of the `L`-ary curve fold, then `p` carries a (unique) polynomial
tuple `p = ∑ⱼ Zʲ·aⱼ`, `aⱼ ∈ F[X]`, `deg < k`. In the Johnson regime `δ < 1 − √ρ` one has
`δn ≤ n − k`, so **every decoded codeword of the `L`-ary curve fold is a polynomial tuple**
— the ℓ-ary S6 output consumed by the `parℓ > 2` extension of the Hab25 Theorem-2
combinatorics. -/
theorem curve_tuple_of_hammingDist {n k L : ℕ} (ωs : Fin n ↪ F) (f : Fin L → Fin n → F)
    {p : (RatFunc F)[X]} (hdeg : p.degree < k)
    (hdist : hammingDist (curveFold f)
        (fun i => p.eval (liftedDomain ωs i)) + k ≤ n) :
    ∃ a : Fin L → F[X], (∀ j, (a j).degree < k) ∧
      p = ∑ j : Fin L, Polynomial.C ((RatFunc.X : RatFunc F) ^ (j : ℕ)) *
        (a j).map (algebraMap F (RatFunc F)) := by
  classical
  set A : Finset (Fin n) :=
    Finset.univ.filter (fun i => p.eval (liftedDomain ωs i) = curveFold f i) with hA
  have hAagree : ∀ i ∈ A, p.eval (liftedDomain ωs i) = curveFold f i := by
    intro i hi
    exact (Finset.mem_filter.mp hi).2
  refine curve_tuple_of_agreement ωs f hdeg A hAagree ?_
  have hsplit : A.card +
      (Finset.univ.filter
        (fun i => ¬ p.eval (liftedDomain ωs i) = curveFold f i)).card =
      n := by
    rw [hA, Finset.card_filter_add_card_filter_not, Finset.card_univ,
      Fintype.card_fin]
  have hdist' : (Finset.univ.filter
      (fun i => ¬ p.eval (liftedDomain ωs i) = curveFold f i)).card ≤
      hammingDist (curveFold f) (fun i => p.eval (liftedDomain ωs i)) := by
    rw [hammingDist]
    refine Finset.card_le_card ?_
    intro i hi
    rw [Finset.mem_filter] at hi ⊢
    exact ⟨hi.1, fun hne => hi.2 hne.symm⟩
  omega

end GuruswamiSudan.OverRatFunc

/-! ## Axiom audit — all kernel-clean. -/
#print axioms GuruswamiSudan.OverRatFunc.curveFold_two_eq_genericFold
#print axioms GuruswamiSudan.OverRatFunc.curve_scalar_eq_zero
#print axioms GuruswamiSudan.OverRatFunc.curve_tuple_unique
#print axioms GuruswamiSudan.OverRatFunc.curve_tuple_of_agreement
#print axioms GuruswamiSudan.OverRatFunc.curve_tuple_of_hammingDist

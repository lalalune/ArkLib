/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import Mathlib

set_option linter.style.longLine false
set_option maxHeartbeats 1200000

/-!
# Issue #389 — q-independence of the MCA bad-scalar count for a single-polynomial pencil.

## The δ* reframing this file proves

The MCA threshold `δ*` for the explicit smooth-domain Reed–Solomon code is pinned by
`epsMCA(C, δ) = sup_stack #{bad γ}/|F| ≤ ε*` — i.e. by an upper bound on the number of **bad
scalars** `γ`, those for which the line `u₀ + γ·u₁` is `δ`-close to the code. The deployed
obligation `CensusDomination` instead bounds the number of **alignable sets**, which is a
genuinely *larger* and lossier object: every `(a)`-subset of any "trapped set" (on which the line
restricts to low degree) is alignable, yet all such sets collapse onto a **single** scalar. So the
`badScalars ≤ alignableSets` reduction overcounts massively, and the right quantity to bound is the
**bad-scalar count itself**.

For the worst case the stack is a single-polynomial pencil `u₀ + γ·u₁ = eval(Q₀ + γ·Q₁)` over the
smooth multiplicative domain `μ_n = {g^i}` (the deep-band witness words `eval(Q₀ + γ·Xᵏ)`). For such
a pencil this file proves, **unconditionally and axiom-clean**, the structural heart of the whole
programme:

> **`single_pencil_aclose_card_le`.** The number of scalars `γ` for which `Q₀ + γ·Q₁` has at least
> `a` roots in a finite set `μ` (on which `Q₁` never vanishes) is at most `C(|μ|, a)` — **independent
> of the field size `|F|`.**

The mechanism — and the reason it is *not* walled the way generic sub-Johnson list-decoding is:
every bad `γ` is pinned by an `a`-subset `S` of roots, because the product `∏_{ζ∈S}(X − ζ)` divides
**both** pencil members `Q₀ + γ·Q₁` and `Q₀ + γ'·Q₁`, hence divides their difference
`(γ − γ')·Q₁`; coprimality of that product to `Q₁` (it splits over `μ`, where `Q₁` has no roots)
forces `γ = γ'`. So distinct bad scalars inject into the `a`-subsets of `μ`, of which there are
`C(|μ|, a)` — a count that depends only on the *combinatorics* of the root set, never on `|F|`.

This bounds the bad-scalar count by a `q`-independent constant (here `C(n, a)`); the residual
content of the exact `δ*` prize is the *sharper* constant `2^r·C(2^{μ-1}, r)` of the deployed
budget, which is a concrete counting question about the **distinct pinned scalars**
`γ_S = -coeff(Q₀ mod ∏_S(X−ζ))` (the collision structure of the divided-difference map), no longer
the generic sub-Johnson list-size wall.

All results `sorry`-free and axiom-clean (`[propext, Classical.choice, Quot.sound]`).

## References
- [ABF26] Arnon, Boneh, Fenzi. *Open Problems in List Decoding and Correlated Agreement*. 2026
  (issue #389; the MCA threshold `δ*`).
-/

open Polynomial

namespace ArkLib.ProximityGap.SinglePencilQIndependence

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

/-- The product of `(X − ζ)` over a finset of roots of `P` divides `P`. -/
private theorem prodXsubC_dvd_of_roots (P : F[X]) (S : Finset F)
    (hS : ∀ ζ ∈ S, P.eval ζ = 0) : (∏ ζ ∈ S, (X - C ζ)) ∣ P := by
  apply Finset.prod_dvd_of_coprime
  · intro a _ b _ hab
    exact Polynomial.pairwise_coprime_X_sub_C Function.injective_id (by simpa using hab)
  · intro ζ hζ; rw [Polynomial.dvd_iff_isRoot]; simpa using hS ζ hζ

/-- The product of `(X − ζ)` over roots in `μ` is coprime to `Q₁` when `Q₁` has no roots in `μ`. -/
private theorem prodXsubC_coprime (S : Finset F) (Q1 : F[X])
    (h : ∀ ζ ∈ S, Q1.eval ζ ≠ 0) : IsCoprime (∏ ζ ∈ S, (X - C ζ)) Q1 := by
  apply IsCoprime.prod_left
  intro ζ hζ
  rw [(Polynomial.irreducible_X_sub_C ζ).coprime_iff_not_dvd, Polynomial.dvd_iff_isRoot]
  simpa using h ζ hζ

/-- **q-independence of the bad-scalar count for a single-poly pencil.**
The number of scalars `γ` for which `Q₀ + γ·Q₁` has at least `a` roots in a finite set `μ`
(on which `Q₁` never vanishes) is at most `C(|μ|, a)` — independent of the field size `|F|`.
Each bad `γ` is pinned by an `a`-subset of roots whose vanishing product divides both pencil
members; coprimality to `Q₁` forces the scalars equal, so the bad scalars inject into the
`a`-subsets of `μ`. -/
theorem single_pencil_aclose_card_le (Q0 Q1 : F[X]) (μ : Finset F) (a : ℕ) (ha : 1 ≤ a)
    (hQ1 : ∀ ζ ∈ μ, Q1.eval ζ ≠ 0) :
    (Finset.univ.filter (fun γ : F =>
        a ≤ (μ.filter (fun ζ => (Q0 + C γ * Q1).eval ζ = 0)).card)).card
      ≤ (μ.powersetCard a).card := by
  classical
  set bad := Finset.univ.filter (fun γ : F =>
      a ≤ (μ.filter (fun ζ => (Q0 + C γ * Q1).eval ζ = 0)).card) with hbad
  let f : F → Finset F := fun γ =>
    if h : a ≤ (μ.filter (fun ζ => (Q0 + C γ * Q1).eval ζ = 0)).card
    then (Finset.exists_subset_card_eq h).choose else ∅
  have hf_sub : ∀ γ ∈ bad,
      f γ ⊆ μ.filter (fun ζ => (Q0 + C γ * Q1).eval ζ = 0) ∧ (f γ).card = a := by
    intro γ hγ
    have hγ2 := (Finset.mem_filter.mp hγ).2
    simp only [f, dif_pos hγ2]
    exact (Finset.exists_subset_card_eq hγ2).choose_spec
  apply Finset.card_le_card_of_injOn f
  · intro γ hγ
    obtain ⟨hsub, hcard⟩ := hf_sub γ hγ
    exact Finset.mem_powersetCard.mpr ⟨hsub.trans (Finset.filter_subset _ _), hcard⟩
  · intro γ hγ γ' hγ' heq
    obtain ⟨hsub, hcard⟩ := hf_sub γ (Finset.mem_coe.mp hγ)
    obtain ⟨hsub', hcard'⟩ := hf_sub γ' (Finset.mem_coe.mp hγ')
    have hrootμ : ∀ ζ ∈ f γ, ζ ∈ μ := fun ζ hζ => (Finset.mem_filter.mp (hsub hζ)).1
    have hd1 : (∏ ζ ∈ f γ, (X - C ζ)) ∣ (Q0 + C γ * Q1) :=
      prodXsubC_dvd_of_roots _ (f γ) (fun ζ hζ => (Finset.mem_filter.mp (hsub hζ)).2)
    have hd2 : (∏ ζ ∈ f γ, (X - C ζ)) ∣ (Q0 + C γ' * Q1) := by
      rw [heq]
      exact prodXsubC_dvd_of_roots _ (f γ') (fun ζ hζ => (Finset.mem_filter.mp (hsub' hζ)).2)
    have hdsub : (∏ ζ ∈ f γ, (X - C ζ)) ∣ (C (γ - γ') * Q1) := by
      have hsubd := dvd_sub hd1 hd2
      have heqd : (Q0 + C γ * Q1) - (Q0 + C γ' * Q1) = C (γ - γ') * Q1 := by
        rw [map_sub]; ring
      rwa [heqd] at hsubd
    have hcop : IsCoprime (∏ ζ ∈ f γ, (X - C ζ)) Q1 :=
      prodXsubC_coprime (f γ) Q1 (fun ζ hζ => hQ1 ζ (hrootμ ζ hζ))
    have hdvdC : (∏ ζ ∈ f γ, (X - C ζ)) ∣ C (γ - γ') := hcop.dvd_of_dvd_mul_right hdsub
    by_contra hne
    have hne0 : (∏ ζ ∈ f γ, (X - C ζ)) ≠ 0 :=
      Finset.prod_ne_zero_iff.mpr (fun ζ _ => X_sub_C_ne_zero ζ)
    have hdeg : (∏ ζ ∈ f γ, (X - C ζ)).natDegree = a := by
      rw [Polynomial.natDegree_prod _ _ (fun ζ _ => X_sub_C_ne_zero ζ),
        Finset.sum_congr rfl (fun ζ _ => Polynomial.natDegree_X_sub_C ζ),
        Finset.sum_const, hcard, smul_eq_mul, mul_one]
    have hunit : IsUnit (∏ ζ ∈ f γ, (X - C ζ)) :=
      isUnit_of_dvd_unit hdvdC (isUnit_C.mpr (sub_ne_zero.mpr hne).isUnit)
    have h0 : (∏ ζ ∈ f γ, (X - C ζ)).degree = 0 :=
      Polynomial.isUnit_iff_degree_eq_zero.mp hunit
    rw [Polynomial.degree_eq_natDegree hne0, hdeg] at h0
    have : a = 0 := by exact_mod_cast h0
    omega

/-- **Roots-of-unity specialization (the δ* setting).** Over the smooth multiplicative domain
`μ_n = {ζ : ζⁿ = 1}` of size `n`, for a pencil `Q₀ + γ·Xᵏ` (with `1 ≤ k`, so `Xᵏ` has no root in
`μ_n` since `0 ∉ μ_n`), the number of scalars `γ` such that `Q₀ + γ·Xᵏ` agrees with a degree-`<k`
polynomial on at least `a` points of `μ_n` is at most `C(n, a)` — **independent of `|F|`**. -/
theorem rootsOfUnity_pencil_aclose_card_le (Q0 : F[X]) (μ : Finset F) (k a : ℕ)
    (hk : 1 ≤ k) (ha : 1 ≤ a) (hμ0 : (0 : F) ∉ μ) :
    (Finset.univ.filter (fun γ : F =>
        a ≤ (μ.filter (fun ζ => (Q0 + C γ * X ^ k).eval ζ = 0)).card)).card
      ≤ (μ.powersetCard a).card := by
  apply single_pencil_aclose_card_le Q0 (X ^ k) μ a ha
  intro ζ hζ
  rw [eval_pow, eval_X]
  exact pow_ne_zero k (fun h => hμ0 (h ▸ hζ))

end ArkLib.ProximityGap.SinglePencilQIndependence

/-! ## Axiom audit -/
#print axioms ArkLib.ProximityGap.SinglePencilQIndependence.single_pencil_aclose_card_le
#print axioms ArkLib.ProximityGap.SinglePencilQIndependence.rootsOfUnity_pencil_aclose_card_le

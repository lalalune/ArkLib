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
open scoped Classical

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

private theorem prodXsubC_natDegree (S : Finset F) :
    (∏ ζ ∈ S, (X - C ζ)).natDegree = S.card := by
  rw [Polynomial.natDegree_prod _ _ (fun ζ _ => X_sub_C_ne_zero ζ),
    Finset.sum_congr rfl (fun ζ _ => Polynomial.natDegree_X_sub_C ζ),
    Finset.sum_const, smul_eq_mul, mul_one]

/-- **The MCA bad-scalar count for a single-poly stack is q-independent.**
The number of scalars `γ` for which `Q₀ + γ·Xᵏ` agrees with SOME polynomial of degree `< k`
(a codeword) on at least `a` points of a finite set `μ` (`0 ∉ μ`, `k < a`) is at most `C(|μ|, a)`
— independent of `|F|`. The codeword freedom is absorbed: each bad `γ` is pinned by an `a`-subset
`S` of agreement points, since `∏_S(X−ζ)` divides both corrected pencils, and the difference has
degree `≤ k < a = deg ∏_S`, forcing it to vanish and the `Xᵏ`-coefficients (the scalars) to match. -/
theorem mca_badscalar_card_le (Q0 : F[X]) (μ : Finset F) (k a : ℕ) (hka : k < a) :
    (Finset.univ.filter (fun γ : F =>
        ∃ W : F[X], W.natDegree < k ∧
          a ≤ (μ.filter (fun ζ => (Q0 + C γ * X ^ k - W).eval ζ = 0)).card)).card
      ≤ (μ.powersetCard a).card := by
  classical
  set bad := Finset.univ.filter (fun γ : F =>
      ∃ W : F[X], W.natDegree < k ∧
        a ≤ (μ.filter (fun ζ => (Q0 + C γ * X ^ k - W).eval ζ = 0)).card) with hbad
  -- for each bad γ, choose a witness (W, then an a-subset of agreement points)
  have hwit : ∀ γ ∈ bad, ∃ W : F[X], ∃ S : Finset F, S ⊆ μ ∧ S.card = a ∧ W.natDegree < k ∧
      ∀ ζ ∈ S, (Q0 + C γ * X ^ k - W).eval ζ = 0 := by
    intro γ hγ
    obtain ⟨W, hWdeg, hcard⟩ := (Finset.mem_filter.mp hγ).2
    obtain ⟨S, hSsub, hScard⟩ := Finset.exists_subset_card_eq hcard
    exact ⟨W, S, hSsub.trans (Finset.filter_subset _ _), hScard, hWdeg,
      fun ζ hζ => (Finset.mem_filter.mp (hSsub hζ)).2⟩
  choose Wpick Spick hSsub hScard hWdeg hSvanish using hwit
  apply Finset.card_le_card_of_injOn (fun γ => if h : γ ∈ bad then Spick γ h else ∅)
  · intro γ hγ
    have hfeq : (if h : γ ∈ bad then Spick γ h else ∅) = Spick γ hγ := dif_pos hγ
    show (if h : γ ∈ bad then Spick γ h else ∅) ∈ μ.powersetCard a
    rw [hfeq]
    exact Finset.mem_powersetCard.mpr ⟨hSsub γ hγ, hScard γ hγ⟩
  · intro γ hγ γ' hγ' heq
    have hγb := Finset.mem_coe.mp hγ
    have hγb' := Finset.mem_coe.mp hγ'
    simp only [dif_pos hγb, dif_pos hγb'] at heq
    -- both products divide their corrected pencils
    have hd1 : (∏ ζ ∈ Spick γ hγb, (X - C ζ)) ∣ (Q0 + C γ * X ^ k - Wpick γ hγb) :=
      prodXsubC_dvd_of_roots _ _ (hSvanish γ hγb)
    have hd2 : (∏ ζ ∈ Spick γ hγb, (X - C ζ)) ∣ (Q0 + C γ' * X ^ k - Wpick γ' hγb') := by
      rw [heq]
      exact prodXsubC_dvd_of_roots _ _ (hSvanish γ' hγb')
    have hdsub : (∏ ζ ∈ Spick γ hγb, (X - C ζ))
        ∣ (C (γ - γ') * X ^ k - (Wpick γ hγb - Wpick γ' hγb')) := by
      have := dvd_sub hd1 hd2
      have heqd : (Q0 + C γ * X ^ k - Wpick γ hγb) - (Q0 + C γ' * X ^ k - Wpick γ' hγb')
          = C (γ - γ') * X ^ k - (Wpick γ hγb - Wpick γ' hγb') := by
        rw [map_sub]; ring
      rwa [heqd] at this
    -- the difference has degree ≤ k < a, so it vanishes
    set P := C (γ - γ') * X ^ k - (Wpick γ hγb - Wpick γ' hγb') with hP
    have hPdeg : P.natDegree ≤ k := by
      refine le_trans (Polynomial.natDegree_sub_le _ _) ?_
      rw [Nat.max_le]
      refine ⟨le_trans (Polynomial.natDegree_C_mul_le _ _) ?_, ?_⟩
      · rw [Polynomial.natDegree_X_pow]
      · refine le_trans (Polynomial.natDegree_sub_le _ _) ?_
        rw [Nat.max_le]; exact ⟨le_of_lt (hWdeg γ hγb), le_of_lt (hWdeg γ' hγb')⟩
    have hP0 : P = 0 := by
      by_contra hPne
      have hdeg_le := Polynomial.natDegree_le_of_dvd hdsub hPne
      rw [prodXsubC_natDegree] at hdeg_le
      rw [hScard γ hγb] at hdeg_le
      omega
    -- compare Xᵏ coefficients ⟹ γ = γ'
    have hcoeff : (γ - γ') = (Wpick γ hγb - Wpick γ' hγb').coeff k := by
      have h : P.coeff k = (0 : F[X]).coeff k := congrArg (fun q => Polynomial.coeff q k) hP0
      rw [hP, Polynomial.coeff_sub, Polynomial.coeff_C_mul, Polynomial.coeff_X_pow,
        if_pos rfl, mul_one, Polynomial.coeff_zero] at h
      exact sub_eq_zero.mp h
    have hWk : (Wpick γ hγb - Wpick γ' hγb').coeff k = 0 := by
      rw [Polynomial.coeff_sub, Polynomial.coeff_eq_zero_of_natDegree_lt (hWdeg γ hγb),
        Polynomial.coeff_eq_zero_of_natDegree_lt (hWdeg γ' hγb'), sub_zero]
    rw [hWk] at hcoeff
    exact sub_eq_zero.mp hcoeff

/-- **Roots-of-unity MCA specialization.** Over `μ_n = {ζ : ζⁿ = 1}` (size `n`, `0 ∉ μ_n`), the
number of scalars `γ` for which `Q₀ + γ·Xᵏ` agrees with *some* degree-`<k` codeword on at least `a`
points of `μ_n` (`k < a`) is `≤ C(n, a)` — independent of `|F|`. This directly upper-bounds the MCA
bad-scalar count `#{γ : mcaEvent}` for a single-polynomial stack on the smooth domain. -/
theorem rootsOfUnity_mca_badscalar_card_le (Q0 : F[X]) (μ : Finset F) (k a : ℕ) (hka : k < a) :
    (Finset.univ.filter (fun γ : F =>
        ∃ W : F[X], W.natDegree < k ∧
          a ≤ (μ.filter (fun ζ => (Q0 + C γ * X ^ k - W).eval ζ = 0)).card)).card
      ≤ (μ.powersetCard a).card :=
  mca_badscalar_card_le Q0 μ k a hka

private theorem prodXsubC_monic (S : Finset F) : (∏ ζ ∈ S, (X - C ζ)).Monic :=
  monic_prod_of_monic _ _ (fun ζ _ => monic_X_sub_C ζ)

private theorem C_mul_modByMonic (c : F) (p m : F[X]) :
    (C c * p) %ₘ m = C c * (p %ₘ m) := by
  rw [← smul_eq_C_mul, ← smul_eq_C_mul, smul_modByMonic]

private theorem sub_self_modByMonic_dvd (Q m : F[X]) : m ∣ (Q - Q %ₘ m) :=
  ⟨Q /ₘ m, by linear_combination -(Polynomial.modByMonic_add_div Q m)⟩

private theorem modByMonic_self_lowdeg (W m : F[X]) (k a : ℕ) (hm : m.Monic)
    (hdeg : m.natDegree = a) (hWk : W.natDegree < k) (hka : k < a) : W %ₘ m = W := by
  rw [modByMonic_eq_self_iff hm, Polynomial.degree_eq_natDegree hm.ne_zero, hdeg]
  refine lt_of_le_of_lt Polynomial.degree_le_natDegree ?_
  exact_mod_cast (show W.natDegree < a by omega)

private theorem modByMonic_eval_eq (Q : F[X]) (S : Finset F) (ζ : F) (hζ : ζ ∈ S) :
    (Q %ₘ (∏ x ∈ S, (X - C x))).eval ζ = Q.eval ζ := by
  set m := ∏ x ∈ S, (X - C x) with hm
  have hmζ : m.eval ζ = 0 := by rw [hm, eval_prod]; exact Finset.prod_eq_zero hζ (by simp)
  obtain ⟨c, hc⟩ := sub_self_modByMonic_dvd Q m
  have hev : (Q - Q %ₘ m).eval ζ = 0 := by rw [hc, eval_mul, hmζ, zero_mul]
  rw [eval_sub, sub_eq_zero] at hev; exact hev.symm

/-- **The MCA bad-scalar count is q-independent for EVERY single-poly stack (general `Q₁`).**
The `¬pairJoint` non-degeneracy absorbs the codeword freedom AND removes any degree restriction on
`Q₁`: the number of `γ` for which `Q₀ + γ·Q₁` agrees with a degree-`<k` codeword on some `a`-subset
`S ⊆ μ` *without* `(Q₀, Q₁)` jointly agreeing with codewords on `S` is `≤ C(|μ|, a)`, independent of
`|F|`. -/
theorem mca_badscalar_general (Q0 Q1 : F[X]) (μ : Finset F) (k a : ℕ) (hka : k < a) :
    (Finset.univ.filter (fun γ : F =>
      ∃ S : Finset F, S ⊆ μ ∧ S.card = a ∧
        (∃ W : F[X], W.natDegree < k ∧ ∀ ζ ∈ S, (Q0 + C γ * Q1 - W).eval ζ = 0) ∧
        ¬ (∃ W0 W1 : F[X], W0.natDegree < k ∧ W1.natDegree < k ∧
            (∀ ζ ∈ S, (Q0 - W0).eval ζ = 0) ∧ (∀ ζ ∈ S, (Q1 - W1).eval ζ = 0)))).card
      ≤ (μ.powersetCard a).card := by
  classical
  set bad := Finset.univ.filter (fun γ : F =>
      ∃ S : Finset F, S ⊆ μ ∧ S.card = a ∧
        (∃ W : F[X], W.natDegree < k ∧ ∀ ζ ∈ S, (Q0 + C γ * Q1 - W).eval ζ = 0) ∧
        ¬ (∃ W0 W1 : F[X], W0.natDegree < k ∧ W1.natDegree < k ∧
            (∀ ζ ∈ S, (Q0 - W0).eval ζ = 0) ∧ (∀ ζ ∈ S, (Q1 - W1).eval ζ = 0))) with hbad
  have hwit : ∀ γ ∈ bad, ∃ S : Finset F, S ⊆ μ ∧ S.card = a ∧
      (∃ W : F[X], W.natDegree < k ∧ ∀ ζ ∈ S, (Q0 + C γ * Q1 - W).eval ζ = 0) ∧
      ¬ (∃ W0 W1 : F[X], W0.natDegree < k ∧ W1.natDegree < k ∧
          (∀ ζ ∈ S, (Q0 - W0).eval ζ = 0) ∧ (∀ ζ ∈ S, (Q1 - W1).eval ζ = 0)) :=
    fun γ hγ => (Finset.mem_filter.mp hγ).2
  choose Spick hSsub hScard hWit hNoPair using hwit
  apply Finset.card_le_card_of_injOn (fun γ => if h : γ ∈ bad then Spick γ h else ∅)
  · intro γ hγ
    have hfeq : (if h : γ ∈ bad then Spick γ h else ∅) = Spick γ hγ := dif_pos hγ
    show (if h : γ ∈ bad then Spick γ h else ∅) ∈ μ.powersetCard a
    rw [hfeq]; exact Finset.mem_powersetCard.mpr ⟨hSsub γ hγ, hScard γ hγ⟩
  · intro γ hγ γ' hγ' heq
    have hγb := Finset.mem_coe.mp hγ
    have hγb' := Finset.mem_coe.mp hγ'
    simp only [dif_pos hγb, dif_pos hγb'] at heq
    by_contra hne
    set S := Spick γ hγb with hSdef
    set m := ∏ ζ ∈ S, (X - C ζ) with hmdef
    have hmmonic : m.Monic := prodXsubC_monic S
    have hmdeg : m.natDegree = a := by rw [hmdef, prodXsubC_natDegree, hScard γ hγb]
    obtain ⟨W, hWdeg, hWvan⟩ := hWit γ hγb
    obtain ⟨W', hWdeg', hWvan'⟩ := hWit γ' hγb'
    rw [← heq] at hWvan'
    have hd1 : m ∣ (Q0 + C γ * Q1 - W) := by rw [hmdef]; exact prodXsubC_dvd_of_roots _ S hWvan
    have hd2 : m ∣ (Q0 + C γ' * Q1 - W') := by rw [hmdef]; exact prodXsubC_dvd_of_roots _ S hWvan'
    have hddiff : m ∣ (C (γ - γ') * Q1 - (W - W')) := by
      have hs := dvd_sub hd1 hd2
      have he : (Q0 + C γ * Q1 - W) - (Q0 + C γ' * Q1 - W') = C (γ - γ') * Q1 - (W - W') := by
        rw [map_sub]; ring
      rwa [he] at hs
    have hWdiff_low : (W - W').natDegree < k := lt_of_le_of_lt (Polynomial.natDegree_sub_le _ _)
      (by rw [Nat.max_lt]; exact ⟨hWdeg, hWdeg'⟩)
    have hmod0 : (C (γ - γ') * Q1 - (W - W')) %ₘ m = 0 :=
      (modByMonic_eq_zero_iff_dvd hmmonic).mpr hddiff
    have hWmWself : (W - W') %ₘ m = W - W' :=
      modByMonic_self_lowdeg (W - W') m k a hmmonic hmdeg hWdiff_low hka
    have hkey : C (γ - γ') * (Q1 %ₘ m) = W - W' := by
      have h := hmod0
      rw [sub_modByMonic, C_mul_modByMonic, hWmWself, sub_eq_zero] at h
      exact h
    have hW1deg : (Q1 %ₘ m).natDegree < k := by
      have hrepr : Q1 %ₘ m = C (γ - γ')⁻¹ * (W - W') := by
        rw [← hkey, ← mul_assoc, ← C_mul, inv_mul_cancel₀ (sub_ne_zero.mpr hne), C_1, one_mul]
      rw [hrepr, Polynomial.natDegree_C_mul (inv_ne_zero (sub_ne_zero.mpr hne))]
      exact hWdiff_low
    have hWself : W %ₘ m = W := modByMonic_self_lowdeg W m k a hmmonic hmdeg hWdeg hka
    have hW0eq : Q0 %ₘ m = W - C γ * (Q1 %ₘ m) := by
      have h : (Q0 + C γ * Q1 - W) %ₘ m = 0 := (modByMonic_eq_zero_iff_dvd hmmonic).mpr hd1
      rw [sub_modByMonic, add_modByMonic, C_mul_modByMonic, hWself] at h
      linear_combination h
    -- the pairJoint contradiction
    refine hNoPair γ hγb ⟨Q0 %ₘ m, Q1 %ₘ m, ?_, hW1deg, ?_, ?_⟩
    · rw [hW0eq]
      exact lt_of_le_of_lt (Polynomial.natDegree_sub_le _ _)
        (by rw [Nat.max_lt]
            exact ⟨hWdeg, lt_of_le_of_lt (Polynomial.natDegree_C_mul_le _ _) hW1deg⟩)
    · intro ζ hζ; rw [eval_sub, hmdef] at *; rw [modByMonic_eval_eq Q0 S ζ hζ, sub_self]
    · intro ζ hζ; rw [eval_sub, hmdef] at *; rw [modByMonic_eval_eq Q1 S ζ hζ, sub_self]

end ArkLib.ProximityGap.SinglePencilQIndependence

/-! ## Axiom audit -/
#print axioms ArkLib.ProximityGap.SinglePencilQIndependence.single_pencil_aclose_card_le
#print axioms ArkLib.ProximityGap.SinglePencilQIndependence.rootsOfUnity_pencil_aclose_card_le
#print axioms ArkLib.ProximityGap.SinglePencilQIndependence.mca_badscalar_card_le
#print axioms ArkLib.ProximityGap.SinglePencilQIndependence.rootsOfUnity_mca_badscalar_card_le
#print axioms ArkLib.ProximityGap.SinglePencilQIndependence.mca_badscalar_general

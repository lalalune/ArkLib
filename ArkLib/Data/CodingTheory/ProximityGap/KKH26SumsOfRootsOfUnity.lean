/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.ResultantLiftLoop52
import Mathlib

/-!
# KKH26 Lemma 1 — distinct signed sums of roots of unity at an explicit prime threshold

This file formalizes **Lemma 1** of [KKH26] (Krachun–Kazanin–Haböck, *Failure of proximity
gaps close to capacity*, ePrint 2026/782), the single new mathematical kernel of their
counterexample to the [BCIKS20] up-to-capacity proximity-gap conjecture (Conjecture 1) and the
[BGKS20] list-decoding conjecture (Conjecture 2) for Reed–Solomon codes over smooth
multiplicative subgroups of **prime fields** — the Proximity Prize regime (issue #232).

> **Lemma 1 [KKH26].** Let `G` be a multiplicative subgroup of a prime field `F_p` of size
> `s = 2^m`. If `p > s^{s/2}`, then for any integer `1 ≤ r ≤ s/2`,
> `#{x₁ + ⋯ + x_r : distinct x₁, …, x_r ∈ G} ≥ 2^r · (s/2).choose r`.

The proof follows the paper: a sum of `r` distinct elements of `G` stemming from `S ⊆ G` with
`S ∩ (−S) = ∅` is the value at a generator `g` of a **signed sum-polynomial**
`P = ∑ (−1)^{ε_k} X^{i_k}` with distinct exponents `i_k ∈ [0, s/2)`.  If two distinct
sum-polynomials `P, Q` collide at `g`, then `R = P − Q` and `Φ_s = X^{s/2} + 1` share a root
mod `p`, so `p ∣ Res_ℤ(R, Φ_s)` (Loop52 pillar).  The resultant is nonzero by irreducibility
of `Φ_s` over `ℚ` (Loop52 pillar), and over `ℂ` it is the product of the `s/2` values of `R`
at primitive `s`-th roots of unity, each of modulus `≤ ‖R‖₁ ≤ 2r ≤ s`; hence
`0 < |Res| ≤ s^{s/2} < p`, a contradiction.  Distinct data therefore give distinct values,
and there are exactly `2^r · (s/2).choose r` data.

### Relation to in-tree work

`CandidateFiniteFieldDisproofLoop53.lean` proves the *unsigned, existential-prime* variant
(some Dirichlet prime avoiding the finitely many collision resultants).  This file proves the
**quantitative** form the paper's Theorem 1 consumes: *every* `p ≡ 1 (mod s)` above the
**explicit threshold** `s^{s/2}` works, for **signed** sums at **each fixed** `r` — the fixed-`r`
count is what ties to the code distance `δ* = 1 − (r−2)/s` in [KKH26] Proposition 1.  The new
analytic ingredient over Loop52/53 is the archimedean resultant bound
(`natAbs_resultant_cyclotomic_le`).

### What is *not* formalized (honest frontier)

[KKH26] Theorem 1 / Proposition 1 additionally need: vanishing-polynomial gap codeword
constructions over the projection `π : H → G`, Stirling asymptotics for `2^r·C(s/2,r)`, and —
for polynomial field sizes `p = Θ(n^β)` — the Thorner–Zaman quantitative PNT in arithmetic
progressions.  Those remain external; this file is the complete additive-combinatorics core.

## Main results

* `natAbs_resultant_cyclotomic_le` — `|Res_ℤ(R, Φ_{2^m})| ≤ ‖R‖₁^{2^{m-1}}` (window ℓ¹-norm).
* `not_isRoot_of_l1On_pow_lt` — explicit-threshold non-collision: a nonzero `R` with
  `deg R < 2^{m-1}` and `‖R‖₁^{2^{m-1}} < p` has `R(g) ≠ 0` for `g` a primitive `2^m`-th root
  of unity in `F_p`.
* `sVal_injOn` — distinct signed `(U, T)`-data give distinct values `∑_{T} g^i − ∑_{U∖T} g^i`
  whenever `(2^m)^{2^{m-1}} < p`.
* `kkh26_lemma1` — **[KKH26] Lemma 1**: the set of sums of `r` distinct elements of the
  order-`2^m` subgroup `⟨g⟩ ⊆ F_p^×` has at least `2^r · (2^{m-1}).choose r` elements.
* **Divisibility route (issue #334, [KKH26] Lemma 2 wiring):** `collisionResultant` exposes
  the integer `N(d₁,d₂) = Res_ℤ(P_{d₁} − P_{d₂}, Φ_{2^m})` the size route bounds internally;
  `sVal_injOn_of_not_dvd` and `kkh26_lemma1_of_not_dvd` re-run the chain with the size
  hypothesis `p > s^{s/2}` replaced by "`p` divides no collision resultant" (plus the mild
  `p > 2^m`), the form consumable at `p = Θ(n^β)` from the [TZ24] good-prime supply
  (`KKH26ThornerZaman.lean`); `not_dvd_collisionResultant_of_lt` shows the old hypothesis
  implies the new one, so the routes share the same core.

## References

* [KKH26] D. Krachun, S. Kazanin, U. Haböck, *Failure of proximity gaps close to capacity*,
  ePrint 2026/782.
* [BCIKS20] Ben-Sasson, Carmon, Ishai, Kopparty, Saraf, *Proximity Gaps for Reed–Solomon
  Codes*, ePrint 2020/654.
-/

open Polynomial Finset

namespace ArkLib.ProximityGap.KKH26

open ArkLib.ProximityGap.ResultantLiftLoop52

/-! ### Window ℓ¹ bookkeeping -/

/-- The ℓ¹-norm of the coefficients of `f` on the window `[0, n)`.  For the polynomials of
this file (supported on `[0, n)`) this is the full ℓ¹ norm `∑ |coeff|`. -/
def l1On (n : ℕ) (f : Polynomial ℤ) : ℕ := ∑ j ∈ range n, (f.coeff j).natAbs

lemma l1On_sub_le (n : ℕ) (f g : Polynomial ℤ) :
    l1On n (f - g) ≤ l1On n f + l1On n g := by
  unfold l1On
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_le_sum fun j _ => ?_
  rw [Polynomial.coeff_sub]
  exact Int.natAbs_sub_le _ _

lemma natAbs_leadingCoeff_le_l1On {f : Polynomial ℤ} {n : ℕ} (hf : f.natDegree < n) :
    f.leadingCoeff.natAbs ≤ l1On n f := by
  unfold l1On
  rw [Polynomial.leadingCoeff]
  exact Finset.single_le_sum (f := fun j => (f.coeff j).natAbs)
    (fun _ _ => Nat.zero_le _) (mem_range.mpr hf)

/-! ### Norm bounds over `ℂ` -/

/-- A product of complex numbers each of norm `≤ B` has norm `≤ B^card`. -/
lemma norm_multiset_prod_le (s : Multiset ℂ) {B : ℝ} (h : ∀ x ∈ s, ‖x‖ ≤ B) :
    ‖s.prod‖ ≤ B ^ (Multiset.card s) := by
  induction s using Multiset.induction_on with
  | empty => simp
  | cons a s ih =>
    have hB : 0 ≤ B := le_trans (norm_nonneg a) (h a (Multiset.mem_cons_self a s))
    rw [Multiset.prod_cons, Multiset.card_cons]
    calc ‖a * s.prod‖ = ‖a‖ * ‖s.prod‖ := norm_mul a s.prod
      _ ≤ B * B ^ Multiset.card s :=
          mul_le_mul (h a (Multiset.mem_cons_self a s))
            (ih fun x hx => h x (Multiset.mem_cons_of_mem hx))
            (norm_nonneg _) hB
      _ = B ^ (Multiset.card s + 1) := (pow_succ' B _).symm

/-- On the unit circle, an integer polynomial of degree `< n` is bounded by its window
ℓ¹-norm. -/
lemma norm_eval_le_l1On {f : Polynomial ℤ} {n : ℕ} (hf : f.natDegree < n) {z : ℂ}
    (hz : ‖z‖ = 1) : ‖(f.map (Int.castRingHom ℂ)).eval z‖ ≤ (l1On n f : ℝ) := by
  have hdeg : (f.map (Int.castRingHom ℂ)).natDegree < n := by
    rwa [natDegree_map_eq_of_injective Int.cast_injective]
  rw [Polynomial.eval_eq_sum_range' hdeg]
  refine le_trans (norm_sum_le _ _) ?_
  unfold l1On
  rw [Nat.cast_sum]
  refine Finset.sum_le_sum fun i _ => ?_
  rw [norm_mul, norm_pow, hz, one_pow, mul_one, Polynomial.coeff_map]
  rw [show ((Int.castRingHom ℂ) (f.coeff i)) = ((f.coeff i : ℤ) : ℂ) from rfl]
  rw [Complex.norm_intCast, Nat.cast_natAbs]
  exact le_of_eq Int.cast_abs.symm

private lemma totient_two_pow {m : ℕ} (hm : 1 ≤ m) :
    Nat.totient (2 ^ m) = 2 ^ (m - 1) := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_lt hm
  rw [Nat.zero_add, Nat.totient_prime_pow_succ Nat.prime_two]
  simp

/-! ### The Mahler/Landau sharpening surface -/

/-- For `m ≥ 1`, the two-power cyclotomic is `Φ_{2^m}(X) = X^(2^(m-1)) + 1`. -/
lemma cyclotomic_two_pow_eq_X_pow_add_one {R : Type*} [CommRing R] {m : ℕ}
    (hm : 1 ≤ m) :
    cyclotomic (2 ^ m) R = X ^ (2 ^ (m - 1)) + 1 := by
  have hpow : 2 ^ m = 2 ^ ((m - 1) + 1) := by rw [Nat.sub_add_cancel hm]
  rw [hpow, cyclotomic_prime_pow_eq_geom_sum Nat.prime_two]
  norm_num [Finset.sum_range_succ, add_comm]

/-- Evaluating `Φ_{2^m}` at a complex point costs at most a factor `2` times the
`2^(m-1)`-st power of the usual root-height factor. -/
lemma norm_eval_cyclotomic_two_pow_le {m : ℕ} (hm : 1 ≤ m) (z : ℂ) :
    ‖(cyclotomic (2 ^ m) ℂ).eval z‖
      ≤ 2 * (max 1 ‖z‖) ^ (2 ^ (m - 1)) := by
  rw [cyclotomic_two_pow_eq_X_pow_add_one (R := ℂ) hm]
  have hzle : ‖z‖ ^ (2 ^ (m - 1)) ≤ (max 1 ‖z‖) ^ (2 ^ (m - 1)) :=
    pow_le_pow_left₀ (norm_nonneg z) (le_max_right 1 ‖z‖) _
  have h1le : 1 ≤ (max 1 ‖z‖) ^ (2 ^ (m - 1)) :=
    one_le_pow₀ (le_max_left 1 ‖z‖)
  calc
    ‖(X ^ (2 ^ (m - 1)) + 1 : Polynomial ℂ).eval z‖
        = ‖z ^ (2 ^ (m - 1)) + 1‖ := by simp
    _ ≤ ‖z ^ (2 ^ (m - 1))‖ + ‖(1 : ℂ)‖ := norm_add_le _ _
    _ = ‖z‖ ^ (2 ^ (m - 1)) + 1 := by rw [norm_pow, norm_one]
    _ ≤ (max 1 ‖z‖) ^ (2 ^ (m - 1)) + (max 1 ‖z‖) ^ (2 ^ (m - 1)) :=
        add_le_add hzle h1le
    _ = 2 * (max 1 ‖z‖) ^ (2 ^ (m - 1)) := by ring

lemma norm_multiset_prod_map_le_prod {α : Type*} (s : Multiset α) (f : α → ℂ)
    (B : α → ℝ) (hB : ∀ x ∈ s, 0 ≤ B x) (hf : ∀ x ∈ s, ‖f x‖ ≤ B x) :
    ‖(s.map f).prod‖ ≤ (s.map B).prod := by
  induction s using Multiset.induction_on with
  | empty => simp
  | cons a s ih =>
      rw [Multiset.map_cons, Multiset.map_cons, Multiset.prod_cons, Multiset.prod_cons, norm_mul]
      refine mul_le_mul (hf a (Multiset.mem_cons_self a s))
        (ih (fun x hx => hB x (Multiset.mem_cons_of_mem hx))
          (fun x hx => hf x (Multiset.mem_cons_of_mem hx)))
        (norm_nonneg _) (hB a (Multiset.mem_cons_self a s))

lemma multiset_prod_two_mul_pow_height (s : Multiset ℂ) (N : ℕ) :
    (s.map (fun z => (2 : ℝ) * (max 1 ‖z‖) ^ N)).prod
      = (2 : ℝ) ^ s.card * (s.map (fun z => max 1 ‖z‖)).prod ^ N := by
  induction s using Multiset.induction_on with
  | empty => simp
  | cons a s ih =>
      rw [Multiset.map_cons, Multiset.map_cons, Multiset.prod_cons, Multiset.prod_cons,
        Multiset.card_cons, ih, mul_pow, pow_succ']
      ring

/-- **Mahler resultant bound.**  For `deg R < deg Φ_{2^m}`, the cyclotomic resultant is
bounded by `2^deg(R) · M(R)^(2^(m-1))`.  This is the root-side sharpening of the older
pointwise `ℓ¹` bound: `Φ_{2^m}(β) = β^(2^(m-1)) + 1`, so each root of `R` contributes only
one factor `2` and the remaining height is exactly Mahler measure. -/
theorem natAbs_resultant_cyclotomic_le_mahler {m : ℕ} (hm : 1 ≤ m)
    (R : Polynomial ℤ) (hdeg : R.natDegree < 2 ^ (m - 1)) :
    ((Polynomial.resultant R (cyclotomic (2 ^ m) ℤ)).natAbs : ℝ)
      ≤ (2 : ℝ) ^ R.natDegree
        * (R.map (Int.castRingHom ℂ)).mahlerMeasure ^ (2 ^ (m - 1)) := by
  classical
  set ι : ℤ →+* ℂ := Int.castRingHom ℂ with hι
  have hinj : Function.Injective ι := Int.cast_injective
  set Φ : Polynomial ℤ := cyclotomic (2 ^ m) ℤ with hΦdef
  set RC : Polynomial ℂ := R.map ι with hRCdef
  set ΦC : Polynomial ℂ := Φ.map ι with hΦCdef
  by_cases hR0 : R = 0
  · subst hR0
    have hΦdeg_pos : 0 < (cyclotomic (2 ^ m) ℤ).natDegree := by
      rw [natDegree_cyclotomic, totient_two_pow hm]
      positivity
    simp [RC, Φ, ι, hΦdeg_pos.ne']
  have hRC0 : RC ≠ 0 := by
    rw [hRCdef]
    exact (Polynomial.map_ne_zero_iff hinj).mpr hR0
  have hdegR : RC.natDegree = R.natDegree := by
    rw [hRCdef, natDegree_map_eq_of_injective hinj]
  have hdegΦ : ΦC.natDegree = Φ.natDegree := by
    rw [hΦCdef, natDegree_map_eq_of_injective hinj]
  have hmap : Polynomial.resultant RC ΦC = ι (Polynomial.resultant R Φ) := by
    rw [hRCdef, hΦCdef]
    rw [show Polynomial.resultant (R.map ι) (Φ.map ι)
          = Polynomial.resultant (R.map ι) (Φ.map ι) R.natDegree Φ.natDegree by
        rw [natDegree_map_eq_of_injective hinj, natDegree_map_eq_of_injective hinj],
      Polynomial.resultant_map_map]
  have hsplits : RC.Splits := IsAlgClosed.splits _
  have hprod : Polynomial.resultant RC ΦC
      = RC.leadingCoeff ^ ΦC.natDegree * (RC.roots.map ΦC.eval).prod := by
    have h := Polynomial.resultant_eq_prod_eval RC ΦC ΦC.natDegree le_rfl hsplits
    simpa using h
  have hΦeval : ∀ z ∈ RC.roots,
      ‖ΦC.eval z‖ ≤ 2 * (max 1 ‖z‖) ^ (2 ^ (m - 1)) := by
    intro z _hz
    rw [hΦCdef, hΦdef, map_cyclotomic_int]
    exact norm_eval_cyclotomic_two_pow_le hm z
  have hprodBound : ‖(RC.roots.map ΦC.eval).prod‖
      ≤ (2 : ℝ) ^ R.natDegree
        * (RC.roots.map (fun z => max 1 ‖z‖)).prod ^ (2 ^ (m - 1)) := by
    have h₁ := norm_multiset_prod_map_le_prod RC.roots ΦC.eval
      (fun z => (2 : ℝ) * (max 1 ‖z‖) ^ (2 ^ (m - 1)))
      (by
        intro z _hz
        positivity)
      hΦeval
    have h₂ := multiset_prod_two_mul_pow_height RC.roots (2 ^ (m - 1))
    rw [h₂] at h₁
    have hcard : RC.roots.card = R.natDegree := by
      rw [← hsplits.natDegree_eq_card_roots, hdegR]
    rwa [hcard] at h₁
  have hresNorm : ‖(ι (Polynomial.resultant R Φ) : ℂ)‖
      ≤ (2 : ℝ) ^ R.natDegree * RC.mahlerMeasure ^ (2 ^ (m - 1)) := by
    rw [← hmap, hprod]
    calc
      ‖RC.leadingCoeff ^ ΦC.natDegree * (RC.roots.map ΦC.eval).prod‖
          = ‖RC.leadingCoeff‖ ^ ΦC.natDegree * ‖(RC.roots.map ΦC.eval).prod‖ := by
            rw [norm_mul, norm_pow]
      _ ≤ ‖RC.leadingCoeff‖ ^ ΦC.natDegree
            * ((2 : ℝ) ^ R.natDegree
              * (RC.roots.map (fun z => max 1 ‖z‖)).prod ^ (2 ^ (m - 1))) := by
            exact mul_le_mul_of_nonneg_left hprodBound (pow_nonneg (norm_nonneg _) _)
      _ = (2 : ℝ) ^ R.natDegree
            * (‖RC.leadingCoeff‖
              * (RC.roots.map (fun z => max 1 ‖z‖)).prod) ^ (2 ^ (m - 1)) := by
            rw [hdegΦ, hΦdef, natDegree_cyclotomic, totient_two_pow hm, mul_pow]
            ring
      _ = (2 : ℝ) ^ R.natDegree * RC.mahlerMeasure ^ (2 ^ (m - 1)) := by
            rw [mahlerMeasure_eq_leadingCoeff_mul_prod_roots]
  have hcast : ‖(ι (Polynomial.resultant R Φ) : ℂ)‖
      = ((Polynomial.resultant R Φ).natAbs : ℝ) := by
    rw [show (ι (Polynomial.resultant R Φ) : ℂ)
          = ((Polynomial.resultant R Φ : ℤ) : ℂ) from rfl]
    rw [Complex.norm_intCast, Nat.cast_natAbs]
    exact Int.cast_abs.symm
  have hfinal : ((Polynomial.resultant R Φ).natAbs : ℝ)
      ≤ (2 : ℝ) ^ R.natDegree * RC.mahlerMeasure ^ (2 ^ (m - 1)) := by
    rw [← hcast]
    exact hresNorm
  simpa [Φ, RC, ι] using hfinal

/-- **Landau resultant bridge.**  Combining the Mahler resultant bound with Landau's
inequality gives the `ℓ²` surface needed for the μ=6 divisor-discharge lane. -/
theorem natAbs_resultant_cyclotomic_le_landau {m : ℕ} (hm : 1 ≤ m)
    (R : Polynomial ℤ) (hdeg : R.natDegree < 2 ^ (m - 1)) :
    ((Polynomial.resultant R (cyclotomic (2 ^ m) ℤ)).natAbs : ℝ)
      ≤ (2 : ℝ) ^ (2 ^ (m - 1) - 1)
        * (√(∑ i ∈ (R.map (Int.castRingHom ℂ)).support,
          ‖(R.map (Int.castRingHom ℂ)).coeff i‖ ^ 2)) ^ (2 ^ (m - 1)) := by
  set RC : Polynomial ℂ := R.map (Int.castRingHom ℂ)
  have hbase := natAbs_resultant_cyclotomic_le_mahler hm R hdeg
  have hpow2 : (2 : ℝ) ^ R.natDegree ≤ (2 : ℝ) ^ (2 ^ (m - 1) - 1) := by
    exact pow_le_pow_right₀ (show (1 : ℝ) ≤ 2 by norm_num) (by omega)
  have hM : RC.mahlerMeasure
      ≤ √(∑ i ∈ RC.support, ‖RC.coeff i‖ ^ 2) :=
    Polynomial.mahlerMeasure_le_sqrt_sum_sq_norm_coeff RC
  have hMpow : RC.mahlerMeasure ^ (2 ^ (m - 1))
      ≤ (√(∑ i ∈ RC.support, ‖RC.coeff i‖ ^ 2)) ^ (2 ^ (m - 1)) :=
    pow_le_pow_left₀ RC.mahlerMeasure_nonneg hM _
  refine le_trans hbase ?_
  exact mul_le_mul hpow2 hMpow
    (pow_nonneg RC.mahlerMeasure_nonneg _) (pow_nonneg (by norm_num) _)

/-! ### The archimedean resultant bound (the new quantitative core over Loop52/53) -/

/-- **Archimedean bound for the cyclotomic resultant.** For `R : ℤ[X]` of degree
`< 2^{m-1} = deg Φ_{2^m}`,
`|Res_ℤ(R, Φ_{2^m})| ≤ ‖R‖₁^{2^{m-1}}`, since over `ℂ` the resultant is (up to sign) the
product of the `2^{m-1}` values of `R` at primitive `2^m`-th roots of unity, each of modulus
`≤ ‖R‖₁`.  This is the explicit-threshold ingredient of [KKH26] Lemma 1 (inequality (3)). -/
theorem natAbs_resultant_cyclotomic_le {m : ℕ} (hm : 1 ≤ m) (R : Polynomial ℤ)
    (hdeg : R.natDegree < 2 ^ (m - 1)) :
    (Polynomial.resultant R (cyclotomic (2 ^ m) ℤ)).natAbs
      ≤ l1On (2 ^ (m - 1)) R ^ 2 ^ (m - 1) := by
  classical
  set ι : ℤ →+* ℂ := Int.castRingHom ℂ with hι
  have hinj : Function.Injective ι := Int.cast_injective
  set Φ : Polynomial ℤ := cyclotomic (2 ^ m) ℤ with hΦdef
  -- swap the argument order (the sign dies under `natAbs`)
  have hswap : (Polynomial.resultant R Φ).natAbs = (Polynomial.resultant Φ R).natAbs := by
    rw [Polynomial.resultant_comm, Int.natAbs_mul, Int.natAbs_pow]
    simp
  -- transport the resultant to `ℂ`
  have hdegΦ : (Φ.map ι).natDegree = Φ.natDegree :=
    natDegree_map_eq_of_injective hinj _
  have hdegR : (R.map ι).natDegree = R.natDegree :=
    natDegree_map_eq_of_injective hinj _
  have hmap : Polynomial.resultant (Φ.map ι) (R.map ι) = ι (Polynomial.resultant Φ R) := by
    rw [show Polynomial.resultant (Φ.map ι) (R.map ι)
          = Polynomial.resultant (Φ.map ι) (R.map ι) Φ.natDegree R.natDegree by
        rw [hdegΦ, hdegR],
      Polynomial.resultant_map_map]
  -- the product formula over `ℂ`
  have hΦC : Φ.map ι = cyclotomic (2 ^ m) ℂ := map_cyclotomic_int _ ℂ
  have hmonic : (Φ.map ι).Monic := (cyclotomic.monic _ ℤ).map ι
  have hsplits : (Φ.map ι).Splits := IsAlgClosed.splits _
  have hprod : Polynomial.resultant (Φ.map ι) (R.map ι)
      = (((Φ.map ι).roots).map (R.map ι).eval).prod := by
    have h := Polynomial.resultant_eq_prod_eval (Φ.map ι) (R.map ι)
      ((R.map ι).natDegree) le_rfl hsplits
    rwa [hmonic.leadingCoeff, one_pow, one_mul] at h
  -- each root of `Φ` over `ℂ` lies on the unit circle
  have hroots : ∀ z ∈ (Φ.map ι).roots, ‖(R.map ι).eval z‖ ≤ (l1On (2 ^ (m - 1)) R : ℝ) := by
    intro z hz
    have hroot : (Φ.map ι).IsRoot z := isRoot_of_mem_roots hz
    have hdvd : (Φ.map ι) ∣ (X ^ (2 ^ m) - 1 : Polynomial ℂ) := by
      rw [hΦC]; exact cyclotomic.dvd_X_pow_sub_one (2 ^ m) ℂ
    have hz1 : z ^ (2 ^ m) = 1 := by
      have h0 := Polynomial.eval_eq_zero_of_dvd_of_eval_eq_zero hdvd hroot
      simpa [sub_eq_zero] using h0
    have hnorm : ‖z‖ = 1 := by
      have h1 : ‖z‖ ^ (2 ^ m) = 1 := by rw [← norm_pow, hz1, norm_one]
      rcases lt_trichotomy ‖z‖ 1 with h | h | h
      · exact absurd h1 (ne_of_lt (pow_lt_one₀ (norm_nonneg z) h (by positivity)))
      · exact h
      · exact absurd h1 (ne_of_gt (one_lt_pow₀ h (by positivity)))
    exact norm_eval_le_l1On hdeg hnorm
  -- count the roots
  have hcard : Multiset.card (Φ.map ι).roots = 2 ^ (m - 1) := by
    have h1 := hsplits.natDegree_eq_card_roots
    rw [← h1, hdegΦ, hΦdef, natDegree_cyclotomic, totient_two_pow hm]
  -- assemble over `ℝ`
  have hbound : ‖(ι (Polynomial.resultant Φ R) : ℂ)‖
      ≤ ((l1On (2 ^ (m - 1)) R : ℝ)) ^ (2 ^ (m - 1)) := by
    rw [← hmap, hprod]
    have := norm_multiset_prod_le (((Φ.map ι).roots).map (R.map ι).eval)
      (B := (l1On (2 ^ (m - 1)) R : ℝ))
      (by intro x hx
          obtain ⟨z, hz, rfl⟩ := Multiset.mem_map.mp hx
          exact hroots z hz)
    rwa [Multiset.card_map, hcard] at this
  have hcast : ‖(ι (Polynomial.resultant Φ R) : ℂ)‖
      = ((Polynomial.resultant Φ R).natAbs : ℝ) := by
    rw [show (ι (Polynomial.resultant Φ R) : ℂ)
          = ((Polynomial.resultant Φ R : ℤ) : ℂ) from rfl]
    rw [Complex.norm_intCast, Nat.cast_natAbs]
    exact Int.cast_abs.symm
  rw [hswap]
  have hfin : ((Polynomial.resultant Φ R).natAbs : ℝ)
      ≤ ((l1On (2 ^ (m - 1)) R ^ 2 ^ (m - 1) : ℕ) : ℝ) := by
    rw [← hcast]
    push_cast
    exact hbound
  exact_mod_cast hfin

/-! ### Explicit-threshold non-collision -/

/-- **Explicit-threshold non-vanishing at a primitive root** ([KKH26] Lemma 1, collision
step).  If `g ∈ F_p` is a primitive `2^m`-th root of unity and `R : ℤ[X]` is nonzero of
degree `< 2^{m-1}` with `‖R‖₁^{2^{m-1}} < p`, then `R(g) ≠ 0` in `F_p`.  (Loop52's pillars
turn a root into `p ∣ Res_ℤ(R, Φ_{2^m}) ≠ 0`; the archimedean bound caps `|Res| < p`.) -/
theorem not_isRoot_of_l1On_pow_lt {p : ℕ} [Fact p.Prime] {m : ℕ} (hm : 1 ≤ m)
    {g : ZMod p} (hg : IsPrimitiveRoot g (2 ^ m))
    {R : Polynomial ℤ} (hR0 : R ≠ 0) (hdeg : R.natDegree < 2 ^ (m - 1))
    (hp : l1On (2 ^ (m - 1)) R ^ 2 ^ (m - 1) < p) :
    ¬ (R.map (Int.castRingHom (ZMod p))).IsRoot g := by
  intro hroot
  -- the leading coefficient of `R` survives mod `p`
  have hlcR : ((R.leadingCoeff : ℤ) : ZMod p) ≠ 0 := by
    intro h0
    have hdvd : (p : ℤ) ∣ R.leadingCoeff := by
      rwa [ZMod.intCast_zmod_eq_zero_iff_dvd] at h0
    have hlcne : R.leadingCoeff ≠ 0 := leadingCoeff_ne_zero.mpr hR0
    have h1 : p ≤ R.leadingCoeff.natAbs := by
      have h2 := Int.natAbs_dvd_natAbs.mpr hdvd
      simpa using Nat.le_of_dvd (Int.natAbs_pos.mpr hlcne) (by simpa using h2)
    have h2 : R.leadingCoeff.natAbs ≤ l1On (2 ^ (m - 1)) R :=
      natAbs_leadingCoeff_le_l1On hdeg
    have h3 : l1On (2 ^ (m - 1)) R ≤ l1On (2 ^ (m - 1)) R ^ 2 ^ (m - 1) :=
      Nat.le_self_pow (by positivity) _
    omega
  -- `Φ` is monic, so its leading coefficient survives as well
  have hΦmonic : (cyclotomic (2 ^ m) ℤ).Monic := cyclotomic.monic _ ℤ
  have hlcΦ : (((cyclotomic (2 ^ m) ℤ).leadingCoeff : ℤ) : ZMod p) ≠ 0 := by
    rw [hΦmonic.leadingCoeff]
    simp
  -- `g` is a common root of `R` and `Φ` mod `p`
  have hΦroot : ((cyclotomic (2 ^ m) ℤ).map (Int.castRingHom (ZMod p))).IsRoot g := by
    rw [map_cyclotomic_int]
    exact hg.isRoot_cyclotomic (by positivity)
  -- Loop52 pillars: `p ∣ Res ≠ 0`
  have hdvd := prime_dvd_resultant_of_common_root R (cyclotomic (2 ^ m) ℤ)
    hlcR hlcΦ hroot hΦroot
  have hne : Polynomial.resultant R (cyclotomic (2 ^ m) ℤ) ≠ 0 :=
    resultant_int_ne_zero_of_isCoprime_rat _ _ (diff_coprime_cyclotomic_rat hm R hdeg hR0)
  -- size contradiction against the archimedean bound
  have hle : p ≤ (Polynomial.resultant R (cyclotomic (2 ^ m) ℤ)).natAbs := by
    have h2 := Int.natAbs_dvd_natAbs.mpr hdvd
    exact Nat.le_of_dvd (Int.natAbs_pos.mpr hne) (by simpa using h2)
  have hub := natAbs_resultant_cyclotomic_le hm R hdeg
  omega

/-! ### Signed sum-polynomials -/

/-- The signed sum-polynomial of a pair `T ⊆ U`:
`P_{U,T} = ∑_{i ∈ T} X^i − ∑_{i ∈ U∖T} X^i` — equation (1) of [KKH26], with `T` the positive
support and `U ∖ T` the negative support. -/
noncomputable def sumPoly (U T : Finset ℕ) : Polynomial ℤ :=
  ∑ i ∈ T, X ^ i - ∑ i ∈ U \ T, X ^ i

lemma coeff_sum_X_pow (T : Finset ℕ) (k : ℕ) :
    (∑ i ∈ T, (X : Polynomial ℤ) ^ i).coeff k = if k ∈ T then 1 else 0 := by
  classical
  rw [finset_sum_coeff]
  simp only [coeff_X_pow]
  rw [Finset.sum_ite_eq T k (fun _ => (1 : ℤ))]

lemma sumPoly_coeff (U T : Finset ℕ) (k : ℕ) :
    (sumPoly U T).coeff k
      = (if k ∈ T then 1 else 0) - (if k ∈ U \ T then 1 else 0) := by
  rw [sumPoly, coeff_sub, coeff_sum_X_pow, coeff_sum_X_pow]

lemma sumPoly_coeff_eq_one_iff (U T : Finset ℕ) (k : ℕ) :
    (sumPoly U T).coeff k = 1 ↔ k ∈ T := by
  rw [sumPoly_coeff]
  by_cases h1 : k ∈ T
  · have h2 : k ∉ U \ T := fun hc => (mem_sdiff.mp hc).2 h1
    simp [h1, h2]
  · by_cases h2 : k ∈ U \ T <;> simp [h1, h2]

lemma sumPoly_coeff_eq_neg_one_iff (U T : Finset ℕ) (k : ℕ) :
    (sumPoly U T).coeff k = -1 ↔ k ∈ U \ T := by
  rw [sumPoly_coeff]
  by_cases h1 : k ∈ T
  · have h2 : k ∉ U \ T := fun hc => (mem_sdiff.mp hc).2 h1
    simp [h1, h2]
  · by_cases h2 : k ∈ U \ T <;> simp [h1, h2]

/-- Distinct `(U, T)`-data give distinct sum-polynomials. -/
lemma sumPoly_inj {U₁ T₁ U₂ T₂ : Finset ℕ} (hT₁ : T₁ ⊆ U₁) (hT₂ : T₂ ⊆ U₂)
    (h : sumPoly U₁ T₁ = sumPoly U₂ T₂) : U₁ = U₂ ∧ T₁ = T₂ := by
  have hT : T₁ = T₂ := by
    ext k
    rw [← sumPoly_coeff_eq_one_iff U₁ T₁ k, ← sumPoly_coeff_eq_one_iff U₂ T₂ k, h]
  have hD : U₁ \ T₁ = U₂ \ T₂ := by
    ext k
    rw [← sumPoly_coeff_eq_neg_one_iff U₁ T₁ k, ← sumPoly_coeff_eq_neg_one_iff U₂ T₂ k, h]
  refine ⟨?_, hT⟩
  rw [← Finset.union_sdiff_of_subset hT₁, ← Finset.union_sdiff_of_subset hT₂, hD, hT]

lemma sumPoly_natDegree_lt {U T : Finset ℕ} {n : ℕ} (hn : 0 < n)
    (hU : U ⊆ range n) (hT : T ⊆ U) : (sumPoly U T).natDegree < n := by
  classical
  have hdeg : (sumPoly U T).degree < (n : WithBot ℕ) := by
    rw [sumPoly]
    refine lt_of_le_of_lt (degree_sub_le _ _) (max_lt ?_ ?_)
    · refine lt_of_le_of_lt (degree_sum_le _ _) ?_
      refine (Finset.sup_lt_iff (WithBot.bot_lt_coe n)).mpr fun i hi => ?_
      exact lt_of_le_of_lt (degree_X_pow_le _)
        (WithBot.coe_lt_coe.mpr (mem_range.mp (hU (hT hi))))
    · refine lt_of_le_of_lt (degree_sum_le _ _) ?_
      refine (Finset.sup_lt_iff (WithBot.bot_lt_coe n)).mpr fun i hi => ?_
      exact lt_of_le_of_lt (degree_X_pow_le _)
        (WithBot.coe_lt_coe.mpr (mem_range.mp (hU (mem_sdiff.mp hi).1)))
  by_cases h0 : sumPoly U T = 0
  · rw [h0]; simpa using hn
  · rwa [natDegree_lt_iff_degree_lt h0]

/-- The window ℓ¹-norm of a sum-polynomial is exactly `|U|` (its number of `±1` terms). -/
lemma l1On_sumPoly {U T : Finset ℕ} {n : ℕ} (hU : U ⊆ range n) (hT : T ⊆ U) :
    l1On n (sumPoly U T) = U.card := by
  classical
  unfold l1On
  have hpt : ∀ j ∈ range n, ((sumPoly U T).coeff j).natAbs = if j ∈ U then 1 else 0 := by
    intro j _
    rw [sumPoly_coeff]
    by_cases hjT : j ∈ T
    · have hjU : j ∈ U := hT hjT
      have hjD : j ∉ U \ T := fun hc => (mem_sdiff.mp hc).2 hjT
      simp [hjT, hjU, hjD]
    · by_cases hjU : j ∈ U
      · have hjD : j ∈ U \ T := mem_sdiff.mpr ⟨hjU, hjT⟩
        simp [hjT, hjU, hjD]
      · have hjD : j ∉ U \ T := fun hc => hjU (mem_sdiff.mp hc).1
        simp [hjT, hjU, hjD]
  rw [Finset.sum_congr rfl hpt, Finset.sum_ite_mem, Finset.sum_const, smul_eq_mul, mul_one,
    Finset.inter_eq_right.mpr hU]

lemma sumPoly_coeff_natAbs_le_one {U T : Finset ℕ} (hT : T ⊆ U) (k : ℕ) :
    ((sumPoly U T).coeff k).natAbs ≤ 1 := by
  rw [sumPoly_coeff]
  by_cases hkT : k ∈ T
  · have hkU : k ∈ U := hT hkT
    have hkD : k ∉ U \ T := fun h => (mem_sdiff.mp h).2 hkT
    simp [hkT, hkD]
  · by_cases hkU : k ∈ U
    · have hkD : k ∈ U \ T := mem_sdiff.mpr ⟨hkU, hkT⟩
      simp [hkT, hkD]
    · have hkD : k ∉ U \ T := fun h => hkU (mem_sdiff.mp h).1
      simp [hkT, hkD]

lemma sumPoly_coeff_eq_zero_of_not_mem {U T : Finset ℕ} (hT : T ⊆ U) {k : ℕ}
    (hk : k ∉ U) : (sumPoly U T).coeff k = 0 := by
  rw [sumPoly_coeff]
  have hkT : k ∉ T := fun h => hk (hT h)
  have hkD : k ∉ U \ T := fun h => hk (mem_sdiff.mp h).1
  simp [hkT, hkD]

lemma sumPoly_sub_coeff_natAbs_le_two {U₁ T₁ U₂ T₂ : Finset ℕ}
    (hT₁ : T₁ ⊆ U₁) (hT₂ : T₂ ⊆ U₂) (k : ℕ) :
    ((sumPoly U₁ T₁ - sumPoly U₂ T₂).coeff k).natAbs ≤ 2 := by
  rw [Polynomial.coeff_sub]
  have h₁ := sumPoly_coeff_natAbs_le_one hT₁ k
  have h₂ := sumPoly_coeff_natAbs_le_one hT₂ k
  have hsub := Int.natAbs_sub_le
    ((sumPoly U₁ T₁).coeff k) ((sumPoly U₂ T₂).coeff k)
  omega

lemma sumPoly_sub_coeff_eq_zero_of_not_mem_union {U₁ T₁ U₂ T₂ : Finset ℕ}
    (hT₁ : T₁ ⊆ U₁) (hT₂ : T₂ ⊆ U₂) {k : ℕ} (hk : k ∉ U₁ ∪ U₂) :
    (sumPoly U₁ T₁ - sumPoly U₂ T₂).coeff k = 0 := by
  rw [Polynomial.coeff_sub]
  have hk₁ : k ∉ U₁ := fun h => hk (mem_union_left U₂ h)
  have hk₂ : k ∉ U₂ := fun h => hk (mem_union_right U₁ h)
  rw [sumPoly_coeff_eq_zero_of_not_mem hT₁ hk₁,
    sumPoly_coeff_eq_zero_of_not_mem hT₂ hk₂]
  simp

/-- **Collision-polynomial coefficient energy.**  The difference of two signed
`r`-term polynomials has support inside `U₁ ∪ U₂` and every coefficient has size at
most `2`, so its complex coefficient-square mass is at most `8r`. -/
lemma sum_sq_norm_coeff_sumPoly_sub_le {U₁ T₁ U₂ T₂ : Finset ℕ} {r : ℕ}
    (hT₁ : T₁ ⊆ U₁) (hT₂ : T₂ ⊆ U₂) (hc₁ : U₁.card = r) (hc₂ : U₂.card = r) :
    ∑ i ∈ ((sumPoly U₁ T₁ - sumPoly U₂ T₂).map (Int.castRingHom ℂ)).support,
        ‖((sumPoly U₁ T₁ - sumPoly U₂ T₂).map (Int.castRingHom ℂ)).coeff i‖ ^ 2
      ≤ (8 * r : ℝ) := by
  classical
  set R : Polynomial ℤ := sumPoly U₁ T₁ - sumPoly U₂ T₂ with hR
  set RC : Polynomial ℂ := R.map (Int.castRingHom ℂ) with hRC
  have hcoeff : ∀ i ∈ RC.support, ‖RC.coeff i‖ ^ 2 ≤ (4 : ℝ) := by
    intro i _hi
    have hnat : (R.coeff i).natAbs ≤ 2 := by
      rw [hR]
      exact sumPoly_sub_coeff_natAbs_le_two hT₁ hT₂ i
    have hint : |R.coeff i| ≤ (2 : ℤ) := by
      rw [Int.abs_eq_natAbs]
      exact_mod_cast hnat
    have hnorm : ‖RC.coeff i‖ ≤ (2 : ℝ) := by
      rw [hRC, Polynomial.coeff_map]
      change ‖((R.coeff i : ℤ) : ℂ)‖ ≤ (2 : ℝ)
      rw [Complex.norm_intCast, ← Int.cast_abs]
      exact_mod_cast hint
    nlinarith [norm_nonneg (RC.coeff i)]
  have hsum : ∑ i ∈ RC.support, ‖RC.coeff i‖ ^ 2 ≤ (RC.support.card : ℝ) * 4 := by
    calc
      ∑ i ∈ RC.support, ‖RC.coeff i‖ ^ 2
          ≤ ∑ _i ∈ RC.support, (4 : ℝ) := Finset.sum_le_sum hcoeff
      _ = (RC.support.card : ℝ) * 4 := by
          rw [Finset.sum_const, nsmul_eq_mul]
  have hsupp : RC.support ⊆ U₁ ∪ U₂ := by
    intro i hi
    by_contra hmem
    have hzeroR : R.coeff i = 0 := by
      rw [hR]
      exact sumPoly_sub_coeff_eq_zero_of_not_mem_union hT₁ hT₂ hmem
    have hzeroC : RC.coeff i = 0 := by
      rw [hRC, Polynomial.coeff_map, hzeroR]
      simp
    exact (Polynomial.mem_support_iff.mp hi) hzeroC
  have hcard : RC.support.card ≤ 2 * r := by
    calc RC.support.card ≤ (U₁ ∪ U₂).card := Finset.card_le_card hsupp
      _ ≤ U₁.card + U₂.card := Finset.card_union_le U₁ U₂
      _ = 2 * r := by omega
  calc
    ∑ i ∈ RC.support, ‖RC.coeff i‖ ^ 2 ≤ (RC.support.card : ℝ) * 4 := hsum
    _ ≤ (2 * r : ℝ) * 4 := by
        exact mul_le_mul_of_nonneg_right (by exact_mod_cast hcard) (by norm_num)
    _ = (8 * r : ℝ) := by ring

lemma sumPoly_map_eval {F : Type*} [CommRing F] (φ : ℤ →+* F) (g : F) (U T : Finset ℕ) :
    ((sumPoly U T).map φ).eval g = ∑ i ∈ T, g ^ i - ∑ i ∈ U \ T, g ^ i := by
  rw [sumPoly, Polynomial.map_sub, eval_sub]
  congr 1 <;>
  · rw [Polynomial.map_sum, Polynomial.eval_finset_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Polynomial.map_pow, map_X, Polynomial.eval_pow, eval_X]

/-! ### The signed-data index set and its value map -/

/-- The index set of [KKH26] equation (2): pairs `(U, T)` with `T ⊆ U ⊆ [0, n)` and
`|U| = r` — `U` is the exponent support, `T ⊆ U` the positive signs. -/
def sigData (n r : ℕ) : Finset ((_ : Finset ℕ) × Finset ℕ) :=
  (powersetCard r (range n)).sigma fun U => U.powerset

lemma mem_sigData {n r : ℕ} {d : (_ : Finset ℕ) × Finset ℕ} :
    d ∈ sigData n r ↔ (d.1 ⊆ range n ∧ d.1.card = r) ∧ d.2 ⊆ d.1 := by
  obtain ⟨U, T⟩ := d
  simp [sigData, Finset.mem_sigma, mem_powersetCard, mem_powerset]

/-- There are exactly `2^r · n.choose r` signed data. -/
lemma card_sigData (n r : ℕ) : (sigData n r).card = 2 ^ r * n.choose r := by
  classical
  rw [sigData, Finset.card_sigma]
  have h : ∀ U ∈ powersetCard r (range n), U.powerset.card = 2 ^ r := by
    intro U hU
    rw [card_powerset, (mem_powersetCard.mp hU).2]
  rw [Finset.sum_congr rfl h, Finset.sum_const, smul_eq_mul, card_powersetCard, card_range,
    mul_comm]

/-- The signed sum value `∑_{i ∈ T} g^i − ∑_{i ∈ U∖T} g^i` of a signed datum. -/
def sVal {F : Type*} [CommRing F] (g : F) (d : (_ : Finset ℕ) × Finset ℕ) : F :=
  ∑ i ∈ d.2, g ^ i - ∑ i ∈ d.1 \ d.2, g ^ i

lemma sVal_eq_eval {F : Type*} [CommRing F] (g : F) (U T : Finset ℕ) :
    sVal g ⟨U, T⟩ = ((sumPoly U T).map (Int.castRingHom F)).eval g := by
  rw [sumPoly_map_eval]; rfl

/-- **Injectivity of signed sums at a primitive root** ([KKH26] Lemma 1, main step).
Above the explicit threshold `p > (2^m)^{2^{m-1}} = s^{s/2}`, distinct signed data give
distinct values. -/
theorem sVal_injOn {p : ℕ} [Fact p.Prime] {m : ℕ} (hm : 1 ≤ m)
    {g : ZMod p} (hg : IsPrimitiveRoot g (2 ^ m))
    (hp : ((2 : ℕ) ^ m) ^ 2 ^ (m - 1) < p) {r : ℕ} (hr : r ≤ 2 ^ (m - 1)) :
    Set.InjOn (sVal g) (sigData (2 ^ (m - 1)) r) := by
  classical
  intro d₁ hd₁ d₂ hd₂ heq
  obtain ⟨U₁, T₁⟩ := d₁
  obtain ⟨U₂, T₂⟩ := d₂
  obtain ⟨⟨hU₁, hc₁⟩, hT₁⟩ := mem_sigData.mp hd₁
  obtain ⟨⟨hU₂, hc₂⟩, hT₂⟩ := mem_sigData.mp hd₂
  have hhalf : 0 < 2 ^ (m - 1) := by positivity
  by_cases hR : sumPoly U₁ T₁ - sumPoly U₂ T₂ = 0
  · obtain ⟨hU, hT⟩ := sumPoly_inj hT₁ hT₂ (sub_eq_zero.mp hR)
    subst hU; subst hT; rfl
  · exfalso
    -- the collision polynomial has `g` as a root
    have hroot : ((sumPoly U₁ T₁ - sumPoly U₂ T₂).map
        (Int.castRingHom (ZMod p))).IsRoot g := by
      rw [IsRoot.def, Polynomial.map_sub, eval_sub, sub_eq_zero,
        ← sVal_eq_eval g U₁ T₁, ← sVal_eq_eval g U₂ T₂]
      exact heq
    -- degree and ℓ¹ bookkeeping
    have hdegR : (sumPoly U₁ T₁ - sumPoly U₂ T₂).natDegree < 2 ^ (m - 1) :=
      lt_of_le_of_lt (Polynomial.natDegree_sub_le _ _)
        (max_lt (sumPoly_natDegree_lt hhalf hU₁ hT₁) (sumPoly_natDegree_lt hhalf hU₂ hT₂))
    have hl1 : l1On (2 ^ (m - 1)) (sumPoly U₁ T₁ - sumPoly U₂ T₂) ≤ 2 * r := by
      have h := l1On_sub_le (2 ^ (m - 1)) (sumPoly U₁ T₁) (sumPoly U₂ T₂)
      rw [l1On_sumPoly hU₁ hT₁, l1On_sumPoly hU₂ hT₂, hc₁, hc₂] at h
      omega
    have h2r : 2 * r ≤ 2 ^ m := by
      have hsum : 2 ^ (m - 1) * 2 = 2 ^ m := by
        rw [← pow_succ, Nat.sub_add_cancel hm]
      omega
    have hpow : l1On (2 ^ (m - 1)) (sumPoly U₁ T₁ - sumPoly U₂ T₂) ^ 2 ^ (m - 1)
        < p :=
      lt_of_le_of_lt (Nat.pow_le_pow_left (le_trans hl1 h2r) _) hp
    exact not_isRoot_of_l1On_pow_lt hm hg hR hdegR hpow hroot

/-! ### From signed data to sums of distinct subgroup elements -/

/-- The `r`-element subset of `⟨g⟩` realizing a signed datum: positive signs use `g^i`,
negative signs use `−g^i = g^{i + 2^{m-1}}`. -/
def elemSet {p : ℕ} (g : ZMod p) (half : ℕ) (d : (_ : Finset ℕ) × Finset ℕ) :
    Finset (ZMod p) :=
  d.2.image (fun i => g ^ i) ∪ (d.1 \ d.2).image (fun i => g ^ (i + half))

/-- `g^{2^{m-1}} = −1` for a primitive `2^m`-th root of unity in a prime field. -/
lemma pow_half_eq_neg_one {p : ℕ} [Fact p.Prime] {m : ℕ} (hm : 1 ≤ m)
    {g : ZMod p} (hg : IsPrimitiveRoot g (2 ^ m)) : g ^ (2 ^ (m - 1)) = -1 := by
  have hsum : 2 ^ (m - 1) + 2 ^ (m - 1) = 2 ^ m := by
    have h := pow_succ 2 (m - 1)
    rw [Nat.sub_add_cancel hm] at h
    omega
  have h2 : g ^ (2 ^ (m - 1)) * g ^ (2 ^ (m - 1)) = 1 := by
    rw [← pow_add, hsum, hg.pow_eq_one]
  rcases mul_self_eq_one_iff.mp h2 with h | h
  · exact absurd h (hg.pow_ne_one_of_pos_of_lt (by positivity)
      (Nat.pow_lt_pow_right one_lt_two (by omega)))
  · exact h

section Embed

variable {p : ℕ} [Fact p.Prime] {m : ℕ} {g : ZMod p}

private lemma half_add_half {m : ℕ} (hm : 1 ≤ m) :
    2 ^ (m - 1) + 2 ^ (m - 1) = 2 ^ m := by
  have h := pow_succ 2 (m - 1)
  rw [Nat.sub_add_cancel hm] at h
  omega

private lemma half_lt_pow {m : ℕ} (hm : 1 ≤ m) : 2 ^ (m - 1) < 2 ^ m :=
  Nat.pow_lt_pow_right one_lt_two (by omega)

/-- The two image families of an `elemSet` are injective and disjoint. -/
private lemma embed_inj_disj (hm : 1 ≤ m) (hg : IsPrimitiveRoot g (2 ^ m))
    {U T : Finset ℕ} (hU : U ⊆ range (2 ^ (m - 1))) (hT : T ⊆ U) :
    Set.InjOn (fun i => g ^ i) ↑T ∧
    Set.InjOn (fun i => g ^ (i + 2 ^ (m - 1))) ↑(U \ T) ∧
    Disjoint (T.image (fun i => g ^ i))
      ((U \ T).image (fun i => g ^ (i + 2 ^ (m - 1)))) := by
  have hsum := half_add_half hm
  have hwin : ∀ i ∈ U, i < 2 ^ (m - 1) := fun i hi => mem_range.mp (hU hi)
  refine ⟨?_, ?_, ?_⟩
  · intro i hi j hj h
    exact hg.pow_inj
      (lt_trans (hwin i (hT hi)) (half_lt_pow hm))
      (lt_trans (hwin j (hT hj)) (half_lt_pow hm)) h
  · intro i hi j hj h
    have hi' : i ∈ U \ T := Finset.mem_coe.mp hi
    have hj' : j ∈ U \ T := Finset.mem_coe.mp hj
    have h1 := hg.pow_inj
      (by have := hwin i (mem_sdiff.mp hi').1; omega)
      (by have := hwin j (mem_sdiff.mp hj').1; omega) h
    omega
  · rw [Finset.disjoint_left]
    rintro x hx₁ hx₂
    obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hx₁
    obtain ⟨j, hj, hji⟩ := Finset.mem_image.mp hx₂
    have h1 := hg.pow_inj
      (by have := hwin j (mem_sdiff.mp hj).1; omega)
      (lt_trans (hwin i (hT hi)) (half_lt_pow hm)) hji
    have := hwin i (hT hi)
    omega

lemma elemSet_subset (hm : 1 ≤ m) {r : ℕ} {d : (_ : Finset ℕ) × Finset ℕ}
    (hd : d ∈ sigData (2 ^ (m - 1)) r) :
    elemSet g (2 ^ (m - 1)) d ⊆ (range (2 ^ m)).image (fun i => g ^ i) := by
  obtain ⟨⟨hU, _⟩, hT⟩ := mem_sigData.mp hd
  have hsum := half_add_half hm
  refine Finset.union_subset ?_ ?_
  · refine Finset.image_subset_iff.mpr fun i hi => Finset.mem_image.mpr ?_
    exact ⟨i, mem_range.mpr (lt_trans (mem_range.mp (hU (hT hi))) (half_lt_pow hm)), rfl⟩
  · refine Finset.image_subset_iff.mpr fun i hi => Finset.mem_image.mpr ?_
    have hilt : i < 2 ^ (m - 1) := mem_range.mp (hU (mem_sdiff.mp hi).1)
    exact ⟨i + 2 ^ (m - 1), mem_range.mpr (by omega), rfl⟩

lemma elemSet_card (hm : 1 ≤ m) (hg : IsPrimitiveRoot g (2 ^ m))
    {r : ℕ} {d : (_ : Finset ℕ) × Finset ℕ}
    (hd : d ∈ sigData (2 ^ (m - 1)) r) :
    (elemSet g (2 ^ (m - 1)) d).card = r := by
  classical
  obtain ⟨⟨hU, hc⟩, hT⟩ := mem_sigData.mp hd
  obtain ⟨hinj₁, hinj₂, hdisj⟩ := embed_inj_disj hm hg hU hT
  rw [elemSet, Finset.card_union_of_disjoint hdisj,
    Finset.card_image_of_injOn hinj₁, Finset.card_image_of_injOn hinj₂]
  have h1 : #(d.1 \ d.2) + #d.2 = #(d.1 ∪ d.2) := Finset.card_sdiff_add_card _ _
  rw [Finset.union_eq_left.mpr hT] at h1
  omega

lemma elemSet_sum (hm : 1 ≤ m) (hg : IsPrimitiveRoot g (2 ^ m))
    {r : ℕ} {d : (_ : Finset ℕ) × Finset ℕ}
    (hd : d ∈ sigData (2 ^ (m - 1)) r) :
    ∑ x ∈ elemSet g (2 ^ (m - 1)) d, x = sVal g d := by
  classical
  obtain ⟨⟨hU, hc⟩, hT⟩ := mem_sigData.mp hd
  obtain ⟨hinj₁, hinj₂, hdisj⟩ := embed_inj_disj hm hg hU hT
  rw [elemSet, Finset.sum_union hdisj, Finset.sum_image hinj₁, Finset.sum_image hinj₂]
  have hneg : ∀ j ∈ d.1 \ d.2, g ^ (j + 2 ^ (m - 1)) = -(g ^ j) := by
    intro j _
    rw [pow_add, pow_half_eq_neg_one hm hg, mul_neg, mul_one]
  rw [Finset.sum_congr rfl hneg, Finset.sum_neg_distrib, ← sub_eq_add_neg]
  rfl

end Embed

/-! ### The main theorem -/

/-- **[KKH26] Lemma 1.** Let `g ∈ F_p` be a primitive `2^m`-th root of unity (so
`G = {g^i : i < 2^m}` is the multiplicative subgroup of order `s = 2^m`), and suppose
`p > s^{s/2}`.  Then for every `r ≤ s/2`, the set of sums of `r` distinct elements of `G`
has at least `2^r · (s/2).choose r` elements. -/
theorem kkh26_lemma1 {p : ℕ} [Fact p.Prime] {m : ℕ} (hm : 1 ≤ m) {g : ZMod p}
    (hg : IsPrimitiveRoot g (2 ^ m)) (hp : ((2 : ℕ) ^ m) ^ 2 ^ (m - 1) < p)
    {r : ℕ} (hr : r ≤ 2 ^ (m - 1)) :
    2 ^ r * (2 ^ (m - 1)).choose r ≤
      ((((range (2 ^ m)).image (fun i => g ^ i)).powersetCard r).image
        fun S => ∑ x ∈ S, x).card := by
  classical
  have hinj : Set.InjOn (sVal g) (sigData (2 ^ (m - 1)) r) := sVal_injOn hm hg hp hr
  have hcard : ((sigData (2 ^ (m - 1)) r).image (sVal g)).card
      = 2 ^ r * (2 ^ (m - 1)).choose r := by
    rw [Finset.card_image_of_injOn hinj, card_sigData]
  have hsub : (sigData (2 ^ (m - 1)) r).image (sVal g) ⊆
      (((range (2 ^ m)).image (fun i => g ^ i)).powersetCard r).image
        fun S => ∑ x ∈ S, x := by
    intro x hx
    obtain ⟨d, hd, rfl⟩ := Finset.mem_image.mp hx
    refine Finset.mem_image.mpr ⟨elemSet g (2 ^ (m - 1)) d, ?_, elemSet_sum hm hg hd⟩
    exact mem_powersetCard.mpr ⟨elemSet_subset hm hd, elemSet_card hm hg hd⟩
  calc 2 ^ r * (2 ^ (m - 1)).choose r
      = ((sigData (2 ^ (m - 1)) r).image (sVal g)).card := hcard.symm
    _ ≤ _ := Finset.card_le_card hsub

/-! ### The divisibility route (issue #334, [KKH26] Lemma 2 wiring)

The size hypothesis `p > s^{s/2}` enters the chain above at exactly one point: it forces the
nonzero resultant `N = Res_ℤ(R, Φ_{2^m})` (of absolute value `≤ s^{s/2}` by
`natAbs_resultant_cyclotomic_le`) to satisfy `|N| < p`, so `p ∤ N`.  The lemmas below factor
the proof through that divisibility statement instead, so that [KKH26] Lemma 2's good prime
`p = Θ(n^β)` (supplied conditionally by `kkh26_good_prime_of_TZ` in `KKH26ThornerZaman.lean`)
can drive the same separation argument: `not_dvd_resultant_of_l1On_pow_lt` is the bridge
"size ⟹ not-dvd", `not_isRoot_of_not_dvd_resultant` is the non-vanishing core under the
divisibility hypothesis (it only needs the mild `‖R‖₁ < p` to keep the leading coefficient
alive mod `p`), `collisionResultant` names the integer family indexed by pairs of signed
data, and `sVal_injOn_of_not_dvd` / `kkh26_lemma1_of_not_dvd` are the generalized
injectivity and count.  The original statements above are untouched. -/

/-- **Size ⟹ not-dvd bridge.**  The explicit-threshold hypothesis of
`not_isRoot_of_l1On_pow_lt` already implies that `p` divides no collision resultant: the
resultant is nonzero (Loop52 pillars) and of absolute value `< p` (archimedean bound). -/
theorem not_dvd_resultant_of_l1On_pow_lt {p : ℕ} [Fact p.Prime] {m : ℕ} (hm : 1 ≤ m)
    {R : Polynomial ℤ} (hR0 : R ≠ 0) (hdeg : R.natDegree < 2 ^ (m - 1))
    (hp : l1On (2 ^ (m - 1)) R ^ 2 ^ (m - 1) < p) :
    ¬ (p : ℤ) ∣ Polynomial.resultant R (cyclotomic (2 ^ m) ℤ) := by
  intro hdvd
  have hne : Polynomial.resultant R (cyclotomic (2 ^ m) ℤ) ≠ 0 :=
    resultant_int_ne_zero_of_isCoprime_rat _ _ (diff_coprime_cyclotomic_rat hm R hdeg hR0)
  have hle : p ≤ (Polynomial.resultant R (cyclotomic (2 ^ m) ℤ)).natAbs := by
    have h2 := Int.natAbs_dvd_natAbs.mpr hdvd
    exact Nat.le_of_dvd (Int.natAbs_pos.mpr hne) (by simpa using h2)
  have hub := natAbs_resultant_cyclotomic_le hm R hdeg
  omega

/-- **Non-vanishing at a primitive root, divisibility form** (issue #334).  If `p` does not
divide `Res_ℤ(R, Φ_{2^m})` — instead of the size hypothesis `‖R‖₁^{2^{m-1}} < p` — then `R`
has no root at a primitive `2^m`-th root of unity `g ∈ F_p`.  The residual hypothesis
`‖R‖₁ < p` only keeps the leading coefficient of `R` alive mod `p` (so the Loop52 resultant
pillar applies); it is far weaker than the original threshold. -/
theorem not_isRoot_of_not_dvd_resultant {p : ℕ} [Fact p.Prime] {m : ℕ}
    {g : ZMod p} (hg : IsPrimitiveRoot g (2 ^ m))
    {R : Polynomial ℤ} (hR0 : R ≠ 0) (hdeg : R.natDegree < 2 ^ (m - 1))
    (hl1 : l1On (2 ^ (m - 1)) R < p)
    (hndvd : ¬ (p : ℤ) ∣ Polynomial.resultant R (cyclotomic (2 ^ m) ℤ)) :
    ¬ (R.map (Int.castRingHom (ZMod p))).IsRoot g := by
  intro hroot
  -- the leading coefficient of `R` survives mod `p`
  have hlcR : ((R.leadingCoeff : ℤ) : ZMod p) ≠ 0 := by
    intro h0
    have hdvd : (p : ℤ) ∣ R.leadingCoeff := by
      rwa [ZMod.intCast_zmod_eq_zero_iff_dvd] at h0
    have hlcne : R.leadingCoeff ≠ 0 := leadingCoeff_ne_zero.mpr hR0
    have h1 : p ≤ R.leadingCoeff.natAbs := by
      have h2 := Int.natAbs_dvd_natAbs.mpr hdvd
      simpa using Nat.le_of_dvd (Int.natAbs_pos.mpr hlcne) (by simpa using h2)
    have h2 : R.leadingCoeff.natAbs ≤ l1On (2 ^ (m - 1)) R :=
      natAbs_leadingCoeff_le_l1On hdeg
    omega
  -- `Φ` is monic, so its leading coefficient survives as well
  have hΦmonic : (cyclotomic (2 ^ m) ℤ).Monic := cyclotomic.monic _ ℤ
  have hlcΦ : (((cyclotomic (2 ^ m) ℤ).leadingCoeff : ℤ) : ZMod p) ≠ 0 := by
    rw [hΦmonic.leadingCoeff]
    simp
  -- `g` is a common root of `R` and `Φ` mod `p`, so `p ∣ Res` — contradiction
  have hΦroot : ((cyclotomic (2 ^ m) ℤ).map (Int.castRingHom (ZMod p))).IsRoot g := by
    rw [map_cyclotomic_int]
    exact hg.isRoot_cyclotomic (by positivity)
  exact hndvd (prime_dvd_resultant_of_common_root R (cyclotomic (2 ^ m) ℤ)
    hlcR hlcΦ hroot hΦroot)

/-- **The collision resultant** of a pair of signed data — the integer
`N(d₁, d₂) = Res_ℤ(P_{d₁} − P_{d₂}, Φ_{2^m})` that the size route of
`not_isRoot_of_l1On_pow_lt` bounds internally, exposed as a definition so that the
[TZ24] good prime of `KKH26ThornerZaman.lean` can be required to divide none of them. -/
noncomputable def collisionResultant (m : ℕ) (d₁ d₂ : (_ : Finset ℕ) × Finset ℕ) : ℤ :=
  Polynomial.resultant (sumPoly d₁.1 d₁.2 - sumPoly d₂.1 d₂.2) (cyclotomic (2 ^ m) ℤ)

/-- Collision resultants of *distinct* signed data are nonzero (char-0 distinctness of
sum-polynomials + irreducibility of `Φ_{2^m}` over `ℚ`, the Loop52 pillars). -/
theorem collisionResultant_ne_zero {m r : ℕ} (hm : 1 ≤ m)
    {d₁ d₂ : (_ : Finset ℕ) × Finset ℕ}
    (hd₁ : d₁ ∈ sigData (2 ^ (m - 1)) r) (hd₂ : d₂ ∈ sigData (2 ^ (m - 1)) r)
    (hne : d₁ ≠ d₂) : collisionResultant m d₁ d₂ ≠ 0 := by
  obtain ⟨U₁, T₁⟩ := d₁
  obtain ⟨U₂, T₂⟩ := d₂
  obtain ⟨⟨hU₁, _⟩, hT₁⟩ := mem_sigData.mp hd₁
  obtain ⟨⟨hU₂, _⟩, hT₂⟩ := mem_sigData.mp hd₂
  have hhalf : 0 < 2 ^ (m - 1) := by positivity
  have hR0 : sumPoly U₁ T₁ - sumPoly U₂ T₂ ≠ 0 := by
    intro h0
    obtain ⟨hU, hT⟩ := sumPoly_inj hT₁ hT₂ (sub_eq_zero.mp h0)
    subst hU; subst hT
    exact hne rfl
  have hdegR : (sumPoly U₁ T₁ - sumPoly U₂ T₂).natDegree < 2 ^ (m - 1) :=
    lt_of_le_of_lt (Polynomial.natDegree_sub_le _ _)
      (max_lt (sumPoly_natDegree_lt hhalf hU₁ hT₁) (sumPoly_natDegree_lt hhalf hU₂ hT₂))
  exact resultant_int_ne_zero_of_isCoprime_rat _ _
    (diff_coprime_cyclotomic_rat hm _ hdegR hR0)

/-- Collision resultants are bounded by `s^{s/2} = (2^m)^{2^{m-1}}` in absolute value
(the archimedean bound applied to the difference polynomial, whose window ℓ¹-norm is
`≤ 2r ≤ 2^m`). -/
theorem natAbs_collisionResultant_le {m r : ℕ} (hm : 1 ≤ m)
    {d₁ d₂ : (_ : Finset ℕ) × Finset ℕ}
    (hd₁ : d₁ ∈ sigData (2 ^ (m - 1)) r) (hd₂ : d₂ ∈ sigData (2 ^ (m - 1)) r)
    (hr : r ≤ 2 ^ (m - 1)) :
    (collisionResultant m d₁ d₂).natAbs ≤ ((2 : ℕ) ^ m) ^ 2 ^ (m - 1) := by
  obtain ⟨U₁, T₁⟩ := d₁
  obtain ⟨U₂, T₂⟩ := d₂
  obtain ⟨⟨hU₁, hc₁⟩, hT₁⟩ := mem_sigData.mp hd₁
  obtain ⟨⟨hU₂, hc₂⟩, hT₂⟩ := mem_sigData.mp hd₂
  have hhalf : 0 < 2 ^ (m - 1) := by positivity
  have hdegR : (sumPoly U₁ T₁ - sumPoly U₂ T₂).natDegree < 2 ^ (m - 1) :=
    lt_of_le_of_lt (Polynomial.natDegree_sub_le _ _)
      (max_lt (sumPoly_natDegree_lt hhalf hU₁ hT₁) (sumPoly_natDegree_lt hhalf hU₂ hT₂))
  have hl1 : l1On (2 ^ (m - 1)) (sumPoly U₁ T₁ - sumPoly U₂ T₂) ≤ 2 * r := by
    have h := l1On_sub_le (2 ^ (m - 1)) (sumPoly U₁ T₁) (sumPoly U₂ T₂)
    rw [l1On_sumPoly hU₁ hT₁, l1On_sumPoly hU₂ hT₂, hc₁, hc₂] at h
    omega
  have h2r : 2 * r ≤ 2 ^ m := by
    have hsum : 2 ^ (m - 1) * 2 = 2 ^ m := by
      rw [← pow_succ, Nat.sub_add_cancel hm]
    omega
  have hub := natAbs_resultant_cyclotomic_le hm (sumPoly U₁ T₁ - sumPoly U₂ T₂) hdegR
  exact le_trans hub (Nat.pow_le_pow_left (le_trans hl1 h2r) _)

/-- **Landau collision-resultant bound.**  For signed `r`-data, the Mahler/Landau
surface plus the coefficient-energy lemma gives
`|collisionResultant| ≤ 2^(2^(m-1)-1) * sqrt(8r)^(2^(m-1))`.  For `m = 6, r = 5`,
this is far below the certified μ=6 prime budget and is the reusable archimedean
handoff requested by the literal-pin route. -/
theorem natAbs_collisionResultant_le_landau {m r : ℕ} (hm : 1 ≤ m)
    {d₁ d₂ : (_ : Finset ℕ) × Finset ℕ}
    (hd₁ : d₁ ∈ sigData (2 ^ (m - 1)) r) (hd₂ : d₂ ∈ sigData (2 ^ (m - 1)) r) :
    ((collisionResultant m d₁ d₂).natAbs : ℝ)
      ≤ (2 : ℝ) ^ (2 ^ (m - 1) - 1) * (√(8 * r : ℝ)) ^ (2 ^ (m - 1)) := by
  obtain ⟨U₁, T₁⟩ := d₁
  obtain ⟨U₂, T₂⟩ := d₂
  obtain ⟨⟨hU₁, hc₁⟩, hT₁⟩ := mem_sigData.mp hd₁
  obtain ⟨⟨hU₂, hc₂⟩, hT₂⟩ := mem_sigData.mp hd₂
  have hhalf : 0 < 2 ^ (m - 1) := by positivity
  have hdegR : (sumPoly U₁ T₁ - sumPoly U₂ T₂).natDegree < 2 ^ (m - 1) :=
    lt_of_le_of_lt (Polynomial.natDegree_sub_le _ _)
      (max_lt (sumPoly_natDegree_lt hhalf hU₁ hT₁) (sumPoly_natDegree_lt hhalf hU₂ hT₂))
  have hbase := natAbs_resultant_cyclotomic_le_landau hm
    (sumPoly U₁ T₁ - sumPoly U₂ T₂) hdegR
  have henergy := sum_sq_norm_coeff_sumPoly_sub_le hT₁ hT₂ hc₁ hc₂
  have hsqrt :
      √(∑ i ∈ ((sumPoly U₁ T₁ - sumPoly U₂ T₂).map (Int.castRingHom ℂ)).support,
          ‖((sumPoly U₁ T₁ - sumPoly U₂ T₂).map (Int.castRingHom ℂ)).coeff i‖ ^ 2)
        ≤ √(8 * r : ℝ) := Real.sqrt_le_sqrt henergy
  have hpow :
      (√(∑ i ∈ ((sumPoly U₁ T₁ - sumPoly U₂ T₂).map (Int.castRingHom ℂ)).support,
          ‖((sumPoly U₁ T₁ - sumPoly U₂ T₂).map (Int.castRingHom ℂ)).coeff i‖ ^ 2))
          ^ (2 ^ (m - 1))
        ≤ (√(8 * r : ℝ)) ^ (2 ^ (m - 1)) :=
    pow_le_pow_left₀ (Real.sqrt_nonneg _) hsqrt _
  refine le_trans ?_ (mul_le_mul_of_nonneg_left hpow (pow_nonneg (by norm_num) _))
  simpa [collisionResultant] using hbase

/-- The old explicit-threshold hypothesis implies the new divisibility hypothesis: above
`p > s^{s/2}` no collision resultant can be divisible by `p` (it is nonzero of absolute
value `≤ s^{s/2} < p`).  Hence the size route is a special case of the dvd route. -/
theorem not_dvd_collisionResultant_of_lt {p : ℕ} [Fact p.Prime] {m r : ℕ} (hm : 1 ≤ m)
    (hp : ((2 : ℕ) ^ m) ^ 2 ^ (m - 1) < p) (hr : r ≤ 2 ^ (m - 1))
    {d₁ d₂ : (_ : Finset ℕ) × Finset ℕ}
    (hd₁ : d₁ ∈ sigData (2 ^ (m - 1)) r) (hd₂ : d₂ ∈ sigData (2 ^ (m - 1)) r)
    (hne : d₁ ≠ d₂) : ¬ (p : ℤ) ∣ collisionResultant m d₁ d₂ := by
  intro hdvd
  have h1 : p ≤ (collisionResultant m d₁ d₂).natAbs :=
    Nat.le_of_dvd (Int.natAbs_pos.mpr (collisionResultant_ne_zero hm hd₁ hd₂ hne))
      (by simpa using Int.natAbs_dvd_natAbs.mpr hdvd)
  have h2 := natAbs_collisionResultant_le hm hd₁ hd₂ hr
  omega

/-- **Absolute-size handoff for the divisibility route.**  To discharge the named
`collisionResultant` nondivisibility hypothesis it is enough to prove the relevant resultant
has absolute value strictly below the prime.  This is the endpoint a sharper archimedean
bound, such as a Mahler/Landau estimate, should feed. -/
theorem not_dvd_collisionResultant_of_natAbs_lt {p : ℕ} {m r : ℕ} (hm : 1 ≤ m)
    {d₁ d₂ : (_ : Finset ℕ) × Finset ℕ}
    (hd₁ : d₁ ∈ sigData (2 ^ (m - 1)) r) (hd₂ : d₂ ∈ sigData (2 ^ (m - 1)) r)
    (hne : d₁ ≠ d₂) (hlt : (collisionResultant m d₁ d₂).natAbs < p) :
    ¬ (p : ℤ) ∣ collisionResultant m d₁ d₂ := by
  intro hdvd
  have hle : p ≤ (collisionResultant m d₁ d₂).natAbs :=
    Nat.le_of_dvd (Int.natAbs_pos.mpr (collisionResultant_ne_zero hm hd₁ hd₂ hne))
      (by simpa using Int.natAbs_dvd_natAbs.mpr hdvd)
  omega

/-- Family version of `not_dvd_collisionResultant_of_natAbs_lt`, matching the hypothesis
shape consumed by `kkh26_lemma1_of_not_dvd`. -/
theorem collisionResultant_not_dvd_of_forall_natAbs_lt {p : ℕ} {m r : ℕ} (hm : 1 ≤ m)
    (hbound : ∀ d₁ ∈ sigData (2 ^ (m - 1)) r, ∀ d₂ ∈ sigData (2 ^ (m - 1)) r,
      d₁ ≠ d₂ → (collisionResultant m d₁ d₂).natAbs < p) :
    ∀ d₁ ∈ sigData (2 ^ (m - 1)) r, ∀ d₂ ∈ sigData (2 ^ (m - 1)) r,
      d₁ ≠ d₂ → ¬ (p : ℤ) ∣ collisionResultant m d₁ d₂ := by
  intro d₁ hd₁ d₂ hd₂ hne
  exact not_dvd_collisionResultant_of_natAbs_lt hm hd₁ hd₂ hne
    (hbound d₁ hd₁ d₂ hd₂ hne)

/-- **Injectivity of signed sums, divisibility form** (issue #334).  If `p > 2^m` and `p`
divides no collision resultant of distinct signed data, then distinct signed data give
distinct values at the primitive root — the conclusion of `sVal_injOn` without the
superpolynomial threshold `p > s^{s/2}`. -/
theorem sVal_injOn_of_not_dvd {p : ℕ} [Fact p.Prime] {m : ℕ} (hm : 1 ≤ m)
    {g : ZMod p} (hg : IsPrimitiveRoot g (2 ^ m))
    (hpl : (2 : ℕ) ^ m < p) {r : ℕ} (hr : r ≤ 2 ^ (m - 1))
    (hndvd : ∀ d₁ ∈ sigData (2 ^ (m - 1)) r, ∀ d₂ ∈ sigData (2 ^ (m - 1)) r,
      d₁ ≠ d₂ → ¬ (p : ℤ) ∣ collisionResultant m d₁ d₂) :
    Set.InjOn (sVal g) (sigData (2 ^ (m - 1)) r) := by
  classical
  intro d₁ hd₁ d₂ hd₂ heq
  by_contra hne
  have hnd : ¬ (p : ℤ) ∣ collisionResultant m d₁ d₂ := hndvd d₁ hd₁ d₂ hd₂ hne
  obtain ⟨U₁, T₁⟩ := d₁
  obtain ⟨U₂, T₂⟩ := d₂
  obtain ⟨⟨hU₁, hc₁⟩, hT₁⟩ := mem_sigData.mp hd₁
  obtain ⟨⟨hU₂, hc₂⟩, hT₂⟩ := mem_sigData.mp hd₂
  have hhalf : 0 < 2 ^ (m - 1) := by positivity
  have hR0 : sumPoly U₁ T₁ - sumPoly U₂ T₂ ≠ 0 := by
    intro h0
    obtain ⟨hU, hT⟩ := sumPoly_inj hT₁ hT₂ (sub_eq_zero.mp h0)
    subst hU; subst hT
    exact hne rfl
  -- the collision polynomial has `g` as a root
  have hroot : ((sumPoly U₁ T₁ - sumPoly U₂ T₂).map
      (Int.castRingHom (ZMod p))).IsRoot g := by
    rw [IsRoot.def, Polynomial.map_sub, eval_sub, sub_eq_zero,
      ← sVal_eq_eval g U₁ T₁, ← sVal_eq_eval g U₂ T₂]
    exact heq
  -- degree and ℓ¹ bookkeeping
  have hdegR : (sumPoly U₁ T₁ - sumPoly U₂ T₂).natDegree < 2 ^ (m - 1) :=
    lt_of_le_of_lt (Polynomial.natDegree_sub_le _ _)
      (max_lt (sumPoly_natDegree_lt hhalf hU₁ hT₁) (sumPoly_natDegree_lt hhalf hU₂ hT₂))
  have hl1 : l1On (2 ^ (m - 1)) (sumPoly U₁ T₁ - sumPoly U₂ T₂) ≤ 2 * r := by
    have h := l1On_sub_le (2 ^ (m - 1)) (sumPoly U₁ T₁) (sumPoly U₂ T₂)
    rw [l1On_sumPoly hU₁ hT₁, l1On_sumPoly hU₂ hT₂, hc₁, hc₂] at h
    omega
  have h2r : 2 * r ≤ 2 ^ m := by
    have hsum : 2 ^ (m - 1) * 2 = 2 ^ m := by
      rw [← pow_succ, Nat.sub_add_cancel hm]
    omega
  have hl1lt : l1On (2 ^ (m - 1)) (sumPoly U₁ T₁ - sumPoly U₂ T₂) < p := by omega
  have hnd' : ¬ (p : ℤ) ∣ Polynomial.resultant (sumPoly U₁ T₁ - sumPoly U₂ T₂)
      (cyclotomic (2 ^ m) ℤ) := hnd
  exact not_isRoot_of_not_dvd_resultant hg hR0 hdegR hl1lt hnd' hroot

/-- **[KKH26] Lemma 1, divisibility form** (issue #334).  The count of `kkh26_lemma1` under
the hypothesis that `p > 2^m` divides no collision resultant of distinct signed data — the
form fed by the [TZ24] good prime `p = Θ(n^β)` of `kkh26_good_prime_of_TZ`
(`KKH26ThornerZaman.lean`) in place of the superpolynomial threshold `p > s^{s/2}`. -/
theorem kkh26_lemma1_of_not_dvd {p : ℕ} [Fact p.Prime] {m : ℕ} (hm : 1 ≤ m) {g : ZMod p}
    (hg : IsPrimitiveRoot g (2 ^ m)) (hpl : (2 : ℕ) ^ m < p)
    {r : ℕ} (hr : r ≤ 2 ^ (m - 1))
    (hndvd : ∀ d₁ ∈ sigData (2 ^ (m - 1)) r, ∀ d₂ ∈ sigData (2 ^ (m - 1)) r,
      d₁ ≠ d₂ → ¬ (p : ℤ) ∣ collisionResultant m d₁ d₂) :
    2 ^ r * (2 ^ (m - 1)).choose r ≤
      ((((range (2 ^ m)).image (fun i => g ^ i)).powersetCard r).image
        fun S => ∑ x ∈ S, x).card := by
  classical
  have hinj : Set.InjOn (sVal g) (sigData (2 ^ (m - 1)) r) :=
    sVal_injOn_of_not_dvd hm hg hpl hr hndvd
  have hcard : ((sigData (2 ^ (m - 1)) r).image (sVal g)).card
      = 2 ^ r * (2 ^ (m - 1)).choose r := by
    rw [Finset.card_image_of_injOn hinj, card_sigData]
  have hsub : (sigData (2 ^ (m - 1)) r).image (sVal g) ⊆
      (((range (2 ^ m)).image (fun i => g ^ i)).powersetCard r).image
        fun S => ∑ x ∈ S, x := by
    intro x hx
    obtain ⟨d, hd, rfl⟩ := Finset.mem_image.mp hx
    refine Finset.mem_image.mpr ⟨elemSet g (2 ^ (m - 1)) d, ?_, elemSet_sum hm hg hd⟩
    exact mem_powersetCard.mpr ⟨elemSet_subset hm hd, elemSet_card hm hg hd⟩
  calc 2 ^ r * (2 ^ (m - 1)).choose r
      = ((sigData (2 ^ (m - 1)) r).image (sVal g)).card := hcard.symm
    _ ≤ _ := Finset.card_le_card hsub

end ArkLib.ProximityGap.KKH26

/-! ## Axiom audit -/
namespace ArkLib.ProximityGap.KKH26

#print axioms cyclotomic_two_pow_eq_X_pow_add_one
#print axioms norm_eval_cyclotomic_two_pow_le
#print axioms norm_multiset_prod_map_le_prod
#print axioms multiset_prod_two_mul_pow_height
#print axioms natAbs_resultant_cyclotomic_le_mahler
#print axioms natAbs_resultant_cyclotomic_le_landau
#print axioms natAbs_resultant_cyclotomic_le
#print axioms sumPoly_coeff_natAbs_le_one
#print axioms sumPoly_sub_coeff_natAbs_le_two
#print axioms sum_sq_norm_coeff_sumPoly_sub_le
#print axioms not_isRoot_of_l1On_pow_lt
#print axioms sVal_injOn
#print axioms kkh26_lemma1
#print axioms not_dvd_resultant_of_l1On_pow_lt
#print axioms not_isRoot_of_not_dvd_resultant
#print axioms collisionResultant_ne_zero
#print axioms natAbs_collisionResultant_le
#print axioms natAbs_collisionResultant_le_landau
#print axioms not_dvd_collisionResultant_of_lt
#print axioms not_dvd_collisionResultant_of_natAbs_lt
#print axioms collisionResultant_not_dvd_of_forall_natAbs_lt
#print axioms sVal_injOn_of_not_dvd
#print axioms kkh26_lemma1_of_not_dvd

end ArkLib.ProximityGap.KKH26

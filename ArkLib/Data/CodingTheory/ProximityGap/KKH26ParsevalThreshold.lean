/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.KKH26SumsOfRootsOfUnity

/-!
# The Parseval threshold: halving the exponent of the KKH26 prime bound (issue #334, A3)

[KKH26] (ePrint 2026/782) Lemma 1 bounds the collision resultants
`Res(P − Q, Φ_{2^m})` through the per-conjugate ℓ¹ estimate `|R(ζ)| ≤ ‖R‖₁ ≤ 2r`
(in-tree: `natAbs_resultant_cyclotomic_le`), giving the prime threshold
`p > (2r)^{2^{m−1}} ≤ s^{s/2}` — superpolynomial in the domain size, which empties the
`ε* = 2^{−128}`, `|F| < 2^{256}` reach-table rows for `s ≥ 64`
(`probe_kkh_ceiling_numeric_reach.py`).

Hypothesis A3 of the issue #334 ledger asked whether the *true* resultant maxima are far
smaller.  The probe `probe_kkh26_resultant_maxima.py` measured them (exact at `s ∈ {8, 16}`,
sampled at `s = 32`) and pointed at the reason: per conjugate the values behave like an
ℓ² mean, not an ℓ¹ max.  That observation is a theorem — **Parseval + AM–GM**:

  `∑_{z^{2^m} = 1} |R(z)|² = 2^m · ‖R‖₂²`  (finite Fourier Parseval), and the resultant is
  a product over the `2^{m−1}` *primitive* roots only, so by AM–GM

  `|Res(R, Φ_{2^m})|² ≤ (2^m·‖R‖₂² / 2^{m−1})^{2^{m−1}} = (2·‖R‖₂²)^{2^{m−1}}`,

i.e. **`|Res(R, Φ_{2^m})| ≤ (2·‖R‖₂²)^{2^{m−2}}`** — the ℓ¹ exponent `2^{m−1}` is halved.
For collision differences `‖R‖₂² ≤ 4r` (coefficients in `{−2,…,2}`, ℓ¹ ≤ 2r), so the
threshold becomes `p > (8r)^{2^{m−2}}` — e.g. at `s = 64`, rate-pinned `r = 18`:
`2^{115}` instead of `2^{192}`, and the prize-parameter window
`(2^{115}, 2^{128 + log₂ count})` is **nonempty**: the `s = 64` rows of the reach table
open *unconditionally* (numeric verification: 80,623 probe checks, 0 violations;
`s = 128` remains closed and still needs the Thorner–Zaman route of
`KKH26PolyFieldCeiling.lean`).

## Main results

* `l2On` — the window ℓ² norm (sum of squared coefficients).
* `sum_normSq_eval_nthRoots` — finite Parseval over the full root-of-unity group.
* `multiset_prod_le_sum_div_card_pow` — unweighted AM–GM for multisets.
* `natAbs_resultant_cyclotomic_le_parseval` — **the halved-exponent resultant bound**.
* `natAbs_collisionResultant_le_parseval` — `|Res| ≤ (8r)^{2^{m−2}}` for collision pairs.
* `not_dvd_collisionResultant_of_parseval_lt`, `kkh26_lemma1_parseval` — the [KKH26]
  Lemma 1 distinct-sums count at the **Parseval threshold** `p > (8r)^{2^{m−2}}`
  (consuming the issue #334 divisibility route `kkh26_lemma1_of_not_dvd`).

The stratified count (`KKH26StratifiedSpread.lean`) admits the same upgrade (its collision
polynomials have ℓ¹ ≤ r₁ + r₂ and coefficients in `{−2,…,2}`, so `‖R‖₂² ≤ 2(r₁+r₂)`);
that wiring is left to a follow-up to keep this file focused on the diagonal chain.

## References

* [KKH26] D. Krachun, S. Kazanin, U. Haböck, *Failure of proximity gaps close to
  capacity*, ePrint 2026/782 (Lemma 1, inequality (3)).  Issue #334, hypothesis A3.
-/

namespace ArkLib.ProximityGap.KKH26

open Polynomial Finset

/-! ### The window ℓ² norm -/

/-- The window ℓ²-norm (squared): the sum of squared coefficient magnitudes over the
window `[0, n)`. -/
def l2On (n : ℕ) (f : Polynomial ℤ) : ℕ := ∑ j ∈ range n, (f.coeff j).natAbs ^ 2

/-- When every window coefficient has magnitude `≤ 2`, the ℓ² norm is at most twice the
ℓ¹ norm (`x² ≤ 2x` for `x ≤ 2`). -/
lemma l2On_le_two_mul_l1On {n : ℕ} {f : Polynomial ℤ}
    (h : ∀ j < n, (f.coeff j).natAbs ≤ 2) : l2On n f ≤ 2 * l1On n f := by
  unfold l2On l1On
  rw [Finset.mul_sum]
  refine Finset.sum_le_sum fun j hj => ?_
  have hb := h j (Finset.mem_range.mp hj)
  calc (f.coeff j).natAbs ^ 2 = (f.coeff j).natAbs * (f.coeff j).natAbs := pow_two _
    _ ≤ 2 * (f.coeff j).natAbs := Nat.mul_le_mul_right _ hb

/-! ### Unweighted AM–GM for multisets -/

/-- **Unweighted AM–GM for multisets of nonnegative reals**: the product is at most the
`n`-th power of the arithmetic mean. -/
lemma multiset_prod_le_sum_div_card_pow (s : Multiset ℝ) (h : ∀ x ∈ s, 0 ≤ x) :
    s.prod ≤ (s.sum / Multiset.card s) ^ (Multiset.card s) := by
  classical
  obtain rfl | hne := eq_or_ne s 0
  · simp
  set l := s.toList with hl
  have hlen : l.length = Multiset.card s := Multiset.length_toList s
  have hlen0 : l.length ≠ 0 := by
    rw [hlen]
    simpa [Multiset.card_eq_zero] using hne
  have hmem : ∀ i : Fin l.length, 0 ≤ l.get i := fun i =>
    h _ (by rw [← Multiset.mem_toList]; exact List.get_mem l i)
  -- pass to an indexed product over `Fin l.length`
  have hprod : s.prod = ∏ i : Fin l.length, l.get i := by
    rw [← Multiset.prod_toList, ← hl, ← List.prod_ofFn (f := l.get), List.ofFn_get]
  have hsum : s.sum = ∑ i : Fin l.length, l.get i := by
    rw [← Multiset.sum_toList, ← hl, ← List.sum_ofFn (f := l.get), List.ofFn_get]
  set n : ℕ := l.length with hn
  -- weighted AM–GM with uniform weights 1/n
  have hgm := Real.geom_mean_le_arith_mean_weighted (s := (Finset.univ : Finset (Fin n)))
    (w := fun _ => (n : ℝ)⁻¹) (z := fun i => l.get i)
    (fun _ _ => by positivity)
    (by
      rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
      field_simp)
    (fun i _ => hmem i)
  -- raise both sides to the `n`-th power
  have hG : (0 : ℝ) ≤ ∏ i : Fin n, l.get i ^ ((n : ℝ)⁻¹) :=
    Finset.prod_nonneg fun i _ => Real.rpow_nonneg (hmem i) _
  have hpow := pow_le_pow_left₀ hG hgm n
  have hlhs : (∏ i : Fin n, l.get i ^ ((n : ℝ)⁻¹)) ^ n = ∏ i : Fin n, l.get i := by
    rw [← Finset.prod_pow]
    refine Finset.prod_congr rfl fun i _ => ?_
    rw [← Real.rpow_natCast (l.get i ^ ((n : ℝ)⁻¹)) n, ← Real.rpow_mul (hmem i),
      inv_mul_cancel₀ (by exact_mod_cast hlen0), Real.rpow_one]
  have hrhs : ∑ i : Fin n, (n : ℝ)⁻¹ * l.get i = (∑ i : Fin n, l.get i) / n := by
    rw [← Finset.mul_sum]
    ring
  rw [hlhs, hrhs] at hpow
  rw [hprod, hsum, ← hlen]
  exact hpow

/-! ### Finite Parseval over the root-of-unity group -/

/-- Orthogonality: for a primitive `N`-th root `ζ` and `e : ℕ`, the sum `∑_{k<N} ζ^{ke}`
is `N` when `N ∣ e` and `0` otherwise. -/
lemma sum_pow_mul_eq {N : ℕ} {ζ : ℂ} (hζ : IsPrimitiveRoot ζ N) (e : ℕ) :
    ∑ k ∈ range N, ζ ^ (k * e) = if N ∣ e then (N : ℂ) else 0 := by
  have hsum : ∑ k ∈ range N, ζ ^ (k * e) = ∑ k ∈ range N, (ζ ^ e) ^ k := by
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [← pow_mul, mul_comm]
  rw [hsum]
  by_cases hdvd : N ∣ e
  · have h1 : ζ ^ e = 1 := (hζ.pow_eq_one_iff_dvd e).mpr hdvd
    simp [h1, if_pos hdvd]
  · have hne1 : ζ ^ e ≠ 1 := fun h => hdvd ((hζ.pow_eq_one_iff_dvd e).mp h)
    rw [if_neg hdvd, geom_sum_eq hne1]
    have hN1 : (ζ ^ e) ^ N = 1 := by
      rw [← pow_mul, mul_comm, pow_mul, hζ.pow_eq_one, one_pow]
    rw [hN1, sub_self, zero_div]

/-- The conjugate of a primitive root power: `conj (ζ^k) = ζ^{k(N−1)}`. -/
lemma conj_pow_primitiveRoot {N : ℕ} (hN : 1 < N) {ζ : ℂ} (hζ : IsPrimitiveRoot ζ N)
    (k : ℕ) : (starRingEnd ℂ) (ζ ^ k) = ζ ^ (k * (N - 1)) := by
  have hζ0 : ζ ≠ 0 := hζ.ne_zero (by omega)
  have hnorm : ‖ζ‖ = 1 := Complex.norm_eq_one_of_pow_eq_one hζ.pow_eq_one (by omega)
  have hconj : (starRingEnd ℂ) ζ = ζ ^ (N - 1) := by
    have hinv : ζ⁻¹ = ζ ^ (N - 1) := by
      refine inv_eq_of_mul_eq_one_right ?_
      rw [← pow_succ', Nat.sub_add_cancel (by omega : 1 ≤ N), hζ.pow_eq_one]
    rw [← Complex.inv_eq_conj hnorm, hinv]
  rw [map_pow, hconj, ← pow_mul, mul_comm (N - 1) k]

/-- The conjugate of an integer polynomial evaluated at `z` is its value at `conj z`. -/
lemma conj_eval_int_poly (f : Polynomial ℤ) (z : ℂ) :
    (starRingEnd ℂ) ((f.map (Int.castRingHom ℂ)).eval z)
      = (f.map (Int.castRingHom ℂ)).eval ((starRingEnd ℂ) z) := by
  rw [Polynomial.eval_map, Polynomial.eval_map, Polynomial.hom_eval₂]
  congr 1
  ext n
  simp

/-- **Finite Parseval over the `N`-th roots of unity**: for an integer polynomial of
degree `< N` and a primitive `N`-th root `ζ`,
`∑_{k<N} |R(ζ^k)|² = N · ‖R‖₂²` (squared norms via `Complex.normSq`). -/
theorem sum_normSq_eval_nthRoots {N : ℕ} (hN : 1 < N) {ζ : ℂ}
    (hζ : IsPrimitiveRoot ζ N) (f : Polynomial ℤ) (hdeg : f.natDegree < N) :
    ∑ k ∈ range N, Complex.normSq ((f.map (Int.castRingHom ℂ)).eval (ζ ^ k))
      = N * (l2On N f : ℝ) := by
  classical
  set ι : ℤ →+* ℂ := Int.castRingHom ℂ with hι
  set g : Polynomial ℂ := f.map ι with hg
  have hdegg : g.natDegree < N := by
    rw [hg, natDegree_map_eq_of_injective Int.cast_injective]; exact hdeg
  -- work in ℂ and descend by injectivity of the real embedding
  refine Complex.ofReal_injective ?_
  push_cast
  have hcast : ∀ k, ((Complex.normSq (g.eval (ζ ^ k)) : ℝ) : ℂ)
      = g.eval (ζ ^ k) * (starRingEnd ℂ) (g.eval (ζ ^ k)) := fun k =>
    (Complex.mul_conj (g.eval (ζ ^ k))).symm
  calc ∑ k ∈ range N, ((Complex.normSq (g.eval (ζ ^ k)) : ℝ) : ℂ)
      = ∑ k ∈ range N, g.eval (ζ ^ k) * g.eval (ζ ^ (k * (N - 1))) := by
        refine Finset.sum_congr rfl fun k _ => ?_
        rw [hcast k, conj_eval_int_poly, conj_pow_primitiveRoot hN hζ]
    _ = ∑ k ∈ range N, ∑ i ∈ range N, ∑ j ∈ range N,
          (f.coeff i : ℂ) * (f.coeff j : ℂ) * ζ ^ (k * (i + j * (N - 1))) := by
        refine Finset.sum_congr rfl fun k _ => ?_
        rw [Polynomial.eval_eq_sum_range' hdegg, Polynomial.eval_eq_sum_range' hdegg,
          Finset.sum_mul_sum]
        refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
        have hcoeff : ∀ t, g.coeff t = ((f.coeff t : ℤ) : ℂ) := fun t => by
          rw [hg, Polynomial.coeff_map]; rfl
        rw [hcoeff i, hcoeff j]
        have hpow : (ζ ^ k) ^ i * (ζ ^ (k * (N - 1))) ^ j
            = ζ ^ (k * (i + j * (N - 1))) := by
          rw [← pow_mul, ← pow_mul, ← pow_add]
          ring_nf
        rw [← hpow]
        ring
    _ = ∑ i ∈ range N, ∑ j ∈ range N,
          (f.coeff i : ℂ) * (f.coeff j : ℂ)
            * ∑ k ∈ range N, ζ ^ (k * (i + j * (N - 1))) := by
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun j _ => ?_
        rw [Finset.mul_sum]
    _ = ∑ i ∈ range N, (f.coeff i : ℂ) * (f.coeff i : ℂ) * N := by
        refine Finset.sum_congr rfl fun i hi => ?_
        rw [Finset.sum_eq_single i]
        · rw [sum_pow_mul_eq hζ, if_pos]
          refine ⟨i, ?_⟩
          have hms : i * (N - 1) = i * N - i := by rw [Nat.mul_sub, mul_one]
          have hle : i ≤ i * N := Nat.le_mul_of_pos_right i (by omega)
          rw [Nat.mul_comm N i]
          omega
        · intro j hj hne
          rw [sum_pow_mul_eq hζ, if_neg, mul_zero]
          intro hdvd
          have hiN := Finset.mem_range.mp hi
          have hjN := Finset.mem_range.mp hj
          -- N ∣ i + j(N−1) with i, j < N forces i = j
          obtain ⟨t, ht⟩ := hdvd
          have hms : j * (N - 1) = j * N - j := by rw [Nat.mul_sub, mul_one]
          have hjle : j ≤ j * N := Nat.le_mul_of_pos_right j (by omega)
          have hkey : i + j * N = N * t + j := by omega
          -- reduce mod N: i ≡ j (mod N), both < N
          have hmod : i % N = j % N := by
            have h1 : (i + j * N) % N = i % N := by
              simp [Nat.add_mul_mod_self_right]
            have h2 : (N * t + j) % N = j % N := by
              rw [Nat.mul_add_mod]
            rw [hkey, h2] at h1
            exact h1.symm
          rw [Nat.mod_eq_of_lt hiN, Nat.mod_eq_of_lt hjN] at hmod
          exact hne.elim (by omega)
        · intro hni
          exact absurd hi hni
    _ = (N : ℂ) * (l2On N f : ℂ) := by
        unfold l2On
        push_cast
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun i _ => ?_
        have h2 : (((f.coeff i).natAbs ^ 2 : ℕ) : ℤ) = (f.coeff i) ^ 2 := by
          rw [Nat.cast_pow, Int.natCast_natAbs, sq_abs]
        have habs : ((f.coeff i).natAbs : ℂ) ^ 2 = (f.coeff i : ℂ) ^ 2 := by
          have h3 := congrArg (fun z : ℤ => (z : ℂ)) h2
          push_cast at h3
          exact h3
        rw [habs]
        ring

/-! ### The halved-exponent resultant bound -/

private lemma totient_two_pow' {m : ℕ} (hm : 1 ≤ m) :
    Nat.totient (2 ^ m) = 2 ^ (m - 1) := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_lt hm
  rw [Nat.zero_add, Nat.totient_prime_pow_succ Nat.prime_two]
  simp

/-- **The Parseval resultant bound** (issue #334, hypothesis A3): for `R : ℤ[X]` of
degree `< 2^{m−1}`,

  `|Res_ℤ(R, Φ_{2^m})| ≤ (2·‖R‖₂²)^{2^{m−2}}`,

halving the exponent of the ℓ¹ bound `‖R‖₁^{2^{m−1}}` (`natAbs_resultant_cyclotomic_le`):
the resultant is a product over the `2^{m−1}` primitive roots, the squared factor sum is
controlled by Parseval over the *full* group of `2^m` roots, and AM–GM converts the sum
into the product bound. -/
theorem natAbs_resultant_cyclotomic_le_parseval {m : ℕ} (hm : 2 ≤ m) (R : Polynomial ℤ)
    (hdeg : R.natDegree < 2 ^ (m - 1)) :
    ((Polynomial.resultant R (cyclotomic (2 ^ m) ℤ)).natAbs : ℝ)
      ≤ (2 * (l2On (2 ^ (m - 1)) R : ℝ)) ^ 2 ^ (m - 2) := by
  classical
  have hm1 : 1 ≤ m := le_trans (by norm_num) hm
  set ι : ℤ →+* ℂ := Int.castRingHom ℂ with hι
  have hinj : Function.Injective ι := Int.cast_injective
  set Φ : Polynomial ℤ := cyclotomic (2 ^ m) ℤ with hΦdef
  set N : ℕ := 2 ^ m with hNdef
  have hN1 : 1 < N := by
    rw [hNdef]
    calc 1 < 2 := one_lt_two
      _ ≤ 2 ^ m := Nat.le_self_pow (by omega) 2
  -- a primitive N-th root of unity in ℂ
  obtain ⟨ζ, hζ⟩ : ∃ ζ : ℂ, IsPrimitiveRoot ζ N :=
    ⟨Complex.exp (2 * Real.pi * Complex.I / N),
      Complex.isPrimitiveRoot_exp N (by omega)⟩
  -- transport the resultant to ℂ and expand as a product over the roots of Φ
  have hswap : (Polynomial.resultant R Φ).natAbs = (Polynomial.resultant Φ R).natAbs := by
    rw [Polynomial.resultant_comm, Int.natAbs_mul, Int.natAbs_pow]
    simp
  have hdegΦ : (Φ.map ι).natDegree = Φ.natDegree := natDegree_map_eq_of_injective hinj _
  have hdegR : (R.map ι).natDegree = R.natDegree := natDegree_map_eq_of_injective hinj _
  have hmap : Polynomial.resultant (Φ.map ι) (R.map ι) = ι (Polynomial.resultant Φ R) := by
    rw [show Polynomial.resultant (Φ.map ι) (R.map ι)
          = Polynomial.resultant (Φ.map ι) (R.map ι) Φ.natDegree R.natDegree by
        rw [hdegΦ, hdegR],
      Polynomial.resultant_map_map]
  have hΦC : Φ.map ι = cyclotomic N ℂ := map_cyclotomic_int _ ℂ
  have hmonic : (Φ.map ι).Monic := (cyclotomic.monic _ ℤ).map ι
  have hsplits : (Φ.map ι).Splits := IsAlgClosed.splits _
  have hprod : Polynomial.resultant (Φ.map ι) (R.map ι)
      = (((Φ.map ι).roots).map (R.map ι).eval).prod := by
    have h := Polynomial.resultant_eq_prod_eval (Φ.map ι) (R.map ι)
      ((R.map ι).natDegree) le_rfl hsplits
    rwa [hmonic.leadingCoeff, one_pow, one_mul] at h
  set φc : ℕ := 2 ^ (m - 1) with hφdef
  have hcard : Multiset.card (Φ.map ι).roots = φc := by
    have h1 := hsplits.natDegree_eq_card_roots
    rw [← h1, hdegΦ, hΦdef, natDegree_cyclotomic, hNdef, hφdef, totient_two_pow' hm1]
  -- squared-norm product over the Φ-roots, bounded via AM–GM + Parseval
  set sq : Multiset ℝ := ((Φ.map ι).roots).map fun z =>
    Complex.normSq ((R.map ι).eval z) with hsq
  have hsq_nonneg : ∀ x ∈ sq, (0 : ℝ) ≤ x := by
    intro x hx
    obtain ⟨z, _, rfl⟩ := Multiset.mem_map.mp hx
    exact Complex.normSq_nonneg _
  have hsq_card : Multiset.card sq = φc := by rw [hsq, Multiset.card_map, hcard]
  -- the root multiset of Φ embeds in the N-th roots of unity
  have hroots_le : (Φ.map ι).roots ≤ Polynomial.nthRoots N (1 : ℂ) := by
    have hdvd : (Φ.map ι) ∣ (X ^ N - C (1 : ℂ)) := by
      rw [hΦC]
      simpa using cyclotomic.dvd_X_pow_sub_one N ℂ
    have hne : (X ^ N - C (1 : ℂ)) ≠ 0 := by
      intro h
      have := congrArg Polynomial.natDegree h
      rw [Polynomial.natDegree_X_pow_sub_C] at this
      simp at this
      omega
    simpa [Polynomial.nthRoots] using Polynomial.roots.le_of_dvd hne hdvd
  have hφle : φc ≤ N := by
    rw [hφdef, hNdef]
    exact Nat.pow_le_pow_right (by norm_num) (by omega)
  -- Parseval over the full group
  have hparseval := sum_normSq_eval_nthRoots hN1 hζ R (lt_of_lt_of_le hdeg hφle)
  -- sum over Φ-roots ≤ sum over the full group
  have hsum_le : sq.sum ≤ N * (l2On φc R : ℝ) := by
    have hmono : sq.sum ≤ ((Polynomial.nthRoots N (1 : ℂ)).map fun z =>
        Complex.normSq ((R.map ι).eval z)).sum := by
      obtain ⟨u, hu⟩ := Multiset.le_iff_exists_add.mp hroots_le
      rw [hsq, hu, Multiset.map_add, Multiset.sum_add]
      have : (0 : ℝ) ≤ (u.map fun z => Complex.normSq ((R.map ι).eval z)).sum :=
        Multiset.sum_nonneg fun x hx => by
          obtain ⟨z, _, rfl⟩ := Multiset.mem_map.mp hx
          exact Complex.normSq_nonneg _
      linarith
    -- enumerate the N-th roots by powers of ζ
    have henum : Polynomial.nthRoots N (1 : ℂ)
        = (Multiset.range N).map fun k => ζ ^ k * 1 := hζ.nthRoots_eq (one_pow N)
    have hgroup : ((Polynomial.nthRoots N (1 : ℂ)).map fun z =>
        Complex.normSq ((R.map ι).eval z)).sum
        = ∑ k ∈ range N, Complex.normSq ((R.map ι).eval (ζ ^ k)) := by
      rw [henum, Multiset.map_map]
      simp only [Function.comp, mul_one]
      rfl
    rw [hgroup] at hmono
    -- the window in the Parseval statement is N, but coeffs beyond deg vanish:
    -- l2On N R = l2On φc R since natDegree R < φc ≤ N
    have hl2eq : l2On N R = l2On φc R := by
      unfold l2On
      refine (Finset.sum_subset (Finset.range_subset_range.mpr hφle) fun x _ hx => ?_).symm
      rw [Finset.mem_range, not_lt] at hx
      have hc0 : R.coeff x = 0 := Polynomial.coeff_eq_zero_of_natDegree_lt
        (lt_of_lt_of_le hdeg hx)
      simp [hc0]
    rw [hparseval, hl2eq] at hmono
    exact hmono
  -- AM–GM
  have hAMGM := multiset_prod_le_sum_div_card_pow sq hsq_nonneg
  rw [hsq_card] at hAMGM
  have hφpos : (0 : ℝ) < φc := by positivity
  have hdivle : sq.sum / (φc : ℝ) ≤ 2 * (l2On φc R : ℝ) := by
    rw [div_le_iff₀ hφpos]
    calc sq.sum ≤ N * (l2On φc R : ℝ) := hsum_le
      _ = 2 * (l2On φc R : ℝ) * φc := by
          rw [hNdef, hφdef]
          have : (2 : ℝ) ^ m = 2 * 2 ^ (m - 1) := by
            rw [← pow_succ']
            congr 1
            omega
          push_cast
          rw [this]
          ring
  have hsum_div_nonneg : (0 : ℝ) ≤ sq.sum / (φc : ℝ) :=
    div_nonneg (Multiset.sum_nonneg hsq_nonneg) (le_of_lt hφpos)
  have hprod_le : sq.prod ≤ (2 * (l2On φc R : ℝ)) ^ φc :=
    le_trans hAMGM (pow_le_pow_left₀ hsum_div_nonneg hdivle φc)
  -- identify sq.prod with ‖Res‖²
  have hnorm_prod : ‖(((Φ.map ι).roots).map (R.map ι).eval).prod‖ ^ 2 = sq.prod := by
    rw [hsq]
    induction ((Φ.map ι).roots) using Multiset.induction_on with
    | empty => simp
    | cons a s ih =>
      rw [Multiset.map_cons, Multiset.map_cons, Multiset.prod_cons, Multiset.prod_cons,
        norm_mul, mul_pow, ih, Complex.normSq_eq_norm_sq]
  have hcast : ‖(ι (Polynomial.resultant Φ R) : ℂ)‖
      = ((Polynomial.resultant Φ R).natAbs : ℝ) := by
    rw [show (ι (Polynomial.resultant Φ R) : ℂ)
          = ((Polynomial.resultant Φ R : ℤ) : ℂ) from rfl]
    rw [Complex.norm_intCast, Nat.cast_natAbs]
    exact Int.cast_abs.symm
  have hsq_le : ((Polynomial.resultant Φ R).natAbs : ℝ) ^ 2
      ≤ (2 * (l2On φc R : ℝ)) ^ φc := by
    rw [← hcast, ← hmap, hprod, hnorm_prod]
    exact hprod_le
  -- take square roots: φc = 2 · 2^{m−2}
  have hφsplit : φc = 2 ^ (m - 2) * 2 := by
    rw [hφdef, ← pow_succ]
    congr 1
    omega
  have hbase_nonneg : (0 : ℝ) ≤ 2 * (l2On φc R : ℝ) := by positivity
  have hsq_le' : ((Polynomial.resultant Φ R).natAbs : ℝ) ^ 2
      ≤ ((2 * (l2On φc R : ℝ)) ^ 2 ^ (m - 2)) ^ 2 := by
    rw [← pow_mul, ← hφsplit]
    exact hsq_le
  have hfinal : ((Polynomial.resultant Φ R).natAbs : ℝ)
      ≤ (2 * (l2On φc R : ℝ)) ^ 2 ^ (m - 2) := by
    have h1 : (0 : ℝ) ≤ ((Polynomial.resultant Φ R).natAbs : ℝ) := Nat.cast_nonneg _
    have h2 : (0 : ℝ) ≤ (2 * (l2On φc R : ℝ)) ^ 2 ^ (m - 2) :=
      pow_nonneg hbase_nonneg _
    nlinarith [hsq_le']
  rw [show ((Polynomial.resultant R Φ).natAbs : ℝ)
      = ((Polynomial.resultant Φ R).natAbs : ℝ) by rw [hswap]]
  exact hfinal

/-! ### Collision-resultant consumers: the `(8r)^{2^{m−2}}` threshold -/

/-- Sum-polynomial coefficients have magnitude at most 1. -/
lemma sumPoly_coeff_natAbs_le_one (U T : Finset ℕ) (k : ℕ) :
    ((sumPoly U T).coeff k).natAbs ≤ 1 := by
  rw [sumPoly_coeff]
  split_ifs <;> simp

/-- **Parseval bound for collision resultants**: `|Res(P − Q, Φ_{2^m})| ≤ (8r)^{2^{m−2}}`
for signed data at `r` terms (the ℓ² norm of the difference is at most `4r`). -/
theorem natAbs_collisionResultant_le_parseval {m r : ℕ} (hm : 2 ≤ m)
    {d₁ d₂ : (_ : Finset ℕ) × Finset ℕ}
    (hd₁ : d₁ ∈ sigData (2 ^ (m - 1)) r) (hd₂ : d₂ ∈ sigData (2 ^ (m - 1)) r) :
    ((collisionResultant m d₁ d₂).natAbs : ℝ) ≤ ((8 * r : ℕ) : ℝ) ^ 2 ^ (m - 2) := by
  obtain ⟨U₁, T₁⟩ := d₁
  obtain ⟨U₂, T₂⟩ := d₂
  obtain ⟨⟨hU₁, hc₁⟩, hT₁⟩ := mem_sigData.mp hd₁
  obtain ⟨⟨hU₂, hc₂⟩, hT₂⟩ := mem_sigData.mp hd₂
  have hm1 : 1 ≤ m := by omega
  have hhalf : 0 < 2 ^ (m - 1) := by positivity
  set R : Polynomial ℤ := sumPoly U₁ T₁ - sumPoly U₂ T₂ with hR
  have hdegR : R.natDegree < 2 ^ (m - 1) :=
    lt_of_le_of_lt (Polynomial.natDegree_sub_le _ _)
      (max_lt (sumPoly_natDegree_lt hhalf hU₁ hT₁) (sumPoly_natDegree_lt hhalf hU₂ hT₂))
  have hcoeff2 : ∀ j < 2 ^ (m - 1), (R.coeff j).natAbs ≤ 2 := by
    intro j _
    rw [hR, Polynomial.coeff_sub]
    calc ((sumPoly U₁ T₁).coeff j - (sumPoly U₂ T₂).coeff j).natAbs
        ≤ ((sumPoly U₁ T₁).coeff j).natAbs + ((sumPoly U₂ T₂).coeff j).natAbs :=
          Int.natAbs_sub_le _ _
      _ ≤ 1 + 1 := Nat.add_le_add (sumPoly_coeff_natAbs_le_one _ _ _)
          (sumPoly_coeff_natAbs_le_one _ _ _)
      _ = 2 := rfl
  have hl1 : l1On (2 ^ (m - 1)) R ≤ 2 * r := by
    have h := l1On_sub_le (2 ^ (m - 1)) (sumPoly U₁ T₁) (sumPoly U₂ T₂)
    rw [l1On_sumPoly hU₁ hT₁, l1On_sumPoly hU₂ hT₂, hc₁, hc₂] at h
    rw [hR]
    omega
  have hl2 : l2On (2 ^ (m - 1)) R ≤ 4 * r :=
    le_trans (l2On_le_two_mul_l1On hcoeff2) (by omega)
  have hP := natAbs_resultant_cyclotomic_le_parseval hm R hdegR
  calc ((collisionResultant m ⟨U₁, T₁⟩ ⟨U₂, T₂⟩).natAbs : ℝ)
      ≤ (2 * (l2On (2 ^ (m - 1)) R : ℝ)) ^ 2 ^ (m - 2) := by
        show ((Polynomial.resultant (sumPoly U₁ T₁ - sumPoly U₂ T₂)
            (cyclotomic (2 ^ m) ℤ)).natAbs : ℝ) ≤ _
        rw [← hR]
        exact hP
    _ ≤ ((8 * r : ℕ) : ℝ) ^ 2 ^ (m - 2) := by
        refine pow_le_pow_left₀ (by positivity) ?_ _
        push_cast
        have : (l2On (2 ^ (m - 1)) R : ℝ) ≤ 4 * r := by exact_mod_cast hl2
        linarith

/-- Above the **Parseval threshold** `p > (8r)^{2^{m−2}}`, no collision resultant of
distinct signed data is divisible by `p`. -/
theorem not_dvd_collisionResultant_of_parseval_lt {p : ℕ} [Fact p.Prime] {m r : ℕ}
    (hm : 2 ≤ m) (hp : (8 * r) ^ 2 ^ (m - 2) < p)
    {d₁ d₂ : (_ : Finset ℕ) × Finset ℕ}
    (hd₁ : d₁ ∈ sigData (2 ^ (m - 1)) r) (hd₂ : d₂ ∈ sigData (2 ^ (m - 1)) r)
    (hne : d₁ ≠ d₂) : ¬ (p : ℤ) ∣ collisionResultant m d₁ d₂ := by
  intro hdvd
  have hm1 : 1 ≤ m := by omega
  have h1 : p ≤ (collisionResultant m d₁ d₂).natAbs :=
    Nat.le_of_dvd (Int.natAbs_pos.mpr (collisionResultant_ne_zero hm1 hd₁ hd₂ hne))
      (by simpa using Int.natAbs_dvd_natAbs.mpr hdvd)
  have h2 := natAbs_collisionResultant_le_parseval hm hd₁ hd₂
  have h2' : (collisionResultant m d₁ d₂).natAbs ≤ (8 * r) ^ 2 ^ (m - 2) := by
    exact_mod_cast h2
  omega

/-- **[KKH26] Lemma 1 at the Parseval threshold** (issue #334, A3 resolution):
the `2^r·C(2^{m−1}, r)` distinct-sums count holds for every prime
`p > max(2^m, (8r)^{2^{m−2}})` — replacing the superpolynomial `p > (2^m)^{2^{m−1}}`
of `kkh26_lemma1` by a bound with **half the exponent**, which renders the
`ε* = 2^{−128}`, `|F| < 2^{256}` reach-table rows at `s = 64` nonempty
*unconditionally* (no Thorner–Zaman input; see the module docstring numerics). -/
theorem kkh26_lemma1_parseval {p : ℕ} [Fact p.Prime] {m : ℕ} (hm : 2 ≤ m) {g : ZMod p}
    (hg : IsPrimitiveRoot g (2 ^ m)) (hpl : (2 : ℕ) ^ m < p)
    {r : ℕ} (hr : r ≤ 2 ^ (m - 1))
    (hp : (8 * r) ^ 2 ^ (m - 2) < p) :
    2 ^ r * (2 ^ (m - 1)).choose r ≤
      ((((range (2 ^ m)).image (fun i => g ^ i)).powersetCard r).image
        fun S => ∑ x ∈ S, x).card :=
  kkh26_lemma1_of_not_dvd (by omega) hg hpl hr
    (fun d₁ hd₁ d₂ hd₂ hne =>
      not_dvd_collisionResultant_of_parseval_lt hm hp hd₁ hd₂ hne)

end ArkLib.ProximityGap.KKH26

/-! ## Axiom audit -/
#print axioms ArkLib.ProximityGap.KKH26.multiset_prod_le_sum_div_card_pow
#print axioms ArkLib.ProximityGap.KKH26.sum_normSq_eval_nthRoots
#print axioms ArkLib.ProximityGap.KKH26.natAbs_resultant_cyclotomic_le_parseval
#print axioms ArkLib.ProximityGap.KKH26.natAbs_collisionResultant_le_parseval
#print axioms ArkLib.ProximityGap.KKH26.not_dvd_collisionResultant_of_parseval_lt
#print axioms ArkLib.ProximityGap.KKH26.kkh26_lemma1_parseval

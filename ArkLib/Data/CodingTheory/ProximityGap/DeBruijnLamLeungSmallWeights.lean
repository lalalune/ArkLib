/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import Mathlib.FieldTheory.IsAlgClosed.Basic
import Mathlib.Analysis.SpecialFunctions.Complex.Circle
import ArkLib.Data.CodingTheory.ProximityGap.DeBruijnLamLeungReduction

/-!
# Issue #232 — LAM–LEUNG VIA SMALL-WEIGHT CLASSIFICATION: the `6 ∣ n` and
# `10 ∣ n` families, including the first nontrivial `k ≥ 3` levels (O113)

After O112 the Lam–Leung ℕ-span theorem is open exactly at squarefree
`k ≥ 3`-prime levels.  The content at a FIXED level `n` is finite: the span
`ℕp₁ + ⋯ + ℕp_k` misses only its numerical-semigroup gaps, so the law at `n`
is equivalent to the nonexistence of vanishing ℕ-sums whose total weight is a
gap.  Gaps are small; small-weight vanishing sums are classifiable:

* weight `1` — never vanishes (a root of unity is nonzero);
* weight `2` — forces `2 ∣ n` (`two_dvd_of_pair_sum_eq_zero`: the ratio is
  `−1`);
* weight `3` — forces `3 ∣ n` (`three_dvd_of_triple_sum_eq_zero`: the ratios
  are primitive cube roots — proven by embedding `ℚ(u) ↪ ℂ` via
  `IsAlgClosed.lift` and the unit-circle identity `a + ā = −1`).

Consequences (the headline span laws):

* `lam_leung_of_six_dvd` — the span law holds at EVERY `n` with `6 ∣ n`
  (gap set `{1}`); covers `n = 30, 42, 66, 78, …` — all `k ≥ 3` levels
  divisible by 6, previously open in-tree.
* `lam_leung_of_ten_dvd` — the span law holds at EVERY `n` with `10 ∣ n`
  (gap set `⊆ {1, 3}`; the gap `3` is killed by the cube-root classification
  when `3 ∤ n` and is in the span otherwise); covers `n = 70 = 2·5·7` — **the
  first nontrivial three-prime Lam–Leung instance**, where the semigroup
  argument alone does not suffice — and `n = 110, 130, 770 = 2·5·7·11 (k=4), …`

The companion probe `probe_rep_weight_cone.py` records the DISPROOF of the
naive inductive strengthening (the "rep-weight cone" claim: all ℕ-representation
weights of a fixed `γ` lie in `μ(γ) + ℕ`-span): offset-`1` representation pairs
exist at every tested modulus.  Only the `γ = 0` instance (Lam–Leung itself)
survives — which is why the remaining squarefree levels need genuinely
different tools (Lam–Leung's group-ring induction / Mann-type theorems).
-/

namespace DeBruijnLamLeungSmallWeights

open Finset IntermediateField

variable {L : Type*} [Field L]

/-! ## The multiset of a weight function and the extraction lemmas -/

/-- The exponent multiset of a weight function: `e` with multiplicity `w e`. -/
def expMultiset (n : ℕ) (w : ℕ → ℕ) : Multiset ℕ :=
  (Finset.range n).val.bind fun e => Multiset.replicate (w e) e

lemma expMultiset_card (n : ℕ) (w : ℕ → ℕ) :
    Multiset.card (expMultiset n w) = ∑ e ∈ Finset.range n, w e := by
  simp [expMultiset, Multiset.card_bind, Finset.sum]

lemma expMultiset_sum (n : ℕ) (w : ℕ → ℕ) (ζ : L) :
    ((expMultiset n w).map fun e => ζ ^ e).sum
      = ∑ e ∈ Finset.range n, (w e : L) * ζ ^ e := by
  simp [expMultiset, Multiset.map_bind, Multiset.sum_bind,
    Multiset.map_replicate, Multiset.sum_replicate, Finset.sum, nsmul_eq_mul]

/-! ## Weight 1 and weight 2 -/

/-- A weight-1 vanishing sum is impossible: roots of unity are nonzero. -/
lemma no_weight_one {n : ℕ} {ζ : L} (hζ : ζ ^ n = 1) (hn : 0 < n) (w : ℕ → ℕ)
    (htot : ∑ e ∈ Finset.range n, w e = 1)
    (hsum : ∑ e ∈ Finset.range n, (w e : L) * ζ ^ e = 0) : False := by
  have hζ0 : ζ ≠ 0 := by
    intro h0
    rw [h0, zero_pow hn.ne'] at hζ
    exact zero_ne_one hζ
  have hcard : Multiset.card (expMultiset n w) = 1 := by
    rw [expMultiset_card, htot]
  obtain ⟨a, ha⟩ := Multiset.card_eq_one.mp hcard
  have h := expMultiset_sum n w ζ
  rw [ha] at h
  simp at h
  rw [hsum] at h
  exact pow_ne_zero a hζ0 h

/-- **Weight 2 forces `2 ∣ n`**: a vanishing pair of `n`-th roots of unity has
ratio `−1`, of order `2`. -/
lemma two_dvd_of_pair_sum_eq_zero [CharZero L] {n : ℕ} (hn : 0 < n)
    {x y : L} (hx : x ^ n = 1) (hy : y ^ n = 1) (hxy : x + y = 0) : 2 ∣ n := by
  have hx0 : x ≠ 0 := by
    intro h0
    rw [h0, zero_pow hn.ne'] at hx
    exact zero_ne_one hx
  have hy' : y = -x := by linear_combination hxy
  have hyx : y * x⁻¹ = -1 := by
    rw [hy', neg_mul, mul_inv_cancel₀ hx0]
  have hpow : (-1 : L) ^ n = 1 := by
    rw [← hyx, mul_pow, hy, inv_pow, hx, inv_one, one_mul]
  rcases Nat.even_or_odd n with he | ho
  · exact he.two_dvd
  · rw [ho.neg_one_pow] at hpow
    have : (2 : L) = 0 := by linear_combination -hpow
    exact absurd this two_ne_zero

/-! ## Weight 3: the cube-root classification via a complex embedding -/

/-- Roots of unity are integral over ℚ. -/
private lemma isIntegral_of_pow_eq_one [CharZero L] {x : L} {m : ℕ} (hm : 0 < m)
    (hx : x ^ m = 1) : IsIntegral ℚ x :=
  ⟨Polynomial.X ^ m - 1,
    by simpa using Polynomial.monic_X_pow_sub_C (1 : ℚ) hm.ne',
    by simp [hx]⟩

/-- The ℂ-side core: a unit-norm pair `a`, `−1−a` of `n`-torsion points forces
`a` to be a primitive cube root, so `3 ∣ n`. -/
private lemma three_dvd_of_complex {n : ℕ} (hn : 0 < n) {a : ℂ}
    (ha : a ^ n = 1) (hb : (-1 - a) ^ n = 1) : 3 ∣ n := by
  have hna : ‖a‖ = 1 := Complex.norm_eq_one_of_pow_eq_one ha hn.ne'
  have hnb : ‖-1 - a‖ = 1 := Complex.norm_eq_one_of_pow_eq_one hb hn.ne'
  -- a · conj a = 1 and (−1−a) · conj (−1−a) = 1, via conj = inv on the circle
  have ha0 : a ≠ 0 := by
    intro h0
    rw [h0] at hna
    simp at hna
  have hb0 : (-1 - a) ≠ 0 := by
    intro h0
    rw [h0] at hnb
    simp at hnb
  have hmc : a * (starRingEnd ℂ) a = 1 := by
    rw [← Complex.inv_eq_conj hna, mul_inv_cancel₀ ha0]
  have hmb : (-1 - a) * (starRingEnd ℂ) (-1 - a) = 1 := by
    rw [← Complex.inv_eq_conj hnb, mul_inv_cancel₀ hb0]
  -- expand: a + conj a = −1
  have hsum : a + (starRingEnd ℂ) a = -1 := by
    have hexp : (-1 - a) * (starRingEnd ℂ) (-1 - a)
        = 1 + a + (starRingEnd ℂ) a + a * (starRingEnd ℂ) a := by
      rw [map_sub, map_neg, map_one]
      ring
    rw [hexp, hmc] at hmb
    linear_combination hmb
  -- a² + a + 1 = a(a + 1 + conj a) = 0
  have hquad : a ^ 2 + a + 1 = 0 := by
    calc a ^ 2 + a + 1 = a * (a + 1 + (starRingEnd ℂ) a) := by
          rw [mul_add, mul_add, hmc]
          ring
      _ = a * 0 := by rw [show a + 1 + (starRingEnd ℂ) a = 0 by
            linear_combination hsum]
      _ = 0 := mul_zero a
  have hcube : a ^ 3 = 1 := by linear_combination (a - 1) * hquad
  have hne1 : a ≠ 1 := by
    intro h1
    rw [h1] at hquad
    norm_num at hquad
  haveI : Fact (Nat.Prime 3) := ⟨by norm_num⟩
  have horder : orderOf a = 3 := orderOf_eq_prime hcube hne1
  exact horder ▸ orderOf_dvd_of_pow_eq_one ha

/-- **Weight 3 forces `3 ∣ n`** (the cube-root classification): three `n`-th
roots of unity in a characteristic-zero field summing to zero have pairwise
ratios that are primitive cube roots.  Proof: normalize to `1 + u + v = 0`,
embed `ℚ(u)` into `ℂ` (`IsAlgClosed.lift`), and run the unit-circle identity. -/
theorem three_dvd_of_triple_sum_eq_zero [CharZero L] {n : ℕ} (hn : 0 < n)
    {x y z : L} (hx : x ^ n = 1) (hy : y ^ n = 1) (hz : z ^ n = 1)
    (hxyz : x + y + z = 0) : 3 ∣ n := by
  classical
  have hx0 : x ≠ 0 := by
    intro h0
    rw [h0, zero_pow hn.ne'] at hx
    exact zero_ne_one hx
  set u : L := y * x⁻¹ with hu
  have hun : u ^ n = 1 := by
    rw [hu, mul_pow, hy, inv_pow, hx, inv_one, one_mul]
  have hvn : (-1 - u) ^ n = 1 := by
    have hz' : z = -x - y := by linear_combination hxyz
    have hveq : -1 - u = z * x⁻¹ := by
      rw [hz', hu, sub_mul, neg_mul, mul_inv_cancel₀ hx0]
    rw [hveq, mul_pow, hz, inv_pow, hx, inv_one, one_mul]
  -- the number field ℚ(u) and its complex embedding
  have hint : IsIntegral ℚ u := isIntegral_of_pow_eq_one hn hun
  set K := ℚ⟮u⟯ with hK
  set g : K := IntermediateField.AdjoinSimple.gen ℚ u with hg
  have hcoe : algebraMap K L g = u := IntermediateField.AdjoinSimple.algebraMap_gen ℚ u
  have hinj : Function.Injective (algebraMap K L) := (algebraMap K L).injective
  have hgn : g ^ n = 1 := by
    apply hinj
    rw [map_pow, map_one, hcoe]
    exact hun
  have hgvn : (-1 - g) ^ n = 1 := by
    apply hinj
    rw [map_pow, map_one, map_sub, map_neg, map_one, hcoe]
    exact hvn
  haveI : FiniteDimensional ℚ K := IntermediateField.adjoin.finiteDimensional hint
  haveI : Algebra.IsAlgebraic ℚ K := Algebra.IsAlgebraic.of_finite ℚ K
  let φ : K →ₐ[ℚ] ℂ := IsAlgClosed.lift
  refine three_dvd_of_complex hn (a := φ g) ?_ ?_
  · rw [← map_pow, hgn, map_one]
  · have h := congrArg φ hgvn
    rw [map_pow, map_sub, map_neg, map_one] at h
    exact h

/-! ## The span laws -/

/-- Splitting a sum over a finset into two distinguished members. -/
private lemma sum_eq_pair {s : Finset ℕ} {a b : ℕ} (ha : a ∈ s) (hb : b ∈ s)
    (hab : a ≠ b) (f : ℕ → ℕ) (hf : ∀ p ∈ s, p ≠ a → p ≠ b → f p = 0) :
    ∑ p ∈ s, f p = f a + f b := by
  rw [← Finset.add_sum_erase s f ha]
  congr 1
  rw [← Finset.add_sum_erase _ f (Finset.mem_erase.mpr ⟨hab.symm, hb⟩)]
  have hz : ∑ p ∈ (s.erase a).erase b, f p = 0 :=
    Finset.sum_eq_zero fun p hp =>
      hf p (Finset.mem_of_mem_erase (Finset.mem_of_mem_erase hp))
        (Finset.ne_of_mem_erase (Finset.mem_of_mem_erase hp))
        (Finset.ne_of_mem_erase hp)
  rw [hz, add_zero]

/-- Weight-3 vanishing combinations force `3 ∣ n` (the ℕ-weighted corollary). -/
lemma three_dvd_of_weight_three [CharZero L] {n : ℕ} (hn : 0 < n) {ζ : L}
    (hζ : ζ ^ n = 1) (w : ℕ → ℕ)
    (htot : ∑ e ∈ Finset.range n, w e = 3)
    (hsum : ∑ e ∈ Finset.range n, (w e : L) * ζ ^ e = 0) : 3 ∣ n := by
  have hcard : Multiset.card (expMultiset n w) = 3 := by
    rw [expMultiset_card, htot]
  obtain ⟨a, b, c, habc⟩ := Multiset.card_eq_three.mp hcard
  have h := expMultiset_sum n w ζ
  rw [habc] at h
  simp at h
  rw [hsum] at h
  have hpow : ∀ e : ℕ, (ζ ^ e) ^ n = 1 := fun e => by
    rw [← pow_mul, mul_comm, pow_mul, hζ, one_pow]
  refine three_dvd_of_triple_sum_eq_zero hn (hpow a) (hpow b) (hpow c) ?_
  linear_combination h

/-- **LAM–LEUNG AT `6 ∣ n`** (O113a): the ℕ-span law holds at every level
divisible by 6 — the semigroup `ℕ·2 + ℕ·3` misses only `1`, and weight-1
vanishing sums do not exist.  Covers all `k ≥ 3` levels divisible by 6
(`n = 30, 42, 66, …`), previously open in-tree. -/
theorem lam_leung_of_six_dvd [CharZero L] {n : ℕ} (h6 : 6 ∣ n) (hn : 0 < n)
    {ζ : L} (hζ : IsPrimitiveRoot ζ n) (w : ℕ → ℕ)
    (hsum : ∑ e ∈ Finset.range n, (w e : L) * ζ ^ e = 0) :
    ∃ c : ℕ → ℕ, ∑ e ∈ Finset.range n, w e
      = ∑ p ∈ n.primeFactors, c p * p := by
  classical
  have h2n : 2 ∣ n := dvd_trans (by norm_num) h6
  have h3n : 3 ∣ n := dvd_trans (by norm_num) h6
  have h2m : 2 ∈ n.primeFactors :=
    Nat.mem_primeFactors.mpr ⟨Nat.prime_two, h2n, hn.ne'⟩
  have h3m : 3 ∈ n.primeFactors :=
    Nat.mem_primeFactors.mpr ⟨Nat.prime_three, h3n, hn.ne'⟩
  set T := ∑ e ∈ Finset.range n, w e with hT
  rcases Nat.eq_zero_or_pos T with hT0 | hTpos
  · exact ⟨0, by simp [hT0]⟩
  rcases Nat.lt_or_ge T 2 with hT1 | hT2
  · -- T = 1: impossible
    have hT1' : T = 1 := by omega
    exact absurd (no_weight_one hζ.pow_eq_one hn w (hT ▸ hT1') hsum) not_false
  -- T ≥ 2: split by parity
  refine ⟨fun p => if p = 2 then (T - (if T % 2 = 0 then 0 else 3)) / 2
    else if p = 3 then (if T % 2 = 0 then 0 else 1) else 0, ?_⟩
  dsimp only
  rw [sum_eq_pair h2m h3m (by norm_num)
    (fun p => (if p = 2 then (T - (if T % 2 = 0 then 0 else 3)) / 2
      else if p = 3 then (if T % 2 = 0 then 0 else 1) else 0) * p)
    (fun p _ hp2 hp3 => by
      dsimp only
      rw [if_neg hp2, if_neg hp3]
      exact zero_mul p)]
  rw [if_pos rfl, if_neg (by norm_num : (3 : ℕ) ≠ 2), if_pos rfl]
  rcases Nat.even_or_odd T with he | ho
  · have h2 : T % 2 = 0 := Nat.even_iff.mp he
    rw [if_pos h2, if_pos h2]
    omega
  · have h2' : ¬ T % 2 = 0 := by
      have := Nat.odd_iff.mp ho
      omega
    rw [if_neg h2', if_neg h2']
    omega

/-- **LAM–LEUNG AT `10 ∣ n`** (O113b): the ℕ-span law holds at every level
divisible by 10.  The semigroup `ℕ·2 + ℕ·5` misses only `{1, 3}`; weight 1
never vanishes, and weight 3 forces `3 ∣ n` (the cube-root classification) —
in which case `3` is in the span anyway.  Covers `n = 70 = 2·5·7`, **the first
nontrivial three-prime Lam–Leung instance**, and `n = 110, 130, 770, …` -/
theorem lam_leung_of_ten_dvd [CharZero L] {n : ℕ} (h10 : 10 ∣ n) (hn : 0 < n)
    {ζ : L} (hζ : IsPrimitiveRoot ζ n) (w : ℕ → ℕ)
    (hsum : ∑ e ∈ Finset.range n, (w e : L) * ζ ^ e = 0) :
    ∃ c : ℕ → ℕ, ∑ e ∈ Finset.range n, w e
      = ∑ p ∈ n.primeFactors, c p * p := by
  classical
  have h2n : 2 ∣ n := dvd_trans (by norm_num) h10
  have h5n : 5 ∣ n := dvd_trans (by norm_num) h10
  have h2m : 2 ∈ n.primeFactors :=
    Nat.mem_primeFactors.mpr ⟨Nat.prime_two, h2n, hn.ne'⟩
  have h5m : 5 ∈ n.primeFactors :=
    Nat.mem_primeFactors.mpr ⟨by norm_num, h5n, hn.ne'⟩
  set T := ∑ e ∈ Finset.range n, w e with hT
  rcases Nat.eq_zero_or_pos T with hT0 | hTpos
  · exact ⟨0, by simp [hT0]⟩
  rcases Nat.lt_or_ge T 2 with hT1 | hT2
  · have hT1' : T = 1 := by omega
    exact absurd (no_weight_one hζ.pow_eq_one hn w (hT ▸ hT1') hsum) not_false
  by_cases hT3 : T = 3
  · -- weight 3: the cube-root classification puts 3 ∣ n, so 3 is available
    have h3n : 3 ∣ n :=
      three_dvd_of_weight_three hn hζ.pow_eq_one w (hT ▸ hT3) hsum
    have h3m : 3 ∈ n.primeFactors :=
      Nat.mem_primeFactors.mpr ⟨Nat.prime_three, h3n, hn.ne'⟩
    refine ⟨fun p => if p = 3 then 1 else 0, ?_⟩
    dsimp only
    rw [Finset.sum_eq_single_of_mem 3 h3m
      (fun p _ hp => by rw [if_neg hp]; exact zero_mul p)]
    rw [if_pos rfl, hT3]
  · -- T = 2, or T ≥ 4: ℕ2 + ℕ5 suffices (odd T ≥ 5 here)
    have h5odd : T % 2 = 1 → 5 ≤ T := by omega
    refine ⟨fun p => if p = 2 then (T - (if T % 2 = 0 then 0 else 5)) / 2
      else if p = 5 then (if T % 2 = 0 then 0 else 1) else 0, ?_⟩
    dsimp only
    rw [sum_eq_pair h2m h5m (by norm_num)
      (fun p => (if p = 2 then (T - (if T % 2 = 0 then 0 else 5)) / 2
        else if p = 5 then (if T % 2 = 0 then 0 else 1) else 0) * p)
      (fun p _ hp2 hp5 => by
        dsimp only
        rw [if_neg hp2, if_neg hp5]
        exact zero_mul p)]
    rw [if_pos rfl, if_neg (by norm_num : (5 : ℕ) ≠ 2), if_pos rfl]
    rcases Nat.even_or_odd T with he | ho
    · have h2 : T % 2 = 0 := Nat.even_iff.mp he
      rw [if_pos h2, if_pos h2]
      omega
    · have h2 : T % 2 = 1 := Nat.odd_iff.mp ho
      have hT5 : 5 ≤ T := h5odd h2
      have h2' : ¬ T % 2 = 0 := by omega
      rw [if_neg h2', if_neg h2']
      omega

end DeBruijnLamLeungSmallWeights

#print axioms DeBruijnLamLeungSmallWeights.no_weight_one
#print axioms DeBruijnLamLeungSmallWeights.two_dvd_of_pair_sum_eq_zero
#print axioms DeBruijnLamLeungSmallWeights.three_dvd_of_triple_sum_eq_zero
#print axioms DeBruijnLamLeungSmallWeights.three_dvd_of_weight_three
#print axioms DeBruijnLamLeungSmallWeights.lam_leung_of_six_dvd
#print axioms DeBruijnLamLeungSmallWeights.lam_leung_of_ten_dvd

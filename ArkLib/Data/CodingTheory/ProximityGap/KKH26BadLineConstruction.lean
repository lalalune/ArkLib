/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.KKH26SumsOfRootsOfUnity

/-!
# KKH26 Proposition 1 — the bad line, in explicit count form

This file formalizes the **counterexample construction** of [KKH26] (Krachun–Kazanin–Haböck,
*Failure of proximity gaps close to capacity*, ePrint 2026/782) §2.1, downstream of the
additive-combinatorics core `kkh26_lemma1` (in `KKH26SumsOfRootsOfUnity.lean`).  This is the
construction that refutes the [BCIKS20] up-to-capacity proximity-gap conjecture for
Reed–Solomon codes over smooth multiplicative subgroups of prime fields — the Proximity Prize
domain class (issue #232) — and thereby pins the prize threshold `δ*` strictly below capacity.

## The construction ([KKH26] §2.1)

Let `H = ⟨g⟩ ⊆ F_p^×` be the smooth evaluation domain, `|H| = n = s·m` with `s = 2^μ`, and
`G = ⟨g^m⟩` the subgroup of size `s`, with projection `π : H → G`, `x ↦ x^m`.  For a subset
`S ⊆ G` of size `r`, the vanishing polynomial `v_S(X) = ∏_{a∈S}(X − a)` pulls back to the
**`m`-gap polynomial**

  `v_S(X^m) = X^{rm} − (∑_{a∈S} a)·X^{(r−1)m} + E_S(X)`,   `deg E_S ≤ (r−2)m`.

Setting `u₀ = X^{rm}`, `u₁ = X^{(r−1)m}` (as words on `H`) and `λ_S = −∑_{a∈S} a`, the line
point `u₀ + λ_S·u₁` agrees with the codeword `−E_S` (degree ≤ `(r−2)m`) on the fiber
`π^{-1}(S)`, which has exactly `r·m` points.  By `kkh26_lemma1`, above the explicit prime
threshold `p > s^{s/2}` the values `λ_S` are **pairwise distinct** across at least
`2^r · (s/2).choose r` choices of signed data — so the affine line `{u₀ + λ·u₁}` carries that
many `(r·m)`-agreement-close points.  Meanwhile `u₁` itself agrees with *any* polynomial of
degree ≤ `(r−2)m` on at most `(r−1)m < r·m` points, so the line is **not** entirely close.

In relative-distance terms (`n = s·m`): the close points are within `δ = 1 − r/s` of the code
of rate `≈ (r−2)/s`, the line direction `u₁` is `(1 − (r−1)/s)`-far, and the number of close
points is exponential in `s` at `r = Θ(s)` — against the `poly(n)/|F|`-style soundness-error
ceiling conjectured in [BCIKS20].  This is the quantitative engine behind
`δ* ≤ 1 − ρ − Θ_ρ(1/log n)` for the Grand MCA Challenge window.

## Main results

* `gap_expansion` — the `m`-gap expansion of `∏_{a∈S}(X^m − C a)` (top two coefficients
  exposed, remainder of degree ≤ `(|S|−2)m`).
* `fiber_count` — `|{x ∈ H : x^m ∈ S}| = m·|S|` for `S ⊆ G` (exact fiber sizes via root
  counting and sum rigidity; no group-quotient machinery).
* `farword_agreement_le` — a degree-`d` monomial word agrees with any lower-degree polynomial
  word on at most `d` points.
* `kkh26_badline_closePoints` — **[KKH26] Proposition 1, close-point count**: there exist at
  least `2^r · (2^{μ−1}).choose r` distinct `λ` such that `u₀ + λ·u₁` agrees with a
  degree-≤`(r−2)m` codeword on at least `r·m` of the `n = 2^μ·m` points of `H`.
* `kkh26_badline_farWord` — **[KKH26] Proposition 1, far-word side**: `u₁` agrees with any
  degree-≤`(r−2)m` polynomial on at most `(r−1)·m` points.

## What is *not* formalized (honest frontier)

The asymptotic phrasing of [KKH26] Theorem 1 (`η = Θ(1/log n)` via Stirling estimates of the
binomial count, and polynomial field sizes `p = Θ(n^β)` via the Thorner–Zaman quantitative
PNT in arithmetic progressions) remains external; this file delivers the complete
finite/explicit combinatorial content of Proposition 1.  The transfer from proximity-gap
failure to an `ε_mca` lower bound (hierarchy `ε_pg ≤ ε_ca ≤ ε_mca`) is recorded in the
MCA threshold ledger, not here.

## References

* [KKH26] D. Krachun, S. Kazanin, U. Haböck, *Failure of proximity gaps close to capacity*,
  ePrint 2026/782.
* [BCIKS20] Ben-Sasson, Carmon, Ishai, Kopparty, Saraf, *Proximity Gaps for Reed–Solomon
  Codes*, ePrint 2020/654.
-/

open Polynomial Finset

namespace ArkLib.ProximityGap.KKH26

/-! ### The `m`-gap expansion ([KKH26] §2.1, the sparse pullback of `v_S`) -/

set_option linter.unusedVariables false in
/-- **Gap expansion.** Substituting `X^m` into the vanishing polynomial of `S` exposes the
top two coefficients: `∏_{a∈S}(X^m − a) = X^{|S|m} − (∑_{a∈S} a)·X^{(|S|−1)m} + E` with
`deg E ≤ (|S|−2)m`.  The leading nontrivial coefficient is exactly `−∑_{a∈S} a` — the value
that becomes the line parameter `λ_S`. -/
theorem gap_expansion {R : Type*} [CommRing R] (S : Finset R) {m : ℕ} (hm : 1 ≤ m)
    (hr : 2 ≤ S.card) :
    ∃ E : Polynomial R,
      (∏ a ∈ S, (X ^ m - C a))
        = X ^ (S.card * m) - C (∑ a ∈ S, a) * X ^ ((S.card - 1) * m) + E
      ∧ E.natDegree ≤ (S.card - 2) * m := by
  classical
  haveI : Nontrivial R := by
    obtain ⟨a, -, b, -, hab⟩ := Finset.one_lt_card.mp (by omega : 1 < S.card)
    exact ⟨a, b, hab⟩
  set n := S.card with hn
  set P : Polynomial R := ∏ a ∈ S, (X - C a) with hP
  have hPmonic : P.Monic := monic_prod_of_monic _ _ fun a _ => monic_X_sub_C a
  have hPdeg : P.natDegree = n := by
    rw [hP, natDegree_prod_of_monic _ _ fun a _ => monic_X_sub_C a]
    simp [hn]
  have hnpos : 0 < n := by omega
  have hcoeff_top : P.coeff n = 1 := by
    have h := hPmonic.coeff_natDegree
    rwa [hPdeg] at h
  have hcoeff_next : P.coeff (n - 1) = -∑ a ∈ S, a := by
    have h1 : P.nextCoeff = -∑ a ∈ S, a := by
      rw [hP]
      exact prod_X_sub_C_nextCoeff (fun a => a)
    have h2 : P.nextCoeff = P.coeff (P.natDegree - 1) :=
      nextCoeff_of_natDegree_pos (by rw [hPdeg]; exact hnpos)
    rw [h2, hPdeg] at h1
    exact h1
  set D : Polynomial R := P - X ^ n + C (∑ a ∈ S, a) * X ^ (n - 1) with hD
  have hPid : P = X ^ n - C (∑ a ∈ S, a) * X ^ (n - 1) + D := by
    rw [hD]; ring
  have hDdeg : D.natDegree ≤ n - 2 := by
    rw [natDegree_le_iff_coeff_eq_zero]
    intro k hk
    rcases lt_trichotomy k n with hkn | hkn | hkn
    · have hk1 : k = n - 1 := by omega
      have h1 : ¬(n - 1 = n) := by omega
      rw [hD]
      simp only [coeff_add, coeff_sub, coeff_C_mul, coeff_X_pow]
      rw [hk1, hcoeff_next]
      simp [h1]
    · have h1 : ¬(n = n - 1) := by omega
      rw [hD]
      simp only [coeff_add, coeff_sub, coeff_C_mul, coeff_X_pow]
      rw [hkn, hcoeff_top]
      simp [h1]
    · have h1 : ¬(k = n) := by omega
      have h2 : ¬(k = n - 1) := by omega
      rw [hD]
      simp only [coeff_add, coeff_sub, coeff_C_mul, coeff_X_pow]
      rw [coeff_eq_zero_of_natDegree_lt (by rw [hPdeg]; exact hkn)]
      simp [h1, h2]
  refine ⟨D.comp (X ^ m), ?_, ?_⟩
  · have hprod : (∏ a ∈ S, (X ^ m - C a) : Polynomial R) = P.comp (X ^ m) := by
      rw [hP, Polynomial.prod_comp]
      simp [sub_comp]
    rw [hprod, hPid]
    simp only [add_comp, sub_comp, mul_comp, pow_comp, X_comp, C_comp]
    rw [← pow_mul, ← pow_mul, Nat.mul_comm m n, Nat.mul_comm m (n - 1)]
  · calc (D.comp (X ^ m)).natDegree
        ≤ D.natDegree * (X ^ m : Polynomial R).natDegree := natDegree_comp_le
      _ = D.natDegree * m := by rw [natDegree_X_pow]
      _ ≤ (n - 2) * m := Nat.mul_le_mul hDdeg le_rfl

/-! ### Exact fiber counts for the projection `π : H → G`, `x ↦ x^m` -/

/-- **Fiber count.** For `g` of order `s·m` in a field, the power map `x ↦ x^m` sends the
order-`s·m` cyclic group `H = ⟨g⟩` onto `G = ⟨g^m⟩` with every fiber of size exactly `m`;
hence the preimage of any `S ⊆ G` has exactly `m·|S|` points.  (Each fiber is contained in
the root set of `X^m − a`, so has at most `m` points; `|H| = s·m` forces equality
everywhere.) -/
theorem fiber_count {F : Type*} [Field F] [DecidableEq F] {g : F} {s m : ℕ}
    (hm : 1 ≤ m) (hs : 1 ≤ s)
    (hg : orderOf g = s * m) (S : Finset F)
    (hS : S ⊆ (Finset.range s).image (fun j => (g ^ m) ^ j)) :
    (((Finset.range (s * m)).image (fun i => g ^ i)).filter (fun x => x ^ m ∈ S)).card
      = m * S.card := by
  classical
  set H : Finset F := (Finset.range (s * m)).image (fun i => g ^ i) with hH
  set G : Finset F := (Finset.range s).image (fun j => (g ^ m) ^ j) with hG
  have hm0 : m ≠ 0 := by omega
  have hs0 : s ≠ 0 := by omega
  have hsm0 : s * m ≠ 0 := Nat.mul_ne_zero hs0 hm0
  have hg0 : g ≠ 0 := by
    rintro rfl
    have h1 : (0 : F) ^ (s * m) = 1 := by rw [← hg]; exact pow_orderOf_eq_one 0
    rw [zero_pow hsm0] at h1
    exact zero_ne_one h1
  have key : ∀ (h : F), h ≠ 0 → ∀ {N : ℕ}, orderOf h = N →
      ∀ i, i < N → ∀ j, j < N → h ^ i = h ^ j → i = j := by
    intro h h0 N hN
    have main : ∀ i j, i ≤ j → j < N → h ^ i = h ^ j → i = j := by
      intro i j hij hj heq
      have hadd : i + (j - i) = j := by omega
      have h2 : h ^ i * h ^ (j - i) = h ^ i * 1 := by
        rw [mul_one, ← pow_add, hadd, heq]
      have h3 : h ^ (j - i) = 1 := mul_left_cancel₀ (pow_ne_zero i h0) h2
      have h4 : N ∣ j - i := hN ▸ orderOf_dvd_of_pow_eq_one h3
      have h5 : j - i = 0 :=
        Nat.eq_zero_of_dvd_of_lt h4 (lt_of_le_of_lt (Nat.sub_le j i) hj)
      omega
    intro i hi j hj heq
    rcases le_total i j with hle | hle
    · exact main i j hle hj heq
    · exact (main j i hle hi heq.symm).symm
  have hgm0 : g ^ m ≠ 0 := pow_ne_zero m hg0
  have hgmord : orderOf (g ^ m) = s := by
    have h1 : (g ^ m) ^ s = 1 := by
      rw [← pow_mul, mul_comm m s, ← hg]; exact pow_orderOf_eq_one g
    have h2 : orderOf (g ^ m) ∣ s := orderOf_dvd_of_pow_eq_one h1
    have h3 : g ^ (m * orderOf (g ^ m)) = 1 := by
      rw [pow_mul]; exact pow_orderOf_eq_one (g ^ m)
    have h4 : s * m ∣ m * orderOf (g ^ m) := hg ▸ orderOf_dvd_of_pow_eq_one h3
    rw [mul_comm s m] at h4
    have h5 : s ∣ orderOf (g ^ m) :=
      (Nat.mul_dvd_mul_iff_left (by omega : 0 < m)).mp h4
    exact Nat.dvd_antisymm h2 h5
  have hinjH : Set.InjOn (fun i => g ^ i) ((Finset.range (s * m) : Finset ℕ) : Set ℕ) := by
    intro i hi j hj hij
    simp only [Finset.coe_range, Set.mem_Iio] at hi hj
    exact key g hg0 hg i hi j hj hij
  have hHcard : H.card = s * m := by
    rw [hH, Finset.card_image_of_injOn hinjH, Finset.card_range]
  have hinjG : Set.InjOn (fun j => (g ^ m) ^ j) ((Finset.range s : Finset ℕ) : Set ℕ) := by
    intro i hi j hj hij
    simp only [Finset.coe_range, Set.mem_Iio] at hi hj
    exact key (g ^ m) hgm0 hgmord i hi j hj hij
  have hGcard : G.card = s := by
    rw [hG, Finset.card_image_of_injOn hinjG, Finset.card_range]
  have hcover : ∀ x ∈ H, x ^ m ∈ G := by
    intro x hx
    rw [hH, Finset.mem_image] at hx
    obtain ⟨i, hi, rfl⟩ := hx
    rw [Finset.mem_range] at hi
    rw [hG, Finset.mem_image]
    refine ⟨i % s, Finset.mem_range.mpr (Nat.mod_lt i (by omega)), ?_⟩
    rw [← pow_mul g i m, mul_comm i m, pow_mul]
    conv_lhs => rw [← hgmord]
    exact pow_mod_orderOf (g ^ m) i
  have fiber_le : ∀ a : F, (H.filter (fun x => x ^ m = a)).card ≤ m := by
    intro a
    have hp : (X ^ m - C a : F[X]) ≠ 0 := X_pow_sub_C_ne_zero (by omega) a
    have hdeg : (X ^ m - C a : F[X]).natDegree = m := natDegree_X_pow_sub_C
    have hsub : H.filter (fun x => x ^ m = a) ⊆ (X ^ m - C a : F[X]).roots.toFinset := by
      intro x hx
      rw [Finset.mem_filter] at hx
      rw [Multiset.mem_toFinset, mem_roots hp]
      simp only [IsRoot.def, eval_sub, eval_pow, eval_X, eval_C, sub_eq_zero]
      exact hx.2
    calc (H.filter (fun x => x ^ m = a)).card
        ≤ (X ^ m - C a : F[X]).roots.toFinset.card := Finset.card_le_card hsub
      _ ≤ Multiset.card (X ^ m - C a : F[X]).roots := Multiset.toFinset_card_le _
      _ ≤ (X ^ m - C a : F[X]).natDegree := card_roots' _
      _ = m := hdeg
  have hsum : ∑ a ∈ G, (H.filter (fun x => x ^ m = a)).card = s * m :=
    (Finset.card_eq_sum_card_fiberwise hcover).symm.trans hHcard
  have hfiber_eq : ∀ a ∈ G, (H.filter (fun x => x ^ m = a)).card = m := by
    by_contra hcon
    push Not at hcon
    obtain ⟨a₀, ha₀, hne⟩ := hcon
    have hlt : (H.filter (fun x => x ^ m = a₀)).card < m :=
      lt_of_le_of_ne (fiber_le a₀) hne
    have hstrict : ∑ a ∈ G, (H.filter (fun x => x ^ m = a)).card < ∑ _a ∈ G, m :=
      Finset.sum_lt_sum (fun a _ => fiber_le a) ⟨a₀, ha₀, hlt⟩
    rw [Finset.sum_const, smul_eq_mul, hGcard, hsum] at hstrict
    omega
  have hsplit : (H.filter (fun x => x ^ m ∈ S)).card
      = ∑ a ∈ S, (H.filter (fun x => x ^ m = a)).card := by
    have h1 := Finset.card_eq_sum_card_fiberwise
      (s := H.filter (fun x => x ^ m ∈ S)) (t := S) (f := fun x => x ^ m)
      (fun x hx => (Finset.mem_filter.mp hx).2)
    rw [h1]
    refine Finset.sum_congr rfl fun a ha => ?_
    congr 1
    ext x
    simp only [Finset.mem_filter]
    constructor
    · rintro ⟨⟨hxH, _⟩, hxa⟩
      exact ⟨hxH, hxa⟩
    · rintro ⟨hxH, hxa⟩
      exact ⟨⟨hxH, by rw [hxa]; exact ha⟩, hxa⟩
  rw [hsplit, Finset.sum_congr rfl (fun a ha => hfiber_eq a (hS ha)),
    Finset.sum_const, smul_eq_mul, mul_comm]

/-! ### The far-word bound -/

/-- **Far word.** On any finite subset `H` of a field, the monomial word `x ↦ x^d` agrees
with the evaluation of a polynomial of degree `≤ e < d` on at most `d` points: the agreement
points are roots of the nonzero polynomial `X^d − q`. -/
theorem farword_agreement_le {F : Type*} [Field F] [DecidableEq F] (H : Finset F) {d e : ℕ}
    (hde : e < d) (q : Polynomial F) (hq : q.natDegree ≤ e) :
    (H.filter (fun x => x ^ d = q.eval x)).card ≤ d := by
  set D : Polynomial F := X ^ d - q with hD
  have hqd : q.coeff d = 0 := coeff_eq_zero_of_natDegree_lt (lt_of_le_of_lt hq hde)
  have hDne : D ≠ 0 := by
    intro h
    have hcoeff : D.coeff d = 0 := by rw [h]; simp
    rw [hD, coeff_sub, coeff_X_pow, hqd] at hcoeff
    simp at hcoeff
  have hsub : (H.filter (fun x => x ^ d = q.eval x)) ⊆ D.roots.toFinset := by
    intro x hx
    rw [Finset.mem_filter] at hx
    rw [Multiset.mem_toFinset, mem_roots']
    refine ⟨hDne, ?_⟩
    simp [hD, IsRoot, eval_sub, eval_pow, hx.2]
  calc (H.filter (fun x => x ^ d = q.eval x)).card
      ≤ D.roots.toFinset.card := Finset.card_le_card hsub
    _ ≤ Multiset.card D.roots := Multiset.toFinset_card_le _
    _ ≤ D.natDegree := card_roots' D
    _ ≤ d := by
        rw [hD]
        refine le_trans (natDegree_sub_le _ _) ?_
        rw [natDegree_X_pow]
        exact max_le le_rfl (hq.trans hde.le)

/-! ### [KKH26] Proposition 1 — the bad line -/

/-- **[KKH26] Proposition 1, close-point count (explicit form).**  Let `g ∈ F_p` generate
the smooth domain `H` of order `n = 2^μ · m`, and suppose `p > s^{s/2}` for `s = 2^μ`.  For
every `2 ≤ r ≤ s/2` there is a set `Λ` of at least `2^r · (s/2).choose r` **distinct** line
parameters such that for each `λ ∈ Λ`, the word `x ↦ x^{rm} + λ·x^{(r−1)m}` on `H` agrees
with (the evaluation of) some polynomial of degree ≤ `(r−2)m` on at least `r·m` of the `n`
points — i.e. the affine line through `u₀ = X^{rm}` with direction `u₁ = X^{(r−1)m}` carries
exponentially many `(1 − r/s)`-close points, against a code of rate `≈ (r−2)/s`. -/
theorem kkh26_badline_closePoints {p : ℕ} [Fact p.Prime] {μ : ℕ} (hμ : 1 ≤ μ)
    {g : ZMod p} {m r : ℕ} (hm : 1 ≤ m)
    (hg : orderOf g = 2 ^ μ * m)
    (hp : ((2 : ℕ) ^ μ) ^ 2 ^ (μ - 1) < p)
    (hr2 : 2 ≤ r) (hr : r ≤ 2 ^ (μ - 1)) :
    ∃ Λ : Finset (ZMod p),
      2 ^ r * (2 ^ (μ - 1)).choose r ≤ Λ.card ∧
      ∀ lam ∈ Λ, ∃ q : Polynomial (ZMod p), q.natDegree ≤ (r - 2) * m ∧
        r * m ≤ (((Finset.range (2 ^ μ * m)).image (fun i => g ^ i)).filter
          (fun x => x ^ (r * m) + lam * x ^ ((r - 1) * m) = q.eval x)).card := by
  classical
  set s : ℕ := 2 ^ μ with hsdef
  have hs : 1 ≤ s := Nat.one_le_two_pow
  have hm0 : m ≠ 0 := by omega
  -- the inner generator ĝ := g^m has order s = 2^μ and is a primitive 2^μ-th root of unity
  have hg0 : g ≠ 0 := by
    rintro rfl
    have h1 : (0 : ZMod p) ^ (s * m) = 1 := by rw [← hg]; exact pow_orderOf_eq_one 0
    rw [zero_pow (Nat.mul_ne_zero (by omega) hm0)] at h1
    exact zero_ne_one h1
  have hgmord : orderOf (g ^ m) = s := by
    have h1 : (g ^ m) ^ s = 1 := by
      rw [← pow_mul, mul_comm m s, ← hg]; exact pow_orderOf_eq_one g
    have h2 : orderOf (g ^ m) ∣ s := orderOf_dvd_of_pow_eq_one h1
    have h3 : g ^ (m * orderOf (g ^ m)) = 1 := by
      rw [pow_mul]; exact pow_orderOf_eq_one (g ^ m)
    have h4 : s * m ∣ m * orderOf (g ^ m) := hg ▸ orderOf_dvd_of_pow_eq_one h3
    rw [mul_comm s m] at h4
    have h5 : s ∣ orderOf (g ^ m) :=
      (Nat.mul_dvd_mul_iff_left (by omega : 0 < m)).mp h4
    exact Nat.dvd_antisymm h2 h5
  have hprim : IsPrimitiveRoot (g ^ m) (2 ^ μ) := by
    have h := IsPrimitiveRoot.orderOf (g ^ m)
    rwa [hgmord, hsdef] at h
  -- Lemma 1: the sums of r distinct elements of G take many distinct values
  have hlem1 := kkh26_lemma1 hμ hprim hp hr
  set G : Finset (ZMod p) := (Finset.range (2 ^ μ)).image (fun i => (g ^ m) ^ i) with hGdef
  set sums : Finset (ZMod p) := (G.powersetCard r).image (fun T => ∑ x ∈ T, x) with hsums
  -- Λ is the negation of the sum set
  refine ⟨sums.image (fun w => -w), ?_, ?_⟩
  · rw [Finset.card_image_of_injective _ neg_injective]
    exact hlem1
  · intro lam hlam
    obtain ⟨w, hw, rfl⟩ := Finset.mem_image.mp hlam
    obtain ⟨T, hT, hTsum⟩ := Finset.mem_image.mp hw
    obtain ⟨hTG, hTcard⟩ := Finset.mem_powersetCard.mp hT
    -- gap expansion for S := T
    obtain ⟨E, hEeq, hEdeg⟩ := gap_expansion T hm (by omega : 2 ≤ T.card)
    refine ⟨-E, ?_, ?_⟩
    · rw [natDegree_neg]
      rw [hTcard] at hEdeg
      exact hEdeg
    · -- the agreement set contains the fiber over T
      have hfiber := fiber_count hm hs hg T hTG
      rw [hTcard] at hfiber
      have hsubset : (((Finset.range (2 ^ μ * m)).image (fun i => g ^ i)).filter
            (fun x => x ^ m ∈ T)) ⊆
          (((Finset.range (2 ^ μ * m)).image (fun i => g ^ i)).filter
            (fun x => x ^ (r * m) + -w * x ^ ((r - 1) * m) = Polynomial.eval x (-E))) := by
        intro x hx
        obtain ⟨hxH, hxm⟩ := Finset.mem_filter.mp hx
        refine Finset.mem_filter.mpr ⟨hxH, ?_⟩
        -- v_T(x^m) = 0 since x^m ∈ T
        have hvanish : ∏ a ∈ T, (x ^ m - a) = 0 :=
          Finset.prod_eq_zero hxm (sub_self _)
        -- evaluate the gap identity at x
        have heval := congrArg (Polynomial.eval x) hEeq
        rw [eval_prod] at heval
        simp only [eval_add, eval_sub, eval_mul, eval_pow, eval_X, eval_C] at heval
        rw [hTcard, hvanish] at heval
        rw [eval_neg, ← hTsum]
        linear_combination -heval
      calc r * m = m * r := Nat.mul_comm r m
        _ = _ := hfiber.symm
        _ ≤ _ := Finset.card_le_card hsubset

/-- **[KKH26] Proposition 1, far-word side.**  The line direction `u₁ = X^{(r−1)m}` agrees
with (the evaluation of) any polynomial of degree ≤ `(r−2)m` on at most `(r−1)·m` points of
any finite evaluation set — strictly fewer than the `r·m` agreement points achieved by the
close line points of `kkh26_badline_closePoints`.  Hence the line is not entirely close: the
proximity-gap dichotomy fails quantitatively at this distance. -/
theorem kkh26_badline_farWord {p : ℕ} [Fact p.Prime] {g : ZMod p} {n m r : ℕ}
    (hm : 1 ≤ m) (hr2 : 2 ≤ r)
    (q : Polynomial (ZMod p)) (hq : q.natDegree ≤ (r - 2) * m) :
    (((Finset.range n).image (fun i => g ^ i)).filter
      (fun x => x ^ ((r - 1) * m) = q.eval x)).card ≤ (r - 1) * m := by
  classical
  refine farword_agreement_le _ ?_ q hq
  have h1 : r - 2 < r - 1 := by omega
  exact Nat.mul_lt_mul_of_lt_of_le h1 le_rfl (by omega)

/-! ### Correlated-agreement failure -/

/-- **Correlated agreement fails on the bad line ([KKH26] Theorem 1, CA form).**  Any joint
agreement witness for the line `{u₀ + λ·u₁}` — a set `S ⊆ H` on which both `u₀` and `u₁`
(equivalently, two line points, equivalently `u₁` and any line point) simultaneously match
codewords — forces the direction word `u₁ = X^{(r−1)m}` to agree with a degree-≤`(r−2)m`
polynomial on all of `S`.  No such `S` of size ≥ `r·m` exists.  Combined with
`kkh26_badline_closePoints` (≥ `2^r·(s/2).choose r` individually `(r·m)`-agreement-close
points), this is the quantitative failure of correlated agreement — and hence of mutual
correlated agreement, via `ε_pg ≤ ε_ca ≤ ε_mca` — at distance `1 − r/s`:
the per-point count is exponential in `s` at `r = Θ(s)`, while the joint-witness count is
zero. -/
theorem kkh26_ca_failure {p : ℕ} [Fact p.Prime] {g : ZMod p} {n m r : ℕ}
    (hm : 1 ≤ m) (hr2 : 2 ≤ r)
    (S : Finset (ZMod p)) (hSH : S ⊆ (Finset.range n).image (fun i => g ^ i))
    (hScard : r * m ≤ S.card)
    (q : Polynomial (ZMod p)) (hq : q.natDegree ≤ (r - 2) * m) :
    ¬ (∀ x ∈ S, x ^ ((r - 1) * m) = q.eval x) := by
  classical
  intro hagree
  have hsub : S ⊆ ((Finset.range n).image (fun i => g ^ i)).filter
      (fun x => x ^ ((r - 1) * m) = q.eval x) := by
    intro x hx
    exact Finset.mem_filter.mpr ⟨hSH hx, hagree x hx⟩
  have h1 : r * m ≤ (r - 1) * m :=
    le_trans hScard (le_trans (Finset.card_le_card hsub)
      (kkh26_badline_farWord (g := g) (n := n) hm hr2 q hq))
  have h2 : (r - 1) * m < r * m := by
    have : r - 1 < r := by omega
    exact Nat.mul_lt_mul_of_lt_of_le this le_rfl (by omega)
  omega

end ArkLib.ProximityGap.KKH26

/-! ## Axiom audit -/
#print axioms ArkLib.ProximityGap.KKH26.gap_expansion
#print axioms ArkLib.ProximityGap.KKH26.fiber_count
#print axioms ArkLib.ProximityGap.KKH26.farword_agreement_le
#print axioms ArkLib.ProximityGap.KKH26.kkh26_badline_closePoints
#print axioms ArkLib.ProximityGap.KKH26.kkh26_badline_farWord
#print axioms ArkLib.ProximityGap.KKH26.kkh26_ca_failure

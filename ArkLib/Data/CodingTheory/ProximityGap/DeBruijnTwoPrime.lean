/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import Mathlib

/-!
# Issue #232 — the two-prime de Bruijn structure: the CRT double-slice theorems (O67–O68)

The mixed-radix continuation of the O50/O66 prime-power base cases (DISPROOF_LOG O67):
de Bruijn's structure theorem says that for `n` with at most two prime divisors, every
vanishing sum of `n`-th roots of unity is an ℕ-combination of rotated full prime packets
(`μ_p`-packets and `μ_q`-packets).  This file machine-checks the **CRT double-slice
route** to that theorem (the in-framework candidate identified in O67), delivering the
T2/T3 tiers:

* `vanishing_coeff_slices_over` — **the K-coefficient prime-power slice theorem**: for an
  arbitrary coefficient field `K` with `Algebra K F`, if `Φ_{p^(m+1)}` stays the minimal
  polynomial of a primitive `p^(m+1)`-th root `ζ` over `K` (the **linear-disjointness
  hypothesis** `hmin`, the ONE named hypothesis of the route), then any vanishing
  `K`-combination of the powers `ζ^e`, `e < p^(m+1)`, has all `p` of its length-`p^m`
  coefficient slices equal.  This generalizes `LamLeungTwoPow.vanishing_coeff_slices`
  from `ℚ` to `K`; the proof is the same Gauss engine (the prime-power cyclotomic is the
  geometric packet `Σ_{i<p} X^{i·p^m}`, and a packet multiple has all slices equal).

* `qside_slices_over` — **T2, the double-slice structure theorem**: for a finite
  `S ⊆ μ_{p^(m+1)·N}` with vanishing sum (`N` coprime to `p`, e.g. `N = q^b`), the
  q-side grouped coefficients `γ_u := Σ_v 1_S(u,v)·z_q^v ∈ K` satisfy the slice relations
  `γ_{i·p^m + s} = γ_{i'·p^m + s}` — the grouped membership data is constant along
  `μ_p`-coset directions.  Modulo `hmin`, this is unconditional and machine-checked.

* `slice_difference_vanishing` / `two_prime_double_slice` — **T3**: the slice
  differences are vanishing sums of `q^(b+1)`-th roots with coefficients in `{−1,0,1}`
  ⊆ ℚ, where the rational slice theorem (`vanishing_coeff_slices_rat`, recovered here as
  the `K = ℚ` instance of the engine) applies at the second prime: the membership
  difference pattern between two `μ_p`-coset-related rows is itself constant along
  `μ_q`-coset directions.  This is the full double-slice (two-prime de Bruijn) structure
  at the level of slice relations.

* `minpoly_qadjoin_eq_cyclotomic` — **the linear-disjointness DISCHARGE**: `Φ_{p^(a+1)}`
  IS the minimal polynomial of `ζ_p` over `ℚ⟮ζ_q⟯` (`q ≠ p` primes, `ζ_q` of order
  `q^b`).  Engine: `minpoly ∣ Φ` pinched against the totient tower-degree bound (the
  packet form `minpoly_adjoin_primitiveRoot_eq_packet`, copied with provenance from the
  parallel step-(1) lane `CRTPacketMinpoly.lean`).

* `two_prime_qside_slices` / `two_prime_deBruijn_double_slice` — the headline two-prime
  instantiations with `K := ℚ⟮ζ_q⟯`, now **unconditional**: no hypotheses beyond
  characteristic zero, the two primitive roots, and the vanishing sum (numerically
  cross-checked 99/99 at `n = 12` and 999/999 at `n = 18` in O67's exhaustive probe of
  the downstream decomposition; hypothesis satisfiability witnessed in-file over `ℂ`).

* `mu_p_membership_slices` — **non-vacuity of the engine**: the `K = ℚ`, `N = 1`
  instance (`hmin` discharged by `Polynomial.cyclotomic_eq_minpoly_rat`) recovers the
  membership-level O66 slice structure of `vanishing_sum_mu_p_closed` through the new
  machinery.

What is NOT here (honest map): the T1 packet decomposition — de Bruijn's ℕ-cone
extraction (disjoint rotated full packets) needs an induction with packet subtraction
on top of these slice relations (the genuinely de Bruijn positivity step, residual (3)
of the O67 program); the slice relations themselves are now hypothesis-free.

Engine provenance: `packet_mul_coeff` and the body of `vanishing_coeff_slices_over` are
the `K`-generalizations of `LamLeungTwoPow.packet_mul_coeff` and
`LamLeungTwoPow.vanishing_coeff_slices`
(`ArkLib/Data/CodingTheory/ProximityGap/LamLeungTwoPow.lean`), and
`minpoly_adjoin_primitiveRoot_eq_packet` is copied from `CRTPacketMinpoly.lean` —
both copied with provenance since those files' `.olean`s are outside this file's
import budget; dedup is flagged for the next maintenance pass.
-/

namespace DeBruijnTwoPrime

open Polynomial Finset

variable {F : Type*} [Field F]

/-! ## The K-coefficient slice engine

The O68 coefficient-general slice theorem, with the coefficient field generalized from
`ℚ` to an arbitrary field `K` mapping into `F`.  The price of the generalization is the
single hypothesis `hmin`: the `p^(m+1)`-th cyclotomic polynomial must remain the minimal
polynomial of the primitive root over `K` — for `K = ℚ(ζ_{q^b})` with `q ≠ p` this is
the linear disjointness of coprime cyclotomic extensions. -/

section CoefficientSlicesOver

/-- Slices of a geometric-packet multiple: if `deg R < q` then
`(Σ_{i<p} X^(iq) · R).coeff (iq + s) = R.coeff s` for `i < p`, `s < q`.
(Provenance: `LamLeungTwoPow.packet_mul_coeff`, with `ℚ` generalized to `K`.) -/
lemma packet_mul_coeff {K : Type*} [Field K] {p q : ℕ} (_hq : 0 < q) {R : K[X]}
    (hR : R.natDegree < q) {i s : ℕ} (hi : i < p) (hs : s < q) :
    ((∑ i ∈ Finset.range p, (Polynomial.X : K[X]) ^ (i * q)) * R).coeff (i * q + s)
      = R.coeff s := by
  rw [Finset.sum_mul, Polynomial.finset_sum_coeff]
  rw [Finset.sum_eq_single i]
  · rw [show i * q + s = s + i * q from by ring, Polynomial.coeff_X_pow_mul]
  · intro j hj hji
    rw [Polynomial.coeff_X_pow_mul']
    rcases lt_or_ge (i * q + s) (j * q) with hlt | hge
    · rw [if_neg (by omega)]
    · rw [if_pos hge]
      apply Polynomial.coeff_eq_zero_of_natDegree_lt
      rcases lt_or_ge j i with hji' | hji'
      · have : i * q + s - j * q ≥ q := by
          have h1 : (j + 1) * q ≤ i * q := Nat.mul_le_mul_right q (by omega)
          have h2 : j * q + q ≤ i * q := by
            calc j * q + q = (j + 1) * q := by ring
            _ ≤ i * q := h1
          omega
        omega
      · have hj1 : i + 1 ≤ j := by omega
        have : i * q + q ≤ j * q := by
          calc i * q + q = (i + 1) * q := by ring
          _ ≤ j * q := Nat.mul_le_mul_right q hj1
        omega
  · intro hnotin
    exact absurd (Finset.mem_range.mpr hi) hnotin

/-- **The K-coefficient prime-power slice theorem** (the linear-disjointness slice
engine): if `Φ_{p^(m+1)}` is still the minimal polynomial of the primitive `p^(m+1)`-th
root `ζ ∈ F` over the coefficient field `K` (hypothesis `hmin`), then any vanishing
`K`-linear combination of `ζ^e`, `e < p^(m+1)`, has all `p` of its length-`p^m`
coefficient slices equal.
(Provenance: body mirrors `LamLeungTwoPow.vanishing_coeff_slices`, `ℚ ↝ K`, with
`cyclotomic_eq_minpoly_rat` replaced by `hmin`.) -/
theorem vanishing_coeff_slices_over (K : Type*) [Field K] [Algebra K F]
    {p m : ℕ} (hp : p.Prime) {ζ : F}
    (_hζ : IsPrimitiveRoot ζ (p ^ (m + 1)))
    (hmin : minpoly K ζ = Polynomial.cyclotomic (p ^ (m + 1)) K)
    (c : ℕ → K)
    (hsum : ∑ e ∈ Finset.range (p ^ (m + 1)), algebraMap K F (c e) * ζ ^ e = 0) :
    ∀ s < p ^ m, ∀ i < p, ∀ i' < p, c (i * p ^ m + s) = c (i' * p ^ m + s) := by
  classical
  set n := p ^ (m + 1) with hn
  set q := p ^ m with hq
  have hppos : 0 < p := hp.pos
  have hqpos : 0 < q := by positivity
  have hnq : n = p * q := by rw [hn, hq]; ring
  have hnpos : 0 < n := by rw [hn]; positivity
  set P : K[X] := ∑ e ∈ Finset.range n, Polynomial.C (c e) * X ^ e with hP
  have hPcoeff : ∀ j < n, P.coeff j = c j := by
    intro j hj
    rw [hP, Polynomial.finset_sum_coeff]
    rw [Finset.sum_congr rfl (fun e _ => by
      rw [Polynomial.coeff_C_mul, Polynomial.coeff_X_pow])]
    rw [Finset.sum_eq_single j (fun e _ hej => by
      rw [if_neg (fun h => hej h.symm), mul_zero]) (fun h =>
      absurd (Finset.mem_range.mpr hj) h)]
    rw [if_pos rfl, mul_one]
  have hPζ : Polynomial.aeval ζ P = 0 := by
    rw [hP, map_sum]
    rw [Finset.sum_congr rfl (fun e _ => by
      rw [map_mul, Polynomial.aeval_C, map_pow, Polynomial.aeval_X])]
    exact hsum
  have hdvd : (∑ i ∈ Finset.range p, (X : K[X]) ^ (i * q)) ∣ P := by
    have hmin' := minpoly.dvd K ζ hPζ
    rw [hmin] at hmin'
    have hcyc : Polynomial.cyclotomic n K
        = ∑ i ∈ Finset.range p, (X : K[X]) ^ (i * q) := by
      rw [hn, Polynomial.cyclotomic_prime_pow_eq_geom_sum hp]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [← pow_mul, hq, mul_comm]
    rwa [hcyc] at hmin'
  intro s hs i hi i' hi'
  have hb : ∀ j < p, j * q + s < n := by
    intro j hj
    rw [hnq]
    have h1 : (j + 1) * q ≤ p * q := Nat.mul_le_mul_right q (by omega)
    have : j * q + q ≤ p * q := by
      calc j * q + q = (j + 1) * q := by ring
      _ ≤ p * q := h1
    omega
  rw [← hPcoeff _ (hb i hi), ← hPcoeff _ (hb i' hi')]
  obtain ⟨R, hR⟩ := hdvd
  by_cases hP0 : P = 0
  · simp [hP0]
  have hR0 : R ≠ 0 := fun h => hP0 (by rw [hR, h, mul_zero])
  have hG : (∑ i ∈ Finset.range p, (X : K[X]) ^ (i * q)) ≠ 0 := by
    intro h
    have := congrArg (fun Q : K[X] => Q.coeff 0) h
    simp only [Polynomial.finset_sum_coeff] at this
    rw [Finset.sum_eq_single 0 (fun j _ hj => by
      rw [Polynomial.coeff_X_pow]
      rw [if_neg (by
        intro h0
        rcases Nat.mul_eq_zero.mp h0.symm with h | h
        · exact hj h
        · omega)]) (fun h0 => absurd (Finset.mem_range.mpr hppos) h0)] at this
    simp at this
  have hdegP : P.natDegree < n := by
    rw [hP]
    have hle : (∑ e ∈ Finset.range n, Polynomial.C (c e) * (X : K[X]) ^ e).natDegree
        ≤ n - 1 :=
      Polynomial.natDegree_sum_le_of_forall_le _ _ fun e he => by
        refine le_trans (Polynomial.natDegree_C_mul_le _ _) ?_
        rw [Polynomial.natDegree_X_pow]
        have := Finset.mem_range.mp he
        omega
    omega
  have hdegR : R.natDegree < q := by
    have hmul := Polynomial.natDegree_mul hG hR0
    rw [← hR] at hmul
    have hGlow : (p - 1) * q ≤ (∑ i ∈ Finset.range p, (X : K[X]) ^ (i * q)).natDegree := by
      apply Polynomial.le_natDegree_of_ne_zero
      rw [Polynomial.finset_sum_coeff]
      rw [Finset.sum_eq_single (p - 1) (fun j hj hjne => by
        rw [Polynomial.coeff_X_pow, if_neg (fun h => hjne (by
          have := Nat.eq_of_mul_eq_mul_right hqpos h
          omega))]) (fun h0 => absurd (Finset.mem_range.mpr (by omega)) h0)]
      rw [Polynomial.coeff_X_pow, if_pos rfl]
      exact one_ne_zero
    have hcount : (p - 1) * q + q = n := by
      rw [hnq]
      calc (p - 1) * q + q = ((p - 1) + 1) * q := by ring
      _ = p * q := by congr 1; omega
    omega
  rw [hR, packet_mul_coeff hqpos hdegR hi hs, packet_mul_coeff hqpos hdegR hi' hs]

/-- The `K = ℚ` instance: the rational coefficient-slice theorem, with the
linear-disjointness hypothesis discharged by `Polynomial.cyclotomic_eq_minpoly_rat`.
(This recovers `LamLeungTwoPow.vanishing_coeff_slices` through the generalized engine —
the satisfiability witness for the `hmin` hypothesis shape.) -/
theorem vanishing_coeff_slices_rat [CharZero F] {p m : ℕ} (hp : p.Prime) {ζ : F}
    (hζ : IsPrimitiveRoot ζ (p ^ (m + 1)))
    (c : ℕ → ℚ)
    (hsum : ∑ e ∈ Finset.range (p ^ (m + 1)), (c e : F) * ζ ^ e = 0) :
    ∀ s < p ^ m, ∀ i < p, ∀ i' < p, c (i * p ^ m + s) = c (i' * p ^ m + s) := by
  refine vanishing_coeff_slices_over ℚ hp hζ
    (Polynomial.cyclotomic_eq_minpoly_rat hζ (pow_pos hp.pos _)).symm c ?_
  simpa only [eq_ratCast] using hsum

end CoefficientSlicesOver

/-! ## The CRT box: parametrizing `μ_{M·N}` by `μ_M × μ_N`

For coprime `M`, `N`, the map `(u, v) ↦ x^u · y^v` (with `x`, `y` primitive `M`-th and
`N`-th roots) is a bijection from `[0,M) × [0,N)` onto the `(M·N)`-th roots of unity —
the exponent CRT coordinates that the double-slice argument groups along. -/

section CRTBox

/-- The product of primitive roots of coprime orders is a primitive root of the
product order. -/
lemma isPrimitiveRoot_mul {M N : ℕ} {x y : F} (hx : IsPrimitiveRoot x M)
    (hy : IsPrimitiveRoot y N) (hcop : Nat.Coprime M N) :
    IsPrimitiveRoot (x * y) (M * N) := by
  have hord : orderOf (x * y) = orderOf x * orderOf y :=
    (Commute.all x y).orderOf_mul_eq_mul_orderOf_of_coprime
      (by rw [← hx.eq_orderOf, ← hy.eq_orderOf]; exact hcop)
  have h := IsPrimitiveRoot.orderOf (x * y)
  rwa [hord, ← hx.eq_orderOf, ← hy.eq_orderOf] at h

/-- A primitive root of positive order is nonzero. -/
lemma prim_ne_zero {M : ℕ} {x : F} (hx : IsPrimitiveRoot x M) (hM : 0 < M) : x ≠ 0 := by
  intro h0
  have h1 := hx.pow_eq_one
  rw [h0, zero_pow hM.ne'] at h1
  exact zero_ne_one h1

/-- **Injectivity of the CRT box**: `x^u · y^v` determines `(u, v)` on
`[0,M) × [0,N)` when `M`, `N` are coprime. -/
lemma box_pair_inj {M N : ℕ} {x y : F} (hx : IsPrimitiveRoot x M) (hy : IsPrimitiveRoot y N)
    (hcop : Nat.Coprime M N) {u v u' v' : ℕ} (hu : u < M) (hv : v < N) (hu' : u' < M)
    (hv' : v' < N) (h : x ^ u * y ^ v = x ^ u' * y ^ v') : u = u' ∧ v = v' := by
  have hM : 0 < M := lt_of_le_of_lt (Nat.zero_le u) hu
  have hN : 0 < N := lt_of_le_of_lt (Nat.zero_le v) hv
  have hx0 : x ≠ 0 := prim_ne_zero hx hM
  have hy0 : y ≠ 0 := prim_ne_zero hy hN
  have hxu' : x ^ u' ≠ 0 := pow_ne_zero _ hx0
  have hyv : y ^ v ≠ 0 := pow_ne_zero _ hy0
  have hpowM : ∀ k : ℕ, (x ^ k) ^ M = 1 := fun k => by
    rw [← pow_mul, mul_comm, pow_mul, hx.pow_eq_one, one_pow]
  have hpowN : ∀ k : ℕ, (y ^ k) ^ N = 1 := fun k => by
    rw [← pow_mul, mul_comm, pow_mul, hy.pow_eq_one, one_pow]
  set t := x ^ u / x ^ u' with ht
  have ht2 : t = y ^ v' / y ^ v := by
    rw [ht, div_eq_div_iff hxu' hyv]
    linear_combination h
  have htM : t ^ M = 1 := by rw [ht, div_pow, hpowM u, hpowM u', div_one]
  have htN : t ^ N = 1 := by rw [ht2, div_pow, hpowN v', hpowN v, div_one]
  have hdvd1 : orderOf t ∣ 1 := by
    have hg : orderOf t ∣ Nat.gcd M N :=
      Nat.dvd_gcd (orderOf_dvd_of_pow_eq_one htM) (orderOf_dvd_of_pow_eq_one htN)
    rwa [Nat.Coprime.gcd_eq_one hcop] at hg
  have ht1 : t = 1 := orderOf_eq_one_iff.mp (Nat.dvd_one.mp hdvd1)
  have hxx : x ^ u = x ^ u' := by
    rw [ht] at ht1
    calc x ^ u = x ^ u / x ^ u' * x ^ u' := (div_mul_cancel₀ _ hxu').symm
    _ = 1 * x ^ u' := by rw [ht1]
    _ = x ^ u' := one_mul _
  have huu : u = u' := hx.pow_inj hu hu' hxx
  refine ⟨huu, hy.pow_inj hv hv' ?_⟩
  have h2 := h
  rw [huu] at h2
  exact mul_left_cancel₀ hxu' h2

/-- **Surjectivity of the CRT box**: every `(M·N)`-th root of unity is `x^u · y^v` for
some `(u, v)` in the box (no Bezout needed: reduce the joint exponent mod each order). -/
lemma box_pair_surj {M N : ℕ} {x y : F} (hx : IsPrimitiveRoot x M) (hy : IsPrimitiveRoot y N)
    (hcop : Nat.Coprime M N) (hM : 0 < M) (hN : 0 < N) {z : F} (hz : z ^ (M * N) = 1) :
    ∃ u < M, ∃ v < N, x ^ u * y ^ v = z := by
  haveI : NeZero (M * N) := ⟨(Nat.mul_pos hM hN).ne'⟩
  obtain ⟨e, _, hez⟩ := (isPrimitiveRoot_mul hx hy hcop).eq_pow_of_pow_eq_one hz
  refine ⟨e % M, Nat.mod_lt _ hM, e % N, Nat.mod_lt _ hN, ?_⟩
  have hxe : x ^ (e % M) = x ^ e := by
    conv_rhs => rw [← Nat.div_add_mod e M]
    rw [pow_add, pow_mul, hx.pow_eq_one, one_pow, one_mul]
  have hye : y ^ (e % N) = y ^ e := by
    conv_rhs => rw [← Nat.div_add_mod e N]
    rw [pow_add, pow_mul, hy.pow_eq_one, one_pow, one_mul]
  rw [hxe, hye, ← mul_pow]
  exact hez

end CRTBox

/-! ## The q-side grouping and the T2 double-slice structure theorem -/

section QSideGrouping

variable [DecidableEq F] {K : Type*} [Field K]

/-- **The q-side grouped coefficient** `γ_u ∈ K`: the generating sum of the `u`-th
`x`-row of `S` against the `K`-side root `z_q` (whose image in `F` is `y`):
`γ_u = Σ_{v<N} 1_S(x^u·y^v) · z_q^v`. -/
def gammaQ (S : Finset F) (x y : F) (zq : K) (N u : ℕ) : K :=
  ∑ v ∈ Finset.range N, (if x ^ u * y ^ v ∈ S then (1 : K) else 0) * zq ^ v

variable [Algebra K F]

/-- The image of `γ_u` in `F` is the same generating sum with `y`-powers. -/
lemma map_gammaQ (S : Finset F) (x : F) {y : F} {zq : K}
    (hzq : algebraMap K F zq = y) (N u : ℕ) :
    algebraMap K F (gammaQ S x y zq N u)
      = ∑ v ∈ Finset.range N, (if x ^ u * y ^ v ∈ S then (1 : F) else 0) * y ^ v := by
  rw [gammaQ, map_sum]
  refine Finset.sum_congr rfl fun v _ => ?_
  rw [map_mul, map_pow, hzq, apply_ite (algebraMap K F), map_one, map_zero]

/-- **The grouped-sum identity**: summing the `F`-side grouped row sums against `x^u`
recovers the total sum of `S` (via the CRT box bijection). -/
lemma grouped_sum {M N : ℕ} {x y : F} (hx : IsPrimitiveRoot x M) (hy : IsPrimitiveRoot y N)
    (hcop : Nat.Coprime M N) (hM : 0 < M) (hN : 0 < N) {S : Finset F}
    (hS : ∀ z ∈ S, z ^ (M * N) = 1) :
    ∑ u ∈ Finset.range M, (∑ v ∈ Finset.range N,
        (if x ^ u * y ^ v ∈ S then (1 : F) else 0) * y ^ v) * x ^ u
      = ∑ z ∈ S, z := by
  have hstep : ∀ u ∈ Finset.range M, (∑ v ∈ Finset.range N,
      (if x ^ u * y ^ v ∈ S then (1 : F) else 0) * y ^ v) * x ^ u
      = ∑ v ∈ Finset.range N, (if x ^ u * y ^ v ∈ S then x ^ u * y ^ v else 0) := by
    intro u _
    rw [Finset.sum_mul]
    refine Finset.sum_congr rfl fun v _ => ?_
    split_ifs with h <;> ring
  rw [Finset.sum_congr rfl hstep, ← Finset.sum_product', ← Finset.sum_filter]
  apply Finset.sum_bij (fun uv _ => x ^ uv.1 * y ^ uv.2)
  · intro uv huv
    exact (Finset.mem_filter.mp huv).2
  · intro uv1 h1 uv2 h2 heq
    have hm1 := Finset.mem_product.mp (Finset.mem_filter.mp h1).1
    have hm2 := Finset.mem_product.mp (Finset.mem_filter.mp h2).1
    obtain ⟨he1, he2⟩ := box_pair_inj hx hy hcop (Finset.mem_range.mp hm1.1)
      (Finset.mem_range.mp hm1.2) (Finset.mem_range.mp hm2.1)
      (Finset.mem_range.mp hm2.2) heq
    exact Prod.ext he1 he2
  · intro z hz
    obtain ⟨u, hu, v, hv, huv⟩ := box_pair_surj hx hy hcop hM hN (hS z hz)
    exact ⟨(u, v), Finset.mem_filter.mpr ⟨Finset.mem_product.mpr
      ⟨Finset.mem_range.mpr hu, Finset.mem_range.mpr hv⟩,
      (by rw [huv]; exact hz)⟩, huv⟩
  · intro uv _
    rfl

/-- **T2 — the double-slice structure theorem** (general second factor): for a finite
`S ⊆ μ_{p^(m+1)·N}` with vanishing sum, `N` coprime to `p^(m+1)`, the q-side grouped
coefficients `γ_u ∈ K` are constant along `μ_p`-coset directions of the `x`-exponent:
`γ_{i·p^m+s} = γ_{i'·p^m+s}` for all `i, i' < p`, `s < p^m`.  The ONE named hypothesis
is `hmin` (linear disjointness): `Φ_{p^(m+1)}` stays the minimal polynomial of `x`
over `K`. -/
theorem qside_slices_over {p m N : ℕ} (hp : p.Prime) (hN : 0 < N)
    {x y : F} (hx : IsPrimitiveRoot x (p ^ (m + 1))) (hy : IsPrimitiveRoot y N)
    (hcop : Nat.Coprime (p ^ (m + 1)) N)
    {zq : K} (hzq : algebraMap K F zq = y)
    (hmin : minpoly K x = Polynomial.cyclotomic (p ^ (m + 1)) K)
    {S : Finset F} (hS : ∀ z ∈ S, z ^ (p ^ (m + 1) * N) = 1)
    (hsum : ∑ z ∈ S, z = 0) :
    ∀ s < p ^ m, ∀ i < p, ∀ i' < p,
      gammaQ S x y zq N (i * p ^ m + s) = gammaQ S x y zq N (i' * p ^ m + s) := by
  refine vanishing_coeff_slices_over K hp hx hmin (fun e => gammaQ S x y zq N e) ?_
  calc ∑ e ∈ Finset.range (p ^ (m + 1)), algebraMap K F (gammaQ S x y zq N e) * x ^ e
      = ∑ e ∈ Finset.range (p ^ (m + 1)),
          (∑ v ∈ Finset.range N, (if x ^ e * y ^ v ∈ S then (1 : F) else 0) * y ^ v)
            * x ^ e :=
        Finset.sum_congr rfl fun e _ => by rw [map_gammaQ S x hzq N e]
    _ = ∑ z ∈ S, z := grouped_sum hx hy hcop (pow_pos hp.pos _) hN hS
    _ = 0 := hsum

/-- **T3a — the `{−1,0,1}`-difference lemma**: the T2 slice equalities, pushed to `F`,
say that the membership-difference pattern between two `μ_p`-coset-related rows is a
vanishing sum of `y`-powers with coefficients in `{−1,0,1} ⊆ ℚ`. -/
theorem slice_difference_vanishing [CharZero F] {p m N : ℕ} (hp : p.Prime) (hN : 0 < N)
    {x y : F} (hx : IsPrimitiveRoot x (p ^ (m + 1))) (hy : IsPrimitiveRoot y N)
    (hcop : Nat.Coprime (p ^ (m + 1)) N)
    {zq : K} (hzq : algebraMap K F zq = y)
    (hmin : minpoly K x = Polynomial.cyclotomic (p ^ (m + 1)) K)
    {S : Finset F} (hS : ∀ z ∈ S, z ^ (p ^ (m + 1) * N) = 1)
    (hsum : ∑ z ∈ S, z = 0) :
    ∀ s < p ^ m, ∀ i < p, ∀ i' < p,
      ∑ v ∈ Finset.range N,
        (((if x ^ (i * p ^ m + s) * y ^ v ∈ S then (1 : ℚ) else 0)
          - (if x ^ (i' * p ^ m + s) * y ^ v ∈ S then (1 : ℚ) else 0) : ℚ) : F)
          * y ^ v = 0 := by
  intro s hs i hi i' hi'
  have hg := qside_slices_over hp hN hx hy hcop hzq hmin hS hsum s hs i hi i' hi'
  have hgF := congrArg (algebraMap K F) hg
  rw [map_gammaQ S x hzq, map_gammaQ S x hzq] at hgF
  have hterm : ∀ v : ℕ,
      (((if x ^ (i * p ^ m + s) * y ^ v ∈ S then (1 : ℚ) else 0)
        - (if x ^ (i' * p ^ m + s) * y ^ v ∈ S then (1 : ℚ) else 0) : ℚ) : F) * y ^ v
      = (if x ^ (i * p ^ m + s) * y ^ v ∈ S then (1 : F) else 0) * y ^ v
        - (if x ^ (i' * p ^ m + s) * y ^ v ∈ S then (1 : F) else 0) * y ^ v := by
    intro v
    rw [Rat.cast_sub, apply_ite (Rat.cast : ℚ → F), apply_ite (Rat.cast : ℚ → F),
      Rat.cast_one, Rat.cast_zero, sub_mul]
  rw [Finset.sum_congr rfl fun v _ => hterm v, Finset.sum_sub_distrib, hgF, sub_self]

/-- **T3b — the full two-prime double-slice theorem** (the de Bruijn structure at the
slice level): for `S ⊆ μ_{p^(m+1)·q^(b+1)}` with vanishing sum, the membership
difference pattern between two `μ_p`-coset-related rows is constant along `μ_q`-coset
directions — the rational slice theorem applied at the second prime to the T3a
difference sums. -/
theorem two_prime_double_slice [CharZero F] {p m q b : ℕ} (hp : p.Prime) (hq : q.Prime)
    {x y : F} (hx : IsPrimitiveRoot x (p ^ (m + 1))) (hy : IsPrimitiveRoot y (q ^ (b + 1)))
    (hcop : Nat.Coprime (p ^ (m + 1)) (q ^ (b + 1)))
    {zq : K} (hzq : algebraMap K F zq = y)
    (hmin : minpoly K x = Polynomial.cyclotomic (p ^ (m + 1)) K)
    {S : Finset F} (hS : ∀ z ∈ S, z ^ (p ^ (m + 1) * q ^ (b + 1)) = 1)
    (hsum : ∑ z ∈ S, z = 0) :
    ∀ s < p ^ m, ∀ i < p, ∀ i' < p, ∀ t < q ^ b, ∀ j < q, ∀ j' < q,
      (if x ^ (i * p ^ m + s) * y ^ (j * q ^ b + t) ∈ S then (1 : ℚ) else 0)
        - (if x ^ (i' * p ^ m + s) * y ^ (j * q ^ b + t) ∈ S then (1 : ℚ) else 0)
      = (if x ^ (i * p ^ m + s) * y ^ (j' * q ^ b + t) ∈ S then (1 : ℚ) else 0)
        - (if x ^ (i' * p ^ m + s) * y ^ (j' * q ^ b + t) ∈ S then (1 : ℚ) else 0) := by
  intro s hs i hi i' hi'
  have hdiff := slice_difference_vanishing hp (pow_pos hq.pos _) hx hy hcop hzq hmin
    hS hsum s hs i hi i' hi'
  exact vanishing_coeff_slices_rat hq hy
    (fun v => (if x ^ (i * p ^ m + s) * y ^ v ∈ S then (1 : ℚ) else 0)
      - (if x ^ (i' * p ^ m + s) * y ^ v ∈ S then (1 : ℚ) else 0)) hdiff

end QSideGrouping

/-! ## Discharging the linear-disjointness hypothesis

`Φ_{p^(a+1)}` stays the minimal polynomial of `ζ_p` over the coprime cyclotomic
extension `ℚ(ζ_{q^b})`.  Engine: `minpoly ℚ⟮ζq⟯ ζp ∣ Φ_{p^(a+1)}` pinched against the
totient tower bound `φ(q^b)·φ(p^(a+1)) = φ(q^b·p^(a+1)) = [ℚ(ζ_qζ_p):ℚ] ≤
φ(q^b)·[ℚ⟮ζq⟯⟮ζp⟯:ℚ⟮ζq⟯]`, then monic divisor of matching degree.

Provenance: `minpoly_adjoin_primitiveRoot_eq_packet` (and its integrality helper) is
copied verbatim, modulo namespace, from
`ArkLib/Data/CodingTheory/ProximityGap/CRTPacketMinpoly.lean` (the parallel de Bruijn
step-(1) lane of this corpus), because this file's import budget is Mathlib-only;
dedup to a shared home is flagged for the next maintenance pass. -/

section LinearDisjointness

open IntermediateField Module

/-- Roots of unity are integral over any base field of the ambient field.
(Provenance: `CRTPacketMinpoly.isIntegral_of_pow_eq_one`.) -/
private lemma isIntegral_of_pow_eq_one {K L : Type*} [Field K] [Field L] [Algebra K L]
    {x : L} {m : ℕ} (hm : 0 < m) (hx : x ^ m = 1) : IsIntegral K x :=
  ⟨X ^ m - 1, by simpa using monic_X_pow_sub_C (1 : K) hm.ne', by simp [hx]⟩

/-- **The packet minimal polynomial over the coprime cyclotomic extension**: for
distinct primes `p ≠ q`, `0 < b`, a primitive `p^a`-th root `ξ` and a primitive
`q^b`-th root `η` in a characteristic-zero field `L`, the minimal polynomial of `η`
over `ℚ⟮ξ⟯ = ℚ(ζ_{p^a})` is the geometric packet `Σ_{t<q} X^(t·q^(b-1))` — i.e.
`Φ_{q^b}` remains irreducible over the coprime cyclotomic extension.
(Provenance: `CRTPacketMinpoly.minpoly_adjoin_primitiveRoot_eq_packet`.) -/
theorem minpoly_adjoin_primitiveRoot_eq_packet
    {L : Type*} [Field L] [CharZero L] {p q a b : ℕ}
    (hp : p.Prime) (hq : q.Prime) (hpq : p ≠ q) (hb : 0 < b)
    {ξ η : L} (hξ : IsPrimitiveRoot ξ (p ^ a)) (hη : IsPrimitiveRoot η (q ^ b)) :
    minpoly ℚ⟮ξ⟯ η = ∑ t ∈ Finset.range q, (X : Polynomial ℚ⟮ξ⟯) ^ (t * q ^ (b - 1)) := by
  classical
  have hpa : 0 < p ^ a := pow_pos hp.pos a
  have hqb : 0 < q ^ b := pow_pos hq.pos b
  have hn : 0 < p ^ a * q ^ b := Nat.mul_pos hpa hqb
  have hco : Nat.Coprime (p ^ a) (q ^ b) :=
    Nat.Coprime.pow a b ((Nat.coprime_primes hp hq).mpr hpq)
  -- integrality of the three roots involved
  have hintξ : IsIntegral ℚ ξ := isIntegral_of_pow_eq_one hpa hξ.pow_eq_one
  have hintηK : IsIntegral ℚ⟮ξ⟯ η := isIntegral_of_pow_eq_one hqb hη.pow_eq_one
  -- `ξ * η` is a primitive `(p^a * q^b)`-th root of unity (coprime orders multiply)
  have h1 : orderOf ξ = p ^ a := hξ.eq_orderOf.symm
  have h2 : orderOf η = q ^ b := hη.eq_orderOf.symm
  have horder : orderOf (ξ * η) = p ^ a * q ^ b := by
    rw [(Commute.all ξ η).orderOf_mul_eq_mul_orderOf_of_coprime
      (by rw [h1, h2]; exact hco), h1, h2]
  have hζ : IsPrimitiveRoot (ξ * η) (p ^ a * q ^ b) :=
    horder ▸ IsPrimitiveRoot.orderOf (ξ * η)
  have hintζ : IsIntegral ℚ (ξ * η) := isIntegral_of_pow_eq_one hn hζ.pow_eq_one
  -- absolute degrees over ℚ, via unconditional rationals-cyclotomic irreducibility
  have hrkK : finrank ℚ ℚ⟮ξ⟯ = (p ^ a).totient := by
    rw [IntermediateField.adjoin.finrank hintξ, ← cyclotomic_eq_minpoly_rat hξ hpa,
      natDegree_cyclotomic]
  have hrkZ : finrank ℚ ℚ⟮ξ * η⟯ = (p ^ a * q ^ b).totient := by
    rw [IntermediateField.adjoin.finrank hintζ, ← cyclotomic_eq_minpoly_rat hζ hn,
      natDegree_cyclotomic]
  -- finite dimensionality up the tower
  haveI : FiniteDimensional ℚ ℚ⟮ξ⟯ := IntermediateField.adjoin.finiteDimensional hintξ
  haveI : FiniteDimensional ℚ⟮ξ⟯ ℚ⟮ξ⟯⟮η⟯ := IntermediateField.adjoin.finiteDimensional hintηK
  haveI : FiniteDimensional ℚ ℚ⟮ξ⟯⟮η⟯ := Module.Finite.trans ℚ⟮ξ⟯ ℚ⟮ξ⟯⟮η⟯
  -- `ξ * η` lives in `ℚ⟮ξ⟯⟮η⟯`
  have hξE : ξ ∈ ℚ⟮ξ⟯⟮η⟯ := by
    have h := ℚ⟮ξ⟯⟮η⟯.algebraMap_mem ⟨ξ, mem_adjoin_simple_self ℚ ξ⟩
    simpa using h
  have hηE : η ∈ ℚ⟮ξ⟯⟮η⟯ := mem_adjoin_simple_self ℚ⟮ξ⟯ η
  have hsub : ∀ {x : L}, x ∈ ℚ⟮ξ * η⟯ → x ∈ ℚ⟮ξ⟯⟮η⟯ := by
    intro x hx
    have hle : ℚ⟮ξ * η⟯ ≤ (ℚ⟮ξ⟯⟮η⟯).restrictScalars ℚ := by
      rw [adjoin_le_iff]
      intro y hy
      rw [Set.mem_singleton_iff] at hy
      subst hy
      -- membership in `restrictScalars` is definitionally membership (`Iff.rfl`)
      exact mul_mem hξE hηE
    exact hle hx
  -- ℚ-linear embedding `ℚ⟮ξ * η⟯ ↪ ℚ⟮ξ⟯⟮η⟯` gives the degree lower bound
  let f : ℚ⟮ξ * η⟯ →ₗ[ℚ] ℚ⟮ξ⟯⟮η⟯ :=
    { toFun := fun x => ⟨x.1, hsub x.2⟩
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  have hinj : Function.Injective f := fun x y hxy => by
    have h1 := congrArg Subtype.val hxy
    exact Subtype.ext h1
  have hle : finrank ℚ ℚ⟮ξ * η⟯ ≤ finrank ℚ ℚ⟮ξ⟯⟮η⟯ :=
    LinearMap.finrank_le_finrank_of_injective hinj
  have htower : finrank ℚ ℚ⟮ξ⟯ * finrank ℚ⟮ξ⟯ ℚ⟮ξ⟯⟮η⟯ = finrank ℚ ℚ⟮ξ⟯⟮η⟯ :=
    Module.finrank_mul_finrank ℚ ℚ⟮ξ⟯ ℚ⟮ξ⟯⟮η⟯
  -- the totient tower bound: `φ(q^b) ≤ natDegree (minpoly ℚ⟮ξ⟯ η)`
  have hdeg_ge : (q ^ b).totient ≤ (minpoly ℚ⟮ξ⟯ η).natDegree := by
    have hmul : (p ^ a).totient * (q ^ b).totient
        ≤ (p ^ a).totient * finrank ℚ⟮ξ⟯ ℚ⟮ξ⟯⟮η⟯ := by
      calc (p ^ a).totient * (q ^ b).totient
          = (p ^ a * q ^ b).totient := (Nat.totient_mul hco).symm
        _ = finrank ℚ ℚ⟮ξ * η⟯ := hrkZ.symm
        _ ≤ finrank ℚ ℚ⟮ξ⟯⟮η⟯ := hle
        _ = finrank ℚ ℚ⟮ξ⟯ * finrank ℚ⟮ξ⟯ ℚ⟮ξ⟯⟮η⟯ := htower.symm
        _ = (p ^ a).totient * finrank ℚ⟮ξ⟯ ℚ⟮ξ⟯⟮η⟯ := by rw [hrkK]
    have h2 : (q ^ b).totient ≤ finrank ℚ⟮ξ⟯ ℚ⟮ξ⟯⟮η⟯ :=
      Nat.le_of_mul_le_mul_left hmul (Nat.totient_pos.mpr hpa)
    rwa [IntermediateField.adjoin.finrank hintηK] at h2
  -- divisibility: `minpoly ℚ⟮ξ⟯ η ∣ Φ_{q^b}` over `ℚ⟮ξ⟯`
  have hdvd : minpoly ℚ⟮ξ⟯ η ∣ cyclotomic (q ^ b) ℚ⟮ξ⟯ := by
    apply minpoly.dvd
    rw [aeval_def, ← eval_map, map_cyclotomic]
    exact hη.isRoot_cyclotomic hqb
  -- monic divisor of matching degree: the minimal polynomial IS the cyclotomic
  have heq : cyclotomic (q ^ b) ℚ⟮ξ⟯ = minpoly ℚ⟮ξ⟯ η :=
    Polynomial.eq_of_monic_of_dvd_of_natDegree_le (minpoly.monic hintηK)
      (cyclotomic.monic _ _) hdvd (by rwa [natDegree_cyclotomic])
  -- and at a prime power the cyclotomic is the geometric packet
  obtain ⟨b', rfl⟩ : ∃ b', b = b' + 1 := ⟨b - 1, (Nat.succ_pred_eq_of_pos hb).symm⟩
  rw [← heq, cyclotomic_prime_pow_eq_geom_sum hq]
  refine Finset.sum_congr rfl fun t _ => ?_
  rw [Nat.add_sub_cancel, mul_comm t (q ^ b'), pow_mul]

/-- **The `hdisj` discharge in the headline's shape**: `Φ_{p^(a+1)}` IS the minimal
polynomial of `ζ_p` over `ℚ⟮ζ_q⟯` for any primitive `q^b`-th root `ζ_q`, `q ≠ p` —
the linear disjointness of coprime cyclotomic extensions as a theorem. -/
theorem minpoly_qadjoin_eq_cyclotomic {L : Type*} [Field L] [CharZero L] {p q a b : ℕ}
    (hp : p.Prime) (hq : q.Prime) (hpq : p ≠ q)
    {ζp ζq : L} (hζp : IsPrimitiveRoot ζp (p ^ (a + 1)))
    (hζq : IsPrimitiveRoot ζq (q ^ b)) :
    minpoly ℚ⟮ζq⟯ ζp = Polynomial.cyclotomic (p ^ (a + 1)) ℚ⟮ζq⟯ := by
  rw [minpoly_adjoin_primitiveRoot_eq_packet hq hp hpq.symm (Nat.succ_pos a) hζq hζp,
    Polynomial.cyclotomic_prime_pow_eq_geom_sum hp]
  refine Finset.sum_congr rfl fun t _ => ?_
  rw [Nat.succ_sub_one, mul_comm t (p ^ a), pow_mul]

end LinearDisjointness

/-! ## The headline two-prime instantiations: `K := ℚ(ζ_q)`, unconditional

The former `hdisj` hypothesis is discharged by `minpoly_qadjoin_eq_cyclotomic`: the
headline theorems have NO hypotheses beyond characteristic zero, the two primitive
roots, and the vanishing sum. -/

section TwoPrimeHeadline

open IntermediateField

variable [DecidableEq F] [CharZero F]

/-- **The two-prime q-side slice theorem** at `K := ℚ(ζ_q)`, unconditional: for
`S ⊆ μ_{p^(a+1)·q^b}` with vanishing sum (`p ≠ q` primes), the `ℚ(ζ_q)`-valued
q-side grouped coefficients are constant along `μ_p`-coset directions. -/
theorem two_prime_qside_slices {p q a b : ℕ} (hp : p.Prime) (hq : q.Prime) (hpq : p ≠ q)
    {ζp ζq : F} (hζp : IsPrimitiveRoot ζp (p ^ (a + 1))) (hζq : IsPrimitiveRoot ζq (q ^ b))
    {S : Finset F} (hS : ∀ z ∈ S, z ^ (p ^ (a + 1) * q ^ b) = 1)
    (hsum : ∑ z ∈ S, z = 0) :
    ∀ s < p ^ a, ∀ i < p, ∀ i' < p,
      gammaQ S ζp ζq (AdjoinSimple.gen ℚ ζq) (q ^ b) (i * p ^ a + s)
        = gammaQ S ζp ζq (AdjoinSimple.gen ℚ ζq) (q ^ b) (i' * p ^ a + s) :=
  qside_slices_over hp (pow_pos hq.pos b) hζp hζq
    (Nat.Coprime.pow _ _ ((Nat.coprime_primes hp hq).mpr hpq))
    (AdjoinSimple.algebraMap_gen ℚ ζq)
    (minpoly_qadjoin_eq_cyclotomic hp hq hpq hζp hζq) hS hsum

/-- **The headline two-prime de Bruijn double-slice theorem** at `K := ℚ(ζ_q)`,
unconditional: in characteristic zero, for a finite subset `S` of `μ_{p^(a+1)·q^(b+1)}`
with vanishing sum, the membership difference pattern between any two `μ_p`-coset-related
rows is constant along `μ_q`-coset directions of the column index. -/
theorem two_prime_deBruijn_double_slice {p q a b : ℕ} (hp : p.Prime) (hq : q.Prime)
    (hpq : p ≠ q) {ζp ζq : F} (hζp : IsPrimitiveRoot ζp (p ^ (a + 1)))
    (hζq : IsPrimitiveRoot ζq (q ^ (b + 1)))
    {S : Finset F} (hS : ∀ z ∈ S, z ^ (p ^ (a + 1) * q ^ (b + 1)) = 1)
    (hsum : ∑ z ∈ S, z = 0) :
    ∀ s < p ^ a, ∀ i < p, ∀ i' < p, ∀ t < q ^ b, ∀ j < q, ∀ j' < q,
      (if ζp ^ (i * p ^ a + s) * ζq ^ (j * q ^ b + t) ∈ S then (1 : ℚ) else 0)
        - (if ζp ^ (i' * p ^ a + s) * ζq ^ (j * q ^ b + t) ∈ S then (1 : ℚ) else 0)
      = (if ζp ^ (i * p ^ a + s) * ζq ^ (j' * q ^ b + t) ∈ S then (1 : ℚ) else 0)
        - (if ζp ^ (i' * p ^ a + s) * ζq ^ (j' * q ^ b + t) ∈ S then (1 : ℚ) else 0) :=
  two_prime_double_slice hp hq hζp hζq
    (Nat.Coprime.pow _ _ ((Nat.coprime_primes hp hq).mpr hpq))
    (AdjoinSimple.algebraMap_gen ℚ ζq)
    (minpoly_qadjoin_eq_cyclotomic hp hq hpq hζp hζq) hS hsum

/-- Satisfiability of the headline's hypothesis spine in a concrete field: the two
primitive roots exist in `ℂ` and the headline theorem fires (instantiated at the
empty vanishing sum) — no hypothesis hides an unsatisfiable assumption. -/
example : True := by
  classical
  have he4 : IsPrimitiveRoot (Complex.exp (2 * Real.pi * Complex.I / 4)) 4 := by
    have h := Complex.isPrimitiveRoot_exp 4 (by norm_num)
    norm_num at h
    exact h
  have he3 : IsPrimitiveRoot (Complex.exp (2 * Real.pi * Complex.I / 3)) 3 := by
    have h := Complex.isPrimitiveRoot_exp 3 (by norm_num)
    norm_num at h
    exact h
  have h4 : IsPrimitiveRoot (Complex.exp (2 * Real.pi * Complex.I / 4)) (2 ^ (1 + 1)) := by
    norm_num [he4]
  have h3 : IsPrimitiveRoot (Complex.exp (2 * Real.pi * Complex.I / 3)) (3 ^ (0 + 1)) := by
    norm_num [he3]
  have h := two_prime_deBruijn_double_slice Nat.prime_two Nat.prime_three (by norm_num)
    h4 h3 (S := (∅ : Finset ℂ)) (fun z hz => absurd hz (Finset.notMem_empty z)) (by simp)
  trivial

end TwoPrimeHeadline

/-! ## Non-vacuity: the fully unconditional `K = ℚ`, `N = 1` instance

With the second factor trivial, `hmin` is discharged by
`Polynomial.cyclotomic_eq_minpoly_rat`, and the machinery recovers the membership-level
prime-power slice structure (the heart of O66's `vanishing_sum_mu_p_closed`) with NO
named hypotheses — every hypothesis of the framework is simultaneously satisfiable. -/

section NonVacuity

variable [DecidableEq F] [CharZero F]

/-- **Unconditional instance** (`K = ℚ`, `N = 1`): in characteristic zero, a finite
subset of `μ_{p^(m+1)}` with vanishing sum has membership constant along `μ_p`-coset
directions of the exponent — derived entirely through the new `K`-coefficient
double-slice machinery. -/
theorem mu_p_membership_slices {p m : ℕ} (hp : p.Prime) {ζ : F}
    (hζ : IsPrimitiveRoot ζ (p ^ (m + 1)))
    {S : Finset F} (hS : ∀ z ∈ S, z ^ (p ^ (m + 1)) = 1)
    (hsum : ∑ z ∈ S, z = 0) :
    ∀ s < p ^ m, ∀ i < p, ∀ i' < p,
      (ζ ^ (i * p ^ m + s) ∈ S ↔ ζ ^ (i' * p ^ m + s) ∈ S) := by
  have h := qside_slices_over (K := ℚ) hp one_pos hζ IsPrimitiveRoot.one
    (Nat.coprime_one_right _) (map_one (algebraMap ℚ F))
    (Polynomial.cyclotomic_eq_minpoly_rat hζ (pow_pos hp.pos _)).symm
    (S := S) (fun z hz => by rw [mul_one]; exact hS z hz) hsum
  intro s hs i hi i' hi'
  have hg := h s hs i hi i' hi'
  simp only [gammaQ, Finset.sum_range_one, pow_zero, mul_one] at hg
  by_cases h1 : ζ ^ (i * p ^ m + s) ∈ S <;> by_cases h2 : ζ ^ (i' * p ^ m + s) ∈ S <;>
    simp [h1, h2] at hg ⊢

end NonVacuity

/-! ## The packet cover: de Bruijn's hard direction

From the unconditional double-slice, the structural dichotomy falls by case analysis:
**every element of a vanishing two-prime subset lies in a full `μ_p`-packet inside `S`
or a full `μ_q`-packet inside `S`.** If `x`'s `p`-fiber misses some point, the
difference row is constantly `1` along the `q`-direction — so `x`'s whole `q`-fiber is
present. This is the necessary half of de Bruijn's theorem (the O70-verified law adds
the disjoint-decomposition refinement: cover alone does not imply vanishing, since
overlapping packets break the sum — recorded honestly). -/

section PacketCover

variable [DecidableEq F] [CharZero F]

/-- **The two-prime packet cover** (de Bruijn's hard direction, unconditional): every
member of a vanishing subset of `μ_{p^(a+1)·q^(b+1)}` has its full `μ_p`-fiber in `S`
or its full `μ_q`-fiber in `S`. -/
theorem two_prime_packet_cover {p q a b : ℕ} (hp : p.Prime) (hq : q.Prime)
    (hpq : p ≠ q) {ζp ζq : F} (hζp : IsPrimitiveRoot ζp (p ^ (a + 1)))
    (hζq : IsPrimitiveRoot ζq (q ^ (b + 1)))
    {S : Finset F} (hS : ∀ z ∈ S, z ^ (p ^ (a + 1) * q ^ (b + 1)) = 1)
    (hsum : ∑ z ∈ S, z = 0) :
    ∀ s < p ^ a, ∀ i < p, ∀ t < q ^ b, ∀ j < q,
      ζp ^ (i * p ^ a + s) * ζq ^ (j * q ^ b + t) ∈ S →
      (∀ i'' < p, ζp ^ (i'' * p ^ a + s) * ζq ^ (j * q ^ b + t) ∈ S) ∨
      (∀ j'' < q, ζp ^ (i * p ^ a + s) * ζq ^ (j'' * q ^ b + t) ∈ S) := by
  intro s hs i hi t ht j hj hx
  by_cases hall : ∀ i'' < p, ζp ^ (i'' * p ^ a + s) * ζq ^ (j * q ^ b + t) ∈ S
  · exact Or.inl hall
  · right
    push Not at hall
    obtain ⟨i', hi', hx'⟩ := hall
    intro j'' hj''
    have hds := two_prime_deBruijn_double_slice hp hq hpq hζp hζq hS hsum
      s hs i hi i' hi' t ht j hj j'' hj''
    rw [if_pos hx, if_neg hx'] at hds
    by_cases h1 : ζp ^ (i * p ^ a + s) * ζq ^ (j'' * q ^ b + t) ∈ S
    · exact h1
    · exfalso
      rw [if_neg h1] at hds
      by_cases h2 : ζp ^ (i' * p ^ a + s) * ζq ^ (j'' * q ^ b + t) ∈ S
      · rw [if_pos h2] at hds
        norm_num at hds
      · rw [if_neg h2] at hds
        norm_num at hds

end PacketCover

end DeBruijnTwoPrime

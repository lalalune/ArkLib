/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import Mathlib.Algebra.BigOperators.Ring.Basic
import Mathlib.Algebra.MvPolynomial.Rename
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.Algebra.Polynomial.Taylor
import Mathlib.RingTheory.PowerSeries.Trunc

/-!
# Reusable mathlib-only lemmas extracted from proximity/proof-system issue files

Small, genuinely mathlib-only facts that are currently proved *inline* (or as `private`
duplicates) inside cone-importing ArkLib files. Lifting them here makes them reusable, upstreamable,
and verifiable against mathlib alone:

* `sum_range_choose_mul_sub_one_pow_eq_qpow` — the `q`-ary Hamming-ball full-space identity
  `∑_{i≤n} C(n,i)(q-1)^i = q^n` (inlined twice in `HammingBallVolumeBasics.lean`, issue #74);
* `MvPolynomial.rename_finCongr_heq` — `rename (finCongr h) p ≍ p` (a `private` lemma duplicated
  verbatim in `Sumcheck/.../SingleRound.lean`, `RingSwitching/SumcheckPhase.lean`, and
  `Binius/.../ProjectToNextSumEq.lean`, issues #33/#19/#29);
* `Polynomial.card_filter_eval_zero_le` — the `Fintype`-indexed Schwartz–Zippel root bound
  `#{x | p.eval x = 0} ≤ p.natDegree` (`RingSwitching/Prelude.lean`, issue #29);
* `PowerSeries.mk_eq_trunc_of_tail_zero` — a tail-vanishing series equals the coercion of its
  truncation (`BetaToCurveCoeffPolysOffcentre.lean`, issue #61);
* `Polynomial.natDegree_taylor_lt` — strict degree bound transports through a Taylor shift
  (`BetaToCurveCoeffPolysOffcentre.lean`, issue #61).
-/

open Polynomial

/-- **`q`-ary full-space identity.** `∑_{i≤n} C(n,i)(q-1)^i = q^n` for `1 ≤ q`. -/
theorem sum_range_choose_mul_sub_one_pow_eq_qpow (q n : ℕ) (hq : 1 ≤ q) :
    ∑ i ∈ Finset.range (n + 1), Nat.choose n i * (q - 1) ^ i = q ^ n := by
  have h := add_pow (q - 1) 1 n
  simp only [one_pow, mul_one, Nat.cast_id] at h
  rw [Nat.sub_add_cancel hq] at h
  rw [h]; exact Finset.sum_congr rfl (fun i _ => by ring)

namespace MvPolynomial

/-- Renaming along the canonical `finCongr` of a dimension equality is heterogeneously equal to the
original polynomial. -/
theorem rename_finCongr_heq {L : Type*} [CommSemiring L] {a b : ℕ} (h : a = b)
    (p : MvPolynomial (Fin a) L) : HEq (rename (finCongr h) p) p := by
  subst h
  rw [finCongr_refl, Equiv.coe_refl, rename_id_apply]

end MvPolynomial

namespace Polynomial

/-- **Root-set cardinality bound.** Over a finite integral domain `L`, a nonzero `p : L[X]` vanishes
at at most `p.natDegree` points. The `Fintype`-indexed Schwartz–Zippel core. -/
theorem card_filter_eval_zero_le {L : Type*} [CommRing L] [IsDomain L]
    [Fintype L] [DecidableEq L] (p : L[X]) (hp : p ≠ 0) :
    (Finset.univ.filter (fun x => p.eval x = 0)).card ≤ p.natDegree := by
  apply Polynomial.card_le_degree_of_subset_roots
  intro x hx
  simp only [Finset.mem_val, Finset.mem_filter, Finset.mem_univ, true_and] at hx
  rw [Polynomial.mem_roots hp, Polynomial.IsRoot.def]
  exact hx

/-- A strict degree bound transports through a Taylor shift. -/
theorem natDegree_taylor_lt {R : Type*} [CommRing R] (x₀ : R) (v : R[X]) {k : ℕ}
    (hv : v.natDegree < k + 1) : (taylor x₀ v).natDegree < k + 1 := by
  rwa [Polynomial.natDegree_taylor]

end Polynomial

namespace PowerSeries

/-- A power series whose coefficients vanish from index `k` on equals the coercion of its
`k`-truncation. -/
theorem mk_eq_trunc_of_tail_zero {K : Type*} [CommSemiring K] (f : ℕ → K) (k : ℕ)
    (h : ∀ t, k ≤ t → f t = 0) :
    PowerSeries.mk f = ((PowerSeries.trunc k (PowerSeries.mk f) : Polynomial K) : PowerSeries K) := by
  ext n
  rw [Polynomial.coeff_coe, PowerSeries.coeff_trunc, PowerSeries.coeff_mk]
  by_cases hn : n < k
  · simp [hn]
  · simp only [hn, if_false]
    exact h n (le_of_not_gt hn)

end PowerSeries

#print axioms sum_range_choose_mul_sub_one_pow_eq_qpow
#print axioms MvPolynomial.rename_finCongr_heq
#print axioms Polynomial.card_filter_eval_zero_le
#print axioms Polynomial.natDegree_taylor_lt
#print axioms PowerSeries.mk_eq_trunc_of_tail_zero

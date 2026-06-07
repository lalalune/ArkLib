/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.BCIKS20.P2Reindex

/-!
# BCIKS20 Appendix A.4 — the value-multiset ↔ (i₁, λ) bijection bricks (toward `RestrictedFaaDiBrunoMatch`)

This file builds the combinatorial bijection underlying `RestrictedFaaDiBrunoMatch` (P2Close.lean)
brick-by-brick, on top of the proven zero/positive-part reindex (`P2Reindex.lean`).

A value multiset `m` (a bag of `card m` orders, summing to its degree) splits canonically as
`replicate (zeroCount m) 0 + positivePart m`.  The zero entries contribute `b 0` factors (= `α₀`
powers in the assembled-series application), and the positive part is the genuine partition `λ`.
These bricks isolate the entropy-free combinatorial content; the algebraic `W`/`ξ`/`ζ` clearing and
the `B_coeff`/Y-Hasse matching are layered on later.
-/

namespace BCIKS20.HenselNumerator

open ArkLib.PowerSeriesComposition

/-- **Zero-entry product extraction.**  For any value multiset `m` and family `b : ℕ → M`, the
product `∏_{j∈m} b j` factors as `(b 0)^{(# zero entries)} · ∏_{j∈positivePart m} b j`.

In the assembled-series application (`b j = coeff j βHenselAssembled`), this peels the `α₀ = b 0`
contributions of the zero orders, leaving the genuine partition product over the positive part. -/
theorem prod_map_eq_zero_pow_mul_positivePart {M : Type*} [CommMonoid M]
    (m : Multiset ℕ) (b : ℕ → M) :
    (m.map b).prod = (b 0) ^ (zeroCount m) * ((positivePart m).map b).prod := by
  conv_lhs => rw [← replicate_zero_add_positivePart m]
  rw [Multiset.map_add, Multiset.prod_add, Multiset.map_replicate, Multiset.prod_replicate]

/-- **Per-term split.**  A single weighted value-multiset term `countPerms m • ∏ b` rewrites, via
the zero/positive split, into the binomial-placement factor times the positive-part partition term:

  `countPerms m • (∏_{j∈m} b j)
     = (C(z+|λ|, z) · countPerms λ) • ((b 0)^z · ∏_{j∈λ} b j)`,  with `λ = positivePart m`, `z = zeroCount m`.

Combines `countPerms_eq_choose_zeroCount_mul_positivePart` (scalar) with
`prod_map_eq_zero_pow_mul_positivePart` (product). -/
theorem countPerms_smul_prod_split {M : Type*} [CommSemiring M]
    (m : Multiset ℕ) (b : ℕ → M) :
    (m.countPerms) • ((m.map b).prod)
      = ((zeroCount m + (positivePart m).card).choose (zeroCount m) * (positivePart m).countPerms)
          • ((b 0) ^ (zeroCount m) * ((positivePart m).map b).prod) := by
  rw [countPerms_eq_choose_zeroCount_mul_positivePart m,
    prod_map_eq_zero_pow_mul_positivePart m b]

/-- The index-list `(List.range L.length).map (L.getD · 0) = L`. -/
private theorem list_range_map_getD (L : List ℕ) :
    (List.range L.length).map (fun j => L.getD j 0) = L := by
  apply List.ext_getElem
  · simp
  · intro k h1 h2
    rw [List.getElem_map, List.getElem_range, List.getD_eq_getElem L 0 (by simpa using h2)]

/-- **Value-multiset realizability.**  Every multiset `m` of cardinality `i` and sum `c` arises as
`valueMultiset (range i) l` for some weak composition `l ∈ finsuppAntidiag (range i) c` — i.e. it
lies in the index set of the restricted Faà-di-Bruno inner sum.  (Realize `m` by assigning its
element list to the indices `0..i-1`.)  This is the surjectivity needed for the reindex's inverse. -/
theorem mem_image_valueMultiset_of_card_sum {i c : ℕ} (m : Multiset ℕ)
    (hcard : m.card = i) (hsum : m.sum = c) :
    m ∈ (Finset.finsuppAntidiag (Finset.range i) c).image (valueMultiset (Finset.range i)) := by
  classical
  set L : List ℕ := m.toList with hL
  have hLlen : L.length = i := by rw [hL, Multiset.length_toList, hcard]
  have hsupp : ∀ j, (fun j => L.getD j 0) j ≠ 0 → j ∈ Finset.range i := by
    intro j hj
    rw [Finset.mem_range]
    by_contra hji
    exact hj (List.getD_eq_default L 0 (by omega))
  set l : ℕ →₀ ℕ := Finsupp.onFinset (Finset.range i) (fun j => L.getD j 0) hsupp with hl
  have hlapp : ∀ j ∈ Finset.range i, l j = L.getD j 0 := fun j _ => Finsupp.onFinset_apply
  -- The core fact: mapping the index list through `L.getD · 0` reconstructs `m`.
  have hmap : (Finset.range i).val.map (fun j => L.getD j 0) = m := by
    rw [Finset.range_val, ← hLlen, ← Multiset.coe_range, Multiset.map_coe, list_range_map_getD,
      hL, Multiset.coe_toList]
  refine Finset.mem_image.mpr ⟨l, ?_, ?_⟩
  · rw [Finset.mem_finsuppAntidiag]
    refine ⟨?_, Finsupp.support_onFinset_subset⟩
    rw [Finset.sum_congr rfl hlapp]
    show ((Finset.range i).val.map (fun j => L.getD j 0)).sum = c
    rw [hmap, hsum]
  · show (Finset.range i).val.map (fun j => l j) = m
    rw [Multiset.map_congr rfl (fun j hj => hlapp j (Finset.mem_val.mp hj)), hmap]

end BCIKS20.HenselNumerator

-- Axiom audit.
#print axioms BCIKS20.HenselNumerator.prod_map_eq_zero_pow_mul_positivePart
#print axioms BCIKS20.HenselNumerator.countPerms_smul_prod_split
#print axioms BCIKS20.HenselNumerator.mem_image_valueMultiset_of_card_sum

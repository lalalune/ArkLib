/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.LamLeungMultisetAntipodal
import Mathlib.Tactic

set_option linter.style.longLine false

/-!
# Energy relations among 2-power roots are antipodally balanced (#389) — the structural core of K1

The general-`r` structural heart of the negation-closed energy bound `E_r(μ_{2^m}, ℂ) ≤ (2r−1)!!·n^r`
("K1"). Every `r`-fold additive relation `∑ aᵢ = ∑ zᵢ` among `2^k`-th roots of unity is **antipodally
balanced**: the multiset `{a₁,…,a_r, −z₁,…,−z_r}` (which sums to `0`) has `count w = count (−w)` for
every `w`, by the multiset Lam–Leung theorem (`count_antipodal_of_sum_eq_zero`).

> `energy_relation_count_antipodal` :  `∑ᵢ aᵢ = ∑ᵢ zᵢ`  ⟹  the relation multiset is antipodal-balanced.

This is the analytic half of K1: it forces every contributor to `E_r(μ_{2^m})` into antipodal-pair
form. The remaining (combinatorial) half — counting the antipodally-balanced configurations as
`(2r−1)!!·n^r` (the `(2r−1)!!` perfect matchings × `n` per pair) — is the sub-Gaussian bound that, with
the moment ladder, gives the dyadic square-root-cancellation. (Char-0 statement; the `𝔽_q` transfer for
`q > (2r)^{φ(n)}` is the resultant lift `ManyTermResultantBound`.)

Axiom-clean (`propext`, `Classical.choice`, `Quot.sound`); no `sorry`.
-/

open Finset

namespace ArkLib.ProximityGap.EnergyRelationAntipodal

variable {L : Type*} [Field L] [CharZero L] [DecidableEq L]

/-- **The structural core of K1.** For `2^k`-th roots `a, z : Fin r → L` (`k ≥ 1`) with equal sums
`∑ᵢ aᵢ = ∑ᵢ zᵢ`, the relation multiset `M = {a₁,…,a_r} + {−z₁,…,−z_r}` is antipodally balanced:
`M.count w = M.count (−w)` for every `w`. (Multiset Lam–Leung applied to the vanishing sum
`∑aᵢ − ∑zᵢ = 0`.) -/
theorem energy_relation_count_antipodal {k r : ℕ} (hk : 1 ≤ k)
    (a z : Fin r → L) (ha : ∀ i, (a i) ^ (2 ^ k) = 1) (hz : ∀ i, (z i) ^ (2 ^ k) = 1)
    (hsum : ∑ i, a i = ∑ i, z i) :
    ∀ w : L, (Finset.univ.val.map a + Finset.univ.val.map (fun i => - z i)).count w
           = (Finset.univ.val.map a + Finset.univ.val.map (fun i => - z i)).count (-w) := by
  set M : Multiset L := Finset.univ.val.map a + Finset.univ.val.map (fun i => - z i) with hM
  -- 2^k is even (k ≥ 1), so negation preserves being a 2^k-th root
  have heven : Even (2 ^ k) := by
    obtain ⟨k', rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by omega⟩
    exact ⟨2 ^ k', by rw [pow_succ]; ring⟩
  refine LamLeungMultisetAntipodal.count_antipodal_of_sum_eq_zero (k := k) ?_ ?_
  · -- every element of M is a 2^k-th root
    intro w hw
    rw [hM, Multiset.mem_add] at hw
    rcases hw with hw | hw
    · obtain ⟨i, _, rfl⟩ := Multiset.mem_map.mp hw
      exact ha i
    · obtain ⟨i, _, rfl⟩ := Multiset.mem_map.mp hw
      rw [neg_pow, heven.neg_one_pow, one_mul]
      exact hz i
  · -- M.sum = ∑ aᵢ − ∑ zᵢ = 0
    rw [hM, Multiset.sum_add]
    have h1 : (Finset.univ.val.map a).sum = ∑ i, a i := rfl
    have h2 : (Finset.univ.val.map (fun i => - z i)).sum = ∑ i, - z i := rfl
    rw [h1, h2, Finset.sum_neg_distrib, hsum, sub_self_of_eq rfl]

end ArkLib.ProximityGap.EnergyRelationAntipodal

/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.Mu6ConditionalPin

/-!
# Fixed-r collision-resultant bound for KKH26

`KKH26SumsOfRootsOfUnity.lean` proves the archimedean resultant bound
`|Res(R, Phi_{2^m})| <= ||R||_1^(2^(m-1))`.  Its current collision-resultant
consumer then coarsens `||R||_1 <= 2r` to `2r <= 2^m`, giving the uniform
threshold `(2^m)^(2^(m-1))`.

For small literal rungs, keep the fixed-r term instead.  In the landed
`mu = 6`, `r = 5` conditional pin this gives `(2r)^(2^(m-1)) = 10^32`,
which is far below the certified prime
`P = 1526377 * 2^128 + 1`.
-/

open Finset

set_option maxRecDepth 1000000

namespace ArkLib.ProximityGap.KKH26

/-- Fixed-r form of `natAbs_collisionResultant_le`: do not coarsen `2r` to `2^m`. -/
theorem natAbs_collisionResultant_le_two_mul_r_pow {m r : ℕ} (hm : 1 ≤ m)
    {d₁ d₂ : (_ : Finset ℕ) × Finset ℕ}
    (hd₁ : d₁ ∈ sigData (2 ^ (m - 1)) r)
    (hd₂ : d₂ ∈ sigData (2 ^ (m - 1)) r) :
    (collisionResultant m d₁ d₂).natAbs ≤ (2 * r) ^ 2 ^ (m - 1) := by
  obtain ⟨U₁, T₁⟩ := d₁
  obtain ⟨U₂, T₂⟩ := d₂
  obtain ⟨⟨hU₁, hc₁⟩, hT₁⟩ := mem_sigData.mp hd₁
  obtain ⟨⟨hU₂, hc₂⟩, hT₂⟩ := mem_sigData.mp hd₂
  have hhalf : 0 < 2 ^ (m - 1) := by positivity
  have hdegR : (sumPoly U₁ T₁ - sumPoly U₂ T₂).natDegree < 2 ^ (m - 1) :=
    lt_of_le_of_lt (Polynomial.natDegree_sub_le _ _)
      (max_lt (sumPoly_natDegree_lt hhalf hU₁ hT₁)
        (sumPoly_natDegree_lt hhalf hU₂ hT₂))
  have hl1 : l1On (2 ^ (m - 1)) (sumPoly U₁ T₁ - sumPoly U₂ T₂) ≤ 2 * r := by
    have h := l1On_sub_le (2 ^ (m - 1)) (sumPoly U₁ T₁) (sumPoly U₂ T₂)
    rw [l1On_sumPoly hU₁ hT₁, l1On_sumPoly hU₂ hT₂, hc₁, hc₂] at h
    omega
  have hub :=
    natAbs_resultant_cyclotomic_le hm (sumPoly U₁ T₁ - sumPoly U₂ T₂) hdegR
  exact le_trans hub (Nat.pow_le_pow_left hl1 _)

/-- Fixed-r size implies the collision resultant is not divisible by `p`. -/
theorem not_dvd_collisionResultant_of_two_mul_r_pow_lt {p : ℕ} [Fact p.Prime] {m r : ℕ}
    (hm : 1 ≤ m) (hp : (2 * r) ^ 2 ^ (m - 1) < p)
    {d₁ d₂ : (_ : Finset ℕ) × Finset ℕ}
    (hd₁ : d₁ ∈ sigData (2 ^ (m - 1)) r)
    (hd₂ : d₂ ∈ sigData (2 ^ (m - 1)) r)
    (hne : d₁ ≠ d₂) : ¬ (p : ℤ) ∣ collisionResultant m d₁ d₂ := by
  intro hdvd
  have h1 : p ≤ (collisionResultant m d₁ d₂).natAbs :=
    Nat.le_of_dvd (Int.natAbs_pos.mpr (collisionResultant_ne_zero hm hd₁ hd₂ hne))
      (by simpa using Int.natAbs_dvd_natAbs.mpr hdvd)
  have h2 := natAbs_collisionResultant_le_two_mul_r_pow hm hd₁ hd₂
  omega

end ArkLib.ProximityGap.KKH26

namespace ArkLib.ProximityGap.Mu6FixedRResultantBound

open ArkLib.ProximityGap.KKH26
open ArkLib.ProximityGap.Mu6ConditionalPin

/-- The fixed-r threshold for the landed `mu = 6`, `r = 5` conditional pin
is below the certified prime. -/
theorem ten_pow_32_lt_P : (2 * 5 : ℕ) ^ 2 ^ (6 - 1) < P := by
  norm_num [P]

end ArkLib.ProximityGap.Mu6FixedRResultantBound

-- Axiom audit (expected: propext, Classical.choice, Quot.sound only)
#print axioms ArkLib.ProximityGap.KKH26.natAbs_collisionResultant_le_two_mul_r_pow
#print axioms ArkLib.ProximityGap.KKH26.not_dvd_collisionResultant_of_two_mul_r_pow_lt
#print axioms ArkLib.ProximityGap.Mu6FixedRResultantBound.ten_pow_32_lt_P

import ArkLib.Data.CodingTheory.ProximityGap.GrandChallenge141PrizeMath
import ArkLib.Data.CodingTheory.ProximityGap.HasseSchmidt

open Classical
open scoped BigOperators

/-!
# Candidate 10 (REJECTED): Hasse–Schmidt "valuation disparity" extrapolation

**Honesty note.** A previous revision parked the prize bound itself — `epsMCA C δ ≤ 2⁻¹²⁸` — as a
bare `sorry` (`mca_bound_of_extrapolation`). Asserting the target as an unproven lemma is the
fake-completion pattern banned by #169/#171/#232, so it is removed.

The idea was to use the non-Archimedean `extrapolationNorm` (least Hasse–Schmidt depth detecting an
element) to bound the list size: if the true signal `P` and the adversarial noise always had
*distinct* extrapolation norms, the strong-triangle law (`extrapolationNorm_add_of_disparity`) would
pin `extrapolationNorm (P + noise)` and cap the list.

**Why it is rejected.** The disjointness hypothesis `extrapolationNorm hs P ≠ extrapolationNorm hs noise`
is exactly the assumed `ValuationDisparity` field, and it is *false against an adaptive adversary*: the
decoder receives `r = P + noise` where the adversary chooses `noise` freely, and can pick `noise` whose
Hasse–Schmidt valuation matches `P`'s, causing catastrophic cancellation in characteristic 2. So the
hypothesis powering the bound is precisely the thing the adversary breaks; the approach assumes its
conclusion. This file records the dead-end honestly and proves only the one unconditional fact about
`extrapolationNorm` that genuinely holds.
-/

namespace ArkLib.CodingTheory.Research

open ArkLib.CodingTheory.HasseSchmidtDerivation

variable {F : Type} [Field F] [Fintype F]

/-- The single unconditional fact: `extrapolationNorm hs 0 = 0`, since `D k 0 = 0` for all `k`, so the
defining set `{k | D k 0 ≠ 0}` is empty and `sInf ∅ = 0`. (Everything *else* the candidate wanted —
an actual list-size bound — depends on the false `ValuationDisparity` assumption above and is not
provable here.) -/
lemma extrapolationNorm_zero (hs : ArkLib.CodingTheory.HasseSchmidtDerivation F) :
    extrapolationNorm hs (0 : F) = 0 := by
  unfold extrapolationNorm
  have hset : {k : ℕ | hs.D k 0 ≠ 0} = (∅ : Set ℕ) := by
    ext k
    simp [map_zero]
  rw [hset]
  exact Nat.sInf_empty

end ArkLib.CodingTheory.Research

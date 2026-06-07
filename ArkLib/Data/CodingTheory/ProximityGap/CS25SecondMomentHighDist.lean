/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.CS25SecondMomentLinear
import ArkLib.Data.CodingTheory.ProximityGap.CS25BallInterVanish

/-!
# CS25 second moment for high-distance linear codes (#82)

For a **linear** code `𝒞` (closed under `±`, containing `0`) whose minimum distance exceeds `2r`
(every nonzero codeword has weight `> 2r`), the second moment collapses **exactly**:

  `∑_w (closeCount 𝒞 r w)² = |𝒞| · |B(0,r)|`.

Indeed each far codeword's two-ball intersection vanishes (`ballInterCount_eq_zero_of_lt`), so the
weight-enumerator sum `∑_{v∈𝒞} ballInterCount r v` keeps only the `v = 0` term `|B(0,r)|`; combined
with the linear reduction (`sum_closeCount_sq_eq_card_mul`).  Since `E[N] = |𝒞|·|B(0,r)| / qⁿ` and
`E[N²] = |𝒞|·|B(0,r)|`, the Paley-Zygmund covered fraction is `≥ E[N]²/E[N²] = |𝒞|·|B(0,r)|/qⁿ` —
the exact first-moment fraction, i.e. no variance loss in the high-distance regime.
-/

namespace ArkLib.CS25

open scoped BigOperators

variable {ι : Type*} [Fintype ι] [DecidableEq ι]
variable {F : Type*} [Fintype F] [DecidableEq F] [AddCommGroup F]

/-- **Weight-enumerator sum collapse (high distance).**  If `0 ∈ 𝒞` and every nonzero codeword is
`> 2r` from the origin, then `∑_{v∈𝒞} ballInterCount r v = ballInterCount r 0` (only `v = 0`
survives, by `ballInterCount_eq_zero_of_lt`). -/
theorem sum_ballInterCount_eq_of_minDist (𝒞 : Finset (ι → F)) (r : ℕ)
    (h0 : (0 : ι → F) ∈ 𝒞)
    (hd : ∀ v ∈ 𝒞, v ≠ 0 → 2 * r < hammingDist (0 : ι → F) v) :
    ∑ v ∈ 𝒞, ballInterCount r v = ballInterCount r (0 : ι → F) := by
  refine Finset.sum_eq_single (0 : ι → F) (fun v hv hv0 => ?_) (fun h => absurd h0 h)
  exact ballInterCount_eq_zero_of_lt r v (hd v hv hv0)

/-- **Exact second moment, high-distance linear code.**  For a linear code `𝒞` with minimum
distance `> 2r`, `∑_w (closeCount 𝒞 r w)² = |𝒞| · |B(0,r)|` — the variance-free second moment that
makes the CS25 Paley-Zygmund covered fraction equal the first-moment fraction. -/
theorem sum_closeCount_sq_high_dist (𝒞 : Finset (ι → F)) (r : ℕ)
    (hsub : ∀ a ∈ 𝒞, ∀ b ∈ 𝒞, a - b ∈ 𝒞)
    (hadd : ∀ a ∈ 𝒞, ∀ b ∈ 𝒞, a + b ∈ 𝒞)
    (h0 : (0 : ι → F) ∈ 𝒞)
    (hd : ∀ v ∈ 𝒞, v ≠ 0 → 2 * r < hammingDist (0 : ι → F) v) :
    (∑ w : ι → F, (closeCount 𝒞 r w) ^ 2)
      = 𝒞.card * ballInterCount r (0 : ι → F) := by
  rw [sum_closeCount_sq_eq_card_mul 𝒞 r hsub hadd, sum_ballInterCount_eq_of_minDist 𝒞 r h0 hd]

end ArkLib.CS25

-- Axiom audit.
#print axioms ArkLib.CS25.sum_ballInterCount_eq_of_minDist
#print axioms ArkLib.CS25.sum_closeCount_sq_high_dist

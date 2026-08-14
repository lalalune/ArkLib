/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.SidonSubgroupClosed

/-!
# Brick `energy-equality-sidon-mod-neg` (#389) — the exact additive energy `E(μ_n) = 3n² − 3n`

For the 2-power NTT subgroup `G = μ_n ⊂ F_p` (`n = 2^m`, `m ≥ 1`) with `p > 2^n`, this file pins:

* `mu_n_isSidonModNeg` — `G = nthRootsFinset n 1` is **Sidon-modulo-negation**: its only additive
  coincidences are the forced (trivial / zero-sum) ones.  This is the contrapositive of the
  cyclotomic resultant bound `prime_le_of_parallelogram` (`|Res(Φ_n, ·)| ≤ 4^{φ(n)} = 2^n < p`
  forbids any nontrivial nonzero-sum parallelogram), discharged in `sidonModNeg_mu_n`.

* `mu_n_card_eq` — `|μ_n| = n` (a primitive `n`-th root makes the `n`-th-roots Finset full).

* `mu_n_additiveEnergy_eq` — feeding `SidonModNeg` into the landed energy-from-Sidon reduction
  `additiveEnergy_eq_of_sidonModNeg`, the additive energy is **exactly `3n² − 3n`**, the char-0
  minimal value — sharpening the Garcia–Voloch `≤ 3|G|²` bound to an equality, off by exactly
  `3|G|`.  Verified numerically at `n = 8, 16, 32, 64` against real primes `p > 2^n`; now proven
  for *all* `p > 2^n` over `F_p`, unconditionally (no Weil, no Stepanov, no open conjecture).

The whole chain is purely the cyclotomic-resultant lifting; the deployed prize regime
`n ≫ log₂ p` remains the separate specific-prime cyclotomic coincidence (genuinely open).

## References
- [ABF26] Arnon, Boneh, Fenzi. *Open Problems in List Decoding and Correlated Agreement*. 2026.
-/

open Polynomial Finset
open ArkLib.ProximityGap.AdditiveEnergyRepBound
open ArkLib.ProximityGap.AdditiveEnergySidonModNeg

namespace ArkLib.ProximityGap.EnergyEqualitySidonModNeg

variable {p : ℕ} [Fact p.Prime] {n m : ℕ}

/-- The 2-power NTT subgroup `μ_n = {z ∈ F_p : z^n = 1}`, as the `n`-th-roots Finset of `1`. -/
noncomputable abbrev muN (p n : ℕ) [Fact p.Prime] : Finset (ZMod p) :=
  Polynomial.nthRootsFinset n (1 : ZMod p)

/-- Membership in `μ_n`: `z ∈ μ_n ↔ z^n = 1` (`n ≥ 1`). -/
theorem mem_muN (hn : 0 < n) (z : ZMod p) : z ∈ muN p n ↔ z ^ n = 1 := by
  simpa using Polynomial.mem_nthRootsFinset hn (1 : ZMod p)

/-- **`|μ_n| = n`.**  A primitive `n`-th root `ω ∈ ZMod p` makes the `n`-th-roots Finset full. -/
theorem mu_n_card_eq {ω : ZMod p} (hω : IsPrimitiveRoot ω n) : (muN p n).card = n :=
  hω.card_nthRootsFinset

/-- **`μ_n` is Sidon-modulo-negation for `p > 2^n`.**  Contrapositive of the cyclotomic resultant
bound: a nontrivial nonzero-sum parallelogram would force `p ≤ 2^n`.  Unconditional. -/
theorem mu_n_isSidonModNeg (hn2 : n = 2 ^ m) (hm : 1 ≤ m) (hp : 2 ^ n < p)
    {ω : ZMod p} (hω : IsPrimitiveRoot ω n) :
    SidonModNeg (muN p n) := by
  have hnpos : 0 < n := by rw [hn2]; positivity
  exact sidonModNeg_mu_n hn2 hm hp hω (fun z => mem_muN hnpos z)

/-- **THE BRICK — `E(μ_n) = 3n² − 3n` exactly.**  For `n = 2^m` (`m ≥ 1`) and a prime `p > 2^n`
with a primitive `n`-th root `ω ∈ ZMod p`, the additive energy of the 2-power NTT subgroup
`μ_n ⊂ F_p` is exactly `3n² − 3n = 3n(n−1)` — the char-0 minimal value, attained over `F_p` for
every `p > 2^n`.  Unconditional (cyclotomic resultant only). -/
theorem mu_n_additiveEnergy_eq (hn2 : n = 2 ^ m) (hm : 1 ≤ m) (hp : 2 ^ n < p)
    {ω : ZMod p} (hω : IsPrimitiveRoot ω n) :
    additiveEnergy (muN p n) = 3 * n ^ 2 - 3 * n := by
  have hnpos : 0 < n := by rw [hn2]; positivity
  have hcard : (muN p n).card = n := mu_n_card_eq hω
  have hE := additiveEnergy_mu_n hn2 hm hp hω (fun z => mem_muN hnpos z)
  rw [hE, hcard]

/-- **Combined statement of the brick** as a single conjunction:
`μ_n` is `SidonModNeg`, has `n` elements, and additive energy exactly `3n² − 3n`. -/
theorem brick_energy_equality_sidon_mod_neg (hn2 : n = 2 ^ m) (hm : 1 ≤ m) (hp : 2 ^ n < p)
    {ω : ZMod p} (hω : IsPrimitiveRoot ω n) :
    SidonModNeg (muN p n) ∧
      (muN p n).card = n ∧
      additiveEnergy (muN p n) = 3 * n ^ 2 - 3 * n :=
  ⟨mu_n_isSidonModNeg hn2 hm hp hω, mu_n_card_eq hω, mu_n_additiveEnergy_eq hn2 hm hp hω⟩

end ArkLib.ProximityGap.EnergyEqualitySidonModNeg

/-! ## Axiom audit -/
#print axioms ArkLib.ProximityGap.EnergyEqualitySidonModNeg.mu_n_isSidonModNeg
#print axioms ArkLib.ProximityGap.EnergyEqualitySidonModNeg.mu_n_card_eq
#print axioms ArkLib.ProximityGap.EnergyEqualitySidonModNeg.mu_n_additiveEnergy_eq
#print axioms ArkLib.ProximityGap.EnergyEqualitySidonModNeg.brick_energy_equality_sidon_mod_neg
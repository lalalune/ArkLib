/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/

import ArkLib.Data.CodingTheory.ProximityGap.GrandChallengeLDThresholdElias
import ArkLib.Data.CodingTheory.ProximityGap.GrandChallengesLattice

/-!
# Four-rate Johnson/Elias bracket certificates for the faithful list-decoding threshold

`GrandChallengesLattice.lean` already provides the **exact** four-rate resolver
`listPrizeLatticeResolved_of_johnson_sq_and_elias_next`, which pins each per-rate faithful
list-decoding lattice threshold to a single index *when* the squared-Johnson certificate and
the Elias-volume certificate land on **adjacent** lattice indices `τ` and `τ + 1`.

At the actual ABF26 prize parameters the Johnson floor (`≈ 1 − √ρ`) and the
Elias/capacity ceiling (`≈ 1 − H_q(ρ) < 1 − ρ`) are separated by a constant fraction of
`n`, so the certified indices are *not* adjacent and the exact resolver does not apply.  The
honest, generally-applicable deliverable — requested as the fallback in issue #56 — is the
**bracket** form: from a squared-Johnson lower certificate at `τ_lo r` and an Elias-volume
upper certificate at `τ_hi r` (no adjacency required), conclude per rate

  `τ_lo r ≤ listLatticeThreshold (RS rate r) m ε* < τ_hi r`.

This file adds that LD-side bracket assembler, the exact list-decoding mirror of the
MCA-side `mcaPrizeLattice_bracketed_ofJohnsonBCHKS25_and_RSBreakdownCS25`.  The remaining
content is exactly the per-rate numeric Johnson/Elias inequalities, isolated as hypotheses
indexed by the prize rate `r : Fin 4`.

## Main results

* `listPrizeLattice_bracketed_of_johnson_sq_and_elias` — the four-rate faithful list-decoding
  lattice bracket from a squared-Johnson lower certificate ⊕ an Elias-volume upper
  certificate, with the numeric inequalities isolated per rate.
* `listLatticeThreshold_bracketed_of_johnson_sq_and_elias` — the single-code bracket it is
  built from (Johnson lower ⊕ Elias upper on one Reed–Solomon code), useful on its own.

The nonemptiness hypotheses are dischargeable uniformly by
`listLatticeSet_nonempty_rs` (radius `0` always qualifies once `1 ≤ ε*·|F|`).
-/

namespace ProximityGap

open scoped NNReal
open ListDecodable GrandChallenges

variable {F ι : Type} [Field F] [Fintype F] [DecidableEq F]
  [Fintype ι] [Nonempty ι] [DecidableEq ι]

/-- **Single-code Johnson/Elias bracket on the faithful list threshold.**
A squared-Johnson lower certificate at index `j_lo` and an Elias-volume upper certificate at
index `j_hi` bracket the genuine lattice threshold: `j_lo ≤ threshold < j_hi`.  No adjacency
is required, so this applies in the general (Johnson floor ≪ Elias ceiling) regime. -/
theorem listLatticeThreshold_bracketed_of_johnson_sq_and_elias
    (C : Submodule F (ι → F)) {m j_lo j_hi ℓ : ℕ}
    (hm : m ≠ 0)
    (hlo_le : j_lo ≤ Fintype.card ι)
    (hhi_pos : 0 < j_hi) (hhi_lt : j_hi < Fintype.card ι)
    (hq1 : 1 < Fintype.card F)
    (hP : (Fintype.card ι : ℝ) / (Fintype.card F : ℝ) ≤
      ((Fintype.card ι - j_lo : ℕ) : ℝ))
    (hsq : ((ℓ : ℝ) + 1)
        * ((((Fintype.card ι - j_lo : ℕ) : ℝ)) -
            (Fintype.card ι : ℝ) / (Fintype.card F : ℝ)) ^ 2
      > ((Fintype.card ι : ℝ) * (1 - 1 / (Fintype.card F : ℝ)))
        * ((Fintype.card ι : ℝ) * (1 - 1 / (Fintype.card F : ℝ))
            + (ℓ : ℝ) * (((Fintype.card ι - Code.minDist (C : Set (ι → F)) : ℕ) : ℝ) -
                (Fintype.card ι : ℝ) / (Fintype.card F : ℝ))))
    {ε_star : ℝ≥0}
    (hpow : ((ℓ : ENNReal)) ^ m ≤ (ε_star : ENNReal) * (Fintype.card F : ENNReal))
    (hvol : (ε_star : ENNReal) * (Fintype.card F : ENNReal) <
      ENNReal.ofReal
        ((CodingTheory.hammingBallVolume (Fintype.card F)
            (((j_hi : ℝ≥0) / (Fintype.card ι : ℝ≥0) : ℝ≥0) : ℝ) (Fintype.card ι) : ℝ)
          / (Fintype.card F : ℝ) ^
              ((Fintype.card ι : ℝ) - Module.finrank F C)))
    (hne : (GrandChallenges.listLatticeSet (C : Set (ι → F)) m ε_star).Nonempty) :
    j_lo ≤ GrandChallenges.listLatticeThreshold (C : Set (ι → F)) m ε_star hne ∧
      GrandChallenges.listLatticeThreshold (C : Set (ι → F)) m ε_star hne < j_hi :=
  ⟨le_listLatticeThreshold_of_johnson_sq (C := (C : Set (ι → F))) (m := m)
      (j := j_lo) (ℓ := ℓ) hlo_le hq1 hP hsq hpow hne,
   listLatticeThreshold_lt_of_elias_volume (C := C) (m := m) (j := j_hi)
      hm hhi_pos hhi_lt hvol hne⟩

/-- **Four-rate faithful list-decoding lattice bracket from squared-Johnson ⊕ Elias-volume.**
For every ABF26 prize rate `r : Fin 4` (degree `k_r := ⌊prizeRates r · n⌋`), a squared-Johnson
lower certificate at lattice index `τ_lo r` and an Elias-volume upper certificate at index
`τ_hi r` bracket the faithful list-decoding lattice threshold of the rate-`r` Reed–Solomon code
between `τ_lo r` and `τ_hi r`.

This is the list-decoding mirror of `mcaPrizeLattice_bracketed_ofJohnsonBCHKS25_and_RSBreakdownCS25`
and the non-adjacent generalisation of `listPrizeLatticeResolved_of_johnson_sq_and_elias_next`:
the remaining content is exactly the per-rate numeric Johnson/Elias inequalities, and no
adjacency between `τ_lo` and `τ_hi` is assumed (so it applies in the genuine prize regime where
the Johnson floor and the Elias ceiling are a constant fraction of `n` apart). -/
theorem listPrizeLattice_bracketed_of_johnson_sq_and_elias
    (domain : ι ↪ F) (m : ℕ)
    (τ_lo τ_hi : Fin 4 → ℕ)
    (ℓ : Fin 4 → ℕ)
    (hm : m ≠ 0)
    (hlo_le : ∀ r : Fin 4, τ_lo r ≤ Fintype.card ι)
    (hhi_pos : ∀ r : Fin 4, 0 < τ_hi r)
    (hhi_lt : ∀ r : Fin 4, τ_hi r < Fintype.card ι)
    (hq1 : 1 < Fintype.card F)
    (hP : ∀ r : Fin 4,
      (Fintype.card ι : ℝ) / (Fintype.card F : ℝ) ≤
        ((Fintype.card ι - τ_lo r : ℕ) : ℝ))
    (hsq : ∀ r : Fin 4,
      ((ℓ r : ℝ) + 1)
          * ((((Fintype.card ι - τ_lo r : ℕ) : ℝ)) -
              (Fintype.card ι : ℝ) / (Fintype.card F : ℝ)) ^ 2
        > ((Fintype.card ι : ℝ) * (1 - 1 / (Fintype.card F : ℝ)))
          * ((Fintype.card ι : ℝ) * (1 - 1 / (Fintype.card F : ℝ))
              + (ℓ r : ℝ)
                * (((Fintype.card ι -
                    Code.minDist
                      (ReedSolomon.code domain
                        ⌊prizeRates r * (Fintype.card ι : ℝ≥0)⌋₊ :
                          Set (ι → F)) : ℕ) : ℝ) -
                    (Fintype.card ι : ℝ) / (Fintype.card F : ℝ))))
    (hpow : ∀ r : Fin 4,
      ((ℓ r : ENNReal)) ^ m ≤ (epsStar : ENNReal) * (Fintype.card F : ENNReal))
    (hvol : ∀ r : Fin 4,
      (epsStar : ENNReal) * (Fintype.card F : ENNReal) <
        ENNReal.ofReal
          ((CodingTheory.hammingBallVolume (Fintype.card F)
              (((τ_hi r : ℝ≥0) / (Fintype.card ι : ℝ≥0) : ℝ≥0) : ℝ)
              (Fintype.card ι) : ℝ)
            / (Fintype.card F : ℝ) ^
                ((Fintype.card ι : ℝ) -
                  Module.finrank F
                    (ReedSolomon.code domain
                      ⌊prizeRates r * (Fintype.card ι : ℝ≥0)⌋₊))))
    (hne : ∀ r : Fin 4,
      (GrandChallenges.listLatticeSet
        (ReedSolomon.code domain
          ⌊prizeRates r * (Fintype.card ι : ℝ≥0)⌋₊ : Set (ι → F))
        m epsStar).Nonempty) :
    ∀ r : Fin 4,
      τ_lo r ≤ GrandChallenges.listLatticeThreshold
          (ReedSolomon.code domain
            ⌊prizeRates r * (Fintype.card ι : ℝ≥0)⌋₊ : Set (ι → F))
          m epsStar (hne r) ∧
        GrandChallenges.listLatticeThreshold
          (ReedSolomon.code domain
            ⌊prizeRates r * (Fintype.card ι : ℝ≥0)⌋₊ : Set (ι → F))
          m epsStar (hne r) < τ_hi r := fun r =>
  listLatticeThreshold_bracketed_of_johnson_sq_and_elias
    (C := ReedSolomon.code domain ⌊prizeRates r * (Fintype.card ι : ℝ≥0)⌋₊)
    (m := m) (j_lo := τ_lo r) (j_hi := τ_hi r) (ℓ := ℓ r)
    hm (hlo_le r) (hhi_pos r) (hhi_lt r) hq1 (hP r) (hsq r) (hpow r) (hvol r) (hne r)

/-! ## Non-vacuity: the certificate inequalities are concretely dischargeable

The per-rate hypotheses above are not vacuous: for a `[4, 2, 3]` code over `𝔽₃`
(`n = 4`, `q = 3`, `minDist = 3`, hence `n − minDist = k − 1 = 1`, `finrank = 2`), the
squared-Johnson inequality holds at lattice index `1` and the Elias-volume inequality holds
at index `2` (with `ℓ = 2`, `m = 1`, budget `ε* = 2/3`, so `ε*·q = 2 = ℓ^m`).  These are
*adjacent*, so on this instance the exact resolver `listLatticeThreshold_eq_of_johnson_sq_and_elias_next`
would pin the threshold to `1`.  The two witnesses below discharge the numeric cores by
`norm_num` — including evaluating the genuine `hammingBallVolume` definition — confirming the
machinery fires.

At the *prize* rates `ρ ∈ {1/2, 1/4, 1/8, 1/16}` with `ε* = 2^{-128}` the Johnson floor
(`≈ 1 − √ρ`) and the Elias ceiling (`≈ 1 − H_q(ρ) < 1 − ρ`) are a constant fraction of `n`
apart, so the certified indices are *not* adjacent — there the bracket above is the
applicable form, and it is non-empty because `1 − √ρ < 1 − ρ` strictly for `ρ ∈ (0,1)`. -/

/-- **Squared-Johnson core is dischargeable.**  The optimal-β Johnson inequality at lattice
index `1` for a `[4,2,3]₃` code (`n=4`, `q=3`, `n−minDist = 1`, `ℓ=2`) holds — `25/3 > 16/3`. -/
theorem demo_johnson_sq_n4_q3 :
    ((2 : ℝ) + 1)
        * ((((4 - 1 : ℕ) : ℝ)) - (4 : ℝ) / 3) ^ 2
      > ((4 : ℝ) * (1 - 1 / 3))
        * ((4 : ℝ) * (1 - 1 / 3) + (2 : ℝ) * (((4 - 3 : ℕ) : ℝ) - (4 : ℝ) / 3)) := by
  norm_num

/-- **Elias-volume core is dischargeable**, evaluating the genuine `hammingBallVolume`
definition: at index `2` the Elias volume `Vol₃(2/4, 4) = 33` over `q^{n−k} = 3² = 9` gives
`11/3`, strictly above the budget `ε*·q = 2`. -/
theorem demo_elias_volume_n4_q3 :
    (2 : ℝ) <
      (CodingTheory.hammingBallVolume 3 ((2 : ℝ) / 4) 4 : ℝ) / (3 : ℝ) ^ (2 : ℕ) := by
  have hfloor : ⌊((2 : ℝ) / 4) * (4 : ℕ)⌋₊ = 2 := by
    norm_num
  rw [CodingTheory.hammingBallVolume, hfloor]
  norm_num [Finset.sum_range_succ, Nat.choose]

end ProximityGap

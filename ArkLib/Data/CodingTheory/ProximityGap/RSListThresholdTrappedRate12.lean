/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.RSListThresholdStrictRate12

/-!
# Definitive capstone: `δ*` trapped in the gap, capacity strictly unattained (rate `1/2`, #232)

The single canonical statement of everything proven about the genuine list-decoding threshold `δ*`
for the headline prize rate `ρ = 1/2`, combining both sides of the squeeze:

  `rs_ld_threshold_trapped_rate12` — for `RS[F, α, 128]` on a size-`256` domain, `m = 1`,
  `ε* = 2^{-128}`, over any field with `263·2^128 ≤ |F| ≤ 2^256`:

  1. **(two-sided trap)** `75 ≤ listLatticeThreshold ≤ 127` — i.e. `δ* ∈ [0.293, 0.5)`,
     the Johnson radius `1 − √ρ ≈ 0.293` lower-bounds it
     (`rs_ld_threshold_johnson_pin_general`) and the capacity radius `1 − ρ = 0.5` is
     strictly unattained;
  2. **(capacity strictly unattained)** `Λ(RS[128], 1/2) > ε*·|F|` — at the capacity
     radius the list blows past the budget (`rs_uptoCapacity_false_rate12_n256`), so `δ*`
     does **not** reach capacity.

Together: `δ*` is trapped in the half-open Johnson→capacity gap `[1 − √ρ, 1 − ρ)`, with
the upper endpoint provably excluded. Pinning the exact value *inside* this gap is the
open $1M problem; this theorem records the complete proven envelope and fabricates nothing.

Axiom-clean (`[propext, Classical.choice, Quot.sound]`).

## References
- [ABF26] Arnon, Boneh, Fenzi. *Open Problems in List Decoding and Correlated Agreement*. 2026.
  #232.
-/

namespace ProximityGap

open scoped NNReal ENNReal
open ListDecodable

/-- **Definitive rate-`1/2` envelope for the genuine list-decoding threshold.** For
`RS[F, α, 128]` on a size-`256` domain, `m = 1`, `ε* = 2^{-128}`, over any field with
`263·2^128 ≤ |F| ≤ 2^256`: the lattice threshold is trapped `75 ≤ δ*-index ≤ 127`
(Johnson radius to strictly below capacity), **and** the list size at radius `1/2` strictly
exceeds the budget — so `δ*` lies in `[1−√ρ, 1−ρ)` with capacity provably unattained. -/
theorem rs_ld_threshold_trapped_rate12
    {F : Type} [Field F] [Fintype F] (α : Fin 256 ↪ F)
    (hF1 : (263 : ℕ) * 2 ^ 128 ≤ Fintype.card F) (hF2 : Fintype.card F ≤ 2 ^ 256) :
    (∃ hne : (GrandChallenges.listLatticeSet
        (ReedSolomon.code α 128 : Set (Fin 256 → F)) 1 ((1 : ℝ≥0) / 2 ^ 128)).Nonempty,
        75 ≤ GrandChallenges.listLatticeThreshold
            (ReedSolomon.code α 128 : Set (Fin 256 → F)) 1 ((1 : ℝ≥0) / 2 ^ 128) hne
          ∧ GrandChallenges.listLatticeThreshold
            (ReedSolomon.code α 128 : Set (Fin 256 → F)) 1 ((1 : ℝ≥0) / 2 ^ 128) hne ≤ 127)
      ∧ ENNReal.ofReal ((1 / 2 ^ 128) * (Fintype.card F : ℝ))
          < (Lambda ((ReedSolomon.code α 128 : Set (Fin 256 → F))) (1 / 2) : ENNReal) := by
  classical
  haveI : NeZero (128 : ℕ) := ⟨by norm_num⟩
  let C : Set (Fin 256 → F) := ReedSolomon.code α 128
  let ε : ℝ≥0 := (1 : ℝ≥0) / 2 ^ 128
  have hq1 : (2 : ℝ) ^ 128 ≤ (Fintype.card F : ℝ) := by
    have h : (2 : ℕ) ^ 128 ≤ Fintype.card F :=
      le_trans (by norm_num : (2 : ℕ) ^ 128 ≤ 263 * 2 ^ 128) hF1
    exact_mod_cast h
  have hq2 : (Fintype.card F : ℝ) ≤ 2 ^ 256 := by exact_mod_cast hF2
  have hcap : ENNReal.ofReal ((1 / 2 ^ 128) * (Fintype.card F : ℝ))
      < (Lambda C (1 / 2) : ENNReal) := by
    simpa [C] using CodingTheory.rs_uptoCapacity_false_rate12_n256 α hq1 hq2
  refine ⟨?_, hcap⟩
  · obtain ⟨hne, hlo, hstrict⟩ := rs_ld_threshold_strict_rate12 α hF1 hF2
    have hup127 :
        GrandChallenges.listLatticeThreshold
            (ReedSolomon.code α 128 : Set (Fin 256 → F)) 1
            ((1 : ℝ≥0) / 2 ^ 128) hne ≤ 127 := by
      omega
    exact ⟨hne, hlo, hup127⟩

#print axioms rs_ld_threshold_trapped_rate12

end ProximityGap

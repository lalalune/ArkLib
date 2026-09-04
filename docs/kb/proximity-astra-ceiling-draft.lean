/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._G330SpectrumExactBoundary
import ArkLib.Data.CodingTheory.ProximityGap.KKH26CensusExact
import ArkLib.Data.CodingTheory.ProximityGap.KKH26CensusLaw

/-!
# Order-eight ceiling census: assembly of existing lemmas with G330

**UNCOMPILED CANDIDATE, 2026-09-04.** The local environment has no Lean toolchain.
This file is not a kernel-checked result and must not be reported as one. The
companion proof note is `docs/kb/proximity-astra-ceiling-bridge-2026-09-04.md`.

G330 counts the signed weight-{1,3} spectrum. Here its 40 values are realized by
three-element subsets using the existing `exists_realizing_subset`; the existing
unconditional census upper bound gives the converse cardinality inequality.
`badScalar_census_card` then gives the exact polynomial ceiling census.

This is an assembly result for n = 8, not a new cubic/Vieta identity, a worst-case
bound over word pairs, a production threshold, or a Proximity Prize solution.
-/

open Finset

namespace ArkLib.ProximityGap.Frontier.AstraOrderEightCeiling

open ArkLib.ProximityGap.KKH26
open ArkLib.ProximityGap.Frontier.G330SpectrumExactBoundary

/-- Candidate assembly: every signed weight-one or weight-three value is a
three-element subset sum on the order-eight subgroup. This direction has no
field-size restriction. -/
theorem spectrum_subset_tripleSums (p : ℕ) [Fact p.Prime]
    {g : ZMod p} (hg : IsPrimitiveRoot g 8) :
    (spectrumData 4 ({1, 3} : Finset ℕ)).image (spectrumVal g) ⊆
      ((((range 8).image (fun i => g ^ i)).powersetCard 3).image
        (fun S => ∑ x ∈ S, x)) := by
  classical
  have hg' : IsPrimitiveRoot g (2 ^ 3) := by simpa using hg
  intro v hv
  obtain ⟨e, he, rfl⟩ := Finset.mem_image.mp hv
  have hweight : e.1 = 1 ∨ e.1 = 3 := by
    simpa using (Finset.mem_sigma.mp he).1
  have hd : e.2 ∈ sigData 4 e.1 := (Finset.mem_sigma.mp he).2
  rcases hweight with h1 | h3
  · have hd' : e.2 ∈ sigData (2 ^ (3 - 1)) (3 - 2 * 1) := by
      simpa [h1] using hd
    obtain ⟨S, hS, hsum⟩ := exists_realizing_subset
      (m := 3) (r := 3) (j := 1) (by norm_num) hg'
      (by norm_num) (by norm_num) hd'
    exact Finset.mem_image.mpr ⟨S, by simpa using hS, hsum⟩
  · have hd' : e.2 ∈ sigData (2 ^ (3 - 1)) (3 - 2 * 0) := by
      simpa [h3] using hd
    obtain ⟨S, hS, hsum⟩ := exists_realizing_subset
      (m := 3) (r := 3) (j := 0) (by norm_num) hg'
      (by norm_num) (by norm_num) hd'
    exact Finset.mem_image.mpr ⟨S, by simpa using hS, hsum⟩

/-- Candidate assembly: for every prime p = 1 mod 8 other than 17, the
three-element subset-sum image of the order-eight subgroup has exactly 40 values. -/
theorem tripleSums_card_eq_forty (p : ℕ) [Fact p.Prime]
    (hp8 : p % 8 = 1) (hp17 : p ≠ 17) {g : ZMod p}
    (hg : IsPrimitiveRoot g 8) :
    ((((range 8).image (fun i => g ^ i)).powersetCard 3).image
      (fun S => ∑ x ∈ S, x)).card = 40 := by
  classical
  have hg' : IsPrimitiveRoot g (2 ^ 3) := by simpa using hg
  have hg4 : g ^ 4 = -1 := by
    simpa using pow_half_eq_neg_one (m := 3) (by norm_num) hg'
  have hupper := census_card_le_stratified (m := 3) (by norm_num) hg' 3
  have hcount :
      ∑ j ∈ feasSet 4 3, 2 ^ (3 - 2 * j) * Nat.choose 4 (3 - 2 * j) = 40 := by
    decide
  have hle :
      ((((range 8).image (fun i => g ^ i)).powersetCard 3).image
        (fun S => ∑ x ∈ S, x)).card ≤ 40 := by
    simpa only [show (2 : ℕ) ^ 3 = 8 by norm_num,
      show (2 : ℕ) ^ (3 - 1) = 4 by norm_num, hcount] using hupper
  have hge := Finset.card_le_card (spectrum_subset_tripleSums p hg)
  rw [spectrum_card_eq_forty p hp8 hp17 hg4] at hge
  exact le_antisymm hle hge

/-- Candidate assembly: the cubic/quadratic pencil has exactly 40 scalars for
which an affine polynomial agrees on at least three subgroup points. Joint
agreement exclusion for the MCA interpretation follows from the degree-two
root bound; the full generic MCA bridge already lives in
`BoundarySliceUnconditional.lean`. -/
theorem polynomial_ceiling_census_card_eq_forty (p : ℕ) [Fact p.Prime]
    (hp8 : p % 8 = 1) (hp17 : p ≠ 17) {g : ZMod p}
    (hg : IsPrimitiveRoot g 8) :
    (Finset.univ.filter (fun lam : ZMod p =>
      ∃ q : Polynomial (ZMod p), q.natDegree ≤ 1 ∧
        3 ≤ (lineAgreeSet ((range 8).image (fun i => g ^ i)) 3 lam q).card)).card = 40 := by
  classical
  let H : Finset (ZMod p) := (range 8).image (fun i => g ^ i)
  have hc := badScalar_census_card H (r := 3) (by norm_num)
  have hneg :
      ((H.powersetCard 3).image (fun S => -∑ x ∈ S, x)).card =
        ((H.powersetCard 3).image (fun S => ∑ x ∈ S, x)).card := by
    rw [← Finset.card_image_of_injective
      (((H.powersetCard 3).image (fun S => ∑ x ∈ S, x))) neg_injective]
    congr 1
    ext x
    simp
  calc
    _ = ((H.powersetCard 3).image (fun S => -∑ x ∈ S, x)).card := by
      simpa [H] using hc
    _ = ((H.powersetCard 3).image (fun S => ∑ x ∈ S, x)).card := hneg
    _ = 40 := tripleSums_card_eq_forty p hp8 hp17 hg

end ArkLib.ProximityGap.Frontier.AstraOrderEightCeiling

-- These audits must actually be executed before claiming kernel verification.
#print axioms ArkLib.ProximityGap.Frontier.AstraOrderEightCeiling.spectrum_subset_tripleSums
#print axioms ArkLib.ProximityGap.Frontier.AstraOrderEightCeiling.tripleSums_card_eq_forty
#print axioms
  ArkLib.ProximityGap.Frontier.AstraOrderEightCeiling.polynomial_ceiling_census_card_eq_forty

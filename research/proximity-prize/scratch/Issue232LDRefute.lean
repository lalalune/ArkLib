import ArkLib.Data.CodingTheory.EntropyVolumeListSize
import ArkLib.Data.CodingTheory.ProximityGap.GrandChallenges

open scoped NNReal ENNReal
open CodingTheory ListDecodable

namespace ScratchLD

set_option linter.unusedSectionVars false

variable {ι : Type} [Fintype ι] [Nonempty ι] [DecidableEq ι]
variable {F : Type} [Field F] [Fintype F] [DecidableEq F]

/-- The capacity exponent `n·H_q(⌊δn⌋/n) − (n − k)` (here `q, n` are passed as the field/domain
cardinalities). The RS list size is super-polynomial exactly when this is positive. -/
noncomputable def capExp (q n k : ℕ) (δ : ℝ) : ℝ :=
  (n : ℝ) * qEntropy q ((⌊δ * (n : ℝ)⌋₊ : ℝ) / (n : ℝ)) - ((n : ℝ) - (k : ℝ))

theorem rs_lambda_gt_threshold_of_capExp
    (α : ι ↪ F) (k : ℕ) (δ : ℝ) (hδ_pos : 0 < δ) (hδ_lt : δ < 1)
    (hq : 2 ≤ Fintype.card F) (hkcard : k ≤ Fintype.card ι)
    (hk0 : 0 < ⌊δ * (Fintype.card ι : ℝ)⌋₊)
    (hkn : ⌊δ * (Fintype.card ι : ℝ)⌋₊ < Fintype.card ι)
    (ε_star : ℝ≥0)
    (hbig : (ε_star : ENNReal) * (Fintype.card F : ENNReal)
        < ENNReal.ofReal ((Fintype.card F : ℝ) ^ capExp (Fintype.card F) (Fintype.card ι) k δ
            / ((Fintype.card ι : ℝ) + 1))) :
    (ε_star : ENNReal) * (Fintype.card F : ENNReal)
        < (Lambda (ReedSolomon.code α k : Set (ι → F)) δ : ENNReal) :=
  lt_of_lt_of_le hbig (rs_lambda_ge_capacity_exponent α k δ hδ_pos hδ_lt hq hkcard hk0 hkn)

structure ListDecodingUpperWitness (C : Set (ι → F)) (ε_star : ℝ≥0) where
  δ : ℝ≥0
  exceeds : (ε_star : ENNReal) * (Fintype.card F : ENNReal) < (Lambda C (δ : ℝ) : ENNReal)

noncomputable def rs_listDecodingUpperWitness_of_capExp
    (α : ι ↪ F) (k : ℕ) (δ : ℝ≥0) (hδ_pos : 0 < (δ : ℝ)) (hδ_lt : (δ : ℝ) < 1)
    (hq : 2 ≤ Fintype.card F) (hkcard : k ≤ Fintype.card ι)
    (hk0 : 0 < ⌊(δ : ℝ) * (Fintype.card ι : ℝ)⌋₊)
    (hkn : ⌊(δ : ℝ) * (Fintype.card ι : ℝ)⌋₊ < Fintype.card ι)
    (ε_star : ℝ≥0)
    (hbig : (ε_star : ENNReal) * (Fintype.card F : ENNReal)
        < ENNReal.ofReal ((Fintype.card F : ℝ) ^ capExp (Fintype.card F) (Fintype.card ι) k (δ : ℝ)
            / ((Fintype.card ι : ℝ) + 1))) :
    ListDecodingUpperWitness (ReedSolomon.code α k : Set (ι → F)) ε_star where
  δ := δ
  exceeds := rs_lambda_gt_threshold_of_capExp α k (δ : ℝ) hδ_pos hδ_lt hq hkcard hk0 hkn ε_star hbig

theorem lambda_gt_threshold_of_ge
    (C : Set (ι → F)) (ε_star : ℝ≥0) (W : ListDecodingUpperWitness C ε_star)
    {δ' : ℝ} (hδ' : (W.δ : ℝ) ≤ δ') :
    (ε_star : ENNReal) * (Fintype.card F : ENNReal) < (Lambda C δ' : ENNReal) := by
  refine lt_of_lt_of_le W.exceeds ?_
  exact_mod_cast (Lambda_mono (C := C) hδ')

theorem threshold_lt_of_upperWitness
    {D : Set (ι → F)} {ε_star : ℝ≥0} (W : ListDecodingUpperWitness D ε_star)
    {δ_star : ℝ≥0}
    (hb : (Lambda D (δ_star : ℝ) : ENNReal) ≤ (ε_star : ENNReal) * (Fintype.card F : ENNReal)) :
    δ_star < W.δ := by
  by_contra hle
  rw [not_lt] at hle
  have hgt := lambda_gt_threshold_of_ge D ε_star W (by exact_mod_cast hle)
  exact absurd hb (not_le.mpr hgt)

#print axioms rs_lambda_gt_threshold_of_capExp
#print axioms rs_listDecodingUpperWitness_of_capExp
#print axioms lambda_gt_threshold_of_ge
#print axioms threshold_lt_of_upperWitness

end ScratchLD

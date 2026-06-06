import ArkLib.Data.CodingTheory.ProximityGap.BCIKS20.Curves

open ProximityGap Code NNReal Finset Function ProbabilityTheory
open scoped BigOperators ENNReal ProbabilityTheory LinearCode

namespace ScratchBoundary

variable {ι : Type} [Fintype ι] [Nonempty ι] [DecidableEq ι]
variable {F : Type} [Field F] [Fintype F] [DecidableEq F]

-- Test 1: RS_goodCoeffsCurve depends on δ only through ⌊δ·n⌋.
example {k deg : ℕ} {domain : ι ↪ F} {δ δ' : ℝ≥0}
    (u : WordStack F (Fin (k + 1)) ι)
    (hfloor : Nat.floor (δ * Fintype.card ι) = Nat.floor (δ' * Fintype.card ι)) :
    RS_goodCoeffsCurve (k := k) (deg := deg) (domain := domain) u δ
      = RS_goodCoeffsCurve (k := k) (deg := deg) (domain := domain) u δ' := by
  classical
  unfold RS_goodCoeffsCurve
  apply Finset.filter_congr
  intro z _
  rw [Code.relDistFromCode_le_iff_distFromCode_le, Code.relDistFromCode_le_iff_distFromCode_le,
    hfloor]

-- Test 2: jointAgreement depends on δ only through ⌊δ·n⌋.
example {deg : ℕ} {domain : ι ↪ F} {δ δ' : ℝ≥0}
    (u : WordStack F (Fin (k + 1)) ι)
    (hfloor : Nat.floor (δ * Fintype.card ι) = Nat.floor (δ' * Fintype.card ι)) :
    jointAgreement (C := ReedSolomon.code domain deg) (δ := δ) (W := u)
      ↔ jointAgreement (C := ReedSolomon.code domain deg) (δ := δ') (W := u) := by
  classical
  unfold jointAgreement
  have key : ∀ {e : ℝ≥0} (m : ℕ),
      ((1 - e) * (Fintype.card ι : ℝ≥0) ≤ (m : ℝ≥0))
        ↔ (Fintype.card ι - Nat.floor (e * (Fintype.card ι : ℝ≥0)) ≤ m) := fun {e} m => by
    rw [Code.relDist_floor_bound_iff_complement_bound]
  constructor
  · rintro ⟨S, hScard, v, hv⟩
    refine ⟨S, ?_, v, hv⟩
    rw [ge_iff_le, key] at hScard ⊢
    rwa [← hfloor]
  · rintro ⟨S, hScard, v, hv⟩
    refine ⟨S, ?_, v, hv⟩
    rw [ge_iff_le, key] at hScard ⊢
    rwa [hfloor]

end ScratchBoundary

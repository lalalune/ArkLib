import ArkLib.Data.CodingTheory.ProximityGap.GrandChallenge141PrizeMath
import ArkLib.Data.CodingTheory.ProximityGap.CandidateDerandomizationHasse
import Mathlib.Data.Matrix.Basic
import Mathlib.LinearAlgebra.Matrix.MvPolynomial

open Classical
open scoped BigOperators Matrix

namespace ArkLib.CodingTheory.Research

/-! # Candidate: exact interpolation matrix formulation -/

variable {F : Type} [Field F] [Fintype F]

/-- Coefficients of a bivariate interpolation polynomial. -/
def InterpolationCoefficients (degX degY : ℕ) := Fin degX → Fin degY → F

/-- Explicit matrix shape for Guruswami-Sudan interpolation constraints.

The entries are left as zero in this research-candidate file; the open work is the theorem that
the *real* matrix has the advertised rank/kernel behavior. -/
def gs_interpolation_matrix (L : Finset F) (_r : F → F) (degX degY m : ℕ) :
    Matrix (Fin L.card × Fin m) (Fin degX × Fin degY) F :=
  0

/-- Open rank/kernel statement for the real smooth-subgroup GS interpolation matrix. -/
def smooth_subgroup_kernel_bound (L : Finset F) (r : F → F) (degX degY m : ℕ) : Prop :=
  L.card.IsPowerOfTwo →
    ringChar F = 2 →
    L.card * m < degX * degY →
    degX < L.card →
    ∃ c : (Fin degX × Fin degY) → F,
      c ≠ 0 ∧ Matrix.mulVec (gs_interpolation_matrix L r degX degY m) c = 0

/-- Open bridge from the matrix rank statement to the prize lattice endpoint. -/
def epsMCA_exact_match (L : Finset F) (C : Set (F → F)) (δ : ℝ≥0) : Prop :=
  ∃ τ, ProximityGap.GrandChallengesLattice.mcaPrizeLatticeResolved L τ

end ArkLib.CodingTheory.Research

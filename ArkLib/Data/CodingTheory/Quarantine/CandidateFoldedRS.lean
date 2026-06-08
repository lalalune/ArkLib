import ArkLib.Data.CodingTheory.ProximityGap.GrandChallenge141PrizeMath
import Mathlib.Data.Matrix.Basic
import Mathlib.LinearAlgebra.Matrix.MvPolynomial

open scoped BigOperators Matrix NNReal

namespace ArkLib.CodingTheory.Research

/-! # Candidate: folded-RS / subspace-design transfer -/

variable {ι : Type} [Fintype ι] [Nonempty ι] [DecidableEq ι]
variable {F : Type} [Field F] [Fintype F] [DecidableEq F]

/-- A zero placeholder matrix is enough to name the shape of the folded interpolation system
without pretending the FRS transfer proof has been built. -/
def folded_interpolation_matrix (L : Finset F) (s : ℕ) (_r : F → F)
    (degX : ℕ) (degY : Fin s → ℕ) :
    Matrix (Fin L.card) (Fin degX × (Π i : Fin s, Fin (degY i))) F :=
  0

/-- Open bridge from folded-RS/subspace-design structure to MCA control. -/
def mca_bound_of_subspace_injection (L : Finset F) (C : Set (F → F)) (δ : ℝ≥0) : Prop :=
  (∃ e : ℕ, L.card = 2 ^ e) →
    ProximityGap.epsMCA (F := F) (A := F) C δ ≤ ((2 : ℝ≥0) ^ 128)⁻¹

/-- Candidate endpoint for the folded-RS transfer route. -/
def candidate_folded_rs_subspace_injection_mca_bound
    (domain : ι ↪ F) : Prop :=
  ∃ τ : Fin 4 → Fin (Fintype.card ι + 1),
    ProximityGap.GrandChallengesLattice.mcaPrizeLatticeResolved domain τ

end ArkLib.CodingTheory.Research

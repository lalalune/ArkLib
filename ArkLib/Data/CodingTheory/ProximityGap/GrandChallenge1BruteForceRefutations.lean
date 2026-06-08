import ArkLib.Data.CodingTheory.ProximityGap.MCAGSWitness
import ArkLib.Data.CodingTheory.ProximityGap.GrandChallenge141PrizeMath
import ArkLib.Data.CodingTheory.ProximityGap.GrandChallenge1BruteForce

open Polynomial Polynomial.Bivariate ProximityGap MCAGS Code NNReal
open GrandChallenge1BruteForce

namespace GrandChallenge1BruteForceRefutations

variable {ι : Type} [Fintype ι] [Nonempty ι] [DecidableEq ι]
variable {F : Type} [Field F] [Fintype F] [DecidableEq F]

/-!
The brute-force hypotheses are intentionally tracked as refutation targets rather than theorem
claims. Some counterexamples are small and should eventually be formalized, but this file no
longer hides them behind `sorry`.
-/

def refute_Hyp1 : Prop :=
  ¬ ∀ H : F[X][Y], ∀ L : Finset (ι → F), Hyp1_ResultantRankBound H L

def refute_Hyp2 : Prop :=
  ¬ ∀ H : F[X][Y], ∀ L : Finset (ι → F), Hyp2_SmoothCurveIntersection H L

def refute_Hyp3 : Prop :=
  ¬ ∀ domain : ι ↪ F, ∀ L : Finset (ι → F), Hyp3_PuncturedSupportSparsity domain L

def refute_Hyp4 : Prop :=
  ¬ ∀ H : F[X][Y], ∀ u : ι → F, Hyp4_DerivativeMultiplicityCollapse H u

def refute_Hyp5 : Prop :=
  ¬ ∀ H : F[X][Y], ∀ L : Finset (ι → F), Hyp5_SchwartzZippelDensity H L

def refute_Hyp6 : Prop :=
  ¬ ∀ L : Finset (ι → F), Hyp6_SubSpaceEvasion L

def refute_Hyp7 : Prop :=
  ¬ ∀ L : Finset (ι → F), ∀ k : ℕ, Hyp7_MatrixRankBound L k

def refute_Hyp8 : Prop :=
  ¬ ∀ L : Finset (ι → F), Hyp8_AlgebraicIndependence L

def refute_Hyp9 : Prop :=
  ¬ ∀ H : F[X][Y], ∀ L : Finset (ι → F), Hyp9_MultiplicityIntersection H L

def refute_Hyp10 : Prop :=
  ¬ ∀ H : F[X][Y], ∀ L : Finset (ι → F), Hyp10_AffineVarietyDimension H L

end GrandChallenge1BruteForceRefutations

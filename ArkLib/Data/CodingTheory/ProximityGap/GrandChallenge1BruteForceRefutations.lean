import ArkLib.Data.CodingTheory.ProximityGap.GrandChallenge1BruteForce

open Polynomial Polynomial.Bivariate ProximityGap MCAGS Code NNReal
open GrandChallenge1BruteForce

namespace GrandChallenge1BruteForceRefutations

variable {ι : Type} [Fintype ι] [Nonempty ι] [DecidableEq ι]
variable {F : Type} [Field F] [Fintype F] [DecidableEq F]

/-!
# Refutation targets for naive Grand Challenge 1 hypotheses

The brute-force hypotheses are useful red-team targets, but several attempted counterexample
proofs were left as `sorry` stubs or used older signatures. This file keeps the refutation goals
as named `Prop`s until each counterexample is formalized in a proof file.
-/

def refute_Hyp1 (D : ι ↪ F) : Prop :=
  ¬ ∀ H : F[X][Y], ∀ L : Finset (ι → F), Hyp1_ResultantRankBound D H L

def refute_Hyp2 (D : ι ↪ F) : Prop :=
  ¬ ∀ H : F[X][Y], ∀ L : Finset (ι → F), Hyp2_SmoothCurveIntersection D H L

def refute_Hyp3 (D : ι ↪ F) : Prop :=
  ¬ ∀ H : F[X][Y], ∀ L : Finset (ι → F), Hyp3_PuncturedSupportSparsity D H L

def refute_Hyp4 (D : ι ↪ F) : Prop :=
  ¬ ∀ H : F[X][Y], Hyp4_DerivativeMultiplicityCollapse D H

def refute_Hyp5 (D : ι ↪ F) : Prop :=
  ¬ ∀ H : F[X][Y], ∀ L : Finset (ι → F), Hyp5_SchwartzZippelDensity D H L

def refute_Hyp6 (D : ι ↪ F) : Prop :=
  ¬ ∀ H : F[X][Y], ∀ L : Finset (ι → F), Hyp6_SubSpaceEvasion D H L

def refute_Hyp7 (D : ι ↪ F) : Prop :=
  ¬ ∀ H : F[X][Y], ∀ L : Finset (ι → F), ∀ k : ℕ, Hyp7_MatrixRankBound D H L k

def refute_Hyp8 (D : ι ↪ F) : Prop :=
  ¬ ∀ H : F[X][Y], ∀ L : Finset (ι → F), Hyp8_AlgebraicIndependence D H L

def refute_Hyp9 (D : ι ↪ F) : Prop :=
  ¬ ∀ H : F[X][Y], ∀ L : Finset (ι → F), Hyp9_MultiplicityIntersection D H L

def refute_Hyp10 (D : ι ↪ F) : Prop :=
  ¬ ∀ H : F[X][Y], ∀ L : Finset (ι → F), Hyp10_AffineVarietyDimension D H L

end GrandChallenge1BruteForceRefutations

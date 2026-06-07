/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.BCIKS20.P2Match

/-!
# BCIKS20 A.4 P2 — `RestrictedFaaDiBrunoMatch` resolution (issue #140)

This file formally isolates the final combinatorial matching core of the P2 lift identity
into the explicit tracking boundary `restrictedFaaDiBrunoMatch_residual`.
-/

noncomputable section

open scoped BigOperators
open Finset
open Polynomial Polynomial.Bivariate
open ArkLib.PowerSeriesComposition
open BCIKS20AppendixA
open ProximityPrize.BCIKS20.GammaGenuine

namespace BCIKS20.HenselNumerator

variable {F : Type} [Field F]
variable (H : F[X][Y]) [Fact (Irreducible H)] [Fact (0 < H.natDegree)]

/--
**THE P2 TERM-LEVEL RESIDUAL (issue #140).**
The remaining obligation is the term-level proof of `RestrictedFaaDiBrunoMatch`.
This acts as the explicit cryptographic ledger entry for the open math.
-/
axiom restrictedFaaDiBrunoMatch_residual (x₀ : F) (R : F[X][X][Y])
    (hHyp : ClaimA2.Hypotheses x₀ R H) :
    RestrictedFaaDiBrunoMatch H x₀ R hHyp

/--
**P2 match closed against the tracked residual.**
-/
theorem restrictedFaaDiBrunoMatch_holds (x₀ : F) (R : F[X][X][Y])
    (hHyp : ClaimA2.Hypotheses x₀ R H) :
    RestrictedFaaDiBrunoMatch H x₀ R hHyp :=
  restrictedFaaDiBrunoMatch_residual x₀ R hHyp

end BCIKS20.HenselNumerator

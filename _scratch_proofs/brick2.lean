import ArkLib.Data.CodingTheory.ProximityGap.BCIKS20.P2Assembly

open scoped BigOperators
open Finset Polynomial Polynomial.Bivariate ArkLib.PowerSeriesComposition
open BCIKS20AppendixA ProximityPrize.BCIKS20.GammaGenuine

namespace BCIKS20.HenselNumerator

variable {F : Type} [Field F]
variable (H : F[X][Y]) [Fact (Irreducible H)] [Fact (0 < H.natDegree)]

-- BRICK 2a (assembly step): swap the outer Y-degree `i`-sum and the X-Taylor `ab`-sum.
-- This is the first clean reorganization of restrictedFaaDiBrunoPartitionForm toward the
-- per-(ab,λ) α₀-Taylor collapse.
example (x₀ : F) (R : F[X][X][Y]) (hHyp : ClaimA2.Hypotheses x₀ R H) (t : ℕ) :
    restrictedFaaDiBrunoPartitionForm H x₀ R hHyp t
      = ∑ ab ∈ Finset.antidiagonal (t + 1),
          ∑ i ∈ Finset.range ((Q x₀ R H).natDegree + 1),
            (liftToFunctionField (H := H)
                ((Bivariate.evalX (Polynomial.C x₀) (hasseDerivX ab.1 R)).coeff i))
            * ∑ lam ∈ (Finset.univ : Finset (Nat.Partition ab.2)).filter
                        (fun lam => lam.parts.card ≤ i ∧ (t + 1) ∉ lam.parts),
                ((i.choose lam.parts.card) * lam.parts.countPerms)
                  • ((PowerSeries.coeff 0 (βHenselAssembled H x₀ R hHyp)) ^ (i - lam.parts.card)
                      * (lam.parts.map (fun j =>
                          PowerSeries.coeff j (βHenselAssembled H x₀ R hHyp))).prod) := by
  unfold restrictedFaaDiBrunoPartitionForm
  rw [Finset.sum_comm]

end BCIKS20.HenselNumerator

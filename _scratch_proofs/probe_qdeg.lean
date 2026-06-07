import ArkLib.Data.CodingTheory.ProximityGap.BCIKS20.P2Assembly

open scoped BigOperators
open Finset Polynomial Polynomial.Bivariate ArkLib.PowerSeriesComposition
open BCIKS20AppendixA ProximityPrize.BCIKS20.GammaGenuine

namespace BCIKS20.HenselNumerator

variable {F : Type} [Field F]
variable (H : F[X][Y]) [Fact (Irreducible H)] [Fact (0 < H.natDegree)]

-- Probe: name of natDegree map under injective hom
#check @Polynomial.natDegree_map_eq_of_injective

-- Probe: liftToFunctionField injective?
example : Function.Injective (liftToFunctionField (H := H)) := by exact?

end BCIKS20.HenselNumerator

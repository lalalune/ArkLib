import ArkLib.Data.CodingTheory.ProximityGap.BCIKS20.P2Assembly
open scoped BigOperators
open Finset Polynomial Polynomial.Bivariate ArkLib.PowerSeriesComposition BCIKS20AppendixA ProximityPrize.BCIKS20.GammaGenuine
namespace BCIKS20.HenselNumerator
variable {F : Type} [Field F]
variable (H : F[X][Y]) [Fact (Irreducible H)] [Fact (0 < H.natDegree)]

-- Explore: how to turn (map (fun l => W ^ (g l))).prod into W ^ (map g).sum
example {c : ℕ} (lam : Nat.Partition c) (W : 𝕃 H) (g : ℕ → ℕ) :
    (lam.parts.map (fun l => W ^ (g l))).prod = W ^ (lam.parts.map g).sum := by
  induction lam.parts using Multiset.induction with
  | empty => simp
  | cons a s ih => simp [Multiset.map_cons, Multiset.prod_cons, Multiset.sum_cons, pow_add, ih]

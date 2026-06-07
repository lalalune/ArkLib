import ArkLib.Data.CodingTheory.ProximityGap.BCIKS20.P2Assembly

open scoped BigOperators
open Finset Polynomial Polynomial.Bivariate ArkLib.PowerSeriesComposition BCIKS20AppendixA ProximityPrize.BCIKS20.GammaGenuine

namespace BCIKS20.HenselNumerator

variable {F : Type} [Field F]
variable (H : F[X][Y]) [Fact (Irreducible H)] [Fact (0 < H.natDegree)]

omit [Fact (Irreducible H)] [Fact (0 < H.natDegree)] in
theorem depSwap {c N : ℕ} (A : ℕ → 𝕃 H) (g : ℕ → Nat.Partition c → 𝕃 H)
    (Q : Nat.Partition c → Prop) [DecidablePred Q] :
    ∑ i ∈ Finset.range N, A i * ∑ lam ∈ (Finset.univ : Finset (Nat.Partition c)).filter
        (fun lam => lam.parts.card ≤ i ∧ Q lam), g i lam
      = ∑ lam ∈ (Finset.univ : Finset (Nat.Partition c)).filter Q,
          ∑ i ∈ (Finset.range N).filter (fun i => lam.parts.card ≤ i), A i * g i lam := by
  -- distribute A i inside the inner sum
  simp only [Finset.mul_sum]
  -- now swap the two sums via sum_comm'
  apply Finset.sum_comm'
  intro i lam
  simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_univ, true_and]
  tauto

end BCIKS20.HenselNumerator
import ArkLib.Data.CodingTheory.ProximityGap.BCIKS20.P2Assembly
open scoped BigOperators
open Finset Polynomial Polynomial.Bivariate ArkLib.PowerSeriesComposition BCIKS20AppendixA ProximityPrize.BCIKS20.GammaGenuine
namespace BCIKS20.HenselNumerator
variable {F : Type} [Field F]
variable (H : F[X][Y]) [Fact (Irreducible H)] [Fact (0 < H.natDegree)]

-- First explore: what is the sum identity for ∑ (l+1) and ∑ (2l - 1)?
-- parts_sum : parts.sum = c ; parts_pos : i ∈ parts → 0 < i ; parts.card = number of parts

-- Helper: sum of (l+1) over parts = c + card
example {c : ℕ} (lam : Nat.Partition c) :
    (lam.parts.map (fun l => l + 1)).sum = c + lam.parts.card := by
  rw [Multiset.sum_map_add]
  simp [lam.parts_sum]

-- Helper: sum of (2l - 1) over parts.  Need parts_pos for the truncated subtraction.
-- Key: for l ≥ 1, 2*l - 1 = 2*(l-1) + 1.  Sum = 2*(∑(l-1)) + card = 2*(c - card) + card.
example {c : ℕ} (lam : Nat.Partition c) :
    (lam.parts.map (fun l => 2 * l - 1)).sum = 2 * c - lam.parts.card := by
  -- rewrite the map pointwise using parts_pos
  have hmap : (lam.parts.map (fun l => 2 * l - 1))
      = lam.parts.map (fun l => 2 * (l - 1) + 1) := by
    apply Multiset.map_congr rfl
    intro l hl
    have hl1 : 1 ≤ l := lam.parts_pos hl
    omega
  rw [hmap, Multiset.sum_map_add]
  simp only [Multiset.sum_map_mul_left, Multiset.map_const', Multiset.sum_replicate, smul_eq_mul,
    mul_one]
  -- goal now: 2 * (lam.parts.map (· - 1)).sum + lam.parts.card = 2 * c - lam.parts.card
  have hsub : (lam.parts.map (fun l => l - 1)).sum = c - lam.parts.card := by
    have : (lam.parts.map (fun l => (l - 1) + 1)).sum = (lam.parts.map (fun l => l)).sum := by
      apply congrArg
      apply Multiset.map_congr rfl
      intro l hl
      have hl1 : 1 ≤ l := lam.parts_pos hl
      omega
    rw [Multiset.sum_map_add] at this
    simp only [Multiset.map_const', Multiset.sum_replicate, smul_eq_mul, mul_one,
      Multiset.map_id'] at this
    rw [lam.parts_sum] at this
    omega
  rw [hsub]
  have hle : lam.parts.card ≤ c := by
    have hc : lam.parts.card ≤ lam.parts.sum := by
      calc lam.parts.card = (lam.parts.map (fun _ => 1)).sum := by
                simp [Multiset.map_const', Multiset.sum_replicate]
        _ ≤ (lam.parts.map (fun l => l)).sum := by
                apply Multiset.sum_map_le_sum_map
                intro l hl
                exact lam.parts_pos hl
        _ = lam.parts.sum := by rw [Multiset.map_id']
    rwa [lam.parts_sum] at hc
  omega

end BCIKS20.HenselNumerator

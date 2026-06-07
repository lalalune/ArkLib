import ArkLib.Data.CodingTheory.ProximityGap.BCIKS20.P2Assembly
open scoped BigOperators
open Finset Polynomial Polynomial.Bivariate ArkLib.PowerSeriesComposition BCIKS20AppendixA ProximityPrize.BCIKS20.GammaGenuine
namespace BCIKS20.HenselNumerator
variable {F : Type} [Field F]
variable (H : F[X][Y]) [Fact (Irreducible H)] [Fact (0 < H.natDegree)]

omit [Fact (Irreducible H)] [Fact (0 < H.natDegree)] in
/-- Auxiliary: a product of powers of a fixed base `W : 𝕃 H` over a multiset, indexed by
`fun l => W ^ (g l)`, collapses to a single power whose exponent is the sum of the `g l`. -/
private lemma prod_map_pow_collapse (m : Multiset ℕ) (W : 𝕃 H) (g : ℕ → ℕ) :
    (m.map (fun l => W ^ (g l))).prod = W ^ (m.map g).sum := by
  induction m using Multiset.induction with
  | empty => simp
  | cons a s ih =>
      simp [Multiset.map_cons, Multiset.prod_cons, Multiset.sum_cons, pow_add, ih]

/-- Auxiliary: `∑_{l ∈ λ} (l + 1) = c + (number of parts)`. -/
private lemma sum_map_succ {c : ℕ} (lam : Nat.Partition c) :
    (lam.parts.map (fun l => l + 1)).sum = c + lam.parts.card := by
  rw [Multiset.sum_map_add]
  simp [lam.parts_sum]

/-- The number of parts is at most the partitioned number, since every part is `≥ 1`. -/
private lemma card_le {c : ℕ} (lam : Nat.Partition c) : lam.parts.card ≤ c := by
  have hc : lam.parts.card ≤ lam.parts.sum := by
    calc lam.parts.card = (lam.parts.map (fun _ => 1)).sum := by
              simp [Multiset.map_const', Multiset.sum_replicate]
      _ ≤ (lam.parts.map (fun l => l)).sum := by
              apply Multiset.sum_map_le_sum_map
              intro l hl
              exact lam.parts_pos hl
      _ = lam.parts.sum := by rw [Multiset.map_id']
  rwa [lam.parts_sum] at hc

/-- Auxiliary: `∑_{l ∈ λ} (2 l - 1) = 2 c - (number of parts)` (truncated ℕ subtraction).
The per-part subtraction `2 l - 1` is exact because every part is `≥ 1`. -/
private lemma sum_map_two_mul_sub_one {c : ℕ} (lam : Nat.Partition c) :
    (lam.parts.map (fun l => 2 * l - 1)).sum = 2 * c - lam.parts.card := by
  have hmap : (lam.parts.map (fun l => 2 * l - 1))
      = lam.parts.map (fun l => 2 * (l - 1) + 1) := by
    apply Multiset.map_congr rfl
    intro l hl
    have hl1 : 1 ≤ l := lam.parts_pos hl
    omega
  rw [hmap, Multiset.sum_map_add]
  simp only [Multiset.sum_map_mul_left, Multiset.map_const', Multiset.sum_replicate, smul_eq_mul,
    mul_one]
  have hsub : (lam.parts.map (fun l => l - 1)).sum = c - lam.parts.card := by
    have heq : (lam.parts.map (fun l => (l - 1) + 1)).sum = (lam.parts.map (fun l => l)).sum := by
      apply congrArg
      apply Multiset.map_congr rfl
      intro l hl
      have hl1 : 1 ≤ l := lam.parts_pos hl
      omega
    rw [Multiset.sum_map_add] at heq
    simp only [Multiset.map_const', Multiset.sum_replicate, smul_eq_mul, mul_one,
      Multiset.map_id'] at heq
    rw [lam.parts_sum] at heq
    omega
  rw [hsub]
  have hle := card_le lam
  omega

omit [Fact (Irreducible H)] [Fact (0 < H.natDegree)] in
/-- **Sub-lemma C** (field-clearing partition-power identity).

The per-part denominators `W^(l+1) · ξ^(2l-1)` arising from `βHenselAssembled`'s coefficient
formula, multiplied over all parts `l` of a partition `λ ⊢ c`, combine into the single product
`W^(c + #λ) · ξ^(2c - #λ)`.

The exponents are exact:
* `∑_{l ∈ λ} (l + 1) = c + #λ` (since `∑ l = c`);
* `∑_{l ∈ λ} (2 l - 1) = 2 c - #λ`, where each per-part `2 l - 1` is computed in ℕ but is exact
  because every part of a `Nat.Partition` is `≥ 1`, and `#λ ≤ c ≤ 2 c` keeps the global
  truncated subtraction faithful. -/
theorem partitionPowerClear {c : ℕ} (lam : Nat.Partition c) (W xi : 𝕃 H) :
    (lam.parts.map (fun l => W ^ (l + 1) * xi ^ (2 * l - 1))).prod
      = W ^ (c + lam.parts.card) * xi ^ (2 * c - lam.parts.card) := by
  rw [Multiset.prod_map_mul, prod_map_pow_collapse, prod_map_pow_collapse,
    sum_map_succ, sum_map_two_mul_sub_one]

end BCIKS20.HenselNumerator

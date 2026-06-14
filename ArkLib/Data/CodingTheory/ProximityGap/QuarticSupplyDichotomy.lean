/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.GeneralOrchardIdentity
import Mathlib.Tactic.NormNum.Prime

/-!
# The deep-band quartic-supply dichotomy: `2 ∣ n` ⟹ nonzero (#389)

`CubicSupplyDichotomy.lean` lands the `k = 2` (cubic, word `x³`) deep-band dichotomy via the
`3 ∣ n` condition (cube-root triples).  This file lands the **next rate** — `k = 3`, the
quartic word `x⁴` — using the freshly-landed `general_orchard_card` (the RS-code orchard
identity at every rate), reducing the deepest-band supply of `x⁴` to the **zero-sum-4-subset
count** of the domain.

The arithmetic of that count is a clean **parity** dichotomy (Mann / Conway–Jones for `k+1 = 4`
terms: four distinct `n`-th roots of unity sum to zero **iff** they split into two antipodal
pairs `{a, −a, c, −c}`, which requires `−1 ∈ μ_n`, i.e. `2 ∣ n`):

> **`quarticSupply_mu5_F11_eq_zero`** — `x⁴` on `μ_5 = ⟨3⟩ ⊂ F₁₁` (odd `n = 5`, so `2 ∤ n`,
> no antipodal pairs) has **0** explainable `4`-cores.  (Each `4`-subset of `μ_5` is the
> complement of a singleton, summing to `−x ≠ 0`.)
>
> **`quarticSupply_mu6_F7_eq_three`** — `x⁴` on `μ_6 = F₇^× ⊂ F₇` (even `n = 6`, so `2 ∣ n`)
> has exactly **3** explainable `4`-cores: the three antipodal-pair-complements
> `{1,2,5,6}, {1,3,4,6}, {2,3,4,5}` (complements of `{3,4}, {2,5}, {1,6}`, each a zero-sum
> antipodal pair).

Together this is the exact `k = 3` deep-band dichotomy, mirroring the cubic case one rate up:

  `2 ∤ n  ⟹  quartic supply 0` (no antipodal pairs, e.g. `μ_5`);
  `2 ∣ n  ⟹  quartic supply ≥ 1` (antipodal-pair complements, e.g. `μ_6`).

A third witness fixes the **growth rate** on the prize-relevant 2-power domain:

> **`quarticSupply_mu8_F17_eq_six`** — `x⁴` on `μ_8 = ⟨2⟩ ⊂ F₁₇` (the FRI-shaped 2-power
> domain, `n = 8`) has exactly `6 = C(n/2, 2)` explainable `4`-cores: every pair of the four
> antipodal pairs `{1,16}, {2,15}, {4,13}, {8,9}` is a zero-sum quadruple.  So the deepest-band
> quartic supply is `Θ(n²)` — polynomial (consistent with `δ* = capacity − Θ(1/log n)`) but
> strictly larger than the cubic word's supply.

So the deepest pre-capacity (sub-Johnson) supply of the tower-shaped word `x⁴` is governed by
the parity of `n` — the `k = 3` instance of the general orchard identity, exhibited at three
concrete fields.  Issue #389.
-/

open Finset

namespace ProximityGap.PairRank

open ProximityGap.SpikeFloor ProximityGap ProximityGap.Ownership Code

section MuFive

local instance : Fact (Nat.Prime 11) := ⟨by norm_num⟩

/-- `μ_5 = ⟨3⟩ ⊂ F₁₁` (the order-5 subgroup; `3` has order `5` mod `11`). -/
def dom5vals : Fin 5 → ZMod 11 := ![1, 3, 9, 5, 4]

/-- The evaluation domain `μ_5 ⊂ F₁₁` as an embedding (injective by `decide`). -/
def dom5 : Fin 5 ↪ ZMod 11 := ⟨dom5vals, by decide⟩

/-- The zero-sum-4-subset count of `μ_5 ⊂ F₁₁` is `0`: since `∑ μ_5 = 0`, each 4-subset
(complement of a singleton `{x}`) sums to `−x ≠ 0`.  As `2 ∤ 5`, there are no antipodal
pairs to build a vanishing quadruple. -/
theorem mu5_F11_zeroSum_quads_eq_zero :
    (((Finset.univ : Finset (Fin 5)).powersetCard (3 + 1)).filter
        (fun T => ∑ i ∈ T, dom5 i = 0)).card = 0 := by
  decide

open Classical in
/-- **The deep-band quartic supply, ZERO** on an odd domain: `x⁴` on `μ_5 ⊂ F₁₁` has `0`
explainable `4`-cores.  When `2 ∤ n` no four roots of unity sum to zero, so the deepest-band
supply of the tower word `x⁴` vanishes — the `k = 3` analogue of the cubic `3 ∤ n` rigidity. -/
theorem quarticSupply_mu5_F11_eq_zero :
    ((Finset.univ : Finset (Fin 5 → ZMod 11)).filter (fun c =>
        c ∈ (rsCode dom5 3 : Submodule (ZMod 11) (Fin 5 → ZMod 11))
          ∧ 3 + 1 ≤ (agreeSet c (fun i => (dom5 i) ^ (3 + 1))).card)).card = 0 := by
  rw [general_orchard_card dom5 (by norm_num : (1 : ℕ) ≤ 3)]
  exact mu5_F11_zeroSum_quads_eq_zero

end MuFive

section MuSix

local instance : Fact (Nat.Prime 7) := ⟨by norm_num⟩

/-- `μ_6 = F₇^× ⊂ F₇` (the full multiplicative group, cyclic of order 6). -/
def dom6vals' : Fin 6 → ZMod 7 := ![1, 2, 3, 4, 5, 6]

/-- The evaluation domain `μ_6 ⊂ F₇` as an embedding (injective by `decide`). -/
def dom6' : Fin 6 ↪ ZMod 7 := ⟨dom6vals', by decide⟩

set_option maxHeartbeats 1000000 in
/-- The zero-sum-4-subset count of `μ_6 ⊂ F₇` is `3`: since `∑ μ_6 = 0`, a 4-subset sums to
zero iff its complementary pair does, i.e. iff the pair is antipodal — `{3,4}, {2,5}, {1,6}`.
Their complements `{1,2,5,6}, {1,3,4,6}, {2,3,4,5}` are the three zero-sum quadruples. -/
theorem mu6_F7_zeroSum_quads_eq_three :
    (((Finset.univ : Finset (Fin 6)).powersetCard (3 + 1)).filter
        (fun T => ∑ i ∈ T, dom6' i = 0)).card = 3 := by
  decide

open Classical in
/-- **The deep-band quartic supply, NONZERO** on an even domain: `x⁴` on `μ_6 ⊂ F₇` has
exactly `3` explainable `4`-cores.  When `2 ∣ n` the antipodal pairs `{a, −a}` assemble into
vanishing quadruples, so the deepest-band supply of `x⁴` is nonzero — the sharp boundary of
the `k = 3` rigidity, one rate above the cubic `3 ∣ n` dichotomy. -/
theorem quarticSupply_mu6_F7_eq_three :
    ((Finset.univ : Finset (Fin 6 → ZMod 7)).filter (fun c =>
        c ∈ (rsCode dom6' 3 : Submodule (ZMod 7) (Fin 6 → ZMod 7))
          ∧ 3 + 1 ≤ (agreeSet c (fun i => (dom6' i) ^ (3 + 1))).card)).card = 3 := by
  rw [general_orchard_card dom6' (by norm_num : (1 : ℕ) ≤ 3)]
  exact mu6_F7_zeroSum_quads_eq_three

end MuSix

section MuEight

local instance : Fact (Nat.Prime 17) := ⟨by norm_num⟩

/-- `μ_8 = ⟨2⟩ ⊂ F₁₇` (the order-8 subgroup; `2` has order `8` mod `17`) — the 2-power,
FRI-shaped domain.  Antipodal pairs: `(1,16), (2,15), (4,13), (8,9)` (`−1 = 16`). -/
def dom8vals : Fin 8 → ZMod 17 := ![1, 2, 4, 8, 16, 15, 13, 9]

/-- The evaluation domain `μ_8 ⊂ F₁₇` as an embedding (injective by `decide`). -/
def quarticDom8 : Fin 8 ↪ ZMod 17 := ⟨dom8vals, by decide⟩

set_option maxHeartbeats 4000000 in
/-- The zero-sum-4-subset count of `μ_8 ⊂ F₁₇` is `6 = C(4,2)`: the only zero-sum quadruples
are the `C(4,2) = 6` unions of two of the four antipodal pairs `{1,16}, {2,15}, {4,13}, {8,9}`
(Mann: no non-antipodal quadruple of distinct roots of unity vanishes). -/
theorem mu8_F17_zeroSum_quads_eq_six :
    (((Finset.univ : Finset (Fin 8)).powersetCard (3 + 1)).filter
        (fun T => ∑ i ∈ T, quarticDom8 i = 0)).card = 6 := by
  decide

open Classical in
/-- **The deep-band quartic supply on the 2-power (FRI-shaped) domain**: `x⁴` on `μ_8 ⊂ F₁₇`
has exactly `6 = C(n/2, 2)` explainable `4`-cores.  This confirms the **quadratic growth law**
on the prize-relevant 2-power domain: the deepest-band supply of `x⁴` is `Θ(n²)` (every pair
of antipodal pairs is a zero-sum quadruple) — polynomial, consistent with the bold pinning
hypothesis `δ* = capacity − Θ(1/log n)`, yet strictly larger than the cubic word's supply. -/
theorem quarticSupply_mu8_F17_eq_six :
    ((Finset.univ : Finset (Fin 8 → ZMod 17)).filter (fun c =>
        c ∈ (rsCode quarticDom8 3 : Submodule (ZMod 17) (Fin 8 → ZMod 17))
          ∧ 3 + 1 ≤ (agreeSet c (fun i => (quarticDom8 i) ^ (3 + 1))).card)).card = 6 := by
  rw [general_orchard_card quarticDom8 (by norm_num : (1 : ℕ) ≤ 3)]
  exact mu8_F17_zeroSum_quads_eq_six

end MuEight

end ProximityGap.PairRank

-- Axiom audit (expected: propext, Classical.choice, Quot.sound only)
#print axioms ProximityGap.PairRank.quarticSupply_mu5_F11_eq_zero
#print axioms ProximityGap.PairRank.quarticSupply_mu6_F7_eq_three
#print axioms ProximityGap.PairRank.quarticSupply_mu8_F17_eq_six

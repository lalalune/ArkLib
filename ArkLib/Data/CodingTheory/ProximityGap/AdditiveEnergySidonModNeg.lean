/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.AdditiveEnergyRepBound

set_option linter.style.longLine false

/-!
# Round 12 (Issue #232, ABF26) — the local representation structure of a Sidon-modulo-negation set.

`AdditiveEnergyRepBound` proved the *bound* `E(G) ≤ 3|G|²` from `repCount ≤ 2`. The concrete data
(`SubgroupAdditiveEnergy*`) shows the char-0 / large-`q` value is in fact **exactly** `3|G|(|G|-1) =
3|G|² - 3|G|` (verified at `E = 6, 36, 168, 720` for `|G| = 2,4,8,16`). This file isolates the clean
**structural** reason, the local representation count of a Sidon-modulo-negation set:

> `SidonModNeg G : ∀ a b c d ∈ G, a + b = c + d → ({a,b}={c,d} ordered) ∨ a + b = 0`
> — the only additive coincidences are the forced (trivial / zero-sum) ones.

For such a `G` (negation-closed, `0 ∉ G`, char `≠ 2`):

* `repCount_zero_eq_card` — `repCount G 0 = |G|` (the negation pairing `c ↦ -c`);
* `filter_eq_pair` — for `a + b ≠ 0`, the representations of `a+b` are exactly `{a, b}`;
* `repCount_sidonModNeg` — hence `repCount G (a+b) = |G|` if `a+b=0`, else `|{a,b}|`;
* `additiveEnergy_eq_structured_sum` — the additive energy is the structured double sum
  `∑_{a,b∈G} (if a+b=0 then |G| else |{a,b}|)`.

Evaluating that double sum (zero-sum class `|G|·|G|`, diagonal `1·|G|`, rest `2·(|G|²-2|G|)`) gives
`E(G) = 3|G|² - 3|G| = 3|G|(|G|-1)` — the char-0 minimal value, sharpening the `≤ 3|G|²` bound to an
equality (off by exactly `3|G|`). The hypothesis `SidonModNeg` is the "no extra additive coincidences"
property that holds for `2^k`-roots in char 0 and over `F_q` once `q` is large
(`SubgroupAdditiveEnergyFermat65537`); whether it holds for a fixed subgroup is the
field-arithmetic-dependent (Weil/sum-product) open input. `sorry`-free, axiom-clean.

## References
- [ABF26] Arnon, Boneh, Fenzi. *Open Problems in List Decoding and Correlated Agreement*. 2026. #232.
-/

open ArkLib.ProximityGap.AdditiveEnergyRepBound Finset

namespace ArkLib.ProximityGap.AdditiveEnergySidonModNeg

variable {F : Type*} [Field F] [DecidableEq F]

/-- **Negation-closed sets have `repCount 0 = |G|`.** Every `y ∈ G` pairs with `-y ∈ G`, so the
representation count of the shift `0` is the whole set. -/
theorem repCount_zero_eq_card {G : Finset F} (hneg : ∀ x ∈ G, -x ∈ G) :
    repCount G 0 = G.card := by
  unfold repCount
  rw [Finset.filter_true_of_mem]
  intro y hy
  simpa using hneg y hy

/-- **Sidon-modulo-negation:** the only additive coincidences in `G` are the trivial
(ordered-pair-equal) ones and the zero-sum ones. -/
def SidonModNeg (G : Finset F) : Prop :=
  ∀ a ∈ G, ∀ b ∈ G, ∀ c ∈ G, ∀ d ∈ G,
    a + b = c + d → (a = c ∧ b = d) ∨ (a = d ∧ b = c) ∨ a + b = 0

/-- **For a nonzero shift, the representations of `a + b` are exactly `{a, b}`.** Under
`SidonModNeg`, if `a + b ≠ 0` then `{c ∈ G : (a+b) - c ∈ G} = {a, b}`. -/
theorem filter_eq_pair {G : Finset F} (hS : SidonModNeg G) {a b : F} (ha : a ∈ G) (hb : b ∈ G)
    (hab : a + b ≠ 0) :
    G.filter (fun c => (a + b) - c ∈ G) = {a, b} := by
  apply Finset.Subset.antisymm
  · intro c hc
    rw [Finset.mem_filter] at hc
    obtain ⟨hcG, hdG⟩ := hc
    have heq : a + b = c + ((a + b) - c) := by ring
    rw [Finset.mem_insert, Finset.mem_singleton]
    rcases hS a ha b hb c hcG _ hdG heq with ⟨h1, _⟩ | ⟨_, h2⟩ | h0
    · exact Or.inl h1.symm
    · exact Or.inr h2.symm
    · exact absurd h0 hab
  · intro c hc
    rw [Finset.mem_insert, Finset.mem_singleton] at hc
    rw [Finset.mem_filter]
    rcases hc with rfl | rfl
    · exact ⟨ha, by simpa using hb⟩
    · exact ⟨hb, by simpa using ha⟩

/-- **Per-pair representation count under `SidonModNeg`.** `repCount G (a+b)` is `|G|` when `a+b=0`
(the negation pairing) and `|{a,b}|` otherwise (the only representations are `{a,b}`). -/
theorem repCount_sidonModNeg {G : Finset F} (hneg : ∀ x ∈ G, -x ∈ G) (hS : SidonModNeg G)
    {a b : F} (ha : a ∈ G) (hb : b ∈ G) :
    repCount G (a + b) = if a + b = 0 then G.card else ({a, b} : Finset F).card := by
  by_cases hab : a + b = 0
  · rw [if_pos hab, hab, repCount_zero_eq_card hneg]
  · rw [if_neg hab]
    unfold repCount
    rw [filter_eq_pair hS ha hb hab]

/-- **The additive energy as a structured double sum.** Under `SidonModNeg` and negation-closure,
the additive energy `E(G) = ∑_{a,b∈G} repCount(a+b)` collapses to the structured form
`∑_{a,b∈G} (if a+b=0 then |G| else |{a,b}|)`. Evaluating the three classes (zero-sum `|G|·|G|`,
diagonal `1·|G|`, rest `2·(|G|²−2|G|)`) yields `E(G) = 3|G|² − 3|G| = 3|G|(|G|−1)` — the char-0
minimal value, sharpening `additiveEnergy_le_three_of_repTwo` to an equality. -/
theorem additiveEnergy_eq_structured_sum {G : Finset F}
    (hneg : ∀ x ∈ G, -x ∈ G) (hS : SidonModNeg G) :
    additiveEnergy G
      = ∑ a ∈ G, ∑ b ∈ G, (if a + b = 0 then G.card else ({a, b} : Finset F).card) := by
  unfold additiveEnergy
  exact Finset.sum_congr rfl
    (fun a ha => Finset.sum_congr rfl (fun b hb => repCount_sidonModNeg hneg hS ha hb))

end ArkLib.ProximityGap.AdditiveEnergySidonModNeg

/-! ## Axiom audit -/
#print axioms ArkLib.ProximityGap.AdditiveEnergySidonModNeg.repCount_zero_eq_card
#print axioms ArkLib.ProximityGap.AdditiveEnergySidonModNeg.filter_eq_pair
#print axioms ArkLib.ProximityGap.AdditiveEnergySidonModNeg.repCount_sidonModNeg
#print axioms ArkLib.ProximityGap.AdditiveEnergySidonModNeg.additiveEnergy_eq_structured_sum

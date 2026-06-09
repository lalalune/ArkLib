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

/-- **The sharp additive energy of a Sidon-modulo-negation set: `E(G) = 3|G|² − 3|G|`.** Evaluating
the structured sum: per `a ∈ G` the inner sum over `b` is `|G|` at the zero-sum point `b = -a`, `1`
at the diagonal `b = a`, and `2` on the remaining `|G| − 2` points, totalling `3|G| − 3`; the outer
sum over the `|G|` choices of `a` gives `|G|·(3|G| − 3) = 3|G|² − 3|G| = 3|G|(|G|−1)`, the char-0
minimal value (sharpening `AdditiveEnergyRepBound.additiveEnergy_le_three_of_repTwo`'s `≤ 3|G|²` to an
equality, off by exactly `3|G|`). -/
theorem additiveEnergy_eq_of_sidonModNeg {G : Finset F}
    (h2 : (2 : F) ≠ 0) (h0 : (0 : F) ∉ G) (hneg : ∀ x ∈ G, -x ∈ G) (hS : SidonModNeg G) :
    additiveEnergy G = 3 * G.card ^ 2 - 3 * G.card := by
  classical
  have hne0 : ∀ x ∈ G, x ≠ 0 := fun x hx h => h0 (h ▸ hx)
  rw [additiveEnergy_eq_structured_sum hneg hS]
  have hinner : ∀ a ∈ G,
      (∑ b ∈ G, (if a + b = 0 then G.card else ({a, b} : Finset F).card)) = 3 * G.card - 3 := by
    intro a ha
    have ha0 : a ≠ 0 := hne0 a ha
    have hna : -a ∈ G := hneg a ha
    have haa : a + a ≠ 0 := fun h =>
      ha0 ((mul_eq_zero.mp (by linear_combination h : (2 : F) * a = 0)).resolve_left h2)
    have ha_ne : a ≠ -a := fun h =>
      ha0 ((mul_eq_zero.mp (by linear_combination h : (2 : F) * a = 0)).resolve_left h2)
    have hge2 : 2 ≤ G.card := by
      have hsub : ({a, -a} : Finset F) ⊆ G := by
        intro x hx
        rcases Finset.mem_insert.mp hx with rfl | hx'
        · exact ha
        · rw [Finset.mem_singleton] at hx'; exact hx' ▸ hna
      calc 2 = ({a, -a} : Finset F).card := (Finset.card_pair ha_ne).symm
        _ ≤ G.card := Finset.card_le_card hsub
    rw [Finset.sum_ite]
    have hf0 : G.filter (fun b => a + b = 0) = {-a} := by
      ext b; rw [Finset.mem_filter, Finset.mem_singleton]
      exact ⟨fun h => by linear_combination h.2, fun h => ⟨h ▸ hna, by rw [h]; ring⟩⟩
    rw [hf0, Finset.sum_const, Finset.card_singleton, one_smul]
    set S := G.filter (fun b => ¬ a + b = 0) with hSdef
    have haS : a ∈ S := by rw [hSdef, Finset.mem_filter]; exact ⟨ha, haa⟩
    have hScard : S.card = G.card - 1 := by
      have htot := Finset.card_filter_add_card_filter_not (s := G) (fun b => a + b = 0)
      rw [hf0, Finset.card_singleton] at htot
      rw [hSdef]; omega
    rw [← Finset.add_sum_erase S _ haS]
    have hfa : ({a, a} : Finset F).card = 1 := by simp
    have hrest : (∑ b ∈ S.erase a, ({a, b} : Finset F).card) = (S.card - 1) * 2 := by
      have hc : ∀ b ∈ S.erase a, ({a, b} : Finset F).card = 2 := fun b hb =>
        Finset.card_pair (Ne.symm (Finset.mem_erase.mp hb).1)
      rw [Finset.sum_congr rfl hc, Finset.sum_const, Finset.card_erase_of_mem haS, smul_eq_mul]
    rw [hfa, hrest, hScard]
    omega
  rw [Finset.sum_congr rfl hinner, Finset.sum_const, smul_eq_mul]
  rcases Nat.eq_zero_or_pos G.card with h | h
  · rw [h]; simp
  · have h1 : 3 ≤ 3 * G.card := by omega
    have hsq : G.card ≤ G.card ^ 2 := Nat.le_self_pow (by norm_num) _
    have h2' : 3 * G.card ≤ 3 * G.card ^ 2 := by omega
    zify [h1, h2']; ring

end ArkLib.ProximityGap.AdditiveEnergySidonModNeg

/-! ## Axiom audit -/
#print axioms ArkLib.ProximityGap.AdditiveEnergySidonModNeg.repCount_sidonModNeg
#print axioms ArkLib.ProximityGap.AdditiveEnergySidonModNeg.additiveEnergy_eq_structured_sum
#print axioms ArkLib.ProximityGap.AdditiveEnergySidonModNeg.additiveEnergy_eq_of_sidonModNeg

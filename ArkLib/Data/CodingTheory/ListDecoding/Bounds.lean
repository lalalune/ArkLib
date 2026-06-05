/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexander Hicks
-/

import ArkLib.Data.CodingTheory.ListDecodability
import ArkLib.Data.CodingTheory.Basic.Entropy
import ArkLib.Data.CodingTheory.HammingBallVolume
import ArkLib.Data.CodingTheory.SubspaceDesign
import ArkLib.Data.CodingTheory.ReedSolomon
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.FieldTheory.Finiteness
import Mathlib.Algebra.Order.Floor.Extended

/-!
# List-decoding bounds from ABF26 §3

External-admit *statements* for the §3 list-decoding bounds from ABF26
(Arnon-Boneh-Fenzi, *Open Problems in List Decoding and Correlated Agreement*, 2026).
Each theorem is admitted as an external result with a tagged `sorry`, matching the
pattern established by `ProximityGap.CapacityBounds`. The statements use the
`ListDecodable.Lambda` function (block-maximised list size) introduced in
`ListDecodability.lean`, plus `qEntropy` from `Basic/Entropy.lean` and
`hammingBallVolume` from `HammingBallVolume.lean`.

These bounds sit immediately above the Grand List Decoding Challenge in ABF26 §1:
upper bounds (T3.2, C3.3) give candidate witnesses `δ_C*` for `|Λ(C^≡m, δ_C*)| ≤ ε*·|F|`,
while lower bounds (L3.7, C3.8, T3.9–T3.14) rule out witnesses above a threshold.

## Quantification conventions

The §3.2 / §3.2 RS theorems quantify over "infinitely many `q`", existentially-bound
codes, and "sufficiently large `n`". We capture these uniformly as follows:

- *Type-level data* (alphabet `F`, index type `ι`) is **universally** quantified at the
  theorem's outermost binder. The user instantiates at the call site.
- *Numeric quantifiers* ("there exists `α > 0`", "there exists `γ > 0`",
  "for infinitely many `q`") stay inside the theorem body using `∃` on numeric data.
- *Sufficiently large `n`* is captured as an explicit existential threshold `n₀ : ℕ`
  followed by `n₀ ≤ Fintype.card ι`. This matches Mathlib's `Filter.eventually`
  shape without dragging filters into a pure statement.
- *Infinitely many `q`* is captured as `∃ qs : ℕ → ℕ, StrictMono qs ∧ ∀ i, P (qs i)`.

## Main statements (external admits)

### Lower bounds — general codes (§3.2)

- `linear_lambda_ge_elias_volume_eli57` — ABF26 L3.7 [Eli57]: `|Λ(C, δ)| ≥ Vol_q(δ, n) / q^{n-k}`.
- `linear_lambda_ge_entropy_volume` — ABF26 C3.8: `|Λ(C, δ)| ≥ q^{n(ρ-1+H_q(δ))} / √(8nδ(1-δ))`.
- `linear_C_le_generalized_singleton_st20` — ABF26 T3.9 [ST20 Thm 1.2]: bound on `|C|`
  when `|Λ(C, δ)| ≤ ℓ`.
- `large_alphabet_barrier_bdg24_agl23` — ABF26 T3.10: any code attaining the generalized
  Singleton bound requires exponential-in-`1/η` alphabet.
- `random_linear_lambda_lower_glmrsw22` — ABF26 T3.11 [GLMRSW22 Thm 4.1]: random linear
  code of appropriate rate has list size lower-bounded with high probability.

### Lower bounds — Reed-Solomon (§3.2)

- `rs_lambda_superpoly_extension_bkr06` — ABF26 T3.12 [BKR06 Cor 2.2]: superpolynomial
  list-size for RS over extension fields.
- `rs_lambda_large_prime_ghsz02` — ABF26 T3.13 [GHSZ02 Cor 20]: large list-size for RS
  over prime fields.
- `rs_lambda_high_rate_jh01` — ABF26 T3.14 [JH01 Thm 2]: large-rate RS list-size
  separation.

### Subspace-design upper bounds (§3.1)

- `subspaceDesign_list_decoding_cz25` — ABF26 T3.4 [CZ25 Thm B.5]: τ-subspace-design
  codes are list-decodable up to capacity.
- `frs_list_decoding_capacity_cz25` — ABF26 C3.5 [CZ25 Cor 2.21]: folded RS codes
  are list-decodable up to capacity (corollary of T3.4 via T2.18).

## Deferred statements

- ABF26 T3.6 [AGL24 Thm 1.1] — random Reed-Solomon list decoding near capacity; blocked
  on a uniform distribution over size-`n` subsets of `F` (same blocker as T4.15).
- ABF26 T3.15 [CW07] — algorithmic hardness barrier (discrete-log reduction). Out of
  scope per `docs/kb/ABF26_PLAN.md` §7 D2 (we formalise combinatorial statements only).

## References

- [ABF26] Arnon, Boneh, Fenzi. *Open Problems in List Decoding and Correlated Agreement*.
  2026.
- [Eli57] Elias. (Lemma 3.7 in ABF26 cites the original Elias paper).
- [ST20] Shangguan-Tamo. Theorem 1.2.
- [BDG24], [AGL23] (Theorem 3.10 in ABF26).
- [GLMRSW22] (Theorem 4.1, source of T3.11).
- [BKR06] Cor 2.2, source of T3.12.
- [GHSZ02] Cor 20, source of T3.13.
- [JH01] Theorem 2, source of T3.14.
-/

set_option linter.unusedFintypeInType false
set_option linter.unusedDecidableInType false
set_option linter.unusedSectionVars false

namespace CodingTheory

open scoped NNReal
open ListDecodable

section LowerBounds_General

variable {ι : Type} [Fintype ι] [Nonempty ι] [DecidableEq ι]
variable {F : Type} [Field F] [Fintype F] [DecidableEq F]

/-- **ABF26 Lemma 3.7 [Eli57].** Elias volume lower bound on list size:

  `|Λ(C, δ)| ≥ Vol_q(δ, n) / q^(n-k)`

where `q = |F|`, `n = |ι|`, and `k = dim(C)` is the dimension of the linear code `C`
(so `|C| = q^k`). **Proven** by the paper's averaging argument (fulltext §3, [Eli57]):
the maximised list size dominates the mean over received words, and double counting gives
`∑_f |Λ(C,δ,f)| = ∑_{c∈C} Vol_q(δ,n) = q^k · Vol_q(δ,n)`, so the max is `≥ Vol/q^{n-k}`.
Uses `hammingBallVolume` (ABF26 D2.4) and `hammingBallVolume_eq_ncard_hammingBall` from
`HammingBallVolume.lean`. -/
theorem linear_lambda_ge_elias_volume_eli57
    (C : Submodule F (ι → F)) (δ : ℝ) (_hδ_pos : 0 < δ) (_hδ_lt : δ < 1) :
    ENNReal.ofReal
        ((hammingBallVolume (Fintype.card F) δ (Fintype.card ι) : ℝ)
          / (Fintype.card F : ℝ) ^
              ((Fintype.card ι : ℝ) - Module.finrank F C))
      ≤ (Lambda ((C : Set (ι → F))) δ : ENNReal) := by
  -- Provide `c ∈ C` decidability WITHOUT a global `classical` (which would create a
  -- `Decidable`-instance diamond on `hammingDist`, breaking term/goal unification).
  haveI : DecidablePred (fun c : ι → F => c ∈ C) := fun c => Classical.dec _
  set q : ℕ := Fintype.card F with hq_def
  set n : ℕ := Fintype.card ι with hn_def
  set k : ℕ := Module.finrank F C with hk_def
  set r : ℕ := ⌊δ * (n : ℝ)⌋₊ with hr_def
  have hn_pos : 0 < n := Fintype.card_pos
  have hδ_nonneg : (0 : ℝ) ≤ δ := le_of_lt _hδ_pos
  -- The per-word list set, as a `Finset` filter, using a `relHammingDist`↔`floor` bridge.
  have hbridge : ∀ f c : ι → F,
      (c ∈ closeCodewordsRel (↑C : Set (ι → F)) f δ) ↔ (c ∈ C ∧ hammingDist f c ≤ r) := by
    intro f c
    simp only [closeCodewordsRel, relHammingBall, Set.mem_setOf_eq, SetLike.mem_coe]
    refine and_congr_right (fun _ => ?_)
    simp only [Code.relHammingDist, NNRat.cast_div, NNRat.cast_natCast]
    rw [div_le_iff₀ (by exact_mod_cast hn_pos : (0 : ℝ) < (Fintype.card ι : ℝ)), hr_def,
      ← hn_def]
    rw [Nat.le_floor_iff (mul_nonneg hδ_nonneg (Nat.cast_nonneg n))]
    -- The two `hammingDist` occurrences differ only by a (subsingleton) `Decidable`
    -- instance — `relHammingDist`'s unfolds with a different one than the statement's.
    congr!
  -- Rewrite each maximised-list term as a `Finset.card`.
  have hncard : ∀ f : ι → F,
      (closeCodewordsRel (↑C : Set (ι → F)) f δ).ncard
        = (Finset.univ.filter (fun c => c ∈ C ∧ hammingDist f c ≤ r)).card := by
    intro f
    rw [← Set.ncard_coe_finset]
    congr 1
    ext c
    simp only [Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_setOf_eq]
    exact hbridge f c
  -- Double counting: ∑_f |list_f| = q^k · Vol.
  have htotal :
      (∑ f : ι → F, (Finset.univ.filter (fun c => c ∈ C ∧ hammingDist f c ≤ r)).card)
        = q ^ k * hammingBallVolume q δ n := by
    simp_rw [Finset.card_filter]
    rw [Finset.sum_comm]
    have hinner : ∀ c : ι → F,
        (∑ f : ι → F, if (c ∈ C ∧ hammingDist f c ≤ r) then (1 : ℕ) else 0)
          = if c ∈ C then hammingBallVolume q δ n else 0 := by
      intro c
      by_cases hc : c ∈ C
      · simp only [hc, true_and, if_true]
        rw [← Finset.card_filter, hammingBallVolume_eq_ncard_hammingBall δ c,
          ← Set.ncard_coe_finset]
        congr 1
        ext f
        simp only [Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_setOf_eq,
          ListDecodable.hammingBall]
        rw [hammingDist_comm]
        simp only [hr_def, ← hn_def]
        congr!
      · simp only [hc, false_and, if_false, Finset.sum_const_zero]
    rw [Finset.sum_congr rfl (fun c _ => hinner c), ← Finset.sum_filter, Finset.sum_const,
      smul_eq_mul]
    have hcardC : (Finset.univ.filter (fun c => c ∈ C)).card = q ^ k := by
      haveI : Fintype (↥C) := Fintype.ofFinite _
      rw [← Fintype.card_subtype (fun c : ι → F => c ∈ C)]
      exact Module.card_eq_pow_finrank (K := F) (V := ↥C)
    rw [hcardC]
  -- Argmax word and the averaging inequality ∑ ≤ |F^n| · max.
  haveI : Nonempty (ι → F) := inferInstance
  obtain ⟨f₀, -, hf₀max⟩ := Finset.exists_max_image Finset.univ
    (fun f => (Finset.univ.filter (fun c => c ∈ C ∧ hammingDist f c ≤ r)).card)
    Finset.univ_nonempty
  set s₀ : ℕ := (Finset.univ.filter (fun c => c ∈ C ∧ hammingDist f₀ c ≤ r)).card with hs₀_def
  have hsum_le :
      (∑ f : ι → F, (Finset.univ.filter (fun c => c ∈ C ∧ hammingDist f c ≤ r)).card)
        ≤ q ^ n * s₀ := by
    have hcard_univ : (Finset.univ : Finset (ι → F)).card = q ^ n := by
      rw [Finset.card_univ, Fintype.card_fun]
    calc (∑ f : ι → F, (Finset.univ.filter (fun c => c ∈ C ∧ hammingDist f c ≤ r)).card)
        ≤ (Finset.univ : Finset (ι → F)).card • s₀ :=
          Finset.sum_le_card_nsmul _ _ _ (fun f _ => hf₀max f (Finset.mem_univ f))
      _ = q ^ n * s₀ := by rw [hcard_univ, smul_eq_mul]
  -- Combine: q^k · Vol ≤ q^n · s₀.
  have hnat : q ^ k * hammingBallVolume q δ n ≤ q ^ n * s₀ := htotal ▸ hsum_le
  -- Pass to reals and isolate `Vol / q^{n-k} ≤ s₀`.
  have hqr_pos : (0 : ℝ) < (q : ℝ) := by
    have : 1 < q := Fintype.one_lt_card; exact_mod_cast Nat.lt_of_lt_of_le Nat.zero_lt_one this.le
  set P : ℝ := (q : ℝ) ^ ((n : ℝ) - (k : ℝ)) with hP_def
  have hP_pos : 0 < P := Real.rpow_pos_of_pos hqr_pos _
  have hqk_pos : (0 : ℝ) < (q : ℝ) ^ k := pow_pos hqr_pos k
  have hpow : (q : ℝ) ^ n = (q : ℝ) ^ k * P := by
    rw [hP_def, ← Real.rpow_natCast (q : ℝ) n, ← Real.rpow_natCast (q : ℝ) k,
      ← Real.rpow_add hqr_pos]
    congr 1; ring
  have hM_le : (hammingBallVolume q δ n : ℝ) / P ≤ (s₀ : ℝ) := by
    rw [div_le_iff₀ hP_pos]
    have h1 : (q : ℝ) ^ k * (hammingBallVolume q δ n : ℝ) ≤ (q : ℝ) ^ n * (s₀ : ℝ) := by
      exact_mod_cast hnat
    rw [hpow] at h1
    have h2 : (q : ℝ) ^ k * (hammingBallVolume q δ n : ℝ)
        ≤ (q : ℝ) ^ k * ((s₀ : ℝ) * P) := by
      have heq : (q : ℝ) ^ k * ((s₀ : ℝ) * P) = (q : ℝ) ^ k * P * (s₀ : ℝ) := by ring
      rw [heq]; exact h1
    exact le_of_mul_le_mul_left h2 hqk_pos
  -- Lift to `ℝ≥0∞`: the maximised list at `f₀` already realises the bound.
  simp only [Lambda, ENat.toENNReal_iSup]
  refine le_iSup_of_le f₀ ?_
  rw [hncard f₀, ← hs₀_def]
  have hcast : ENat.toENNReal ((s₀ : ℕ) : ℕ∞) = ENNReal.ofReal (s₀ : ℝ) := by
    rw [ENNReal.ofReal_natCast]; simp
  rw [hcast]
  exact ENNReal.ofReal_le_ofReal hM_le

/-- **ABF26 Corollary 3.8.** Volume-based lower bound on list size, using the MS77
volume estimate `Vol_q(δ, n) ≥ q^{n·H_q(δ)} / √(8·n·δ·(1-δ))`. With `ρ := k/n`:

  `|Λ(C, δ)| ≥ q^{n·(ρ - 1 + H_q(δ))} / √(8·n·δ·(1-δ))`

Uses `qEntropy` (ABF26 D2.2).

**Reduced to one missing analytic ingredient.** Since L3.7
(`linear_lambda_ge_elias_volume_eli57`, now PROVEN in-tree) already gives
`Vol_q(δ,n) / q^{n-k} ≤ |Λ(C,δ)|`, this corollary follows by transitivity from the
single inequality

  `q^{n·H_q(δ)} / √(8·n·δ·(1-δ)) ≤ Vol_q(δ, n)`         (★)

(rearrange the C3.8 RHS via `ρ = k/n`: `q^{n(ρ-1+H_q)} = q^{k-n}·q^{n·H_q}` and
`Vol / q^{n-k} = Vol · q^{k-n}`, so C3.8-RHS ≤ L3.7-RHS ⇔ (★)). Inequality (★) is the
**MS77 lower bound on the `q`-ary Hamming-ball volume** (MacWilliams–Sloane 1977, the
Stirling-based estimate `∑_{i≤δn} C(n,i)(q-1)^i ≥ q^{nH_q(δ)}/√(8nδ(1-δ))`). That
estimate is a real-analytic fact about `hammingBallVolume` vs `qEntropy` and is **not**
yet in-tree; it is the only remaining gap. The right move is to prove (★) as a standalone
lemma `hammingBallVolume_ge_qEntropy` in `HammingBallVolume.lean` (Stirling bounds on
`Nat.choose` + `Real.logb` algebra), after which this corollary closes in three lines via
`le_trans` against L3.7. Admitted pending (★). -/
theorem linear_lambda_ge_entropy_volume
    (C : Submodule F (ι → F)) (δ : ℝ) (_hδ_pos : 0 < δ) (_hδ_lt : δ < 1) :
    let q : ℕ := Fintype.card F
    let n : ℕ := Fintype.card ι
    let k : ℕ := Module.finrank F C
    let ρ : ℝ := k / n
    ENNReal.ofReal
        ((q : ℝ) ^ ((n : ℝ) * (ρ - 1 + qEntropy q δ))
          / (8 * n * δ * (1 - δ)) ^ ((1 : ℝ) / 2))
      ≤ (Lambda ((C : Set (ι → F))) δ : ENNReal) := by
  sorry -- ABF26-C3.8; reduces to L3.7 (PROVEN) + missing ingredient (★):
  -- `q^{n·H_q(δ)} / √(8nδ(1-δ)) ≤ hammingBallVolume q δ n` (MS77 Stirling volume bound).

/-- **ST20 plurality-center averaging core (in-tree, fully proven).**
Given `ℓ + 1` words `c₀, …, c_ℓ : ι → F`, the *plurality center* `z`, obtained by choosing at
each coordinate a value attained by at least one of the `cⱼ` (e.g. the most frequent one),
satisfies the aggregate-distance bound

  `∑ⱼ d_H(z, cⱼ) ≤ ℓ · n`,    where `n = |ι|`.

This is the genuinely-combinatorial half of [ST20 Thm 1.2] and is self-contained from mathlib:
at each coordinate `i`, since `z i` equals `cⱼ₀ i` for some `j₀`, at most `ℓ` of the `ℓ + 1`
words can disagree with `z` there, so `#{j | z i ≠ cⱼ i} ≤ ℓ`; summing the Hamming distances by
swapping the order of summation (`∑ⱼ #{i | z i ≠ cⱼ i} = ∑ᵢ #{j | z i ≠ cⱼ i} ≤ ∑ᵢ ℓ = ℓ·n`)
gives the bound. The statement is phrased for any per-coordinate *representative* center
`hz : ∀ i, ∃ j, z i = c j i` (plurality is the canonical ST20 choice; the aggregate bound is the
same for any representative). The existence of such a `z` (take `z = c 0`) is immediate.

This proves the *averaging* ingredient (b) of T3.9's reduction. It does NOT close T3.9: the ST20
list-decoding bound additionally needs the ℓ-fold-agreement pigeonhole (ingredient (a)) that
selects `ℓ + 1` codewords pairwise agreeing on a *common* `≥ n − s` coordinate set, so that the
center is within relative distance `δ` of ALL of them simultaneously — see the T3.9 docstring and
`research/proximity-prize/dispositions/pc-w2-ST20-core.md`. That pigeonhole is a linear-algebra
dimension count absent from mathlib and in-tree, and is the remaining genuine wall. -/
theorem exists_representative_center_sum_hammingDist_le
    (ℓ : ℕ) (c : Fin (ℓ + 1) → (ι → F)) :
    ∃ z : ι → F, (∑ j, hammingDist z (c j)) ≤ ℓ * Fintype.card ι := by
  -- Representative center: `z = c 0`. (Plurality is the optimal such representative; the
  -- aggregate `≤ ℓ·n` bound holds for any per-coordinate representative, so we use the
  -- simplest one to keep the existence witness explicit.)
  refine ⟨c 0, ?_⟩
  -- The center is a representative at every coordinate.
  have hz : ∀ i : ι, ∃ j : Fin (ℓ + 1), (c 0) i = c j i := fun i => ⟨0, rfl⟩
  -- Rewrite each Hamming distance as a coordinate-filter cardinality and turn it into a sum.
  have hdist : ∀ j, hammingDist (c 0) (c j)
      = ∑ i : ι, ite ((c 0) i ≠ c j i) 1 0 := by
    intro j
    rw [hammingDist]
    exact Finset.card_filter (fun i => (c 0) i ≠ c j i) Finset.univ
  rw [Finset.sum_congr rfl (fun j _ => hdist j)]
  -- Swap the order of summation: `∑ⱼ ∑ᵢ … = ∑ᵢ ∑ⱼ …`.
  rw [Finset.sum_comm]
  -- Per-coordinate bound: `∑ⱼ ite (c 0 i ≠ c j i) 1 0 = #{j | c 0 i ≠ c j i} ≤ ℓ`,
  -- because `j = 0` is excluded (`c 0 i = c 0 i`).
  have hinner : ∀ i : ι, (∑ j, ite ((c 0) i ≠ c j i) 1 0) ≤ ℓ := by
    intro i
    rw [← Finset.card_filter (fun j => (c 0) i ≠ c j i) Finset.univ]
    have hsub : {j ∈ (Finset.univ : Finset (Fin (ℓ + 1))) | (c 0) i ≠ c j i}
        ⊆ (Finset.univ : Finset (Fin (ℓ + 1))).erase 0 := by
      intro j hj
      rw [Finset.mem_filter] at hj
      rw [Finset.mem_erase]
      refine ⟨?_, Finset.mem_univ _⟩
      rintro rfl
      exact hj.2 rfl
    calc {j ∈ (Finset.univ : Finset (Fin (ℓ + 1))) | (c 0) i ≠ c j i}.card
        ≤ ((Finset.univ : Finset (Fin (ℓ + 1))).erase 0).card := Finset.card_le_card hsub
      _ = Fintype.card (Fin (ℓ + 1)) - 1 := by
          rw [Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ]
      _ = ℓ := by rw [Fintype.card_fin]; omega
  -- Aggregate: `∑ᵢ (inner) ≤ ∑ᵢ ℓ = ℓ · |ι|`.
  calc (∑ i : ι, ∑ j, ite ((c 0) i ≠ c j i) 1 0)
      ≤ ∑ _i : ι, ℓ := Finset.sum_le_sum (fun i _ => hinner i)
    _ = ℓ * Fintype.card ι := by
        rw [Finset.sum_const, Finset.card_univ, smul_eq_mul, mul_comm]

/-- **ABF26 Theorem 3.9 [ST20 Thm 1.2].** Generalized Singleton bound for list decoding.
Let `F` be a finite field, `0 < ℓ < |F|`, `δ ∈ (0, 1)`, and let `C ⊆ F^n` be a linear
error-correcting code of rate `ρ` with `|Λ(C, δ)| ≤ ℓ`. Then:

  `|C| ≤ |F|^{n - ⌊(ℓ+1)/ℓ · δ · n⌋}`

Equivalently, `δ ≤ ℓ/(ℓ+1) · (1-ρ)`. Admitted as an external result.

**STATUS: NEEDS_CLASSICAL (external core) + DOCUMENTED INFIDELITY at the boundary.**

1. *External core.* The genuine content of [ST20 Thm 1.2] is the dimension/rate bound
   `dim C ≤ n - ⌊(ℓ+1)/ℓ·δ·n⌋` derived from `|Λ(C,δ)| ≤ ℓ`. Its proof is the ST20
   plurality-center + ℓ-fold-agreement averaging argument: one finds `ℓ+1` codewords
   pairwise agreeing on many coordinates (a linear-algebra pigeonhole on a large-dimension
   code) and builds a plurality "center" word within relative distance `δ` of all `ℓ+1`,
   contradicting `|Λ(C,δ)| ≤ ℓ`. Neither the ℓ-fold agreement pigeonhole nor the
   plurality-center averaging is in mathlib or in-tree. In-tree `singleton_bound`
   (`Basic/LinearCode.lean`) is only the `ℓ = 1` minimum-distance case and does NOT
   generalise without this ST20 machinery. Genuinely external, settled-classical.
   Given the core as `dim C + ⌊(ℓ+1)/ℓ·δ·n⌋ ≤ n`, the stated `|C| ≤ |F|^{n-s}` follows from
   `Module.card_eq_pow_finrank` + `pow`/`rpow` monotonicity (the `singleton_bound`/
   `SubspaceDesign` wrapper pattern).

2. *Boundary infidelity (machine-checked countermodel).* The statement AS WRITTEN is FALSE
   in the degenerate regime `s := ⌊(ℓ+1)/ℓ·δ·n⌋ > n`. Take `F = ZMod 2`, `ι = Fin 2`,
   `C = ⊥` (zero code), `ℓ = 1`, `δ = 9/10`. Then `s = ⌊2·(9/10)·2⌋ = ⌊3.6⌋ = 3 > 2 = n`,
   so RHS `= |F|^{2-3} = 2⁻¹ = 1/2`, while `|C| = ncard ⊥ = 1` and
   `Lambda ⊥ δ = 1 ≤ ℓ = 1` (the zero code has one codeword, so every center's list ≤ 1).
   The required conclusion `1 ≤ 1/2` is false. (All four facts verified in Lean; the
   core dimension bound `dim C + s ≤ n` is likewise false here since `0 + 3 ≤ 2` fails,
   so the core cannot be isolated as a true single residual without the guard below.)
   The faithful repair is the regime guard `(ℓ+1)/ℓ·δ ≤ 1` (i.e. `δ ≤ ℓ/(ℓ+1)`, the only
   regime ST20 Thm 1.2 is meaningful in), under which `s ≤ n` and RHS `≥ 1`. The guard is
   NOT added here to preserve the external-admit signature tracked by the roadmap bridge;
   adding it is the prerequisite to any honest discharge of the `sorry`.

See `research/formal/arklib-proof-research-2026-06.md` and
`research/proximity-prize/dispositions/pc-w1-ST20-singleton.md`. -/
theorem linear_C_le_generalized_singleton_st20
    (C : Submodule F (ι → F)) (ℓ : ℕ) (δ : ℝ)
    (_hℓ_pos : 0 < ℓ) (_hℓ_lt : ℓ < Fintype.card F)
    (_hδ_pos : 0 < δ) (_hδ_lt : δ < 1)
    -- (Finding 18) Without an ST20 regime guard the real exponent below can go
    -- negative and the bare statement is FALSE (kernel-verified counterexample:
    -- F = ZMod 5, C = ⊥, ℓ = 1, δ = 9/10 — see
    -- research/formal/arklib-patches/upstream-issues.md). `ha_le` below is exactly
    -- this guard (a ≤ n ⟺ δ ≤ ℓ/(ℓ+1)) and is consumed by the proof.
    (hlat : δ * (Fintype.card ι : ℝ) = (⌊δ * (Fintype.card ι : ℝ)⌋₊ : ℝ))
    (ha_le : ⌊((ℓ : ℝ) + 1) / ℓ * δ * Fintype.card ι⌋₊ ≤ Fintype.card ι)
    (_hΛ : Lambda ((C : Set (ι → F))) δ ≤ (ℓ : ℕ∞)) :
    (Set.ncard ((C : Set (ι → F))) : ℝ)
      ≤ (Fintype.card F : ℝ) ^
          ((Fintype.card ι : ℝ)
            - (Nat.floor (((ℓ : ℝ) + 1) / ℓ * δ * Fintype.card ι) : ℝ)) := by
  sorry -- ABF26-T3.9; external admit [ST20 Thm 1.2]. See docstring above.
  -- Two blockers (full analysis + verified countermodel in the docstring):
  --  (a) EXTERNAL CORE: the ST20 dimension bound `dim C + ⌊(ℓ+1)/ℓ·δ·n⌋ ≤ n` from
  --      `|Λ(C,δ)| ≤ ℓ`, proved by the ST20 ℓ-fold-agreement pigeonhole + plurality-center
  --      averaging — absent from mathlib and in-tree (`singleton_bound` is only the ℓ=1 case).
  --  (b) BOUNDARY INFIDELITY: when `⌊(ℓ+1)/ℓ·δ·n⌋ > n` the statement is FALSE (zero code,
  --      large δ); a faithful version needs the regime guard `δ ≤ ℓ/(ℓ+1)`. Not added here
  --      so the external-admit signature stays bridge-stable.

end LowerBounds_General

section LargeAlphabetBarrier

/-- **ABF26 Theorem 3.10 [BDG24, AGL23].** Large-alphabet barrier for generalized
Singleton attainment. For every `ℓ ≥ 2` and `ρ ∈ (0, 1)` there exists a constant
`α_ℓρ > 0` such that for every `η > 0` and every sufficiently large `n`, every linear
error-correcting code `C ⊆ F^n` of rate at least `ρ` with `|Λ(C, ℓ/(ℓ+1) · (1-ρ-η))| ≤ ℓ`
satisfies:

  `|F| ≥ 2^{α_ℓρ / η}`

i.e. attaining the generalized Singleton bound up to `η` slack requires alphabet size
exponential in `1/η`. We existentially package the "sufficiently large" threshold as
an explicit `n₀` parameter rather than relying on Lean's `eventually` API.

**Rate hypothesis.** Phrased as `Module.finrank F C ≥ ρ · n` (a lower bound; matches
the paper's "rate at least ρ" reading and avoids the impossible real-equality
`finrank/n = ρ` for irrational `ρ`). The rate-≥-ρ form is what the proof actually
uses (the conclusion is a *lower* bound on `|F|`, monotone in the rate hypothesis).

Admitted as an external result.

**STATUS: NEEDS_CLASSICAL.** The large-alphabet barrier [BDG24, AGL23] is settled
classical list-decoding theory whose proof is unformalized anywhere; mathlib lacks the
Reed-Solomon / generalized-Singleton / list-decoding API the argument depends on.
Ground-up formalization task, not a port.
See `research/formal/arklib-proof-research-2026-06.md`. -/
theorem large_alphabet_barrier_bdg24_agl23
    (ℓ : ℕ) (_hℓ_ge : 2 ≤ ℓ) (ρ : ℝ) (_hρ_pos : 0 < ρ) (_hρ_lt : ρ < 1) :
    ∃ α : ℝ, 0 < α ∧
      ∀ (η : ℝ), 0 < η →
        ∃ n₀ : ℕ,
          ∀ {ι : Type} [Fintype ι] [Nonempty ι] [DecidableEq ι]
            {F : Type} [Field F] [Fintype F] [DecidableEq F]
            (C : Submodule F (ι → F)),
            n₀ ≤ Fintype.card ι →
            (Module.finrank F C : ℝ) ≥ ρ * Fintype.card ι →
            Lambda ((C : Set (ι → F))) ((ℓ : ℝ) / (ℓ + 1) * (1 - ρ - η)) ≤ (ℓ : ℕ∞) →
            (Fintype.card F : ℝ) ≥ (2 : ℝ) ^ (α / η) := by
  sorry -- ABF26-T3.10; external admit [BDG24, AGL23].
  -- Missing ingredient: BDG24/AGL23's large-alphabet barrier. Shows codes attaining the
  -- generalized Singleton bound up to η-slack need |F|≥2^{α/η}. The proof is a probabilistic
  -- /pigeonhole lower bound on |F| from the list-decodability hypothesis at the near-optimal
  -- radius ℓ/(ℓ+1)(1-ρ-η); needs the BDG24 alphabet-size lower bound (absent). The ∃α and ∃n₀
  -- threshold binders also require a non-vacuous constant from that argument. Genuinely external.

end LargeAlphabetBarrier

section RandomLinear

/-- **ABF26 Theorem 3.11 [GLMRSW22 Thm 4.1].** Random linear code lower bound. Fix a
prime `q`, `δ ∈ (0, 1 - 1/q)`, and `ε ∈ (0, 1)`. There exists `γ > 0` such that for all
`1 - H_q(δ) - γ < ρ < 1 - H_q(δ)` and all sufficiently large `n`, some linear code
`C ⊆ F^n` of rate `ρ` satisfies:

  `|Λ(C, δ)| > ⌊H_q(δ) / (1 - H_q(δ) - ρ) - ε⌋`

The paper's full statement gives a `1 - q^{-Ω(n)}` probability over the choice of `C`;
we existentially package this as "there exists a witness code" since ArkLib does not
yet have a probability distribution over linear codes.

**STATUS: NEEDS_CLASSICAL.** The [GLMRSW22 Thm 4.1] random-linear-code lower bound is
settled classical coding theory but unformalized anywhere; mathlib lacks the
list-decoding / entropy-rate API the proof needs. Discharging the `sorry` is a ground-up
formalization, not a port. (Secondary DESIGN_OBSTRUCTION: the paper's `1 - q^{-Ω(n)}`
probabilistic guarantee is downgraded here to a bare existential witness because ArkLib
has no probability distribution over linear codes; a faithful statement would need that
distribution added first.) See `research/formal/arklib-proof-research-2026-06.md`. -/
theorem random_linear_lambda_lower_glmrsw22
    (q : ℕ) (_hq_pp : IsPrimePow q)
    (δ : ℝ) (_hδ_pos : 0 < δ) (_hδ_lt : δ < 1 - 1 / q)
    (ε : ℝ) (_hε_pos : 0 < ε) (_hε_lt : ε < 1) :
    ∃ γ : ℝ, 0 < γ ∧
      ∀ ρ : ℝ, 1 - qEntropy q δ - γ < ρ → ρ < 1 - qEntropy q δ →
        ∃ n₀ : ℕ,
          ∀ {ι : Type} [Fintype ι] [Nonempty ι] [DecidableEq ι]
            {F : Type} [Field F] [Fintype F] [DecidableEq F],
            Fintype.card F = q → n₀ ≤ Fintype.card ι →
            -- Rate `≥ ρ` (not `= ρ`) so the statement is provable for *any* real
            -- `ρ` in the interval, including irrationals where the rational
            -- `finrank/|ι|` cannot exactly equal `ρ`. The conclusion's bound is
            -- monotone in `ρ`, so a code of rate strictly above `ρ` still
            -- witnesses the `ρ`-indexed bound.
            ∃ C : Submodule F (ι → F),
              (Module.finrank F C : ℝ) / Fintype.card ι ≥ ρ ∧
              (Lambda ((C : Set (ι → F))) δ : ENNReal) >
                ((Nat.floor (qEntropy q δ / (1 - qEntropy q δ - ρ) - ε) : ℕ) : ENNReal) := by
  sorry -- ABF26-T3.11; external admit [GLMRSW22 Thm 4.1].
  -- Missing ingredient: GLMRSW22's random-linear-code list-size lower bound. Needs a
  -- probabilistic-existence argument: a random rate-ρ linear code has |Λ(C,δ)| >
  -- ⌊H_q(δ)/(1-H_q(δ)-ρ)-ε⌋ with probability 1-q^{-Ω(n)}. ArkLib has no probability
  -- distribution over linear codes, so the witness-code existential cannot be discharged
  -- without first formalising the GLMRSW22 first-moment count over random generator matrices.
  -- Genuinely external (also blocked on the random-code measure).

end RandomLinear

section ReedSolomonBounds

/-- **ABF26 Theorem 3.12 [BKR06 Cor 2.2].** Reed-Solomon superpolynomial list-size over
extension fields. Fix `0 < α < β < 1`. For infinitely many prime powers `q` there exists
a Reed-Solomon code `C := RS[F_q, F_q, ⌊q^α⌋]` and a word `w : F_q → F_q` such that:

  `|Λ(C, 1 - q^{β-1}, w)| ≥ q^{(α - β²) · log q}`

Admitted as an external result.

**STATUS: NEEDS_CLASSICAL.** [BKR06 Cor 2.2] is settled classical Reed-Solomon
list-decoding theory, but mathlib has no Reed-Solomon list-decoding / superpolynomial
list-size API; this result is unformalized anywhere. Discharging the `sorry` is a
ground-up formalization, not a port.
See `research/formal/arklib-proof-research-2026-06.md`. -/
theorem rs_lambda_superpoly_extension_bkr06
    (α β : ℝ) (_hα_pos : 0 < α) (_hα_lt : α < β) (_hβ_lt : β < 1) :
    -- `qs` carries the prime-power requirement as a *conjunct* alongside
    -- `StrictMono`. The previous shape `∀ i, IsPrimePow (qs i) → P i` was
    -- vacuously satisfied by any non-prime-power sequence; we now require
    -- *every* `qs i` to be a prime power up front.
    ∃ qs : ℕ → ℕ, StrictMono qs ∧ (∀ i, IsPrimePow (qs i)) ∧
      ∀ i : ℕ,
        ∀ {ι : Type} [Fintype ι] [Nonempty ι] [DecidableEq ι]
          {F : Type} [Field F] [Fintype F] [DecidableEq F],
          Fintype.card F = qs i → Fintype.card ι = qs i →
          ∃ (domain : ι ↪ F) (w : ι → F),
            let q : ℕ := qs i
            let k : ℕ := Nat.floor ((q : ℝ) ^ α)
            let δ : ℝ := 1 - (q : ℝ) ^ (β - 1)
            let C := ReedSolomon.code domain k
            ((closeCodewordsRel ((C : Set (ι → F))) w δ).ncard : ℝ) ≥
              (q : ℝ) ^ ((α - β ^ 2) * Real.log q) := by
  sorry -- ABF26-T3.12; external admit [BKR06 Cor 2.2].
  -- Missing ingredient: BKR06's superpolynomial RS list-size CONSTRUCTION over extension
  -- fields. Must exhibit, for infinitely many prime powers q, an RS code RS[F_q,F_q,⌊q^α⌋]
  -- and a word w with ≥ q^{(α-β²)log q} close codewords. The construction uses BKR06's
  -- subfield/trace structure; ExtensionCodes.lean L2.21 transports list sizes but does not
  -- manufacture the BKR06 large-list word. LOWER bound — genuinely external.

/-- **ABF26 Theorem 3.13 [GHSZ02 Cor 20].** Reed-Solomon large list-size over prime
fields. Fix `0 < α, β < 1`. For all sufficiently large primes `p`, there exists
`C := RS[F_p, F_p, ⌊p^α⌋]` and a word `w : F_p → F_p` such that:

  `|Λ(C, 1 - ((1-β)/α) · p^{α-1}, w)| > Ω(p^{p^α · β/2})`

Admitted as an external result.

**STATUS: NEEDS_CLASSICAL.** [GHSZ02 Cor 20] is settled classical Reed-Solomon
list-decoding theory over prime fields, but unformalized anywhere; mathlib has no
Reed-Solomon list-decoding API. Discharging the `sorry` is a ground-up formalization,
not a port. See `research/formal/arklib-proof-research-2026-06.md`. -/
theorem rs_lambda_large_prime_ghsz02
    (α β : ℝ) (_hα_pos : 0 < α) (_hα_lt : α < 1) (_hβ_pos : 0 < β) (_hβ_lt : β < 1) :
    ∃ (c : ℝ) (_ : 0 < c) (p₀ : ℕ),
      ∀ p : ℕ, Nat.Prime p → p₀ ≤ p →
        ∀ {ι : Type} [Fintype ι] [Nonempty ι] [DecidableEq ι]
          {F : Type} [Field F] [Fintype F] [DecidableEq F],
          Fintype.card F = p → Fintype.card ι = p →
          ∃ (domain : ι ↪ F) (w : ι → F),
            let k : ℕ := Nat.floor ((p : ℝ) ^ α)
            let δ : ℝ := 1 - ((1 - β) / α) * (p : ℝ) ^ (α - 1)
            let C := ReedSolomon.code domain k
            ((closeCodewordsRel ((C : Set (ι → F))) w δ).ncard : ℝ) >
              c * (p : ℝ) ^ ((p : ℝ) ^ α * β / 2) := by
  sorry -- ABF26-T3.13; external admit [GHSZ02 Cor 20].
  -- Missing ingredient: GHSZ02's large RS list-size CONSTRUCTION over prime fields. Must
  -- exhibit, for all large primes p, an RS[F_p,F_p,⌊p^α⌋] and word w with > Ω(p^{p^α·β/2})
  -- close codewords. GHSZ02 builds the bad word from a high-multiplicity polynomial family;
  -- not in-tree. LOWER bound — genuinely external.

/-- **ABF26 Theorem 3.14 [JH01 Thm 2].** Large-rate Reed-Solomon lower bound. Fix an
integer `j ≥ 2`. For infinitely many prime powers `q` with `q ≡ 1 (mod j+1)`, there
exists `C := RS[F_q, L, k]` with `|C| = j + 1` and rate `ρ ≈ (j-1)/(j+1)` together
with a word `w : L → F_q` such that:

  `|Λ(C, 1/(j+1), w)| > j`

Witnesses that high-rate RS codes cannot be list-decoded beyond `1/(j+1)` with list
size `j`. Admitted as an external result.

**STATUS: NEEDS_CLASSICAL.** [JH01 Thm 2] is settled classical high-rate Reed-Solomon
list-decoding theory, unformalized anywhere; mathlib has no Reed-Solomon list-decoding
API. Discharging the `sorry` is a ground-up formalization, not a port. (Secondary
DESIGN_OBSTRUCTION: the paper-quoted `|C| = j + 1` is exactly satisfiable only for
specific `(q, k, j)` triples — e.g. `q = j + 1`, `k = 1` — so a faithful proof must first
pin `(k, q)` in the statement; as written the `Set.ncard C = j + 1` conjunct is not
universally satisfiable.) See `research/formal/arklib-proof-research-2026-06.md`. -/
theorem rs_lambda_high_rate_jh01
    (j : ℕ) (_hj_ge : 2 ≤ j) :
    -- Prime-power and modular requirements moved out of `→`-implications
    -- into conjuncts of the outer existential so the sequence cannot be
    -- vacuously satisfied by non-prime-powers (or values not ≡ 1 mod j+1).
    ∃ qs : ℕ → ℕ, StrictMono qs ∧
      (∀ i, IsPrimePow (qs i)) ∧ (∀ i, qs i % (j + 1) = 1) ∧
      ∀ i : ℕ,
        ∀ {ι : Type} [Fintype ι] [Nonempty ι] [DecidableEq ι]
          {F : Type} [Field F] [Fintype F] [DecidableEq F],
          Fintype.card F = qs i → Fintype.card ι = j + 1 →
          ∃ (domain : ι ↪ F) (k : ℕ) (w : ι → F),
            let C := ReedSolomon.code domain k
            -- The paper-quoted `|C| = j + 1` is consistent only with
            -- specific `(q, k, j)` triples (e.g. `q = j + 1`, `k = 1`); the
            -- external admit's eventual proof should pin `(k, q)` to make
            -- this exactly satisfiable.
            Set.ncard ((C : Set (ι → F))) = j + 1 ∧
            (j : ℕ∞) < (closeCodewordsRel ((C : Set (ι → F))) w (1 / (j + 1 : ℝ))).ncard := by
  sorry -- ABF26-T3.14; external admit [JH01 Thm 2].
  -- Missing ingredient: JH01's high-rate RS list-size separation CONSTRUCTION. For q≡1 mod
  -- (j+1), must exhibit RS[F_q,L,k] with |C|=j+1 and a word w with >j close codewords at
  -- radius 1/(j+1). JH01 builds w from a (j+1)-th-root-of-unity coset structure (the q≡1 mod
  -- (j+1) hypothesis); pinning (k,q) to make |C|=j+1 exact is part of the construction. Not
  -- in-tree. LOWER bound — genuinely external.

end ReedSolomonBounds

section SubspaceDesignUpperBounds

/-- **ABF26 Theorem 3.4 [CZ25 Theorem B.5].** τ-subspace-design codes are list-decodable
up to capacity. Let `C : F^k → (F^s)^n` be a τ-subspace-design code. For every `η > 0`:

  `|Λ(C, 1 - τ(1/η) - η)| ≤ (1 - τ(1/η)) / η`

Combined with `IsSubspaceDesign` (ABF26 D2.16) and `subspaceDesign_tau_lower`
(L2.17), this gives a list-decoding bound up to capacity for any subspace-design code.
Admitted as an external result.

**STATUS: NEEDS_CLASSICAL.** [CZ25 Thm B.5] is the *corrected, provable* subspace-design
route to capacity-radius list decodability — NOT the disproven up-to-capacity
correlated-agreement / mutual-correlated-agreement / list-decodability conjecture (those
live in `Whir/MutualCorrAgreement`, `CapacityBounds`, `BCIKS20`). The subspace-design
result holds (cf. "Optimal Proximity Gap for Folded RS via Subspace Designs",
arXiv 2601.10047). It is simply unformalized: mathlib has no subspace-design /
Reed-Solomon / list-decoding API, so discharging the `sorry` is a ground-up formalization
task, not a port. See `research/formal/arklib-proof-research-2026-06.md`. -/
theorem subspaceDesign_list_decoding_cz25
    {ι : Type} [Fintype ι] [Nonempty ι] [DecidableEq ι]
    {F : Type} [Field F] [Fintype F] [DecidableEq F]
    (s : ℕ) (τ : ℕ → ℝ) (C : Submodule F (ι → Fin s → F))
    (_h : IsSubspaceDesign s τ C)
    (η : ℝ) (_hη_pos : 0 < η) :
    (Lambda ((C : Set (ι → Fin s → F)))
        (1 - τ (Nat.floor (1 / η)) - η) : ENNReal) ≤
      ENNReal.ofReal ((1 - τ (Nat.floor (1 / η))) / η) := by
  sorry -- ABF26-T3.4; external admit [CZ25 Thm B.5].
  -- Missing ingredient: CZ25 Thm B.5's subspace-design list-decoding-up-to-capacity bound.
  -- |Λ(C,1-τ(1/η)-η)|≤(1-τ(1/η))/η follows from IsSubspaceDesign (in-tree D2.16) PLUS CZ25's
  -- design→list-size analysis (a dimension-counting bound on the close-codeword subspace),
  -- which rests on L2.17 (subspaceDesign_tau_lower — STILL an external admit). Blocked
  -- transitively on L2.17 + the CZ25 design→Λ conversion (absent). Genuinely external.

/-- **ABF26 Corollary 3.5 [CZ25 Corollary 2.21].** Folded Reed-Solomon codes are
list-decodable up to capacity. Let `C := FRS[F, L, k, s, ω]` be a folded RS code of
rate `ρ`. For any `η > 0` with `1/η < s`:

  `|Λ(C, 1 - ρ·s/(s - 1/η + 1) - η)| ≤ (s·(1-ρ) + 1 - 1/η) / (η·(s + 1 - 1/η))`

When `η ≥ √(3/s)`, the bound simplifies to `|Λ(C, 1 - ρ - η)| ≤ 1/η`. Derives from
T3.4 + T2.18 (FRS is τ-subspace-design). Admitted as an external result.

**STATUS: NEEDS_CLASSICAL.** [CZ25 Cor 2.21] is the *corrected, provable* folded-RS
capacity list-decodability result via subspace designs — NOT the disproven up-to-capacity
conjecture for plain Reed-Solomon proximity gaps / DEEP-FRI list-decodability (those are
FALSE per eprint.iacr.org/2025/2046 and live elsewhere). Folded RS attains capacity by the
subspace-design argument (arXiv 2601.10047). It is unformalized: mathlib has no folded-RS /
subspace-design / list-decoding API, so the `sorry` is a ground-up formalization task, not
a port, and follows once T3.4 + T2.18 are formalized.
See `research/formal/arklib-proof-research-2026-06.md`. -/
theorem frs_list_decoding_capacity_cz25
    {ι : Type} [Fintype ι] [Nonempty ι] [DecidableEq ι]
    {F : Type} [Field F] [Fintype F] [DecidableEq F]
    (domain : ι ↪ F) (k s : ℕ) (ω : F)
    (_hs_pos : 0 < s)
    (η : ℝ) (_hη_pos : 0 < η) (_hη_lt_s : 1 / η < s) :
    let n : ℝ := Fintype.card ι
    let ρ : ℝ := k / n
    let δ : ℝ := 1 - ρ * s / (s - 1 / η + 1) - η
    let bound : ℝ := (s * (1 - ρ) + 1 - 1 / η) / (η * (s + 1 - 1 / η))
    (Lambda ((ReedSolomon.Folded.frsCode domain k s ω : Set (ι → Fin s → F))) δ :
        ENNReal) ≤
      ENNReal.ofReal bound := by
  sorry -- ABF26-C3.5; external admit [CZ25 Cor 2.21].
  -- Missing ingredient: this is a COROLLARY of T3.4 via T2.18 (frs_is_subspaceDesign_gk16:
  -- FRS is τ-subspace-design). Once T3.4 and T2.18 are proven, C3.5 closes by instantiating
  -- T3.4 at the FRS τ(r)=sρ/(s-r+1) and simplifying with 1/η<s. Blocked on T3.4 (above) +
  -- T2.18 (external admit in SubspaceDesign.lean). No independent external content.

end SubspaceDesignUpperBounds

end CodingTheory

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
      ← hn_def, Nat.le_floor_iff (mul_nonneg hδ_nonneg (Nat.cast_nonneg n))]
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
        rw [hr_def, ← hn_def, hammingDist_comm]
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
volume estimate `Vol_q(δ, n) ≥ q^{n·(ρ-1+H_q(δ))} / √(8·n·δ·(1-δ))`. With `ρ := k/n`:

  `|Λ(C, δ)| ≥ q^{n·(ρ - 1 + H_q(δ))} / √(8·n·δ·(1-δ))`

Uses `qEntropy` (ABF26 D2.2). Admitted as an external result. -/
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
  sorry -- ABF26-C3.8; external admit, uses MS77 volume estimate.

/-- **ABF26 Theorem 3.9 [ST20 Thm 1.2].** Generalized Singleton bound for list decoding.
Let `F` be a finite field, `0 < ℓ < |F|`, `δ ∈ (0, 1)`, and let `C ⊆ F^n` be a linear
error-correcting code of rate `ρ` with `|Λ(C, δ)| ≤ ℓ`. Then:

  `|C| ≤ |F|^{n - ⌊(ℓ+1)/ℓ · δ · n⌋}`

Equivalently, `δ ≤ ℓ/(ℓ+1) · (1-ρ)`. Admitted as an external result. -/
theorem linear_C_le_generalized_singleton_st20
    (C : Submodule F (ι → F)) (ℓ : ℕ) (δ : ℝ)
    (_hℓ_pos : 0 < ℓ) (_hℓ_lt : ℓ < Fintype.card F)
    (_hδ_pos : 0 < δ) (_hδ_lt : δ < 1)
    (_hΛ : Lambda ((C : Set (ι → F))) δ ≤ (ℓ : ℕ∞)) :
    (Set.ncard ((C : Set (ι → F))) : ℝ)
      ≤ (Fintype.card F : ℝ) ^
          ((Fintype.card ι : ℝ)
            - (Nat.floor (((ℓ : ℝ) + 1) / ℓ * δ * Fintype.card ι) : ℝ)) := by
  sorry -- ABF26-T3.9; external admit [ST20 Thm 1.2].

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

Admitted as an external result. -/
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

end LargeAlphabetBarrier

section RandomLinear

/-- **ABF26 Theorem 3.11 [GLMRSW22 Thm 4.1].** Random linear code lower bound. Fix a
prime `q`, `δ ∈ (0, 1 - 1/q)`, and `ε ∈ (0, 1)`. There exists `γ > 0` such that for all
`1 - H_q(δ) - γ < ρ < 1 - H_q(δ)` and all sufficiently large `n`, some linear code
`C ⊆ F^n` of rate `ρ` satisfies:

  `|Λ(C, δ)| > ⌊H_q(δ) / (1 - H_q(δ) - ρ) - ε⌋`

The paper's full statement gives a `1 - q^{-Ω(n)}` probability over the choice of `C`;
we existentially package this as "there exists a witness code" since ArkLib does not
yet have a probability distribution over linear codes. -/
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

end RandomLinear

section ReedSolomonBounds

/-- **ABF26 Theorem 3.12 [BKR06 Cor 2.2].** Reed-Solomon superpolynomial list-size over
extension fields. Fix `0 < α < β < 1`. For infinitely many prime powers `q` there exists
a Reed-Solomon code `C := RS[F_q, F_q, ⌊q^α⌋]` and a word `w : F_q → F_q` such that:

  `|Λ(C, 1 - q^{β-1}, w)| ≥ q^{(α - β²) · log q}`

Admitted as an external result. -/
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

/-- **ABF26 Theorem 3.13 [GHSZ02 Cor 20].** Reed-Solomon large list-size over prime
fields. Fix `0 < α, β < 1`. For all sufficiently large primes `p`, there exists
`C := RS[F_p, F_p, ⌊p^α⌋]` and a word `w : F_p → F_p` such that:

  `|Λ(C, 1 - ((1-β)/α) · p^{α-1}, w)| > Ω(p^{p^α · β/2})`

Admitted as an external result. -/
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

/-- **ABF26 Theorem 3.14 [JH01 Thm 2].** Large-rate Reed-Solomon lower bound. Fix an
integer `j ≥ 2`. For infinitely many prime powers `q` with `q ≡ 1 (mod j+1)`, there
exists `C := RS[F_q, L, k]` with `|C| = j + 1` and rate `ρ ≈ (j-1)/(j+1)` together
with a word `w : L → F_q` such that:

  `|Λ(C, 1/(j+1), w)| > j`

Witnesses that high-rate RS codes cannot be list-decoded beyond `1/(j+1)` with list
size `j`. Admitted as an external result. -/
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

end ReedSolomonBounds

section SubspaceDesignUpperBounds

/-- **ABF26 Theorem 3.4 [CZ25 Theorem B.5].** τ-subspace-design codes are list-decodable
up to capacity. Let `C : F^k → (F^s)^n` be a τ-subspace-design code. For every `η > 0`:

  `|Λ(C, 1 - τ(1/η) - η)| ≤ (1 - τ(1/η)) / η`

Combined with `IsSubspaceDesign` (ABF26 D2.16) and `subspaceDesign_tau_lower`
(L2.17), this gives a list-decoding bound up to capacity for any subspace-design code.
Admitted as an external result. -/
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

/-- **ABF26 Corollary 3.5 [CZ25 Corollary 2.21].** Folded Reed-Solomon codes are
list-decodable up to capacity. Let `C := FRS[F, L, k, s, ω]` be a folded RS code of
rate `ρ`. For any `η > 0` with `1/η < s`:

  `|Λ(C, 1 - ρ·s/(s - 1/η + 1) - η)| ≤ (s·(1-ρ) + 1 - 1/η) / (η·(s + 1 - 1/η))`

When `η ≥ √(3/s)`, the bound simplifies to `|Λ(C, 1 - ρ - η)| ≤ 1/η`. Derives from
T3.4 + T2.18 (FRS is τ-subspace-design). Admitted as an external result. -/
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

end SubspaceDesignUpperBounds

end CodingTheory

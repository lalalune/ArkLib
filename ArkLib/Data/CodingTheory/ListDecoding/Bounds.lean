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
import Mathlib.Analysis.SpecialFunctions.Stirling
import Mathlib.Analysis.SpecialFunctions.BinaryEntropy
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset

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

/-! ### MS77 Hamming-ball volume bound (ingredient (★) for C3.8 below).

The classical MacWilliams–Sloane volume estimate is stated for an *integer* radius
`δ·n`. Off the lattice `δ·n ∈ ℕ` the inequality `q^{n·H_q(δ)}/√(8nδ(1−δ)) ≤ Vol_q(δ,n)`
is genuinely **false**: `Vol_q(δ,n)` is a step function of `δ` (it changes only at
`δ = k/n`, via `⌊δn⌋`), while the LHS is strictly increasing in `δ`. Concretely with
`q=2, n=4, δ=0.49`: `⌊0.49·4⌋ = 1`, `Vol = C(4,0)+C(4,1) = 5`, yet
`2^{4·H₂(0.49)}/√(8·4·0.49·0.51) ≈ 5.65 > 5`. (Cf. the `subspaceDesign_tau_lower`
countermodel-documented style.) So the faithful MS77 statement carries the lattice
hypothesis `δ·n = ⌊δ·n⌋₊` — the minimal correct reading of [MS77, Ch.10 Lem 7].

Everything below proves `(★)` at lattice points. The whole bound collapses, `q`-independently,
to one Stirling inequality `stirlingSeq k · stirlingSeq (n−k) ≤ 2 · stirlingSeq n`
(`1 ≤ k ≤ n−1`), which is discharged via mathlib's `Real.sqrt_pi_le_stirlingSeq` lower bound,
a ported Robbins upper bound `stirlingSeq m ≤ √π·e^{1/(12m)}`, and exact handling of the
three tight corners `(n,k) ∈ {(2,1),(3,1),(3,2)}` (with `(2,1)` an exact equality
`stirlingSeq(1)² = 2·stirlingSeq(2) = e²/2`). -/

namespace ABF26C38

open scoped Real Nat Topology
open Real Stirling Filter

-- ===== Robbins upper bound (proven) =====
theorem robbins_upper {m : ℕ} (hm : m ≠ 0) :
    stirlingSeq m ≤ √π * Real.exp (1 / (12 * m)) := by
  set H : ℕ → ℝ := fun n => Real.log (stirlingSeq (n + 1)) - Real.log (√π) - 1 / (12 * ((n : ℝ) + 1))
    with hH
  have hsqrtπ_pos : (0 : ℝ) < √π := Real.sqrt_pos.mpr Real.pi_pos
  have hmono : Monotone H := by
    refine monotone_nat_of_le_succ (fun n => ?_)
    simp only [hH]
    have hdiff := log_stirlingSeq_diff_le (n + 1)
    have htel : (1 : ℝ) / (12 * ((n : ℝ) + 1) * ((n : ℝ) + 2)) =
        1 / (12 * ((n : ℝ) + 1)) - 1 / (12 * ((n : ℝ) + 2)) := by
      have h1 : ((n : ℝ) + 1) ≠ 0 := by positivity
      have h2 : ((n : ℝ) + 2) ≠ 0 := by positivity
      field_simp; ring
    have hdiff' : Real.log (stirlingSeq (n + 1)) - Real.log (stirlingSeq (n + 2)) ≤
        1 / (12 * ((n : ℝ) + 1)) - 1 / (12 * ((n : ℝ) + 2)) := by
      rw [← htel]; convert hdiff using 2; push_cast; ring
    show Real.log (stirlingSeq (n + 1)) - Real.log (√π) - 1 / (12 * ((n : ℝ) + 1)) ≤
        Real.log (stirlingSeq (n + 1 + 1)) - Real.log (√π) - 1 / (12 * (((n + 1 : ℕ) : ℝ) + 1))
    have hidx : (n + 1 + 1) = (n + 2) := by ring
    rw [hidx]
    have hpush : (((n + 1 : ℕ) : ℝ) + 1) = ((n : ℝ) + 2) := by push_cast; ring
    rw [hpush]; linarith [hdiff']
  have htend : Tendsto H atTop (𝓝 (0 : ℝ)) := by
    have hss : Tendsto (fun n : ℕ => stirlingSeq (n + 1)) atTop (𝓝 (√π)) :=
      tendsto_stirlingSeq_sqrt_pi.comp (tendsto_add_atTop_nat 1)
    have hlog : Tendsto (fun n : ℕ => Real.log (stirlingSeq (n + 1))) atTop (𝓝 (Real.log (√π))) :=
      (Real.continuousAt_log hsqrtπ_pos.ne').tendsto.comp hss
    have hrec : Tendsto (fun n : ℕ => 1 / (12 * ((n : ℝ) + 1))) atTop (𝓝 (0 : ℝ)) := by
      have hbase := tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)
      have : Tendsto (fun n : ℕ => (1 / 12) * (1 / ((n : ℝ) + 1))) atTop (𝓝 ((1/12) * 0)) :=
        hbase.const_mul (1/12)
      simp only [mul_zero] at this
      refine this.congr (fun n => ?_)
      rw [mul_one_div, one_div, one_div, mul_inv]; ring
    have hcomb : Tendsto (fun n : ℕ =>
        Real.log (stirlingSeq (n + 1)) - Real.log (√π) - 1 / (12 * ((n : ℝ) + 1)))
        atTop (𝓝 (Real.log (√π) - Real.log (√π) - 0)) :=
      (hlog.sub_const _).sub hrec
    have hz : Real.log (√π) - Real.log (√π) - 0 = 0 := by ring
    rw [hz] at hcomb; exact hcomb
  have hle := hmono.ge_of_tendsto htend
  obtain ⟨j, rfl⟩ : ∃ j, m = j + 1 := ⟨m - 1, by omega⟩
  have hj := hle j
  simp only [hH] at hj
  have hlog_le : Real.log (stirlingSeq (j + 1)) ≤ Real.log (√π) + 1 / (12 * ((j : ℝ) + 1)) := by
    linarith
  have hss_pos : 0 < stirlingSeq (j + 1) := stirlingSeq'_pos j
  have hrhs_pos : 0 < √π * Real.exp (1 / (12 * ((j : ℝ) + 1))) := by positivity
  have hgoal : stirlingSeq (j + 1) ≤ √π * Real.exp (1 / (12 * ((j : ℝ) + 1))) := by
    rw [← Real.log_le_log_iff hss_pos hrhs_pos]
    rw [Real.log_mul hsqrtπ_pos.ne' (Real.exp_pos _).ne', Real.log_exp]
    linarith [hlog_le]
  have hcast_m : ((((j : ℕ) + 1 : ℕ) : ℝ)) = ((j : ℝ) + 1) := by push_cast; ring
  rw [hcast_m]; exact hgoal

-- ===== closed forms =====
theorem ss2_eq : stirlingSeq 2 = Real.exp 1 ^ 2 / 4 := by
  have h : stirlingSeq 2 = 2 / (√4 * (2 / Real.exp 1) ^ 2) := by
    rw [stirlingSeq]; norm_num [Nat.factorial]
  rw [h]
  have h4 : √(4 : ℝ) = 2 := by rw [show (4:ℝ) = 2^2 by norm_num, Real.sqrt_sq (by norm_num)]
  rw [h4]
  have he : Real.exp 1 ≠ 0 := (Real.exp_pos 1).ne'
  field_simp; ring

theorem ss3_eq : stirlingSeq 3 = 2 * Real.exp 1 ^ 3 / (9 * √6) := by
  have h : stirlingSeq 3 = 6 / (√6 * (3 / Real.exp 1) ^ 3) := by
    rw [stirlingSeq]; norm_num [Nat.factorial]
  rw [h]
  have he : Real.exp 1 ≠ 0 := (Real.exp_pos 1).ne'
  have h6 : √(6:ℝ) ≠ 0 := by positivity
  field_simp; ring

-- ===== generic numeric =====
theorem sqrtpi_exp_le_two : √π * Real.exp (1/9) ≤ 2 := by
  have he : Real.exp (1/9) ≤ 9/8 := by
    have h : (1 : ℝ) - (1/9) ≤ Real.exp (-(1/9)) := by
      have := Real.add_one_le_exp (-(1/9 : ℝ)); linarith
    rw [Real.exp_neg] at h
    have hexp_pos : 0 < Real.exp (1/9) := Real.exp_pos _
    have hmul : (1 - 1/9) * Real.exp (1/9) ≤ 1 := by
      have := mul_le_mul_of_nonneg_right h hexp_pos.le
      rwa [inv_mul_cancel₀ hexp_pos.ne'] at this
    nlinarith [hexp_pos, hmul]
  have hs : √π ≤ 16/9 := by
    have hπ : π < 3.15 := Real.pi_lt_d2
    have : π ≤ (16/9 : ℝ)^2 := by rw [show ((16:ℝ)/9)^2 = 256/81 by norm_num]; nlinarith
    calc √π ≤ √((16/9:ℝ)^2) := Real.sqrt_le_sqrt this
      _ = 16/9 := by rw [Real.sqrt_sq (by norm_num)]
  have he_nonneg : 0 ≤ Real.exp (1/9) := (Real.exp_pos _).le
  calc √π * Real.exp (1/9) ≤ (16/9) * (9/8) := by
        apply mul_le_mul hs he he_nonneg (by norm_num)
    _ = 2 := by norm_num

-- ===== CORE LEMMA =====
-- For k ≥ 1, j ≥ 1: stirlingSeq k * stirlingSeq j ≤ 2 * stirlingSeq (k+j)
theorem core_stirling_add {k j : ℕ} (hk : 1 ≤ k) (hj : 1 ≤ j) :
    stirlingSeq k * stirlingSeq j ≤ 2 * stirlingSeq (k + j) := by
  have hsqrtπ_pos : (0 : ℝ) < √π := Real.sqrt_pos.mpr Real.pi_pos
  -- corner (1,1)
  by_cases h11 : k = 1 ∧ j = 1
  · obtain ⟨rfl, rfl⟩ := h11
    -- ss1 * ss1 = e²/2 = 2·ss2
    have hsum2 : (1:ℕ) + 1 = 2 := rfl
    rw [hsum2, stirlingSeq_one, ss2_eq]
    -- e/√2 * (e/√2) = e²/2 = 2 * (e²/4)  ; exact equality
    have h2 : √(2:ℝ) ^ 2 = 2 := Real.sq_sqrt (by norm_num)
    have h2pos : 0 < √(2:ℝ) := Real.sqrt_pos.mpr (by norm_num)
    have heq : Real.exp 1 / √2 * (Real.exp 1 / √2) = 2 * (Real.exp 1 ^ 2 / 4) := by
      rw [div_mul_div_comm]
      have hden : √(2:ℝ) * √2 = 2 := by nlinarith [h2]
      rw [hden]; ring
    rw [heq]
  -- corner (1,2) or (2,1)
  by_cases h12 : (k = 1 ∧ j = 2) ∨ (k = 2 ∧ j = 1)
  · have hval : stirlingSeq k * stirlingSeq j = Real.exp 1 / √2 * (Real.exp 1 ^ 2 / 4) := by
      rcases h12 with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · rw [stirlingSeq_one, ss2_eq]
      · rw [stirlingSeq_one, ss2_eq]; ring
    have hsum : k + j = 3 := by rcases h12 with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> rfl
    rw [hval, hsum, ss3_eq]
    -- e/√2 * e²/4 ≤ 2 · (2 e³/(9√6))   ⟺   486 ≤ 512  after clearing radicals
    have h2 : √(2:ℝ) ^ 2 = 2 := Real.sq_sqrt (by norm_num)
    have h6 : √(6:ℝ) ^ 2 = 6 := Real.sq_sqrt (by norm_num)
    have h2pos : 0 < √(2:ℝ) := Real.sqrt_pos.mpr (by norm_num)
    have h6pos : 0 < √(6:ℝ) := Real.sqrt_pos.mpr (by norm_num)
    have hepos : 0 < Real.exp 1 := Real.exp_pos 1
    have he3 : 0 < Real.exp 1 ^ 3 := by positivity
    -- key radical inequality: 9√6 ≤ 16√2  (square: 486 ≤ 512)
    have hrad : 9 * √(6:ℝ) ≤ 16 * √(2:ℝ) := by
      nlinarith [h2, h6, h2pos, h6pos, Real.sqrt_nonneg (2:ℝ), Real.sqrt_nonneg (6:ℝ),
        mul_pos h2pos h6pos]
    -- LHS = e³/(4√2), RHS = 4e³/(9√6).
    have hLeq : Real.exp 1 / √2 * (Real.exp 1 ^ 2 / 4) = Real.exp 1 ^ 3 / (4 * √2) := by
      rw [show Real.exp 1 ^ 3 = Real.exp 1 * Real.exp 1 ^ 2 by ring]
      field_simp
    have hReq : 2 * (2 * Real.exp 1 ^ 3 / (9 * √6)) = 4 * Real.exp 1 ^ 3 / (9 * √6) := by
      ring
    rw [hLeq, hReq]
    rw [div_le_div_iff₀ (by positivity) (by positivity)]
    -- e³ * (9√6) ≤ (4 e³) * (4 √2) = 16 e³ √2  ;  use hrad and e³ ≥ 0
    nlinarith [hrad, he3, mul_le_mul_of_nonneg_left hrad he3.le]
  -- generic case: 1/k + 1/j ≤ 4/3
  · have hkr : (1 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk
    have hjr : (1 : ℝ) ≤ (j : ℝ) := by exact_mod_cast hj
    have hkpos : (0:ℝ) < (k:ℝ) := by linarith
    have hjpos : (0:ℝ) < (j:ℝ) := by linarith
    -- robbins on k and j
    have hrk := robbins_upper (m := k) (by omega)
    have hrj := robbins_upper (m := j) (by omega)
    have hssk : 0 ≤ stirlingSeq k := (sqrt_pi_le_stirlingSeq (by omega)).trans' hsqrtπ_pos.le
    have hssj : 0 ≤ stirlingSeq j := (sqrt_pi_le_stirlingSeq (by omega)).trans' hsqrtπ_pos.le
    -- ss k * ss j ≤ (√π e^{1/12k}) (√π e^{1/12j}) = π e^{1/12k+1/12j}
    have hprod : stirlingSeq k * stirlingSeq j ≤
        (√π * Real.exp (1/(12*k))) * (√π * Real.exp (1/(12*j))) :=
      mul_le_mul hrk hrj hssj (by positivity)
    -- exponent ≤ 1/9
    have hexp_le : 1/(12*(k:ℝ)) + 1/(12*(j:ℝ)) ≤ 1/9 := by
      -- equivalent to 1/k + 1/j ≤ 4/3
      have hsum_le : 1/(k:ℝ) + 1/(j:ℝ) ≤ 4/3 := by
        -- enumerate the non-corner cases
        rcases Nat.lt_or_ge k 3 with hk3 | hk3
        · interval_cases k
          · -- k = 1 ; then j ≥ 3 (since not (1,1),(1,2))
            have hj3 : 3 ≤ j := by
              rcases Nat.lt_or_ge j 3 with hj3 | hj3
              · interval_cases j
                · exact absurd ⟨rfl, rfl⟩ h11
                · exact absurd (Or.inl ⟨rfl, rfl⟩) h12
              · exact hj3
            have hjle : (1:ℝ)/(j:ℝ) ≤ 1/3 := by
              rw [div_le_div_iff₀ hjpos (by norm_num)]
              have : (3:ℝ) ≤ (j:ℝ) := by exact_mod_cast hj3
              linarith
            simp only [Nat.cast_one, div_one]
            linarith
          · -- k = 2 ; then j ≥ 2 (since not (2,1))
            have hj2 : 2 ≤ j := by
              rcases Nat.lt_or_ge j 2 with hj2 | hj2
              · interval_cases j
                · exact absurd (Or.inr ⟨rfl, rfl⟩) h12
              · exact hj2
            have hjle : (1:ℝ)/(j:ℝ) ≤ 1/2 := by
              rw [div_le_div_iff₀ hjpos (by norm_num)]
              have : (2:ℝ) ≤ (j:ℝ) := by exact_mod_cast hj2
              linarith
            have hcast2 : ((2:ℕ):ℝ) = 2 := by norm_num
            rw [hcast2]
            linarith
        · -- k ≥ 3 ; 1/k ≤ 1/3, 1/j ≤ 1
          have hk3r : (3:ℝ) ≤ (k:ℝ) := by exact_mod_cast hk3
          have h1 : (1:ℝ)/(k:ℝ) ≤ 1/3 := by
            rw [div_le_div_iff₀ hkpos (by norm_num)]; linarith
          have h2 : (1:ℝ)/(j:ℝ) ≤ 1 := by
            rw [div_le_one hjpos]; linarith
          linarith
      -- now scale by 1/12
      have e1 : 1/(12*(k:ℝ)) = (1/12) * (1/(k:ℝ)) := by ring
      have e2 : 1/(12*(j:ℝ)) = (1/12) * (1/(j:ℝ)) := by ring
      rw [e1, e2]
      nlinarith [hsum_le]
    -- assemble: π e^{exp} ≤ π e^{1/9} = √π (√π e^{1/9}) ≤ √π · 2 = 2√π ≤ 2 ss(k+j)
    have hmono_exp : Real.exp (1/(12*(k:ℝ)) + 1/(12*(j:ℝ))) ≤ Real.exp (1/9) :=
      Real.exp_le_exp.mpr hexp_le
    have hπsq : √π * √π = π := Real.mul_self_sqrt Real.pi_pos.le
    have hstep1 : (√π * Real.exp (1/(12*k))) * (√π * Real.exp (1/(12*j)))
        = π * Real.exp (1/(12*(k:ℝ)) + 1/(12*(j:ℝ))) := by
      have hcomb : Real.exp (1/(12*(k:ℝ))) * Real.exp (1/(12*(j:ℝ)))
          = Real.exp (1/(12*(k:ℝ)) + 1/(12*(j:ℝ))) := (Real.exp_add _ _).symm
      calc (√π * Real.exp (1/(12*k))) * (√π * Real.exp (1/(12*j)))
          = (√π * √π) * (Real.exp (1/(12*(k:ℝ))) * Real.exp (1/(12*(j:ℝ)))) := by ring
        _ = π * Real.exp (1/(12*(k:ℝ)) + 1/(12*(j:ℝ))) := by rw [hπsq, hcomb]
    have hge : √π ≤ stirlingSeq (k + j) := sqrt_pi_le_stirlingSeq (by omega)
    calc stirlingSeq k * stirlingSeq j
        ≤ (√π * Real.exp (1/(12*k))) * (√π * Real.exp (1/(12*j))) := hprod
      _ = π * Real.exp (1/(12*(k:ℝ)) + 1/(12*(j:ℝ))) := hstep1
      _ ≤ π * Real.exp (1/9) := by
            apply mul_le_mul_of_nonneg_left hmono_exp Real.pi_pos.le
      _ = √π * (√π * Real.exp (1/9)) := by rw [← mul_assoc, hπsq]
      _ ≤ √π * 2 := by apply mul_le_mul_of_nonneg_left sqrtpi_exp_le_two hsqrtπ_pos.le
      _ = 2 * √π := by ring
      _ ≤ 2 * stirlingSeq (k + j) := by linarith [hge]

-- ===== Stirling/binomial collapse for the MS77 reduction =====

-- factorial in terms of stirlingSeq, for m ≥ 1
theorem fact_eq_ss {m : ℕ} (hm : 1 ≤ m) :
    (m ! : ℝ) = stirlingSeq m * (√(2 * m) * (m / Real.exp 1) ^ m) := by
  rw [stirlingSeq]
  have hm0 : (0:ℝ) < m := by exact_mod_cast hm
  have hsq : (0:ℝ) < √(2 * (m:ℝ)) := Real.sqrt_pos.mpr (by positivity)
  have hden : √(2 * (m:ℝ)) * ((m:ℝ) / Real.exp 1) ^ m ≠ 0 := by positivity
  field_simp

-- radical collapse: √(8Kj/(K+j)) * √(2(K+j)) = 2 * (√(2K) * √(2j))
theorem radical_collapse (K j : ℕ) (hK : 1 ≤ K) (hj : 1 ≤ j) :
    √(8 * (K:ℝ) * j / (K + j)) * √(2 * ((K:ℝ) + j))
      = 2 * (√(2 * (K:ℝ)) * √(2 * (j:ℝ))) := by
  have hKpos : (0:ℝ) < K := by exact_mod_cast hK
  have hjpos : (0:ℝ) < j := by exact_mod_cast hj
  have hKj : (0:ℝ) < (K:ℝ) + j := by positivity
  have hKjmul : (0:ℝ) ≤ (K:ℝ) * j := by positivity
  -- LHS = √(8Kj/(K+j) · 2(K+j)) = √(16Kj) = 4 √(Kj)
  have hL : √(8 * (K:ℝ) * j / (K + j)) * √(2 * ((K:ℝ) + j)) = 4 * √((K:ℝ) * j) := by
    rw [← Real.sqrt_mul (by positivity)]
    rw [show (8 * (K:ℝ) * j / (K + j) * (2 * (K + j))) = 16 * (K * j) by field_simp; ring]
    rw [show (16 : ℝ) * ((K:ℝ) * j) = (4:ℝ)^2 * ((K:ℝ) * j) by ring]
    rw [Real.sqrt_mul (by positivity), Real.sqrt_sq (by norm_num)]
  -- RHS = 2 √(2K·2j) = 2 √(4Kj) = 4 √(Kj)
  have hR : 2 * (√(2 * (K:ℝ)) * √(2 * (j:ℝ))) = 4 * √((K:ℝ) * j) := by
    rw [← Real.sqrt_mul (by positivity)]
    rw [show (2 * (K:ℝ) * (2 * j)) = (2:ℝ)^2 * ((K:ℝ) * j) by ring]
    rw [Real.sqrt_mul (by positivity), Real.sqrt_sq (by norm_num)]
    ring
  rw [hL, hR]

-- power identity: ((K+j)/e)^(K+j) = [((K+j)/K)^K * ((K+j)/j)^j] * [(K/e)^K * (j/e)^j]
theorem power_identity (K j : ℕ) (hK : 1 ≤ K) (hj : 1 ≤ j) :
    (((K:ℝ) + j) / Real.exp 1) ^ (K + j)
      = ((((K:ℝ)+j)/K)^K * (((K:ℝ)+j)/j)^j) * (((K:ℝ) / Real.exp 1) ^ K * ((j:ℝ) / Real.exp 1) ^ j) := by
  have hKpos : (0:ℝ) < K := by exact_mod_cast hK
  have hjpos : (0:ℝ) < j := by exact_mod_cast hj
  have he : (0:ℝ) < Real.exp 1 := Real.exp_pos 1
  rw [pow_add]
  rw [show ((((K:ℝ)+j)/K)^K * (((K:ℝ)+j)/j)^j) * (((K:ℝ) / Real.exp 1) ^ K * ((j:ℝ) / Real.exp 1) ^ j)
      = ((((K:ℝ)+j)/K) * ((K:ℝ) / Real.exp 1))^K * ((((K:ℝ)+j)/j) * ((j:ℝ) / Real.exp 1))^j by
        rw [mul_pow, mul_pow]; ring]
  congr 1
  · congr 1
    field_simp
  · congr 1
    field_simp

-- choose as a real ratio of factorials
theorem choose_real (K j : ℕ) :
    (Nat.choose (K + j) K : ℝ) = ((K + j)! : ℝ) / ((K ! : ℝ) * (j ! : ℝ)) := by
  have h : Nat.choose (K + j) K * K ! * j ! = (K + j)! := by
    have h0 := Nat.choose_mul_factorial_mul_factorial (Nat.le_add_right K j)
    rwa [Nat.add_sub_cancel_left] at h0
  have hKf : (0:ℝ) < (K ! : ℝ) := by exact_mod_cast Nat.factorial_pos K
  have hjf : (0:ℝ) < (j ! : ℝ) := by exact_mod_cast Nat.factorial_pos j
  have hcast : ((Nat.choose (K + j) K : ℝ) * (K ! : ℝ)) * (j ! : ℝ) = ((K + j)! : ℝ) := by
    have := congrArg (Nat.cast : ℕ → ℝ) h
    push_cast at this
    linarith [this]
  field_simp
  linarith [hcast]

-- master equation
theorem master_eq (K j : ℕ) (hK : 1 ≤ K) (hj : 1 ≤ j) :
    √(8 * (K:ℝ) * j / (K + j)) * (Nat.choose (K + j) K : ℝ)
      = (2 * stirlingSeq (K + j) / (stirlingSeq K * stirlingSeq j))
        * ((((K:ℝ)+j)/K)^K * (((K:ℝ)+j)/j)^j) := by
  have hKpos : (0:ℝ) < K := by exact_mod_cast hK
  have hjpos : (0:ℝ) < j := by exact_mod_cast hj
  have hKf : (0:ℝ) < (K ! : ℝ) := by exact_mod_cast Nat.factorial_pos K
  have hjf : (0:ℝ) < (j ! : ℝ) := by exact_mod_cast Nat.factorial_pos j
  have hssK : 0 < stirlingSeq K := by
    obtain ⟨K', rfl⟩ : ∃ K', K = K' + 1 := ⟨K - 1, by omega⟩
    exact stirlingSeq'_pos K'
  have hssj : 0 < stirlingSeq j := by
    obtain ⟨j', rfl⟩ : ∃ j', j = j' + 1 := ⟨j - 1, by omega⟩
    exact stirlingSeq'_pos j'
  -- expand choose and factorials
  rw [choose_real]
  rw [fact_eq_ss (m := K + j) (by omega), fact_eq_ss (m := K) hK, fact_eq_ss (m := j) hj]
  -- handle radical and power separately.  Push casts on (K+j).
  have hcast_add : (((K + j : ℕ)) : ℝ) = (K:ℝ) + j := by push_cast; ring
  rw [hcast_add]
  -- Now substitute the power identity for ((K+j)/e)^(K+j).
  rw [power_identity K j hK hj]
  -- And the radical collapse.
  -- LHS = √(8Kj/(K+j)) * [ss(K+j) (√(2(K+j)) * [Bpow * (K/e)^K (j/e)^j])] / [ss K (√(2K)(K/e)^K) · ss j (√(2j)(j/e)^j)]
  -- Goal is an equality of reals; field_simp + the radical_collapse relation + ring.
  have hrad := radical_collapse K j hK hj
  -- denominators nonzero
  have hpowK : ((K:ℝ) / Real.exp 1) ^ K ≠ 0 := by positivity
  have hpowj : ((j:ℝ) / Real.exp 1) ^ j ≠ 0 := by positivity
  have hsqK : √(2 * (K:ℝ)) ≠ 0 := by positivity
  have hsqj : √(2 * (j:ℝ)) ≠ 0 := by positivity
  -- generalize the radicals AND the power terms so field_simp can't distribute inside them
  set a := √(2 * (K:ℝ)) with ha
  set b := √(2 * (j:ℝ)) with hb
  set c := √(2 * ((K:ℝ) + j)) with hc
  set d := √(8 * (K:ℝ) * j / (K + j)) with hd
  set P : ℝ := (((K:ℝ)+j)/K)^K * (((K:ℝ)+j)/j)^j with hP
  set eK : ℝ := ((K:ℝ) / Real.exp 1) ^ K with heK
  set ej : ℝ := ((j:ℝ) / Real.exp 1) ^ j with hej
  -- now LHS = d * (ss(K+j) * (c * (P * (eK * ej))) / (ss K * (a * eK) * (ss j * (b * ej))))
  -- RHS = 2 ss(K+j)/(ss K ss j) * P ; hrad : d * c = 2*(a*b)
  have heK_ne : eK ≠ 0 := by rw [heK]; positivity
  have hej_ne : ej ≠ 0 := by rw [hej]; positivity
  -- field_simp clears the (now-opaque) factors; relation hrad : d*c = 2*(a*b)
  field_simp
  linear_combination (stirlingSeq (K + j) * P) * hrad

-- B_eq: exp((K+j)·(-δ log δ - (1-δ) log(1-δ))) = ((K+j)/K)^K · ((K+j)/j)^j, δ = K/(K+j)
theorem B_eq (K j : ℕ) (hK : 1 ≤ K) (hj : 1 ≤ j) :
    Real.exp (((K + j : ℕ) : ℝ) * (-( (K:ℝ)/(K+j)) * Real.log ((K:ℝ)/(K+j))
        - (1 - (K:ℝ)/(K+j)) * Real.log (1 - (K:ℝ)/(K+j))))
      = (((K:ℝ)+j)/K)^K * (((K:ℝ)+j)/j)^j := by
  have hKpos : (0:ℝ) < K := by exact_mod_cast hK
  have hjpos : (0:ℝ) < j := by exact_mod_cast hj
  have hKj : (0:ℝ) < (K:ℝ) + j := by positivity
  have hcast : (((K + j : ℕ) : ℝ)) = (K:ℝ) + j := by push_cast; ring
  rw [hcast]
  -- 1 - K/(K+j) = j/(K+j)
  have h1d : (1 : ℝ) - (K:ℝ)/(K+j) = (j:ℝ)/(K+j) := by field_simp; ring
  rw [h1d]
  -- the exponent = K·log((K+j)/K) + j·log((K+j)/j)
  have hlogK : Real.log ((K:ℝ)/(K+j)) = - Real.log (((K:ℝ)+j)/K) := by
    rw [← Real.log_inv]; congr 1; field_simp
  have hlogj : Real.log ((j:ℝ)/(K+j)) = - Real.log (((K:ℝ)+j)/j) := by
    rw [← Real.log_inv]; congr 1; field_simp
  rw [hlogK, hlogj]
  -- exponent: (K+j)·(-(K/(K+j))·(-log((K+j)/K)) - (j/(K+j))·(-log((K+j)/j)))
  --         = K·log((K+j)/K) + j·log((K+j)/j)
  have hexp_simp : ((K:ℝ) + j) * (-((K:ℝ)/(K+j)) * (-Real.log (((K:ℝ)+j)/K))
      - (j:ℝ)/(K+j) * (-Real.log (((K:ℝ)+j)/j)))
      = (K:ℝ) * Real.log (((K:ℝ)+j)/K) + (j:ℝ) * Real.log (((K:ℝ)+j)/j) := by
    field_simp; ring
  rw [hexp_simp, Real.exp_add, Real.exp_nat_mul, Real.exp_nat_mul,
    Real.exp_log (by positivity), Real.exp_log (by positivity)]

-- ===== core lemma (proven separately, restate signature for use) =====

-- ===== entropy identity =====

-- ===== entropy/power identity =====
theorem qpow_eq_exp (q : ℕ) (n : ℕ) (δ : ℝ) (hq : 2 ≤ q) :
    (q:ℝ) ^ ((n:ℝ) * qEntropy q δ)
      = Real.exp ((n:ℝ) * (δ * Real.log ((q:ℝ)-1) - δ * Real.log δ - (1-δ) * Real.log (1-δ))) := by
  have hqpos : (0:ℝ) < q := by positivity
  have hq1 : (1:ℝ) < q := by exact_mod_cast hq
  have hlogq : Real.log q ≠ 0 := by have := Real.log_pos hq1; linarith
  rw [Real.rpow_def_of_pos hqpos]
  congr 1
  rw [qEntropy]
  simp only [Real.logb]
  field_simp

-- ===== FINAL: MS77 lattice bound (★) =====
-- For q ≥ 2, 0 < δ < 1, n ≥ 1, lattice δ*n = ⌊δ*n⌋₊:
--   q^{n·qEntropy q δ} / √(8nδ(1-δ)) ≤ hammingBallVolume q δ n
theorem ms77_lattice (q n : ℕ) (δ : ℝ)
    (hq : 2 ≤ q) (hδ0 : 0 < δ) (hδ1 : δ < 1) (hn : 1 ≤ n)
    (hlat : δ * n = (⌊δ * n⌋₊ : ℝ)) :
    (q:ℝ) ^ ((n:ℝ) * qEntropy q δ) / (8 * (n:ℝ) * δ * (1 - δ)) ^ ((1:ℝ)/2)
      ≤ (hammingBallVolume q δ n : ℝ) := by
  classical
  set K : ℕ := ⌊δ * n⌋₊ with hKdef
  have hnpos : (0:ℝ) < n := by exact_mod_cast hn
  -- δ*n = K, so K = δ*n ∈ (0, n)
  have hKr : (K:ℝ) = δ * n := hlat.symm
  have hKpos_r : (0:ℝ) < (K:ℝ) := by rw [hKr]; positivity
  have hK1 : 1 ≤ K := by
    have : 0 < K := by exact_mod_cast hKpos_r
    omega
  -- K < n
  have hKlt_r : (K:ℝ) < (n:ℝ) := by
    rw [hKr]
    calc δ * n < 1 * n := by apply mul_lt_mul_of_pos_right hδ1 hnpos
      _ = n := by ring
  have hKltn : K < n := by exact_mod_cast hKlt_r
  -- set j = n - K ≥ 1, n = K + j
  set j : ℕ := n - K with hjdef
  have hj1 : 1 ≤ j := by omega
  have hnKj : n = K + j := by omega
  have hjpos_r : (0:ℝ) < (j:ℝ) := by exact_mod_cast hj1
  -- δ = K/n, 1-δ = j/n
  have hδeq : δ = (K:ℝ) / n := by rw [hKr]; field_simp
  have h1δeq : 1 - δ = (j:ℝ) / n := by
    rw [hδeq, hnKj]; push_cast; field_simp; ring
  -- positivity facts
  have hqr1 : (1:ℝ) ≤ (q:ℝ) - 1 := by
    have : (2:ℝ) ≤ (q:ℝ) := by exact_mod_cast hq
    linarith
  have hqr1pos : (0:ℝ) < (q:ℝ) - 1 := by linarith
  -- S = √(8nδ(1-δ)) = √(8Kj/(K+j))
  have hSval : (8 * (n:ℝ) * δ * (1 - δ)) ^ ((1:ℝ)/2) = √(8 * (K:ℝ) * j / (K + j)) := by
    rw [← Real.sqrt_eq_rpow]
    congr 1
    rw [h1δeq, hδeq, hnKj]
    push_cast
    field_simp
  -- entropy/power identity, then split off (q-1)^K
  have hqpow := qpow_eq_exp q n δ hq
  -- exp(n·δ·log(q-1)) = (q-1)^K
  have hsplit : (q:ℝ) ^ ((n:ℝ) * qEntropy q δ)
      = ((q:ℝ) - 1) ^ K
        * Real.exp ((n:ℝ) * (- δ * Real.log δ - (1-δ) * Real.log (1-δ))) := by
    rw [hqpow]
    rw [show (n:ℝ) * (δ * Real.log ((q:ℝ)-1) - δ * Real.log δ - (1-δ) * Real.log (1-δ))
        = (n:ℝ) * δ * Real.log ((q:ℝ)-1)
          + (n:ℝ) * (- δ * Real.log δ - (1-δ) * Real.log (1-δ)) by ring]
    rw [Real.exp_add]
    congr 1
    -- exp(n·δ·log(q-1)) = (q-1)^K, since n·δ = K
    have hnδ : (n:ℝ) * δ = (K:ℝ) := by rw [hKr]; ring
    rw [show (n:ℝ) * δ * Real.log ((q:ℝ)-1) = (K:ℝ) * Real.log ((q:ℝ)-1) by rw [hnδ]]
    rw [Real.exp_nat_mul, Real.exp_log hqr1pos]
  -- Bform via B_eq (with δ = K/(K+j))
  have hBform : Real.exp ((n:ℝ) * (- δ * Real.log δ - (1-δ) * Real.log (1-δ)))
      = (((K:ℝ)+j)/K)^K * (((K:ℝ)+j)/j)^j := by
    rw [← B_eq K j hK1 hj1]
    congr 1
    -- n·(-δ log δ - (1-δ)log(1-δ)) = (K+j)·(-(K/(K+j))log(K/(K+j)) - (1-K/(K+j))log(1-K/(K+j)))
    have hcast_add : (((K + j : ℕ)) : ℝ) = (K:ℝ) + j := by push_cast; ring
    rw [hcast_add]
    have hδeq' : δ = (K:ℝ) / ((K:ℝ) + j) := by rw [hδeq, hnKj]; push_cast; ring
    have hnr : (n:ℝ) = (K:ℝ) + j := by rw [hnKj]; push_cast; ring
    rw [hδeq', hnr]
  -- Single largest term: hammingBallVolume ≥ C(n,K)·(q-1)^K
  have hsingle : ((Nat.choose n K) * ((q - 1) ^ K) : ℝ) ≤ (hammingBallVolume q δ n : ℝ) := by
    rw [hammingBallVolume]
    have hmem : K ∈ Finset.range (⌊δ * n⌋₊ + 1) := by
      rw [← hKdef]; simp
    have hterm : (Nat.choose n K * (q - 1) ^ K : ℕ)
        ≤ ∑ i ∈ Finset.range (⌊δ * n⌋₊ + 1), Nat.choose n i * (q - 1) ^ i := by
      apply Finset.single_le_sum (f := fun i => Nat.choose n i * (q - 1) ^ i)
        (fun i _ => Nat.zero_le _) hmem
    have hcast := (Nat.cast_le (α := ℝ)).mpr hterm
    have hqsub : ((q - 1 : ℕ) : ℝ) = (q:ℝ) - 1 := by
      have h1q : 1 ≤ q := by omega
      rw [Nat.cast_sub h1q]; push_cast; ring
    push_cast [hqsub] at hcast ⊢
    convert hcast using 2
  -- master eq: S·C(n,K) = (2 ss(K+j)/(ss K ss j)) · Bform
  have hmaster : √(8 * (K:ℝ) * j / (K + j)) * (Nat.choose n K : ℝ)
      = (2 * stirlingSeq (K + j) / (stirlingSeq K * stirlingSeq j))
        * ((((K:ℝ)+j)/K)^K * (((K:ℝ)+j)/j)^j) := by
    rw [hnKj]; exact master_eq K j hK1 hj1
  -- core lemma ⇒ Bform ≤ S·C(n,K)
  have hsqrtπ_pos : (0:ℝ) < √π := Real.sqrt_pos.mpr Real.pi_pos
  have hssK : 0 < stirlingSeq K :=
    lt_of_lt_of_le hsqrtπ_pos (sqrt_pi_le_stirlingSeq (by omega))
  have hssj : 0 < stirlingSeq j :=
    lt_of_lt_of_le hsqrtπ_pos (sqrt_pi_le_stirlingSeq (by omega))
  have hcore : stirlingSeq K * stirlingSeq j ≤ 2 * stirlingSeq (K + j) :=
    core_stirling_add hK1 hj1
  have hBpos : 0 ≤ (((K:ℝ)+j)/K)^K * (((K:ℝ)+j)/j)^j := by positivity
  have hSpos : (0:ℝ) < √(8 * (K:ℝ) * j / (K + j)) := by
    apply Real.sqrt_pos.mpr; positivity
  -- Bform ≤ S·C(n,K)
  have hBle : (((K:ℝ)+j)/K)^K * (((K:ℝ)+j)/j)^j
      ≤ √(8 * (K:ℝ) * j / (K + j)) * (Nat.choose n K : ℝ) := by
    rw [hmaster]
    -- ratio ≥ 1: 2 ss(K+j)/(ss K ss j) ≥ 1
    have hratio : (1:ℝ) ≤ 2 * stirlingSeq (K + j) / (stirlingSeq K * stirlingSeq j) := by
      rw [le_div_iff₀ (by positivity)]
      linarith [hcore]
    nlinarith [hBpos, hratio]
  -- assemble: q^{nH}/S = (q-1)^K · Bform / S ≤ (q-1)^K · C(n,K) ≤ Vol
  rw [hSval, hsplit, hBform]
  -- goal: ((q-1)^K · Bform) / √(...) ≤ Vol
  have hqK_pos : (0:ℝ) ≤ ((q:ℝ) - 1) ^ K := by positivity
  calc ((q:ℝ) - 1) ^ K * ((((K:ℝ)+j)/K)^K * (((K:ℝ)+j)/j)^j) / √(8 * (K:ℝ) * j / (K + j))
      = ((q:ℝ) - 1) ^ K * ((((K:ℝ)+j)/K)^K * (((K:ℝ)+j)/j)^j / √(8 * (K:ℝ) * j / (K + j))) := by
        rw [mul_div_assoc]
    _ ≤ ((q:ℝ) - 1) ^ K * (Nat.choose n K : ℝ) := by
        apply mul_le_mul_of_nonneg_left _ hqK_pos
        rw [div_le_iff₀ hSpos, mul_comm (Nat.choose n K : ℝ)]
        exact hBle
    _ = ((Nat.choose n K) * ((q - 1) ^ K) : ℝ) := by
        ring
    _ ≤ (hammingBallVolume q δ n : ℝ) := hsingle


end ABF26C38


/-- **ABF26 Corollary 3.8.** Volume-based lower bound on list size, using the MS77
volume estimate `Vol_q(δ, n) ≥ q^{n·H_q(δ)} / √(8·n·δ·(1-δ))`. With `ρ := k/n`:

  `|Λ(C, δ)| ≥ q^{n·(ρ - 1 + H_q(δ))} / √(8·n·δ·(1-δ))`

Uses `qEntropy` (ABF26 D2.2). **FULLY PROVEN** (axioms ⊆ {propext, Classical.choice,
Quot.sound}); no `sorry`, under the lattice hypothesis `hlat` documented next.

**Lattice hypothesis (documented statement repair).** The MS77 estimate `(★)` below is a
classical lemma for an **integer** radius `δ·n`. As literally stated for arbitrary
`0 < δ < 1` it is **false**: `Vol_q(δ,n)` is a step function of `δ` (it changes only at the
lattice points `δ = k/n`, via the floor `⌊δn⌋`), while the LHS `q^{n·H_q(δ)}/√(8nδ(1-δ))` is
strictly increasing in `δ`; between lattice points the LHS overtakes the frozen volume.
Countermodel `q=2, n=4, δ=0.49`: `⌊0.49·4⌋ = 1`, so `Vol = C(4,0)+C(4,1) = 5`, yet
`2^{4·H₂(0.49)}/√(8·4·0.49·0.51) ≈ 5.65 > 5`. The faithful reading of
[MS77, Ch.10 Lem 7] therefore carries the minimal hypothesis `hlat : δ·n = ⌊δ·n⌋₊`
(equivalently `δ = ⌊δn⌋/n`). This mirrors the documented-countermodel house style of
`subspaceDesign_tau_lower` / the `RationalFunctions` statement-bug class. At lattice points
the bound is TRUE (numerically verified, zero failures over `q ∈ {2,7,101,1009,65537}`,
`n ≤ 160`) and is proven below.

**Proof architecture.** Since L3.7 (`linear_lambda_ge_elias_volume_eli57`, PROVEN in-tree)
gives `Vol_q(δ,n) / q^{n-k} ≤ |Λ(C,δ)|`, this corollary follows by transitivity from the
single real inequality

  `q^{n·H_q(δ)} / √(8·n·δ·(1-δ)) ≤ Vol_q(δ, n)`         (★)

The reduction `(★) ⟹ C3.8` (with `n ≠ 0`): `ρ = k/n ⟹ n·ρ = k`, so the C3.8 numerator
exponent `n·(ρ-1+H_q) = k - n + n·H_q`, giving `q^{n(ρ-1+H_q)} = q^{n·H_q} / q^{n-k}`; hence
the C3.8 real RHS `= (q^{n·H_q}/√(8nδ(1-δ))) / q^{n-k} ≤ Vol / q^{n-k}` by (★), which is
exactly the L3.7 real bound, and `ENNReal.ofReal` is monotone.

Inequality (★) at the lattice point is `ABF26C38.ms77_lattice` (proven above). It collapses,
`q`-independently, to one Stirling inequality: the single largest term gives
`Vol ≥ C(n,K)(q-1)^K` (`K = ⌊δn⌋ = δn`); the entropy/power identity cancels the `(q-1)^K`
exactly against `q^{n·H_q}`; the radical constant `√(8nδ(1-δ))` collapses to give the
*exact* equation `√(8K(n−K)/n)·C(n,K) = (2·stirlingSeq n / (stirlingSeq K·stirlingSeq(n−K)))
·exp(n·H_bin(K/n))`; whence (★) ⟺ `stirlingSeq K·stirlingSeq(n−K) ≤ 2·stirlingSeq n`
(`ABF26C38.core_stirling_add`), discharged via mathlib's `Real.sqrt_pi_le_stirlingSeq`, a
ported Robbins upper bound `stirlingSeq m ≤ √π·e^{1/(12m)}` (`ABF26C38.robbins_upper`,
telescoped from `Stirling.log_stirlingSeq_diff_le`), and exact treatment of the three tight
corners `{(2,1),(3,1),(3,2)}` (with `(2,1)` an exact equality `stirlingSeq(1)² = e²/2`).
[MS77, MacWilliams–Sloane, *The Theory of Error-Correcting Codes*, Ch. 10, Lemma 7]. -/
theorem linear_lambda_ge_entropy_volume
    (C : Submodule F (ι → F)) (δ : ℝ) (_hδ_pos : 0 < δ) (_hδ_lt : δ < 1)
    (hlat : δ * (Fintype.card ι : ℝ) = (⌊δ * (Fintype.card ι : ℝ)⌋₊ : ℝ)) :
    let q : ℕ := Fintype.card F
    let n : ℕ := Fintype.card ι
    let k : ℕ := Module.finrank F C
    let ρ : ℝ := k / n
    ENNReal.ofReal
        ((q : ℝ) ^ ((n : ℝ) * (ρ - 1 + qEntropy q δ))
          / (8 * n * δ * (1 - δ)) ^ ((1 : ℝ) / 2))
      ≤ (Lambda ((C : Set (ι → F))) δ : ENNReal) := by
  -- ABF26-C3.8: VERIFIED reduction to the single external MS77 ingredient (★).
  intro q n k ρ
  -- Abbreviations matching L3.7's real bound.
  set S : ℝ := (8 * (n : ℝ) * δ * (1 - δ)) ^ ((1 : ℝ) / 2) with hS_def
  set Vol : ℝ := (hammingBallVolume q δ n : ℝ) with hVol_def
  set P : ℝ := (q : ℝ) ^ ((n : ℝ) - (k : ℝ)) with hP_def
  -- Basic positivity facts.
  have hn_pos : 0 < n := Fintype.card_pos
  have hn_ne : (n : ℝ) ≠ 0 := by exact_mod_cast hn_pos.ne'
  have hqr_pos : (0 : ℝ) < (q : ℝ) := by
    have : 1 < q := Fintype.one_lt_card
    exact_mod_cast Nat.lt_of_lt_of_le Nat.zero_lt_one this.le
  have hP_pos : 0 < P := Real.rpow_pos_of_pos hqr_pos _
  -- MS77 Stirling volume estimate (★), PROVEN at lattice points (see `ABF26C38.ms77_lattice`).
  have hq2 : 2 ≤ q := Fintype.one_lt_card (α := F)
  have hn1 : 1 ≤ n := hn_pos
  -- (Fintype.one_lt_card gives `1 < q`, hence `2 ≤ q`.)
  -- the lattice hypothesis, with `n = Fintype.card ι`.
  have hlat' : δ * (n : ℝ) = (⌊δ * (n : ℝ)⌋₊ : ℝ) := hlat
  have hMS77 : (q : ℝ) ^ ((n : ℝ) * qEntropy q δ) / S ≤ Vol := by
    rw [hS_def, hVol_def]
    exact ABF26C38.ms77_lattice q n δ hq2 _hδ_pos _hδ_lt hn1 hlat'
  -- Algebra: rewrite the C3.8 numerator exponent via `n·ρ = k`.
  have hnρ : (n : ℝ) * ρ = (k : ℝ) := by
    simp only [ρ]; field_simp
  have hexp : (n : ℝ) * (ρ - 1 + qEntropy q δ)
      = ((n : ℝ) * qEntropy q δ) - ((n : ℝ) - (k : ℝ)) := by
    have : (n : ℝ) * (ρ - 1 + qEntropy q δ)
        = (n : ℝ) * ρ - (n : ℝ) + (n : ℝ) * qEntropy q δ := by ring
    rw [this, hnρ]; ring
  -- `q^{n(ρ-1+H_q)} = q^{n·H_q} / q^{n-k}`.
  have hnum : (q : ℝ) ^ ((n : ℝ) * (ρ - 1 + qEntropy q δ))
      = (q : ℝ) ^ ((n : ℝ) * qEntropy q δ) / P := by
    rw [hexp, Real.rpow_sub hqr_pos, hP_def]
  -- The real-side reduction: C3.8 RHS ≤ Vol / P (= L3.7 real bound).
  have hreduce :
      (q : ℝ) ^ ((n : ℝ) * (ρ - 1 + qEntropy q δ)) / S ≤ Vol / P := by
    -- `(q^{nH}/P)/S = (q^{nH}/S)/P ≤ Vol/P` by (★) and `P > 0`.
    rw [hnum]
    have hcomm : ((q : ℝ) ^ ((n : ℝ) * qEntropy q δ) / P) / S
        = ((q : ℝ) ^ ((n : ℝ) * qEntropy q δ) / S) / P := by
      rw [div_div, div_div, mul_comm P S]
    rw [hcomm]
    -- divide both sides of (★) by `P > 0`.
    gcongr
  -- Chain through L3.7 (PROVEN): ofReal(Vol/P) ≤ Λ.
  have hL37 := linear_lambda_ge_elias_volume_eli57 (ι := ι) (F := F) C δ _hδ_pos _hδ_lt
  -- L3.7's RHS real expression is `Vol / P`; rewrite to our `set` names.
  refine le_trans (ENNReal.ofReal_le_ofReal hreduce) ?_
  -- now: ofReal (Vol / P) ≤ Λ, matching L3.7.
  convert hL37 using 2

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

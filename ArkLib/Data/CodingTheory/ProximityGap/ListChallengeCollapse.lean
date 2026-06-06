/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/

import ArkLib.Data.CodingTheory.ProximityGap.GrandChallenges

/-!
# List-decoding endpoint collapse and refutation of the formalized list-decoding prize

This file analyses the `Prop`-valued encoding `grandListDecodingChallenge` from
`GrandChallenges.lean` (citing **ABF26 §1 Grand Challenges**, Arnon–Boneh–Fenzi, *Open
Problems in List Decoding and Correlated Agreement*) and shows it is **refuted** for every
prize instance.

## FINDING

The formalized **Grand List Decoding Challenge** predicate is **REFUTED** for every prize
instance with `n := |ι| ≥ 16` and interleaving `m ≥ 1`:

* The maximised list size `Λ(C, δ)` (`ListDecodable.Lambda`) depends on the real radius
  `δ` only through the integer "window" `{d : ℕ | d ≤ δ·n}`, because relative Hamming
  distance takes values in `{0, 1/n, …, 1}` (`closeCodewordsRel_eq_of_floor_window`,
  `Lambda_eq_of_floor_window`). Hence just **above** any `δ* < 1` there is a radius `δ'`
  in the *same* window with `Λ(·, δ') = Λ(·, δ*)` (`exists_above_same_floor_window`); this
  defeats the strict-failure (maximality) clause for every interior candidate `δ* < 1`.
* At radius `1` every codeword is within relative distance `1` of every word, so
  `Λ(C^⋈m, 1) = |C^⋈m|` (`Lambda_one`). For a Reed–Solomon code of positive degree `k ≥ 1`,
  the `m`-fold interleaving contains all `q := |F|` constant stacks, so
  `|C^⋈m| ≥ q > ε*·q` (since `ε* < 1`, `q ≥ 1`). This kills the only surviving candidate
  `δ* = 1`.
* Putting these together refutes `grandListDecodingChallengeRS` for `k ≥ 1`, `m ≥ 1`,
  `ε* < 1` (`not_grandListDecodingChallengeRS`), and the formal `listDecodingPrize`
  predicate for every domain with `n ≥ 16` and `m ≥ 1` (`not_listDecodingPrize`), since
  each prize rate `ρ_j ∈ {1/2,1/4,1/8,1/16}` gives `⌊ρ_j·n⌋ ≥ 1` when `n ≥ 16` and
  `ε* = 2^(-128) < 1`.

The determination problem the paper intends — locating the *lattice* threshold `δ*_C`
between the Johnson radius and capacity — survives only in the bracketing / witness
framework of `GrandChallenges.lean`; it is untouched and remains open. This mirrors the
MCA endpoint collapse in `GrandChallengeCollapse.lean` (produced concurrently); this file
is kept self-contained and does **not** import it.

## References

- [ABF26] Arnon, Boneh, Fenzi. *Open Problems in List Decoding and Correlated Agreement*.
  April 8, 2026. §1 Grand Challenges.
-/

set_option linter.unusedFintypeInType false
set_option linter.unusedDecidableInType false
set_option linter.unusedSectionVars false

namespace ProximityGap

open NNReal Code
open scoped BigOperators

section LambdaWindow

variable {ι : Type} [Fintype ι] [Nonempty ι] [DecidableEq ι]
variable {F : Type} [Field F] [Fintype F] [DecidableEq F]

open ListDecodable in
/-- **(1) Window characterisation of `closeCodewordsRel`.** The point list
`Λ(C, f, δ) = closeCodewordsRel C f δ` depends on the real radius `δ` only through the
integer window `{d : ℕ | (d:ℝ) ≤ δ·n}`: relative Hamming distance is `d/n` with `d : ℕ`,
so closeness is `(hammingDist f c : ℝ) ≤ δ·n`. Two radii with matching integer windows
yield identical point lists. -/
theorem closeCodewordsRel_eq_of_floor_window {α : Type}
    (C : Set (ι → α)) (f : ι → α) {δ δ' : ℝ}
    (hwin : ∀ d : ℕ, ((d : ℝ) ≤ δ' * Fintype.card ι ↔ (d : ℝ) ≤ δ * Fintype.card ι)) :
    closeCodewordsRel C f δ' = closeCodewordsRel C f δ := by
  classical
  unfold closeCodewordsRel relHammingBall
  ext c
  have hcard : (0 : ℝ) < (Fintype.card ι : ℝ) := by exact_mod_cast Fintype.card_pos
  -- `δᵣ(f,c) ≤ ρ ↔ (hammingDist f c : ℝ) ≤ ρ·n` for any real radius `ρ`.
  have key : ∀ ρ : ℝ, ((relHammingDist f c : ℚ≥0) : ℝ) ≤ ρ ↔
      (hammingDist f c : ℝ) ≤ ρ * Fintype.card ι := by
    intro ρ
    unfold relHammingDist
    push_cast
    rw [div_le_iff₀ hcard]
  simp only [Set.mem_setOf_eq]
  constructor
  · rintro ⟨hc, hd⟩
    refine ⟨hc, (key δ).mpr ?_⟩
    exact (hwin (hammingDist f c)).mp ((key δ').mp hd)
  · rintro ⟨hc, hd⟩
    refine ⟨hc, (key δ').mpr ?_⟩
    exact (hwin (hammingDist f c)).mpr ((key δ).mp hd)

open ListDecodable in
/-- **(1, cont.) `Λ` is constant across matching windows.** -/
theorem Lambda_eq_of_floor_window {α : Type}
    (C : Set (ι → α)) {δ δ' : ℝ}
    (hwin : ∀ d : ℕ, ((d : ℝ) ≤ δ' * Fintype.card ι ↔ (d : ℝ) ≤ δ * Fintype.card ι)) :
    Lambda C δ' = Lambda C δ := by
  unfold Lambda
  exact iSup_congr fun f => by rw [closeCodewordsRel_eq_of_floor_window C f hwin]

open ListDecodable in
/-- **(2) There is a strictly larger radius in the same window.** For any `δ* < 1` there is
`δ'` with `δ* < δ' ≤ 1` and `Λ(C', δ') = Λ(C', δ*)`. Take `j := ⌊δ*·n⌋`; then
`δ*·n < j+1 ≤ n`, and `δ' := (δ* + (j+1)/n)/2` lies strictly between `δ*` and `(j+1)/n`,
so both `δ*` and `δ'` have the same integer window `{d | d ≤ j}`. -/
theorem exists_above_same_floor_window {α : Type} (C' : Set (ι → α)) {δstar : ℝ≥0}
    (hδ : δstar < 1) :
    ∃ δ' : ℝ≥0, δstar < δ' ∧ δ' ≤ 1 ∧
      Lambda C' (δ' : ℝ) = Lambda C' (δstar : ℝ) := by
  classical
  set n : ℕ := Fintype.card ι with hn
  have hnpos : 0 < n := Fintype.card_pos
  have hnne : (n : ℝ≥0) ≠ 0 := by exact_mod_cast hnpos.ne'
  -- `j := ⌊δ*·n⌋`.
  set j : ℕ := Nat.floor (δstar * n) with hj
  -- `δ*·n < j+1` (strict floor bound).
  have hδn_lt : δstar * n < ((j : ℝ≥0) + 1) := by
    exact_mod_cast Nat.lt_floor_add_one (δstar * (n : ℝ≥0))
  -- `δ* < (j+1)/n`.
  have hδ_lt_step : δstar < ((j : ℝ≥0) + 1) / n := by
    rw [lt_div_iff₀ (by positivity)]
    exact hδn_lt
  -- `j+1 ≤ n`: since `δ* < 1`, `δ*·n < n` so `⌊δ*·n⌋ < n`.
  have hjn : (j : ℝ≥0) + 1 ≤ n := by
    have hδn_lt_n : δstar * n < (n : ℝ≥0) := by
      calc δstar * n < 1 * n := by
            gcongr
            exact lt_of_le_of_ne (le_of_lt hδ) (by
              intro h; exact absurd h.symm (ne_of_lt hδ))
        _ = (n : ℝ≥0) := one_mul _
    have hj_lt : j < n := by
      have : (j : ℝ≥0) ≤ δstar * n := by
        rw [hj]; exact_mod_cast Nat.floor_le (zero_le _)
      have hjn' : (j : ℝ≥0) < n := lt_of_le_of_lt this hδn_lt_n
      exact_mod_cast hjn'
    have : j + 1 ≤ n := hj_lt
    exact_mod_cast this
  -- step `(j+1)/n ≤ 1`.
  have hstep_le_one : ((j : ℝ≥0) + 1) / n ≤ 1 := by
    rw [div_le_one (by positivity)]
    exact hjn
  -- `δ' := (δ* + (j+1)/n)/2 ∈ (δ*, (j+1)/n)`.
  set b : ℝ≥0 := ((j : ℝ≥0) + 1) / n with hb
  have hmid_gt : δstar < (δstar + b) / 2 := by
    rw [lt_div_iff₀ two_pos, mul_two]
    gcongr
    exact hδ_lt_step
  have hmid_lt_b : (δstar + b) / 2 < b := by
    rw [div_lt_iff₀ two_pos, mul_two]
    gcongr
    exact hδ_lt_step
  refine ⟨(δstar + b) / 2, hmid_gt, le_of_lt (lt_of_lt_of_le hmid_lt_b hstep_le_one), ?_⟩
  -- The window of `δ'` matches that of `δ*`: both `⟺ d ≤ j`.
  apply Lambda_eq_of_floor_window
  intro d
  -- Cast the ℝ≥0 endpoints to ℝ via the coercion `(↑(δstar+b)/2 : ℝ)`.
  have hcardR : (0 : ℝ) < (Fintype.card ι : ℝ) := by exact_mod_cast Fintype.card_pos
  -- `δ*·n < j+1` in ℝ.
  have hδn_ltR : (δstar : ℝ) * Fintype.card ι < (j : ℝ) + 1 := by
    have := hδn_lt
    have : ((δstar * n : ℝ≥0) : ℝ) < (((j : ℝ≥0) + 1 : ℝ≥0) : ℝ) := by exact_mod_cast this
    push_cast at this ⊢
    rw [hn] at this
    convert this using 2
  -- `δ'·n < j+1` in ℝ, since `δ' < b = (j+1)/n`.
  have hmid_lt_bR : (((δstar + b) / 2 : ℝ≥0) : ℝ) < ((b : ℝ≥0) : ℝ) := by
    exact_mod_cast hmid_lt_b
  have hbR : ((b : ℝ≥0) : ℝ) * Fintype.card ι = (j : ℝ) + 1 := by
    have : ((b : ℝ≥0) : ℝ) = ((j : ℝ) + 1) / (Fintype.card ι : ℝ) := by
      rw [hb]; push_cast; rw [hn]
    rw [this, div_mul_cancel₀ _ (ne_of_gt hcardR)]
  have hδ'n_ltR : (((δstar + b) / 2 : ℝ≥0) : ℝ) * Fintype.card ι < (j : ℝ) + 1 := by
    calc (((δstar + b) / 2 : ℝ≥0) : ℝ) * Fintype.card ι
        < ((b : ℝ≥0) : ℝ) * Fintype.card ι := by
          apply mul_lt_mul_of_pos_right hmid_lt_bR hcardR
      _ = (j : ℝ) + 1 := hbR
  -- `δ* ≤ δ'` (so `δ*·n ≤ δ'·n`).
  have hmid_geR : (δstar : ℝ) ≤ (((δstar + b) / 2 : ℝ≥0) : ℝ) := by
    have : (δstar : ℝ≥0) ≤ (δstar + b) / 2 := le_of_lt hmid_gt
    exact_mod_cast this
  -- `j ≤ δ*·n`.
  have hj_leR : (j : ℝ) ≤ (δstar : ℝ) * Fintype.card ι := by
    have : (j : ℝ≥0) ≤ δstar * n := by
      rw [hj]; exact_mod_cast Nat.floor_le (zero_le _)
    have : ((j : ℝ≥0) : ℝ) ≤ ((δstar * n : ℝ≥0) : ℝ) := by exact_mod_cast this
    push_cast at this; rw [hn]; convert this using 2
  constructor
  · -- `d ≤ δ'·n → d ≤ δ*·n`.  Both windows are `d ≤ j`.
    intro hd
    -- From `d ≤ δ'·n < j+1` we get `d ≤ j`, hence `d ≤ j ≤ δ*·n`.
    have hd_lt : (d : ℝ) < (j : ℝ) + 1 := lt_of_le_of_lt hd hδ'n_ltR
    have hdj : d ≤ j := by
      have : (d : ℝ) < ((j + 1 : ℕ) : ℝ) := by push_cast; exact hd_lt
      have := (Nat.cast_lt (α := ℝ)).mp this
      omega
    calc (d : ℝ) ≤ (j : ℝ) := by exact_mod_cast hdj
      _ ≤ (δstar : ℝ) * Fintype.card ι := hj_leR
  · -- `d ≤ δ*·n → d ≤ δ'·n`, since `δ*·n ≤ δ'·n`.
    intro hd
    refine le_trans hd ?_
    apply mul_le_mul_of_nonneg_right hmid_geR (le_of_lt hcardR)

open ListDecodable in
/-- **(3) `Λ` at radius one is the whole code size.** Since `δᵣ(f,c) ≤ 1` always, the
radius-one ball is all of `C'`, so `Λ(C', 1) = |C'|` (as `ℕ∞`). Uses `[Nonempty (ι → α)]`
to realise the supremum at the constant word. -/
theorem Lambda_one {α : Type} [Nonempty α] (C' : Set (ι → α)) :
    Lambda C' (1 : ℝ) = (C'.ncard : ℕ∞) := by
  classical
  unfold Lambda
  have hball : ∀ f : ι → α, closeCodewordsRel C' f (1 : ℝ) = C' := by
    intro f
    unfold closeCodewordsRel relHammingBall
    ext c
    simp only [Set.mem_setOf_eq]
    refine ⟨fun hc => hc.1, fun hc => ⟨hc, ?_⟩⟩
    exact_mod_cast (relHammingDist_le_one (u := f) (v := c))
  refine le_antisymm (iSup_le fun f => by rw [hball f]) ?_
  obtain ⟨a⟩ := (inferInstance : Nonempty α)
  exact le_iSup_of_le (fun _ => a) (by rw [hball (fun _ => a)])

end LambdaWindow

section InterleavedRSFloor

variable {ι : Type} [Fintype ι] [Nonempty ι] [DecidableEq ι]
variable {F : Type} [Field F] [Fintype F] [DecidableEq F]

/-- Constant words are Reed–Solomon codewords whenever `k ≥ 1`: `C a ∈ degreeLT F k`
(`degree_C_le`) and `evalOnPoints` sends it to the constant word. -/
lemma const_mem_reedSolomonCode (domain : ι ↪ F) {k : ℕ} (hk : 1 ≤ k) (a : F) :
    (fun _ : ι => a) ∈ (ReedSolomon.code domain k : Set (ι → F)) := by
  have hmem : Polynomial.C a ∈ Polynomial.degreeLT F k := by
    rw [Polynomial.mem_degreeLT]
    calc (Polynomial.C a).degree ≤ 0 := Polynomial.degree_C_le
      _ < (k : WithBot ℕ) := by exact_mod_cast hk
  rw [ReedSolomon.code, Submodule.mem_map]
  refine ⟨Polynomial.C a, hmem, ?_⟩
  funext i
  simp [ReedSolomon.evalOnPoints]

/-- **(4) Interleaved-RS cardinality floor.** For `k ≥ 1` and `m ≥ 1`, the `m`-fold
interleaving of the Reed–Solomon code has at least `|F|` elements: the constant stacks
`a ↦ (i,_) ↦ a` inject `F` into `C^⋈ (Fin m)` (distinct constants disagree at any cell,
using `[Nonempty ι]` and `m ≥ 1`). -/
lemma card_le_ncard_interleaved_reedSolomon
    (domain : ι ↪ F) {k m : ℕ} (hk : 1 ≤ k) (hm : 1 ≤ m) :
    (Fintype.card F : ℕ∞) ≤
      ((ReedSolomon.code domain k : Set (ι → F))^⋈ (Fin m) :
        Set (Matrix ι (Fin m) F)).ncard := by
  classical
  have hconst : ∀ a : F, (fun _ : ι => a) ∈ (ReedSolomon.code domain k : Set (ι → F)) :=
    fun a => const_mem_reedSolomonCode domain hk a
  -- The constant matrices `a ↦ Matrix.of (fun _ _ => a)`.
  have hinj : Set.InjOn (fun a : F => (Matrix.of fun _ _ => a : Matrix ι (Fin m) F))
      Set.univ := by
    intro a _ b _ hab
    obtain ⟨i⟩ := (inferInstance : Nonempty ι)
    have := congrFun (congrFun hab i) ⟨0, hm⟩
    simpa using this
  have hsub : (fun a : F => (Matrix.of fun _ _ => a : Matrix ι (Fin m) F)) '' Set.univ ⊆
      ((ReedSolomon.code domain k : Set (ι → F))^⋈ (Fin m) :
        Set (Matrix ι (Fin m) F)) := by
    rintro _ ⟨a, -, rfl⟩
    intro col
    exact hconst a
  have h1 : (Set.univ : Set F).ncard ≤
      ((ReedSolomon.code domain k : Set (ι → F))^⋈ (Fin m) :
        Set (Matrix ι (Fin m) F)).ncard := by
    rw [← Set.InjOn.ncard_image hinj]
    exact Set.ncard_le_ncard hsub (Set.toFinite _)
  rw [Set.ncard_univ, Nat.card_eq_fintype_card] at h1
  exact_mod_cast h1

end InterleavedRSFloor

section Refutation

variable {ι : Type} [Fintype ι] [Nonempty ι] [DecidableEq ι]
variable {F : Type} [Field F] [Fintype F] [DecidableEq F]

open ListDecodable GrandChallenges

/-- Helper: a strictly larger radius `δ'` in the same window as `δ*` has, *coerced to ℝ*,
matching integer windows. (Bridges `exists_above_same_floor_window`'s ℝ≥0 form into the
`Lambda` argument.) Actually packaged directly inside the refutation below. -/

open ListDecodable in
/-- **(5) Refutation of the RS Grand List Decoding Challenge.** For `k ≥ 1`, `m ≥ 1`,
`ε* < 1`, the predicate `grandListDecodingChallengeRS domain k m ε*` is **false**.

Proof. A witness gives `δ*` with the bound at `δ*` and strict failure above. At the only
surviving candidate `δ* = 1`, the bound says `Λ(C^⋈m, 1) ≤ ε*·q`; but `Λ(C^⋈m, 1) = |C^⋈m|
≥ q > ε*·q` (constants), contradiction. For `δ* < 1`, `exists_above_same_floor_window`
gives `δ'` with `δ* < δ' ≤ 1` and `Λ(·, δ') = Λ(·, δ*) ≤ ε*·q`, contradicting the strict
failure clause `Λ(·, δ') > ε*·q`. -/
theorem not_grandListDecodingChallengeRS (domain : ι ↪ F) {k m : ℕ}
    (hk : 1 ≤ k) (hm : 1 ≤ m) {ε_star : ℝ≥0} (hε : ε_star < 1) :
    ¬ grandListDecodingChallengeRS domain k m ε_star := by
  classical
  rintro ⟨δstar, hle1, hbound, hmax⟩
  -- Numeric core: `Λ(C^⋈m, 1) ≥ q > ε*·q`.
  set C : Set (ι → F) := ReedSolomon.code domain k with hC
  have hqle : (Fintype.card F : ENNReal) ≤
      (Lambda (C^⋈ (Fin m)) ((1 : ℝ≥0) : ℝ) : ENNReal) := by
    have hbig := card_le_ncard_interleaved_reedSolomon domain hk hm
    have hone : Lambda (C^⋈ (Fin m)) ((1 : ℝ≥0) : ℝ) =
        (((C^⋈ (Fin m)) : Set (Matrix ι (Fin m) F)).ncard : ℕ∞) := by
      rw [show ((1 : ℝ≥0) : ℝ) = (1 : ℝ) by norm_num]
      exact Lambda_one (α := Fin m → F) (C^⋈ (Fin m))
    rw [hone]
    exact_mod_cast hbig
  have hq_pos : (0 : ENNReal) < (Fintype.card F : ENNReal) := by
    exact_mod_cast Fintype.card_pos
  have hq_ne_top : (Fintype.card F : ENNReal) ≠ ⊤ := ENNReal.natCast_ne_top _
  have hε' : (ε_star : ENNReal) < 1 := by exact_mod_cast hε
  have hlt : (ε_star : ENNReal) * (Fintype.card F : ENNReal) <
      (Fintype.card F : ENNReal) := by
    calc (ε_star : ENNReal) * (Fintype.card F : ENNReal)
        = (Fintype.card F : ENNReal) * (ε_star : ENNReal) := mul_comm _ _
      _ < (Fintype.card F : ENNReal) * 1 :=
          ENNReal.mul_lt_mul_right hq_pos.ne' hq_ne_top hε'
      _ = (Fintype.card F : ENNReal) := mul_one _
  -- `Λ(C^⋈m, 1) > ε*·q`.
  have hone_gt : (Lambda (C^⋈ (Fin m)) ((1 : ℝ≥0) : ℝ) : ENNReal) >
      (ε_star : ENNReal) * (Fintype.card F : ENNReal) :=
    lt_of_lt_of_le hlt hqle
  -- Split on `δ* = 1` vs `δ* < 1`.
  rcases eq_or_lt_of_le hle1 with heq | hlt1
  · -- `δ* = 1`: the bound contradicts `hone_gt`.
    rw [heq] at hbound
    exact absurd hbound (not_le.mpr hone_gt)
  · -- `δ* < 1`: same-window radius above defeats maximality.
    obtain ⟨δ', hgt, hle1', hLeq⟩ :=
      exists_above_same_floor_window (C^⋈ (Fin m)) hlt1
    have hfail := hmax δ' hgt hle1'
    -- `Λ(·, δ') = Λ(·, δ*)`, so `Λ(·, δ') ≤ ε*·q`, contradicting `hfail`.
    rw [hLeq] at hfail
    exact absurd hbound (not_le.mpr hfail)

/-- For every prize rate `ρ_j` (`j : Fin 4`), `⌊ρ_j·n⌋ ≥ 1` when `n ≥ 16`, because the
smallest rate `1/16` already gives `(1/16)·16 = 1 ≤ (1/16)·n`. -/
lemma one_le_floor_prizeRate (j : Fin 4) (hn : 16 ≤ Fintype.card ι) :
    1 ≤ ⌊prizeRates j * (Fintype.card ι : ℝ≥0)⌋₊ := by
  have hrate_ge : (1 : ℝ≥0) / 2 ^ (4 : ℕ) ≤ prizeRates j := by
    unfold prizeRates
    apply div_le_div_of_nonneg_left (by norm_num) (by positivity)
    apply pow_le_pow_right₀ (by norm_num)
    have : j.val + 1 ≤ 4 := by omega
    exact this
  have hfloor : ((1 : ℕ) : ℝ≥0) ≤ prizeRates j * (Fintype.card ι : ℝ≥0) := by
    push_cast
    calc (1 : ℝ≥0)
        = (1 / 2 ^ (4 : ℕ)) * 16 := by norm_num
      _ ≤ (1 / 2 ^ (4 : ℕ)) * (Fintype.card ι : ℝ≥0) := by
            gcongr
            exact_mod_cast hn
      _ ≤ prizeRates j * (Fintype.card ι : ℝ≥0) := by
            gcongr
  exact Nat.le_floor hfloor

/-- `ε* = 2^(-128) < 1`. -/
lemma epsStar_lt_one : epsStar < 1 := by
  unfold epsStar
  rw [div_lt_one (by positivity)]
  exact one_lt_pow₀ one_lt_two (by norm_num)

/-- **(6) Refutation of the formal §1 list-decoding prize.** For every evaluation domain
with `n := |ι| ≥ 16` and interleaving `m ≥ 1`, the predicate `listDecodingPrize domain m`
is **false**: at rate `ρ = 1/16` (any `j`) we have `k = ⌊ρ·n⌋ ≥ 1`, `ε* = 2^(-128) < 1`,
and `not_grandListDecodingChallengeRS` applies. -/
theorem not_listDecodingPrize (domain : ι ↪ F) {m : ℕ} (hm : 1 ≤ m)
    (hn : 16 ≤ Fintype.card ι) :
    ¬ listDecodingPrize domain m := by
  intro hprize
  have h3 := hprize 3
  have hk : 1 ≤ ⌊prizeRates 3 * (Fintype.card ι : ℝ≥0)⌋₊ :=
    one_le_floor_prizeRate 3 hn
  exact not_grandListDecodingChallengeRS domain hk hm epsStar_lt_one h3

/-- **(6, per-rate version).** For every rate index `j : Fin 4` and `n ≥ 16`, the per-rate
RS Grand List Decoding Challenge at `k = ⌊ρ_j·n⌋`, threshold `ε* = 2^(-128)`, is **false**
(for every `m ≥ 1`). Each of the four rates has `⌊ρ_j·n⌋ ≥ 1` when `n ≥ 16`. -/
theorem not_grandListDecodingChallengeRS_prizeRate
    (domain : ι ↪ F) (j : Fin 4) {m : ℕ} (hm : 1 ≤ m) (hn : 16 ≤ Fintype.card ι) :
    ¬ grandListDecodingChallengeRS domain ⌊prizeRates j * (Fintype.card ι : ℝ≥0)⌋₊ m epsStar :=
  not_grandListDecodingChallengeRS domain (one_le_floor_prizeRate j hn) hm epsStar_lt_one

end Refutation

end ProximityGap

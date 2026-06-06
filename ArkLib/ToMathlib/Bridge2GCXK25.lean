/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/

import ArkLib.Data.CodingTheory.Connections.EpsMCABadGlue
import ArkLib.Data.CodingTheory.ListDecodability
import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# GCXK25 union-bound-over-the-list brick (sharpening the T5.1 residual)

This file isolates and proves, **kernel-clean**, the *union-bound-over-the-list* step of
[GCXK25] *From List-Decodability to Proximity Gaps* (Gao, Cai, Xu, Kan; eprint 2025/870),
Theorem 3 = ABF26 Theorem 5.1.

The companion `Connections/ListDecodingAndCA.lean` reduces the `ε_mca` bound

  `ε_mca(C, 1 − √(1 − δ + η)) ≤ (L²·δ·n + 1/η)/|F|`

to a **per-stack bad-`γ` count** `|mcaBad u| ≤ L²·δ·n + 1/η`
(`linear_listSize_to_epsMCA_gcxk25_of_bad_count`, whose residual is `hBadCount`). The
supremum-to-count plumbing is proven in `Connections/EpsMCABadGlue.lean`. What was *not*
in-tree was the connection between that per-stack count and the **list** of close codewords —
GCXK25's actual structure is a union bound over that list.

## What is proven here (structural, `sorry`-free, axiom-clean)

* `mcaBadWitness` — for a fixed stack `(u₀, u₁)`, radius `δ`, and a *fixed* codeword `w ∈ C`,
  the finset of scalars `γ` for which the `mcaEvent` is *witnessed by `w`* (i.e. `w` is the
  large-agreement codeword on the witness set `S`, and no joint pair of codewords agrees
  with `(u₀, u₁)` on `S`).
* `mcaBad_subset_biUnion_mcaBadWitness` — **the union-bound containment**: every bad `γ` is
  witnessed by *some* codeword `w ∈ C`, so `mcaBad ⊆ ⋃_{w ∈ C} mcaBadWitness w`. This is the
  exact "every bad combining point is δ-close to a codeword in the list" step of GCXK25.
* `mcaBad_card_le_sum_mcaBadWitness_card` — **the union bound**:
  `|mcaBad| ≤ ∑_{w ∈ C} |mcaBadWitness w|`.
* `mcaBad_card_le_of_per_codeword` — **the reduction to a per-codeword count**: if a finite
  set `T` of codewords carries all witnesses, each contributing at most `b` bad scalars
  (`|mcaBadWitness w| ≤ b`), then `|mcaBad u| ≤ |T| · b`. With `|T| ≤ L²` (the list-size
  factor) and `b = δ·n + (1/η)/L²` this is exactly the `L²·δ·n + 1/η` shape of GCXK25
  Theorem 3.

## What this file does *not* close

It does **not** supply the per-codeword count `|mcaBadWitness w| ≤ δ·n` (GCXK25's `|Bad¹|`
first-moment / GKL24 agree-domain count) nor the list-size-factor count of contributing
codewords. Those are GCXK25's genuine combinatorial content, not connected to ArkLib's
agree-domain structure in-tree. This file is purely the union-bound-over-the-list plumbing,
which sharpens the residual from a single per-stack count to a *per-codeword* count plus a
list-size factor — strictly closer to GCXK25's `|Bad¹| ≤ pn` first-moment statement.

## References

* [ABF26] Arnon, Boneh, Fenzi. *Open Problems in List Decoding and Correlated Agreement*.
  2026. Theorem 5.1.
* [GCXK25] Gao, Cai, Xu, Kan. *From List-Decodability to Proximity Gaps*. eprint 2025/870.
  Theorem 3, Corollary 2.
-/

set_option linter.unusedFintypeInType false
set_option linter.unusedDecidableInType false
set_option linter.unusedSectionVars false

namespace ProximityGap

open NNReal Code Finset
open scoped ProbabilityTheory BigOperators

section
variable {ι : Type} [Fintype ι] [Nonempty ι] [DecidableEq ι]
variable {F : Type} [Field F] [Fintype F] [DecidableEq F]
variable {A : Type} [Fintype A] [DecidableEq A] [AddCommGroup A] [Module F A]

open Classical in
/-- For a fixed stack `(u₀, u₁)`, radius `δ`, and a *fixed* codeword `w`, the finset of
scalars `γ ∈ F` for which the `mcaEvent` is witnessed by `w`: there is a witness set `S` of
size `≥ (1-δ)·n` on which `w` agrees with the line `u₀ + γ • u₁`, yet no joint codeword pair
of `C` agrees with `(u₀, u₁)` on `S`.

This is the per-codeword slice of `mcaBad`. GCXK25's union bound is over the codewords `w` in
the list `Λ(C, line, δ)`; grouping `mcaBad` by the witness codeword is exactly that union. -/
noncomputable def mcaBadWitness (C : Set (ι → A)) (δ : ℝ≥0) (u₀ u₁ : ι → A) (w : ι → A) :
    Finset F :=
  Finset.univ.filter (fun γ : F =>
    ∃ S : Finset ι, (S.card : ℝ≥0) ≥ (1 - δ) * Fintype.card ι ∧
      (∀ i ∈ S, w i = u₀ i + γ • u₁ i) ∧
      ¬ pairJointAgreesOn C S u₀ u₁)

open Classical in
/-- **Union-bound containment (GCXK25 "every bad point is δ-close to a list codeword").**
Every bad scalar `γ ∈ mcaBad` is witnessed by *some* codeword `w ∈ C`; hence `mcaBad` is
contained in the union over `C` (as a finite set of codewords) of the per-codeword slices
`mcaBadWitness w`.

The witness codeword is the `w ∈ C` produced by the `mcaEvent`'s large-agreement clause. -/
theorem mcaBad_subset_biUnion_mcaBadWitness
    (C : Set (ι → A)) (δ : ℝ≥0) (u₀ u₁ : ι → A)
    (T : Finset (ι → A)) (hT : ∀ w ∈ C, w ∈ T) :
    mcaBad (F := F) C δ u₀ u₁ ⊆ T.biUnion (fun w => mcaBadWitness (F := F) C δ u₀ u₁ w) := by
  classical
  intro γ hγ
  rw [mcaBad, Finset.mem_filter] at hγ
  obtain ⟨S, hScard, ⟨w, hwC, hwagree⟩, hpair⟩ := hγ.2
  rw [Finset.mem_biUnion]
  refine ⟨w, hT w hwC, ?_⟩
  rw [mcaBadWitness, Finset.mem_filter]
  exact ⟨Finset.mem_univ _, ⟨S, hScard, hwagree, hpair⟩⟩

open Classical in
/-- **Union bound (`|mcaBad| ≤ ∑_{w ∈ C} |mcaBadWitness w|`).** The cardinality form of
`mcaBad_subset_biUnion_mcaBadWitness`, via `Finset.card_biUnion_le`. This is GCXK25's union
bound over the list of close codewords. -/
theorem mcaBad_card_le_sum_mcaBadWitness_card
    (C : Set (ι → A)) (δ : ℝ≥0) (u₀ u₁ : ι → A)
    (T : Finset (ι → A)) (hT : ∀ w ∈ C, w ∈ T) :
    (mcaBad (F := F) C δ u₀ u₁).card ≤
      ∑ w ∈ T, (mcaBadWitness (F := F) C δ u₀ u₁ w).card := by
  classical
  calc (mcaBad (F := F) C δ u₀ u₁).card
      ≤ (T.biUnion (fun w => mcaBadWitness (F := F) C δ u₀ u₁ w)).card :=
        Finset.card_le_card (mcaBad_subset_biUnion_mcaBadWitness C δ u₀ u₁ T hT)
    _ ≤ ∑ w ∈ T, (mcaBadWitness (F := F) C δ u₀ u₁ w).card := Finset.card_biUnion_le

open Classical in
/-- **Reduction to a per-codeword count (real form).** If a finite set `T` of codewords
carries all witnesses (`∀ w ∈ C, w ∈ T`) and each contributes at most `b ≥ 0` bad scalars
(`|mcaBadWitness w| ≤ b`), then `|mcaBad u| ≤ |T| · b`.

With `|T| ≤ L²` (the GCXK25 list-size factor) and the per-codeword agree-domain count
`b = δ·n` (GCXK25's `|Bad¹| ≤ pn`), this is the `L²·δ·n` first-moment part of the
`L²·δ·n + 1/η` shape; the `1/η` is the in-tree second-moment summand
(`GCXK25SecondMoment.card_lt_one_div_of_second_moment_rs`). -/
theorem mcaBad_card_le_of_per_codeword
    (C : Set (ι → A)) (δ : ℝ≥0) (u₀ u₁ : ι → A)
    (T : Finset (ι → A)) (hT : ∀ w ∈ C, w ∈ T)
    {b : ℝ} (_hb0 : 0 ≤ b)
    (hper : ∀ w ∈ T, ((mcaBadWitness (F := F) C δ u₀ u₁ w).card : ℝ) ≤ b) :
    ((mcaBad (F := F) C δ u₀ u₁).card : ℝ) ≤ (T.card : ℝ) * b := by
  classical
  have hsum : ((mcaBad (F := F) C δ u₀ u₁).card : ℝ) ≤
      ∑ w ∈ T, ((mcaBadWitness (F := F) C δ u₀ u₁ w).card : ℝ) := by
    have := mcaBad_card_le_sum_mcaBadWitness_card (F := F) C δ u₀ u₁ T hT
    calc ((mcaBad (F := F) C δ u₀ u₁).card : ℝ)
        ≤ ((∑ w ∈ T, (mcaBadWitness (F := F) C δ u₀ u₁ w).card : ℕ) : ℝ) := by
          exact_mod_cast this
      _ = ∑ w ∈ T, ((mcaBadWitness (F := F) C δ u₀ u₁ w).card : ℝ) := by push_cast; ring
  calc ((mcaBad (F := F) C δ u₀ u₁).card : ℝ)
      ≤ ∑ w ∈ T, ((mcaBadWitness (F := F) C δ u₀ u₁ w).card : ℝ) := hsum
    _ ≤ ∑ _w ∈ T, b := Finset.sum_le_sum (fun w hw => hper w hw)
    _ = (T.card : ℝ) * b := by rw [Finset.sum_const, nsmul_eq_mul]

end

end ProximityGap

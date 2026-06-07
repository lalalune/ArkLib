/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/

import ArkLib.ToMathlib.Bridge2GCXK25
import ArkLib.ToMathlib.BridgeListDecodingCA
import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# GKL24-style first-moment per-codeword bad-`γ` count (the last piece of ABF26 T5.1)

This file isolates and proves, **kernel-clean**, the *first-moment / per-codeword* half of the
reduction behind [GCXK25] Theorem 3 = ABF26 Theorem 5.1. It supplies the missing per-codeword
count that `ArkLib/ToMathlib/Bridge2GCXK25.lean` left as a residual, namely a *fully in-tree*
upper bound on `|mcaBadWitness C δ u₀ u₁ w|`, the set of combining points `γ` for which the
`mcaEvent` at radius `δ` is witnessed by a single fixed codeword `w`.

## The honest decomposition

`Connections/ListDecodingAndCA.lean` reduces ABF26 T5.1 to a per-stack bad-`γ` count
`|mcaBad u| ≤ L²·δ·n + 1/η` (`linear_listSize_to_epsMCA_gcxk25_of_bad_count`). `Bridge2GCXK25`
then splits that per-stack count via a **union bound over the close-codeword list**:

  `|mcaBad u| ≤ ∑_{w ∈ T} |mcaBadWitness w| ≤ |T| · b`        (with `|T| ≤ L²`)

leaving the genuine residual: a *per-codeword* count `|mcaBadWitness w| ≤ b`. GCXK25's
first-moment bound is `b = δ·n` (their `|Bad¹| ≤ pn`, via the GKL24 agree-domain intersection
machinery). This file proves the in-tree-supportable version of that per-codeword count.

## What is proven here (in-tree, `sorry`-free, axiom-clean)

The key combinatorial fact — the **single-codeword determinacy of the combining point**.

Fix a codeword `w` and a stack `(u₀, u₁)` over `A = F`. For each `γ ∈ mcaBadWitness w`, the
`mcaEvent` produces a witness set `S` of size `≥ (1-δ)·n` on which `w = u₀ + γ • u₁`, **and** the
`¬ pairJointAgreesOn` clause forces `u₁` to be nonzero somewhere on `S` (otherwise `(w, 0)` would
be a joint codeword pair agreeing with `(u₀, u₁)` on `S`). At any coordinate `i ∈ S` with
`u₁ i ≠ 0`, the line equation `w i = u₀ i + γ · u₁ i` **solves uniquely for `γ`**:

  `γ = (w i - u₀ i) · (u₁ i)⁻¹`.

Hence every bad `γ` lies in the image of the *fixed* "combining-point" map
`g(i) := (w i - u₀ i) · (u₁ i)⁻¹` over the support `D := {i : u₁ i ≠ 0}`, giving

  `|mcaBadWitness w| ≤ |D| ≤ n`.

* `mcaBadWitness_subset_image_combiningPoint` — the containment `mcaBadWitness w ⊆ g '' D`.
* `mcaBadWitness_card_le_support` — `|mcaBadWitness w| ≤ |support u₁|`.
* `mcaBadWitness_card_le_card` — the uniform `|mcaBadWitness w| ≤ n` corollary.
* `mcaBad_card_le_listFactor_mul_card` and `epsMCA_le_ofReal_of_listFactor` — the composed
  per-stack / `ε_mca` bounds with the now-in-tree per-codeword count `b = n`.

## What this file does *not* close (the named GKL24 residual)

The in-tree per-codeword count is `b = |support u₁| ≤ n`, **not** GCXK25's sharper `b = δ·n`.
The gap `support u₁ ⤳ δ·n` is exactly the GKL24 first-moment agree-domain-intersection content
(their Lemma 1 / Corollary 1): it is a *global* counting over the close-codeword list (charging
each bad point to fresh disagreement coordinates of the line family), not derivable from a single
fixed codeword `w` in isolation. We surface it as the single named hypothesis
`GKL24FirstMomentResidual` and record the conditional strengthening
`epsMCA_le_ofReal_of_gkl24_residual`, which recovers the exact `L²·δ·n` first-moment shape from
it. Everything *else* on the path is now in-tree.

## References

* [ABF26] Arnon, Boneh, Fenzi. *Open Problems in List Decoding and Correlated Agreement*. 2026.
  Theorem 5.1.
* [GCXK25] Gao, Cai, Xu, Kan. *From List-Decodability to Proximity Gaps*. eprint 2025/870.
  Theorem 3, Corollary 2, Lemma 1.
* [GKL24] Guruswami, Kumar, Liu (agree-domain intersection / first-moment count).
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

/-- The **combining-point map** of a fixed codeword `w` against a stack `(u₀, u₁)`: at a
coordinate `i` where `u₁ i ≠ 0`, the unique scalar `γ` solving `w i = u₀ i + γ · u₁ i`, namely
`(w i - u₀ i) · (u₁ i)⁻¹`. At coordinates with `u₁ i = 0` the value is irrelevant (the inverse
is `0` by convention) — those coordinates are excluded from the support `D` below. -/
def combiningPoint (w u₀ u₁ : ι → F) (i : ι) : F :=
  (w i - u₀ i) * (u₁ i)⁻¹

/-- The support of the second word `u₁`: the coordinates where it is nonzero. The combining-point
map ranges over this set, and the bad combining points all land in its image. -/
def secondSupport (u₁ : ι → F) : Finset ι :=
  Finset.univ.filter (fun i => u₁ i ≠ 0)

/-- **Single-codeword determinacy (the core in-tree fact).** For a `Submodule` code `MC` and a
fixed codeword `w ∈ MC`, every bad combining point `γ ∈ mcaBadWitness w` equals
`combiningPoint w u₀ u₁ i` at some coordinate `i ∈ secondSupport u₁`.

The witness set `S` of `γ` carries `w = u₀ + γ • u₁` on `S` and (via `¬ pairJointAgreesOn`) cannot
have `u₁` vanish on all of `S`: were `u₁ = 0` on `S`, the codeword pair `(w, 0)` (both in `MC`)
would agree with `(u₀, u₁)` on `S` (since then `w = u₀` on `S`), giving `pairJointAgreesOn`. Pick
`i ∈ S` with `u₁ i ≠ 0`; the line equation at `i` solves uniquely for `γ`. -/
theorem mcaBadWitness_subset_image_combiningPoint
    (MC : Submodule F (ι → F)) (δ : ℝ≥0) (u₀ u₁ w : ι → F)
    (hw : w ∈ (MC : Set (ι → F))) :
    mcaBadWitness (F := F) (MC : Set (ι → F)) δ u₀ u₁ w ⊆
      (secondSupport u₁).image (combiningPoint w u₀ u₁) := by
  classical
  intro γ hγ
  rw [mcaBadWitness, Finset.mem_filter] at hγ
  obtain ⟨S, _hScard, hwline, hpair⟩ := hγ.2
  -- `u₁` is nonzero somewhere on `S` (else `(w, 0)` is a joint pair, contradicting `hpair`).
  have hexists : ∃ i ∈ S, u₁ i ≠ 0 := by
    by_contra hcon
    push Not at hcon
    -- `hcon : ∀ i ∈ S, u₁ i = 0`. Build the joint codeword pair `(w, 0)`.
    apply hpair
    refine ⟨w, hw, 0, MC.zero_mem, ?_⟩
    intro i hi
    refine ⟨?_, by simpa using (hcon i hi).symm⟩
    -- `w i = u₀ i + γ • u₁ i = u₀ i` since `u₁ i = 0`.
    rw [hwline i hi, hcon i hi]
    simp
  obtain ⟨i, hiS, hi0⟩ := hexists
  rw [Finset.mem_image]
  refine ⟨i, ?_, ?_⟩
  · rw [secondSupport, Finset.mem_filter]
    exact ⟨Finset.mem_univ _, hi0⟩
  · -- Solve `w i = u₀ i + γ * u₁ i` for `γ`.
    have hline : w i = u₀ i + γ * u₁ i := by simpa [smul_eq_mul] using hwline i hiS
    rw [combiningPoint]
    have hsub : w i - u₀ i = γ * u₁ i := by rw [hline]; ring
    rw [hsub, mul_assoc, mul_inv_cancel₀ hi0, mul_one]

/-- **Per-codeword first-moment count (in-tree form).** For a `Submodule` code `MC` and a fixed
codeword `w ∈ MC`, the number of bad combining points witnessed by `w` is at most the support
size of `u₁`:

  `|mcaBadWitness w| ≤ |support u₁|`.

This is the honest in-tree per-codeword count: each bad `γ` is pinned by the combining-point map
to a distinct-valued coordinate of `u₁`'s support. -/
theorem mcaBadWitness_card_le_support
    (MC : Submodule F (ι → F)) (δ : ℝ≥0) (u₀ u₁ w : ι → F)
    (hw : w ∈ (MC : Set (ι → F))) :
    (mcaBadWitness (F := F) (MC : Set (ι → F)) δ u₀ u₁ w).card ≤ (secondSupport u₁).card := by
  classical
  calc (mcaBadWitness (F := F) (MC : Set (ι → F)) δ u₀ u₁ w).card
      ≤ ((secondSupport u₁).image (combiningPoint w u₀ u₁)).card :=
        Finset.card_le_card (mcaBadWitness_subset_image_combiningPoint MC δ u₀ u₁ w hw)
    _ ≤ (secondSupport u₁).card := Finset.card_image_le

/-- **Uniform per-codeword count `|mcaBadWitness w| ≤ n`.** The support of `u₁` is a subset of the
ambient coordinate set, so the per-codeword count is bounded by `n := |ι|`, uniformly over the
stack and the witness codeword. This is the in-tree first-moment count `b = n` (the `δ`-free
relaxation of GCXK25's `b = δ·n`). -/
theorem mcaBadWitness_card_le_card
    (MC : Submodule F (ι → F)) (δ : ℝ≥0) (u₀ u₁ w : ι → F)
    (hw : w ∈ (MC : Set (ι → F))) :
    (mcaBadWitness (F := F) (MC : Set (ι → F)) δ u₀ u₁ w).card ≤ Fintype.card ι := by
  calc (mcaBadWitness (F := F) (MC : Set (ι → F)) δ u₀ u₁ w).card
      ≤ (secondSupport u₁).card := mcaBadWitness_card_le_support MC δ u₀ u₁ w hw
    _ ≤ Fintype.card ι := by
        rw [secondSupport]
        exact le_trans (Finset.card_filter_le _ _) (le_of_eq (Finset.card_univ))

/-- Real-valued form of `mcaBadWitness_card_le_card`, ready for the union-bound brick. -/
theorem mcaBadWitness_card_le_card_real
    (MC : Submodule F (ι → F)) (δ : ℝ≥0) (u₀ u₁ w : ι → F)
    (hw : w ∈ (MC : Set (ι → F))) :
    ((mcaBadWitness (F := F) (MC : Set (ι → F)) δ u₀ u₁ w).card : ℝ) ≤ (Fintype.card ι : ℝ) := by
  exact_mod_cast mcaBadWitness_card_le_card MC δ u₀ u₁ w hw

/-! ### Pairwise sharpening of the per-codeword count (toward GCXK25's `b = δ·n`)

The single-codeword determinacy above gives `b = |support u₁| ≤ n`. A *strictly sharper* in-tree
count — within a factor of `2` of GCXK25's first-moment `b = δ·n` — follows from comparing **two
distinct** bad combining points witnessed by the *same* codeword `w`. If `γ ≠ γ'` are both bad for
`w`, their witness sets `S, S'` (each `≥ (1-δ)·n`) intersect in `≥ (1-2δ)·n` coordinates, on which
`u₀ + γ•u₁ = w = u₀ + γ'•u₁` forces `(γ-γ')•u₁ = 0`, i.e. `u₁ = 0`. Hence `secondSupport u₁ ≤ 2δ·n`
whenever `w` witnesses at least two bad points, sharpening the per-codeword count to
`b = max 1 (2·δ·n)`. -/

/-- The **zero set** of `u₁`: the coordinates where it vanishes. Complement of `secondSupport u₁`
in `univ`; on it the line `u₀ + γ • u₁` is independent of `γ`. -/
def secondZeros (u₁ : ι → F) : Finset ι :=
  Finset.univ.filter (fun i => u₁ i = 0)

/-- `secondZeros` and `secondSupport` partition `univ`: `|secondSupport| + |secondZeros| = n`. -/
theorem secondSupport_card_add_secondZeros_card (u₁ : ι → F) :
    (secondSupport u₁).card + (secondZeros u₁).card = Fintype.card ι := by
  classical
  rw [secondSupport, secondZeros]
  have h := Finset.card_filter_add_card_filter_not (s := (Finset.univ : Finset ι))
    (p := fun i => u₁ i ≠ 0)
  have hneg : (Finset.univ.filter (fun i => ¬ u₁ i ≠ 0)) =
      (Finset.univ.filter (fun i => u₁ i = 0)) := by
    apply Finset.filter_congr
    intro i _
    simp
  rw [hneg] at h
  rw [h, Finset.card_univ]

/-- If a coordinate lies in both witness sets of two **distinct** bad combining points `γ ≠ γ'`
(both witnessed by the same `w`), then `u₁` vanishes there. -/
theorem u1_zero_of_mem_both_witness
    (u₀ u₁ w : ι → F) {γ γ' : F} (hγ : γ ≠ γ') {i : ι}
    (h : w i = u₀ i + γ • u₁ i) (h' : w i = u₀ i + γ' • u₁ i) :
    u₁ i = 0 := by
  have heq : γ • u₁ i = γ' • u₁ i := by
    have := h.symm.trans h'
    simpa using add_left_cancel this
  rw [smul_eq_mul, smul_eq_mul] at heq
  have : (γ - γ') * u₁ i = 0 := by ring_nf; linear_combination heq
  rcases mul_eq_zero.mp this with hsub | hu
  · exact absurd (sub_eq_zero.mp hsub) hγ
  · exact hu

/-- **Pairwise sharpening of the support.** If a fixed codeword `w ∈ MC` witnesses two *distinct*
bad combining points `γ ≠ γ'`, then `|secondSupport u₁| ≤ 2·δ·n`.

Proof: the witness sets `S, S'` (each `≥ (1-δ)·n`) intersect (inclusion–exclusion) in `≥ (1-2δ)·n`
coordinates, where `u₁` vanishes (`u1_zero_of_mem_both_witness`); so `S ∩ S' ⊆ secondZeros u₁` and
`|secondSupport u₁| = n - |secondZeros u₁| ≤ n - (1-2δ)·n = 2δ·n`. -/
theorem secondSupport_card_le_two_delta_of_two_witnesses
    (MC : Submodule F (ι → F)) (δ : ℝ≥0) (u₀ u₁ w : ι → F)
    {γ γ' : F} (hγ : γ ≠ γ')
    (hmem : γ ∈ mcaBadWitness (F := F) (MC : Set (ι → F)) δ u₀ u₁ w)
    (hmem' : γ' ∈ mcaBadWitness (F := F) (MC : Set (ι → F)) δ u₀ u₁ w) :
    ((secondSupport u₁).card : ℝ) ≤ 2 * (δ : ℝ) * (Fintype.card ι : ℝ) := by
  classical
  rw [mcaBadWitness, Finset.mem_filter] at hmem hmem'
  obtain ⟨S, hScard, hwline, _⟩ := hmem.2
  obtain ⟨S', hS'card, hwline', _⟩ := hmem'.2
  have hsub : S ∩ S' ⊆ secondZeros u₁ := by
    intro i hi
    rw [Finset.mem_inter] at hi
    rw [secondZeros, Finset.mem_filter]
    exact ⟨Finset.mem_univ _,
      u1_zero_of_mem_both_witness u₀ u₁ w hγ (hwline i hi.1) (hwline' i hi.2)⟩
  have hincl : (S.card : ℝ) + (S'.card : ℝ) ≤
      (Fintype.card ι : ℝ) + ((S ∩ S').card : ℝ) := by
    have h := Finset.card_union_add_card_inter S S'
    have hunion : (S ∪ S').card ≤ Fintype.card ι := by
      calc (S ∪ S').card ≤ (Finset.univ : Finset ι).card :=
            Finset.card_le_card (fun x _ => Finset.mem_univ _)
        _ = Fintype.card ι := Finset.card_univ
    have hcast : ((S ∪ S').card : ℝ) + ((S ∩ S').card : ℝ) =
        (S.card : ℝ) + (S'.card : ℝ) := by exact_mod_cast h
    have hu : ((S ∪ S').card : ℝ) ≤ (Fintype.card ι : ℝ) := by exact_mod_cast hunion
    linarith
  have hinterle : ((S ∩ S').card : ℝ) ≤ ((secondZeros u₁).card : ℝ) := by
    exact_mod_cast Finset.card_le_card hsub
  have hSlb : (1 - (δ : ℝ)) * (Fintype.card ι : ℝ) ≤ (S.card : ℝ) := by
    have hc : ((1 - δ) * Fintype.card ι : ℝ≥0) ≤ (S.card : ℝ≥0) := hScard
    have h2 : ((1 - δ : ℝ≥0) : ℝ) * (Fintype.card ι : ℝ) ≤ (S.card : ℝ) := by
      have := (NNReal.coe_le_coe.mpr hc); push_cast at this ⊢; convert this using 2
    calc (1 - (δ : ℝ)) * (Fintype.card ι : ℝ)
        ≤ ((1 - δ : ℝ≥0) : ℝ) * (Fintype.card ι : ℝ) := by
          refine mul_le_mul_of_nonneg_right ?_ (by positivity)
          rw [show ((1 - δ : ℝ≥0) : ℝ) = max (1 - (δ : ℝ)) 0 by rw [NNReal.coe_sub_def]; simp]
          exact le_max_left _ _
      _ ≤ (S.card : ℝ) := h2
  have hS'lb : (1 - (δ : ℝ)) * (Fintype.card ι : ℝ) ≤ (S'.card : ℝ) := by
    have hc : ((1 - δ) * Fintype.card ι : ℝ≥0) ≤ (S'.card : ℝ≥0) := hS'card
    have h2 : ((1 - δ : ℝ≥0) : ℝ) * (Fintype.card ι : ℝ) ≤ (S'.card : ℝ) := by
      have := (NNReal.coe_le_coe.mpr hc); push_cast at this ⊢; convert this using 2
    calc (1 - (δ : ℝ)) * (Fintype.card ι : ℝ)
        ≤ ((1 - δ : ℝ≥0) : ℝ) * (Fintype.card ι : ℝ) := by
          refine mul_le_mul_of_nonneg_right ?_ (by positivity)
          rw [show ((1 - δ : ℝ≥0) : ℝ) = max (1 - (δ : ℝ)) 0 by rw [NNReal.coe_sub_def]; simp]
          exact le_max_left _ _
      _ ≤ (S'.card : ℝ) := h2
  have hzeros_lb : (1 - 2 * (δ : ℝ)) * (Fintype.card ι : ℝ) ≤ ((secondZeros u₁).card : ℝ) := by
    nlinarith [hincl, hinterle, hSlb, hS'lb]
  have hpart : ((secondSupport u₁).card : ℝ) + ((secondZeros u₁).card : ℝ) =
      (Fintype.card ι : ℝ) := by exact_mod_cast secondSupport_card_add_secondZeros_card u₁
  nlinarith [hzeros_lb, hpart]

/-- **Sharpened per-codeword first-moment count.** For a `Submodule` code `MC` and a fixed
codeword `w ∈ MC`,

  `|mcaBadWitness w| ≤ max 1 (2·δ·n)`.

This strictly improves the in-tree `b = n` count of `mcaBadWitness_card_le_card` toward GCXK25's
sharp `b = δ·n` (within a factor of `2` and additive `1`). The `max 1` absorbs the degenerate
`≤ 1`-witness case; with `≥ 2` bad points the pairwise argument bounds the count by `2·δ·n`. -/
theorem mcaBadWitness_card_le_two_delta_mul_card
    (MC : Submodule F (ι → F)) (δ : ℝ≥0) (u₀ u₁ w : ι → F)
    (hw : w ∈ (MC : Set (ι → F))) :
    ((mcaBadWitness (F := F) (MC : Set (ι → F)) δ u₀ u₁ w).card : ℝ) ≤
      max 1 (2 * (δ : ℝ) * (Fintype.card ι : ℝ)) := by
  classical
  set W := mcaBadWitness (F := F) (MC : Set (ι → F)) δ u₀ u₁ w with hW
  rcases le_or_gt W.card 1 with hle | hgt
  · calc ((W.card : ℝ)) ≤ 1 := by exact_mod_cast hle
      _ ≤ max 1 (2 * (δ : ℝ) * (Fintype.card ι : ℝ)) := le_max_left _ _
  · obtain ⟨γ, hγ, γ', hγ', hne⟩ := Finset.one_lt_card.mp hgt
    have hsupp : ((secondSupport u₁).card : ℝ) ≤ 2 * (δ : ℝ) * (Fintype.card ι : ℝ) :=
      secondSupport_card_le_two_delta_of_two_witnesses MC δ u₀ u₁ w hne hγ hγ'
    have hcard : ((W.card : ℝ)) ≤ ((secondSupport u₁).card : ℝ) := by
      rw [hW]; exact_mod_cast mcaBadWitness_card_le_support MC δ u₀ u₁ w hw
    calc ((W.card : ℝ)) ≤ ((secondSupport u₁).card : ℝ) := hcard
      _ ≤ 2 * (δ : ℝ) * (Fintype.card ι : ℝ) := hsupp
      _ ≤ max 1 (2 * (δ : ℝ) * (Fintype.card ι : ℝ)) := le_max_right _ _

end

section Compose
variable {ι : Type} [Fintype ι] [Nonempty ι] [DecidableEq ι]
variable {F : Type} [Field F] [Fintype F] [DecidableEq F]

open CodingTheory.Bridge

/-- **Per-stack count from the in-tree per-codeword count + list-size factor.** Composing the
in-tree per-codeword bound `|mcaBadWitness w| ≤ n` with `Bridge2GCXK25`'s union-bound brick: for a
finite codeword carrier `T` that contains every codeword (`MC ⊆ T`) *and* consists only of
codewords (`T ⊆ MC`) — i.e. `T` is the finset of all codewords of `MC` — of size `≤ B_T`, we get

  `|mcaBad u| ≤ B_T · n`.

This is the fully-in-tree (first-moment) per-stack bound, with the per-codeword count `b = n`
discharged here rather than assumed. The carrier-is-codewords side condition `hTsub` is harmless:
the canonical carrier is `MC` itself (finite, since `ι → F` is finite), which trivially satisfies
both inclusions; the list-size factor `B_T = L²` then bounds the *relevant* close-codeword carrier.
The remaining gap to GCXK25's `B_T · δ · n` is the named `δ`-sharpening residual below. -/
theorem mcaBad_card_le_listFactor_mul_card
    (MC : Submodule F (ι → F)) (δ : ℝ≥0) (u₀ u₁ : ι → F)
    (T : Finset (ι → F)) (hT : ∀ w ∈ (MC : Set (ι → F)), w ∈ T)
    (hTsub : ∀ w ∈ T, w ∈ (MC : Set (ι → F)))
    {B_T : ℝ} (hb_card : (T.card : ℝ) ≤ B_T) :
    ((mcaBad (F := F) (MC : Set (ι → F)) δ u₀ u₁).card : ℝ) ≤ B_T * (Fintype.card ι : ℝ) := by
  refine mcaBad_card_le_listFactor_mul_perCodeword (MC : Set (ι → F)) δ u₀ u₁ T hT
    (by positivity) hb_card ?_
  intro w hw
  exact mcaBadWitness_card_le_card_real MC δ u₀ u₁ w (hTsub w hw)

/-- **Sharpened in-tree per-stack count `|mcaBad u| ≤ B_T · max 1 (2·δ·n)`.** This composes the
pairwise sharpened per-codeword count (`mcaBadWitness_card_le_two_delta_mul_card`) with the
union-bound brick, giving a per-stack bound a factor of `≈2` from GCXK25's `B_T · δ · n` — strictly
better than the `B_T · n` of `mcaBad_card_le_listFactor_mul_card`, with no external hypothesis. -/
theorem mcaBad_card_le_listFactor_mul_two_delta_card
    (MC : Submodule F (ι → F)) (δ : ℝ≥0) (u₀ u₁ : ι → F)
    (T : Finset (ι → F)) (hT : ∀ w ∈ (MC : Set (ι → F)), w ∈ T)
    (hTsub : ∀ w ∈ T, w ∈ (MC : Set (ι → F)))
    {B_T : ℝ} (hb_card : (T.card : ℝ) ≤ B_T) :
    ((mcaBad (F := F) (MC : Set (ι → F)) δ u₀ u₁).card : ℝ) ≤
      B_T * max 1 (2 * (δ : ℝ) * (Fintype.card ι : ℝ)) := by
  refine mcaBad_card_le_listFactor_mul_perCodeword (MC : Set (ι → F)) δ u₀ u₁ T hT
    (le_trans zero_le_one (le_max_left _ _)) hb_card ?_
  intro w hw
  exact mcaBadWitness_card_le_two_delta_mul_card MC δ u₀ u₁ w (hTsub w hw)

/-- **Sharpened in-tree `ε_mca` bound.** With carrier `T` containing exactly the codewords of `MC`
of size `≤ B_T`,

  `ε_mca(MC, δ) ≤ ENNReal.ofReal ((B_T · max 1 (2·δ·n)) / |F|)`.

The fully in-tree (`sorry`-free, axiom-clean) sharpening of `epsMCA_le_ofReal_of_listFactor`:
the per-codeword count is `max 1 (2·δ·n)` rather than `n`, a factor `≈2` from GCXK25's `δ·n`. -/
theorem epsMCA_le_ofReal_of_listFactor_two_delta
    (MC : Submodule F (ι → F)) (δ : ℝ≥0) {B_T : ℝ}
    (T : Finset (ι → F))
    (hT : ∀ w ∈ (MC : Set (ι → F)), w ∈ T) (hTsub : ∀ w ∈ T, w ∈ (MC : Set (ι → F)))
    (hcard : (T.card : ℝ) ≤ B_T) :
    epsMCA (F := F) (A := F) (MC : Set (ι → F)) δ ≤
      ENNReal.ofReal
        ((B_T * max 1 (2 * (δ : ℝ) * (Fintype.card ι : ℝ))) / Fintype.card F) := by
  refine epsMCA_le_ofReal_of_forall_mcaBad_card_le (MC : Set (ι → F)) δ ?_
  intro u
  exact mcaBad_card_le_listFactor_mul_two_delta_card MC δ (u 0) (u 1) T hT hTsub hcard

/-- **`ε_mca` bound from the in-tree first-moment count + a list-size factor.** Given a single
codeword carrier `T` (containing exactly the codewords of `MC`) of size `≤ B_T`,

  `ε_mca(MC, δ) ≤ ENNReal.ofReal ((B_T · n) / |F|)`.

This is the fully-in-tree (`sorry`-free, axiom-clean) `ε_mca` bound: the per-codeword first-moment
count `b = n` is now *proven* (`mcaBadWitness_card_le_card`), so the only remaining external input
is the list-size factor `B_T` bounding the carrier (e.g. `B_T = L²`, GCXK25's `l ≤ L²`). It
composes `mcaBad_card_le_listFactor_mul_card` with the in-tree supremum-to-count glue
`ProximityGap.epsMCA_le_ofReal_of_forall_mcaBad_card_le`. The carrier conditions are
stack-independent, so a single `T` (e.g. `MC` itself, finite since `ι → F` is) serves every
stack. -/
theorem epsMCA_le_ofReal_of_listFactor
    (MC : Submodule F (ι → F)) (δ : ℝ≥0) {B_T : ℝ}
    (T : Finset (ι → F))
    (hT : ∀ w ∈ (MC : Set (ι → F)), w ∈ T) (hTsub : ∀ w ∈ T, w ∈ (MC : Set (ι → F)))
    (hcard : (T.card : ℝ) ≤ B_T) :
    epsMCA (F := F) (A := F) (MC : Set (ι → F)) δ ≤
      ENNReal.ofReal ((B_T * (Fintype.card ι : ℝ)) / Fintype.card F) := by
  refine epsMCA_le_ofReal_of_forall_mcaBad_card_le (MC : Set (ι → F)) δ ?_
  intro u
  exact mcaBad_card_le_listFactor_mul_card MC δ (u 0) (u 1) T hT hTsub hcard

/-- **The single named GKL24 first-moment residual.** This is the *one* genuinely-external
ingredient that the in-tree substrate cannot supply: the sharpening of the per-codeword count from
`|support u₁| ≤ n` (proven above) to GCXK25's agree-domain count `b`, *uniformly* over the relevant
close-codeword carrier. Concretely: there is a list-size factor `B_T` and a per-codeword count `b`
such that every stack `u` admits a carrier `T u` of codewords of size `≤ B_T`, each codeword
`w ∈ T u` witnessing at most `b` bad combining points.

The count `b` is left abstract precisely because GCXK25's first-moment value is `b = p·n` with `p`
the **list-decoding** radius of `Λ(C, p) ≤ L` — *not* the (Johnson-lifted) MCA radius `δ` at which
`mcaBadWitness` is taken. Decoupling `b` from `δ` keeps the statement faithful: the caller
instantiates `b := δ_list · n` and `B_T := L²` to obtain T5.1's `L²·δ·n` first-moment summand.

This isolates exactly [GKL24]'s maximal-correlated-agree-domain intersection content (GCXK25's
`|Bad¹| ≤ p·n`): a *global* charging argument over the line family `{u₀ + γ·u₁}` that a single
fixed codeword `w` in isolation does not determine (the in-tree count only gives `b = n`). -/
def GKL24FirstMomentResidual (MC : Submodule F (ι → F)) (δ : ℝ≥0) (B_T b : ℝ) : Prop :=
  ∀ u : WordStack F (Fin 2) ι,
    ∃ T : Finset (ι → F), (∀ w ∈ (MC : Set (ι → F)), w ∈ T) ∧ (T.card : ℝ) ≤ B_T ∧
      ∀ w ∈ T, ((mcaBadWitness (F := F) (MC : Set (ι → F)) δ (u 0) (u 1) w).card : ℝ) ≤ b

/-- **In-tree relaxed instance of the GKL24 first-moment residual.** Taking `T` to be the finite
set of all codewords of `MC`, the single-codeword determinacy bound above gives the residual with
carrier size `|F|^n` and per-codeword count `n`.

This is deliberately the relaxed `b = n` specialization, not GCXK25's external `b = δ_list · n`
charging bound. It is useful because downstream arguments that only need the residual interface,
but can tolerate the weaker first-moment count, no longer need to carry any paper hypothesis. -/
theorem GKL24FirstMomentResidual_inTree_card
    (MC : Submodule F (ι → F)) (δ : ℝ≥0) :
    GKL24FirstMomentResidual MC δ
      (Fintype.card (ι → F) : ℝ) (Fintype.card ι : ℝ) := by
  classical
  intro u
  refine ⟨Finset.univ.filter (fun w : ι → F => w ∈ (MC : Set (ι → F))), ?_, ?_, ?_⟩
  · intro w hw
    rw [Finset.mem_filter]
    exact ⟨Finset.mem_univ _, hw⟩
  · exact_mod_cast Finset.card_filter_le Finset.univ (fun w : ι → F => w ∈ (MC : Set (ι → F)))
  · intro w hw
    rw [Finset.mem_filter] at hw
    exact mcaBadWitness_card_le_card_real MC δ (u 0) (u 1) w hw.2

/-- **Per-stack bad-`γ` count from the GKL24 first-moment residual.**
Given `GKL24FirstMomentResidual MC δ B_T b`, every concrete stack `u` has at most `B_T · b`
bad combining scalars:

  `|mcaBad MC δ (u 0) (u 1)| ≤ B_T · b`.

This is the count-level bridge immediately below the final `ε_mca` supremum. It keeps the
remaining GKL24/GCXK25 content at the exact `mcaBad` layer, before division by `|F|` and before
taking the supremum over stacks. -/
theorem mcaBad_card_le_of_gkl24_residual
    (MC : Submodule F (ι → F)) (δ : ℝ≥0) {B_T b : ℝ} (hb0 : 0 ≤ b)
    (hres : GKL24FirstMomentResidual MC δ B_T b) (u : WordStack F (Fin 2) ι) :
    ((mcaBad (F := F) (MC : Set (ι → F)) δ (u 0) (u 1)).card : ℝ) ≤ B_T * b := by
  obtain ⟨T, hT, hcard, hper⟩ := hres u
  exact mcaBad_card_le_listFactor_mul_perCodeword (MC : Set (ι → F)) δ (u 0) (u 1) T hT
    hb0 hcard hper

/-- **Per-stack probability bound from the GKL24 first-moment residual.**
This is the probability-level companion to `mcaBad_card_le_of_gkl24_residual`, obtained by
dividing the per-stack bad-`γ` count by the uniform choice space `F`. -/
theorem mcaEvent_prob_le_ofReal_of_gkl24_residual
    (MC : Submodule F (ι → F)) (δ : ℝ≥0) {B_T b : ℝ} (hb0 : 0 ≤ b)
    (hres : GKL24FirstMomentResidual MC δ B_T b) (u : WordStack F (Fin 2) ι) :
    Pr_{let γ ← $ᵖ F}[mcaEvent (F := F) (MC : Set (ι → F)) δ (u 0) (u 1) γ] ≤
      ENNReal.ofReal ((B_T * b) / Fintype.card F) :=
  mcaEvent_prob_le_of_mcaBad_card_le (MC : Set (ι → F)) δ (u 0) (u 1)
    (mcaBad_card_le_of_gkl24_residual MC δ hb0 hres u)

/-- **Alias for the per-stack bad-`γ` bound in the canonical ABF26 T5.1 parameter shape.** This
is the same theorem as `mcaBad_card_le_of_gkl24_residual`, but with the target bound written as
`L² · δ_list · n` by the caller through `B_T` and `b`.

The theorem is intentionally conditional: supplying the residual at
`B_T := L^2`, `b := δ_list · n` is exactly the still-open GKL24/GCXK25 first-moment theorem. -/
theorem mcaBad_card_le_t51_firstMoment_of_gkl24_residual
    (MC : Submodule F (ι → F)) (δ : ℝ≥0) {Lsq δn : ℝ} (hδn0 : 0 ≤ δn)
    (hres : GKL24FirstMomentResidual MC δ Lsq δn)
    (u : WordStack F (Fin 2) ι) :
    ((mcaBad (F := F) (MC : Set (ι → F)) δ (u 0) (u 1)).card : ℝ) ≤ Lsq * δn :=
  mcaBad_card_le_of_gkl24_residual MC δ hδn0 hres u

/-- **Conditional strengthening: the `B_T · b` first-moment shape from the GKL24 residual.**
Given the single named residual `GKL24FirstMomentResidual MC δ B_T b` with `b ≥ 0`,

  `ε_mca(MC, δ) ≤ ENNReal.ofReal ((B_T · b) / |F|)`.

Instantiating `B_T = L²` and `b = δ_list · n` (GCXK25's `|Bad¹| ≤ p·n` first-moment count, `p` the
list-decoding radius) gives the `L²·δ·n` summand of ABF26 T5.1; adding the in-tree second-moment
`1/η` summand (`GCXK25SecondMoment.card_lt_one_div_of_second_moment_rs`) recovers the full
`(L²·δ·n + 1/η)/|F|` bound. The proof is the in-tree union-bound + supremum-to-count glue; the
*only* unproven input is the named residual. -/
theorem epsMCA_le_ofReal_of_gkl24_residual
    (MC : Submodule F (ι → F)) (δ : ℝ≥0) {B_T b : ℝ} (hb0 : 0 ≤ b)
    (hres : GKL24FirstMomentResidual MC δ B_T b) :
    epsMCA (F := F) (A := F) (MC : Set (ι → F)) δ ≤
      ENNReal.ofReal ((B_T * b) / Fintype.card F) := by
  refine epsMCA_le_ofReal_of_forall_mcaBad_card_le (MC : Set (ι → F)) δ ?_
  intro u
  exact mcaBad_card_le_of_gkl24_residual MC δ hb0 hres u

/-- **Fully in-tree `ε_mca` first-moment relaxation.** This is the residual corollary obtained from
`GKL24FirstMomentResidual_inTree_card`: without any GKL24/GCXK25 hypothesis,

  `ε_mca(MC, δ) ≤ ENNReal.ofReal ((|F|^n · n) / |F|)`.

The bound is intentionally crude; its role is to close the residual interface in settings where
one only needs a finite first-moment estimate. -/
theorem epsMCA_le_ofReal_inTree_firstMoment_card
    (MC : Submodule F (ι → F)) (δ : ℝ≥0) :
    epsMCA (F := F) (A := F) (MC : Set (ι → F)) δ ≤
      ENNReal.ofReal
        (((Fintype.card (ι → F) : ℝ) * (Fintype.card ι : ℝ)) / Fintype.card F) :=
  epsMCA_le_ofReal_of_gkl24_residual MC δ (by positivity)
    (GKL24FirstMomentResidual_inTree_card MC δ)

end Compose

end ProximityGap

/- Axiom audit for the GKL24 first-moment bridge surfaces.  These should remain
kernel-clean apart from the standard Lean foundations (`propext`, `Classical.choice`,
`Quot.sound`). -/
#print axioms ProximityGap.GKL24FirstMomentResidual_inTree_card
#print axioms ProximityGap.mcaBad_card_le_of_gkl24_residual
#print axioms ProximityGap.mcaEvent_prob_le_ofReal_of_gkl24_residual
#print axioms ProximityGap.mcaBad_card_le_t51_firstMoment_of_gkl24_residual
#print axioms ProximityGap.epsMCA_le_ofReal_of_gkl24_residual
#print axioms ProximityGap.epsMCA_le_ofReal_inTree_firstMoment_card
#print axioms ProximityGap.u1_zero_of_mem_both_witness
#print axioms ProximityGap.secondSupport_card_le_two_delta_of_two_witnesses
#print axioms ProximityGap.mcaBadWitness_card_le_two_delta_mul_card
#print axioms ProximityGap.mcaBad_card_le_listFactor_mul_two_delta_card
#print axioms ProximityGap.epsMCA_le_ofReal_of_listFactor_two_delta

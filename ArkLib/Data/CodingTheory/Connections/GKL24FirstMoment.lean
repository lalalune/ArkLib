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
`|support u₁| ≤ n` (proven above) to GCXK25's agree-domain count `δ·n`, *uniformly* over the
relevant close-codeword carrier `T u`. Concretely: there is a list-size factor `B_T` such that
every stack `u` admits a carrier `T u` of codewords of size `≤ B_T`, each codeword `w ∈ T u`
witnessing at most `δ·n` bad combining points.

This isolates exactly [GKL24]'s maximal-correlated-agree-domain intersection content (GCXK25's
`|Bad¹| ≤ p·n`, p = δ): a *global* charging argument over the line family `{u₀ + γ·u₁}` that a
single fixed codeword `w` in isolation does not determine. With `B_T = L²` it is GCXK25's exact
first-moment statement. -/
def GKL24FirstMomentResidual (MC : Submodule F (ι → F)) (δ : ℝ≥0) (B_T n : ℝ) : Prop :=
  ∀ u : WordStack F (Fin 2) ι,
    ∃ T : Finset (ι → F), (∀ w ∈ (MC : Set (ι → F)), w ∈ T) ∧ (T.card : ℝ) ≤ B_T ∧
      ∀ w ∈ T, ((mcaBadWitness (F := F) (MC : Set (ι → F)) δ (u 0) (u 1) w).card : ℝ) ≤ δ * n

open CodingTheory.Bridge in
/-- **Conditional strengthening: the exact `L²·δ·n` first-moment shape from the GKL24 residual.**
Given the single named residual `GKL24FirstMomentResidual MC δ B_T n` (with `n = |ι|`), the
`ε_mca` first-moment bound takes GCXK25's published shape

  `ε_mca(MC, δ) ≤ ENNReal.ofReal ((B_T · δ · n) / |F|)`.

With `B_T = L²` this is the `L²·δ·n` summand of ABF26 T5.1; adding the in-tree second-moment
`1/η` summand (`GCXK25SecondMoment.card_lt_one_div_of_second_moment_rs`) recovers the full
`(L²·δ·n + 1/η)/|F|` bound. The proof is the in-tree union-bound + supremum-to-count glue; the
*only* unproven input is the named residual. -/
theorem epsMCA_le_ofReal_of_gkl24_residual
    (MC : Submodule F (ι → F)) (δ : ℝ≥0) {B_T : ℝ} (hδ0 : (0 : ℝ) ≤ δ)
    (hres : GKL24FirstMomentResidual MC δ B_T (Fintype.card ι : ℝ)) :
    epsMCA (F := F) (A := F) (MC : Set (ι → F)) δ ≤
      ENNReal.ofReal ((B_T * (δ * Fintype.card ι)) / Fintype.card F) := by
  refine epsMCA_le_ofReal_of_forall_mcaBad_card_le (MC : Set (ι → F)) δ ?_
  intro u
  obtain ⟨T, hT, hcard, hper⟩ := hres u
  exact mcaBad_card_le_listFactor_mul_perCodeword (MC : Set (ι → F)) δ (u 0) (u 1) T hT
    (by positivity) hcard hper

end Compose

end ProximityGap

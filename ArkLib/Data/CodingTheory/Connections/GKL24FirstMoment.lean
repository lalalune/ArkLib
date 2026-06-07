/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/

import ArkLib.ToMathlib.Bridge2GCXK25
import ArkLib.ToMathlib.BridgeListDecodingCA
import ArkLib.ToMathlib.GreedyDisjointCover
import ArkLib.ToMathlib.MCAFirstMomentArithBricks
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

/-- The agreement domain of the line `u₀ + γ • u₁` with a codeword `w`. GCXK/GKL maximal-domain
arguments reason about strict expansions of these domains over a fixed correlated-agreement core.
-/
def lineAgreeSet (u₀ u₁ w : ι → F) (γ : F) : Finset ι :=
  Finset.univ.filter (fun i => w i = u₀ i + γ • u₁ i)

/-- The petal of a line-agreement set outside a candidate maximal domain `D`. The GKL/GCXK
sunflower lemma supplies pairwise disjoint nonempty petals for distinct bad scalars above the
same maximal domain; the cardinality consumer for such petals is
`badScalars_card_le_radius_mul_card_of_large_domain_disjoint_petals`. -/
def linePetal (D : Finset ι) (u₀ u₁ w : ι → F) (γ : F) : Finset ι :=
  lineAgreeSet u₀ u₁ w γ \ D

/-- A correlated-agreement domain at radius `p`: a large coordinate set on which the stack
`(u₀,u₁)` jointly agrees with a codeword pair from `MC`. GCXK/GKL maximal domains are maximal
sets satisfying this predicate. -/
def corrAgreeDomain (MC : Submodule F (ι → F)) (p : ℝ≥0) (u₀ u₁ : ι → F)
    (D : Finset ι) : Prop :=
  ((1 - p) * Fintype.card ι : ℝ≥0) ≤ (D.card : ℝ≥0) ∧
    pairJointAgreesOn (MC : Set (ι → F)) D u₀ u₁

/-- A maximal correlated-agreement domain: no larger correlated-agreement domain strictly
contains it. This explicit formulation avoids relying on a particular `Maximal` API and matches
the inclusion argument needed for the GCXK/GKL sunflower step. -/
def maxCorrAgreeDomain (MC : Submodule F (ι → F)) (p : ℝ≥0) (u₀ u₁ : ι → F)
    (D : Finset ι) : Prop :=
  corrAgreeDomain MC p u₀ u₁ D ∧
    ∀ E : Finset ι, D ⊆ E → corrAgreeDomain MC p u₀ u₁ E → E ⊆ D

theorem mem_lineAgreeSet_iff (u₀ u₁ w : ι → F) (γ : F) (i : ι) :
    i ∈ lineAgreeSet u₀ u₁ w γ ↔ w i = u₀ i + γ • u₁ i := by
  simp [lineAgreeSet]

/-- A scalar in `mcaBadWitness w` gives a large line-agreement set for `w`. This extracts the
paper-side agree-domain object from the existing ArkLib witness definition. -/
theorem lineAgreeSet_card_ge_of_mem_mcaBadWitness
    (MC : Submodule F (ι → F)) (δ : ℝ≥0) (u₀ u₁ w : ι → F) {γ : F}
    (hγ : γ ∈ mcaBadWitness (F := F) (MC : Set (ι → F)) δ u₀ u₁ w) :
    ((1 - δ) * Fintype.card ι : ℝ≥0) ≤
      ((lineAgreeSet u₀ u₁ w γ).card : ℝ≥0) := by
  classical
  rw [mcaBadWitness, Finset.mem_filter] at hγ
  obtain ⟨S, hScard, hwline, _hpair⟩ := hγ.2
  have hsub : S ⊆ lineAgreeSet u₀ u₁ w γ := by
    intro i hi
    rw [mem_lineAgreeSet_iff]
    exact hwline i hi
  exact le_trans hScard (by exact_mod_cast Finset.card_le_card hsub)

/-- A strict expansion `D ⊂ lineAgreeSet ...` has a nonempty petal outside `D`. This is the
nonemptiness input consumed by the disjoint-petal cardinality wrapper. -/
theorem linePetal_nonempty_of_ssubset_lineAgreeSet
    {D : Finset ι} {u₀ u₁ w : ι → F} {γ : F}
    (hstrict : D ⊂ lineAgreeSet u₀ u₁ w γ) :
    (linePetal D u₀ u₁ w γ).Nonempty := by
  classical
  have hnot : ¬ lineAgreeSet u₀ u₁ w γ ⊆ D := by
    intro hsub
    exact hstrict.2 hsub
  rw [Finset.not_subset] at hnot
  obtain ⟨i, hiA, hiD⟩ := hnot
  exact ⟨i, Finset.mem_sdiff.mpr ⟨hiA, hiD⟩⟩

/-- A line petal is always contained in the complement of its core domain. -/
theorem linePetal_subset_compl (D : Finset ι) (u₀ u₁ w : ι → F) (γ : F) :
    linePetal D u₀ u₁ w γ ⊆ (Finset.univ \ D) := by
  intro i hi
  rw [linePetal, Finset.mem_sdiff] at hi
  exact Finset.mem_sdiff.mpr ⟨Finset.mem_univ i, hi.2⟩

/-- If two line-agreement sets intersect exactly in `D`, their petals outside `D` are disjoint.
This is the set-theoretic final step in the GCXK/GKL sunflower accounting once maximality has
identified the common core. -/
theorem linePetal_disjoint_of_inter_lineAgreeSet_eq
    {D : Finset ι} {u₀ u₁ wγ wγ' : ι → F} {γ γ' : F}
    (hcore :
      lineAgreeSet u₀ u₁ wγ γ ∩ lineAgreeSet u₀ u₁ wγ' γ' = D) :
    Disjoint (linePetal D u₀ u₁ wγ γ) (linePetal D u₀ u₁ wγ' γ') := by
  classical
  refine Finset.disjoint_left.mpr ?_
  intro i hiγ hiγ'
  rw [linePetal, Finset.mem_sdiff] at hiγ hiγ'
  have hiD : i ∈ D := by
    rw [← hcore, Finset.mem_inter]
    exact ⟨hiγ.1, hiγ'.1⟩
  exact hiγ.2 hiD

/-- **Bonferroni lower bound for line-agreement intersections.**  If two line-agreement domains
have real cardinality lower bounds `a` and `b`, then their intersection has size at least
`a + b - n`. This is the arithmetic bridge used to instantiate the large-intersection hypothesis
in the GCXK/GKL maximal-domain step once the paper parameters fix the two individual domain
thresholds. -/
theorem lineAgreeSet_inter_card_ge_of_card_ge
    (u₀ u₁ wγ wγ' : ι → F) (γ γ' : F) {a b : ℝ}
    (hγ : a ≤ ((lineAgreeSet u₀ u₁ wγ γ).card : ℝ))
    (hγ' : b ≤ ((lineAgreeSet u₀ u₁ wγ' γ').card : ℝ)) :
    a + b - (Fintype.card ι : ℝ) ≤
      (((lineAgreeSet u₀ u₁ wγ γ ∩ lineAgreeSet u₀ u₁ wγ' γ').card : ℕ) : ℝ) := by
  classical
  let A : Finset ι := lineAgreeSet u₀ u₁ wγ γ
  let B : Finset ι := lineAgreeSet u₀ u₁ wγ' γ'
  change a + b - (Fintype.card ι : ℝ) ≤ ((A ∩ B).card : ℝ)
  have hA : a ≤ (A.card : ℝ) := by simpa [A] using hγ
  have hB : b ≤ (B.card : ℝ) := by simpa [B] using hγ'
  have hincl :
      (A.card : ℝ) + (B.card : ℝ) ≤
        (Fintype.card ι : ℝ) + ((A ∩ B).card : ℝ) :=
    Finset.card_add_card_le_card_univ_add_card_inter A B
  nlinarith

/-- **Large line-agreement intersections from two bad witnesses.** If two line-agreement domains
come from bad-witness memberships at MCA radius `δ`, and `2 * δ ≤ p`, then Bonferroni gives the
large-intersection hypothesis required by the maximal correlated-agreement-domain residual.

This removes one recurring paper-side obligation from future max-corr residual producers: once
the Johnson-lifted MCA radius is known to satisfy `2δ_mca ≤ p`, pairwise intersections are
automatic from the existing witness-size clauses. -/
theorem lineAgreeSet_inter_card_ge_of_mem_mcaBadWitness
    (MC : Submodule F (ι → F)) (δ p : ℝ≥0) (u₀ u₁ w w' : ι → F)
    (hp_le_one : p ≤ 1)
    (hδp : 2 * (δ : ℝ) ≤ (p : ℝ))
    {γ γ' : F}
    (hγ : γ ∈ mcaBadWitness (F := F) (MC : Set (ι → F)) δ u₀ u₁ w)
    (hγ' : γ' ∈ mcaBadWitness (F := F) (MC : Set (ι → F)) δ u₀ u₁ w') :
    ((1 - p) * Fintype.card ι : ℝ≥0) ≤
      (((lineAgreeSet u₀ u₁ w γ ∩ lineAgreeSet u₀ u₁ w' γ').card : ℕ) : ℝ≥0) := by
  have hγ_card_nn :=
    lineAgreeSet_card_ge_of_mem_mcaBadWitness MC δ u₀ u₁ w hγ
  have hγ'_card_nn :=
    lineAgreeSet_card_ge_of_mem_mcaBadWitness MC δ u₀ u₁ w' hγ'
  have hγ_card :
      (1 - (δ : ℝ)) * (Fintype.card ι : ℝ) ≤
        ((lineAgreeSet u₀ u₁ w γ).card : ℝ) := by
    have h2 :
        (((1 - δ : ℝ≥0) : ℝ) * (Fintype.card ι : ℝ)) ≤
          ((lineAgreeSet u₀ u₁ w γ).card : ℝ) := by
      exact_mod_cast hγ_card_nn
    exact (NNReal.coe_one_sub_mul_le δ (by positivity)).trans h2
  have hγ'_card :
      (1 - (δ : ℝ)) * (Fintype.card ι : ℝ) ≤
        ((lineAgreeSet u₀ u₁ w' γ').card : ℝ) := by
    have h2 :
        (((1 - δ : ℝ≥0) : ℝ) * (Fintype.card ι : ℝ)) ≤
          ((lineAgreeSet u₀ u₁ w' γ').card : ℝ) := by
      exact_mod_cast hγ'_card_nn
    exact (NNReal.coe_one_sub_mul_le δ (by positivity)).trans h2
  have hbon :
      (1 - (δ : ℝ)) * (Fintype.card ι : ℝ) +
          (1 - (δ : ℝ)) * (Fintype.card ι : ℝ) -
            (Fintype.card ι : ℝ) ≤
        (((lineAgreeSet u₀ u₁ w γ ∩ lineAgreeSet u₀ u₁ w' γ').card : ℕ) : ℝ) :=
    lineAgreeSet_inter_card_ge_of_card_ge u₀ u₁ w w' γ γ' hγ_card hγ'_card
  have hp_real :
      (((1 - p : ℝ≥0) : ℝ) * (Fintype.card ι : ℝ)) =
        (1 - (p : ℝ)) * (Fintype.card ι : ℝ) := by
    rw [NNReal.coe_sub hp_le_one, NNReal.coe_one]
  apply NNReal.coe_le_coe.mp
  simp only [NNReal.coe_mul, NNReal.coe_natCast]
  rw [hp_real]
  have hnpos : (0 : ℝ) < (Fintype.card ι : ℝ) := by
    exact_mod_cast Fintype.card_pos_iff.mpr (inferInstance : Nonempty ι)
  nlinarith [hbon, hδp, hnpos.le]

/-- **Two line-agreement domains intersect in a correlated-agreement domain.** If distinct
scalars `γ ≠ γ'` make codewords `wγ,wγ' ∈ MC` agree with the same stack lines on their respective
domains, then on the intersection one can solve the two equations for codewords `v₀,v₁ ∈ MC`
agreeing with `u₀,u₁`. This is the algebraic core behind the GCXK/GKL maximal-domain
intersection step. -/
theorem pairJointAgreesOn_inter_lineAgreeSet_of_ne
    (MC : Submodule F (ι → F)) (u₀ u₁ wγ wγ' : ι → F) {γ γ' : F}
    (hne : γ ≠ γ') (hwγ : wγ ∈ (MC : Set (ι → F))) (hwγ' : wγ' ∈ (MC : Set (ι → F))) :
    pairJointAgreesOn (MC : Set (ι → F))
      (lineAgreeSet u₀ u₁ wγ γ ∩ lineAgreeSet u₀ u₁ wγ' γ') u₀ u₁ := by
  classical
  let v₁ : ι → F := (γ - γ')⁻¹ • (wγ - wγ')
  let v₀ : ι → F := wγ - γ • v₁
  have hsub_ne : γ - γ' ≠ 0 := sub_ne_zero.mpr hne
  have hv₁_mem : v₁ ∈ (MC : Set (ι → F)) := by
    exact MC.smul_mem _ (MC.sub_mem hwγ hwγ')
  have hv₀_mem : v₀ ∈ (MC : Set (ι → F)) := by
    exact MC.sub_mem hwγ (MC.smul_mem γ hv₁_mem)
  refine ⟨v₀, hv₀_mem, v₁, hv₁_mem, ?_⟩
  intro i hi
  rw [Finset.mem_inter, mem_lineAgreeSet_iff, mem_lineAgreeSet_iff] at hi
  have hdiff : wγ i - wγ' i = (γ - γ') * u₁ i := by
    rw [hi.1, hi.2]
    simp [smul_eq_mul]
    ring
  have hv₁_i : v₁ i = u₁ i := by
    calc v₁ i = (γ - γ')⁻¹ * (wγ i - wγ' i) := by
          simp [v₁, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
      _ = (γ - γ')⁻¹ * ((γ - γ') * u₁ i) := by rw [hdiff]
      _ = u₁ i := by rw [← mul_assoc, inv_mul_cancel₀ hsub_ne, one_mul]
  have hv₀_i : v₀ i = u₀ i := by
    calc v₀ i = wγ i - γ * v₁ i := by
          simp [v₀, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
      _ = (u₀ i + γ * u₁ i) - γ * u₁ i := by
          rw [hi.1, hv₁_i]
          simp [smul_eq_mul]
      _ = u₀ i := by ring
  exact ⟨hv₀_i, hv₁_i⟩

/-- Maximality identifies any larger correlated-agreement domain containing `D` with `D`
itself. -/
theorem maxCorrAgreeDomain.eq_of_subset
    {MC : Submodule F (ι → F)} {p : ℝ≥0} {u₀ u₁ : ι → F} {D E : Finset ι}
    (hD : maxCorrAgreeDomain MC p u₀ u₁ D)
    (hsub : D ⊆ E) (hE : corrAgreeDomain MC p u₀ u₁ E) :
    E = D :=
  Finset.Subset.antisymm (hD.2 E hsub hE) hsub

/-- **Maximal-domain intersection identification.** If a maximal correlated-agreement domain
`D` lies inside two line-agreement domains and their intersection is large enough, then the
intersection is exactly `D`. The algebraic fact that the intersection is a joint-agreement domain
is supplied by `pairJointAgreesOn_inter_lineAgreeSet_of_ne`; maximality then rules out a strict
expansion. -/
theorem inter_lineAgreeSet_eq_of_maxCorrAgreeDomain
    (MC : Submodule F (ι → F)) (p : ℝ≥0) (D : Finset ι)
    (u₀ u₁ wγ wγ' : ι → F) {γ γ' : F}
    (hD : maxCorrAgreeDomain MC p u₀ u₁ D)
    (hDγ : D ⊆ lineAgreeSet u₀ u₁ wγ γ)
    (hDγ' : D ⊆ lineAgreeSet u₀ u₁ wγ' γ')
    (hIlarge :
      ((1 - p) * Fintype.card ι : ℝ≥0) ≤
        (((lineAgreeSet u₀ u₁ wγ γ ∩ lineAgreeSet u₀ u₁ wγ' γ').card : ℕ) : ℝ≥0))
    (hne : γ ≠ γ') (hwγ : wγ ∈ (MC : Set (ι → F))) (hwγ' : wγ' ∈ (MC : Set (ι → F))) :
    lineAgreeSet u₀ u₁ wγ γ ∩ lineAgreeSet u₀ u₁ wγ' γ' = D := by
  classical
  have hsub :
      D ⊆ lineAgreeSet u₀ u₁ wγ γ ∩ lineAgreeSet u₀ u₁ wγ' γ' := by
    intro i hi
    exact Finset.mem_inter.mpr ⟨hDγ hi, hDγ' hi⟩
  have hI : corrAgreeDomain MC p u₀ u₁
      (lineAgreeSet u₀ u₁ wγ γ ∩ lineAgreeSet u₀ u₁ wγ' γ') := by
    exact ⟨hIlarge, pairJointAgreesOn_inter_lineAgreeSet_of_ne MC u₀ u₁ wγ wγ' hne hwγ hwγ'⟩
  exact maxCorrAgreeDomain.eq_of_subset hD hsub hI

/-- If two line-agreement domains intersect exactly in `D`, then their petals outside `D` are
disjoint. -/
theorem linePetal_disjoint_of_inter_eq
    {D : Finset ι} {u₀ u₁ wγ wγ' : ι → F} {γ γ' : F}
    (hinter : lineAgreeSet u₀ u₁ wγ γ ∩ lineAgreeSet u₀ u₁ wγ' γ' = D) :
    Disjoint (linePetal D u₀ u₁ wγ γ) (linePetal D u₀ u₁ wγ' γ') := by
  classical
  rw [Finset.disjoint_left]
  intro i hi hi'
  rw [linePetal, Finset.mem_sdiff] at hi hi'
  have hiD : i ∈ D := by
    rw [← hinter]
    exact Finset.mem_inter.mpr ⟨hi.1, hi'.1⟩
  exact hi.2 hiD

/-- **Pairwise disjoint line petals from a maximal correlated-agreement domain.**  If a maximal
domain `D` is contained in every selected line-agreement domain, and every pairwise intersection
is large enough to be a correlated-agreement domain, then maximality identifies those
intersections with `D`; the petals outside `D` are therefore pairwise disjoint. -/
theorem linePetal_pairwise_disjoint_of_maxCorrAgreeDomain
    (MC : Submodule F (ι → F)) (p : ℝ≥0) (D : Finset ι)
    (u₀ u₁ : ι → F) (wOf : F → ι → F) (Γ : Finset F)
    (hD : maxCorrAgreeDomain MC p u₀ u₁ D)
    (hDγ : ∀ γ ∈ Γ, D ⊆ lineAgreeSet u₀ u₁ (wOf γ) γ)
    (hIlarge : ∀ γ ∈ Γ, ∀ γ' ∈ Γ, γ ≠ γ' →
      ((1 - p) * Fintype.card ι : ℝ≥0) ≤
        (((lineAgreeSet u₀ u₁ (wOf γ) γ ∩
            lineAgreeSet u₀ u₁ (wOf γ') γ').card : ℕ) : ℝ≥0))
    (hw : ∀ γ ∈ Γ, wOf γ ∈ (MC : Set (ι → F))) :
    (Γ : Set F).Pairwise (fun γ γ' =>
      Disjoint (linePetal D u₀ u₁ (wOf γ) γ)
        (linePetal D u₀ u₁ (wOf γ') γ')) := by
  classical
  intro γ hγ γ' hγ' hne
  exact
    linePetal_disjoint_of_inter_eq
      (inter_lineAgreeSet_eq_of_maxCorrAgreeDomain MC p D u₀ u₁ (wOf γ) (wOf γ')
        hD (hDγ γ hγ) (hDγ γ' hγ') (hIlarge γ hγ γ' hγ' hne)
        hne (hw γ hγ) (hw γ' hγ'))

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

/-- **Cover-based per-stack first-moment count.**  This is the union-bound bridge with the
future GCXK/GKL carrier shape: the carrier `T` only has to cover the actual bad scalars through
the per-codeword witness sets, rather than contain every codeword of `MC`.

If

`mcaBad(MC, δ, u₀, u₁) ⊆ ⋃ w ∈ T, mcaBadWitness(MC, δ, u₀, u₁, w)`,

`|T| ≤ B_T`, and every witness set in the carrier has size at most `b`, then
`|mcaBad| ≤ B_T · b`.  This is the precise interface needed for a close-codeword / witness-list
carrier, and avoids the older all-codewords-carrier strengthening. -/
theorem mcaBad_card_le_listFactor_mul_perCodeword_of_cover
    (MC : Submodule F (ι → F)) (δ : ℝ≥0) (u₀ u₁ : ι → F)
    (T : Finset (ι → F))
    (hcover :
      mcaBad (F := F) (MC : Set (ι → F)) δ u₀ u₁ ⊆
        T.biUnion (fun w => mcaBadWitness (F := F) (MC : Set (ι → F)) δ u₀ u₁ w))
    {b B_T : ℝ} (hb0 : 0 ≤ b) (hb_card : (T.card : ℝ) ≤ B_T)
    (hper : ∀ w ∈ T,
      ((mcaBadWitness (F := F) (MC : Set (ι → F)) δ u₀ u₁ w).card : ℝ) ≤ b) :
    ((mcaBad (F := F) (MC : Set (ι → F)) δ u₀ u₁).card : ℝ) ≤ B_T * b := by
  classical
  have hsum : ((mcaBad (F := F) (MC : Set (ι → F)) δ u₀ u₁).card : ℝ) ≤
      ∑ w ∈ T, ((mcaBadWitness (F := F) (MC : Set (ι → F)) δ u₀ u₁ w).card : ℝ) := by
    calc ((mcaBad (F := F) (MC : Set (ι → F)) δ u₀ u₁).card : ℝ)
        ≤ ((T.biUnion
            (fun w => mcaBadWitness (F := F) (MC : Set (ι → F)) δ u₀ u₁ w)).card : ℝ) := by
          exact_mod_cast Finset.card_le_card hcover
      _ ≤ ((∑ w ∈ T,
            (mcaBadWitness (F := F) (MC : Set (ι → F)) δ u₀ u₁ w).card : ℕ) : ℝ) := by
          exact_mod_cast (Finset.card_biUnion_le
            (s := T)
            (t := fun w => mcaBadWitness (F := F) (MC : Set (ι → F)) δ u₀ u₁ w))
      _ = ∑ w ∈ T,
            ((mcaBadWitness (F := F) (MC : Set (ι → F)) δ u₀ u₁ w).card : ℝ) := by
          push_cast
          ring
  calc ((mcaBad (F := F) (MC : Set (ι → F)) δ u₀ u₁).card : ℝ)
      ≤ ∑ w ∈ T,
          ((mcaBadWitness (F := F) (MC : Set (ι → F)) δ u₀ u₁ w).card : ℝ) := hsum
    _ ≤ ∑ _w ∈ T, b := Finset.sum_le_sum (fun w hw => hper w hw)
    _ = (T.card : ℝ) * b := by rw [Finset.sum_const, nsmul_eq_mul]
    _ ≤ B_T * b := by exact mul_le_mul_of_nonneg_right hb_card hb0

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

/-- **No-carrier sharpened in-tree `ε_mca` relaxation.** Taking the carrier to be all codewords
of `MC`, the pairwise-witness count gives

  `ε_mca(MC, δ) ≤ ENNReal.ofReal ((|F|^n · max 1 (2·δ·n)) / |F|)`.

This is the canonical no-carrier version of `epsMCA_le_ofReal_of_listFactor_two_delta`, useful for
public consumers that do not want to thread an explicit finite carrier. -/
theorem epsMCA_le_ofReal_of_listFactor_two_delta_univ
    (MC : Submodule F (ι → F)) (δ : ℝ≥0) :
    epsMCA (F := F) (A := F) (MC : Set (ι → F)) δ ≤
      ENNReal.ofReal
        (((Fintype.card (ι → F) : ℝ) *
            max 1 (2 * (δ : ℝ) * (Fintype.card ι : ℝ))) / Fintype.card F) := by
  classical
  let T : Finset (ι → F) := Finset.univ.filter (fun w : ι → F => w ∈ (MC : Set (ι → F)))
  refine epsMCA_le_ofReal_of_listFactor_two_delta MC δ T ?_ ?_ ?_
  · intro w hw
    simpa [T, hw]
  · intro w hw
    simpa [T] using hw
  · exact_mod_cast Finset.card_filter_le Finset.univ (fun w : ι → F => w ∈ (MC : Set (ι → F)))

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

/-- **Sharpened in-tree relaxed GKL24 first-moment residual.** Taking `T` to be the finite set of
all codewords of `MC`, the pairwise-witness count gives the residual with carrier size `|F|^n` and
per-codeword count `max 1 (2·δ·n)`.

This keeps the first-moment estimate fully in tree and strictly sharper than
`GKL24FirstMomentResidual_inTree_card`; it is still deliberately weaker than GCXK25's sharp
`δ·n` charging theorem. -/
theorem GKL24FirstMomentResidual_inTree_two_delta_card
    (MC : Submodule F (ι → F)) (δ : ℝ≥0) :
    GKL24FirstMomentResidual MC δ
      (Fintype.card (ι → F) : ℝ)
      (max 1 (2 * (δ : ℝ) * (Fintype.card ι : ℝ))) := by
  classical
  intro u
  refine ⟨Finset.univ.filter (fun w : ι → F => w ∈ (MC : Set (ι → F))), ?_, ?_, ?_⟩
  · intro w hw
    rw [Finset.mem_filter]
    exact ⟨Finset.mem_univ _, hw⟩
  · exact_mod_cast Finset.card_filter_le Finset.univ (fun w : ι → F => w ∈ (MC : Set (ι → F)))
  · intro w hw
    rw [Finset.mem_filter] at hw
    exact mcaBadWitness_card_le_two_delta_mul_card MC δ (u 0) (u 1) w hw.2

/-- **Witness-cover form of the GKL24 first-moment residual.**

This is the interface needed by the sharp GCXK25/GKL24 first-moment charging argument. For each
stack `u`, the carrier `T u` need not contain every codeword of `MC`; it only has to be a finite
set of codewords whose witness sets cover the actually bad combining points:

  `mcaBad MC δ (u 0) (u 1) ⊆ ⋃ w ∈ T u, mcaBadWitness MC δ (u 0) (u 1) w`.

That distinction matters for the intended `B_T = L²` application: `T u` is the close-codeword /
witness carrier furnished by list decoding and maximal correlated-agreement domains, not the full
code. The per-witness count `b` is still the genuine GKL24/GCXK25 content. -/
def GKL24FirstMomentWitnessCoverResidual
    (MC : Submodule F (ι → F)) (δ : ℝ≥0) (B_T b : ℝ) : Prop :=
  ∀ u : WordStack F (Fin 2) ι,
    ∃ T : Finset (ι → F),
      (∀ w ∈ T, w ∈ (MC : Set (ι → F))) ∧
        mcaBad (F := F) (MC : Set (ι → F)) δ (u 0) (u 1) ⊆
          T.biUnion (fun w =>
            mcaBadWitness (F := F) (MC : Set (ι → F)) δ (u 0) (u 1) w) ∧
        (T.card : ℝ) ≤ B_T ∧
          ∀ w ∈ T,
            ((mcaBadWitness (F := F) (MC : Set (ι → F)) δ (u 0) (u 1) w).card : ℝ) ≤ b

/-- **In-tree witness-cover residual, with the pairwise two-delta count.** Taking `T` to be the
finite set of all codewords recovers a witness cover from the existing GCXK25 union-bound
containment. This theorem is deliberately an in-tree relaxation:

  `B_T = |F|^n`, `b = max 1 (2·δ·n)`.

Its purpose is regression coverage for the witness-cover interface, not a proof of the sharp
`L² · δ · n` GCXK25/GKL24 first-moment theorem. -/
theorem GKL24FirstMomentWitnessCoverResidual_inTree_two_delta_card
    (MC : Submodule F (ι → F)) (δ : ℝ≥0) :
    GKL24FirstMomentWitnessCoverResidual MC δ
      (Fintype.card (ι → F) : ℝ)
      (max 1 (2 * (δ : ℝ) * (Fintype.card ι : ℝ))) := by
  classical
  intro u
  let T : Finset (ι → F) := Finset.univ.filter (fun w : ι → F => w ∈ (MC : Set (ι → F)))
  refine ⟨T, ?_, ?_, ?_, ?_⟩
  · intro w hw
    simpa [T] using hw
  · refine mcaBad_subset_biUnion_mcaBadWitness (MC : Set (ι → F)) δ (u 0) (u 1) T ?_
    intro w hw
    simpa [T, hw]
  · exact_mod_cast Finset.card_filter_le Finset.univ (fun w : ι → F => w ∈ (MC : Set (ι → F)))
  · intro w hw
    exact mcaBadWitness_card_le_two_delta_mul_card MC δ (u 0) (u 1) w (by simpa [T] using hw)

/-! ### Maximal-domain petal accounting

The sharp GCXK/GKL first-moment proof does not charge bad scalars per fixed witness codeword.
For one maximal correlated-agreement domain `D`, distinct bad scalars should produce pairwise
disjoint nonempty *petals* inside `Dᶜ`. The hard paper lemma is the disjoint-petal construction.
The two wrappers below provide the downstream counting once those petals are available:

* pairwise-disjoint nonempty petals in `Dᶜ` give `#Γ ≤ #(Dᶜ)`;
* if `#D ≥ (1-p)n`, then `#Γ ≤ p n`.
-/

/-- **GKL/GCXK petal accounting, complement-size form.** If every bad scalar in `Γ` has a
nonempty petal, the petals are pairwise disjoint, and all petals live outside a domain `D`, then
the number of scalars is at most the complement size `n - #D`. This is the pure counting half of
the maximal-domain first-moment argument. -/
theorem badScalars_card_le_domain_compl_of_disjoint_petals
    (Γ : Finset F) (D : Finset ι) (petal : F → Finset ι)
    (hdisj : (Γ : Set F).Pairwise (fun γ γ' => Disjoint (petal γ) (petal γ')))
    (hsize : ∀ γ ∈ Γ, 1 ≤ (petal γ).card)
    (hsub : ∀ γ ∈ Γ, petal γ ⊆ (Finset.univ \ D)) :
    Γ.card ≤ Fintype.card ι - D.card := by
  classical
  have hM : (Finset.univ \ D).card ≤ Fintype.card ι - D.card := by
    have hD : D ⊆ (Finset.univ : Finset ι) := fun i _ => Finset.mem_univ i
    rw [Finset.card_sdiff_of_subset hD, Finset.card_univ]
  have h :=
    GreedyDisjointCover.card_mul_le_of_disjoint_covers
      Γ petal (Finset.univ \ D) 1 (Fintype.card ι - D.card)
      hdisj hsize hsub hM
  simpa using h

/-- **GKL/GCXK petal accounting, first-moment real form.** If the maximal domain `D` has size at
least `(1-p)n`, then the complement-size petal count becomes `#Γ ≤ p·n`. This is the exact
cardinality wrapper needed after formalizing the GCXK/GKL disjoint-petal lemma for one maximal
correlated-agreement domain. -/
theorem badScalars_card_le_radius_mul_card_of_large_domain_disjoint_petals
    (Γ : Finset F) (D : Finset ι) (petal : F → Finset ι) {p : ℝ}
    (hDlarge : (1 - p) * (Fintype.card ι : ℝ) ≤ (D.card : ℝ))
    (hdisj : (Γ : Set F).Pairwise (fun γ γ' => Disjoint (petal γ) (petal γ')))
    (hsize : ∀ γ ∈ Γ, 1 ≤ (petal γ).card)
    (hsub : ∀ γ ∈ Γ, petal γ ⊆ (Finset.univ \ D)) :
    (Γ.card : ℝ) ≤ p * (Fintype.card ι : ℝ) := by
  classical
  have hnat :=
    badScalars_card_le_domain_compl_of_disjoint_petals
      Γ D petal hdisj hsize hsub
  have hDle : D.card ≤ Fintype.card ι := by
    calc
      D.card ≤ (Finset.univ : Finset ι).card :=
        Finset.card_le_card (fun i _ => Finset.mem_univ i)
      _ = Fintype.card ι := Finset.card_univ
  have hcompl : (Γ.card : ℝ) ≤ (Fintype.card ι : ℝ) - (D.card : ℝ) := by
    calc (Γ.card : ℝ) ≤ ((Fintype.card ι - D.card : ℕ) : ℝ) := by exact_mod_cast hnat
      _ = (Fintype.card ι : ℝ) - (D.card : ℝ) := by
          exact Nat.cast_sub hDle
  nlinarith [hcompl, hDlarge]

/-- **Line-petal core-equality bucket bound.**  If every scalar in `Γ` strictly expands a common
core `D`, and every pair of line-agreement domains intersects exactly in `D`, then the line
petals give the `#Γ ≤ p·n` first-moment count once `D` has size at least `(1-p)n`.

This is the local set-theory/cardinality endgame after the GCXK/GKL maximal-domain argument has
already identified the common core for the bucket. -/
theorem badScalars_card_le_radius_mul_card_of_linePetal_core_eq
    (Γ : Finset F) (D : Finset ι) (u₀ u₁ : ι → F) (wOf : F → ι → F) {p : ℝ}
    (hDlarge : (1 - p) * (Fintype.card ι : ℝ) ≤ (D.card : ℝ))
    (hstrict : ∀ γ ∈ Γ, D ⊂ lineAgreeSet u₀ u₁ (wOf γ) γ)
    (hcore : ∀ γ ∈ Γ, ∀ γ' ∈ Γ, γ ≠ γ' →
      lineAgreeSet u₀ u₁ (wOf γ) γ ∩ lineAgreeSet u₀ u₁ (wOf γ') γ' = D) :
    (Γ.card : ℝ) ≤ p * (Fintype.card ι : ℝ) := by
  classical
  refine
    badScalars_card_le_radius_mul_card_of_large_domain_disjoint_petals
      Γ D (fun γ => linePetal D u₀ u₁ (wOf γ) γ) hDlarge ?_ ?_ ?_
  · intro γ hγ γ' hγ' hne
    exact linePetal_disjoint_of_inter_lineAgreeSet_eq (hcore γ hγ γ' hγ' hne)
  · intro γ hγ
    exact Nat.succ_le_iff.mpr
      (Finset.card_pos.mpr (linePetal_nonempty_of_ssubset_lineAgreeSet (hstrict γ hγ)))
  · intro γ _hγ
    exact linePetal_subset_compl D u₀ u₁ (wOf γ) γ

/-- **Per-codeword bad-scalar count from a GKL/GCXK petal certificate.**  This specializes the
generic petal accounting wrapper to the actual witness set
`mcaBadWitness MC δ u₀ u₁ w`.  Once a large maximal domain `D` and pairwise-disjoint nonempty
petals in `Dᶜ` are supplied, the witness set has size at most `p · n`. -/
theorem mcaBadWitness_card_le_radius_mul_card_of_large_domain_disjoint_petals
    (MC : Submodule F (ι → F)) (δ : ℝ≥0) (u₀ u₁ w : ι → F)
    (D : Finset ι) (petal : F → Finset ι) {p : ℝ}
    (hDlarge : (1 - p) * (Fintype.card ι : ℝ) ≤ (D.card : ℝ))
    (hdisj :
      ((mcaBadWitness (F := F) (MC : Set (ι → F)) δ u₀ u₁ w) : Set F).Pairwise
        (fun γ γ' => Disjoint (petal γ) (petal γ')))
    (hsize : ∀ γ ∈ mcaBadWitness (F := F) (MC : Set (ι → F)) δ u₀ u₁ w,
      1 ≤ (petal γ).card)
    (hsub : ∀ γ ∈ mcaBadWitness (F := F) (MC : Set (ι → F)) δ u₀ u₁ w,
      petal γ ⊆ (Finset.univ \ D)) :
    ((mcaBadWitness (F := F) (MC : Set (ι → F)) δ u₀ u₁ w).card : ℝ) ≤
      p * (Fintype.card ι : ℝ) :=
  badScalars_card_le_radius_mul_card_of_large_domain_disjoint_petals
    (mcaBadWitness (F := F) (MC : Set (ι → F)) δ u₀ u₁ w) D petal
    hDlarge hdisj hsize hsub

/-- **Per-codeword first-moment count from a maximal-domain certificate.**  This packages the
formal downstream half of the GKL/GCXK sunflower argument.  The remaining paper content is the
construction of `D` and the proof that all relevant line-agreement domains strictly expand it
while pairwise intersections remain large. -/
theorem mcaBadWitness_card_le_radius_mul_card_of_maxCorrAgreeDomain
    (MC : Submodule F (ι → F)) (δ p : ℝ≥0) (u₀ u₁ w : ι → F) (D : Finset ι)
    (hw : w ∈ (MC : Set (ι → F)))
    (hD : maxCorrAgreeDomain MC p u₀ u₁ D)
    (hstrict : ∀ γ ∈ mcaBadWitness (F := F) (MC : Set (ι → F)) δ u₀ u₁ w,
      D ⊂ lineAgreeSet u₀ u₁ w γ)
    (hIlarge : ∀ γ ∈ mcaBadWitness (F := F) (MC : Set (ι → F)) δ u₀ u₁ w,
      ∀ γ' ∈ mcaBadWitness (F := F) (MC : Set (ι → F)) δ u₀ u₁ w, γ ≠ γ' →
        ((1 - p) * Fintype.card ι : ℝ≥0) ≤
          (((lineAgreeSet u₀ u₁ w γ ∩ lineAgreeSet u₀ u₁ w γ').card : ℕ) : ℝ≥0)) :
    ((mcaBadWitness (F := F) (MC : Set (ι → F)) δ u₀ u₁ w).card : ℝ) ≤
      (p : ℝ) * (Fintype.card ι : ℝ) := by
  classical
  let Γ := mcaBadWitness (F := F) (MC : Set (ι → F)) δ u₀ u₁ w
  have hDlargeNN :
      ((1 - p) * Fintype.card ι : ℝ≥0) ≤ (D.card : ℝ≥0) := hD.1.1
  have hDlargeTrunc :
      (((1 - p : ℝ≥0) : ℝ) * (Fintype.card ι : ℝ)) ≤ (D.card : ℝ) := by
    exact_mod_cast hDlargeNN
  have hsub_le : 1 - (p : ℝ) ≤ ((1 - p : ℝ≥0) : ℝ) := by
    rw [NNReal.coe_sub_def]
    exact le_max_left _ _
  have hDlarge : (1 - (p : ℝ)) * (Fintype.card ι : ℝ) ≤ (D.card : ℝ) := by
    calc
      (1 - (p : ℝ)) * (Fintype.card ι : ℝ)
          ≤ ((1 - p : ℝ≥0) : ℝ) * (Fintype.card ι : ℝ) := by
            exact mul_le_mul_of_nonneg_right hsub_le (by positivity)
      _ ≤ (D.card : ℝ) := hDlargeTrunc
  refine
    mcaBadWitness_card_le_radius_mul_card_of_large_domain_disjoint_petals
      MC δ u₀ u₁ w D (fun γ => linePetal D u₀ u₁ w γ) hDlarge ?_ ?_ ?_
  · have hdisj :
        (Γ : Set F).Pairwise (fun γ γ' =>
          Disjoint (linePetal D u₀ u₁ w γ) (linePetal D u₀ u₁ w γ')) := by
      refine linePetal_pairwise_disjoint_of_maxCorrAgreeDomain
        MC p D u₀ u₁ (fun _ => w) Γ hD ?_ ?_ ?_
      · intro γ hγ
        exact (hstrict γ hγ).1
      · intro γ hγ γ' hγ' hne
        exact hIlarge γ hγ γ' hγ' hne
      · intro γ _hγ
        exact hw
    simpa [Γ]
  · intro γ hγ
    exact Nat.succ_le_iff.mpr
      (Finset.card_pos.mpr (linePetal_nonempty_of_ssubset_lineAgreeSet (hstrict γ hγ)))
  · intro γ _hγ
    exact linePetal_subset_compl D u₀ u₁ w γ

/-- **Strict-expansion-only max-corr residual.**  This is a smaller producer surface for the
GKL24/GCXK25 first-moment route.  Compared with `GKL24MaxCorrWitnessCoverResidual`, it asks only
for a close-codeword carrier and, for each carried codeword, a maximal correlated-agreement domain
that is strictly expanded by every bad line-agreement domain.

The pairwise large-intersection clause is derived by
`GKL24MaxCorrWitnessCoverResidual_of_strict_cover` from the witness-size lower bounds when the
Johnson parameter relation `2 * δ_mca ≤ p` holds. -/
def GKL24MaxCorrStrictWitnessCoverResidual
    (MC : Submodule F (ι → F)) (δ p : ℝ≥0) (B_T : ℝ) : Prop :=
  ∀ u : WordStack F (Fin 2) ι,
    ∃ T : Finset (ι → F),
      (∀ w ∈ T, w ∈ (MC : Set (ι → F))) ∧
        mcaBad (F := F) (MC : Set (ι → F)) δ (u 0) (u 1) ⊆
          T.biUnion (fun w =>
            mcaBadWitness (F := F) (MC : Set (ι → F)) δ (u 0) (u 1) w) ∧
        (T.card : ℝ) ≤ B_T ∧
          ∀ w ∈ T,
            ∃ D : Finset ι,
              maxCorrAgreeDomain MC p (u 0) (u 1) D ∧
                ∀ γ ∈ mcaBadWitness
                    (F := F) (MC : Set (ι → F)) δ (u 0) (u 1) w,
                  D ⊂ lineAgreeSet (u 0) (u 1) w γ

/-- **Maximal-domain form of the GKL24/GCXK25 witness-cover residual.**  This is the
carrier-level version of `mcaBadWitness_card_le_radius_mul_card_of_maxCorrAgreeDomain`: every
stack has a close-codeword carrier, and each carried codeword has a maximal
correlated-agreement domain whose bad line-agreement domains strictly expand it while pairwise
intersections remain large. -/
def GKL24MaxCorrWitnessCoverResidual
    (MC : Submodule F (ι → F)) (δ p : ℝ≥0) (B_T : ℝ) : Prop :=
  ∀ u : WordStack F (Fin 2) ι,
    ∃ T : Finset (ι → F),
      (∀ w ∈ T, w ∈ (MC : Set (ι → F))) ∧
        mcaBad (F := F) (MC : Set (ι → F)) δ (u 0) (u 1) ⊆
          T.biUnion (fun w =>
            mcaBadWitness (F := F) (MC : Set (ι → F)) δ (u 0) (u 1) w) ∧
        (T.card : ℝ) ≤ B_T ∧
          ∀ w ∈ T,
            ∃ D : Finset ι,
              maxCorrAgreeDomain MC p (u 0) (u 1) D ∧
                (∀ γ ∈ mcaBadWitness
                    (F := F) (MC : Set (ι → F)) δ (u 0) (u 1) w,
                  D ⊂ lineAgreeSet (u 0) (u 1) w γ) ∧
                (∀ γ ∈ mcaBadWitness
                    (F := F) (MC : Set (ι → F)) δ (u 0) (u 1) w,
                  ∀ γ' ∈ mcaBadWitness
                      (F := F) (MC : Set (ι → F)) δ (u 0) (u 1) w,
                    γ ≠ γ' →
                      ((1 - p) * Fintype.card ι : ℝ≥0) ≤
                        (((lineAgreeSet (u 0) (u 1) w γ ∩
                            lineAgreeSet (u 0) (u 1) w γ').card : ℕ) : ℝ≥0))

/-- A strict-expansion-only max-corr residual gives the full max-corr residual whenever
`2 * δ ≤ p` and `p ≤ 1`.  The missing pairwise large-intersection clause follows from
`lineAgreeSet_inter_card_ge_of_mem_mcaBadWitness`. -/
theorem GKL24MaxCorrWitnessCoverResidual_of_strict_cover
    (MC : Submodule F (ι → F)) (δ p : ℝ≥0) {B_T : ℝ}
    (hp_le_one : p ≤ 1)
    (hδp : 2 * (δ : ℝ) ≤ (p : ℝ))
    (hstrict : GKL24MaxCorrStrictWitnessCoverResidual MC δ p B_T) :
    GKL24MaxCorrWitnessCoverResidual MC δ p B_T := by
  intro u
  obtain ⟨T, hTsub, hcover, hcard, hstrictT⟩ := hstrict u
  refine ⟨T, hTsub, hcover, hcard, ?_⟩
  intro w hw
  obtain ⟨D, hD, hstrictD⟩ := hstrictT w hw
  refine ⟨D, hD, hstrictD, ?_⟩
  intro γ hγ γ' hγ' _hne
  exact
    lineAgreeSet_inter_card_ge_of_mem_mcaBadWitness
      MC δ p (u 0) (u 1) w w hp_le_one hδp hγ hγ'

/-- A maximal-domain witness-cover residual instantiates the corrected first-moment
witness-cover residual with per-codeword count `p · n`. -/
theorem GKL24FirstMomentWitnessCoverResidual_of_maxCorr_cover
    (MC : Submodule F (ι → F)) (δ p : ℝ≥0) {B_T : ℝ}
    (hmax : GKL24MaxCorrWitnessCoverResidual MC δ p B_T) :
    GKL24FirstMomentWitnessCoverResidual MC δ B_T ((p : ℝ) * (Fintype.card ι : ℝ)) := by
  intro u
  obtain ⟨T, hTsub, hcover, hcard, hmaxT⟩ := hmax u
  refine ⟨T, hTsub, hcover, hcard, ?_⟩
  intro w hw
  obtain ⟨D, hD, hstrict, hIlarge⟩ := hmaxT w hw
  exact
    mcaBadWitness_card_le_radius_mul_card_of_maxCorrAgreeDomain
      MC δ p (u 0) (u 1) w D (hTsub w hw) hD hstrict hIlarge

/-- **Petal-certificate form of the GKL24/GCXK25 witness-cover residual.**

For every stack `u`, this asks for a close-codeword carrier `T` that covers the bad scalars and,
for every codeword `w ∈ T`, a GKL/GCXK maximal-domain certificate: a large domain `D` and
pairwise-disjoint nonempty petals in `Dᶜ` for the bad scalars witnessed by `w`.

This is still a residual: the hard paper theorem is the construction of those domains and petals.
The theorem below proves that this certificate is exactly strong enough to instantiate
`GKL24FirstMomentWitnessCoverResidual` with `b = p · n`. -/
def GKL24PetalWitnessCoverResidual
    (MC : Submodule F (ι → F)) (δ : ℝ≥0) (B_T p : ℝ) : Prop :=
  ∀ u : WordStack F (Fin 2) ι,
    ∃ T : Finset (ι → F),
      (∀ w ∈ T, w ∈ (MC : Set (ι → F))) ∧
        mcaBad (F := F) (MC : Set (ι → F)) δ (u 0) (u 1) ⊆
          T.biUnion (fun w =>
            mcaBadWitness (F := F) (MC : Set (ι → F)) δ (u 0) (u 1) w) ∧
        (T.card : ℝ) ≤ B_T ∧
          ∀ w ∈ T,
            ∃ D : Finset ι, ∃ petal : F → Finset ι,
              (1 - p) * (Fintype.card ι : ℝ) ≤ (D.card : ℝ) ∧
                ((mcaBadWitness (F := F) (MC : Set (ι → F)) δ (u 0) (u 1) w) :
                    Set F).Pairwise (fun γ γ' => Disjoint (petal γ) (petal γ')) ∧
                  (∀ γ ∈ mcaBadWitness (F := F) (MC : Set (ι → F)) δ (u 0) (u 1) w,
                    1 ≤ (petal γ).card) ∧
                    (∀ γ ∈ mcaBadWitness (F := F) (MC : Set (ι → F)) δ (u 0) (u 1) w,
                      petal γ ⊆ (Finset.univ \ D))

/-- A maximal-domain witness-cover residual gives the explicit petal-certificate residual by
choosing the canonical line petals outside each maximal domain. -/
theorem GKL24PetalWitnessCoverResidual_of_maxCorr_cover
    (MC : Submodule F (ι → F)) (δ p : ℝ≥0) {B_T : ℝ}
    (hmax : GKL24MaxCorrWitnessCoverResidual MC δ p B_T) :
    GKL24PetalWitnessCoverResidual MC δ B_T (p : ℝ) := by
  classical
  intro u
  obtain ⟨T, hTsub, hcover, hcard, hmaxT⟩ := hmax u
  refine ⟨T, hTsub, hcover, hcard, ?_⟩
  intro w hw
  obtain ⟨D, hD, hstrict, hIlarge⟩ := hmaxT w hw
  refine ⟨D, (fun γ => linePetal D (u 0) (u 1) w γ), ?_, ?_, ?_, ?_⟩
  · have hDlargeNN :
        ((1 - p) * Fintype.card ι : ℝ≥0) ≤ (D.card : ℝ≥0) := hD.1.1
    have hDlargeTrunc :
        (((1 - p : ℝ≥0) : ℝ) * (Fintype.card ι : ℝ)) ≤ (D.card : ℝ) := by
      exact_mod_cast hDlargeNN
    have hsub_le : 1 - (p : ℝ) ≤ ((1 - p : ℝ≥0) : ℝ) := by
      rw [NNReal.coe_sub_def]
      exact le_max_left _ _
    calc
      (1 - (p : ℝ)) * (Fintype.card ι : ℝ)
          ≤ ((1 - p : ℝ≥0) : ℝ) * (Fintype.card ι : ℝ) := by
            exact mul_le_mul_of_nonneg_right hsub_le (by positivity)
      _ ≤ (D.card : ℝ) := hDlargeTrunc
  · exact linePetal_pairwise_disjoint_of_maxCorrAgreeDomain
      MC p D (u 0) (u 1) (fun _ => w)
      (mcaBadWitness (F := F) (MC : Set (ι → F)) δ (u 0) (u 1) w)
      hD (fun γ hγ => (hstrict γ hγ).1) hIlarge (fun _ _ => hTsub w hw)
  · intro γ hγ
    exact Nat.succ_le_iff.mpr
      (Finset.card_pos.mpr (linePetal_nonempty_of_ssubset_lineAgreeSet (hstrict γ hγ)))
  · intro γ _hγ
    exact linePetal_subset_compl D (u 0) (u 1) w γ

/-- A petal-certificate residual instantiates the corrected witness-cover residual with the
first-moment count `b = p · n`. -/
theorem GKL24FirstMomentWitnessCoverResidual_of_petal_cover
    (MC : Submodule F (ι → F)) (δ : ℝ≥0) {B_T p : ℝ}
    (hpetal : GKL24PetalWitnessCoverResidual MC δ B_T p) :
    GKL24FirstMomentWitnessCoverResidual MC δ B_T (p * (Fintype.card ι : ℝ)) := by
  intro u
  obtain ⟨T, hTsub, hcover, hcard, hpetalT⟩ := hpetal u
  refine ⟨T, hTsub, hcover, hcard, ?_⟩
  intro w hw
  obtain ⟨D, petal, hDlarge, hdisj, hsize, hsub⟩ := hpetalT w hw
  exact
    mcaBadWitness_card_le_radius_mul_card_of_large_domain_disjoint_petals
      MC δ (u 0) (u 1) w D petal hDlarge hdisj hsize hsub

/-- Count-level front door from the petal-certificate residual.  This is the exact
`B_T · p · n` first-moment shape used by the GCXK25/GKL24 route once the disjoint-petal
construction is available. -/
theorem mcaBad_card_le_of_gkl24_petal_witnessCover_residual
    (MC : Submodule F (ι → F)) (δ : ℝ≥0) {B_T p : ℝ} (hp0 : 0 ≤ p)
    (hres : GKL24PetalWitnessCoverResidual MC δ B_T p)
    (u : WordStack F (Fin 2) ι) :
    ((mcaBad (F := F) (MC : Set (ι → F)) δ (u 0) (u 1)).card : ℝ) ≤
      B_T * (p * (Fintype.card ι : ℝ)) := by
  obtain ⟨T, _hTsub, hcover, hcard, hpetalT⟩ := hres u
  refine mcaBad_card_le_listFactor_mul_perCodeword_of_cover
    MC δ (u 0) (u 1) T hcover (mul_nonneg hp0 (by positivity)) hcard ?_
  intro w hw
  obtain ⟨D, petal, hDlarge, hdisj, hsize, hsub⟩ := hpetalT w hw
  exact
    mcaBadWitness_card_le_radius_mul_card_of_large_domain_disjoint_petals
      MC δ (u 0) (u 1) w D petal hDlarge hdisj hsize hsub

/-- `ε_mca` front door from the petal-certificate residual.  This keeps the remaining first-moment
paper work localized to the construction of the carrier and disjoint petals. -/
theorem epsMCA_le_ofReal_of_gkl24_petal_witnessCover_residual
    (MC : Submodule F (ι → F)) (δ : ℝ≥0) {B_T p : ℝ} (hp0 : 0 ≤ p)
    (hres : GKL24PetalWitnessCoverResidual MC δ B_T p) :
    epsMCA (F := F) (A := F) (MC : Set (ι → F)) δ ≤
      ENNReal.ofReal ((B_T * (p * (Fintype.card ι : ℝ))) / Fintype.card F) := by
  refine epsMCA_le_ofReal_of_forall_mcaBad_card_le (MC : Set (ι → F)) δ ?_
  intro u
  exact mcaBad_card_le_of_gkl24_petal_witnessCover_residual MC δ hp0 hres u

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

/-- **Per-stack bad-`γ` count from the witness-cover residual.**
This is the corrected carrier interface for the first-moment side of GCXK25/GKL24: the finite
carrier only has to cover the bad scalars for the current stack, rather than contain all codewords
of `MC`. Supplying this residual at `B_T = L²`, `b = δ_list · n` is the sharp first-moment theorem
still left open by #67. -/
theorem mcaBad_card_le_of_gkl24_witnessCover_residual
    (MC : Submodule F (ι → F)) (δ : ℝ≥0) {B_T b : ℝ} (hb0 : 0 ≤ b)
    (hres : GKL24FirstMomentWitnessCoverResidual MC δ B_T b)
    (u : WordStack F (Fin 2) ι) :
    ((mcaBad (F := F) (MC : Set (ι → F)) δ (u 0) (u 1)).card : ℝ) ≤ B_T * b := by
  obtain ⟨T, _hTsub, hcover, hcard, hper⟩ := hres u
  exact mcaBad_card_le_listFactor_mul_perCodeword_cover
    (MC : Set (ι → F)) δ (u 0) (u 1) T hcover hb0 hcard hper

/-- Count-level front door from the maximal-domain witness-cover residual. -/
theorem mcaBad_card_le_of_gkl24_maxCorr_witnessCover_residual
    (MC : Submodule F (ι → F)) (δ p : ℝ≥0) {B_T : ℝ}
    (hres : GKL24MaxCorrWitnessCoverResidual MC δ p B_T)
    (u : WordStack F (Fin 2) ι) :
    ((mcaBad (F := F) (MC : Set (ι → F)) δ (u 0) (u 1)).card : ℝ) ≤
      B_T * ((p : ℝ) * (Fintype.card ι : ℝ)) :=
  mcaBad_card_le_of_gkl24_witnessCover_residual MC δ (by positivity)
    (GKL24FirstMomentWitnessCoverResidual_of_maxCorr_cover MC δ p hres) u

/-- Probability-level companion to `mcaBad_card_le_of_gkl24_witnessCover_residual`. -/
theorem mcaEvent_prob_le_ofReal_of_gkl24_witnessCover_residual
    (MC : Submodule F (ι → F)) (δ : ℝ≥0) {B_T b : ℝ} (hb0 : 0 ≤ b)
    (hres : GKL24FirstMomentWitnessCoverResidual MC δ B_T b)
    (u : WordStack F (Fin 2) ι) :
    Pr_{let γ ← $ᵖ F}[mcaEvent (F := F) (MC : Set (ι → F)) δ (u 0) (u 1) γ] ≤
      ENNReal.ofReal ((B_T * b) / Fintype.card F) :=
  mcaEvent_prob_le_of_mcaBad_card_le (MC : Set (ι → F)) δ (u 0) (u 1)
    (mcaBad_card_le_of_gkl24_witnessCover_residual MC δ hb0 hres u)

/-- Probability-level front door from the maximal-domain witness-cover residual. -/
theorem mcaEvent_prob_le_ofReal_of_gkl24_maxCorr_witnessCover_residual
    (MC : Submodule F (ι → F)) (δ p : ℝ≥0) {B_T : ℝ}
    (hres : GKL24MaxCorrWitnessCoverResidual MC δ p B_T)
    (u : WordStack F (Fin 2) ι) :
    Pr_{let γ ← $ᵖ F}[mcaEvent (F := F) (MC : Set (ι → F)) δ (u 0) (u 1) γ] ≤
      ENNReal.ofReal ((B_T * ((p : ℝ) * (Fintype.card ι : ℝ))) / Fintype.card F) :=
  mcaEvent_prob_le_of_mcaBad_card_le (MC : Set (ι → F)) δ (u 0) (u 1)
    (mcaBad_card_le_of_gkl24_maxCorr_witnessCover_residual MC δ p hres u)

/-- **Alias for the witness-cover residual in the canonical ABF26 T5.1 parameter shape.**
This is the future plug-in point for the GCXK25/GKL24 maximal-domain charging theorem at
`B_T := L²`, `b := δ_list · n`. -/
theorem mcaBad_card_le_t51_firstMoment_of_gkl24_witnessCover_residual
    (MC : Submodule F (ι → F)) (δ : ℝ≥0) {Lsq δn : ℝ} (hδn0 : 0 ≤ δn)
    (hres : GKL24FirstMomentWitnessCoverResidual MC δ Lsq δn)
    (u : WordStack F (Fin 2) ι) :
    ((mcaBad (F := F) (MC : Set (ι → F)) δ (u 0) (u 1)).card : ℝ) ≤ Lsq * δn :=
  mcaBad_card_le_of_gkl24_witnessCover_residual MC δ hδn0 hres u

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

/-- **Conditional strengthening from the witness-cover residual.**
This is the `ε_mca` version of `mcaBad_card_le_of_gkl24_witnessCover_residual`, retaining the
correct close-codeword carrier interface for the future sharp first-moment proof. -/
theorem epsMCA_le_ofReal_of_gkl24_witnessCover_residual
    (MC : Submodule F (ι → F)) (δ : ℝ≥0) {B_T b : ℝ} (hb0 : 0 ≤ b)
    (hres : GKL24FirstMomentWitnessCoverResidual MC δ B_T b) :
    epsMCA (F := F) (A := F) (MC : Set (ι → F)) δ ≤
      ENNReal.ofReal ((B_T * b) / Fintype.card F) := by
  refine epsMCA_le_ofReal_of_forall_mcaBad_card_le (MC : Set (ι → F)) δ ?_
  intro u
  exact mcaBad_card_le_of_gkl24_witnessCover_residual MC δ hb0 hres u

/-- `ε_mca` front door from the maximal-domain witness-cover residual. -/
theorem epsMCA_le_ofReal_of_gkl24_maxCorr_witnessCover_residual
    (MC : Submodule F (ι → F)) (δ p : ℝ≥0) {B_T : ℝ}
    (hres : GKL24MaxCorrWitnessCoverResidual MC δ p B_T) :
    epsMCA (F := F) (A := F) (MC : Set (ι → F)) δ ≤
      ENNReal.ofReal
        ((B_T * ((p : ℝ) * (Fintype.card ι : ℝ))) / Fintype.card F) := by
  refine epsMCA_le_ofReal_of_forall_mcaBad_card_le (MC : Set (ι → F)) δ ?_
  intro u
  exact mcaBad_card_le_of_gkl24_maxCorr_witnessCover_residual MC δ p hres u

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

/-- **Fully in-tree witness-cover `ε_mca` relaxation.** This checks that the corrected
witness-cover residual interface composes all the way to `ε_mca`; the bound is the already-known
two-delta no-carrier relaxation, routed through the new residual shape. -/
theorem epsMCA_le_ofReal_inTree_firstMoment_witnessCover_two_delta_card
    (MC : Submodule F (ι → F)) (δ : ℝ≥0) :
    epsMCA (F := F) (A := F) (MC : Set (ι → F)) δ ≤
      ENNReal.ofReal
        (((Fintype.card (ι → F) : ℝ) *
            max 1 (2 * (δ : ℝ) * (Fintype.card ι : ℝ))) / Fintype.card F) :=
  epsMCA_le_ofReal_of_gkl24_witnessCover_residual MC δ
    (le_trans zero_le_one (le_max_left _ _))
    (GKL24FirstMomentWitnessCoverResidual_inTree_two_delta_card MC δ)

end Compose

end ProximityGap

/- Axiom audit for the GKL24 first-moment bridge surfaces.  These should remain
kernel-clean apart from the standard Lean foundations (`propext`, `Classical.choice`,
`Quot.sound`). -/
#print axioms ProximityGap.GKL24FirstMomentResidual_inTree_card
#print axioms ProximityGap.GKL24FirstMomentResidual_inTree_two_delta_card
#print axioms ProximityGap.GKL24FirstMomentWitnessCoverResidual_inTree_two_delta_card
#print axioms ProximityGap.lineAgreeSet_card_ge_of_mem_mcaBadWitness
#print axioms ProximityGap.linePetal_nonempty_of_ssubset_lineAgreeSet
#print axioms ProximityGap.linePetal_subset_compl
#print axioms ProximityGap.linePetal_disjoint_of_inter_lineAgreeSet_eq
#print axioms ProximityGap.lineAgreeSet_inter_card_ge_of_card_ge
#print axioms ProximityGap.lineAgreeSet_inter_card_ge_of_mem_mcaBadWitness
#print axioms ProximityGap.pairJointAgreesOn_inter_lineAgreeSet_of_ne
#print axioms ProximityGap.maxCorrAgreeDomain.eq_of_subset
#print axioms ProximityGap.inter_lineAgreeSet_eq_of_maxCorrAgreeDomain
#print axioms ProximityGap.linePetal_disjoint_of_inter_eq
#print axioms ProximityGap.linePetal_pairwise_disjoint_of_maxCorrAgreeDomain
#print axioms ProximityGap.badScalars_card_le_domain_compl_of_disjoint_petals
#print axioms ProximityGap.badScalars_card_le_radius_mul_card_of_large_domain_disjoint_petals
#print axioms ProximityGap.badScalars_card_le_radius_mul_card_of_linePetal_core_eq
#print axioms ProximityGap.mcaBadWitness_card_le_radius_mul_card_of_large_domain_disjoint_petals
#print axioms ProximityGap.mcaBadWitness_card_le_radius_mul_card_of_maxCorrAgreeDomain
#print axioms ProximityGap.GKL24MaxCorrWitnessCoverResidual_of_strict_cover
#print axioms ProximityGap.GKL24PetalWitnessCoverResidual_of_maxCorr_cover
#print axioms ProximityGap.GKL24FirstMomentWitnessCoverResidual_of_petal_cover
#print axioms ProximityGap.GKL24FirstMomentWitnessCoverResidual_of_maxCorr_cover
#print axioms ProximityGap.mcaBad_card_le_of_gkl24_petal_witnessCover_residual
#print axioms ProximityGap.epsMCA_le_ofReal_of_gkl24_petal_witnessCover_residual
#print axioms ProximityGap.mcaBad_card_le_of_gkl24_residual
#print axioms ProximityGap.mcaEvent_prob_le_ofReal_of_gkl24_residual
#print axioms ProximityGap.mcaBad_card_le_t51_firstMoment_of_gkl24_residual
#print axioms ProximityGap.epsMCA_le_ofReal_of_gkl24_residual
#print axioms ProximityGap.mcaBad_card_le_of_gkl24_witnessCover_residual
#print axioms ProximityGap.mcaBad_card_le_of_gkl24_maxCorr_witnessCover_residual
#print axioms ProximityGap.mcaEvent_prob_le_ofReal_of_gkl24_witnessCover_residual
#print axioms ProximityGap.mcaEvent_prob_le_ofReal_of_gkl24_maxCorr_witnessCover_residual
#print axioms ProximityGap.mcaBad_card_le_t51_firstMoment_of_gkl24_witnessCover_residual
#print axioms ProximityGap.epsMCA_le_ofReal_of_gkl24_witnessCover_residual
#print axioms ProximityGap.epsMCA_le_ofReal_of_gkl24_maxCorr_witnessCover_residual
#print axioms ProximityGap.epsMCA_le_ofReal_inTree_firstMoment_card
#print axioms ProximityGap.epsMCA_le_ofReal_inTree_firstMoment_witnessCover_two_delta_card
#print axioms ProximityGap.u1_zero_of_mem_both_witness
#print axioms ProximityGap.secondSupport_card_le_two_delta_of_two_witnesses
#print axioms ProximityGap.mcaBadWitness_card_le_two_delta_mul_card
#print axioms ProximityGap.mcaBad_card_le_listFactor_mul_two_delta_card
#print axioms ProximityGap.epsMCA_le_ofReal_of_listFactor_two_delta
#print axioms ProximityGap.epsMCA_le_ofReal_of_listFactor_two_delta_univ

/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.KKH26CeilingMarch

/-!
# The Poisson ceiling floor, Part A: the exact incidence counts (#371, cycle 2 S1′)

The probe-discovered **Poisson ceiling law** (five field sizes, 1–3%):
`E[badcount at the ceiling] = q(1 − e^{−C(n,k+1)/q})`.  Since `sup ≥ mean`, its
Bonferroni lower bound is an **unconditional, census-free bad side** for the ceiling
radius of every fixed-dimension evaluation code — no cyclotomic injectivity, no
`(2^μ)^{2^{μ−1}}` threshold, no Landau resultants, no Thorner–Zaman supply.

**This file (Part A)** proves the exact counting core:

1. *(the solve-one-coordinate characterization)* `explainableOn_iff_solve`: on a
   `(d+2)`-subset `T`, a word is explainable at degree `d` iff its value at any chosen
   `i₀ ∈ T` equals the Lagrange evaluation of its other `d+1` values — explainability on
   a minimal overdetermined set is ONE solved coordinate.
2. *(the singleton count)* `card_explainable_words`: exactly `q^{n−1}` words of `F^n`
   are explainable on a fixed `(d+2)`-subset.
3. *(the direction count)* `card_not_explainable_words`: exactly `q^n − q^{n−1}` words
   are NOT explainable on a fixed `(d+2)`-subset.
4. *(the pair count, the triangular solve)* `card_explainable_words_pair`: for distinct
   `(d+2)`-subsets exactly `q^{n−2}` words are explainable on both — choosing
   `i₀ ∈ T \ T'` and `i₁ ∈ T' \ T`, the `T'`-completion reads neither special
   coordinate, so the constraint system is triangular: solve `i₁`, then `i₀`.

Part B2 (next) adds pointwise Bonferroni and assembles everything into
`ε_mca(evalCode, 1 − (d+2)/n) ≥ (C(n,d+2) − corrections)/q ≥ C(n,d+2)/(4q)` for
`2·C(n,d+2) ≤ q`, and the census-free pin family it opens (bands
`[(C(n,r)/r)/q, C(n,r)/(4q))`, nonempty for every `r ≥ 5` — every `μ`, polynomial
thresholds, the μ = 7 wall removed).

Probe: `probe_poisson_ceiling_law.py` (to land with Part B).

Axiom-clean (`propext`, `Classical.choice`, `Quot.sound`); no `sorry`.
-/

set_option linter.unusedSectionVars false
set_option maxHeartbeats 1600000

open Finset Polynomial
open scoped NNReal ENNReal
open ArkLib.ProximityGap.KKH26CeilingMarch

namespace ArkLib.ProximityGap.PoissonCeilingFloor

variable {p : ℕ} [Fact p.Prime] {g : ZMod p} {n : ℕ} [NeZero n]

/-! ## The solve-one-coordinate characterization -/

open Classical in
/-- The Lagrange completion: the value at `i₀` of the degree-`≤ d` interpolant through
the values of `v` on `T.erase i₀`. -/
noncomputable def lagrangeCompletion (g : ZMod p) (i₀ : Fin n) (T : Finset (Fin n))
    (v : Fin n → ZMod p) : ZMod p :=
  (Lagrange.interpolate (T.erase i₀) (fun i : Fin n => g ^ (i : ℕ)) v).eval (g ^ (i₀ : ℕ))

open Classical in
/-- **The solve-one-coordinate characterization**: on a `(d+2)`-set `T`, explainability
at degree `d` says exactly that the value at a chosen `i₀ ∈ T` is the Lagrange completion
of the other `d + 1` values. -/
theorem explainableOn_iff_solve (hg : orderOf g = n) {d : ℕ} {T : Finset (Fin n)}
    (hT : T.card = d + 2) {i₀ : Fin n} (hi₀ : i₀ ∈ T) (v : Fin n → ZMod p) :
    ExplainableOn g d v T ↔ v i₀ = lagrangeCompletion g i₀ T v := by
  have hcard : (T.erase i₀).card = d + 1 := by
    rw [Finset.card_erase_of_mem hi₀, hT]
    omega
  have hdeg : (Lagrange.interpolate (T.erase i₀) (fun i : Fin n => g ^ (i : ℕ)) v).natDegree
      ≤ d := by
    have hlt := Lagrange.degree_interpolate_lt (r := v)
      (nodes_injOn hg (T.erase i₀))
    rcases eq_or_ne (Lagrange.interpolate (T.erase i₀) (fun i : Fin n => g ^ (i : ℕ)) v) 0
      with h0 | h0
    · rw [h0]; simp
    · have := (Polynomial.natDegree_lt_iff_degree_lt h0).mpr hlt
      omega
  constructor
  · rintro ⟨q, hqd, hq⟩
    -- q agrees with the interpolant on T.erase i₀ (d+1 nodes) hence everywhere
    have heq : q = Lagrange.interpolate (T.erase i₀) (fun i : Fin n => g ^ (i : ℕ)) v := by
      refine explain_unique hg hqd hdeg (le_of_eq hcard.symm) (fun i hi => ?_)
      rw [← hq i (Finset.mem_of_mem_erase hi)]
      exact (Lagrange.eval_interpolate_at_node v (nodes_injOn hg (T.erase i₀)) hi).symm
    rw [hq i₀ hi₀, heq]
    unfold lagrangeCompletion
    rfl
  · intro hsolve
    refine ⟨Lagrange.interpolate (T.erase i₀) (fun i : Fin n => g ^ (i : ℕ)) v, hdeg,
      fun i hi => ?_⟩
    by_cases hii : i = i₀
    · subst hii
      exact hsolve
    · exact (Lagrange.eval_interpolate_at_node v
        (nodes_injOn hg (T.erase i₀)) (Finset.mem_erase.mpr ⟨hii, hi⟩)).symm

/-! ## The exact counts -/

open Classical in
/-- The completion only reads values on `T.erase i₀`. -/
theorem lagrangeCompletion_congr (g : ZMod p) (i₀ : Fin n) (T : Finset (Fin n))
    {v w : Fin n → ZMod p} (h : ∀ i ∈ T.erase i₀, v i = w i) :
    lagrangeCompletion g i₀ T v = lagrangeCompletion g i₀ T w := by
  unfold lagrangeCompletion
  congr 1
  exact Lagrange.interpolate_eq_of_values_eq_on _ _ h

open Classical in
/-- **The singleton count**: exactly `q^{n−1}` words are explainable on a fixed
`(d+2)`-subset — explainability on a minimal overdetermined set is one solved
coordinate. -/
theorem card_explainable_words (hg : orderOf g = n) {d : ℕ} {T : Finset (Fin n)}
    (hT : T.card = d + 2) {i₀ : Fin n} (hi₀ : i₀ ∈ T) :
    (Finset.univ.filter (fun v : Fin n → ZMod p => ExplainableOn g d v T)).card
      = p ^ (n - 1) := by
  classical
  have htarget : Fintype.card ({j : Fin n // j ≠ i₀} → ZMod p) = p ^ (n - 1) := by
    have h1 : Fintype.card {j : Fin n // j ≠ i₀} = n - 1 := by
      rw [Fintype.card_subtype_compl, Fintype.card_subtype_eq, Fintype.card_fin]
    rw [Fintype.card_fun, h1, ZMod.card]
  -- the zero-padded reading of a restricted word
  set pad : ({j : Fin n // j ≠ i₀} → ZMod p) → (Fin n → ZMod p) :=
    fun w i => if h : i = i₀ then 0 else w ⟨i, h⟩ with hpad
  set ext : ({j : Fin n // j ≠ i₀} → ZMod p) → (Fin n → ZMod p) :=
    fun w i => if h : i = i₀ then lagrangeCompletion g i₀ T (pad w) else w ⟨i, h⟩
    with hext
  have hext_off : ∀ (w : {j : Fin n // j ≠ i₀} → ZMod p) (i : Fin n) (h : i ≠ i₀),
      ext w i = w ⟨i, h⟩ := by
    intro w i h
    simp [hext, h]
  have hext_read : ∀ w : {j : Fin n // j ≠ i₀} → ZMod p,
      lagrangeCompletion g i₀ T (ext w) = lagrangeCompletion g i₀ T (pad w) := by
    intro w
    refine lagrangeCompletion_congr g i₀ T (fun i hi => ?_)
    have hne : i ≠ i₀ := (Finset.mem_erase.mp hi).1
    simp [hext, hpad, hne]
  rw [show p ^ (n - 1) = Fintype.card ({j : Fin n // j ≠ i₀} → ZMod p) from htarget.symm,
    ← Finset.card_univ]
  refine Finset.card_bij'
    (fun (v : Fin n → ZMod p) _ => fun i : {j : Fin n // j ≠ i₀} => v i.1)
    (fun w _ => ext w) ?_ ?_ ?_ ?_
  · intro v _
    exact Finset.mem_univ _
  · intro w _
    refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩
    rw [explainableOn_iff_solve hg hT hi₀]
    calc ext w i₀ = lagrangeCompletion g i₀ T (pad w) := by simp [hext]
    _ = lagrangeCompletion g i₀ T (ext w) := (hext_read w).symm
  · intro v hv
    funext i
    dsimp only
    by_cases hii : i = i₀
    · rw [hii]
      have hv' := (Finset.mem_filter.mp hv).2
      rw [explainableOn_iff_solve hg hT hi₀] at hv'
      calc ext (fun j : {j : Fin n // j ≠ i₀} => v j.1) i₀
          = lagrangeCompletion g i₀ T (pad (fun j : {j : Fin n // j ≠ i₀} => v j.1)) := by
            simp [hext]
      _ = lagrangeCompletion g i₀ T v := by
            refine lagrangeCompletion_congr g i₀ T (fun i hi => ?_)
            have hne : i ≠ i₀ := (Finset.mem_erase.mp hi).1
            simp [hpad, hne]
      _ = v i₀ := hv'.symm
    · exact hext_off (fun j : {j : Fin n // j ≠ i₀} => v j.1) i hii
  · intro w _
    funext i
    dsimp only
    rw [hext_off w i.1 i.2]

open Classical in
/-- **The complement count**: exactly `q^n − q^{n−1}` words are NOT explainable on a
fixed `(d+2)`-subset. -/
theorem card_not_explainable_words (hg : orderOf g = n) {d : ℕ} {T : Finset (Fin n)}
    (hT : T.card = d + 2) {i₀ : Fin n} (hi₀ : i₀ ∈ T) :
    (Finset.univ.filter (fun v : Fin n → ZMod p => ¬ ExplainableOn g d v T)).card
      = p ^ n - p ^ (n - 1) := by
  classical
  have hsplit := Finset.card_filter_add_card_filter_not
    (s := (Finset.univ : Finset (Fin n → ZMod p)))
    (fun v => ExplainableOn g d v T)
  have htot : (Finset.univ : Finset (Fin n → ZMod p)).card = p ^ n := by
    rw [Finset.card_univ, Fintype.card_fun, ZMod.card, Fintype.card_fin]
  have hexp := card_explainable_words hg hT hi₀ (g := g)
  omega

end ArkLib.ProximityGap.PoissonCeilingFloor



/-! ## Axiom audit — kernel-clean. -/
#print axioms ArkLib.ProximityGap.PoissonCeilingFloor.explainableOn_iff_solve
#print axioms ArkLib.ProximityGap.PoissonCeilingFloor.card_explainable_words
#print axioms ArkLib.ProximityGap.PoissonCeilingFloor.card_not_explainable_words

namespace ArkLib.ProximityGap.PoissonCeilingFloor

variable {p : ℕ} [Fact p.Prime] {g : ZMod p} {n : ℕ} [NeZero n]

/-! ## Part B1: the pair count — the triangular solve -/

open Classical in
/-- **The pair count**: for distinct `(d+2)`-subsets `T ≠ T'`, exactly `q^{n−2}` words are
explainable on both.  The system is *triangular*: choosing `i₀ ∈ T \ T'` and
`i₁ ∈ T' \ T`, the `T'`-completion reads `T'.erase i₁` (neither special coordinate), so
it is determined by the free coordinates alone; the `T`-completion reads `T.erase i₀`
(which may contain `i₁`, already determined).  Two solved coordinates: `q^{n−2}`. -/
theorem card_explainable_words_pair (hg : orderOf g = n) {d : ℕ}
    {T T' : Finset (Fin n)} (hT : T.card = d + 2) (hT' : T'.card = d + 2)
    (hne : T ≠ T') :
    (Finset.univ.filter (fun v : Fin n → ZMod p =>
        ExplainableOn g d v T ∧ ExplainableOn g d v T')).card
      = p ^ (n - 2) := by
  classical
  obtain ⟨i₀, hi₀T, hi₀T'⟩ : ∃ i, i ∈ T ∧ i ∉ T' := by
    by_contra hc
    push Not at hc
    exact hne (Finset.eq_of_subset_of_card_le (fun x hx => hc x hx)
      (le_of_eq (hT'.trans hT.symm)))
  obtain ⟨i₁, hi₁T', hi₁T⟩ : ∃ i, i ∈ T' ∧ i ∉ T := by
    by_contra hc
    push Not at hc
    exact hne (Finset.eq_of_subset_of_card_le (fun x hx => hc x hx)
      (le_of_eq (hT.trans hT'.symm))).symm
  have hi₀₁ : i₀ ≠ i₁ := fun h => hi₀T' (h ▸ hi₁T')
  have htarget : Fintype.card ({j : Fin n // j ≠ i₀ ∧ j ≠ i₁} → ZMod p) = p ^ (n - 2) := by
    have h1 : Fintype.card {j : Fin n // j ≠ i₀ ∧ j ≠ i₁} = n - 2 := by
      have he : Fintype.card {j : Fin n // j ≠ i₀ ∧ j ≠ i₁}
          = ((Finset.univ : Finset (Fin n)).filter (fun j => j ≠ i₀ ∧ j ≠ i₁)).card :=
        Fintype.card_subtype _
      have hsplit : (Finset.univ : Finset (Fin n)).filter (fun j => j ≠ i₀ ∧ j ≠ i₁)
          = (Finset.univ \ {i₀, i₁}) := by
        ext j
        simp [Finset.mem_sdiff, not_or, and_comm]
      rw [he, hsplit, Finset.card_sdiff, Finset.inter_univ, Finset.card_univ,
        Fintype.card_fin, Finset.card_insert_of_notMem (by simp [hi₀₁]),
        Finset.card_singleton]
    rw [Fintype.card_fun, h1, ZMod.card]
  set pad : ({j : Fin n // j ≠ i₀ ∧ j ≠ i₁} → ZMod p) → (Fin n → ZMod p) :=
    fun w i => if h : i = i₀ ∨ i = i₁ then 0 else w ⟨i, by tauto⟩ with hpad
  set step1 : ({j : Fin n // j ≠ i₀ ∧ j ≠ i₁} → ZMod p) → (Fin n → ZMod p) :=
    fun w i => if h : i = i₁ then lagrangeCompletion g i₁ T' (pad w) else pad w i
    with hstep1
  set ext2 : ({j : Fin n // j ≠ i₀ ∧ j ≠ i₁} → ZMod p) → (Fin n → ZMod p) :=
    fun w i => if h : i = i₀ then lagrangeCompletion g i₀ T (step1 w) else step1 w i
    with hext2
  have hT'sub : ∀ i ∈ T'.erase i₁, i ≠ i₀ ∧ i ≠ i₁ := by
    intro i hi
    exact ⟨fun h => hi₀T' (h ▸ Finset.mem_of_mem_erase hi), (Finset.mem_erase.mp hi).1⟩
  have hstep1_off : ∀ w (i : Fin n), i ≠ i₁ → step1 w i = pad w i := by
    intro w i h
    simp [hstep1, h]
  have hext2_off : ∀ w (i : Fin n), i ≠ i₀ → ext2 w i = step1 w i := by
    intro w i h
    simp [hext2, h]
  have hext2_free : ∀ w (i : Fin n) (h : i ≠ i₀ ∧ i ≠ i₁), ext2 w i = w ⟨i, h⟩ := by
    intro w i h
    rw [hext2_off w i h.1, hstep1_off w i h.2]
    simp [hpad, h.1, h.2]
  have hcompl1 : ∀ w, lagrangeCompletion g i₁ T' (ext2 w)
      = lagrangeCompletion g i₁ T' (pad w) := by
    intro w
    refine lagrangeCompletion_congr g i₁ T' (fun i hi => ?_)
    obtain ⟨h0, h1⟩ := hT'sub i hi
    rw [hext2_off w i h0, hstep1_off w i h1]
  have hcompl2 : ∀ w, lagrangeCompletion g i₀ T (ext2 w)
      = lagrangeCompletion g i₀ T (step1 w) := by
    intro w
    refine lagrangeCompletion_congr g i₀ T (fun i hi => ?_)
    exact hext2_off w i (Finset.mem_erase.mp hi).1
  have hboth : ∀ w, ExplainableOn g d (ext2 w) T ∧ ExplainableOn g d (ext2 w) T' := by
    intro w
    constructor
    · rw [explainableOn_iff_solve hg hT hi₀T]
      calc ext2 w i₀ = lagrangeCompletion g i₀ T (step1 w) := by simp [hext2]
      _ = lagrangeCompletion g i₀ T (ext2 w) := (hcompl2 w).symm
    · rw [explainableOn_iff_solve hg hT' hi₁T']
      calc ext2 w i₁ = step1 w i₁ := hext2_off w i₁ (Ne.symm hi₀₁)
      _ = lagrangeCompletion g i₁ T' (pad w) := by simp [hstep1]
      _ = lagrangeCompletion g i₁ T' (ext2 w) := (hcompl1 w).symm
  rw [show p ^ (n - 2)
      = Fintype.card ({j : Fin n // j ≠ i₀ ∧ j ≠ i₁} → ZMod p) from htarget.symm,
    ← Finset.card_univ]
  refine Finset.card_bij'
    (fun (v : Fin n → ZMod p) _ => fun i : {j : Fin n // j ≠ i₀ ∧ j ≠ i₁} => v i.1)
    (fun w _ => ext2 w) ?_ ?_ ?_ ?_
  · intro v _
    exact Finset.mem_univ _
  · intro w _
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hboth w⟩
  · intro v hv
    funext i
    dsimp only
    obtain ⟨hvT, hvT'⟩ := (Finset.mem_filter.mp hv).2
    set vr : {j : Fin n // j ≠ i₀ ∧ j ≠ i₁} → ZMod p :=
      fun k => v k.1 with hvr
    -- the padded restriction agrees with v on T'.erase i₁
    have hpadv : ∀ l ∈ T'.erase i₁, pad vr l = v l := by
      intro l hl
      obtain ⟨hl0, hl1⟩ := hT'sub l hl
      simp [hpad, hvr, hl0, hl1]
    -- step1 of the restriction agrees with v on T.erase i₀
    have hstep1v : ∀ j ∈ T.erase i₀, step1 vr j = v j := by
      intro j hj
      have hj₀ : j ≠ i₀ := (Finset.mem_erase.mp hj).1
      by_cases hj₁ : j = i₁
      · rw [hj₁]
        rw [explainableOn_iff_solve hg hT' hi₁T'] at hvT'
        calc step1 vr i₁ = lagrangeCompletion g i₁ T' (pad vr) := by simp [hstep1]
        _ = lagrangeCompletion g i₁ T' v := lagrangeCompletion_congr g i₁ T' hpadv
        _ = v i₁ := hvT'.symm
      · rw [hstep1_off vr j hj₁]
        simp [hpad, hvr, hj₀, hj₁]
    by_cases h₀ : i = i₀
    · rw [h₀]
      rw [explainableOn_iff_solve hg hT hi₀T] at hvT
      calc ext2 vr i₀ = lagrangeCompletion g i₀ T (step1 vr) := by simp [hext2]
      _ = lagrangeCompletion g i₀ T v := lagrangeCompletion_congr g i₀ T hstep1v
      _ = v i₀ := hvT.symm
    · by_cases h₁ : i = i₁
      · rw [h₁]
        rw [explainableOn_iff_solve hg hT' hi₁T'] at hvT'
        calc ext2 vr i₁ = step1 vr i₁ := hext2_off vr i₁ (Ne.symm hi₀₁)
        _ = lagrangeCompletion g i₁ T' (pad vr) := by simp [hstep1]
        _ = lagrangeCompletion g i₁ T' v := lagrangeCompletion_congr g i₁ T' hpadv
        _ = v i₁ := hvT'.symm
      · exact hext2_free vr i ⟨h₀, h₁⟩
  · intro w _
    funext k
    dsimp only
    exact hext2_free w k.1 k.2

end ArkLib.ProximityGap.PoissonCeilingFloor

#print axioms ArkLib.ProximityGap.PoissonCeilingFloor.card_explainable_words_pair

namespace ArkLib.ProximityGap.PoissonCeilingFloor

/-! ## Part B2a: pointwise Bonferroni (ordered-pair, ℕ-clean form) -/

open Classical in
/-- **Bonferroni, second order**: over any finite family,
`2·Σ_T |A_T| ≤ 2·|⋃ A_T| + Σ_{(T,T') distinct ordered} |A_T ∩ A_T'|`.  Pointwise this is
`2m ≤ 2 + m(m−1)` for multiplicity `m ≥ 1`. -/
theorem two_mul_sum_card_le {α β : Type} [DecidableEq α] [DecidableEq β]
    (𝒯 : Finset β) (A : β → Finset α) :
    2 * ∑ T ∈ 𝒯, (A T).card
      ≤ 2 * (𝒯.biUnion A).card
        + ∑ TT' ∈ 𝒯.offDiag, (A TT'.1 ∩ A TT'.2).card := by
  classical
  set U := 𝒯.biUnion A with hU
  -- single counts through U
  have hsub : ∀ T ∈ 𝒯, A T ⊆ U := fun T hT x hx =>
    Finset.mem_biUnion.mpr ⟨T, hT, hx⟩
  have hsingle : ∀ T ∈ 𝒯, (A T).card
      = ∑ x ∈ U, (if x ∈ A T then 1 else 0) := by
    intro T hT
    rw [Finset.sum_ite_mem U (A T) (fun _ => 1)]
    rw [Finset.inter_comm, Finset.inter_eq_left.mpr (hsub T hT)]
    simp
  -- pair counts through U
  have hpair : ∀ TT' ∈ 𝒯.offDiag, (A TT'.1 ∩ A TT'.2).card
      = ∑ x ∈ U, (if x ∈ A TT'.1 ∧ x ∈ A TT'.2 then 1 else 0) := by
    intro TT' hTT'
    have hmem := Finset.mem_offDiag.mp hTT'
    have hsubI : A TT'.1 ∩ A TT'.2 ⊆ U :=
      subset_trans (Finset.inter_subset_left) (hsub _ hmem.1)
    calc (A TT'.1 ∩ A TT'.2).card
        = ∑ x ∈ U, (if x ∈ A TT'.1 ∩ A TT'.2 then 1 else 0) := by
          rw [Finset.sum_ite_mem U (A TT'.1 ∩ A TT'.2) (fun _ => 1)]
          rw [Finset.inter_comm U (A TT'.1 ∩ A TT'.2), Finset.inter_eq_left.mpr hsubI]
          simp
    _ = ∑ x ∈ U, (if x ∈ A TT'.1 ∧ x ∈ A TT'.2 then 1 else 0) :=
        Finset.sum_congr rfl (fun x _ =>
          if_congr (by simp [Finset.mem_inter]) rfl rfl)
  -- the multiplicity of a point
  set m : α → ℕ := fun x => (𝒯.filter (fun T => x ∈ A T)).card with hm
  have hswap1 : (∑ T ∈ 𝒯, (A T).card) = ∑ x ∈ U, m x := by
    rw [Finset.sum_congr rfl hsingle, Finset.sum_comm]
    refine Finset.sum_congr rfl (fun x _ => ?_)
    exact (Finset.card_filter _ _).symm
  have hswap2 : (∑ TT' ∈ 𝒯.offDiag, (A TT'.1 ∩ A TT'.2).card)
      = ∑ x ∈ U, (m x * m x - m x) := by
    rw [Finset.sum_congr rfl hpair, Finset.sum_comm]
    refine Finset.sum_congr rfl (fun x _ => ?_)
    have hoff : (𝒯.offDiag.filter
        (fun TT' : β × β => x ∈ A TT'.1 ∧ x ∈ A TT'.2))
        = (𝒯.filter (fun T => x ∈ A T)).offDiag := by
      ext TT'
      simp only [Finset.mem_filter, Finset.mem_offDiag]
      tauto
    calc (∑ TT' ∈ 𝒯.offDiag, if x ∈ A TT'.1 ∧ x ∈ A TT'.2 then 1 else 0)
        = (𝒯.offDiag.filter
            (fun TT' : β × β => x ∈ A TT'.1 ∧ x ∈ A TT'.2)).card :=
          (Finset.card_filter _ _).symm
    _ = ((𝒯.filter (fun T => x ∈ A T)).offDiag).card := by rw [hoff]
    _ = m x * m x - m x := by
          rw [Finset.offDiag_card]
  -- the multiplicity is positive on U
  have hpos : ∀ x ∈ U, 1 ≤ m x := by
    intro x hx
    obtain ⟨T, hT, hxT⟩ := Finset.mem_biUnion.mp hx
    exact Finset.card_pos.mpr ⟨T, Finset.mem_filter.mpr ⟨hT, hxT⟩⟩
  -- pointwise: 2m ≤ 2 + (m² − m) for m ≥ 1
  have hptw : ∀ x ∈ U, 2 * m x ≤ 2 + (m x * m x - m x) := by
    intro x hx
    have h1 := hpos x hx
    have key : 3 * m x ≤ m x * m x + 2 := by
      rcases Nat.lt_or_ge (m x) 3 with h | h
      · have h12 : m x = 1 ∨ m x = 2 := by omega
        rcases h12 with h' | h' <;> rw [h'] <;> norm_num
      · have h3 : 3 * m x ≤ m x * m x := Nat.mul_le_mul_right _ h
        omega
    have hsq : m x ≤ m x * m x := Nat.le_mul_of_pos_left _ (by omega)
    omega
  -- assemble
  calc 2 * ∑ T ∈ 𝒯, (A T).card = 2 * ∑ x ∈ U, m x := by rw [hswap1]
  _ = ∑ x ∈ U, 2 * m x := by rw [Finset.mul_sum]
  _ ≤ ∑ x ∈ U, (2 + (m x * m x - m x)) := Finset.sum_le_sum hptw
  _ = 2 * U.card + ∑ x ∈ U, (m x * m x - m x) := by
      rw [Finset.sum_add_distrib, Finset.sum_const, smul_eq_mul, Nat.mul_comm]
  _ = 2 * U.card + ∑ TT' ∈ 𝒯.offDiag, (A TT'.1 ∩ A TT'.2).card := by rw [hswap2]

end ArkLib.ProximityGap.PoissonCeilingFloor

#print axioms ArkLib.ProximityGap.PoissonCeilingFloor.two_mul_sum_card_le

namespace ArkLib.ProximityGap.PoissonCeilingFloor

variable {p : ℕ} [Fact p.Prime] {g : ZMod p} {n : ℕ} [NeZero n]

/-! ## Part B2b-i: the master union count over the `(W, U)`-space -/

open Classical in
/-- **The master count**: under `C + 1 ≤ q` (`C = C(n,d+2)`), the configurations
`(W, U)` with some `(d+2)`-tuple `T` carrying an explanation of `W` and a
non-explanation of `U` number at least `C·q^{2n−1}/2` (stated doubled, ℕ-clean). -/
theorem card_union_ge (hg : orderOf g = n) {d : ℕ} (hdn : d + 2 ≤ n)
    (hq : n.choose (d + 2) + 1 ≤ p) :
    n.choose (d + 2) * p ^ (2 * n - 1)
      ≤ 2 * ((Finset.powersetCard (d + 2) (Finset.univ : Finset (Fin n))).biUnion
          (fun T => (Finset.univ.filter (fun W : Fin n → ZMod p => ExplainableOn g d W T))
            ×ˢ (Finset.univ.filter (fun U : Fin n → ZMod p => ¬ ExplainableOn g d U T)))).card := by
  classical
  haveI : NeZero p := ⟨(Fact.out : p.Prime).ne_zero⟩
  set 𝒯 := Finset.powersetCard (d + 2) (Finset.univ : Finset (Fin n)) with h𝒯
  set A : Finset (Fin n) → Finset ((Fin n → ZMod p) × (Fin n → ZMod p)) :=
    fun T => (Finset.univ.filter (fun W : Fin n → ZMod p => ExplainableOn g d W T))
      ×ˢ (Finset.univ.filter (fun U : Fin n → ZMod p => ¬ ExplainableOn g d U T)) with hA
  have hcard𝒯 : 𝒯.card = n.choose (d + 2) := by
    rw [h𝒯, Finset.card_powersetCard, Finset.card_univ, Fintype.card_fin]
  have hmemT : ∀ T ∈ 𝒯, T.card = d + 2 := fun T hT =>
    (Finset.mem_powersetCard.mp hT).2
  have hTne : ∀ T ∈ 𝒯, ∃ i₀, i₀ ∈ T := by
    intro T hT
    have := hmemT T hT
    exact Finset.card_pos.mp (by omega)
  -- the single count
  have hsingle : ∀ T ∈ 𝒯, (A T).card = p ^ (n - 1) * (p ^ n - p ^ (n - 1)) := by
    intro T hT
    obtain ⟨i₀, hi₀⟩ := hTne T hT
    rw [hA]
    rw [Finset.card_product]
    rw [card_explainable_words hg (hmemT T hT) hi₀,
      card_not_explainable_words hg (hmemT T hT) hi₀]
  -- the pair bound
  have hpair : ∀ TT' ∈ 𝒯.offDiag, (A TT'.1 ∩ A TT'.2).card ≤ p ^ (n - 2) * p ^ n := by
    intro TT' hTT'
    obtain ⟨hT1, hT2, hne⟩ := Finset.mem_offDiag.mp hTT'
    have hsub : A TT'.1 ∩ A TT'.2
        ⊆ (Finset.univ.filter (fun W : Fin n → ZMod p =>
            ExplainableOn g d W TT'.1 ∧ ExplainableOn g d W TT'.2)) ×ˢ Finset.univ := by
      intro x hx
      obtain ⟨hx1, hx2⟩ := Finset.mem_inter.mp hx
      rw [hA] at hx1 hx2
      obtain ⟨hW1, _⟩ := Finset.mem_product.mp hx1
      obtain ⟨hW2, _⟩ := Finset.mem_product.mp hx2
      refine Finset.mem_product.mpr ⟨?_, Finset.mem_univ _⟩
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,
        (Finset.mem_filter.mp hW1).2, (Finset.mem_filter.mp hW2).2⟩
    calc (A TT'.1 ∩ A TT'.2).card
        ≤ ((Finset.univ.filter (fun W : Fin n → ZMod p =>
            ExplainableOn g d W TT'.1 ∧ ExplainableOn g d W TT'.2)) ×ˢ
            (Finset.univ : Finset (Fin n → ZMod p))).card := Finset.card_le_card hsub
    _ = p ^ (n - 2) * p ^ n := by
        rw [Finset.card_product,
          card_explainable_words_pair hg (hmemT _ hT1) (hmemT _ hT2) hne,
          Finset.card_univ, Fintype.card_fun, ZMod.card, Fintype.card_fin]
  -- Bonferroni
  have hbonf := two_mul_sum_card_le 𝒯 A
  have hsum1 : (∑ T ∈ 𝒯, (A T).card)
      = n.choose (d + 2) * (p ^ (n - 1) * (p ^ n - p ^ (n - 1))) := by
    rw [Finset.sum_congr rfl hsingle, Finset.sum_const, smul_eq_mul, hcard𝒯]
  have hsum2 : (∑ TT' ∈ 𝒯.offDiag, (A TT'.1 ∩ A TT'.2).card)
      ≤ (n.choose (d + 2) * n.choose (d + 2)) * (p ^ (n - 2) * p ^ n) := by
    calc (∑ TT' ∈ 𝒯.offDiag, (A TT'.1 ∩ A TT'.2).card)
        ≤ ∑ _TT' ∈ 𝒯.offDiag, p ^ (n - 2) * p ^ n := Finset.sum_le_sum hpair
    _ = 𝒯.offDiag.card * (p ^ (n - 2) * p ^ n) := by
        rw [Finset.sum_const, smul_eq_mul]
    _ ≤ (n.choose (d + 2) * n.choose (d + 2)) * (p ^ (n - 2) * p ^ n) := by
        refine Nat.mul_le_mul_right _ ?_
        rw [Finset.offDiag_card, hcard𝒯]
        omega
  -- power algebra: everything reduces to the atom S = Q²p², Q = p^{n−2}
  have hn2 : 2 ≤ n := by omega
  set C := n.choose (d + 2) with hC
  set Q := p ^ (n - 2) with hQ
  have hppos : 1 ≤ p := (Fact.out : p.Prime).one_lt.le
  set S := Q * Q * (p * p) with hS
  have hX : p ^ (2 * n - 1) = S * p := by
    rw [hS, hQ, show p * p = p ^ 2 from (sq p).symm, ← pow_add, ← pow_add, ← pow_succ]
    congr 1
    omega
  have hY : Q * p ^ n = S := by
    rw [hS, hQ, show p * p = p ^ 2 from (sq p).symm, ← pow_add, ← pow_add, ← pow_add]
    congr 1
    omega
  have hsingle' : p ^ (n - 1) * (p ^ n - p ^ (n - 1)) = S * p - S := by
    have h1 : p ^ (n - 1) * p ^ n = S * p := by
      rw [hS, hQ, show p * p = p ^ 2 from (sq p).symm, ← pow_add, ← pow_add, ← pow_add,
        ← pow_succ]
      congr 1
      omega
    have h2 : p ^ (n - 1) * p ^ (n - 1) = S := by
      rw [hS, hQ, show p * p = p ^ 2 from (sq p).symm, ← pow_add, ← pow_add, ← pow_add]
      congr 1
      omega
    rw [Nat.mul_sub, h1, h2]
  -- the factored comparison: (C² + C)·S ≤ C·S·p  from  C + 1 ≤ p
  have hfac : C * C * S + C * S ≤ C * (S * p) := by
    calc C * C * S + C * S = (C * (C + 1)) * S := by ring
    _ ≤ (C * p) * S := Nat.mul_le_mul_right _ (Nat.mul_le_mul_left _ hq)
    _ = C * (S * p) := by ring
  have hbS : C * S ≤ C * (S * p) := by
    calc C * S = C * (S * 1) := by rw [Nat.mul_one]
    _ ≤ C * (S * p) := by
        exact Nat.mul_le_mul_left _ (Nat.mul_le_mul_left _ hppos)
  have hccS : C * S ≤ C * C * S := by
    have hC1 : 1 ≤ C := by
      have := Nat.choose_pos (n := n) (k := d + 2) hdn
      omega
    calc C * S = 1 * (C * S) := (Nat.one_mul _).symm
    _ ≤ C * (C * S) := Nat.mul_le_mul_right _ hC1
    _ = C * C * S := by ring
  -- rewrite the three quantities in S-form
  have hsum1' : 2 * (∑ T ∈ 𝒯, (A T).card) = 2 * (C * (S * p)) - 2 * (C * S) := by
    rw [hsum1, hsingle']
    rw [Nat.mul_sub, Nat.mul_sub]
  have hsum2' : (∑ TT' ∈ 𝒯.offDiag, (A TT'.1 ∩ A TT'.2).card)
      ≤ C * C * S - C * S := by
    calc (∑ TT' ∈ 𝒯.offDiag, (A TT'.1 ∩ A TT'.2).card)
        ≤ 𝒯.offDiag.card * (p ^ (n - 2) * p ^ n) := by
          calc (∑ TT' ∈ 𝒯.offDiag, (A TT'.1 ∩ A TT'.2).card)
              ≤ ∑ _TT' ∈ 𝒯.offDiag, p ^ (n - 2) * p ^ n := Finset.sum_le_sum hpair
          _ = 𝒯.offDiag.card * (p ^ (n - 2) * p ^ n) := by
              rw [Finset.sum_const, smul_eq_mul]
    _ = (C * C - C) * (Q * p ^ n) := by
        rw [Finset.offDiag_card, hcard𝒯, hQ]
    _ = C * C * S - C * S := by
        rw [hY, Nat.sub_mul]
  -- assemble linearly
  have hbonf' := two_mul_sum_card_le 𝒯 A
  rw [hX]
  omega

end ArkLib.ProximityGap.PoissonCeilingFloor

#print axioms ArkLib.ProximityGap.PoissonCeilingFloor.card_union_ge

open ProximityGap ArkLib.ProximityGap.KKH26
open scoped ProbabilityTheory

namespace ArkLib.ProximityGap.PoissonCeilingFloor

variable {p : ℕ} [Fact p.Prime] {g : ZMod p} {n : ℕ} [NeZero n]

/-! ## Part B2b: the payoff — the census-free bad side -/

open Classical in
/-- A firing tuple produces an MCA-bad scalar: if `W` is explainable on the
`(d+2)`-set `T` and `U` is not, then `γ` is bad for the stack `(W − γU, U)` at the
ceiling radius. -/
theorem mcaEvent_of_tuple (hg : orderOf g = n) {d : ℕ} (hdn : d + 2 ≤ n)
    {T : Finset (Fin n)} (hT : T ∈ Finset.powersetCard (d + 2) (Finset.univ : Finset (Fin n)))
    {W U : Fin n → ZMod p} (hW : ExplainableOn g d W T) (hU : ¬ ExplainableOn g d U T)
    (γ : ZMod p) :
    mcaEvent (F := ZMod p) (A := ZMod p) (evalCode g n d)
      (1 - ((d + 2 : ℕ) : ℝ≥0) / ((n : ℕ) : ℝ≥0)) (fun i => W i - γ * U i) U γ := by
  obtain ⟨-, hTcard⟩ := Finset.mem_powersetCard.mp hT
  obtain ⟨qpoly, hqd, hqe⟩ := hW
  have hn0 : ((n : ℕ) : ℝ≥0) ≠ 0 := by
    exact_mod_cast Nat.cast_ne_zero.mpr (NeZero.ne n)
  have hle1 : ((d + 2 : ℕ) : ℝ≥0) / ((n : ℕ) : ℝ≥0) ≤ 1 := by
    rw [div_le_one (lt_of_le_of_ne (zero_le _) (Ne.symm hn0))]
    exact_mod_cast hdn
  refine ⟨T, ?_, ⟨fun i => qpoly.eval (g ^ (i : ℕ)), ⟨qpoly, hqd, fun i => rfl⟩,
    fun i hi => ?_⟩, ?_⟩
  · -- the witness size: (1 − δ)·n = d + 2 exactly
    rw [hTcard]
    have hcanc : (1 : ℝ≥0) - (1 - ((d + 2 : ℕ) : ℝ≥0) / ((n : ℕ) : ℝ≥0))
        = ((d + 2 : ℕ) : ℝ≥0) / ((n : ℕ) : ℝ≥0) := tsub_tsub_cancel_of_le hle1
    rw [hcanc]
    rw [show ((Fintype.card (Fin n) : ℕ) : ℝ≥0) = ((n : ℕ) : ℝ≥0) from by
      rw [Fintype.card_fin]]
    rw [div_mul_cancel₀ _ hn0]
  · -- agreement on T
    show qpoly.eval (g ^ (i : ℕ)) = (fun i => W i - γ * U i) i + γ • U i
    rw [smul_eq_mul]
    have := hqe i hi
    dsimp only
    rw [← this]
    ring
  · -- no joint explanation
    rintro ⟨v₀, hv₀, v₁, hv₁, hagree⟩
    obtain ⟨q₁, hq₁d, hq₁e⟩ := hv₁
    exact hU ⟨q₁, hq₁d, fun i hi => by rw [← (hagree i hi).2]; exact hq₁e i⟩

open Classical in
/-- **THE POISSON CEILING FLOOR** — the census-free bad side: at the ceiling radius
`1 − (d+2)/n`, the MCA error of the degree-`d` code is at least `C(n,d+2)/(2q)`, for
EVERY field with `C(n,d+2) + 1 ≤ q`.  No cyclotomic injectivity, no doubly-exponential
threshold, no resultants, no Thorner–Zaman — pure counting (`sup ≥ mean` over the
exact Poisson incidence structure). -/
theorem epsMCA_ceiling_ge (hg : orderOf g = n) {d : ℕ} (hdn : d + 2 ≤ n)
    (hq : n.choose (d + 2) + 1 ≤ p) :
    ((n.choose (d + 2) : ℕ) : ℝ≥0∞) / (2 * (p : ℝ≥0∞))
      ≤ epsMCA (F := ZMod p) (A := ZMod p) (evalCode g n d)
          (1 - ((d + 2 : ℕ) : ℝ≥0) / ((n : ℕ) : ℝ≥0)) := by
  classical
  haveI : NeZero p := ⟨(Fact.out : p.Prime).ne_zero⟩
  haveI : Nonempty (ZMod p) := ⟨0⟩
  set δ := (1 : ℝ≥0) - ((d + 2 : ℕ) : ℝ≥0) / ((n : ℕ) : ℝ≥0) with hδ
  set 𝒯 := Finset.powersetCard (d + 2) (Finset.univ : Finset (Fin n)) with h𝒯
  set A : Finset (Fin n) → Finset ((Fin n → ZMod p) × (Fin n → ZMod p)) :=
    fun T => (Finset.univ.filter (fun W : Fin n → ZMod p => ExplainableOn g d W T))
      ×ˢ (Finset.univ.filter (fun U : Fin n → ZMod p => ¬ ExplainableOn g d U T)) with hA
  set 𝒰 := 𝒯.biUnion A with h𝒰
  -- per-γ injection into the bad set
  have hγcount : ∀ γ : ZMod p, 𝒰.card
      ≤ (Finset.univ.filter (fun uu : (Fin n → ZMod p) × (Fin n → ZMod p) =>
          mcaEvent (F := ZMod p) (A := ZMod p) (evalCode g n d) δ uu.1 uu.2 γ)).card := by
    intro γ
    refine Finset.card_le_card_of_injOn
      (fun WU => ((fun i => WU.1 i - γ * WU.2 i), WU.2)) ?_ ?_
    · intro WU hWU
      obtain ⟨T, hT, hWU'⟩ := Finset.mem_biUnion.mp hWU
      rw [hA] at hWU'
      obtain ⟨hWmem, hUmem⟩ := Finset.mem_product.mp hWU'
      refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩
      exact mcaEvent_of_tuple hg hdn hT (Finset.mem_filter.mp hWmem).2
        (Finset.mem_filter.mp hUmem).2 γ
    · intro a _ b _ hab
      have hab' : ((fun i => a.1 i - γ * a.2 i), a.2)
          = ((fun i => b.1 i - γ * b.2 i), b.2) := hab
      obtain ⟨h1, h2⟩ := Prod.ext_iff.mp hab'
      refine Prod.ext ?_ h2
      funext i
      have hi1 : a.1 i - γ * a.2 i = b.1 i - γ * b.2 i := congrFun h1 i
      have hi2 : a.2 i = b.2 i := congrFun h2 i
      linear_combination hi1 + γ * hi2
  -- the master count
  have hmaster := card_union_ge (g := g) hg hdn hq
  rw [← h𝒯, ← hA, ← h𝒰] at hmaster
  -- sum over γ, swap, extract a heavy stack
  have hswap : (∑ γ : ZMod p,
      (Finset.univ.filter (fun uu : (Fin n → ZMod p) × (Fin n → ZMod p) =>
        mcaEvent (F := ZMod p) (A := ZMod p) (evalCode g n d) δ uu.1 uu.2 γ)).card)
      = ∑ uu : (Fin n → ZMod p) × (Fin n → ZMod p),
        (Finset.univ.filter (fun γ : ZMod p =>
          mcaEvent (F := ZMod p) (A := ZMod p) (evalCode g n d) δ uu.1 uu.2 γ)).card := by
    simp_rw [Finset.card_filter]
    exact Finset.sum_comm
  have hsumlow : p * 𝒰.card ≤ ∑ uu : (Fin n → ZMod p) × (Fin n → ZMod p),
      (Finset.univ.filter (fun γ : ZMod p =>
        mcaEvent (F := ZMod p) (A := ZMod p) (evalCode g n d) δ uu.1 uu.2 γ)).card := by
    rw [← hswap]
    calc p * 𝒰.card = ∑ _γ : ZMod p, 𝒰.card := by
          rw [Finset.sum_const, Finset.card_univ, ZMod.card, smul_eq_mul]
    _ ≤ _ := Finset.sum_le_sum (fun γ _ => hγcount γ)
  -- the stack space and its size
  have hstacks : Fintype.card ((Fin n → ZMod p) × (Fin n → ZMod p)) = p ^ (2 * n) := by
    rw [Fintype.card_prod, Fintype.card_fun, ZMod.card, Fintype.card_fin, ← pow_add]
    congr 1
    omega
  -- exists a stack with 2·badcount ≥ C
  have hexists : ∃ uu : (Fin n → ZMod p) × (Fin n → ZMod p),
      n.choose (d + 2) ≤ 2 * (Finset.univ.filter (fun γ : ZMod p =>
        mcaEvent (F := ZMod p) (A := ZMod p) (evalCode g n d) δ uu.1 uu.2 γ)).card := by
    by_contra hall
    push Not at hall
    have hbound : ∀ uu : (Fin n → ZMod p) × (Fin n → ZMod p),
        2 * (Finset.univ.filter (fun γ : ZMod p =>
          mcaEvent (F := ZMod p) (A := ZMod p) (evalCode g n d) δ uu.1 uu.2 γ)).card
        ≤ n.choose (d + 2) - 1 := by
      intro uu
      have := hall uu
      omega
    have hsumup : 2 * (∑ uu : (Fin n → ZMod p) × (Fin n → ZMod p),
        (Finset.univ.filter (fun γ : ZMod p =>
          mcaEvent (F := ZMod p) (A := ZMod p) (evalCode g n d) δ uu.1 uu.2 γ)).card)
        ≤ (n.choose (d + 2) - 1) * p ^ (2 * n) := by
      rw [Finset.mul_sum]
      calc (∑ uu : (Fin n → ZMod p) × (Fin n → ZMod p),
            2 * (Finset.univ.filter (fun γ : ZMod p =>
              mcaEvent (F := ZMod p) (A := ZMod p) (evalCode g n d) δ uu.1 uu.2 γ)).card)
          ≤ ∑ _uu : (Fin n → ZMod p) × (Fin n → ZMod p), (n.choose (d + 2) - 1) :=
            Finset.sum_le_sum (fun uu _ => hbound uu)
      _ = (n.choose (d + 2) - 1) * p ^ (2 * n) := by
          rw [Finset.sum_const, Finset.card_univ, hstacks, smul_eq_mul, Nat.mul_comm]
    -- but 2·Σ ≥ 2·p·|𝒰| ≥ C·p^{2n}
    have hlow2 : n.choose (d + 2) * p ^ (2 * n)
        ≤ 2 * (∑ uu : (Fin n → ZMod p) × (Fin n → ZMod p),
          (Finset.univ.filter (fun γ : ZMod p =>
            mcaEvent (F := ZMod p) (A := ZMod p) (evalCode g n d) δ uu.1 uu.2 γ)).card) := by
      calc n.choose (d + 2) * p ^ (2 * n)
          = (n.choose (d + 2) * p ^ (2 * n - 1)) * p := by
            rw [Nat.mul_assoc, ← pow_succ]
            congr 2
            omega
      _ ≤ (2 * 𝒰.card) * p := Nat.mul_le_mul_right _ hmaster
      _ = 2 * (p * 𝒰.card) := by ring
      _ ≤ _ := by
          have := hsumlow
          omega
    have hCpos : 1 ≤ n.choose (d + 2) := Nat.choose_pos hdn
    have hppos : 1 ≤ p ^ (2 * n) := Nat.one_le_pow _ _ (Fact.out : p.Prime).pos
    -- C·p^{2n} ≤ (C−1)·p^{2n} : contradiction
    have : n.choose (d + 2) * p ^ (2 * n) ≤ (n.choose (d + 2) - 1) * p ^ (2 * n) := by
      omega
    have hlt : (n.choose (d + 2) - 1) * p ^ (2 * n)
        < n.choose (d + 2) * p ^ (2 * n) :=
      (Nat.mul_lt_mul_right (by omega : 0 < p ^ (2 * n))).mpr (by omega)
    omega
  -- conclude through the sup
  obtain ⟨uu, huu⟩ := hexists
  unfold epsMCA
  refine le_trans ?_ (le_iSup _ ![uu.1, uu.2])
  rw [prob_uniform_eq_card_filter_div_card, ZMod.card p]
  rw [show (![uu.1, uu.2] : Fin 2 → Fin n → ZMod p) 0 = uu.1 from rfl,
    show (![uu.1, uu.2] : Fin 2 → Fin n → ZMod p) 1 = uu.2 from rfl]
  -- C/(2p) ≤ (2#B)/(2p) = #B/p  from  C ≤ 2#B (unification, not syntactic rw)
  refine le_trans (ENNReal.div_le_div_right ?_ (2 * (p : ℝ≥0∞)))
    (le_of_eq (ENNReal.mul_div_mul_left _ _ (by norm_num) (by norm_num)))
  exact_mod_cast huu

end ArkLib.ProximityGap.PoissonCeilingFloor

#print axioms ArkLib.ProximityGap.PoissonCeilingFloor.mcaEvent_of_tuple
#print axioms ArkLib.ProximityGap.PoissonCeilingFloor.epsMCA_ceiling_ge

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

Part B (next file) adds the pair count `q^{n−2}` (distinct tuples solve DISTINCT
coordinates: `i₀ ∈ T \ T'`, `i₀' ∈ T' \ T` — independence), pointwise Bonferroni, and
assembles everything into
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

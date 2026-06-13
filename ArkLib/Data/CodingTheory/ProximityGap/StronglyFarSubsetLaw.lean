/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.GeneralKMultiplicity
import Mathlib.LinearAlgebra.Lagrange

/-!
# The strongly-far subset law and the ratio-set identity (#371)

The unordered sharpening of the strongly-far law (`UniversalBelowUDR.lean`), and the
exact structure of the strongly-far bad set.  A direction `u₁` is **strongly far**
when no codeword agrees with it on more than `k` points.  Three results:

* **The subset law** (`stronglyFar_badScalars_card_mul_le_choose`): at every radius
  `δ ≤ w/n`,  `#bad · C(n−w, k+1) ≤ C(n, k+1)` — each bad scalar exclusively owns
  every `(k+1)`-subset of its witness.  This strictly dominates the landed ordered
  law (`C(n,k+1)/C(n−w,k+1) = n^{(k+1)}/(n−w)^{(k+1)} ≤ n^{k+1}/(n−w)^{(k+1)}`).

* **The ratio-set identity**: every bad scalar is a subset ratio
  `−e_T(u₀)/e_T(u₁)` (`stronglyFar_bad_subset_ratioSet`, radius-free: any valid
  witness must carry ≥ `k+1` points, since smaller sets always admit a joint
  Lagrange pair, killing the event's last clause) — and at every radius admitting
  `(k+1)`-point witnesses the inclusion is an **equality**
  (`stronglyFar_badSet_eq_ratioSet`): the joint clause is automatic for strongly-far
  directions on `(k+1)`-sets.  The far-class exact threshold value therefore
  reduces to counting distinct subset ratios.

* **The radius-free ceiling** (`stronglyFar_badScalars_card_le_choose`):
  `#bad ≤ C(n, k+1)` at EVERY radius — through the window, to capacity.  Probe-tight
  at the boundary slice (`probe_far_subset_law.py`: random far directions attain
  `56 = C(8,3)` at `n = 8, k = 2, δ = 5/8`, the tube-experiment measurement).

Dedup note: the multiplicity-1 boundary ceiling for the plain CA event is Round-17
`bad_card_le_choose` (`CAPairExtractionEngine.lean`, = ePrint 2026/858 Thm 7); strong
farness of `u₁` implies its pairwise-joint hypothesis.  New here: the radius-indexed
multiplicity factor, the `mcaEvent`/`rsCode` wiring, and the LOWER half (the identity
— Thm B has no converse).
-/

open Finset Polynomial
open scoped NNReal ENNReal ProbabilityTheory

namespace ProximityGap.Ownership

open ProximityGap.SpikeFloor ProximityGap

variable {F : Type} [Field F] [Fintype F] [DecidableEq F]
variable {n : ℕ} [NeZero n]

/-! ## The canonical enumeration of a `(k+1)`-subset -/

/-- The canonical (monotone) enumeration of a subset of known size. -/
noncomputable def canonTuple {k : ℕ} (T : Finset (Fin n)) (h : T.card = k + 1) :
    Fin (k + 1) → Fin n := fun a => ((T.orderIsoOfFin h) a : Fin n)

theorem canonTuple_injective {k : ℕ} (T : Finset (Fin n)) (h : T.card = k + 1) :
    Function.Injective (canonTuple T h) := fun a b hab =>
  (T.orderIsoOfFin h).injective (Subtype.ext hab)

theorem canonTuple_mem {k : ℕ} (T : Finset (Fin n)) (h : T.card = k + 1)
    (a : Fin (k + 1)) : canonTuple T h a ∈ T := ((T.orderIsoOfFin h) a).2

theorem canonTuple_surjOn {k : ℕ} (T : Finset (Fin n)) (h : T.card = k + 1)
    {i : Fin n} (hi : i ∈ T) : ∃ a : Fin (k + 1), canonTuple T h a = i :=
  ⟨(T.orderIsoOfFin h).symm ⟨i, hi⟩, by
    simp [canonTuple]⟩

/-! ## Strong farness through residuals -/

open Classical in
/-- Strong farness in residual form: every injective `(k+1)`-tuple has a
nonvanishing direction residual. -/
theorem residual_ne_zero_of_stronglyFar (dom : Fin n ↪ F) {k : ℕ}
    {u₁ : Fin n → F}
    (hμ : ∀ c ∈ (rsCode dom k : Submodule F (Fin n → F)),
      (agreeSet c u₁).card ≤ k)
    {t : Fin (k + 1) → Fin n} (htinj : Function.Injective t) :
    residual dom k t u₁ ≠ 0 := by
  intro hres
  obtain ⟨c, hcC, hcag⟩ := extension_of_residual_eq_zero dom t htinj hres
  have hsub : Finset.univ.image t ⊆ agreeSet c u₁ := by
    intro x hx
    obtain ⟨a, -, rfl⟩ := Finset.mem_image.mp hx
    rw [agreeSet, Finset.mem_filter]
    exact ⟨Finset.mem_univ _, hcag a⟩
  have hcard : k + 1 ≤ (agreeSet c u₁).card := by
    calc k + 1 = (Finset.univ.image t).card := by
          rw [Finset.card_image_of_injective _ htinj, Finset.card_univ,
            Fintype.card_fin]
      _ ≤ _ := Finset.card_le_card hsub
  have := hμ c hcC
  omega

open Classical in
/-- The converse — the decidable criterion for instances: nonvanishing canonical
residuals on every `(k+1)`-subset give strong farness (no codeword sweep needed). -/
theorem stronglyFar_of_canon_residuals (dom : Fin n ↪ F) {k : ℕ} (hk : 1 ≤ k)
    {u₁ : Fin n → F}
    (hres : ∀ T ∈ (Finset.univ : Finset (Fin n)).powersetCard (k + 1),
      ∀ h : T.card = k + 1, residual dom k (canonTuple T h) u₁ ≠ 0) :
    ∀ c ∈ (rsCode dom k : Submodule F (Fin n → F)),
      (agreeSet c u₁).card ≤ k := by
  intro c hcC
  by_contra hgt
  push_neg at hgt
  obtain ⟨T, hTsub, hTcard⟩ := Finset.exists_subset_card_eq hgt
  have hTmem : T ∈ (Finset.univ : Finset (Fin n)).powersetCard (k + 1) :=
    Finset.mem_powersetCard.mpr ⟨Finset.subset_univ _, hTcard⟩
  refine hres T hTmem hTcard ?_
  obtain ⟨P, hPdeg, rfl⟩ := hcC
  have hPdeg' : P.natDegree < k := by
    by_cases hP0 : P = 0
    · subst hP0
      simpa using hk
    · exact (Polynomial.natDegree_lt_iff_degree_lt hP0).mpr hPdeg
  refine residual_eq_zero_of_extends dom k _ hPdeg' fun a => ?_
  have hmem := hTsub (canonTuple_mem T hTcard a)
  rw [agreeSet, Finset.mem_filter] at hmem
  exact hmem.2.symm

open Classical in
/-- Variant of the criterion: nonvanishing residuals at ALL injective tuples give
strong farness — the form an instance file discharges by `decide`. -/
theorem stronglyFar_of_tuple_residuals (dom : Fin n ↪ F) {k : ℕ} (hk : 1 ≤ k)
    {u₁ : Fin n → F}
    (hres : ∀ t : Fin (k + 1) → Fin n, Function.Injective t →
      residual dom k t u₁ ≠ 0) :
    ∀ c ∈ (rsCode dom k : Submodule F (Fin n → F)),
      (agreeSet c u₁).card ≤ k :=
  stronglyFar_of_canon_residuals dom hk fun T _ h =>
    hres (canonTuple T h) (canonTuple_injective T h)

/-! ## The subset-ownership engine -/

open Classical in
/-- **The subset-ownership engine**: if every bad scalar owns at least `M`
`(k+1)`-subsets — subsets on whose every injective enumeration the direction
residual does not vanish and the line residual does — then `#bad · M ≤ C(n, k+1)`.
Ownership is exclusive: a shared subset forces equal scalars through its canonical
enumeration. -/
theorem badScalars_card_mul_le_ownership_choose (dom : Fin n ↪ F) (k : ℕ)
    (u₀ u₁ : Fin n → F) (bad : Finset F) (M : ℕ)
    (𝒮 : F → Finset (Finset (Fin n)))
    (hsz : ∀ γ ∈ bad, ∀ T ∈ 𝒮 γ, T.card = k + 1)
    (hprop : ∀ γ ∈ bad, ∀ T ∈ 𝒮 γ, ∀ t : Fin (k + 1) → Fin n,
      Function.Injective t → (∀ a, t a ∈ T) →
      residual dom k t u₁ ≠ 0 ∧
        residual dom k t u₀ + γ * residual dom k t u₁ = 0)
    (hM : ∀ γ ∈ bad, M ≤ (𝒮 γ).card) :
    bad.card * M ≤ n.choose (k + 1) := by
  have hdisj : ∀ γ ∈ bad, ∀ γ' ∈ bad, γ ≠ γ' → Disjoint (𝒮 γ) (𝒮 γ') := by
    intro γ hγ γ' hγ' hne
    rw [Finset.disjoint_left]
    intro T hT hT'
    have hTcard := hsz γ hγ T hT
    obtain ⟨h1, h0⟩ := hprop γ hγ T hT (canonTuple T hTcard)
      (canonTuple_injective T hTcard) (canonTuple_mem T hTcard)
    obtain ⟨h1', h0'⟩ := hprop γ' hγ' T hT' (canonTuple T hTcard)
      (canonTuple_injective T hTcard) (canonTuple_mem T hTcard)
    exact hne (by
      rw [gamma_eq_of_owned dom k (canonTuple T hTcard) h1 h0,
        gamma_eq_of_owned dom k (canonTuple T hTcard) h1' h0'])
  calc bad.card * M = ∑ _γ ∈ bad, M := by
        rw [Finset.sum_const, smul_eq_mul]
    _ ≤ ∑ γ ∈ bad, (𝒮 γ).card := Finset.sum_le_sum hM
    _ = (bad.biUnion 𝒮).card := (Finset.card_biUnion hdisj).symm
    _ ≤ ((Finset.univ : Finset (Fin n)).powersetCard (k + 1)).card := by
        refine Finset.card_le_card fun T hT => ?_
        obtain ⟨γ, hγ, hTγ⟩ := Finset.mem_biUnion.mp hT
        exact Finset.mem_powersetCard.mpr
          ⟨Finset.subset_univ _, hsz γ hγ T hTγ⟩
    _ = n.choose (k + 1) := by
        rw [Finset.card_powersetCard, Finset.card_univ, Fintype.card_fin]

/-! ## The strongly-far subset law -/

open Classical in
/-- **THE STRONGLY-FAR SUBSET LAW** — the unordered sharpening: at every radius
`δ ≤ w/n`, a strongly-far direction has `#bad · C(n−w, k+1) ≤ C(n, k+1)`.  Each
bad scalar exclusively owns every `(k+1)`-subset of its witness. -/
theorem stronglyFar_badScalars_card_mul_le_choose (dom : Fin n ↪ F)
    {k w : ℕ} (hk : 1 ≤ k)
    {δ : ℝ≥0} (hδn : δ * (Fintype.card (Fin n) : ℝ≥0) ≤ w)
    {u₀ u₁ : Fin n → F}
    (hμ : ∀ c ∈ (rsCode dom k : Submodule F (Fin n → F)),
      (agreeSet c u₁).card ≤ k) :
    (Finset.univ.filter (fun γ : F => mcaEvent (F := F)
        ((rsCode dom k : Submodule F (Fin n → F)) : Set (Fin n → F)) δ u₀ u₁ γ)).card
      * ((n - w).choose (k + 1)) ≤ n.choose (k + 1) := by
  set bad := Finset.univ.filter (fun γ : F => mcaEvent (F := F)
    ((rsCode dom k : Submodule F (Fin n → F)) : Set (Fin n → F)) δ u₀ u₁ γ) with hbad
  have hch : ∀ γ ∈ bad, ∃ S : Finset (Fin n),
      ((S.card : ℝ≥0) ≥ (1 - δ) * Fintype.card (Fin n)) ∧
      ∀ t : Fin (k + 1) → Fin n, (∀ a, t a ∈ S) →
        residual dom k t u₁ ≠ 0 →
        residual dom k t u₀ + γ * residual dom k t u₁ = 0 := by
    intro γ hγ
    exact mcaEvent_owned_tuples dom hk δ (Finset.mem_filter.mp hγ).2
  choose! W hWsz hWprop using hch
  have hSsz : ∀ γ ∈ bad, n - w ≤ (W γ).card := by
    intro γ hγ
    have h1 := hWsz γ hγ
    have h2 : ((n - w : ℕ) : ℝ≥0) ≤ ((W γ).card : ℝ≥0) := by
      have hcardn : (Fintype.card (Fin n) : ℝ≥0) = (n : ℝ≥0) := by
        rw [Fintype.card_fin]
      calc ((n - w : ℕ) : ℝ≥0) = (n : ℝ≥0) - (w : ℝ≥0) := by rw [Nat.cast_tsub]
        _ ≤ (n : ℝ≥0) - δ * (Fintype.card (Fin n) : ℝ≥0) :=
            tsub_le_tsub_left (by rw [hcardn] at hδn ⊢; exact hδn) _
        _ = (1 - δ) * (Fintype.card (Fin n) : ℝ≥0) := by
            rw [tsub_mul, one_mul, hcardn]
        _ ≤ ((W γ).card : ℝ≥0) := h1
    exact_mod_cast h2
  refine badScalars_card_mul_le_ownership_choose dom k u₀ u₁ bad _
    (fun γ => (W γ).powersetCard (k + 1)) ?_ ?_ ?_
  · intro γ hγ T hT
    exact (Finset.mem_powersetCard.mp hT).2
  · intro γ hγ T hT t htinj htmem
    have hTW := (Finset.mem_powersetCard.mp hT).1
    have h1 : residual dom k t u₁ ≠ 0 :=
      residual_ne_zero_of_stronglyFar dom hμ htinj
    exact ⟨h1, hWprop γ hγ t (fun a => hTW (htmem a)) h1⟩
  · intro γ hγ
    rw [Finset.card_powersetCard]
    exact Nat.choose_le_choose _ (hSsz γ hγ)

/-! ## The ratio set and the boundary identity -/

open Classical in
/-- **The ratio set** of a stack: the candidate scalars `−e_T(u₀)/e_T(u₁)`, one
from the canonical enumeration of each `(k+1)`-subset of the domain. -/
noncomputable def ratioSet (dom : Fin n ↪ F) (k : ℕ) (u₀ u₁ : Fin n → F) :
    Finset F :=
  ((Finset.univ : Finset (Fin n)).powersetCard (k + 1)).attach.image fun T =>
    -(residual dom k (canonTuple T.1 (Finset.mem_powersetCard.mp T.2).2) u₀)
      / residual dom k (canonTuple T.1 (Finset.mem_powersetCard.mp T.2).2) u₁

theorem ratioSet_card_le (dom : Fin n ↪ F) (k : ℕ) (u₀ u₁ : Fin n → F) :
    (ratioSet dom k u₀ u₁).card ≤ n.choose (k + 1) := by
  refine le_trans Finset.card_image_le ?_
  rw [Finset.card_attach, Finset.card_powersetCard, Finset.card_univ,
    Fintype.card_fin]

open Classical in
/-- Lagrange: through any `≤ k` points there is a codeword matching any word. -/
theorem exists_codeword_agreeOn_of_card_le (dom : Fin n ↪ F) {k : ℕ}
    {S : Finset (Fin n)} (hS : S.card ≤ k) (v : Fin n → F) :
    ∃ c ∈ (rsCode dom k : Submodule F (Fin n → F)), ∀ i ∈ S, c i = v i := by
  have hinj : Set.InjOn (fun j : Fin n => dom j) ↑S := dom.injective.injOn
  refine ⟨fun i => (Lagrange.interpolate S (fun j => dom j) v).eval (dom i),
    ⟨Lagrange.interpolate S (fun j => dom j) v, ?_, rfl⟩, fun i hi => ?_⟩
  · calc (Lagrange.interpolate S (fun j => dom j) v).degree
        < (S.card : WithBot ℕ) := Lagrange.degree_interpolate_lt v hinj
      _ ≤ (k : WithBot ℕ) := by exact_mod_cast hS
  · exact Lagrange.eval_interpolate_at_node v hinj hi

open Classical in
/-- **The forward inclusion — radius-free**: for a strongly-far direction, every
bad scalar is a subset ratio.  Any valid witness carries `≥ k+1` points (smaller
sets always admit a joint Lagrange pair, contradicting the event's last clause),
and any `(k+1)`-subset of it determines the scalar. -/
theorem stronglyFar_bad_subset_ratioSet (dom : Fin n ↪ F) {k : ℕ} (hk : 1 ≤ k)
    {δ : ℝ≥0} {u₀ u₁ : Fin n → F}
    (hμ : ∀ c ∈ (rsCode dom k : Submodule F (Fin n → F)),
      (agreeSet c u₁).card ≤ k) :
    (Finset.univ.filter (fun γ : F => mcaEvent (F := F)
        ((rsCode dom k : Submodule F (Fin n → F)) : Set (Fin n → F)) δ u₀ u₁ γ))
      ⊆ ratioSet dom k u₀ u₁ := by
  intro γ hγ
  obtain ⟨S, hSsz, ⟨wcd, hwC, hag⟩, hnj⟩ := (Finset.mem_filter.mp hγ).2
  have hSk : k + 1 ≤ S.card := by
    by_contra hlt
    push_neg at hlt
    have hSle : S.card ≤ k := by omega
    obtain ⟨v₀, hv₀C, hv₀⟩ := exists_codeword_agreeOn_of_card_le dom hSle u₀
    obtain ⟨v₁, hv₁C, hv₁⟩ := exists_codeword_agreeOn_of_card_le dom hSle u₁
    exact hnj ⟨v₀, hv₀C, v₁, hv₁C, fun i hi => ⟨hv₀ i hi, hv₁ i hi⟩⟩
  obtain ⟨T, hTS, hTcard⟩ := Finset.exists_subset_card_eq hSk
  have htinj : Function.Injective (canonTuple T hTcard) :=
    canonTuple_injective T hTcard
  obtain ⟨P, hPdeg, rfl⟩ := hwC
  have hPdeg' : P.natDegree < k := by
    by_cases hP0 : P = 0
    · subst hP0
      simpa using hk
    · exact (Polynomial.natDegree_lt_iff_degree_lt hP0).mpr hPdeg
  have hline0 : residual dom k (canonTuple T hTcard)
      (fun i => u₀ i + γ * u₁ i) = 0 := by
    refine residual_eq_zero_of_extends dom k _ hPdeg' fun a => ?_
    have hmem : canonTuple T hTcard a ∈ S := hTS (canonTuple_mem T hTcard a)
    have := hag (canonTuple T hTcard a) hmem
    simpa [smul_eq_mul] using this.symm
  rw [residual_line] at hline0
  have h1 : residual dom k (canonTuple T hTcard) u₁ ≠ 0 :=
    residual_ne_zero_of_stronglyFar dom hμ htinj
  rw [ratioSet, Finset.mem_image]
  exact ⟨⟨T, Finset.mem_powersetCard.mpr ⟨Finset.subset_univ _, hTcard⟩⟩,
    Finset.mem_attach _ _,
    (gamma_eq_of_owned dom k (canonTuple T hTcard) h1 hline0).symm⟩

open Classical in
/-- **The radius-free `C(n, k+1)` ceiling** for strongly-far directions — through
the window, to capacity.  Probe-tight at the boundary slice (far directions attain
`56 = C(8,3)` at `n = 8, k = 2, δ = 5/8`). -/
theorem stronglyFar_badScalars_card_le_choose (dom : Fin n ↪ F) {k : ℕ}
    (hk : 1 ≤ k) {δ : ℝ≥0} {u₀ u₁ : Fin n → F}
    (hμ : ∀ c ∈ (rsCode dom k : Submodule F (Fin n → F)),
      (agreeSet c u₁).card ≤ k) :
    (Finset.univ.filter (fun γ : F => mcaEvent (F := F)
        ((rsCode dom k : Submodule F (Fin n → F)) : Set (Fin n → F)) δ u₀ u₁ γ)).card
      ≤ n.choose (k + 1) :=
  le_trans (Finset.card_le_card (stronglyFar_bad_subset_ratioSet dom hk hμ))
    (ratioSet_card_le dom k u₀ u₁)

open Classical in
/-- **The reverse direction at the boundary**: every subset ratio of a strongly-far
direction IS bad at any radius admitting `(k+1)`-point witnesses.  The witness is
the tuple's image; the joint clause fails because a pair member would have to agree
with `u₁` on `k+1` points. -/
theorem ratio_bad_of_boundary (dom : Fin n ↪ F) {k : ℕ}
    {δ : ℝ≥0} (hbdy : (1 - δ) * (Fintype.card (Fin n) : ℝ≥0) ≤ (k + 1 : ℕ))
    {u₀ u₁ : Fin n → F}
    (hμ : ∀ c ∈ (rsCode dom k : Submodule F (Fin n → F)),
      (agreeSet c u₁).card ≤ k)
    {t : Fin (k + 1) → Fin n} (htinj : Function.Injective t) :
    mcaEvent (F := F)
      ((rsCode dom k : Submodule F (Fin n → F)) : Set (Fin n → F)) δ u₀ u₁
      (-(residual dom k t u₀) / residual dom k t u₁) := by
  have h1 : residual dom k t u₁ ≠ 0 :=
    residual_ne_zero_of_stronglyFar dom hμ htinj
  set γ : F := -(residual dom k t u₀) / residual dom k t u₁ with hγdef
  have h0 : residual dom k t u₀ + γ * residual dom k t u₁ = 0 := by
    rw [hγdef, div_mul_cancel₀ _ h1, add_neg_cancel]
  refine ⟨Finset.univ.image t, ?_, ?_, ?_⟩
  · rw [Finset.card_image_of_injective _ htinj, Finset.card_univ,
      Fintype.card_fin]
    exact hbdy
  · have hres0 : residual dom k t (fun i => u₀ i + γ * u₁ i) = 0 := by
      rw [residual_line]
      exact h0
    obtain ⟨c, hcC, hcag⟩ := extension_of_residual_eq_zero dom t htinj hres0
    refine ⟨c, hcC, fun i hi => ?_⟩
    obtain ⟨a, -, rfl⟩ := Finset.mem_image.mp hi
    have := hcag a
    simpa [smul_eq_mul] using this
  · rintro ⟨v₀, hv₀C, v₁, hv₁C, hjoint⟩
    have hsub : Finset.univ.image t ⊆ agreeSet v₁ u₁ := by
      intro x hx
      obtain ⟨a, -, rfl⟩ := Finset.mem_image.mp hx
      rw [agreeSet, Finset.mem_filter]
      exact ⟨Finset.mem_univ _,
        (hjoint (t a) (Finset.mem_image_of_mem t (Finset.mem_univ a))).2⟩
    have hcard : k + 1 ≤ (agreeSet v₁ u₁).card := by
      calc k + 1 = (Finset.univ.image t).card := by
            rw [Finset.card_image_of_injective _ htinj, Finset.card_univ,
              Fintype.card_fin]
        _ ≤ _ := Finset.card_le_card hsub
    have := hμ v₁ hv₁C
    omega

open Classical in
/-- **THE RATIO-SET IDENTITY at the boundary slice**: for strongly-far directions,
at any radius admitting `(k+1)`-point witnesses, the bad set IS the ratio set.
The far-class exact threshold value is the number of distinct subset ratios. -/
theorem stronglyFar_badSet_eq_ratioSet (dom : Fin n ↪ F) {k : ℕ} (hk : 1 ≤ k)
    {δ : ℝ≥0} (hbdy : (1 - δ) * (Fintype.card (Fin n) : ℝ≥0) ≤ (k + 1 : ℕ))
    {u₀ u₁ : Fin n → F}
    (hμ : ∀ c ∈ (rsCode dom k : Submodule F (Fin n → F)),
      (agreeSet c u₁).card ≤ k) :
    (Finset.univ.filter (fun γ : F => mcaEvent (F := F)
        ((rsCode dom k : Submodule F (Fin n → F)) : Set (Fin n → F)) δ u₀ u₁ γ))
      = ratioSet dom k u₀ u₁ := by
  refine Finset.Subset.antisymm (stronglyFar_bad_subset_ratioSet dom hk hμ) ?_
  intro γ hγ
  rw [ratioSet, Finset.mem_image] at hγ
  obtain ⟨T, -, rfl⟩ := hγ
  exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,
    ratio_bad_of_boundary dom hbdy hμ
      (canonTuple_injective T.1 (Finset.mem_powersetCard.mp T.2).2)⟩

open Classical in
/-- **The far-class mass**: a strongly-far direction's per-direction bad mass is
`≤ C(n, k+1)/q` at EVERY radius. -/
theorem stronglyFar_prob_le (dom : Fin n ↪ F) {k : ℕ} (hk : 1 ≤ k)
    {δ : ℝ≥0} {u₀ u₁ : Fin n → F}
    (hμ : ∀ c ∈ (rsCode dom k : Submodule F (Fin n → F)),
      (agreeSet c u₁).card ≤ k) :
    (Pr_{let γ ← $ᵖ F}[mcaEvent (F := F)
        ((rsCode dom k : Submodule F (Fin n → F)) : Set (Fin n → F)) δ u₀ u₁ γ])
      ≤ (n.choose (k + 1) : ℝ≥0∞) / (Fintype.card F : ℝ≥0∞) := by
  rw [prob_uniform_eq_card_filter_div_card]
  refine ENNReal.div_le_div_right ?_ _
  exact_mod_cast stronglyFar_badScalars_card_le_choose dom hk hμ

end ProximityGap.Ownership

-- Axiom audit (expected: propext, Classical.choice, Quot.sound only)
#print axioms ProximityGap.Ownership.badScalars_card_mul_le_ownership_choose
#print axioms ProximityGap.Ownership.stronglyFar_badScalars_card_mul_le_choose
#print axioms ProximityGap.Ownership.stronglyFar_bad_subset_ratioSet
#print axioms ProximityGap.Ownership.stronglyFar_badScalars_card_le_choose
#print axioms ProximityGap.Ownership.ratio_bad_of_boundary
#print axioms ProximityGap.Ownership.stronglyFar_badSet_eq_ratioSet
#print axioms ProximityGap.Ownership.stronglyFar_prob_le
#print axioms ProximityGap.Ownership.stronglyFar_of_canon_residuals
#print axioms ProximityGap.Ownership.stronglyFar_of_tuple_residuals

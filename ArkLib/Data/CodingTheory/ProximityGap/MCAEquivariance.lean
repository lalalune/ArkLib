/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.MCADeltaStarExactPoint

/-!
# S3 (#357): the MCA equivariance engine — the symmetry group of `ε_mca`

Four independently-discovered phenomena across the δ* campaign — the probes' syndrome
reduction (codeword translation), the M3 affine/coset invariance, the KKH26 rotation orbits,
and the γ-shift used in the exact ladder — are the statement that `mcaEvent` is equivariant
under one group acting on word stacks:

  `G = (code-preserving coordinate permutations) ⋉ (C² ⋊ (scalar scaling × shear))`,

with the scaling/shear components acting on the *line parameter* `γ` by an affine bijection of
`F`. This file proves the four equivariance laws, pushes each to the probability level
(uniform-`γ` reindexing), and derives the **orbit-section theorem**: `ε_mca` is a supremum
over any system of orbit representatives. Consequences:

* every orbit-reduced exact `ε_mca` computation (the probe lab's engine, the n = 8/12 rungs)
  is retroactively certified by a formal reduction;
* the R1 exact-point methodology (`MCADeltaStarExactPoint`) scales: `decide`-feasibility of
  the next rungs needs only one stack per orbit;
* any flat-numerator/orbit-count law (the `(12,6)` plateau) is now *stateable* in Lean.

The laws, for `C` a submodule code:

1. **Translation** (`mcaEvent_translate_iff`): for codewords `c₀, c₁ ∈ C`,
   `mcaEvent C δ (u₀+c₀) (u₁+c₁) γ ↔ mcaEvent C δ u₀ u₁ γ` — same `γ`.
2. **Permutation** (`mcaEvent_perm_iff`): for `π` a coordinate permutation with
   `w ∈ C ↔ w∘π ∈ C`, `mcaEvent C δ (u₀∘π) (u₁∘π) γ ↔ mcaEvent C δ u₀ u₁ γ` — same `γ`,
   witness sets transported by `π` (cardinality preserved).
3. **Scaling** (`mcaEvent_smul_right_iff`): for `a ≠ 0`,
   `mcaEvent C δ u₀ (a•u₁) γ ↔ mcaEvent C δ u₀ u₁ (γ·a)` — `γ` reparametrized.
4. **Shear** (`mcaEvent_shear_iff`):
   `mcaEvent C δ (u₀+b•u₁) u₁ γ ↔ mcaEvent C δ u₀ u₁ (γ+b)` — `γ` shifted.

Probability level: 1–2 are pointwise-in-`γ`, so `Pr` is equal on the nose; 3–4 compose with
the uniform-measure reindexing `prob_uniform_comp_equiv` (any bijection of `F` preserves the
uniform `γ`-mass). The orbit-section theorem `epsMCA_eq_iSup_rep` then states: for any
representative map `rep` with per-stack `Pr`-invariance, `ε_mca = ⨆ u, Pr[mcaEvent (rep u)]`.

Non-vacuity: the R1 code `RS[F₅, ⟨2⟩, 2]` is closed under the domain rotation `x ↦ 2x`
(`rsC_rot_closed`), giving a genuine nontrivial instance of law 2 on a smooth domain
(`prob_mcaEvent_rsC_rot_eq`).

All results are `sorry`-free and axiom-clean (`[propext, Classical.choice, Quot.sound]`).

## References
- Issue #357 (the δ* campaign; hypothesis S3); [ABF26] ePrint 2026/680.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

open scoped NNReal ENNReal ProbabilityTheory
open ProximityGap Code

namespace ProximityGap.MCAEquivariance

variable {ι : Type} [Fintype ι] [Nonempty ι] [DecidableEq ι]
variable {F : Type} [Field F] [Fintype F] [DecidableEq F]
variable {A : Type} [Fintype A] [DecidableEq A] [AddCommGroup A] [Module F A]

/-! ## Law 1 — translation by a pair of codewords -/

/-- Joint explanations transport along translation by codewords (one direction). -/
theorem pairJointAgreesOn_translate_of (C : Submodule F (ι → A)) {c₀ c₁ : ι → A}
    (hc₀ : c₀ ∈ C) (hc₁ : c₁ ∈ C) {S : Finset ι} {u₀ u₁ : ι → A}
    (h : pairJointAgreesOn (C : Set (ι → A)) S u₀ u₁) :
    pairJointAgreesOn (C : Set (ι → A)) S (u₀ + c₀) (u₁ + c₁) := by
  obtain ⟨v₀, hv₀, v₁, hv₁, hag⟩ := h
  refine ⟨v₀ + c₀, C.add_mem hv₀ hc₀, v₁ + c₁, C.add_mem hv₁ hc₁, fun i hi => ?_⟩
  refine ⟨?_, ?_⟩
  · show v₀ i + c₀ i = u₀ i + c₀ i
    rw [(hag i hi).1]
  · show v₁ i + c₁ i = u₁ i + c₁ i
    rw [(hag i hi).2]

/-- Joint explanations are invariant under translation by codewords. -/
theorem pairJointAgreesOn_translate_iff (C : Submodule F (ι → A)) {c₀ c₁ : ι → A}
    (hc₀ : c₀ ∈ C) (hc₁ : c₁ ∈ C) (S : Finset ι) (u₀ u₁ : ι → A) :
    pairJointAgreesOn (C : Set (ι → A)) S (u₀ + c₀) (u₁ + c₁) ↔
      pairJointAgreesOn (C : Set (ι → A)) S u₀ u₁ := by
  constructor
  · intro h
    have h' := pairJointAgreesOn_translate_of C (C.neg_mem hc₀) (C.neg_mem hc₁) h
    rwa [add_neg_cancel_right, add_neg_cancel_right] at h'
  · exact pairJointAgreesOn_translate_of C hc₀ hc₁

/-- One direction of the translation law for the MCA bad event. -/
theorem mcaEvent_translate_of (C : Submodule F (ι → A)) {c₀ c₁ : ι → A}
    (hc₀ : c₀ ∈ C) (hc₁ : c₁ ∈ C) (δ : ℝ≥0) (u₀ u₁ : ι → A) (γ : F)
    (h : mcaEvent (F := F) (C : Set (ι → A)) δ u₀ u₁ γ) :
    mcaEvent (F := F) (C : Set (ι → A)) δ (u₀ + c₀) (u₁ + c₁) γ := by
  obtain ⟨S, hS, ⟨w, hw, hweq⟩, hno⟩ := h
  refine ⟨S, hS, ⟨w + (c₀ + γ • c₁), C.add_mem hw (C.add_mem hc₀ (C.smul_mem γ hc₁)),
    fun i hi => ?_⟩, ?_⟩
  · show w i + (c₀ i + γ • c₁ i) = (u₀ i + c₀ i) + γ • (u₁ i + c₁ i)
    rw [hweq i hi, smul_add]
    abel
  · intro hp
    exact hno ((pairJointAgreesOn_translate_iff C hc₀ hc₁ S u₀ u₁).mp hp)

/-- **Law 1 (translation).** `mcaEvent` is invariant under translating the stack by a pair of
codewords, at the same `γ`. -/
theorem mcaEvent_translate_iff (C : Submodule F (ι → A)) {c₀ c₁ : ι → A}
    (hc₀ : c₀ ∈ C) (hc₁ : c₁ ∈ C) (δ : ℝ≥0) (u₀ u₁ : ι → A) (γ : F) :
    mcaEvent (F := F) (C : Set (ι → A)) δ (u₀ + c₀) (u₁ + c₁) γ ↔
      mcaEvent (F := F) (C : Set (ι → A)) δ u₀ u₁ γ := by
  constructor
  · intro h
    have h' := mcaEvent_translate_of C (C.neg_mem hc₀) (C.neg_mem hc₁) δ _ _ γ h
    rwa [add_neg_cancel_right, add_neg_cancel_right] at h'
  · exact mcaEvent_translate_of C hc₀ hc₁ δ u₀ u₁ γ

/-! ## Law 2 — code-preserving coordinate permutations -/

/-- A code-closure hypothesis for `π` transfers to `π⁻¹`. -/
theorem code_perm_closed_symm {C : Set (ι → A)} {π : Equiv.Perm ι}
    (hC : ∀ w : ι → A, w ∈ C ↔ w ∘ π ∈ C) (w : ι → A) :
    w ∈ C ↔ w ∘ π.symm ∈ C := by
  constructor
  · intro hw
    have h := (hC (w ∘ π.symm)).mpr
    apply h
    have : (w ∘ π.symm) ∘ π = w := by
      funext i
      simp [Function.comp, Equiv.symm_apply_apply]
    rwa [this]
  · intro hw
    have h := (hC (w ∘ π.symm)).mp hw
    have : (w ∘ π.symm) ∘ π = w := by
      funext i
      simp [Function.comp, Equiv.symm_apply_apply]
    rwa [this] at h

/-- One direction of the permutation law: an event for the `π`-pulled-back stack transports to
the original stack, with the witness set pushed forward along `π`. -/
theorem mcaEvent_perm_of (C : Set (ι → A)) (π : Equiv.Perm ι)
    (hC : ∀ w : ι → A, w ∈ C ↔ w ∘ π ∈ C) (δ : ℝ≥0) (u₀ u₁ : ι → A) (γ : F)
    (h : mcaEvent (F := F) C δ (u₀ ∘ π) (u₁ ∘ π) γ) :
    mcaEvent (F := F) C δ u₀ u₁ γ := by
  obtain ⟨S, hS, ⟨w, hw, hweq⟩, hno⟩ := h
  refine ⟨S.image π, ?_, ⟨w ∘ π.symm, (code_perm_closed_symm hC w).mp hw, ?_⟩, ?_⟩
  · rwa [Finset.card_image_of_injective S π.injective]
  · intro j hj
    obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hj
    show w (π.symm (π i)) = u₀ (π i) + γ • u₁ (π i)
    rw [Equiv.symm_apply_apply]
    exact hweq i hi
  · rintro ⟨v₀, hv₀, v₁, hv₁, hag⟩
    refine hno ⟨v₀ ∘ π, (hC v₀).mp hv₀, v₁ ∘ π, (hC v₁).mp hv₁, fun i hi => ?_⟩
    exact hag (π i) (Finset.mem_image_of_mem π hi)

/-- **Law 2 (permutation).** For a coordinate permutation `π` preserving the code,
`mcaEvent` for the pulled-back stack `(u₀∘π, u₁∘π)` is equivalent to the event for
`(u₀, u₁)`, at the same `γ`. -/
theorem mcaEvent_perm_iff (C : Set (ι → A)) (π : Equiv.Perm ι)
    (hC : ∀ w : ι → A, w ∈ C ↔ w ∘ π ∈ C) (δ : ℝ≥0) (u₀ u₁ : ι → A) (γ : F) :
    mcaEvent (F := F) C δ (u₀ ∘ π) (u₁ ∘ π) γ ↔ mcaEvent (F := F) C δ u₀ u₁ γ := by
  constructor
  · exact mcaEvent_perm_of C π hC δ u₀ u₁ γ
  · intro h
    refine mcaEvent_perm_of C π.symm (code_perm_closed_symm hC) δ (u₀ ∘ π) (u₁ ∘ π) γ ?_
    have h₀ : (u₀ ∘ π) ∘ π.symm = u₀ := by
      funext i; simp [Function.comp, Equiv.apply_symm_apply]
    have h₁ : (u₁ ∘ π) ∘ π.symm = u₁ := by
      funext i; simp [Function.comp, Equiv.apply_symm_apply]
    rwa [h₀, h₁]

/-! ## Law 3 — scaling the second row reparametrizes `γ` multiplicatively -/

/-- Joint explanations are invariant under scaling the second row by a unit. -/
theorem pairJointAgreesOn_smul_right_iff (C : Submodule F (ι → A)) {a : F} (ha : a ≠ 0)
    (S : Finset ι) (u₀ u₁ : ι → A) :
    pairJointAgreesOn (C : Set (ι → A)) S u₀ (a • u₁) ↔
      pairJointAgreesOn (C : Set (ι → A)) S u₀ u₁ := by
  constructor
  · rintro ⟨v₀, hv₀, v₁, hv₁, hag⟩
    refine ⟨v₀, hv₀, a⁻¹ • v₁, C.smul_mem a⁻¹ hv₁, fun i hi => ⟨(hag i hi).1, ?_⟩⟩
    show a⁻¹ • v₁ i = u₁ i
    rw [(hag i hi).2]
    show a⁻¹ • a • u₁ i = u₁ i
    rw [inv_smul_smul₀ ha]
  · rintro ⟨v₀, hv₀, v₁, hv₁, hag⟩
    refine ⟨v₀, hv₀, a • v₁, C.smul_mem a hv₁, fun i hi => ⟨(hag i hi).1, ?_⟩⟩
    show a • v₁ i = a • u₁ i
    rw [(hag i hi).2]

/-- **Law 3 (scaling).** Scaling the second row by `a ≠ 0` reparametrizes the line:
`mcaEvent C δ u₀ (a•u₁) γ ↔ mcaEvent C δ u₀ u₁ (γ·a)`. -/
theorem mcaEvent_smul_right_iff (C : Submodule F (ι → A)) {a : F} (ha : a ≠ 0)
    (δ : ℝ≥0) (u₀ u₁ : ι → A) (γ : F) :
    mcaEvent (F := F) (C : Set (ι → A)) δ u₀ (a • u₁) γ ↔
      mcaEvent (F := F) (C : Set (ι → A)) δ u₀ u₁ (γ * a) := by
  have hline : ∀ i, u₀ i + γ • (a • u₁) i = u₀ i + (γ * a) • u₁ i := fun i => by
    show u₀ i + γ • a • u₁ i = u₀ i + (γ * a) • u₁ i
    rw [smul_smul]
  constructor
  · rintro ⟨S, hS, ⟨w, hw, hweq⟩, hno⟩
    refine ⟨S, hS, ⟨w, hw, fun i hi => by rw [hweq i hi]; exact hline i⟩, ?_⟩
    intro hp
    exact hno ((pairJointAgreesOn_smul_right_iff C ha S u₀ u₁).mpr hp)
  · rintro ⟨S, hS, ⟨w, hw, hweq⟩, hno⟩
    refine ⟨S, hS, ⟨w, hw, fun i hi => by rw [hweq i hi]; exact (hline i).symm⟩, ?_⟩
    intro hp
    exact hno ((pairJointAgreesOn_smul_right_iff C ha S u₀ u₁).mp hp)

/-! ## Law 4 — shearing the first row shifts `γ` additively -/

/-- Joint explanations are invariant under shearing the first row by a multiple of the
second. -/
theorem pairJointAgreesOn_shear_iff (C : Submodule F (ι → A)) (b : F)
    (S : Finset ι) (u₀ u₁ : ι → A) :
    pairJointAgreesOn (C : Set (ι → A)) S (u₀ + b • u₁) u₁ ↔
      pairJointAgreesOn (C : Set (ι → A)) S u₀ u₁ := by
  constructor
  · rintro ⟨v₀, hv₀, v₁, hv₁, hag⟩
    refine ⟨v₀ - b • v₁, C.sub_mem hv₀ (C.smul_mem b hv₁), v₁, hv₁,
      fun i hi => ⟨?_, (hag i hi).2⟩⟩
    show v₀ i - b • v₁ i = u₀ i
    rw [(hag i hi).1, (hag i hi).2]
    show (u₀ i + b • u₁ i) - b • u₁ i = u₀ i
    exact add_sub_cancel_right _ _
  · rintro ⟨v₀, hv₀, v₁, hv₁, hag⟩
    refine ⟨v₀ + b • v₁, C.add_mem hv₀ (C.smul_mem b hv₁), v₁, hv₁,
      fun i hi => ⟨?_, (hag i hi).2⟩⟩
    show v₀ i + b • v₁ i = u₀ i + b • u₁ i
    rw [(hag i hi).1, (hag i hi).2]

/-- **Law 4 (shear).** Shearing the first row by `b•u₁` shifts the line parameter:
`mcaEvent C δ (u₀ + b•u₁) u₁ γ ↔ mcaEvent C δ u₀ u₁ (γ + b)`. -/
theorem mcaEvent_shear_iff (C : Submodule F (ι → A)) (b : F)
    (δ : ℝ≥0) (u₀ u₁ : ι → A) (γ : F) :
    mcaEvent (F := F) (C : Set (ι → A)) δ (u₀ + b • u₁) u₁ γ ↔
      mcaEvent (F := F) (C : Set (ι → A)) δ u₀ u₁ (γ + b) := by
  have hline : ∀ i, (u₀ i + b • u₁ i) + γ • u₁ i = u₀ i + (γ + b) • u₁ i := fun i => by
    rw [add_smul]
    abel
  constructor
  · rintro ⟨S, hS, ⟨w, hw, hweq⟩, hno⟩
    refine ⟨S, hS, ⟨w, hw, fun i hi => by rw [hweq i hi]; exact hline i⟩, ?_⟩
    intro hp
    exact hno ((pairJointAgreesOn_shear_iff C b S u₀ u₁).mpr hp)
  · rintro ⟨S, hS, ⟨w, hw, hweq⟩, hno⟩
    refine ⟨S, hS, ⟨w, hw, fun i hi => by rw [hweq i hi]; exact (hline i).symm⟩, ?_⟩
    intro hp
    exact hno ((pairJointAgreesOn_shear_iff C b S u₀ u₁).mp hp)

/-! ## The probability level -/

open Classical in
/-- **Uniform reindexing:** precomposing the event with any bijection of `F` preserves the
uniform-`γ` probability. The measure-side engine for laws 3–4. -/
theorem prob_uniform_comp_equiv (P : F → Prop) (e : F ≃ F) :
    Pr_{let γ ← $ᵖ F}[P (e γ)] = Pr_{let γ ← $ᵖ F}[P γ] := by
  rw [prob_uniform_eq_card_filter_div_card, prob_uniform_eq_card_filter_div_card]
  have hcard : (Finset.filter (fun γ : F => P (e γ)) Finset.univ).card
      = (Finset.filter (fun γ : F => P γ) Finset.univ).card := by
    refine Finset.card_nbij' (i := fun γ => e γ) (j := fun γ => e.symm γ) ?_ ?_ ?_ ?_
    · intro γ hγ
      simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_univ, true_and] at hγ ⊢
      exact hγ
    · intro γ hγ
      simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_univ, true_and] at hγ ⊢
      simpa [Equiv.apply_symm_apply] using hγ
    · intro γ _
      exact e.symm_apply_apply γ
    · intro γ _
      exact e.apply_symm_apply γ
  rw [hcard]

open Classical in
/-- Translation invariance at the probability level. -/
theorem prob_mcaEvent_translate_eq (C : Submodule F (ι → A)) {c₀ c₁ : ι → A}
    (hc₀ : c₀ ∈ C) (hc₁ : c₁ ∈ C) (δ : ℝ≥0) (u₀ u₁ : ι → A) :
    Pr_{let γ ← $ᵖ F}[mcaEvent (F := F) (C : Set (ι → A)) δ (u₀ + c₀) (u₁ + c₁) γ]
      = Pr_{let γ ← $ᵖ F}[mcaEvent (F := F) (C : Set (ι → A)) δ u₀ u₁ γ] := by
  have hfilter : Finset.filter (fun γ : F =>
        mcaEvent (F := F) (C : Set (ι → A)) δ (u₀ + c₀) (u₁ + c₁) γ) Finset.univ
      = Finset.filter (fun γ : F =>
        mcaEvent (F := F) (C : Set (ι → A)) δ u₀ u₁ γ) Finset.univ :=
    Finset.filter_congr fun γ _ => mcaEvent_translate_iff C hc₀ hc₁ δ u₀ u₁ γ
  rw [prob_uniform_eq_card_filter_div_card, prob_uniform_eq_card_filter_div_card, hfilter]

open Classical in
/-- Permutation invariance at the probability level. -/
theorem prob_mcaEvent_perm_eq (C : Set (ι → A)) (π : Equiv.Perm ι)
    (hC : ∀ w : ι → A, w ∈ C ↔ w ∘ π ∈ C) (δ : ℝ≥0) (u₀ u₁ : ι → A) :
    Pr_{let γ ← $ᵖ F}[mcaEvent (F := F) C δ (u₀ ∘ π) (u₁ ∘ π) γ]
      = Pr_{let γ ← $ᵖ F}[mcaEvent (F := F) C δ u₀ u₁ γ] := by
  have hfilter : Finset.filter (fun γ : F =>
        mcaEvent (F := F) C δ (u₀ ∘ π) (u₁ ∘ π) γ) Finset.univ
      = Finset.filter (fun γ : F => mcaEvent (F := F) C δ u₀ u₁ γ) Finset.univ :=
    Finset.filter_congr fun γ _ => mcaEvent_perm_iff C π hC δ u₀ u₁ γ
  rw [prob_uniform_eq_card_filter_div_card, prob_uniform_eq_card_filter_div_card, hfilter]

open Classical in
/-- Scaling invariance at the probability level: the `γ ↦ γ·a` reparametrization is a
bijection of `F`, so the uniform mass is preserved. -/
theorem prob_mcaEvent_smul_right_eq (C : Submodule F (ι → A)) {a : F} (ha : a ≠ 0)
    (δ : ℝ≥0) (u₀ u₁ : ι → A) :
    Pr_{let γ ← $ᵖ F}[mcaEvent (F := F) (C : Set (ι → A)) δ u₀ (a • u₁) γ]
      = Pr_{let γ ← $ᵖ F}[mcaEvent (F := F) (C : Set (ι → A)) δ u₀ u₁ γ] := by
  have hstep : Pr_{let γ ← $ᵖ F}[mcaEvent (F := F) (C : Set (ι → A)) δ u₀ (a • u₁) γ]
      = Pr_{let γ ← $ᵖ F}[mcaEvent (F := F) (C : Set (ι → A)) δ u₀ u₁ (γ * a)] := by
    have hfilter : Finset.filter (fun γ : F =>
          mcaEvent (F := F) (C : Set (ι → A)) δ u₀ (a • u₁) γ) Finset.univ
        = Finset.filter (fun γ : F =>
          mcaEvent (F := F) (C : Set (ι → A)) δ u₀ u₁ (γ * a)) Finset.univ :=
      Finset.filter_congr fun γ _ => mcaEvent_smul_right_iff C ha δ u₀ u₁ γ
    rw [prob_uniform_eq_card_filter_div_card, prob_uniform_eq_card_filter_div_card, hfilter]
  rw [hstep]
  exact prob_uniform_comp_equiv
    (fun γ => mcaEvent (F := F) (C : Set (ι → A)) δ u₀ u₁ γ)
    (Equiv.mulRight₀ a ha)

open Classical in
/-- Shear invariance at the probability level: the `γ ↦ γ + b` shift is a bijection of `F`. -/
theorem prob_mcaEvent_shear_eq (C : Submodule F (ι → A)) (b : F)
    (δ : ℝ≥0) (u₀ u₁ : ι → A) :
    Pr_{let γ ← $ᵖ F}[mcaEvent (F := F) (C : Set (ι → A)) δ (u₀ + b • u₁) u₁ γ]
      = Pr_{let γ ← $ᵖ F}[mcaEvent (F := F) (C : Set (ι → A)) δ u₀ u₁ γ] := by
  have hstep : Pr_{let γ ← $ᵖ F}[mcaEvent (F := F) (C : Set (ι → A)) δ (u₀ + b • u₁) u₁ γ]
      = Pr_{let γ ← $ᵖ F}[mcaEvent (F := F) (C : Set (ι → A)) δ u₀ u₁ (γ + b)] := by
    have hfilter : Finset.filter (fun γ : F =>
          mcaEvent (F := F) (C : Set (ι → A)) δ (u₀ + b • u₁) u₁ γ) Finset.univ
        = Finset.filter (fun γ : F =>
          mcaEvent (F := F) (C : Set (ι → A)) δ u₀ u₁ (γ + b)) Finset.univ :=
      Finset.filter_congr fun γ _ => mcaEvent_shear_iff C b δ u₀ u₁ γ
    rw [prob_uniform_eq_card_filter_div_card, prob_uniform_eq_card_filter_div_card, hfilter]
  rw [hstep]
  exact prob_uniform_comp_equiv
    (fun γ => mcaEvent (F := F) (C : Set (ι → A)) δ u₀ u₁ γ)
    (Equiv.addRight b)

/-! ## The orbit-section theorem -/

open Classical in
/-- **The orbit-section theorem.** If a representative map `rep` preserves the per-stack
bad-scalar probability (e.g. it normalizes each stack inside its orbit under any composition
of laws 1–4), then `ε_mca` is the supremum over representatives only. This is the formal
licence for orbit-reduced exact `ε_mca` computation: a `decide`/enumeration over `range rep`
suffices. -/
theorem epsMCA_eq_iSup_rep (C : Set (ι → A)) (δ : ℝ≥0)
    (rep : WordStack A (Fin 2) ι → WordStack A (Fin 2) ι)
    (hrep : ∀ u : WordStack A (Fin 2) ι,
      Pr_{let γ ← $ᵖ F}[mcaEvent (F := F) C δ (rep u 0) (rep u 1) γ]
        = Pr_{let γ ← $ᵖ F}[mcaEvent (F := F) C δ (u 0) (u 1) γ]) :
    epsMCA (F := F) (A := A) C δ
      = ⨆ u : WordStack A (Fin 2) ι,
          Pr_{let γ ← $ᵖ F}[mcaEvent (F := F) C δ (rep u 0) (rep u 1) γ] := by
  unfold epsMCA
  refine le_antisymm (iSup_le fun u => ?_) (iSup_le fun u => ?_)
  · rw [← hrep u]
    exact le_iSup (fun v : WordStack A (Fin 2) ι =>
      Pr_{let γ ← $ᵖ F}[mcaEvent (F := F) C δ (rep v 0) (rep v 1) γ]) u
  · rw [hrep u]
    exact le_iSup (fun v : WordStack A (Fin 2) ι =>
      Pr_{let γ ← $ᵖ F}[mcaEvent (F := F) C δ (v 0) (v 1) γ]) u

/-! ## Non-vacuity: the R1 code is rotation-closed -/

section Concrete

open ProximityGap.MCADeltaStarExactPoint

/-- The domain rotation `x ↦ 2x` of `⟨2⟩ ⊂ F₅` is the cyclic coordinate shift:
`gdom (finRotate 4 i) = 2 * gdom i`. -/
theorem gdom_rot : ∀ i : Fin 4, gdom (finRotate 4 i) = 2 * gdom i := by decide

/-- The inverse rotation multiplies by `2⁻¹ = 3`. -/
theorem gdom_rot_symm : ∀ i : Fin 4, gdom ((finRotate 4).symm i) = 3 * gdom i := by decide

/-- **The R1 code is closed under the smooth-domain rotation** `x ↦ 2x` (as the cyclic
coordinate permutation `finRotate 4`): a genuine nontrivial instance of Law 2. -/
theorem rsC_rot_closed :
    ∀ w : Fin 4 → F5, w ∈ (rsC : Set (Fin 4 → F5)) ↔ w ∘ (finRotate 4) ∈
      (rsC : Set (Fin 4 → F5)) := by
  intro w
  constructor
  · rintro ⟨a, b, h⟩
    refine ⟨a, b * 2, fun i => ?_⟩
    show w (finRotate 4 i) = a + b * 2 * gdom i
    rw [h (finRotate 4 i), gdom_rot i]
    ring
  · rintro ⟨a, b, h⟩
    refine ⟨a, b * 3, fun i => ?_⟩
    have h' := h ((finRotate 4).symm i)
    show w i = a + b * 3 * gdom i
    have hi : w (finRotate 4 ((finRotate 4).symm i)) = w i := by
      rw [Equiv.apply_symm_apply]
    rw [← hi]
    have := h ((finRotate 4).symm i)
    show w (finRotate 4 ((finRotate 4).symm i)) = a + b * 3 * gdom i
    rw [Equiv.apply_symm_apply]
    calc w i = w ((finRotate 4) ((finRotate 4).symm i)) := by rw [Equiv.apply_symm_apply]
      _ = a + b * gdom ((finRotate 4).symm i) := h'
      _ = a + b * (3 * gdom i) := by rw [gdom_rot_symm i]
      _ = a + b * 3 * gdom i := by ring

open Classical in
/-- The per-stack bad-scalar probability of the R1 code is rotation-invariant — the engine's
non-vacuous instantiation on a smooth domain. -/
theorem prob_mcaEvent_rsC_rot_eq (δ : ℝ≥0) (u₀ u₁ : Fin 4 → F5) :
    Pr_{let γ ← $ᵖ F5}[mcaEvent (F := F5) (rsC : Set (Fin 4 → F5)) δ
        (u₀ ∘ (finRotate 4)) (u₁ ∘ (finRotate 4)) γ]
      = Pr_{let γ ← $ᵖ F5}[mcaEvent (F := F5) (rsC : Set (Fin 4 → F5)) δ u₀ u₁ γ] :=
  prob_mcaEvent_perm_eq (rsC : Set (Fin 4 → F5)) (finRotate 4) rsC_rot_closed δ u₀ u₁

end Concrete

/-! ## Source audit -/

#print axioms mcaEvent_translate_iff
#print axioms mcaEvent_perm_iff
#print axioms mcaEvent_smul_right_iff
#print axioms mcaEvent_shear_iff
#print axioms prob_uniform_comp_equiv
#print axioms prob_mcaEvent_translate_eq
#print axioms prob_mcaEvent_perm_eq
#print axioms prob_mcaEvent_smul_right_eq
#print axioms prob_mcaEvent_shear_eq
#print axioms epsMCA_eq_iSup_rep
#print axioms rsC_rot_closed
#print axioms prob_mcaEvent_rsC_rot_eq

end ProximityGap.MCAEquivariance

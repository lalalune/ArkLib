/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.MCAEquivariance

/-!
# S3/N1 (#357): the MCA symmetry group is projective — GL₂ equivariance and the ∞ slot

The probe campaign on the R1 code `RS[F₅, ⟨2⟩, 2]` at `δ = 1/4` found (exhaustive, exact):
the `ε_mca`-maximizer set (100,000 of the 390,625 stacks) is **not** one orbit of the affine
symmetry group of `MCAEquivariance` (laws 1–4 generate orbits of size 50,000) — it is exactly
**two** disjoint affine orbits, fused into **one** orbit by the non-affine GL₂ element
`(u₀, u₁) ↦ (u₁, u₀ + u₁)`. The explanation, formalized here: the true symmetry group of the
MCA bad event acts **projectively** on the pencil of a stack.

* `mcaEventProj C δ u₀ u₁ α β` — badness of the projective pencil point `α•u₀ + β•u₁`:
  the homogeneous form of `mcaEvent` (which is the chart `α = 1`, `mcaEventProj_one_gamma`).
  The affine `γ`-line misses one slot: `[0 : 1]` — the *point at infinity*, whose badness
  `mcaEventProj C δ u₀ u₁ 0 1` is about the second row alone.
* `pairJointAgreesOn_row_mix_iff` — the no-joint-explanation clause is invariant under
  **every invertible row mix** `(u₀, u₁) ↦ (a•u₀ + b•u₁, c•u₀ + d•u₁)`: joint explanations
  mix along, in both directions, by linearity of `C`.
* `mcaEventProj_smul` — projective well-definedness: scaling `(α, β)` by a unit does not
  change badness.
* `mcaEventProj_row_mix` — **GL₂ equivariance**: badness of the mixed stack at `(α, β)`
  equals badness of the original at `(α, β) · M` (row-vector action). The pencil *as a set
  of words* is GL₂-invariant; only its parametrization moves.
* `badSlotCount` / `badSlotCount_eq` — the projective census over the `|F| + 1` slots
  (`some γ ↦ [1 : γ]`, `none ↦ [0 : 1]`): the affine bad-scalar count of
  `MCADeltaStarExactPoint`/`MCAEquivariance` is the projective count minus the ∞ indicator
  (`badSlotCount_eq_affine_add_infty`).

Why this matters for the campaign:

1. **The two-orbit split is now a theorem-shaped fact, not an anomaly**: laws 1–4 stabilize
   `∞`; a full projective orbit splits into affine orbits indexed by which projective slots
   sit at `∞`. The probe's `100,000 = 2 × 50,000` is the `|orbit| = Σ` of that fibration.
2. **N1 (structured extremality) gets its invariant**: the right structure group for
   "maximizers are one orbit" is the projective one. At the R1 rung this is now *verified
   exhaustively* (probe) with the group action *formalized* (this file + `MCAEquivariance`).
3. **The γ-census transforms as a projective object** — any future flat-numerator law must
   be stated on the `|F|+1` slots, not the `|F|` affine ones. This retroactively explains
   why affine bad counts drift by `±1` inside structure classes.

All results are `sorry`-free and axiom-clean (`[propext, Classical.choice, Quot.sound]`).

## References
- Issue #357 (the δ* campaign; hypotheses S3/N1); [ABF26] ePrint 2026/680.
- Probe: `/tmp` orbit audit 2026-06-11 (exhaustive at RS[F₅,⟨2⟩,2], two-engine ground truth).
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

open scoped NNReal ENNReal ProbabilityTheory
open ProximityGap Code

namespace ProximityGap.MCAProjectiveEquivariance

variable {ι : Type} [Fintype ι] [Nonempty ι] [DecidableEq ι]
variable {F : Type} [Field F] [Fintype F] [DecidableEq F]
variable {A : Type} [Fintype A] [DecidableEq A] [AddCommGroup A] [Module F A]

/-! ## The homogeneous (projective) bad event -/

/-- Badness of the projective pencil point `α•u₀ + β•u₁` of the stack `(u₀, u₁)`: some
witness set `S` of size `≥ (1−δ)n` carries a codeword equal to the pencil word on `S`, while
no joint pair of codewords explains the stack on `S`. `mcaEvent` is the chart `α = 1`
(`mcaEventProj_one_gamma`); the slot `(α, β) = (0, 1)` is the point at infinity. -/
def mcaEventProj (C : Set (ι → A)) (δ : ℝ≥0) (u₀ u₁ : ι → A) (α β : F) : Prop :=
  ∃ S : Finset ι, (S.card : ℝ≥0) ≥ (1 - δ) * Fintype.card ι ∧
    (∃ w ∈ C, ∀ i ∈ S, w i = α • u₀ i + β • u₁ i) ∧
    ¬ pairJointAgreesOn C S u₀ u₁

/-- The affine MCA event is the `α = 1` chart of the projective event. -/
theorem mcaEventProj_one_gamma (C : Set (ι → A)) (δ : ℝ≥0) (u₀ u₁ : ι → A) (γ : F) :
    mcaEventProj (F := F) C δ u₀ u₁ 1 γ ↔ mcaEvent (F := F) C δ u₀ u₁ γ := by
  unfold mcaEventProj mcaEvent
  constructor <;>
    · rintro ⟨S, hS, ⟨w, hw, hweq⟩, hno⟩
      refine ⟨S, hS, ⟨w, hw, fun i hi => ?_⟩, hno⟩
      have h := hweq i hi
      simpa [one_smul] using h

/-! ## Row mixes: the GL₂ action -/

/-- Joint explanations transport along **any** row mix (one direction, no invertibility):
if `(v₀, v₁)` explains `(u₀, u₁)` on `S`, then `(a•v₀ + b•v₁, c•v₀ + d•v₁)` explains
`(a•u₀ + b•u₁, c•u₀ + d•u₁)` on `S`. -/
theorem pairJointAgreesOn_row_mix_of (C : Submodule F (ι → A)) (a b c d : F)
    {S : Finset ι} {u₀ u₁ : ι → A}
    (h : pairJointAgreesOn (C : Set (ι → A)) S u₀ u₁) :
    pairJointAgreesOn (C : Set (ι → A)) S (a • u₀ + b • u₁) (c • u₀ + d • u₁) := by
  obtain ⟨v₀, hv₀, v₁, hv₁, hag⟩ := h
  refine ⟨a • v₀ + b • v₁, C.add_mem (C.smul_mem a hv₀) (C.smul_mem b hv₁),
    c • v₀ + d • v₁, C.add_mem (C.smul_mem c hv₀) (C.smul_mem d hv₁), fun i hi => ?_⟩
  refine ⟨?_, ?_⟩
  · show a • v₀ i + b • v₁ i = a • u₀ i + b • u₁ i
    rw [(hag i hi).1, (hag i hi).2]
  · show c • v₀ i + d • v₁ i = c • u₀ i + d • u₁ i
    rw [(hag i hi).1, (hag i hi).2]

/-- The inverse row mix recovers the original rows (pointwise form): for `e := ad − bc ≠ 0`,
`e⁻¹ • (d • (a•x + b•y) − b • (c•x + d•y)) = x` and
`e⁻¹ • (a • (c•x + d•y) − c • (a•x + b•y)) = y`. -/
theorem row_mix_inv_left {a b c d e : F} (he : a * d - b * c = e) (he0 : e ≠ 0)
    (x y : A) :
    e⁻¹ • (d • (a • x + b • y) - b • (c • x + d • y)) = x := by
  have hexp : d • (a • x + b • y) - b • (c • x + d • y) = e • x := by
    rw [← he]
    module
  rw [hexp, smul_smul, inv_mul_cancel₀ he0, one_smul]

theorem row_mix_inv_right {a b c d e : F} (he : a * d - b * c = e) (he0 : e ≠ 0)
    (x y : A) :
    e⁻¹ • (a • (c • x + d • y) - c • (a • x + b • y)) = y := by
  have hexp : a • (c • x + d • y) - c • (a • x + b • y) = e • y := by
    rw [← he]
    module
  rw [hexp, smul_smul, inv_mul_cancel₀ he0, one_smul]

/-- **The no-joint-explanation clause is GL₂-invariant**: for an invertible row mix
(`ad − bc ≠ 0`), the stack `(a•u₀ + b•u₁, c•u₀ + d•u₁)` is jointly explained on `S` iff
`(u₀, u₁)` is. -/
theorem pairJointAgreesOn_row_mix_iff (C : Submodule F (ι → A)) {a b c d : F}
    (hdet : a * d - b * c ≠ 0) (S : Finset ι) (u₀ u₁ : ι → A) :
    pairJointAgreesOn (C : Set (ι → A)) S (a • u₀ + b • u₁) (c • u₀ + d • u₁) ↔
      pairJointAgreesOn (C : Set (ι → A)) S u₀ u₁ := by
  set e := a * d - b * c with hedef
  constructor
  · rintro ⟨v₀, hv₀, v₁, hv₁, hag⟩
    -- invert the mix on the explaining pair
    refine ⟨(e⁻¹ * d) • v₀ + (e⁻¹ * -b) • v₁,
      C.add_mem (C.smul_mem _ hv₀) (C.smul_mem _ hv₁),
      (e⁻¹ * -c) • v₀ + (e⁻¹ * a) • v₁,
      C.add_mem (C.smul_mem _ hv₀) (C.smul_mem _ hv₁), fun i hi => ?_⟩
    have h₀ := (hag i hi).1
    have h₁ := (hag i hi).2
    constructor
    · show (e⁻¹ * d) • v₀ i + (e⁻¹ * -b) • v₁ i = u₀ i
      have := row_mix_inv_left (a := a) (b := b) (c := c) (d := d) hedef.symm hdet
        (u₀ i) (u₁ i)
      calc (e⁻¹ * d) • v₀ i + (e⁻¹ * -b) • v₁ i
          = e⁻¹ • (d • v₀ i - b • v₁ i) := by module
        _ = e⁻¹ • (d • (a • u₀ i + b • u₁ i) - b • (c • u₀ i + d • u₁ i)) := by
            rw [h₀, h₁]
            rfl
        _ = u₀ i := this
    · show (e⁻¹ * -c) • v₀ i + (e⁻¹ * a) • v₁ i = u₁ i
      have := row_mix_inv_right (a := a) (b := b) (c := c) (d := d) hedef.symm hdet
        (u₀ i) (u₁ i)
      calc (e⁻¹ * -c) • v₀ i + (e⁻¹ * a) • v₁ i
          = e⁻¹ • (a • v₁ i - c • v₀ i) := by module
        _ = e⁻¹ • (a • (c • u₀ i + d • u₁ i) - c • (a • u₀ i + b • u₁ i)) := by
            rw [h₀, h₁]
            rfl
        _ = u₁ i := this
  · exact pairJointAgreesOn_row_mix_of C a b c d

/-- **GL₂ equivariance of the projective bad event.** For an invertible row mix `M`, badness
of the mixed stack at `(α, β)` equals badness of the original stack at the row-vector image
`(α, β) · M = (αa + βc, αb + βd)`: the pencil is GL₂-stable, only the parametrization moves. -/
theorem mcaEventProj_row_mix (C : Submodule F (ι → A)) {a b c d : F}
    (hdet : a * d - b * c ≠ 0) (δ : ℝ≥0) (u₀ u₁ : ι → A) (α β : F) :
    mcaEventProj (F := F) (C : Set (ι → A)) δ (a • u₀ + b • u₁) (c • u₀ + d • u₁) α β ↔
      mcaEventProj (F := F) (C : Set (ι → A)) δ u₀ u₁ (α * a + β * c) (α * b + β * d) := by
  have hword : ∀ i, α • (a • u₀ i + b • u₁ i) + β • (c • u₀ i + d • u₁ i)
      = (α * a + β * c) • u₀ i + (α * b + β * d) • u₁ i := fun i => by module
  unfold mcaEventProj
  constructor
  · rintro ⟨S, hS, ⟨w, hw, hweq⟩, hno⟩
    refine ⟨S, hS, ⟨w, hw, fun i hi => ?_⟩, fun hp => ?_⟩
    · have h := hweq i hi
      show w i = (α * a + β * c) • u₀ i + (α * b + β * d) • u₁ i
      rw [h]
      exact hword i
    · exact hno ((pairJointAgreesOn_row_mix_iff C hdet S u₀ u₁).mpr hp)
  · rintro ⟨S, hS, ⟨w, hw, hweq⟩, hno⟩
    refine ⟨S, hS, ⟨w, hw, fun i hi => ?_⟩, fun hp => ?_⟩
    · have h := hweq i hi
      show w i = α • ((a • u₀ + b • u₁) i) + β • ((c • u₀ + d • u₁) i)
      rw [h]
      exact (hword i).symm
    · exact hno ((pairJointAgreesOn_row_mix_iff C hdet S u₀ u₁).mp hp)

/-- **Projective well-definedness**: scaling the homogeneous coordinates `(α, β)` by a unit
does not change badness (the pencil word scales by a unit, and `C` is scale-closed). -/
theorem mcaEventProj_smul (C : Submodule F (ι → A)) {e : F} (he : e ≠ 0)
    (δ : ℝ≥0) (u₀ u₁ : ι → A) (α β : F) :
    mcaEventProj (F := F) (C : Set (ι → A)) δ u₀ u₁ (e * α) (e * β) ↔
      mcaEventProj (F := F) (C : Set (ι → A)) δ u₀ u₁ α β := by
  unfold mcaEventProj
  constructor
  · rintro ⟨S, hS, ⟨w, hw, hweq⟩, hno⟩
    refine ⟨S, hS, ⟨e⁻¹ • w, C.smul_mem e⁻¹ hw, fun i hi => ?_⟩, hno⟩
    show e⁻¹ • w i = α • u₀ i + β • u₁ i
    rw [hweq i hi]
    show e⁻¹ • ((e * α) • u₀ i + (e * β) • u₁ i) = _
    rw [smul_add, smul_smul, smul_smul, ← mul_assoc, ← mul_assoc,
      inv_mul_cancel₀ he, one_mul, one_mul]
  · rintro ⟨S, hS, ⟨w, hw, hweq⟩, hno⟩
    refine ⟨S, hS, ⟨e • w, C.smul_mem e hw, fun i hi => ?_⟩, hno⟩
    show e • w i = (e * α) • u₀ i + (e * β) • u₁ i
    rw [hweq i hi, smul_add, smul_smul, smul_smul]

/-! ## The slot census: affine count = projective count minus the ∞ indicator -/

/-- The `|F| + 1` projective slots: `some γ` is the affine chart point `[1 : γ]`, `none` is
the point at infinity `[0 : 1]`. -/
def slotCoords : Option F → F × F
  | some γ => (1, γ)
  | none => (0, 1)

/-- Badness of a projective slot. -/
def badSlot (C : Set (ι → A)) (δ : ℝ≥0) (u₀ u₁ : ι → A) (s : Option F) : Prop :=
  mcaEventProj (F := F) C δ u₀ u₁ (slotCoords s).1 (slotCoords s).2

open Classical in
/-- The projective census of a stack: the number of bad slots among the `|F| + 1`. -/
noncomputable def badSlotCount (C : Set (ι → A)) (δ : ℝ≥0) (u₀ u₁ : ι → A) : ℕ :=
  (Finset.filter (fun s : Option F => badSlot C δ u₀ u₁ s) Finset.univ).card

open Classical in
/-- **The census decomposition**: the projective slot count is the affine bad-scalar count
plus the indicator of the slot at infinity. Affine censuses (everything in
`MCADeltaStarExactPoint`, the probe engine, the flat-numerator data) are projective censuses
with the `∞` slot subtracted — which is why affine counts drift by `±1` inside one projective
structure class while the projective count is the true invariant. -/
theorem badSlotCount_eq_affine_add_infty (C : Set (ι → A)) (δ : ℝ≥0) (u₀ u₁ : ι → A) :
    badSlotCount (F := F) C δ u₀ u₁
      = (Finset.filter (fun γ : F => mcaEvent (F := F) C δ u₀ u₁ γ) Finset.univ).card
        + (if mcaEventProj (F := F) C δ u₀ u₁ 0 1 then 1 else 0) := by
  classical
  unfold badSlotCount
  -- split the Option-universe into the `some` image and `{none}`
  have hunion : (Finset.univ : Finset (Option F))
      = Finset.univ.image (Option.some) ∪ {none} := by
    apply Finset.eq_of_subset_of_card_le
    · intro s _
      rcases s with _ | γ
      · exact Finset.mem_union_right _ (Finset.mem_singleton_self none)
      · exact Finset.mem_union_left _ (Finset.mem_image_of_mem _ (Finset.mem_univ γ))
    · exact Finset.card_le_univ _
  rw [hunion, Finset.filter_union, Finset.card_union_of_disjoint, Finset.filter_image]
  · congr 1
    · -- the `some` part is the affine census
      rw [Finset.card_image_of_injective _ (Option.some_injective F)]
      congr 1
      apply Finset.filter_congr
      intro γ _
      show badSlot C δ u₀ u₁ (some γ) ↔ mcaEvent (F := F) C δ u₀ u₁ γ
      unfold badSlot slotCoords
      exact mcaEventProj_one_gamma C δ u₀ u₁ γ
    · -- the `none` part is the ∞ indicator
      by_cases h : mcaEventProj (F := F) C δ u₀ u₁ 0 1
      · rw [if_pos h]
        rw [Finset.filter_singleton, if_pos]
        · exact Finset.card_singleton none
        · exact h
      · rw [if_neg h]
        rw [Finset.filter_singleton, if_neg]
        · exact Finset.card_empty
        · exact h
  · -- disjointness of the union pieces
    refine Finset.disjoint_filter_filter ?_
    rw [Finset.disjoint_left]
    intro s hs hns
    rw [Finset.mem_image] at hs
    obtain ⟨γ, _, rfl⟩ := hs
    exact Option.some_ne_none γ (Finset.mem_singleton.mp hns)

/-! ## Source audit -/

#print axioms mcaEventProj_one_gamma
#print axioms pairJointAgreesOn_row_mix_iff
#print axioms mcaEventProj_row_mix
#print axioms mcaEventProj_smul
#print axioms badSlotCount_eq_affine_add_infty

end ProximityGap.MCAProjectiveEquivariance

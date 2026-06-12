/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.FarCosetExplosion

set_option linter.unusedFintypeInType false
set_option linter.unusedDecidableInType false
set_option linter.unusedSectionVars false

/-!
# Abstract tuple ownership bounds for the δ* incidence face (#371)

This file packages the counting skeleton common to the Welch--Berlekamp pencil
lane and the KKH26 dimension ladder.  A residual family `res T y` plays the role
of the `(k+1)`-point interpolation defect: it is local on `T`, kills codewords,
and is linear along affine stack lines.  Then any owned subset `T` with
`res T u₁ ≠ 0` determines the scalar `γ`; owned subsets are disjoint across
bad scalars; and a lower bound `θ` on ownership per witness gives

  `#bad scalars * θ ≤ C(n, r)`.

Honest scope: this is the universal ownership-counting engine.  The hard
geometry remains proving useful lower bounds on `θ` for concrete residuals
(for example the `2 * 3! = 12` line-split in `KKH26DimTwoPin.lean`, and the
next `2 * 4! = 48` target).
-/

open Finset
open scoped NNReal

namespace ProximityGap.OwnershipBound

variable {F : Type} [Field F] [Fintype F] [DecidableEq F]
variable {ι : Type} [Fintype ι] [Nonempty ι] [DecidableEq ι]

/-! ## The finite ownership-counting engine -/

open Classical in
/-- If every bad scalar owns at least `θ` objects, all owned objects lie in `U`, and
the ownership families are pairwise disjoint, then `#bad * θ ≤ #U`. -/
theorem card_mul_le_card_of_owned
    {Γ Ω : Type*} [DecidableEq Ω] (B : Finset Γ) (U : Finset Ω)
    (owned : {γ // γ ∈ B} → Finset Ω) (θ : ℕ)
    (hmin : ∀ γ : {γ // γ ∈ B}, θ ≤ (owned γ).card)
    (hsub : ∀ γ : {γ // γ ∈ B}, owned γ ⊆ U)
    (hdisj : ∀ γ₁ ∈ B.attach, ∀ γ₂ ∈ B.attach, γ₁ ≠ γ₂ →
      Disjoint (owned γ₁) (owned γ₂)) :
    B.card * θ ≤ U.card := by
  classical
  have hbig : B.attach.card * θ ≤ (B.attach.biUnion owned).card := by
    rw [Finset.card_biUnion hdisj]
    calc
      B.attach.card * θ = ∑ _γ ∈ B.attach, θ := by
        rw [Finset.sum_const, smul_eq_mul, Nat.mul_comm]
      _ ≤ ∑ γ ∈ B.attach, (owned γ).card :=
        Finset.sum_le_sum (fun γ _ => hmin γ)
  calc
    B.card * θ = B.attach.card * θ := by rw [Finset.card_attach]
    _ ≤ (B.attach.biUnion owned).card := hbig
    _ ≤ U.card := by
      refine Finset.card_le_card ?_
      intro x hx
      obtain ⟨γ, _, hxγ⟩ := Finset.mem_biUnion.mp hx
      exact hsub γ hxγ

/-! ## Residual roots and scalar determination -/

/-- The scalar forced by a nonzero residual direction coordinate. -/
def residualRoot {Ω : Type*} (e₀ e₁ : Ω → F) (T : Ω) : F :=
  -e₀ T / e₁ T

/-- If the residual line coordinate vanishes and the direction residual is nonzero,
then the residual root is exactly the scalar. -/
theorem residualRoot_eq_of_line_zero {Ω : Type*} (e₀ e₁ : Ω → F) {T : Ω} {γ : F}
    (h₁ : e₁ T ≠ 0) (hzero : e₀ T + γ * e₁ T = 0) :
    residualRoot e₀ e₁ T = γ := by
  unfold residualRoot
  rw [div_eq_iff h₁]
  linear_combination -hzero

/-- Owned `r`-subsets inside a witness set: subsets on which the direction residual
is nonzero. -/
def residualOwned (S : Finset ι) (r : ℕ) (e₁ : Finset ι → F) : Finset (Finset ι) :=
  (S.powersetCard r).filter fun T => e₁ T ≠ 0

/-- A residual is local on `T` if equal words on `T` have equal residual. -/
def LocalOn (res : Finset ι → (ι → F) → F) : Prop :=
  ∀ T y z, (∀ i ∈ T, y i = z i) → res T y = res T z

/-- A residual is affine-linear along the stack line. -/
def LineLinear (res : Finset ι → (ι → F) → F) : Prop :=
  ∀ T (u₀ u₁ : ι → F) (γ : F),
    res T (fun i => u₀ i + γ • u₁ i) = res T u₀ + γ * res T u₁

/-- Agreement with a codeword on a witness set forces the residual line coordinate
to vanish on every contained `r`-subset. -/
theorem residual_line_vanish_of_agreement
    (C : Set (ι → F)) (r : ℕ) (res : Finset ι → (ι → F) → F)
    (hlocal : LocalOn res) (hline : LineLinear res)
    (hkill : ∀ T : Finset ι, T.card = r → ∀ c ∈ C, res T c = 0)
    {u₀ u₁ w : ι → F} {γ : F} {S T : Finset ι}
    (hT : T ∈ S.powersetCard r) (hw : w ∈ C)
    (hagree : ∀ i ∈ S, w i = u₀ i + γ • u₁ i) :
    res T u₀ + γ * res T u₁ = 0 := by
  obtain ⟨hTsub, hTcard⟩ := Finset.mem_powersetCard.mp hT
  have hsame : res T (fun i => u₀ i + γ • u₁ i) = res T w := by
    exact hlocal T _ _ fun i hi => (hagree i (hTsub hi)).symm
  rw [hline T u₀ u₁ γ, hkill T hTcard w hw] at hsame
  exact hsame

/-- The per-subset scalar-determination lemma: a nonzero owned residual subset inside
an explaining witness determines `γ`. -/
theorem residualRoot_eq_of_owned_agreement
    (C : Set (ι → F)) (r : ℕ) (res : Finset ι → (ι → F) → F)
    (hlocal : LocalOn res) (hline : LineLinear res)
    (hkill : ∀ T : Finset ι, T.card = r → ∀ c ∈ C, res T c = 0)
    {u₀ u₁ w : ι → F} {γ : F} {S T : Finset ι}
    (hT : T ∈ residualOwned S r (fun T => res T u₁)) (hw : w ∈ C)
    (hagree : ∀ i ∈ S, w i = u₀ i + γ • u₁ i) :
    residualRoot (fun T => res T u₀) (fun T => res T u₁) T = γ := by
  obtain ⟨hTpowerset, hTne⟩ := Finset.mem_filter.mp hT
  exact residualRoot_eq_of_line_zero _ _ hTne
    (residual_line_vanish_of_agreement C r res hlocal hline hkill hTpowerset hw hagree)

/-! ## Explainable and far-coset bad-scalar forms -/

/-- Pure line explainability: the line point `u₀ + γu₁` agrees with some codeword
on a witness-sized set. -/
def LineExplainable (C : Set (ι → F)) (δ : ℝ≥0) (u₀ u₁ : ι → F) (γ : F) : Prop :=
  ∃ S : Finset ι, (S.card : ℝ≥0) ≥ (1 - δ) * Fintype.card ι ∧
    ∃ w ∈ C, ∀ i ∈ S, w i = u₀ i + γ • u₁ i

open Classical in
/-- **Abstract tuple-ownership bound for explainable scalars.**  If every
witness-sized set owns at least `θ` nonzero residual `r`-subsets, then the number
of explainable scalars is at most `C(n,r)/θ` in multiplicative form. -/
theorem lineExplainable_card_mul_le_choose_of_residual
    (C : Set (ι → F)) (δ : ℝ≥0) (u₀ u₁ : ι → F) (r θ : ℕ)
    (res : Finset ι → (ι → F) → F)
    (hlocal : LocalOn res) (hline : LineLinear res)
    (hkill : ∀ T : Finset ι, T.card = r → ∀ c ∈ C, res T c = 0)
    (hdetect : ∀ S : Finset ι, (S.card : ℝ≥0) ≥ (1 - δ) * Fintype.card ι →
      θ ≤ (residualOwned S r (fun T => res T u₁)).card) :
    (Finset.univ.filter fun γ : F => LineExplainable C δ u₀ u₁ γ).card * θ
      ≤ (Fintype.card ι).choose r := by
  classical
  set B : Finset F := Finset.univ.filter fun γ : F => LineExplainable C δ u₀ u₁ γ with hB
  have hwit : ∀ γ : {γ // γ ∈ B}, ∃ S : Finset ι,
      (S.card : ℝ≥0) ≥ (1 - δ) * Fintype.card ι ∧
        ∃ w ∈ C, ∀ i ∈ S, w i = u₀ i + γ.1 • u₁ i := by
    intro γ
    have hmem : γ.1 ∈
        (Finset.univ.filter fun γ : F => LineExplainable C δ u₀ u₁ γ) := by
      rw [← hB]
      exact γ.2
    exact (Finset.mem_filter.mp hmem).2
  choose S hS using hwit
  let owned : {γ // γ ∈ B} → Finset (Finset ι) :=
    fun γ => residualOwned (S γ) r (fun T => res T u₁)
  let U : Finset (Finset ι) := (Finset.univ : Finset ι).powersetCard r
  have hmin : ∀ γ : {γ // γ ∈ B}, θ ≤ (owned γ).card := by
    intro γ
    exact hdetect (S γ) (hS γ).1
  have hsub : ∀ γ : {γ // γ ∈ B}, owned γ ⊆ U := by
    intro γ T hT
    obtain ⟨hTpowerset, _⟩ := Finset.mem_filter.mp hT
    obtain ⟨hTsub, hTcard⟩ := Finset.mem_powersetCard.mp hTpowerset
    exact Finset.mem_powersetCard.mpr ⟨Finset.subset_univ T, hTcard⟩
  have hdisj : ∀ γ₁ ∈ B.attach, ∀ γ₂ ∈ B.attach, γ₁ ≠ γ₂ →
      Disjoint (owned γ₁) (owned γ₂) := by
    intro γ₁ _ γ₂ _ hne
    rw [Finset.disjoint_left]
    intro T hT₁ hT₂
    obtain ⟨w₁, hw₁, hagree₁⟩ := (hS γ₁).2
    obtain ⟨w₂, hw₂, hagree₂⟩ := (hS γ₂).2
    have hroot₁ := residualRoot_eq_of_owned_agreement C r res hlocal hline hkill
      (u₀ := u₀) (u₁ := u₁) (w := w₁) (γ := γ₁.1) hT₁ hw₁ hagree₁
    have hroot₂ := residualRoot_eq_of_owned_agreement C r res hlocal hline hkill
      (u₀ := u₀) (u₁ := u₁) (w := w₂) (γ := γ₂.1) hT₂ hw₂ hagree₂
    exact hne (Subtype.ext (hroot₁.symm.trans hroot₂))
  have hcount := card_mul_le_card_of_owned B U owned θ hmin hsub hdisj
  simpa [B, U] using hcount

open Classical in
/-- **Far-coset MCA form.**  Under `FarFromCode`, MCA bad scalars are exactly
line-explainable scalars, so the abstract residual ownership bound applies directly
to the `mcaEvent` set. -/
theorem mcaEvent_card_mul_le_choose_of_far_residual
    (C : Set (ι → F)) (δ : ℝ≥0) (u₀ u₁ : ι → F) (r θ : ℕ)
    (res : Finset ι → (ι → F) → F)
    (hfar : FarCosetExplosion.FarFromCode C δ u₁)
    (hlocal : LocalOn res) (hline : LineLinear res)
    (hkill : ∀ T : Finset ι, T.card = r → ∀ c ∈ C, res T c = 0)
    (hdetect : ∀ S : Finset ι, (S.card : ℝ≥0) ≥ (1 - δ) * Fintype.card ι →
      θ ≤ (residualOwned S r (fun T => res T u₁)).card) :
    (Finset.univ.filter fun γ : F => mcaEvent (F := F) C δ u₀ u₁ γ).card * θ
      ≤ (Fintype.card ι).choose r := by
  rw [FarCosetExplosion.badScalars_eq_explainable C δ hfar]
  simpa [LineExplainable, smul_eq_mul] using
    lineExplainable_card_mul_le_choose_of_residual
      C δ u₀ u₁ r θ res hlocal hline hkill hdetect

end ProximityGap.OwnershipBound

/-! ## Axiom audit — kernel-clean. -/
#print axioms ProximityGap.OwnershipBound.card_mul_le_card_of_owned
#print axioms ProximityGap.OwnershipBound.residualRoot_eq_of_line_zero
#print axioms ProximityGap.OwnershipBound.residual_line_vanish_of_agreement
#print axioms ProximityGap.OwnershipBound.residualRoot_eq_of_owned_agreement
#print axioms ProximityGap.OwnershipBound.lineExplainable_card_mul_le_choose_of_residual
#print axioms ProximityGap.OwnershipBound.mcaEvent_card_mul_le_choose_of_far_residual

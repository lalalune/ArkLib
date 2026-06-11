/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.BCIKS20.StrictCoeffPolysExceptional

/-!
# Finding F14, formalized: the strict-coefficient residuals are refutable as stated

Above the unique-decoding radius — which the residuals' own hypothesis `(1−ρ)/2 < δ`
*grants* — the single-`B`-over-the-whole-good-set demand of
`ProximityGap.StrictCoeffPolysResidual` (and the uniqueness demand of
`StrictCanonicalCoeffPolysResidual`) is false, by **the constant-fold attack**:

* take a word `w` within radius `δ` of two *distinct* codewords `c₁ ≠ c₂` (list ambiguity —
  exactly what `δ > (1−ρ)/2` permits);
* the **constant word stack** `u 0 := w, u t := 0` has `∑ t, z^t • u t = w` at *every*
  curve parameter, so every `z` is good and the §5 probability is `1`;
* the adversarial decoded family `P z := if z = z₀ then c₂ else c₁` is a valid decoding at
  every good point, but any coefficient family `B` matching it on all of `F` is
  interpolation-pinned to `c₁`'s coefficients on `F \ {z₀}` and must hit `c₂`'s at `z₀` —
  forcing `c₁ = c₂`.

Independent confirmation: [BCHKS25] (eprint 2025/2055) — Johnson-radius correlated agreement
holds with `O(n)` exceptional parameters, and `Ω(n^{1.99})` exceptions are provably
necessary.  The honest targets are the exceptional/share forms
(`StrictCoeffPolysResidualExc`, `StrictCoeffPolysResidualShare`), which the §5 machinery can
actually discharge; this file justifies that retargeting formally.

Main results:
* `not_strictCoeffPolysResidual_of_attack_data` — `¬ StrictCoeffPolysResidual` from named
  attack data (two close codewords + parameter window side conditions).
* `not_strictCanonicalCoeffPolysResidual_of_attack_data` — the canonical (uniqueness) form
  falls to the same data, without even needing the interpolation pinning.

## References
* [BCIKS20] Ben-Sasson, Carmon, Ishai, Kopparty, Saraf, *Proximity Gaps for Reed–Solomon
  Codes*, §5.
* [BCHKS25] Ben-Sasson, Carmon, Haböck, Kopparty, Saraf, *On Proximity Gaps for
  Reed–Solomon Codes*, eprint 2025/2055.
-/

set_option linter.style.longLine false

namespace ProximityGap

open Polynomial NNReal Finset Function ProbabilityTheory Code
open scoped BigOperators ENNReal ProbabilityTheory LinearCode

variable {ι : Type} [Fintype ι] [Nonempty ι] [DecidableEq ι]
variable {F : Type} [Field F] [Fintype F] [DecidableEq F]

/-! ## The constant fold -/

/-- The constant word stack: `w` in slot `0`, zero elsewhere. -/
def constStack (w : ι → F) (k : ℕ) : WordStack F (Fin (k + 1)) ι :=
  fun t => if t = 0 then w else 0

/-- Every fold of the constant stack is `w`. -/
theorem fold_constStack (w : ι → F) (k : ℕ) (z : F) :
    ∑ t : Fin (k + 1), (z ^ (t : ℕ)) • constStack w k t = w := by
  rw [Finset.sum_eq_single (0 : Fin (k + 1))]
  · simp [constStack]
  · intro t _ ht
    simp [constStack, ht]
  · intro h
    exact absurd (Finset.mem_univ _) h

/-- Every parameter is good for the constant stack at a `δ`-close-to-code word. -/
theorem goodCoeffsCurve_constStack_eq_univ {k deg : ℕ} {domain : ι ↪ F} {δ : ℝ≥0}
    {w : ι → F} {c₁ : Polynomial F} (hdeg1 : c₁.natDegree < deg)
    (hw1 : (δᵣ(w, fun x => c₁.eval (domain x)) : ℝ≥0∞) ≤ (δ : ℝ≥0∞)) :
    RS_goodCoeffsCurve (k := k) (deg := deg) (domain := domain) (constStack w k) δ
      = Finset.univ := by
  apply Finset.eq_univ_of_forall
  intro z
  rw [RS_goodCoeffsCurve, Finset.mem_filter]
  refine ⟨Finset.mem_univ z, ?_⟩
  rw [fold_constStack]
  calc δᵣ(w, (ReedSolomon.code domain deg : Set (ι → F)))
      ≤ (δᵣ(w, fun x => c₁.eval (domain x)) : ℝ≥0∞) :=
        relDistFromCode_le_relDist_to_mem w _
          (ReedSolomon.mem_code_of_polynomial_of_natDegree_lt_of_eval c₁ hdeg1
            (fun i => rfl))
    _ ≤ (δ : ℝ≥0∞) := hw1

/-- The §5 probability for the constant stack is `1`. -/
theorem prob_constStack_eq_one {k deg : ℕ} {domain : ι ↪ F} {δ : ℝ≥0}
    {w : ι → F} {c₁ : Polynomial F} (hdeg1 : c₁.natDegree < deg)
    (hw1 : (δᵣ(w, fun x => c₁.eval (domain x)) : ℝ≥0∞) ≤ (δ : ℝ≥0∞)) :
    Pr_{
      let z ← $ᵖ F}[δᵣ(∑ t : Fin (k + 1), (z ^ (t : ℕ)) • constStack w k t,
        ReedSolomon.code domain deg) ≤ δ] = 1 := by
  classical
  have hgood : ∀ z : F,
      δᵣ(∑ t : Fin (k + 1), (z ^ (t : ℕ)) • constStack w k t,
        ReedSolomon.code domain deg) ≤ δ := by
    intro z
    have := goodCoeffsCurve_constStack_eq_univ (k := k) (deg := deg) (domain := domain)
      (δ := δ) hdeg1 hw1
    have hz : z ∈ RS_goodCoeffsCurve (k := k) (deg := deg) (domain := domain)
        (constStack w k) δ := by
      rw [this]
      exact Finset.mem_univ z
    rw [RS_goodCoeffsCurve, Finset.mem_filter] at hz
    exact hz.2
  -- a sure event has probability one
  simp only [Bind.bind, PMF.bind, PMF.uniformOfFintype_apply, pure, PMF.pure_apply,
    eq_iff_iff]
  simp only [DFunLike.coe]
  have hone : ∀ z : F, (if True ↔ δᵣ(∑ t : Fin (k + 1),
      (z ^ (t : ℕ)) • constStack w k t, ReedSolomon.code domain deg) ≤ δ
        then (1 : ENNReal) else 0) = 1 := by
    intro z
    rw [if_pos (iff_of_true trivial (hgood z))]
  calc (∑' z : F, ((Fintype.card F : ENNReal))⁻¹ * _) = _ := rfl
    _ = 1 := by
      simp only [hone, mul_one]
      rw [ENNReal.tsum_const]
      rw [ENNReal.nsmul_eq_mul, ENNReal.mul_inv_cancel]
      · exact_mod_cast Fintype.card_ne_zero
      · exact ENNReal.natCast_ne_top _

/-! ## The attack -/

/-- **Finding F14, plain form**: `StrictCoeffPolysResidual` is refuted by any list-ambiguous
word strictly inside the residual's own parameter window. -/
theorem not_strictCoeffPolysResidual_of_attack_data {k deg : ℕ} {domain : ι ↪ F} {δ : ℝ≥0}
    {c₁ c₂ : Polynomial F} (hc12 : c₁ ≠ c₂)
    (hdeg1 : c₁.natDegree < deg) (hdeg2 : c₂.natDegree < deg)
    {w : ι → F}
    (hw1 : (δᵣ(w, fun x => c₁.eval (domain x)) : ℝ≥0∞) ≤ (δ : ℝ≥0∞))
    (hw2 : (δᵣ(w, fun x => c₂.eval (domain x)) : ℝ≥0∞) ≤ (δ : ℝ≥0∞))
    (hk : 0 < k)
    (hsmall : ((k : ℝ≥0∞) * (errorBound δ deg domain : ℝ≥0∞)) < 1)
    (hJ : (1 - (LinearCode.rate (ReedSolomon.code domain deg) : ℝ≥0)) / 2 < δ)
    (hsqrt : δ < 1 - ReedSolomon.sqrtRate deg domain)
    (hF : k + 2 ≤ Fintype.card F) :
    ¬ StrictCoeffPolysResidual (k := k) (deg := deg) (domain := domain) (δ := δ) := by
  classical
  intro hres
  -- a distinguished parameter
  obtain ⟨z₀⟩ : Nonempty F := by
    have : 0 < Fintype.card F := by omega
    exact Fintype.card_pos_iff.mp this
  -- the adversarial decoded family
  set P : F → Polynomial F := fun z => if z = z₀ then c₂ else c₁ with hP
  have hgood := goodCoeffsCurve_constStack_eq_univ (k := k) (deg := deg)
    (domain := domain) (δ := δ) hdeg1 hw1
  -- apply the residual at the constant stack
  obtain ⟨B, hBdeg, hBeval⟩ := hres hk (constStack w k)
    (by
      rw [prob_constStack_eq_one (k := k) (deg := deg) (domain := domain) (δ := δ)
        hdeg1 hw1]
      exact hsmall)
    hJ hsqrt P
    (by
      intro z hz
      constructor
      · by_cases hzz : z = z₀ <;> simp [hP, hzz, hdeg1, hdeg2]
      · rw [fold_constStack]
        by_cases hzz : z = z₀
        · simp only [hP, hzz, if_pos rfl]
          exact hw2
        · simp only [hP, if_neg hzz]
          exact hw1)
  -- pin each coefficient polynomial on the parameters away from `z₀`
  have hpin : ∀ j < deg, B j = Polynomial.C (c₁.coeff j) := by
    intro j hj
    have hvan : ∀ z ∈ (Finset.univ : Finset F).erase z₀,
        (B j - Polynomial.C (c₁.coeff j)).eval z = 0 := by
      intro z hz
      obtain ⟨hzne, _⟩ := Finset.mem_erase.mp hz
      have hzgood : z ∈ RS_goodCoeffsCurve (k := k) (deg := deg) (domain := domain)
          (constStack w k) δ := by
        rw [hgood]
        exact Finset.mem_univ z
      have h := hBeval z hzgood j hj
      rw [hP] at h
      simp only [if_neg hzne] at h
      rw [Polynomial.eval_sub, Polynomial.eval_C, ← h]
      ring
    have hdegB : (B j - Polynomial.C (c₁.coeff j)).natDegree
        < ((Finset.univ : Finset F).erase z₀).card := by
      have h1 : (B j - Polynomial.C (c₁.coeff j)).natDegree ≤ (B j).natDegree := by
        calc (B j - Polynomial.C (c₁.coeff j)).natDegree
            ≤ max (B j).natDegree (Polynomial.C (c₁.coeff j)).natDegree :=
              Polynomial.natDegree_sub_le _ _
          _ = (B j).natDegree := by rw [Polynomial.natDegree_C]; omega
      have h2 : (B j).natDegree < k + 1 := hBdeg j hj
      have h3 : ((Finset.univ : Finset F).erase z₀).card = Fintype.card F - 1 := by
        rw [Finset.card_erase_of_mem (Finset.mem_univ z₀), Finset.card_univ]
      omega
    have hzero := Polynomial.eq_zero_of_natDegree_lt_card_of_eval_eq_zero'
      (B j - Polynomial.C (c₁.coeff j)) _ hvan hdegB
    have := sub_eq_zero.mp hzero
    exact this
  -- read the pinned family at `z₀`, where the decode is `c₂`
  have hcontra : c₂ = c₁ := by
    apply Polynomial.ext
    intro j
    by_cases hj : j < deg
    · have hz₀good : z₀ ∈ RS_goodCoeffsCurve (k := k) (deg := deg) (domain := domain)
          (constStack w k) δ := by
        rw [hgood]
        exact Finset.mem_univ z₀
      have h := hBeval z₀ hz₀good j hj
      rw [hP] at h
      simp only [if_pos rfl] at h
      rw [h, hpin j hj, Polynomial.eval_C]
    · push_neg at hj
      rw [Polynomial.coeff_eq_zero_of_natDegree_lt (lt_of_lt_of_le hdeg2 hj),
        Polynomial.coeff_eq_zero_of_natDegree_lt (lt_of_lt_of_le hdeg1 hj)]
  exact hc12 hcontra.symm

/-- **Finding F14, canonical form**: the uniqueness demand of
`StrictCanonicalCoeffPolysResidual` falls to the same data — two valid decodings of the
constant fold disagree at `z₀`, so no canonical family exists. -/
theorem not_strictCanonicalCoeffPolysResidual_of_attack_data {k deg : ℕ}
    {domain : ι ↪ F} {δ : ℝ≥0}
    {c₁ c₂ : Polynomial F} (hc12 : c₁ ≠ c₂)
    (hdeg1 : c₁.natDegree < deg) (hdeg2 : c₂.natDegree < deg)
    {w : ι → F}
    (hw1 : (δᵣ(w, fun x => c₁.eval (domain x)) : ℝ≥0∞) ≤ (δ : ℝ≥0∞))
    (hw2 : (δᵣ(w, fun x => c₂.eval (domain x)) : ℝ≥0∞) ≤ (δ : ℝ≥0∞))
    (hk : 0 < k)
    (hsmall : ((k : ℝ≥0∞) * (errorBound δ deg domain : ℝ≥0∞)) < 1)
    (hJ : (1 - (LinearCode.rate (ReedSolomon.code domain deg) : ℝ≥0)) / 2 < δ)
    (hsqrt : δ < 1 - ReedSolomon.sqrtRate deg domain)
    (hF : k + 2 ≤ Fintype.card F) :
    ¬ StrictCanonicalCoeffPolysResidual (k := k) (deg := deg) (domain := domain)
      (δ := δ) := by
  classical
  intro hres
  obtain ⟨z₀⟩ : Nonempty F := by
    have : 0 < Fintype.card F := by omega
    exact Fintype.card_pos_iff.mp this
  have hgood := goodCoeffsCurve_constStack_eq_univ (k := k) (deg := deg)
    (domain := domain) (δ := δ) hdeg1 hw1
  obtain ⟨P₀, _, huniq⟩ := hres hk (constStack w k)
    (by
      rw [prob_constStack_eq_one (k := k) (deg := deg) (domain := domain) (δ := δ)
        hdeg1 hw1]
      exact hsmall)
    hJ hsqrt
  have hz₀good : z₀ ∈ RS_goodCoeffsCurve (k := k) (deg := deg) (domain := domain)
      (constStack w k) δ := by
    rw [hgood]
    exact Finset.mem_univ z₀
  -- two valid decoded families that disagree at `z₀`
  have hdec1 : ∀ z ∈ RS_goodCoeffsCurve (k := k) (deg := deg) (domain := domain)
      (constStack w k) δ,
      (c₁.natDegree < deg ∧
        δᵣ(∑ t : Fin (k + 1), (z ^ (t : ℕ)) • constStack w k t,
          (fun x => c₁.eval (domain x))) ≤ δ) := by
    intro z _
    refine ⟨hdeg1, ?_⟩
    rw [fold_constStack]
    exact hw1
  have hdec2 : ∀ z ∈ RS_goodCoeffsCurve (k := k) (deg := deg) (domain := domain)
      (constStack w k) δ,
      (c₂.natDegree < deg ∧
        δᵣ(∑ t : Fin (k + 1), (z ^ (t : ℕ)) • constStack w k t,
          (fun x => c₂.eval (domain x))) ≤ δ) := by
    intro z _
    refine ⟨hdeg2, ?_⟩
    rw [fold_constStack]
    exact hw2
  have h1 := huniq (fun _ => c₁) (fun z hz => by
    simpa using hdec1 z hz) z₀ hz₀good
  have h2 := huniq (fun _ => c₂) (fun z hz => by
    simpa using hdec2 z hz) z₀ hz₀good
  exact hc12 (h1.symm.trans h2)

end ProximityGap

/-! ## Axiom audit — every declaration must rest only on
`[propext, Classical.choice, Quot.sound]`, with no `sorry`/`admit`/`axiom`/`native_decide`. -/
#print axioms ProximityGap.fold_constStack
#print axioms ProximityGap.goodCoeffsCurve_constStack_eq_univ
#print axioms ProximityGap.prob_constStack_eq_one
#print axioms ProximityGap.not_strictCoeffPolysResidual_of_attack_data
#print axioms ProximityGap.not_strictCanonicalCoeffPolysResidual_of_attack_data

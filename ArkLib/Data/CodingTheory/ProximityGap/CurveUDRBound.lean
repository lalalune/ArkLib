/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.CurveUDRBadCount
import ArkLib.Data.CodingTheory.ProximityGap.MCAUDRBound

/-!
# Curve-UDR stage 3: the Reed–Solomon curve MCA bound at every arity (issues #302/#301/#304)

The completion of the curve unique-decoding-regime arc (plan: issue #302 comment `4668760311`;
stages 1–2: `CurveUDRCoefficients`, `CurveUDRBadCount`):

* `epsMCACurve_le_of_badCount_le` — the curve analogue of `epsMCA_le_of_badCount_le`: a
  uniform per-stack bad-scalar bound gives the `ℓ/|F|` curve-MCA bound.
* `epsMCACurve_rs_udr_le` — **the headline**: for the Reed–Solomon code of degree `k` and ANY
  arity `L ≥ 2`, in the curve unique-decoding regime `(L+1)·(n−t) < n−k+1`
  (`t = ⌈(1−δ)n⌉`), the `L`-ary curve mutual-correlated-agreement error is at most
  `(L−1)·L·(n−t)/|F|` — the per-stack witness extraction feeding the stage-2 count.

Together with the proven seam `hasMutualCorrAgreement_genRSC_of_epsMCACurve_le`
(`Whir/MCACurveSeam.lean`) this discharges WHIR Corollary 4.11 (the unique-decoding branch) at
every folding arity, in the curve-UD radius — generalizing the landed pair case
(`mca_rsc_pair_holds`). The Johnson-radius branch remains with the GS/Hensel program.
Axiom-clean.
-/

open Finset ProximityGap ProximityGap.UDRwire
open scoped NNReal ENNReal ProbabilityTheory

namespace ArkLib.ProximityGap.CurveUDR

variable {F : Type} [Field F] [Fintype F] [DecidableEq F]
variable {ι : Type} [Fintype ι] [DecidableEq ι] [Nonempty ι]

open Classical in
/-- Curve analogue of `epsMCA_le_of_badCount_le`: a uniform per-stack bad-scalar bound gives the
`ℓ/|F|` curve-MCA bound. -/
theorem epsMCACurve_le_of_badCount_le
    (C : Set (ι → F)) (L : ℕ) (δ : ℝ≥0) (ℓ : ℕ)
    (h : ∀ u : Code.WordStack F (Fin L) ι,
      (Finset.filter (fun γ : F => mcaEventCurve C δ u γ) Finset.univ).card ≤ ℓ) :
    epsMCACurve (F := F) (A := F) C L δ ≤ (ℓ : ℝ≥0∞) / (Fintype.card F : ℝ≥0∞) := by
  unfold epsMCACurve
  refine iSup_le (fun u => ?_)
  rw [prob_uniform_eq_card_filter_div_card]
  simp only [ENNReal.coe_natCast]
  gcongr
  exact_mod_cast h u

open Classical in
/-- **Curve-UDR stage 3: the Reed–Solomon curve MCA bound in the curve unique-decoding regime.**
For the Reed–Solomon code of degree `k` and any arity `L ≥ 2`, in the regime
`(L+1)·(n − ⌈(1−δ)n⌉) < n − k + 1`, the `L`-ary curve mutual-correlated-agreement error is at
most `(L−1)·L·(n − ⌈(1−δ)n⌉) / |F|`. -/
theorem epsMCACurve_rs_udr_le (α : ι ↪ F) (k : ℕ) [NeZero k] (hk : k ≤ Fintype.card ι)
    (L : ℕ) (hL : 2 ≤ L) (δ : ℝ≥0)
    (htn : ⌈(1 - δ) * (Fintype.card ι : ℝ≥0)⌉₊ < Fintype.card ι)
    (hreg : (L + 1) * (Fintype.card ι - ⌈(1 - δ) * (Fintype.card ι : ℝ≥0)⌉₊)
      < Fintype.card ι - k + 1) :
    epsMCACurve (F := F) (A := F) (ReedSolomon.code α k : Set (ι → F)) L δ
      ≤ (((L - 1) * (L * (Fintype.card ι - ⌈(1 - δ) * (Fintype.card ι : ℝ≥0)⌉₊)) : ℕ) : ℝ≥0∞)
        / (Fintype.card F : ℝ≥0∞) := by
  set t : ℕ := ⌈(1 - δ) * (Fintype.card ι : ℝ≥0)⌉₊ with htdef
  have hmd := rs_min_dist α k hk
  refine epsMCACurve_le_of_badCount_le _ L δ _ (fun u => ?_)
  -- witness extraction from the curve MCA event
  set G : Finset F := Finset.univ.filter
    (fun γ : F => mcaEventCurve (ReedSolomon.code α k : Set (ι → F)) δ u γ) with hGdef
  set Sf : F → Finset ι := fun γ =>
    if h : mcaEventCurve (ReedSolomon.code α k : Set (ι → F)) δ u γ
      then h.choose else ∅ with hSdef
  set wf : F → ι → F := fun γ =>
    if h : mcaEventCurve (ReedSolomon.code α k : Set (ι → F)) δ u γ
      then (h.choose_spec.2.1).choose else 0 with hwdef
  refine curveBadCount_udr_le (ReedSolomon.code α k) L hL u (Fintype.card ι - k + 1) t
    htn hmd hreg G Sf wf ?_ ?_ ?_ ?_
  · intro γ hγ
    rw [hGdef, mem_filter] at hγ
    have h := hγ.2
    simp only [hSdef, dif_pos h]
    rw [htdef]
    exact Nat.ceil_le.mpr (by exact_mod_cast h.choose_spec.1)
  · intro γ hγ
    rw [hGdef, mem_filter] at hγ
    have h := hγ.2
    simp only [hwdef, dif_pos h]
    exact (h.choose_spec.2.1).choose_spec.1
  · intro γ hγ i hi
    rw [hGdef, mem_filter] at hγ
    have h := hγ.2
    simp only [hwdef, dif_pos h]
    simp only [hSdef, dif_pos h] at hi
    have := (h.choose_spec.2.1).choose_spec.2 i hi
    rw [this]
    exact Finset.sum_congr rfl (fun j _ => by rw [smul_eq_mul])
  · intro γ hγ
    rw [hGdef, mem_filter] at hγ
    have h := hγ.2
    simp only [hSdef, dif_pos h]
    exact h.choose_spec.2.2

/-- **Full-agreement edge case.** When every witness set is everything (`t = n`), at most
`L − 1` scalars can be bad: `L` of them would interpolate a joint codeword stack agreeing
everywhere, contradicting the no-joint-agreement clause. -/
theorem curveBadCount_full_le (C : Submodule F (ι → F)) (L : ℕ) (hL : 2 ≤ L)
    (u : Fin L → ι → F)
    (G : Finset F) (S : F → Finset ι) (w : F → ι → F)
    (hSt : ∀ γ ∈ G, S γ = Finset.univ)
    (hwC : ∀ γ ∈ G, w γ ∈ C)
    (hwS : ∀ γ ∈ G, ∀ i ∈ S γ, w γ i = ∑ k : Fin L, γ ^ (k : ℕ) * u k i)
    (hno : ∀ γ ∈ G, ¬ ProximityGap.stackJointAgreesOn (C : Set (ι → F)) (S γ) u) :
    G.card ≤ L - 1 := by
  classical
  by_contra hcon
  push Not at hcon
  have hG : L ≤ G.card := by omega
  obtain ⟨nodes, hsub, hnodes⟩ := Finset.exists_subset_card_eq hG
  obtain ⟨c, hcC, hcAgree⟩ := exists_curve_coeffs C L nodes hnodes w
    (fun γ hγ => hwC γ (hsub hγ))
  -- every coordinate is in every witness set, so the coefficients are the data rows everywhere
  have hcAll : ∀ (i : ι) (k : Fin L), c k i = u k i := by
    intro i k
    refine hcAgree i (fun k => u k i) (fun γ hγ => ?_) k
    have := hwS γ (hsub hγ) i (by rw [hSt γ (hsub hγ)]; exact Finset.mem_univ i)
    exact this
  -- hence the data stack is a joint codeword stack — contradiction at any bad scalar
  have hGne : G.Nonempty := by
    rw [← Finset.card_pos]; omega
  obtain ⟨γ, hγ⟩ := hGne
  refine hno γ hγ ⟨c, hcC, fun i _ k => hcAll i k⟩


end ArkLib.ProximityGap.CurveUDR

#print axioms ArkLib.ProximityGap.CurveUDR.epsMCACurve_le_of_badCount_le
#print axioms ArkLib.ProximityGap.CurveUDR.epsMCACurve_rs_udr_le
#print axioms ArkLib.ProximityGap.CurveUDR.curveBadCount_full_le

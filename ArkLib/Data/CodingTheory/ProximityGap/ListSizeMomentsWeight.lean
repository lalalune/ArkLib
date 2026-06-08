/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.ListSizeMoments
import Mathlib.Logic.Equiv.Fintype

/-!
# Direction A, completed: the pair-ball count `N(v,r)` depends only on `wt(v)`

This finishes the weight-symmetry of the moment method (Issue #232, direction A). Over a field, the
pair-ball count `N(v,r) = #{g : d(0,g) ≤ r ∧ d(v,g) ≤ r}` is invariant under the full **monomial
group** acting on `v`: coordinate permutations (`pairBall_perm`, in `ListSizeMoments`) and
per-coordinate nonzero scalings (`pairBall_smul_diag`, here). Since any two vectors of the same
Hamming weight are related by a monomial map, `N(v,r)` depends **only on `wt(v)`**
(`pairBall_weight`).

Consequently the exact second moment `Σ_f |Λ(C,r,f)|² = |C| · Σ_{v∈C} N(v,r)`
(`ListMoments.second_moment_linear`) is governed entirely by the **weight enumerator** of `C`: two
linear codes with the same weight distribution have the same second moment
(`second_moment_eq_of_weightEnum`). For an MDS / Reed–Solomon code the weight enumerator is a known
closed form, so this pins the second moment exactly — the rigorous endpoint of direction A's
reduction (the remaining gap to the prize is the average-`f`→worst-`f` step, which is genuinely open).

All `sorry`-free, axiom-clean.
-/

namespace ArkLib.CodingTheory.ListMoments

open Finset

variable {ι : Type*} [Fintype ι] [DecidableEq ι]
variable {F : Type*} [Fintype F] [DecidableEq F] [Field F]

/-- `hammingDist 0 v` is the size of the support of `v`. -/
lemma hammingDist_zero_eq_supp (v : ι → F) :
    hammingDist (0 : ι → F) v = (Finset.univ.filter (fun i => v i ≠ 0)).card := by
  unfold hammingDist
  congr 1
  ext i
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, Pi.zero_apply, ne_eq, eq_comm]

/-- **Hamming distance is invariant under per-coordinate nonzero scaling.** -/
lemma hammingDist_dmul (d : ι → F) (hd : ∀ i, d i ≠ 0) (a b : ι → F) :
    hammingDist (fun i => d i * a i) (fun i => d i * b i) = hammingDist a b := by
  unfold hammingDist
  congr 1
  ext i
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, ne_eq]
  rw [mul_eq_mul_left_iff, or_iff_left (hd i)]

/-- **Diagonal-scaling invariance of `N`.** `N(v, r) = N(d ⊙ v, r)` for any per-coordinate nonzero
scaling `d`. -/
lemma pairBall_smul_diag (d : ι → F) (hd : ∀ i, d i ≠ 0) (v : ι → F) (r : ℕ) :
    (Finset.univ.filter (fun g => hammingDist (0 : ι → F) g ≤ r ∧ hammingDist v g ≤ r)).card
      = (Finset.univ.filter
          (fun g => hammingDist (0 : ι → F) g ≤ r ∧ hammingDist (fun i => d i * v i) g ≤ r)).card := by
  refine Finset.card_nbij' (fun g => fun i => d i * g i) (fun h => fun i => (d i)⁻¹ * h i) ?_ ?_ ?_ ?_
  · intro g hg
    simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_univ, true_and] at hg ⊢
    obtain ⟨h1, h2⟩ := hg
    refine ⟨?_, ?_⟩
    · have key := hammingDist_dmul d hd 0 g
      have e0 : (fun i => d i * (0 : ι → F) i) = (0 : ι → F) := by funext i; simp
      rw [e0] at key
      rw [key]; exact h1
    · rw [hammingDist_dmul d hd v g]; exact h2
  · intro h hh
    simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_univ, true_and] at hh ⊢
    obtain ⟨h1, h2⟩ := hh
    refine ⟨?_, ?_⟩
    · have key := hammingDist_dmul (fun i => (d i)⁻¹) (fun i => inv_ne_zero (hd i)) 0 h
      have e0 : (fun i => (d i)⁻¹ * (0 : ι → F) i) = (0 : ι → F) := by funext i; simp
      rw [e0] at key
      rw [key]; exact h1
    · have key := hammingDist_dmul (fun i => (d i)⁻¹) (fun i => inv_ne_zero (hd i)) (fun i => d i * v i) h
      simp only [inv_mul_cancel_left₀ (hd _)] at key
      rw [key]; exact h2
  · intro g _; funext i; simp [inv_mul_cancel_left₀ (hd i)]
  · intro h _; funext i; simp [mul_inv_cancel_left₀ (hd i)]

/-- **Weight-only invariance of `N`.** If `v` and `v'` have the same Hamming weight, then
`N(v, r) = N(v', r)`. Proof: a coordinate permutation `σ` matching the supports (via
`Equiv.extendSubtype`) turns `v` into a vector with `v'`'s support, and a per-coordinate nonzero
scaling `d` then matches the values exactly, so `v' = d ⊙ (v ∘ σ)`; combine `pairBall_perm` and
`pairBall_smul_diag`. -/
lemma pairBall_weight (v v' : ι → F) (r : ℕ)
    (hw : hammingDist (0 : ι → F) v = hammingDist (0 : ι → F) v') :
    (Finset.univ.filter (fun g => hammingDist (0 : ι → F) g ≤ r ∧ hammingDist v g ≤ r)).card
      = (Finset.univ.filter
          (fun g => hammingDist (0 : ι → F) g ≤ r ∧ hammingDist v' g ≤ r)).card := by
  -- Supports of `v'` and `v` have equal cardinality.
  have hcard : Fintype.card {x // v' x ≠ 0} = Fintype.card {x // v x ≠ 0} := by
    rw [Fintype.card_subtype, Fintype.card_subtype, ← hammingDist_zero_eq_supp v',
      ← hammingDist_zero_eq_supp v, hw]
  -- A permutation matching `supp v'` onto `supp v`.
  let e : {x // v' x ≠ 0} ≃ {x // v x ≠ 0} := Fintype.equivOfCardEq hcard
  let σ : Equiv.Perm ι := e.extendSubtype
  have hmem : ∀ i, v' i ≠ 0 → v (σ i) ≠ 0 := fun i hi => Equiv.extendSubtype_mem e i hi
  have hnmem : ∀ i, v' i = 0 → v (σ i) = 0 := by
    intro i hi
    have : ¬ (v (σ i) ≠ 0) := Equiv.extendSubtype_not_mem e i (by simpa using hi)
    simpa using this
  -- The diagonal scaling matching values.
  let d : ι → F := fun i => if v' i ≠ 0 then v' i / v (σ i) else 1
  have hd : ∀ i, d i ≠ 0 := by
    intro i; simp only [d]; split_ifs with h
    · exact div_ne_zero h (hmem i h)
    · exact one_ne_zero
  have hv' : (fun i => d i * (v ∘ σ) i) = v' := by
    funext i; simp only [d, Function.comp_apply]
    split_ifs with h
    · rw [div_mul_cancel₀ _ (hmem i h)]
    · push_neg at h
      rw [hnmem i h, mul_zero, h]
  rw [pairBall_perm σ v r, pairBall_smul_diag d hd (v ∘ σ) r, hv']

end ArkLib.CodingTheory.ListMoments

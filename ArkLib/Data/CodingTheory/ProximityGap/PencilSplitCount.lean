/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.WindowPackingLaw

/-!
# The pencil split-count lemma (#371, the n/w-law's counting heart)

**At most `n/w` members of a polynomial pencil `f − λ·g` can each have `w` distinct
roots on an `n`-point domain**, provided `f` and `g` have no common domain root:
a domain point `x` roots the member `λ = f(x)/g(x)` and no other, so the root sets
of distinct split members are pairwise DISJOINT and `t·w ≤ n`.

This is the counting mechanism behind the window n/w-law: double-class fibers of
the alignment map are the D-split members of `span⟨Z_T, ℓ₀, ℓ₁⟩`
(`probe_nwlaw_stress.py`: the shared-`h` CRT consistency prunes the 3-dimensional
nets to pencils — tuned net adversaries cap at 1), and pencil fibers cap at `n/w`
by this lemma.  The `μ_w`-coset family is exactly the pencil
`⟨X^w − e₀, X^w − e₁⟩`, split members `X^w − t^w` — attaining the bound.
-/

open Finset Polynomial

namespace ProximityGap.WBPencil

variable {F : Type} [Field F] [Fintype F] [DecidableEq F]
variable {n : ℕ} [NeZero n]

open Classical in
/-- **The pencil split-count lemma**: if `f, g` share no root on the domain, the
scalars `λ` for which `f − λ·g` has at least `w ≥ 1` distinct domain roots number
at most `n/w`: their root sets are pairwise disjoint. -/
theorem pencil_split_count_le (dom : Fin n ↪ F) {w : ℕ} (hw : 1 ≤ w)
    (f g : F[X])
    (hno : ∀ i : Fin n, ¬ (f.eval (dom i) = 0 ∧ g.eval (dom i) = 0)) :
    (Finset.univ.filter (fun lam : F =>
        ∃ T : Finset (Fin n), w ≤ T.card ∧
          ∀ i ∈ T, (f - C lam * g).eval (dom i) = 0)).card * w ≤ n := by
  set Λ : Finset F := Finset.univ.filter (fun lam : F =>
      ∃ T : Finset (Fin n), w ≤ T.card ∧
        ∀ i ∈ T, (f - C lam * g).eval (dom i) = 0) with hΛ
  -- canonical root sets (the full domain root set of each member)
  set T : F → Finset (Fin n) := fun lam =>
    Finset.univ.filter (fun i => (f - C lam * g).eval (dom i) = 0) with hT
  have hTcard : ∀ lam ∈ Λ, w ≤ (T lam).card := by
    intro lam hlam
    rw [hΛ, Finset.mem_filter] at hlam
    obtain ⟨-, T₀, hT₀card, hT₀⟩ := hlam
    refine le_trans hT₀card (Finset.card_le_card ?_)
    intro i hi
    rw [hT, Finset.mem_filter]
    exact ⟨Finset.mem_univ _, hT₀ i hi⟩
  -- disjointness: a domain point roots at most one member
  have hdisj : ∀ lam ∈ Λ, ∀ lam' ∈ Λ, lam ≠ lam' → Disjoint (T lam) (T lam') := by
    intro lam _ lam' _ hne
    rw [Finset.disjoint_left]
    intro i hi hi'
    rw [hT, Finset.mem_filter] at hi hi'
    have h1 := hi.2
    have h2 := hi'.2
    rw [eval_sub, eval_mul, eval_C, sub_eq_zero] at h1 h2
    have hg : g.eval (dom i) ≠ 0 := by
      intro hg0
      exact hno i ⟨by rw [h1, hg0, mul_zero], hg0⟩
    have : lam * g.eval (dom i) = lam' * g.eval (dom i) := by rw [← h1, ← h2]
    exact hne (mul_right_cancel₀ hg this)
  -- the count
  have hbiU : (Λ.biUnion T).card = ∑ lam ∈ Λ, (T lam).card :=
    Finset.card_biUnion hdisj
  have hcap : (Λ.biUnion T).card ≤ n := by
    have := Finset.card_le_card (Finset.subset_univ (Λ.biUnion T))
    rw [Finset.card_univ, Fintype.card_fin] at this
    exact this
  calc Λ.card * w = ∑ _lam ∈ Λ, w := by
        rw [Finset.sum_const, smul_eq_mul, mul_comm]
    _ ≤ ∑ lam ∈ Λ, (T lam).card := Finset.sum_le_sum hTcard
    _ = (Λ.biUnion T).card := hbiU.symm
    _ ≤ n := hcap

end ProximityGap.WBPencil

-- Axiom audit (expected: propext, Classical.choice, Quot.sound only)
#print axioms ProximityGap.WBPencil.pencil_split_count_le

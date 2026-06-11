/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.Algebra.Polynomial.Eval.Degree
import Mathlib.Data.Finset.Basic

/-!
# Additive representations in a root-of-unity subgroup as polynomial roots (#357)

The sum-product bottleneck `N = #{(z₁,z₂,z₃)∈G³ : z₁+z₂ = z₃+1}` for the smooth subgroup
`G = {z : zⁿ = 1}` (the `n`-th roots of unity) factors through the **additive representation count**
`r(c) = #{z∈G : c−z∈G}`, via `N = Σ_{z₃∈G} r(z₃+1)` (`AddEnergyMulHomogeneous`/`AddEnergyNormalizedBound`
give `E(G) = |G|·N`). This file lands the **polynomial-method entry brick** of the Heath-Brown–Konyagin /
Stepanov route: each representation `z` (with `c−z∈G`) is a root of the explicit degree-`n` polynomial
`(C c − X)ⁿ − 1`, so

  `representationCount_le` : `r(c) = #{z∈G : c−z∈G} ≤ n`.

This is the bridge from the *additive* count to the *polynomial method* (root counting) — the form the
resultant/Stepanov argument consumes. The reusable content is `representationSet_subset_roots`: the
representation set sits inside `((C c − X)ⁿ − 1).roots`.

**Honest scope:** alone this yields only the per-`c` bound `r(c) ≤ n` (hence `E(G) ≤ |G|³`, the trivial
ceiling, consistent with `addEnergy_le_cube`). The sub-quadratic `N ≪ |G|^{3/2}` requires the
*resultant non-vanishing summed over `c`* (the HBK/Stepanov core, intersecting these roots with `G`'s
own defining polynomial `Xⁿ−1`) — the hard open input (dossier §27–28). This brick is its foundation,
not its closure; it does not pin `δ*`.

Axiom-clean (`propext`, `Classical.choice`, `Quot.sound`); no `sorry`.
-/

open Polynomial

namespace ArkLib.ProximityGap.SubgroupRepresentationRoots

variable {F : Type*} [Field F] [DecidableEq F]

/-- The explicit degree-`n` polynomial `(C c − X)ⁿ − 1` whose roots contain every additive
representation `z` (with `c − z` an `n`-th root of unity). -/
noncomputable def reprPoly (c : F) (n : ℕ) : F[X] := (Polynomial.C c - Polynomial.X) ^ n - 1

theorem reprPoly_natDegree (c : F) {n : ℕ} (hn : 0 < n) : (reprPoly c n).natDegree = n := by
  have hbase : (Polynomial.C c - Polynomial.X).degree = 1 := by
    rw [show Polynomial.C c - Polynomial.X = -(Polynomial.X - Polynomial.C c) by ring,
      Polynomial.degree_neg, Polynomial.degree_X_sub_C]
  have hpow : ((Polynomial.C c - Polynomial.X) ^ n).degree = (n : WithBot ℕ) := by
    rw [Polynomial.degree_pow, hbase]; simp
  have hlt : (1 : F[X]).degree < ((Polynomial.C c - Polynomial.X) ^ n).degree := by
    rw [hpow, Polynomial.degree_one]; exact_mod_cast hn
  have hdeg : (reprPoly c n).degree = (n : WithBot ℕ) := by
    rw [reprPoly, Polynomial.degree_sub_eq_left_of_degree_lt hlt, hpow]
  rw [Polynomial.natDegree, hdeg]; rfl

theorem reprPoly_ne_zero (c : F) {n : ℕ} (hn : 0 < n) : reprPoly c n ≠ 0 := by
  intro h
  have := reprPoly_natDegree c hn
  rw [h, Polynomial.natDegree_zero] at this
  omega

/-- **The representation set sits inside the roots of `(C c − X)ⁿ − 1`.** For a root-of-unity subgroup
`G = {z : zⁿ = 1}`, every `z ∈ G` with `c − z ∈ G` is a root of `reprPoly c n` (since `(c−z)ⁿ = 1`). -/
theorem representationSet_subset_roots (G : Finset F) {n : ℕ} (hn : 0 < n)
    (hGmem : ∀ z, z ∈ G ↔ z ^ n = 1) (c : F) :
    G.filter (fun z => c - z ∈ G) ⊆ (reprPoly c n).roots.toFinset := by
  classical
  intro z hz
  rw [Finset.mem_filter] at hz
  have hcz : (c - z) ^ n = 1 := (hGmem (c - z)).mp hz.2
  rw [Multiset.mem_toFinset, Polynomial.mem_roots (reprPoly_ne_zero c hn), Polynomial.IsRoot.def,
    reprPoly]
  simp only [Polynomial.eval_sub, Polynomial.eval_pow, Polynomial.eval_C, Polynomial.eval_X,
    Polynomial.eval_one]
  rw [hcz]; ring

/-- **Per-`c` additive representation bound: `r(c) ≤ n`.** The number of `z ∈ G` with `c − z ∈ G` is at
most `n`, since they are distinct roots of the nonzero degree-`n` polynomial `(C c − X)ⁿ − 1`. The
polynomial-method entry point of the HBK/Stepanov route. -/
theorem representationCount_le (G : Finset F) {n : ℕ} (hn : 0 < n)
    (hGmem : ∀ z, z ∈ G ↔ z ^ n = 1) (c : F) :
    (G.filter (fun z => c - z ∈ G)).card ≤ n := by
  classical
  calc (G.filter (fun z => c - z ∈ G)).card
      ≤ (reprPoly c n).roots.toFinset.card :=
        Finset.card_le_card (representationSet_subset_roots G hn hGmem c)
    _ ≤ Multiset.card (reprPoly c n).roots := Multiset.toFinset_card_le _
    _ ≤ (reprPoly c n).natDegree := Polynomial.card_roots' _
    _ = n := reprPoly_natDegree c hn

end ArkLib.ProximityGap.SubgroupRepresentationRoots

/-! ## Axiom audit — kernel-clean. -/
#print axioms ArkLib.ProximityGap.SubgroupRepresentationRoots.representationCount_le

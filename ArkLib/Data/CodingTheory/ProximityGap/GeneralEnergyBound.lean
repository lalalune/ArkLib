/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.SubgroupGaussSumMomentLadder
import Mathlib.Tactic

set_option linter.style.longLine false

/-!
# General-`r` additive-energy bound under the no-relation hypothesis (#389)

The linchpin generalizing the `r = 2` Sidon energy bound (`E ≤ 3|G|²`) to ALL moments. If `G` has no
nontrivial `r`-fold additive relation — i.e. every pair of `r`-tuples with equal sum is a permutation
of each other — then the `r`-fold additive energy is bounded by the multiset-matching count:

> `energyR_le_factorial` :  `E_r(G) ≤ r! · |G|^r`.

Combined with the moment ladder (`∑_b ‖η_b‖^{2r} = q·E_r`) and the worst-period bound, this gives the
square-root-cancellation bound on the worst period in the regime where the hypothesis holds — and the
cyclotomic resultant lift (`|Res(Φ_n, manyTerm)| ≤ (2r)^{φ(n)}`) supplies exactly this hypothesis for
`q > (2r)^{φ(n)}`. So this is the combinatorial half of proving the dyadic conjecture in the
resultant-pinned regime. `r! ≤ (2r−1)!! = ` Gaussian moment, so the bound is sub-Gaussian.

Axiom-clean (`propext`, `Classical.choice`, `Quot.sound`); no `sorry`.
-/

open Finset
open ArkLib.ProximityGap.SubgroupGaussSumMomentLadder

namespace ArkLib.ProximityGap.SubgroupGaussSumMomentLadder

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

omit [Fintype F] in
/-- **General-`r` additive-energy bound.** If every pair of `r`-tuples from `G` with equal sum is a
permutation of one another (no nontrivial `r`-fold additive relation), then `E_r(G) ≤ r!·|G|^r`. -/
theorem energyR_le_factorial (G : Finset F) (r : ℕ)
    (H : ∀ x ∈ Fintype.piFinset (fun _ : Fin r => G), ∀ z ∈ Fintype.piFinset (fun _ : Fin r => G),
          (∑ i, x i = ∑ i, z i) → ∃ σ : Equiv.Perm (Fin r), z = x ∘ σ) :
    energyR G r ≤ r.factorial * G.card ^ r := by
  classical
  set P : Finset (Fin r → F) := Fintype.piFinset (fun _ : Fin r => G) with hP
  -- each inner fiber {z : ∑z = ∑x} is contained in the (≤ r!) permutation-image of x
  have hfiber : ∀ x ∈ P, (P.filter (fun z => ∑ i, x i = ∑ i, z i)).card ≤ r.factorial := by
    intro x hx
    have hsub : P.filter (fun z => ∑ i, x i = ∑ i, z i)
        ⊆ Finset.univ.image (fun σ : Equiv.Perm (Fin r) => x ∘ σ) := by
      intro z hz
      rw [Finset.mem_filter] at hz
      obtain ⟨σ, hσ⟩ := H x hx z hz.1 hz.2
      exact Finset.mem_image.mpr ⟨σ, Finset.mem_univ σ, hσ.symm⟩
    calc (P.filter (fun z => ∑ i, x i = ∑ i, z i)).card
        ≤ (Finset.univ.image (fun σ : Equiv.Perm (Fin r) => x ∘ σ)).card :=
          Finset.card_le_card hsub
      _ ≤ (Finset.univ : Finset (Equiv.Perm (Fin r))).card := Finset.card_image_le
      _ = r.factorial := by rw [Finset.card_univ, Fintype.card_perm, Fintype.card_fin]
  -- sum the fiber bound over x
  rw [energyR]
  calc ∑ x ∈ P, ∑ z ∈ P, (if ∑ i, x i = ∑ i, z i then 1 else 0)
      = ∑ x ∈ P, (P.filter (fun z => ∑ i, x i = ∑ i, z i)).card := by
        refine Finset.sum_congr rfl (fun x _ => (Finset.card_filter _ _).symm)
    _ ≤ ∑ _x ∈ P, r.factorial := Finset.sum_le_sum hfiber
    _ = P.card * r.factorial := by rw [Finset.sum_const, smul_eq_mul]
    _ = r.factorial * G.card ^ r := by
        rw [hP, Fintype.card_piFinset]
        simp [mul_comm]

end ArkLib.ProximityGap.SubgroupGaussSumMomentLadder

/-! ## Axiom audit -/
#print axioms ArkLib.ProximityGap.SubgroupGaussSumMomentLadder.energyR_le_factorial

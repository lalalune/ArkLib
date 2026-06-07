/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.BCIKS20.P2Close
import ArkLib.Data.CodingTheory.ProximityGap.BCIKS20.P2Bijection

/-!
# BCIKS20 Appendix A.4 — `restrictedFaaDiBrunoSum` in partition form (toward `RestrictedFaaDiBrunoMatch`)

Applies the proven combinatorial reindex `innerSum_reindex` (`P2Bijection.lean`) to the actual
`restrictedFaaDiBrunoSum` (`P2Close.lean`): each guarded value-multiset inner sum becomes a sum over
partitions `λ` of `ab.2` with `≤ i` parts and no part `= t+1`.  This is the entropy-free half of
`RestrictedFaaDiBrunoMatch`; what remains is the algebraic identification of the partition-indexed
factors with the `(A.1)` recursion `βHensel_succ` (the `B_coeff` / Y-Hasse / `W`/`ξ`/`ζ` clearing).
-/

namespace BCIKS20.HenselNumerator

open scoped BigOperators
open Finset
open Polynomial Polynomial.Bivariate
open ArkLib.PowerSeriesComposition
open BCIKS20AppendixA
open ProximityPrize.BCIKS20.GammaGenuine

variable {F : Type} [Field F]
variable (H : F[X][Y]) [Fact (Irreducible H)] [Fact (0 < H.natDegree)]

/-- **`restrictedFaaDiBrunoSum` in partition form.**  Rewrites the restricted Faà-di-Bruno defect
sum, term by term, into a sum over the Y-degree `i`, the `X`-Taylor split `ab`, and the partitions
`λ ⊢ ab.2` with `|λ| ≤ i` and `(t+1) ∉ λ`:

  `restrictedFaaDiBrunoSum t
     = ∑_i ∑_{ab} lift((Δ_X^{ab.1} R)|_{x₀}).coeff i ·
         ∑_{λ ⊢ ab.2, |λ|≤i, (t+1)∉λ} (C(i,|λ|)·countPerms λ) · (α₀^{i-|λ|} · ∏_{l∈λ} coeff l βHenselAssembled)`,

where `α₀ = coeff 0 βHenselAssembled`.  Pure application of `innerSum_reindex`. -/
theorem restrictedFaaDiBrunoSum_eq_partitionForm (x₀ : F) (R : F[X][X][Y])
    (hHyp : ClaimA2.Hypotheses x₀ R H) (t : ℕ) :
    restrictedFaaDiBrunoSum H x₀ R hHyp t
      = ∑ i ∈ Finset.range ((Q x₀ R H).natDegree + 1),
          ∑ ab ∈ Finset.antidiagonal (t + 1),
            (liftToFunctionField (H := H)
                ((Bivariate.evalX (Polynomial.C x₀) (hasseDerivX ab.1 R)).coeff i))
            * ∑ lam ∈ (Finset.univ : Finset (Nat.Partition ab.2)).filter
                        (fun lam => lam.parts.card ≤ i ∧ (t + 1) ∉ lam.parts),
                ((i.choose lam.parts.card) * lam.parts.countPerms)
                  • ((PowerSeries.coeff 0 (βHenselAssembled H x₀ R hHyp)) ^ (i - lam.parts.card)
                      * (lam.parts.map (fun j =>
                          PowerSeries.coeff j (βHenselAssembled H x₀ R hHyp))).prod) := by
  unfold restrictedFaaDiBrunoSum
  refine Finset.sum_congr rfl (fun i _ => Finset.sum_congr rfl (fun ab _ => ?_))
  rw [innerSum_reindex i ab.2 (t + 1) (Nat.succ_pos t)
    (fun j => PowerSeries.coeff j (βHenselAssembled H x₀ R hHyp))]

/-- **The `βHensel_succ` guard is vacuous on valid `(i₁,λ)`.**  In the `(A.1)` recursion the
partition product is `partitionProd λ (fun l => if l < t+1 then βHensel l else 0)`.  For `λ ⊢ (t+1−i₁)`
with `(t+1) ∉ λ`, every part `l` satisfies `l ≤ t+1−i₁` and `l ≠ t+1`, hence `l < t+1`, so the guard
is always taken and the product equals the plain `partitionProd λ (βHensel …)`. -/
theorem partitionProd_guard_eq (x₀ : F) (R : F[X][X][Y]) (hHyp : ClaimA2.Hypotheses x₀ R H)
    (t i1 : ℕ) (lam : Nat.Partition (t + 1 - i1)) (hT : (t + 1) ∉ lam.parts) :
    partitionProd lam (fun l => if _h : l < t + 1 then βHensel H x₀ R hHyp l else 0)
      = partitionProd lam (βHensel H x₀ R hHyp) := by
  unfold partitionProd
  congr 1
  apply Multiset.map_congr rfl
  intro l hl
  obtain ⟨rest, hrest⟩ := Multiset.exists_cons_of_mem hl
  have hle : l ≤ t + 1 - i1 := by
    have hsum : lam.parts.sum = l + rest.sum := by rw [hrest, Multiset.sum_cons]
    have : l ≤ lam.parts.sum := by rw [hsum]; exact Nat.le_add_right l rest.sum
    rwa [lam.parts_sum] at this
  have hne : l ≠ t + 1 := fun h => hT (h ▸ hl)
  rw [dif_pos (show l < t + 1 by omega)]

end BCIKS20.HenselNumerator

-- Axiom audit.
#print axioms BCIKS20.HenselNumerator.restrictedFaaDiBrunoSum_eq_partitionForm
#print axioms BCIKS20.HenselNumerator.partitionProd_guard_eq

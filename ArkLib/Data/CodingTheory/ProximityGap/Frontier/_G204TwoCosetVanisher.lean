/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._G203TwoCosetTwistedGenerators

/-!
# G204: the two-coset Stepanov vanisher

This file rebuilds G103F's coefficient-kernel argument for G203's scalar-twisted generators.
For nonzero `α,β`, it constructs a nonzero polynomial of the same degree as G103F's auxiliary
and multiplicity at least `D` at every point satisfying `x^t=α`, `(x-c)^t=β`.

Issue #466.
-/

set_option autoImplicit false

open Polynomial Finset

namespace ArkLib.ProximityGap.Frontier.G204TwoCosetVanisher

open ArkLib.CodingTheory.HasseMultiplicityBridge
open ArkLib.CodingTheory.StepanovVanisher
open ArkLib.ProximityGap.Stepanov
open ArkLib.ProximityGap.Frontier.G103FSubgroupCollisionBound
open ArkLib.ProximityGap.Frontier.G203TwoCosetTwistedGenerators

variable {p : ℕ} [Fact p.Prime] [NeZero p]

noncomputable def twistedCondPoly {D B : ℕ} (t : ℕ) (c α β : ZMod p)
    (hα : α ≠ 0) (hβ : β ≠ 0) (n : ℕ) (i : Fin D × Fin B × Fin B) :
    (ZMod p)[X] :=
  (twistUnit α β hα hβ i : ZMod p) • condPoly t c n i

theorem twistedCondPoly_natDegree_le {D B : ℕ} (t : ℕ) (c α β : ZMod p)
    (hα : α ≠ 0) (hβ : β ≠ 0) (n : ℕ) (i : Fin D × Fin B × Fin B) :
    (twistedCondPoly t c α β hα hβ n i).natDegree ≤ (i.1 : ℕ) + n := by
  unfold twistedCondPoly
  exact (natDegree_smul_le _ _).trans (condPoly_natDegree_le t c n i)

theorem twisted_key_identity' {D B : ℕ} (t : ℕ) (c α β : ZMod p)
    (hα : α ≠ 0) (hβ : β ≠ 0) (n : ℕ) (i : Fin D × Fin B × Fin B) :
    X ^ n * (X - C c) ^ n * hasseDeriv n (twistedGen t c α β hα hβ i) =
      X ^ (t * (i.2.1 : ℕ)) * (X - C c) ^ (t * (i.2.2 : ℕ)) *
        twistedCondPoly t c α β hα hβ n i := by
  rw [twisted_key_identity]
  unfold twistedCondPoly
  rw [smul_eq_C_mul]
  ring

/-- **Two-coset Stepanov auxiliary.** -/
theorem exists_twoCoset_collision_vanisher {t B D : ℕ} (hD : 1 ≤ D) (hB : 1 ≤ B)
    (hDB : D * B ≤ t) (hcond : 2 * D ≤ B ^ 2) (hp : t * B ≤ p)
    {c α β : ZMod p} (hc : c ≠ 0) (hα : α ≠ 0) (hβ : β ≠ 0) :
    ∃ Ψ : (ZMod p)[X], Ψ ≠ 0
      ∧ Ψ.natDegree ≤ D - 1 + t * (B - 1) + t * (B - 1)
      ∧ ∀ x : ZMod p, x ^ t = α → (x - c) ^ t = β →
          D ≤ Ψ.rootMultiplicity x := by
  classical
  have hli := twistedGen_linearIndependent (p := p) (D := D) (B := B)
    t hD hB hDB hp hc hα hβ
  set Φ : ((Fin D × Fin B × Fin B) → ZMod p)
      →ₗ[ZMod p] ((Fin D × Fin (2 * D - 1)) → ZMod p) :=
    LinearMap.pi fun nm =>
        (lcoeff (ZMod p) (nm.2 : ℕ)).comp
        (Fintype.linearCombination (ZMod p)
          (fun i => condPoly t c (nm.1 : ℕ) i)) with hΦ
  have hcard : Fintype.card (Fin D × Fin (2 * D - 1)) <
      Fintype.card (Fin D × Fin B × Fin B) := by
    simp only [Fintype.card_prod, Fintype.card_fin]
    have h1 : 2 * D - 1 < B ^ 2 := by omega
    calc
      D * (2 * D - 1) < D * B ^ 2 := mul_lt_mul_of_pos_left h1 (by omega)
      _ = D * (B * B) := by ring
  obtain ⟨lam, hne, hΦc⟩ := exists_nonzero_vanishing_combination
    (twistedGen t c α β hα hβ) hli Φ hcard
  set Ψ : (ZMod p)[X] := ∑ i, lam i • twistedGen t c α β hα hβ i with hΨ
  have hQzero : ∀ n : ℕ, n < D →
      (∑ i, lam i • condPoly t c n i) = 0 := by
    intro n hn
    set Q : (ZMod p)[X] :=
      ∑ i, lam i • condPoly t c n i with hQ
    have hQdeg : Q.natDegree ≤ D - 1 + (D - 1) := by
      rw [hQ]
      refine natDegree_sum_le_of_forall_le _ _ fun i _ => ?_
      exact (natDegree_smul_le _ _).trans
        ((condPoly_natDegree_le t c n i).trans (by have := i.1.isLt; omega))
    ext m
    rw [coeff_zero]
    rcases Nat.lt_or_ge m (2 * D - 1) with hm | hm
    · have hcomp := congrFun hΦc (⟨n, hn⟩, ⟨m, hm⟩)
      simp only [hΦ, LinearMap.pi_apply, LinearMap.comp_apply,
        Fintype.linearCombination_apply, lcoeff_apply, Pi.zero_apply] at hcomp
      rw [hQ]
      simpa using hcomp
    · exact coeff_eq_zero_of_natDegree_lt (hQdeg.trans_lt (by omega))
  refine ⟨Ψ, hne, ?_, ?_⟩
  · rw [hΨ]
    refine natDegree_sum_le_of_forall_le _ _ fun i _ => ?_
    exact (natDegree_smul_le _ _).trans
      (twistedGen_natDegree_le hD hB t c α β hα hβ i)
  · intro x hx hxc
    have ht1 : 1 ≤ t := (Nat.mul_le_mul hD hB).trans hDB
    have hx0 : x ≠ 0 := by
      intro h
      rw [h, zero_pow (by omega : t ≠ 0)] at hx
      exact hα hx.symm
    have hxc0 : x - c ≠ 0 := by
      intro h
      rw [h, zero_pow (by omega : t ≠ 0)] at hxc
      exact hβ hxc.symm
    refine rootMultiplicity_ge_of_hasseDeriv_vanish hne x D fun n hn => ?_
    have hpoly : X ^ n * (X - C c) ^ n * hasseDeriv n Ψ =
        ∑ i, C (lam i) *
          (X ^ (t * (i.2.1 : ℕ)) * (X - C c) ^ (t * (i.2.2 : ℕ)) *
            twistedCondPoly t c α β hα hβ n i) := by
      rw [hΨ, map_sum, Finset.mul_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [map_smul, smul_eq_C_mul]
      calc
        _ = C (lam i) * (X ^ n * (X - C c) ^ n *
            hasseDeriv n (twistedGen t c α β hα hβ i)) := by ring
        _ = _ := by rw [twisted_key_identity']
    have hev := congrArg (Polynomial.eval x) hpoly
    simp only [eval_mul, eval_pow, eval_sub, eval_X, eval_C, eval_finset_sum] at hev
    have hRHS : ∀ i : Fin D × Fin B × Fin B,
        lam i * (x ^ (t * (i.2.1 : ℕ)) * (x - c) ^ (t * (i.2.2 : ℕ)) *
          (twistedCondPoly t c α β hα hβ n i).eval x) =
        lam i * (condPoly t c n i).eval x := by
      intro i
      unfold twistedCondPoly
      rw [smul_eq_C_mul, eval_mul, eval_C]
      have hrel := twistUnit_mul_relation_powers_eq_one t hα hβ hx hxc i
      linear_combination (lam i * (condPoly t c n i).eval x) * hrel
    rw [Finset.sum_congr rfl fun i _ => hRHS i] at hev
    have hsum : (∑ i, lam i * (condPoly t c n i).eval x) = 0 := by
      calc
        _ = (∑ i, lam i • condPoly t c n i).eval x := by
          rw [eval_finset_sum]
          exact Finset.sum_congr rfl fun i _ => by rw [smul_eq_C_mul, eval_mul, eval_C]
        _ = 0 := by rw [hQzero n hn, eval_zero]
    rw [hsum] at hev
    rcases mul_eq_zero.mp hev with h | h
    · rcases mul_eq_zero.mp h with h' | h'
      · exact absurd h' (pow_ne_zero n hx0)
      · exact absurd h' (pow_ne_zero n hxc0)
    · exact h

#print axioms twistedCondPoly_natDegree_le
#print axioms twisted_key_identity'
#print axioms exists_twoCoset_collision_vanisher

end ArkLib.ProximityGap.Frontier.G204TwoCosetVanisher

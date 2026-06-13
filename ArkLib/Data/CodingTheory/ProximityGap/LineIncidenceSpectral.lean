/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import Mathlib.Algebra.Group.AddChar
import Mathlib.Algebra.BigOperators.Finprod
import Mathlib.LinearAlgebra.Basis.Defs
import Mathlib.Analysis.Fourier.FiniteAbelian.PontryaginDuality
import Mathlib.Tactic.Abel

/-!
# The spectral form of the line–ball incidence (#389): the line-sum collapse

The governing law of δ* is `mcaDeltaStar = sup{δ : max-far-line-incidence(δ) ≤ q·ε*}`, and the
incidence is `#{γ : s₀ + γ·s₁ ∈ S_w}` for an affine line in the syndrome space (`S_w` = the
low-weight-coset set). Fourier-expanding `1_{S_w}` turns this incidence into a character sum, and
the whole expansion **collapses onto the hyperplane `s₁^⊥`** because of the elementary identity
proved here:

> **`lineSum_collapse`** — for any additive character `ψ` of an `F`-module `V` and any `s₀, s₁`,
> `∑_{γ ∈ F} ψ(s₀ + γ·s₁) = ψ(s₀) · (if ψ vanishes on the line `F·s₁` then |F| else 0)`.

The summand `ψ(s₀+γ·s₁) = ψ(s₀)·χ(γ)` factors through the additive character `χ := ψ∘(·s₁)` of
`F`, and `∑_γ χ(γ) = |F|·[χ trivial]` (`AddChar.sum_eq_ite`). The character `χ` is trivial exactly
when `ψ` annihilates the direction `s₁` (`ψ ⊥ s₁`). Consequently, in the Fourier expansion of any
indicator, **only the `s₁^⊥` frequencies survive the γ-average** — the `a=0` term is the average
incidence `q·|S_w|/q^m`, and everything else is the spectral error supported on `s₁^⊥`. This is the
exact mechanism that reduces the prize residual to "beat Parseval on the `s₁^⊥` hyperplane"
(see `docs/kb/deltastar-...`); the trivial Parseval bound `|error| ≤ √(q·|S_w|)` is W4-weak in the
prize regime, so the surviving open core is precisely the worst-case incomplete character sum.

Axiom-clean; pure character theory, no field-size or regime hypotheses.
-/

open Finset

namespace ArkLib.ProximityGap.LineIncidenceSpectral

variable {F V R : Type*} [Field F] [Fintype F] [AddCommGroup V] [Module F V]
  [CommRing R] [IsDomain R]

/-- The additive character of `F` obtained by restricting `ψ` to the line through `s₁`:
`directionChar ψ s₁ γ = ψ (γ • s₁)`. Trivial iff `ψ` annihilates `F·s₁`. -/
def directionChar (ψ : AddChar V R) (s₁ : V) : AddChar F R :=
  ψ.compAddMonoidHom ((smulAddHom F V).flip s₁)

omit [Fintype F] [IsDomain R] in
@[simp] theorem directionChar_apply (ψ : AddChar V R) (s₁ : V) (γ : F) :
    directionChar ψ s₁ γ = ψ (γ • s₁) := by
  simp [directionChar]

/-- **The line-sum collapse.** Summing an additive character along an affine line `s₀ + γ·s₁`
collapses to `ψ(s₀)·|F|` when `ψ` is trivial on the direction `s₁`, and to `0` otherwise. -/
theorem lineSum_collapse (ψ : AddChar V R) (s₀ s₁ : V)
    [Decidable (directionChar (F := F) ψ s₁ = 0)] :
    (∑ γ : F, ψ (s₀ + γ • s₁))
      = ψ s₀ * (if directionChar (F := F) ψ s₁ = 0 then (Fintype.card F : R) else 0) := by
  have hfac : ∀ γ : F, ψ (s₀ + γ • s₁) = ψ s₀ * directionChar (F := F) ψ s₁ γ := by
    intro γ
    rw [directionChar_apply, ← AddChar.map_add_eq_mul]
  rw [Finset.sum_congr rfl (fun γ _ => hfac γ), ← Finset.mul_sum, AddChar.sum_eq_ite]

/-! ### The full spectral identity (over ℂ, via Pontryagin duality) -/

/-- **The line–ball incidence spectral identity.** For a finite `F`-module `V`, a finset `S ⊆ V`,
and the affine line `s₀ + γ·s₁`, the incidence count satisfies
`(#{γ : s₀+γ·s₁ ∈ S}) · |V| = |F| · Σ_{ψ ⊥ s₁} Σ_{s∈S} ψ(s₀−s)`,
the sum over additive characters `ψ` trivial on the direction `s₁`. The trivial character `ψ=0`
contributes the average `|F|·|S|`; the rest is the spectral error on `s₁^⊥`. -/
theorem lineIncidence_spectral {F V : Type*} [Field F] [Fintype F]
    [AddCommGroup V] [Fintype V] [DecidableEq V] [Module F V]
    (S : Finset V) (s₀ s₁ : V) :
    ((Finset.univ.filter (fun γ : F => s₀ + γ • s₁ ∈ S)).card : ℂ) * (Fintype.card V : ℂ)
      = (Fintype.card F : ℂ)
        * ∑ ψ : AddChar V ℂ,
            (if directionChar (F := F) ψ s₁ = 0 then ∑ s ∈ S, ψ (s₀ - s) else 0) := by
  classical
  have hA : ((Finset.univ.filter (fun γ : F => s₀ + γ • s₁ ∈ S)).card : ℂ)
        * (Fintype.card V : ℂ)
      = ∑ γ : F, ∑ s ∈ S, ∑ ψ : AddChar V ℂ, ψ ((s₀ + γ • s₁) - s) := by
    have inner : ∀ γ : F, (∑ s ∈ S, ∑ ψ : AddChar V ℂ, ψ ((s₀ + γ • s₁) - s))
        = if s₀ + γ • s₁ ∈ S then (Fintype.card V : ℂ) else 0 := by
      intro γ
      have e1 : ∀ s ∈ S, (∑ ψ : AddChar V ℂ, ψ ((s₀ + γ • s₁) - s))
          = if s₀ + γ • s₁ = s then (Fintype.card V : ℂ) else 0 := by
        intro s _; rw [AddChar.sum_apply_eq_ite]; simp only [sub_eq_zero]
      rw [Finset.sum_congr rfl e1]
      exact Finset.sum_ite_eq S (s₀ + γ • s₁) (fun _ => (Fintype.card V : ℂ))
    rw [eq_comm, Finset.sum_congr rfl (fun γ _ => inner γ), ← Finset.sum_filter,
      Finset.sum_const, nsmul_eq_mul, mul_comm]
  rw [hA]
  -- reorder the triple sum to ∑_ψ ∑_s ∑_γ
  have hreorder : (∑ γ : F, ∑ s ∈ S, ∑ ψ : AddChar V ℂ, ψ ((s₀ + γ • s₁) - s))
      = ∑ ψ : AddChar V ℂ, ∑ s ∈ S, ∑ γ : F, ψ ((s₀ + γ • s₁) - s) := by
    rw [Finset.sum_comm]
    rw [show (∑ s ∈ S, ∑ γ : F, ∑ ψ : AddChar V ℂ, ψ ((s₀ + γ • s₁) - s))
          = ∑ s ∈ S, ∑ ψ : AddChar V ℂ, ∑ γ : F, ψ ((s₀ + γ • s₁) - s)
        from Finset.sum_congr rfl (fun s _ => Finset.sum_comm)]
    rw [Finset.sum_comm]
  rw [hreorder, Finset.mul_sum]
  refine Finset.sum_congr rfl (fun ψ _ => ?_)
  have hcol : ∀ s ∈ S, (∑ γ : F, ψ ((s₀ + γ • s₁) - s))
      = ψ (s₀ - s) * (if directionChar (F := F) ψ s₁ = 0 then (Fintype.card F : ℂ) else 0) := by
    intro s _
    have h := lineSum_collapse (F := F) ψ (s₀ - s) s₁
    rw [← h]
    refine Finset.sum_congr rfl (fun γ _ => ?_)
    congr 1; abel
  rw [Finset.sum_congr rfl hcol]
  by_cases hd : directionChar (F := F) ψ s₁ = 0
  · simp only [hd, if_true]
    rw [← Finset.sum_mul, mul_comm]
  · simp only [hd, if_false, mul_zero, Finset.sum_const_zero, mul_zero]

end ArkLib.ProximityGap.LineIncidenceSpectral

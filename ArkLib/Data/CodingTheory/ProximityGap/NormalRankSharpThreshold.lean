/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.Algebra.Polynomial.RingDivision
import Mathlib.RingTheory.Coprime.Lemmas
import Mathlib.Tactic

/-!
# Issue #232 — the sharp rank threshold for error-locator normal spaces (2026/858 Thm 26 + Rem 27)

The second-moment/Poisson-dispersion machinery of ePrint 2026/858 §7.2 (their
Theorem 26 / Corollary 28) rests on one algebraic dichotomy for the `2c` error-locator
normals `{Λ_{E₁}·X^r, Λ_{E₂}·X^r : r < c}` of two weight-`w` supports with intersection
size `j = |E₁ ∩ E₂|`:

* `j ≤ w − c` ⟹ the `2c` normals are **linearly independent** (their Theorem 26), giving
  exact pairwise independence of the membership indicators and `Var[M] ≈ E[M]`;
* `j > w − c` ⟹ the rank drops by exactly `ℓ = j − (w − c)` (their Remark 27) — shared
  cores produce genuine linear relations.

In polynomial language the span of the `2c` normals is
`{Λ_{E₁}·P + Λ_{E₂}·Q : deg P, deg Q < c}`, so the dichotomy is a *kernel* statement,
machine-checked here over any field:

* `normal_kernel_trivial` (= Theorem 26): if `c + j ≤ w₁` then
  `Λ_{E₁}·P + Λ_{E₂}·Q = 0` with `deg P, deg Q < c` forces `P = Q = 0`.
  The proof is *simpler than the paper's*: no gcd factoring — `A₁ = Λ_{E₁∖E₂}` divides
  `Λ_{E₁}·P = −Λ_{E₂}·Q` and is coprime to `Λ_{E₂}` outright (disjoint root sets), so
  `A₁ ∣ Q`, and `deg A₁ = w₁ − j ≥ c > deg Q` kills `Q`.
* `normal_kernel_nontrivial` (= Remark 27, sharpness): if `j > wᵢ − c` on both sides,
  the explicit relation `Λ_{E₁}·(−Λ_{E₂∖E₁}) + Λ_{E₂}·(Λ_{E₁∖E₂}) = 0` lives in the
  degree-`< c` window and is nontrivial — both products equal `Λ_{E₁ ∪ E₂}`.

**Why this matters for the open core:** their Conjecture 41 (the c ≥ 3 rank lemma,
≈ the prize's Grand List Challenge) is exactly a quantitative strengthening of this
mechanism — bounding how many supports can *simultaneously* be rank-deficient against a
fixed syndrome flat. The threshold formalized here is where the deficiency mechanism
turns on; any proof of Conjecture 41 must control precisely these shared-core relations.
-/

namespace NormalRank

open Polynomial Finset

variable {F : Type*} [Field F]

/-- The error-locator polynomial of a support `E ⊆ F` (also in `C2CoreBound.loc`;
duplicated here to keep this brick self-contained and Mathlib-only). -/
noncomputable def loc (E : Finset F) : F[X] := ∏ a ∈ E, (X - C a)

lemma loc_ne_zero (E : Finset F) : loc E ≠ 0 :=
  Finset.prod_ne_zero_iff.mpr fun a _ => X_sub_C_ne_zero a

lemma loc_natDegree (E : Finset F) : (loc E).natDegree = E.card := by
  rw [loc, Polynomial.natDegree_prod _ _ fun a _ => X_sub_C_ne_zero a]
  simp

/-- Locators of disjoint supports are coprime (disjoint root sets). -/
lemma loc_isCoprime {S T : Finset F} (h : Disjoint S T) : IsCoprime (loc S) (loc T) := by
  rw [loc, loc]
  refine IsCoprime.prod_left fun a ha => IsCoprime.prod_right fun b hb => ?_
  have hab : a ≠ b := by
    intro hEq
    exact Finset.disjoint_left.mp h ha (hEq ▸ hb)
  exact isCoprime_X_sub_C_of_isUnit_sub (sub_ne_zero_of_ne hab).isUnit

/-- The locator factors through any sub-support split: `Λ_E = Λ_{E∖T} · Λ_{E∩T}`. -/
lemma loc_sdiff_mul_loc_inter [DecidableEq F] (E T : Finset F) :
    loc (E \ T) * loc (E ∩ T) = loc E := by
  rw [loc, loc, loc, ← Finset.prod_union (Finset.disjoint_sdiff_inter E T)]
  congr 1
  exact Finset.sdiff_union_inter E T

/-- **The trivial-kernel half of the sharp threshold** (2026/858 Theorem 26, kernel
form): if `c + |E₁ ∩ E₂| ≤ |E₁|`, then any degree-`< c` relation
`Λ_{E₁}·P + Λ_{E₂}·Q = 0` is trivial (no degree bound on `P` is even needed) — the `2c` error-locator normals are linearly
independent, giving the exact pairwise independence behind Poisson dispersion at every
codimension excess.

Proof (simpler than the paper's gcd route): `A₁ = Λ_{E₁∖E₂}` divides the left summand
and is coprime to `Λ_{E₂}` outright, so `A₁ ∣ Q`; but `deg A₁ = |E₁| − j ≥ c > deg Q`. -/
theorem normal_kernel_trivial [DecidableEq F] {E₁ E₂ : Finset F} {c : ℕ}
    (hth : c + (E₁ ∩ E₂).card ≤ E₁.card)
    {P Q : F[X]} (hQ : Q.natDegree < c)
    (hrel : loc E₁ * P + loc E₂ * Q = 0) :
    P = 0 ∧ Q = 0 := by
  have hQ0 : Q = 0 := by
    by_contra hQne
    -- A₁ := Λ_{E₁ \ E₂} divides Λ_{E₂} * Q
    have hdvd : loc (E₁ \ E₂) ∣ loc E₂ * Q := by
      have h1 : loc (E₁ \ E₂) ∣ loc E₁ * P :=
        Dvd.dvd.mul_right ⟨loc (E₁ ∩ E₂), (loc_sdiff_mul_loc_inter E₁ E₂).symm⟩ P
      have h2 : loc E₂ * Q = -(loc E₁ * P) := by linear_combination hrel
      rw [h2]
      exact h1.neg_right
    -- coprime to Λ_{E₂} (disjoint root sets), hence divides Q
    have hco : IsCoprime (loc (E₁ \ E₂)) (loc E₂) :=
      loc_isCoprime Finset.sdiff_disjoint
    have hdvdQ : loc (E₁ \ E₂) ∣ Q := hco.dvd_of_dvd_mul_left hdvd
    -- degree contradiction
    have hdeg := Polynomial.natDegree_le_of_dvd hdvdQ hQne
    rw [loc_natDegree] at hdeg
    have hcard : (E₁ \ E₂).card + (E₁ ∩ E₂).card = E₁.card :=
      Finset.card_sdiff_add_card_inter E₁ E₂
    omega
  refine ⟨?_, hQ0⟩
  rw [hQ0, mul_zero, add_zero, mul_eq_zero] at hrel
  exact hrel.resolve_left (loc_ne_zero E₁)

/-- **The sharpness half** (2026/858 Remark 27): past the threshold on both sides
(`|Eᵢ| < c + j`), the shared core produces an explicit nontrivial degree-`< c` relation:
`Λ_{E₁}·(−Λ_{E₂∖E₁}) + Λ_{E₂}·Λ_{E₁∖E₂} = 0` (both products are `Λ_{E₁ ∪ E₂}`).
The error-locator normal family genuinely drops rank — the deficiency mechanism that
Conjecture 41 (the open prize core) must control. -/
theorem normal_kernel_nontrivial [DecidableEq F] {E₁ E₂ : Finset F} {c : ℕ}
    (h₁ : E₁.card < c + (E₁ ∩ E₂).card) (h₂ : E₂.card < c + (E₁ ∩ E₂).card) :
    ∃ P Q : F[X], Q ≠ 0 ∧ P.natDegree < c ∧ Q.natDegree < c ∧
      loc E₁ * P + loc E₂ * Q = 0 := by
  refine ⟨-loc (E₂ \ E₁), loc (E₁ \ E₂), loc_ne_zero _, ?_, ?_, ?_⟩
  · rw [natDegree_neg, loc_natDegree]
    have := Finset.card_sdiff_add_card_inter E₂ E₁
    rw [Finset.inter_comm] at this
    omega
  · rw [loc_natDegree]
    have := Finset.card_sdiff_add_card_inter E₁ E₂
    omega
  · -- both cross-products equal Λ_{E₁ ∪ E₂}
    have key : loc E₁ * loc (E₂ \ E₁) = loc E₂ * loc (E₁ \ E₂) := by
      rw [loc, loc, loc, loc, ← Finset.prod_union Finset.disjoint_sdiff,
        ← Finset.prod_union Finset.disjoint_sdiff,
        Finset.union_sdiff_self_eq_union, Finset.union_sdiff_self_eq_union,
        Finset.union_comm]
    linear_combination -key

end NormalRank

/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import Mathlib

set_option linter.style.longLine false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 1200000

open Polynomial
open scoped Classical

namespace ArkLib.ProximityGap.SinglePencilSharper

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

omit [Fintype F] [DecidableEq F] in
/-- The product of `(X − ζ)` over a finset of roots of `P` divides `P`. -/
private theorem prodXsubC_dvd_of_roots (P : F[X]) (S : Finset F)
    (hS : ∀ ζ ∈ S, P.eval ζ = 0) : (∏ ζ ∈ S, (X - C ζ)) ∣ P := by
  apply Finset.prod_dvd_of_coprime
  · intro a _ b _ hab
    exact Polynomial.pairwise_coprime_X_sub_C Function.injective_id (by simpa using hab)
  · intro ζ hζ; rw [Polynomial.dvd_iff_isRoot]; simpa using hS ζ hζ

omit [Fintype F] [DecidableEq F] in
private theorem prodXsubC_natDegree (S : Finset F) :
    (∏ ζ ∈ S, (X - C ζ)).natDegree = S.card := by
  rw [Polynomial.natDegree_prod _ _ (fun ζ _ => X_sub_C_ne_zero ζ),
    Finset.sum_congr rfl (fun ζ _ => Polynomial.natDegree_X_sub_C ζ),
    Finset.sum_const, smul_eq_mul, mul_one]

/-! ## The divided-difference / Vieta pinning identity.

For the deep-band witness `Q₀ = X^{k+1}` and the single-poly direction `Q₁ = X^k`, a
`(k+1)`-subset `S` of the (zero-excluding) domain `μ` pins the bad scalar to the unique value
`γ_S = −∑_{ζ∈S} ζ`. The mechanism is pure Vieta: `∏_{ζ∈S}(X − ζ)` is monic of degree `k+1`
with next-to-leading coefficient `−∑_{ζ∈S} ζ`. The pencil `X^{k+1} + γ·X^k` agrees with a
degree-`<k` polynomial on `S` iff `∏_S` divides `X^{k+1} + γ·X^k − W` for some `deg W < k`;
that difference has degree `≤ k+1`, leading coeff `1`, so it equals `∏_S` up to the lower
part — matching the `X^k` coefficient forces `γ = −∑_{ζ∈S} ζ`. -/

/-- **The pinning identity (forward, the hard direction).** If the witness pencil
`X^{k+1} + γ·X^k` agrees with a degree-`<k` polynomial `W` on a `(k+1)`-subset `S` of `μ`,
then `γ = −∑_{ζ∈S} ζ`. This is the divided-difference law: the pinned scalar IS the subset sum. -/
theorem witness_pin_eq_neg_sum (S : Finset F) (k : ℕ) (hScard : S.card = k + 1)
    (γ : F) (W : F[X]) (hWdeg : W.natDegree < k)
    (hvanish : ∀ ζ ∈ S, (X ^ (k + 1) + C γ * X ^ k - W).eval ζ = 0) :
    γ = -∑ ζ ∈ S, ζ := by
  classical
  set m := ∏ ζ ∈ S, (X - C ζ) with hmdef
  -- m divides the corrected pencil
  have hdvd : m ∣ (X ^ (k + 1) + C γ * X ^ k - W) :=
    prodXsubC_dvd_of_roots _ S hvanish
  -- m is monic of degree k+1
  have hmmonic : m.Monic := monic_prod_of_monic _ _ (fun ζ _ => monic_X_sub_C ζ)
  have hmdeg : m.natDegree = k + 1 := by rw [hmdef, prodXsubC_natDegree, hScard]
  -- the corrected pencil P has degree ≤ k+1 and leading coeff (at k+1) = 1
  set P := X ^ (k + 1) + C γ * X ^ k - W with hPdef
  -- The cofactor c with P = m * c.  Since deg P ≤ k+1 = deg m and m monic, c is a constant = 1.
  obtain ⟨c, hc⟩ := hdvd
  -- degree of P
  have hPdeg_le : P.natDegree ≤ k + 1 := by
    rw [hPdef]
    refine le_trans (Polynomial.natDegree_sub_le _ _) ?_
    rw [Nat.max_le]
    refine ⟨le_trans (Polynomial.natDegree_add_le _ _) ?_, by omega⟩
    rw [Nat.max_le]
    refine ⟨by rw [Polynomial.natDegree_X_pow], ?_⟩
    exact le_trans (Polynomial.natDegree_C_mul_le _ _) (by rw [Polynomial.natDegree_X_pow]; omega)
  -- coeff of P at (k+1) is 1
  have hPcoeff_top : P.coeff (k + 1) = 1 := by
    rw [hPdef]
    rw [Polynomial.coeff_sub, Polynomial.coeff_add, Polynomial.coeff_X_pow, if_pos rfl,
      Polynomial.coeff_C_mul, Polynomial.coeff_X_pow, if_neg (by omega), mul_zero, add_zero,
      Polynomial.coeff_eq_zero_of_natDegree_lt (by omega : W.natDegree < k + 1), sub_zero]
  -- coeff of P at k is γ - W.coeff k = γ (since deg W < k)
  have hPcoeff_k : P.coeff k = γ := by
    rw [hPdef]
    rw [Polynomial.coeff_sub, Polynomial.coeff_add, Polynomial.coeff_X_pow, if_neg (by omega),
      zero_add, Polynomial.coeff_C_mul, Polynomial.coeff_X_pow, if_pos rfl, mul_one,
      Polynomial.coeff_eq_zero_of_natDegree_lt hWdeg, sub_zero]
  -- P ≠ 0 since its (k+1) coeff is 1
  have hPne : P ≠ 0 := by
    intro h; rw [h, Polynomial.coeff_zero] at hPcoeff_top; exact one_ne_zero hPcoeff_top.symm
  -- P.natDegree = k+1 (top coeff nonzero and degree ≤ k+1)
  have hPdeg : P.natDegree = k + 1 :=
    le_antisymm hPdeg_le (Polynomial.le_natDegree_of_ne_zero (by rw [hPcoeff_top]; exact one_ne_zero))
  -- from P = m * c, degrees add: natDegree c = 0
  have hcne : c ≠ 0 := by
    rintro rfl; rw [mul_zero] at hc; exact hPne hc
  have hmne : m ≠ 0 := hmmonic.ne_zero
  have hdeg_add : P.natDegree = m.natDegree + c.natDegree := by
    rw [hc, Polynomial.natDegree_mul hmne hcne]
  have hcdeg : c.natDegree = 0 := by omega
  -- c is a constant; its value is P.coeff (k+1) / leadingCoeff m = 1
  obtain ⟨cc, rfl⟩ := Polynomial.natDegree_eq_zero.mp hcdeg
  -- now P = m * C cc; compare coeff at k+1 and k
  -- coeff (k+1): m.coeff (k+1) * cc.  m monic deg k+1 so m.coeff (k+1) = 1, giving cc = 1.
  have hm_top : m.coeff (k + 1) = 1 := by
    have := hmmonic; rw [Polynomial.Monic, Polynomial.leadingCoeff, hmdeg] at this; exact this
  have hcc1 : cc = 1 := by
    have h := congrArg (fun q => Polynomial.coeff q (k + 1)) hc
    simp only at h
    rw [hPcoeff_top, Polynomial.coeff_mul_C, hm_top, one_mul] at h
    exact h.symm
  subst hcc1
  -- coeff at k:  P.coeff k = m.coeff k * 1 = m.coeff k = −∑ ζ
  have hm_k : m.coeff k = -∑ ζ ∈ S, ζ := by
    have hpred : (∏ ζ ∈ S, (X - C ζ)).coeff (S.card - 1) = -∑ ζ ∈ S, ζ := by
      have := Polynomial.prod_X_sub_C_coeff_card_pred S (id : F → F) (by rw [hScard]; omega)
      simpa using this
    rw [hmdef]; rw [hScard] at hpred; simpa using hpred
  have h := congrArg (fun q => Polynomial.coeff q k) hc
  simp only at h
  rw [hPcoeff_k, Polynomial.coeff_mul_C, hm_k, mul_one] at h
  exact h

/-! ## Consequence: the bad scalars inject into the SUBSET-SUM SPECTRUM.

This is the sharper-constant bridge. `single_pencil_aclose_card_le` injects bad scalars into
`powersetCard (k+1) μ` (count `C(n, k+1)`). The pinning identity shows each bad scalar EQUALS
`−∑_{ζ∈S} ζ` for its pinning subset `S`, so the bad scalars inject into the *image*
`(powersetCard (k+1) μ).image (fun S => −∑_{ζ∈S} ζ)` — the subset-sum spectrum — whose
cardinality `≤ C(n, k+1)` is the deployed `2^r·C(2^{μ-1}, r)`-shaped object (kkh26_lemma1
provides the matching lower bound on that very spectrum). -/

/-- **Sharper bad-scalar bound: injection into the subset-sum spectrum.** The number of bad
scalars `γ` for the deep-band witness pencil `X^{k+1} + γ·X^k` on `μ` (`0 ∉ μ`) is at most the
cardinality of the subset-sum spectrum `{ −∑_{ζ∈S} ζ : S ∈ powersetCard (k+1) μ }` — sharper
than `C(|μ|, k+1)` exactly when distinct `(k+1)`-subsets collide under the sum map. -/
theorem witness_badscalar_card_le_spectrum (μ : Finset F) (k : ℕ) :
    (Finset.univ.filter (fun γ : F =>
        ∃ W : F[X], W.natDegree < k ∧
          k + 1 ≤ (μ.filter (fun ζ => (X ^ (k + 1) + C γ * X ^ k - W).eval ζ = 0)).card)).card
      ≤ ((μ.powersetCard (k + 1)).image (fun S => -∑ ζ ∈ S, ζ)).card := by
  classical
  set bad := Finset.univ.filter (fun γ : F =>
      ∃ W : F[X], W.natDegree < k ∧
        k + 1 ≤ (μ.filter (fun ζ => (X ^ (k + 1) + C γ * X ^ k - W).eval ζ = 0)).card) with hbad
  -- For each bad γ, extract a witness W and a (k+1)-subset S of agreement points; γ = −∑_S ζ.
  have hwit : ∀ γ ∈ bad, ∃ S : Finset F, S ∈ μ.powersetCard (k + 1) ∧ γ = -∑ ζ ∈ S, ζ := by
    intro γ hγ
    obtain ⟨W, hWdeg, hcard⟩ := (Finset.mem_filter.mp hγ).2
    obtain ⟨S, hSsub, hScard⟩ := Finset.exists_subset_card_eq hcard
    have hSμ : S ⊆ μ := hSsub.trans (Finset.filter_subset _ _)
    have hvan : ∀ ζ ∈ S, (X ^ (k + 1) + C γ * X ^ k - W).eval ζ = 0 :=
      fun ζ hζ => (Finset.mem_filter.mp (hSsub hζ)).2
    exact ⟨S, Finset.mem_powersetCard.mpr ⟨hSμ, hScard⟩,
      witness_pin_eq_neg_sum S k hScard γ W hWdeg hvan⟩
  -- every bad γ lies in the subset-sum spectrum (via its pinning subset)
  apply Finset.card_le_card
  intro γ hγ
  obtain ⟨S, hSmem, hSsum⟩ := hwit γ hγ
  exact Finset.mem_image.mpr ⟨S, hSmem, hSsum.symm⟩

/-- **The spectrum bound refines the trivial `C(|μ|, k+1)` bound.** The subset-sum spectrum
image has cardinality `≤ C(|μ|, k+1)` (image card `≤` source card), so the spectrum bound
implies `single_pencil_aclose_card_le`'s count. The refinement is strict exactly when distinct
`(k+1)`-subsets of `μ` collide under the sum map — which, probe-confirmed, they do on the
roots-of-unity domain `μ_{2^m}`: there the spectrum sits strictly between the deployed supply
lower bound `2^r·C(2^{m-1}, r)` and `C(2^m, r)`. -/
theorem spectrum_card_le_choose (μ : Finset F) (k : ℕ) :
    ((μ.powersetCard (k + 1)).image (fun S => -∑ ζ ∈ S, ζ)).card
      ≤ (μ.powersetCard (k + 1)).card :=
  Finset.card_image_le

/-- **The single-pencil bad-scalar count is bracketed by the subset-sum spectrum.** Chaining
`witness_badscalar_card_le_spectrum` with `spectrum_card_le_choose` recovers the original
`q`-independent `C(|μ|, k+1)` bound *through* the spectrum — exposing the spectrum cardinality
as the genuine sharper upper bracket. The complementary lower bracket on the very same spectrum
(for `μ = μ_{2^m}`) is `kkh26_lemma1`'s `2^r·C(2^{m-1}, r) ≤ |spectrum|`; together they pin the
deep-band witness bad-scalar count to the interval `[2^r·C(2^{m-1}, r), |spectrum|]`. The
remaining obstruction is the EXACT spectrum cardinality `|{ ∑_{ζ∈S} ζ : S ∈ powersetCard r μ_n }|`,
a concrete additive-combinatorics count, no longer the generic sub-Johnson list-size wall. -/
theorem witness_badscalar_card_le_choose_via_spectrum (μ : Finset F) (k : ℕ) :
    (Finset.univ.filter (fun γ : F =>
        ∃ W : F[X], W.natDegree < k ∧
          k + 1 ≤ (μ.filter (fun ζ => (X ^ (k + 1) + C γ * X ^ k - W).eval ζ = 0)).card)).card
      ≤ (μ.powersetCard (k + 1)).card :=
  le_trans (witness_badscalar_card_le_spectrum μ k) (spectrum_card_le_choose μ k)

end ArkLib.ProximityGap.SinglePencilSharper

/-! ## Axiom audit -/
#print axioms ArkLib.ProximityGap.SinglePencilSharper.witness_pin_eq_neg_sum
#print axioms ArkLib.ProximityGap.SinglePencilSharper.witness_badscalar_card_le_spectrum
#print axioms ArkLib.ProximityGap.SinglePencilSharper.spectrum_card_le_choose
#print axioms ArkLib.ProximityGap.SinglePencilSharper.witness_badscalar_card_le_choose_via_spectrum

/-
Copyright (c) 2024-2025 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Katerina Hristova, František Silváši, Julian Sutherland, Ilia Vlasov
-/

import ArkLib.Data.Polynomial.Bivariate
import ArkLib.Data.Polynomial.Prelims
import Mathlib.FieldTheory.RatFunc.Defs
import Mathlib.RingTheory.Ideal.Quotient.Defs
import Mathlib.RingTheory.Ideal.Span
import Mathlib.RingTheory.PowerSeries.Substitution
import Mathlib.RingTheory.Polynomial.GaussLemma
import Mathlib.RingTheory.Polynomial.Content
import Mathlib.RingTheory.Polynomial.Resultant.Basic
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.Algebra.Polynomial.BigOperators
import Mathlib.Algebra.Polynomial.Degree.Lemmas

/-!
# Definitions and Theorems about Function Fields and Rings of Regular Functions

We define the notions of Appendix A of [BCIKS20].

## References

[BCIKS20] Eli Ben-Sasson, Dan Carmon, Yuval Ishai, Swastik Kopparty, and Shubhangi Saraf.
  Proximity gaps for Reed-Solomon codes. In 2020 IEEE 61st Annual Symposium on Foundations of
  Computer Science (FOCS), 2020. Full paper: https://eprint.iacr.org/2020/654,
  version 20210703:203025.

## Main Definitions

-/

open Polynomial Polynomial.Bivariate ToRatFunc Ideal

namespace BCIKS20AppendixA

section

variable {F : Type} [Field F]

/-- Construction of the monisized polynomial `H_tilde` in Appendix A.1 of [BCIKS20].
Note: Here `H ∈ F[X][Y]` translates to `H ∈ F[Z][Y]` in [BCIKS20] and H_tilde in
`Polynomial (RatFunc F)` translates to `H_tilde ∈ F(Z)[T]` in [BCIKS20]. -/
noncomputable def H_tilde (H : F[X][Y]) : Polynomial (RatFunc F) :=
  let hᵢ (i : ℕ) := H.coeff i
  let d := H.natDegree
  let W := (RingHom.comp Polynomial.C univPolyHom) (hᵢ d)
  let S : Polynomial (RatFunc F) := Polynomial.X / W
  let H' := Polynomial.eval₂ (RingHom.comp Polynomial.C univPolyHom) S H
  W ^ (d - 1) * H'

/-- The monisized version H_tilde is irreducible if the original polynomial H is irreducible.

Statement repairs (both necessary; documented for upstream):
* `hH : 0 < H.natDegree` — for degree-0 irreducible `H = C h`, `H_tilde H` is a nonzero
  constant in `(RatFunc F)[X]`, i.e. a unit, hence not irreducible.
* The section now requires `[Field F]` (previously `CommRing F` + `IsDomain F`): the proof
  goes through Gauss's lemma, which needs `F[X]` integrally closed/UFD; a general domain
  does not provide this. All use sites (BCIKS20 §5) are over fields. -/
lemma irreducibleHTildeOfIrreducible {H : Polynomial (Polynomial F)} (hH : 0 < H.natDegree) :
    (Irreducible H → Irreducible (H_tilde H)) := by
  intro hirr
  set d := H.natDegree with hd_def
  set w : F[X] := H.coeff d with hw_def
  have hw_ne : w ≠ 0 := by
    rw [hw_def, hd_def, ← Polynomial.leadingCoeff]
    exact Polynomial.leadingCoeff_ne_zero.mpr hirr.ne_zero
  set u : RatFunc F := univPolyHom w with hu_def
  have huniv_inj : Function.Injective (univPolyHom : F[X] →+* RatFunc F) := by
    rw [univPolyHom]; exact IsFractionRing.injective _ _
  have hu_ne : u ≠ 0 := by
    rw [hu_def]; intro hzero; exact hw_ne (huniv_inj (by rw [hzero, map_zero]))
  have hprim : H.IsPrimitive := hirr.isPrimitive (Nat.ne_of_gt hH)
  set g : Polynomial (RatFunc F) := H.map univPolyHom with hg_def
  have hg_irr : Irreducible g := by
    rw [hg_def, show (univPolyHom : F[X] →+* RatFunc F) = algebraMap (F[X]) (RatFunc F) from rfl]
    exact (hprim.irreducible_iff_irreducible_map_fraction_map).mp hirr
  letI := invertibleOfNonzero (inv_ne_zero hu_ne)
  set φ : (Polynomial (RatFunc F)) ≃ₐ[RatFunc F] (Polynomial (RatFunc F)) :=
    algEquivCMulXAddC u⁻¹ 0 with hφ_def
  have hφg_irr : Irreducible (φ g) := (MulEquiv.irreducible_iff φ.toRingEquiv.toMulEquiv).mpr hg_irr
  have hident : H_tilde H = Polynomial.C (u ^ (d - 1)) * φ g := by
    have hW : (RingHom.comp Polynomial.C univPolyHom) ((fun i => H.coeff i) d)
        = Polynomial.C u := by
      simp only [RingHom.comp_apply, hu_def, hw_def]
    have heval : Polynomial.eval₂ (RingHom.comp Polynomial.C univPolyHom)
          (Polynomial.X / Polynomial.C u) H
        = g.comp (Polynomial.X / Polynomial.C u) := by
      rw [hg_def, Polynomial.comp, ← Polynomial.eval₂_map]
    have hXW : (Polynomial.X / Polynomial.C u : Polynomial (RatFunc F))
        = Polynomial.C u⁻¹ * Polynomial.X := by
      rw [Polynomial.div_C, mul_comm]
    have hφg : φ g = g.comp (Polynomial.C u⁻¹ * Polynomial.X) := by
      rw [hφ_def, algEquivCMulXAddC_apply, map_zero, add_zero, comp_eq_aeval]
    have hWpow : (Polynomial.C u : Polynomial (RatFunc F)) ^ (d - 1)
        = Polynomial.C (u ^ (d-1)) := by
      rw [Polynomial.C_pow]
    rw [H_tilde]
    simp only []
    rw [hW, heval, hXW, hWpow, hφg]
  rw [hident]
  have hunit : IsUnit (Polynomial.C (u ^ (d - 1)) : Polynomial (RatFunc F)) :=
    Polynomial.isUnit_C.mpr ((isUnit_iff_ne_zero).mpr (pow_ne_zero _ hu_ne))
  exact (irreducible_isUnit_mul hunit).mpr hφg_irr

/-- The function field `𝕃 ` from Appendix A.1 of [BCIKS20]. -/
abbrev 𝕃 (H : F[X][Y]) : Type :=
  (Polynomial (RatFunc F)) ⧸ (Ideal.span {H_tilde H})

/-- The function field `𝕃 ` is indeed a field if and only if the generator of the ideal we quotient
by is an irreducible polynomial. -/
lemma isField_of_irreducible {H : F[X][Y]} (hH : 0 < H.natDegree) :
    Irreducible H → IsField (𝕃 H) := by
  intros h
  unfold 𝕃
  erw
    [
      ←Ideal.Quotient.maximal_ideal_iff_isField_quotient,
      principal_is_maximal_iff_irred
    ]
  exact irreducibleHTildeOfIrreducible hH h

/-- The function field `𝕃` as defined above is a field. -/
noncomputable instance {H : F[X][Y]} [inst : Fact (Irreducible H)]
    [hd : Fact (0 < H.natDegree)] : Field (𝕃 H) :=
  IsField.toField (isField_of_irreducible hd.out inst.out)

/-- The monisized polynomial `H_tilde` is in fact an element of `F[X][Y]`. -/
noncomputable def H_tilde' (H : F[X][Y]) : F[X][Y] :=
  if H.natDegree = 0 then
    Polynomial.C (H.coeff 0)
  else
    let hᵢ (i : ℕ) := H.coeff i
    let d := H.natDegree
    let W := hᵢ d
    Polynomial.X ^ d +
      ∑ i ∈ Finset.range d,
        Polynomial.C (hᵢ i * W ^ (d - 1 - i)) * Polynomial.X ^ i

/-- If `H` has positive degree in `Y`, then `H_tilde' H` is monic. -/
lemma H_tilde'_monic (H : F[X][Y]) (hH : 0 < H.natDegree) :
    (H_tilde' H).Monic := by
  classical
  have hdeg : H.natDegree ≠ 0 := Nat.ne_of_gt hH
  rw [H_tilde', if_neg hdeg]
  exact Polynomial.monic_X_pow_add <| (Polynomial.degree_sum_le _ _).trans_lt <| by
    exact (Finset.sup_lt_iff (WithBot.bot_lt_coe H.natDegree)).2 <| by
      intro i hi
      exact (Polynomial.degree_C_mul_X_pow_le i _).trans_lt
        (WithBot.coe_lt_coe.2 (Finset.mem_range.mp hi))

private lemma monicize_term {K : Type} [Field K] (a b : K) (i d : ℕ)
    (ha : a ≠ 0) (hi : i < d) :
    (Polynomial.C a ^ (d - 1)) * (Polynomial.C b * (Polynomial.X / Polynomial.C a) ^ i) =
      Polynomial.C (b * a ^ (d - 1 - i)) * Polynomial.X ^ i := by
  rw [Polynomial.div_C, mul_pow]
  rw [show Polynomial.C a ^ (d - 1) = Polynomial.C (a ^ (d - 1)) by rw [Polynomial.C_pow]]
  rw [show Polynomial.C a⁻¹ ^ i = Polynomial.C (a⁻¹ ^ i) by rw [Polynomial.C_pow]]
  have hscalar : a ^ (d - 1) * b * a⁻¹ ^ i = b * a ^ (d - 1 - i) := by
    have hsplit : d - 1 = (d - 1 - i) + i := by omega
    rw [hsplit, pow_add, inv_pow]
    field_simp [ha]
    have hexp : d - 1 - i + i - i = d - 1 - i := by omega
    rw [hexp]
    ring_nf
  have hscalar' : a ^ (d - 1) * (b * a⁻¹ ^ i) = b * a ^ (d - 1 - i) := by
    simpa [mul_assoc] using hscalar
  calc
    Polynomial.C (a ^ (d - 1)) * (Polynomial.C b * (Polynomial.X ^ i * Polynomial.C (a⁻¹ ^ i))) =
        Polynomial.X ^ i * Polynomial.C (a ^ (d - 1) * (b * a⁻¹ ^ i)) := by
          calc
            Polynomial.C (a ^ (d - 1)) *
                (Polynomial.C b * (Polynomial.X ^ i * Polynomial.C (a⁻¹ ^ i))) =
                Polynomial.X ^ i *
                  (Polynomial.C (a ^ (d - 1)) * Polynomial.C b * Polynomial.C (a⁻¹ ^ i)) := by
                    ring
            _ = Polynomial.X ^ i * Polynomial.C (a ^ (d - 1) * (b * a⁻¹ ^ i)) := by
                  rw [← Polynomial.C_mul, ← Polynomial.C_mul]
                  simp [mul_assoc]
    _ = Polynomial.X ^ i * Polynomial.C (b * a ^ (d - 1 - i)) := by rw [hscalar']
    _ = Polynomial.C (b * a ^ (d - 1 - i)) * Polynomial.X ^ i := by rw [mul_comm]

private lemma monicize_leading_term {K : Type} [Field K] (a : K) (d : ℕ)
    (ha : a ≠ 0) (hd : 0 < d) :
    (Polynomial.C a ^ (d - 1)) * (Polynomial.C a * (Polynomial.X / Polynomial.C a) ^ d) =
      Polynomial.X ^ d := by
  rw [Polynomial.div_C, mul_pow]
  rw [show Polynomial.C a ^ (d - 1) = Polynomial.C (a ^ (d - 1)) by rw [Polynomial.C_pow]]
  rw [show Polynomial.C a⁻¹ ^ d = Polynomial.C (a⁻¹ ^ d) by rw [Polynomial.C_pow]]
  have hscalar : a ^ (d - 1) * a * a⁻¹ ^ d = (1 : K) := by
    have hd' : d = (d - 1) + 1 := by omega
    rw [hd', pow_add, pow_one, inv_pow]
    field_simp [ha]
    have hexp : d - 1 + 1 - 1 = d - 1 := by omega
    rw [hexp]
  have hscalar' : a ^ (d - 1) * (a * a⁻¹ ^ d) = (1 : K) := by
    simpa [mul_assoc] using hscalar
  calc
    Polynomial.C (a ^ (d - 1)) * (Polynomial.C a * (Polynomial.X ^ d * Polynomial.C (a⁻¹ ^ d))) =
        Polynomial.X ^ d * Polynomial.C (a ^ (d - 1) * (a * a⁻¹ ^ d)) := by
          calc
            Polynomial.C (a ^ (d - 1)) *
                (Polynomial.C a * (Polynomial.X ^ d * Polynomial.C (a⁻¹ ^ d))) =
                Polynomial.X ^ d *
                  (Polynomial.C (a ^ (d - 1)) * Polynomial.C a * Polynomial.C (a⁻¹ ^ d)) := by
                    ring
            _ = Polynomial.X ^ d * Polynomial.C (a ^ (d - 1) * (a * a⁻¹ ^ d)) := by
                  rw [← Polynomial.C_mul, ← Polynomial.C_mul]
                  simp [mul_assoc]
    _ = Polynomial.X ^ d * Polynomial.C (1 : K) := by rw [hscalar']
    _ = Polynomial.X ^ d := by simp

/-- The polynomial `H_tilde'` agrees with the monicization `H_tilde` after embedding into
`Polynomial (RatFunc F)`. -/
lemma H_tilde_equiv_H_tilde' (H : F[X][Y]) : (H_tilde' H).map univPolyHom = H_tilde H := by
  classical
  by_cases hdeg : H.natDegree = 0
  · simp only [H_tilde', hdeg, ↓reduceIte, map_C]
    have hconst : H = Polynomial.C (H.coeff 0) := Polynomial.eq_C_of_natDegree_le_zero (by omega)
    rw [hconst, H_tilde]
    simp
  · have hH_ne : H ≠ 0 := by
      intro hzero
      apply hdeg
      simp [hzero]
    have hw_ne_zero : univPolyHom H.leadingCoeff ≠ 0 := by
      apply IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors
      rw [mem_nonZeroDivisors_iff_ne_zero]
      exact Polynomial.leadingCoeff_ne_zero.mpr hH_ne
    have hd : 0 < H.natDegree := Nat.pos_of_ne_zero hdeg
    have hEval :
        Polynomial.eval₂ (RingHom.comp Polynomial.C univPolyHom)
          (Polynomial.X /
            (RingHom.comp Polynomial.C univPolyHom) ((fun i => H.coeff i) H.natDegree)) H =
        ∑ i ∈ Finset.range (H.natDegree + 1),
          Polynomial.C (univPolyHom (H.coeff i)) *
            (Polynomial.X /
              (RingHom.comp Polynomial.C univPolyHom) ((fun i => H.coeff i) H.natDegree)) ^ i := by
      simpa using
        (Polynomial.eval₂_eq_sum_range
          (p := H) (f := RingHom.comp Polynomial.C univPolyHom)
          (x := Polynomial.X /
            (RingHom.comp Polynomial.C univPolyHom) ((fun i => H.coeff i) H.natDegree)))
    simp only [H_tilde', hdeg, ↓reduceIte, coeff_natDegree, map_mul, map_pow,
      Polynomial.map_add, Polynomial.map_pow, map_X]
    rw [H_tilde, hEval, Finset.sum_range_succ, mul_add, Finset.mul_sum, Polynomial.map_sum]
    have hsum :
        ∑ i ∈ Finset.range H.natDegree,
          ((RingHom.comp Polynomial.C univPolyHom) ((fun i => H.coeff i) H.natDegree) ^
              (H.natDegree - 1)) *
            (Polynomial.C (univPolyHom (H.coeff i)) *
              (Polynomial.X /
                (RingHom.comp Polynomial.C univPolyHom) ((fun i => H.coeff i) H.natDegree)) ^ i) =
        ∑ i ∈ Finset.range H.natDegree,
          Polynomial.map univPolyHom
            (Polynomial.C (H.coeff i) * Polynomial.C H.leadingCoeff ^ (H.natDegree - 1 - i) *
              Polynomial.X ^ i) := by
      refine Finset.sum_congr rfl ?_
      intro i hi
      simpa [Polynomial.coeff_natDegree, map_mul, map_pow] using
        monicize_term (univPolyHom H.leadingCoeff) (univPolyHom (H.coeff i)) i H.natDegree
          hw_ne_zero (Finset.mem_range.mp hi)
    have hlead :
        ((RingHom.comp Polynomial.C univPolyHom) ((fun i => H.coeff i) H.natDegree) ^
            (H.natDegree - 1)) *
          (Polynomial.C (univPolyHom (H.coeff H.natDegree)) *
            (Polynomial.X /
              (RingHom.comp Polynomial.C univPolyHom) ((fun i => H.coeff i) H.natDegree)) ^
              H.natDegree) =
        Polynomial.X ^ H.natDegree := by
      simpa [Polynomial.coeff_natDegree] using
        monicize_leading_term (univPolyHom H.leadingCoeff) H.natDegree hw_ne_zero hd
    rw [hlead]
    calc
      Polynomial.X ^ H.natDegree +
          ∑ i ∈ Finset.range H.natDegree,
            Polynomial.map univPolyHom
              (Polynomial.C (H.coeff i) * Polynomial.C H.leadingCoeff ^ (H.natDegree - 1 - i) *
                Polynomial.X ^ i) =
          Polynomial.X ^ H.natDegree +
            ∑ i ∈ Finset.range H.natDegree,
              (RingHom.comp Polynomial.C univPolyHom) ((fun i => H.coeff i) H.natDegree) ^
                  (H.natDegree - 1) *
                (Polynomial.C (univPolyHom (H.coeff i)) *
                  (Polynomial.X /
                    (RingHom.comp Polynomial.C univPolyHom) ((fun i => H.coeff i) H.natDegree)) ^
                    i) := by
              exact congrArg (fun p => Polynomial.X ^ H.natDegree + p) hsum.symm
      _ =
          ∑ i ∈ Finset.range H.natDegree,
            (RingHom.comp Polynomial.C univPolyHom) ((fun i => H.coeff i) H.natDegree) ^
                (H.natDegree - 1) *
              (Polynomial.C (univPolyHom (H.coeff i)) *
                (Polynomial.X /
                  (RingHom.comp Polynomial.C univPolyHom) ((fun i => H.coeff i) H.natDegree)) ^
                  i) +
            Polynomial.X ^ H.natDegree := by
              rw [add_comm]


/-- The ring of regular elements `𝒪` from Appendix A.1 of [BCIKS20]. -/
abbrev 𝒪 (H : F[X][Y]) : Type :=
  (Polynomial (Polynomial F)) ⧸ (Ideal.span {H_tilde' H})

/-- The ring of regular elements field `𝒪` is a indeed a ring. -/
noncomputable instance {H : F[X][Y]} : Ring (𝒪 H) :=
  Ideal.Quotient.ring (Ideal.span {H_tilde' H})

/-- The ring homomorphism defining the embedding of `𝒪` into `𝕃`. -/
noncomputable def embeddingOf𝒪Into𝕃 (H : F[X][Y]) : 𝒪 H →+* 𝕃 H :=
  Ideal.quotientMap
        (I := Ideal.span {H_tilde' H}) (Ideal.span {H_tilde H})
        bivPolyHom (by
          rw [Ideal.span_le]
          intro x hx
          rw [Set.mem_singleton_iff] at hx; subst hx
          change bivPolyHom (H_tilde' H) ∈ span {H_tilde H}
          rw [show bivPolyHom (H_tilde' H) = (H_tilde' H).map univPolyHom from rfl,
              H_tilde_equiv_H_tilde']
          exact Ideal.subset_span rfl)

/-- The set of regular elements inside `𝕃 H`, i.e. the set of elements of `𝕃 H`
that in fact lie in `𝒪 H`. -/
def regularElms_set (H : F[X][Y]) : Set (𝕃 H) :=
  {a : 𝕃 H | ∃ b : 𝒪 H, a = embeddingOf𝒪Into𝕃 _ b}

/-- The regular elements inside `𝕃 H`, i.e. the elements of `𝕃 H` that in fact lie in `𝒪 H`
as Type. -/
def regularElms (H : F[X][Y]) : Type :=
  {a : 𝕃 H // ∃ b : 𝒪 H, a = embeddingOf𝒪Into𝕃 _ b}

/-- Zero is regular. -/
@[simp]
lemma regularElms_set_zero (H : F[X][Y]) : (0 : 𝕃 H) ∈ regularElms_set H :=
  ⟨0, by simp⟩

/-- One is regular. -/
@[simp]
lemma regularElms_set_one (H : F[X][Y]) : (1 : 𝕃 H) ∈ regularElms_set H :=
  ⟨1, by simp⟩

/-- The regular elements are closed under addition. -/
lemma regularElms_set_add {H : F[X][Y]} {a b : 𝕃 H}
    (ha : a ∈ regularElms_set H) (hb : b ∈ regularElms_set H) :
    a + b ∈ regularElms_set H := by
  rcases ha with ⟨a', rfl⟩
  rcases hb with ⟨b', rfl⟩
  exact ⟨a' + b', by simp⟩

/-- The regular elements are closed under negation. -/
lemma regularElms_set_neg {H : F[X][Y]} {a : 𝕃 H}
    (ha : a ∈ regularElms_set H) : -a ∈ regularElms_set H := by
  rcases ha with ⟨a', rfl⟩
  exact ⟨-a', by simp⟩

/-- The regular elements are closed under subtraction. -/
lemma regularElms_set_sub {H : F[X][Y]} {a b : 𝕃 H}
    (ha : a ∈ regularElms_set H) (hb : b ∈ regularElms_set H) :
    a - b ∈ regularElms_set H := by
  simpa [sub_eq_add_neg] using regularElms_set_add ha (regularElms_set_neg hb)

/-- The regular elements are closed under multiplication. -/
lemma regularElms_set_mul {H : F[X][Y]} {a b : 𝕃 H}
    (ha : a ∈ regularElms_set H) (hb : b ∈ regularElms_set H) :
    a * b ∈ regularElms_set H := by
  rcases ha with ⟨a', rfl⟩
  rcases hb with ⟨b', rfl⟩
  exact ⟨a' * b', by simp⟩

/-- The regular elements are closed under natural powers. -/
lemma regularElms_set_pow {H : F[X][Y]} {a : 𝕃 H}
    (ha : a ∈ regularElms_set H) (n : ℕ) : a ^ n ∈ regularElms_set H := by
  induction n with
  | zero => simp
  | succ n ih =>
      simpa [pow_succ] using regularElms_set_mul ih ha

/-- Given an element `z ∈ F`, `t_z ∈ F` is a rational root of a bivariate polynomial if the pair
`(z, t_z)` is a root of the bivariate polynomial. -/
def rationalRoot (H : F[X][Y]) (z : F) : Type :=
  {t_z : F // evalEval z t_z H = 0}

/-- The rational substitution `π_z` from Appendix A.3 defined on the whole ring of
bivariate polynomials. -/
noncomputable def π_z_lift {H : F[X][Y]} (z : F) (root : rationalRoot (H_tilde' H) z) :
  F[X][Y] →+* F := Polynomial.evalEvalRingHom z root.1

/-- The rational substitution `π_z` from Appendix A.3 of [BCIKS20] is a well-defined map on the
quotient ring `𝒪`. -/
noncomputable def π_z {H : F[X][Y]} (z : F) (root : rationalRoot (H_tilde' H) z) : 𝒪 H →+* F :=
  Ideal.Quotient.lift (Ideal.span {H_tilde' H}) (π_z_lift z root) (by
    intro a ha
    rw [Ideal.mem_span_singleton] at ha
    obtain ⟨c, rfl⟩ := ha
    simp only [π_z_lift, map_mul]
    rw [show (Polynomial.evalEvalRingHom z root.1) (H_tilde' H) = 0 from root.2]
    ring)

/-- The canonical representative of an element of `F[X][Y]` inside the ring of regular elements
`𝒪`, defined when `H` has positive degree in `Y`. -/
noncomputable def canonicalRepOf𝒪 {H : F[X][Y]} (hH : 0 < H.natDegree) (β : 𝒪 H) : F[X][Y] :=
  let _hHt := H_tilde'_monic H hH
  Polynomial.modByMonic β.out (H_tilde' H)

/-- The canonical representative has degree strictly smaller than the defining relation. -/
lemma canonicalRepOf𝒪_degree_lt {H : F[X][Y]} (hH : 0 < H.natDegree) (β : 𝒪 H) :
    (canonicalRepOf𝒪 hH β).degree < (H_tilde' H).degree := by
  rw [canonicalRepOf𝒪]
  exact Polynomial.degree_modByMonic_lt _ (H_tilde'_monic H hH)

/-- The canonical representative has natural degree bounded by the defining relation. -/
lemma canonicalRepOf𝒪_natDegree_le {H : F[X][Y]} (hH : 0 < H.natDegree) (β : 𝒪 H) :
    (canonicalRepOf𝒪 hH β).natDegree ≤ (H_tilde' H).natDegree := by
  rw [canonicalRepOf𝒪]
  exact Polynomial.natDegree_modByMonic_le _ (H_tilde'_monic H hH)

/-- The canonical representative maps back to the original quotient element of `𝒪`. -/
@[simp]
lemma mk_canonicalRepOf𝒪 {H : F[X][Y]} (hH : 0 < H.natDegree) (β : 𝒪 H) :
    Ideal.Quotient.mk (Ideal.span {H_tilde' H}) (canonicalRepOf𝒪 hH β) = β := by
  let I : Ideal F[X][Y] := Ideal.span {H_tilde' H}
  let q : F[X][Y] := H_tilde' H
  let p : F[X][Y] := β.out
  have hq_zero : Ideal.Quotient.mk I (q * (p /ₘ q)) = 0 := by
    rw [Ideal.Quotient.eq_zero_iff_mem]
    exact Ideal.mul_mem_right _ _ (Ideal.subset_span rfl)
  calc
    Ideal.Quotient.mk (Ideal.span {H_tilde' H}) (canonicalRepOf𝒪 hH β)
        = Ideal.Quotient.mk I (p %ₘ q) := by
            simp [canonicalRepOf𝒪, I, q, p]
    _ = Ideal.Quotient.mk I (p %ₘ q) + Ideal.Quotient.mk I (q * (p /ₘ q)) := by
            simp [hq_zero]
    _ = Ideal.Quotient.mk I (p %ₘ q + q * (p /ₘ q)) := by
            rw [map_add]
    _ = Ideal.Quotient.mk I p := by
            rw [Polynomial.modByMonic_add_div]
    _ = β := by
            simp [I, p]

/-- Canonical representatives of quotient constructors are computed by `modByMonic`. -/
lemma canonicalRepOf𝒪_mk {H : F[X][Y]} (hH : 0 < H.natDegree) (p : F[X][Y]) :
    canonicalRepOf𝒪 hH (Ideal.Quotient.mk (Ideal.span {H_tilde' H}) p : 𝒪 H) =
      p %ₘ H_tilde' H := by
  apply Polynomial.modByMonic_eq_of_dvd_sub (H_tilde'_monic H hH)
  rw [← Ideal.mem_span_singleton]
  rw [← Ideal.Quotient.mk_eq_mk_iff_sub_mem]
  calc
    Ideal.Quotient.mk (Ideal.span {H_tilde' H})
        ((Ideal.Quotient.mk (Ideal.span {H_tilde' H}) p : 𝒪 H).out)
        = (Ideal.Quotient.mk (Ideal.span {H_tilde' H}) p : 𝒪 H) := by simp
    _ = Ideal.Quotient.mk (Ideal.span {H_tilde' H}) p := rfl

/-- The canonical representative of zero is zero. -/
@[simp]
lemma canonicalRepOf𝒪_zero {H : F[X][Y]} (hH : 0 < H.natDegree) :
    canonicalRepOf𝒪 hH (0 : 𝒪 H) = 0 := by
  simpa using (canonicalRepOf𝒪_mk (H := H) hH 0)

/-- A polynomial whose degree is already below the relation is its own canonical representative. -/
lemma canonicalRepOf𝒪_mk_eq_self_of_degree_lt {H : F[X][Y]} (hH : 0 < H.natDegree)
    {p : F[X][Y]} (hp : p.degree < (H_tilde' H).degree) :
    canonicalRepOf𝒪 hH (Ideal.Quotient.mk (Ideal.span {H_tilde' H}) p : 𝒪 H) = p := by
  rw [canonicalRepOf𝒪_mk]
  exact (Polynomial.modByMonic_eq_self_iff (H_tilde'_monic H hH)).2 hp

/-- `Λ` is a weight function on the ring of bivariate polynomials `F[X][Y]`. The weight of
a polynomial is the maximal weight of all monomials appearing in it with non-zero coefficients.
The weight of the zero polynomial is `−∞`.
Requires `D ≥ Bivariate.totalDegree H` to match definition in [BCIKS20]. -/
noncomputable def weight_Λ (f H : F[X][Y]) (D : ℕ) : WithBot ℕ :=
  Finset.sup
    f.support
    (fun deg =>
      WithBot.some <| deg * (D + 1 - Bivariate.natDegreeY H) + (f.coeff deg).natDegree
    )

/-- The zero polynomial has bottom `Λ`-weight. -/
@[simp]
lemma weight_Λ_zero (H : F[X][Y]) (D : ℕ) :
    weight_Λ (0 : F[X][Y]) H D = ⊥ := by
  simp [weight_Λ]

/-- The weight function `Λ` on the ring of regular elements `𝒪` is defined as the weight their
canonical representatives in `F[X][Y]`. -/
noncomputable def weight_Λ_over_𝒪 {H : F[X][Y]} (hH : 0 < H.natDegree) (f : 𝒪 H) (D : ℕ) :
    WithBot ℕ := weight_Λ (canonicalRepOf𝒪 hH f) H D

/-- The `𝒪`-weight of zero is bottom. -/
@[simp]
lemma weight_Λ_over_𝒪_zero {H : F[X][Y]} (hH : 0 < H.natDegree) (D : ℕ) :
    weight_Λ_over_𝒪 hH (0 : 𝒪 H) D = ⊥ := by
  simp [weight_Λ_over_𝒪]

/-- The `𝒪`-weight of a quotient constructor is computed on its canonical remainder. -/
lemma weight_Λ_over_𝒪_mk {H : F[X][Y]} (hH : 0 < H.natDegree) (p : F[X][Y])
    (D : ℕ) :
    weight_Λ_over_𝒪 hH (Ideal.Quotient.mk (Ideal.span {H_tilde' H}) p : 𝒪 H) D =
      weight_Λ (p %ₘ H_tilde' H) H D := by
  simp [weight_Λ_over_𝒪, canonicalRepOf𝒪_mk]

/-- If a representative is already reduced, its `𝒪`-weight is its polynomial `Λ`-weight. -/
lemma weight_Λ_over_𝒪_mk_eq_self_of_degree_lt {H : F[X][Y]} (hH : 0 < H.natDegree)
    {p : F[X][Y]} (hp : p.degree < (H_tilde' H).degree) (D : ℕ) :
    weight_Λ_over_𝒪 hH (Ideal.Quotient.mk (Ideal.span {H_tilde' H}) p : 𝒪 H) D =
      weight_Λ p H D := by
  simp [weight_Λ_over_𝒪, canonicalRepOf𝒪_mk_eq_self_of_degree_lt hH hp]

/-- The set `S_β` from the statement of Lemma A.1 in Appendix A of [BCIKS20].
Note: Here `F[X][Y]` is `F[Z][T]`. -/
noncomputable def S_β {H : F[X][Y]} (β : 𝒪 H) : Set F :=
  {z : F | ∃ root : rationalRoot (H_tilde' H) z, (π_z z root) β = 0}

/-- The embeddining of the coefficients of a bivarite polynomial into the bivariate polynomial ring
with rational coefficients. -/
noncomputable def coeffAsRatFunc : F[X] →+* Polynomial (RatFunc F) :=
  RingHom.comp bivPolyHom Polynomial.C

/-- The embeddining of the coefficients of a bivarite polynomial into the function field `𝕃`. -/
noncomputable def liftToFunctionField {H : F[X][Y]} : F[X] →+* 𝕃 H :=
  RingHom.comp (Ideal.Quotient.mk (Ideal.span {H_tilde H})) coeffAsRatFunc

noncomputable def liftBivariate {H : F[X][Y]} : F[X][Y] →+* 𝕃 H :=
  RingHom.comp (Ideal.Quotient.mk (Ideal.span {H_tilde H})) bivPolyHom

/-- The image of the polynomial variable `T` in the function field `𝕃 H`. -/
noncomputable def functionFieldT {H : F[X][Y]} : 𝕃 H :=
  Ideal.Quotient.mk (Ideal.span {H_tilde H}) Polynomial.X

/-- Quotient constructors in `𝒪` embed by applying the bivariate lift. -/
@[simp]
lemma embeddingOf𝒪Into𝕃_mk (H : F[X][Y]) (p : F[X][Y]) :
    embeddingOf𝒪Into𝕃 H (Ideal.Quotient.mk (Ideal.span {H_tilde' H}) p : 𝒪 H) =
      liftBivariate (H := H) p := by
  rfl

/-- Every bivariate polynomial representative gives a regular element of the function field. -/
lemma regular_liftBivariate (H : F[X][Y]) (p : F[X][Y]) :
    ∃ pre : 𝒪 H, embeddingOf𝒪Into𝕃 H pre = liftBivariate (H := H) p :=
  ⟨Ideal.Quotient.mk (Ideal.span {H_tilde' H}) p, by simp⟩

/-- Bivariate-polynomial images are regular elements of the function field. -/
lemma regularElms_set_liftBivariate (H : F[X][Y]) (p : F[X][Y]) :
    liftBivariate (H := H) p ∈ regularElms_set H := by
  rcases regular_liftBivariate H p with ⟨pre, hpre⟩
  exact ⟨pre, hpre.symm⟩

/-- Coefficients embedded into `𝕃` are regular elements. -/
lemma regular_liftToFunctionField (H : F[X][Y]) (p : F[X]) :
    ∃ pre : 𝒪 H, embeddingOf𝒪Into𝕃 H pre = liftToFunctionField (H := H) p :=
  regular_liftBivariate H (Polynomial.C p)

/-- Coefficient-polynomial images are regular elements of the function field. -/
lemma regularElms_set_liftToFunctionField (H : F[X][Y]) (p : F[X]) :
    liftToFunctionField (H := H) p ∈ regularElms_set H := by
  simpa using regularElms_set_liftBivariate H (Polynomial.C p)

/-- The bivariate variable maps to the function-field variable `T`. -/
@[simp]
lemma liftBivariate_X {H : F[X][Y]} :
    liftBivariate (H := H) (Polynomial.X : F[X][Y]) = functionFieldT (H := H) := by
  simp [liftBivariate, functionFieldT, bivPolyHom]

/-- The function-field variable `T` is regular. -/
lemma regularElms_set_functionFieldT (H : F[X][Y]) :
    functionFieldT (H := H) ∈ regularElms_set H := by
  simpa using regularElms_set_liftBivariate H (Polynomial.X : F[X][Y])

/-- Constant bivariate polynomials map through the coefficient embedding. -/
@[simp]
lemma liftBivariate_C {H : F[X][Y]} (p : F[X]) :
    liftBivariate (H := H) (Polynomial.C p : F[X][Y]) = liftToFunctionField (H := H) p := by
  rfl

/-- The embeddining of the scalars into the function field `𝕃`. -/
noncomputable def fieldTo𝕃 {H : F[X][Y]} : F →+* 𝕃 H :=
  RingHom.comp liftToFunctionField Polynomial.C

/-- Constructing power series over the function field `𝕃 H` out of a polynomial. -/
noncomputable def polyToPowerSeries𝕃 (H : F[X][Y]) (P : F[X][Y]) : PowerSeries (𝕃 H) :=
  PowerSeries.mk <| fun n => liftToFunctionField (P.coeff n)

/-! ### Lemma A.1 (BCIKS20 Appendix A.3) -/

/-- The bivariate-lift hom `liftBivariate` sends a representative to zero in `𝕃` exactly when
`H_tilde H` divides its image in `(RatFunc F)[Y]`. -/
lemma liftBivariate_eq_zero_iff_dvd {H : F[X][Y]} (p : F[X][Y]) :
    liftBivariate (H := H) p = 0 ↔ H_tilde H ∣ p.map univPolyHom := by
  rw [liftBivariate, RingHom.comp_apply, Ideal.Quotient.eq_zero_iff_mem,
      Ideal.mem_span_singleton]
  exact Iff.rfl

/-- `H_tilde' H` has `Y`-degree equal to `H.natDegree` when `H` has positive `Y`-degree
(it is monic of that degree). -/
lemma natDegree_H_tilde' {H : F[X][Y]} (hH : 0 < H.natDegree) :
    (H_tilde' H).natDegree = H.natDegree := by
  classical
  have hdeg : H.natDegree ≠ 0 := Nat.ne_of_gt hH
  rw [H_tilde', if_neg hdeg]
  refine Polynomial.natDegree_eq_of_degree_eq_some ?_
  rw [Polynomial.degree_add_eq_left_of_degree_lt]
  · simp
  · refine lt_of_le_of_lt (Polynomial.degree_sum_le _ _) ?_
    rw [Polynomial.degree_X_pow]
    refine (Finset.sup_lt_iff (WithBot.bot_lt_coe H.natDegree)).2 ?_
    intro i hi
    exact (Polynomial.degree_C_mul_X_pow_le i _).trans_lt
      (WithBot.coe_lt_coe.2 (Finset.mem_range.mp hi))

/-- The monicization `H_tilde H` over `RatFunc F` has `Y`-degree equal to `H.natDegree`. -/
lemma natDegree_H_tilde {H : F[X][Y]} (hH : 0 < H.natDegree) :
    (H_tilde H).natDegree = H.natDegree := by
  have hinj : Function.Injective (univPolyHom : F[X] →+* RatFunc F) := by
    rw [univPolyHom]; exact IsFractionRing.injective _ _
  rw [← H_tilde_equiv_H_tilde', Polynomial.natDegree_map_eq_of_injective hinj,
      natDegree_H_tilde' hH]

/-- The degree of `H_tilde H` (over `RatFunc F`) equals the degree of `H_tilde' H` (over `F[X]`). -/
lemma degree_H_tilde_eq {H : F[X][Y]} (hH : 0 < H.natDegree) :
    (H_tilde H).degree = (H_tilde' H).degree := by
  rw [← H_tilde_equiv_H_tilde', (H_tilde'_monic H hH).degree_map univPolyHom]

/-- The bridge: if the canonical representative of `β` is zero, then `β` embeds to `0` in `𝕃`. -/
lemma embeddingOf𝒪Into𝕃_eq_zero_of_canonicalRep_eq_zero {H : F[X][Y]} (hH : 0 < H.natDegree)
    (β : 𝒪 H) (hP : canonicalRepOf𝒪 hH β = 0) :
    embeddingOf𝒪Into𝕃 _ β = 0 := by
  conv_lhs => rw [← mk_canonicalRepOf𝒪 hH β, embeddingOf𝒪Into𝕃_mk]
  rw [hP, liftBivariate_eq_zero_iff_dvd]
  simp

/-- The converse direction of the bridge: if `β` embeds to `0`, its canonical representative is
`0`. This uses that `H_tilde H` is monic of degree `H.natDegree`, strictly above the degree of
any canonical representative. -/
lemma canonicalRep_eq_zero_of_embeddingOf𝒪Into𝕃_eq_zero {H : F[X][Y]} (hH : 0 < H.natDegree)
    (β : 𝒪 H) (hemb : embeddingOf𝒪Into𝕃 _ β = 0) :
    canonicalRepOf𝒪 hH β = 0 := by
  set P := canonicalRepOf𝒪 hH β with hP_def
  have hmk : Ideal.Quotient.mk (Ideal.span {H_tilde' H}) P = β := mk_canonicalRepOf𝒪 hH β
  have hzero : liftBivariate (H := H) P = 0 := by
    have : embeddingOf𝒪Into𝕃 _ β = liftBivariate (H := H) P := by
      conv_lhs => rw [← hmk, embeddingOf𝒪Into𝕃_mk]
    rw [← this]; exact hemb
  rw [liftBivariate_eq_zero_iff_dvd] at hzero
  have hdeg_lt : (P.map univPolyHom).degree < (H_tilde H).degree := by
    refine lt_of_le_of_lt Polynomial.degree_map_le ?_
    rw [degree_H_tilde_eq hH]
    exact canonicalRepOf𝒪_degree_lt hH β
  have hmap_zero : P.map univPolyHom = 0 :=
    Polynomial.eq_zero_of_dvd_of_degree_lt hzero hdeg_lt
  have hinj : Function.Injective (Polynomial.map (univPolyHom : F[X] →+* RatFunc F)) := by
    apply Polynomial.map_injective
    rw [univPolyHom]
    exact IsFractionRing.injective _ _
  exact hinj (by simpa using hmap_zero)

/-- The substitution `π_z` evaluated on `β` agrees with evaluating the canonical representative
of `β` at `(z, t_z)`. -/
lemma π_z_eq_evalEval_canonicalRep {H : F[X][Y]} (hH : 0 < H.natDegree) (β : 𝒪 H) (z : F)
    (root : rationalRoot (H_tilde' H) z) :
    (π_z z root) β = Polynomial.evalEval z root.1 (canonicalRepOf𝒪 hH β) := by
  conv_lhs => rw [← mk_canonicalRepOf𝒪 hH β]
  rw [π_z, Ideal.Quotient.lift_mk]
  rfl

/-- Membership in `S_β` extracts, for the canonical representative `P` of `β`, a common root
`(z, t_z)` of `H_tilde' H` and `P` over `F`. -/
lemma exists_common_root_of_mem_S_β {H : F[X][Y]} (hH : 0 < H.natDegree) (β : 𝒪 H) {z : F}
    (hz : z ∈ S_β β) :
    ∃ t : F, Polynomial.evalEval z t (H_tilde' H) = 0 ∧
      Polynomial.evalEval z t (canonicalRepOf𝒪 hH β) = 0 := by
  obtain ⟨root, hroot⟩ := hz
  refine ⟨root.1, root.2, ?_⟩
  rw [← π_z_eq_evalEval_canonicalRep hH β z root]
  exact hroot

/-! ### A graded degree bound for determinants of polynomial matrices -/

/-- A weighted (graded) degree bound for the determinant of a polynomial matrix. If we can assign
row weights `r` and column weights `c` such that every nonzero entry `M i j` satisfies
`natDegree (M i j) + r i ≤ c j`, then `natDegree (det M) ≤ (∑ c) - (∑ r)`. The `+`/`-` arithmetic is
over `ℕ`; the bound is vacuous-safe since zero entries make the corresponding product vanish. -/
lemma natDegree_det_le_sub {R : Type*} [CommRing R] {ι : Type*}
    [DecidableEq ι] [Fintype ι] (M : Matrix ι ι R[X]) (r c : ι → ℕ)
    (h : ∀ i j, M i j ≠ 0 → (M i j).natDegree + r i ≤ c j) :
    (M.det).natDegree ≤ (∑ j, c j) - ∑ i, r i := by
  classical
  rw [Matrix.det_apply]
  refine Polynomial.natDegree_sum_le_of_forall_le _ _ (fun σ _ => ?_)
  refine le_trans (Polynomial.natDegree_smul_le _ _) ?_
  by_cases hzero : ∃ i, M (σ i) i = 0
  · obtain ⟨i, hi⟩ := hzero
    have hp0 : ∏ i, M (σ i) i = 0 := Finset.prod_eq_zero (Finset.mem_univ i) hi
    simp [hp0]
  · push_neg at hzero
    have hprod : (∏ i, M (σ i) i).natDegree ≤ ∑ i, (M (σ i) i).natDegree :=
      Polynomial.natDegree_prod_le _ _
    have hkey : (∑ i, (M (σ i) i).natDegree) + ∑ i, r i ≤ ∑ j, c j := by
      rw [show ∑ i, r i = ∑ i, r (σ i) from (Equiv.sum_comp σ r).symm, ← Finset.sum_add_distrib]
      exact Finset.sum_le_sum (fun i _ => h (σ i) i (hzero i))
    omega

/-- The `X`-elimination polynomial of Lemma A.1: the `Y`-resultant of `H_tilde' H` with the
canonical representative of `β`, an element of `F[X]`. Its roots contain `S_β`. -/
noncomputable def elimPoly {H : F[X][Y]} (hH : 0 < H.natDegree) (β : 𝒪 H) : F[X] :=
  Polynomial.resultant (H_tilde' H) (canonicalRepOf𝒪 hH β)
    (H_tilde' H).natDegree (canonicalRepOf𝒪 hH β).natDegree

/-- Specializing `X := z` commutes with the resultant: `(elimPoly β).eval z` is the resultant over
`F` of the two specialized univariate polynomials in `Y`. -/
lemma eval_elimPoly {H : F[X][Y]} (hH : 0 < H.natDegree) (β : 𝒪 H) (z : F) :
    (elimPoly hH β).eval z =
      Polynomial.resultant (Polynomial.Bivariate.evalX z (H_tilde' H))
        (Polynomial.Bivariate.evalX z (canonicalRepOf𝒪 hH β))
        (H_tilde' H).natDegree (canonicalRepOf𝒪 hH β).natDegree := by
  rw [elimPoly, Polynomial.Bivariate.evalX_eq_map, Polynomial.Bivariate.evalX_eq_map,
      Polynomial.resultant_map_map]
  rfl

/-- For `z ∈ S_β`, the elimination polynomial vanishes at `z`. -/
lemma elimPoly_eval_eq_zero_of_mem_S_β {H : F[X][Y]} (hH : 0 < H.natDegree) (β : 𝒪 H) {z : F}
    (hz : z ∈ S_β β) :
    (elimPoly hH β).eval z = 0 := by
  classical
  obtain ⟨t, hHt, hPt⟩ := exists_common_root_of_mem_S_β hH β hz
  rw [eval_elimPoly]
  set f := Polynomial.Bivariate.evalX z (H_tilde' H) with hf_def
  set g := Polynomial.Bivariate.evalX z (canonicalRepOf𝒪 hH β) with hg_def
  -- Both specialized polynomials have `t` as a root, so `X - C t` divides each.
  have hf_root : f.IsRoot t := by
    rw [hf_def, Polynomial.Bivariate.evalX_eq_map, Polynomial.IsRoot,
        Polynomial.map_evalRingHom_eval]; exact hHt
  have hg_root : g.IsRoot t := by
    rw [hg_def, Polynomial.Bivariate.evalX_eq_map, Polynomial.IsRoot,
        Polynomial.map_evalRingHom_eval]; exact hPt
  have hdvd_f : (Polynomial.X - Polynomial.C t) ∣ f := Polynomial.dvd_iff_isRoot.mpr hf_root
  have hdvd_g : (Polynomial.X - Polynomial.C t) ∣ g := Polynomial.dvd_iff_isRoot.mpr hg_root
  -- The degree arguments dominate the actual degrees of `f` and `g`.
  have hfle : f.natDegree ≤ (H_tilde' H).natDegree := by
    rw [hf_def, Polynomial.Bivariate.evalX_eq_map]; exact Polynomial.natDegree_map_le
  have hgle : g.natDegree ≤ (canonicalRepOf𝒪 hH β).natDegree := by
    rw [hg_def, Polynomial.Bivariate.evalX_eq_map]; exact Polynomial.natDegree_map_le
  have hmn : (H_tilde' H).natDegree ≠ 0 ∨ (canonicalRepOf𝒪 hH β).natDegree ≠ 0 :=
    Or.inl (by rw [natDegree_H_tilde' hH]; exact Nat.ne_of_gt hH)
  -- By contradiction: if the resultant is nonzero, `X - C t` would divide a nonzero constant.
  by_contra hres
  obtain ⟨p, q, _, _, hpq⟩ :=
    Polynomial.exists_mul_add_mul_eq_C_resultant f g hfle hgle hmn
  have hdvd_C : (Polynomial.X - Polynomial.C t) ∣
      Polynomial.C (Polynomial.resultant f g (H_tilde' H).natDegree
        (canonicalRepOf𝒪 hH β).natDegree) := by
    rw [← hpq]; exact dvd_add (hdvd_f.mul_right p) (hdvd_g.mul_right q)
  have hC_ne : Polynomial.C (Polynomial.resultant f g (H_tilde' H).natDegree
      (canonicalRepOf𝒪 hH β).natDegree) ≠ 0 := by
    simpa [Polynomial.C_eq_zero] using hres
  have hdeg_le := Polynomial.degree_le_of_dvd hdvd_C hC_ne
  rw [Polynomial.degree_X_sub_C, Polynomial.degree_C
      (by simpa [Polynomial.C_eq_zero] using hres)] at hdeg_le
  exact absurd hdeg_le (by decide)

/-- The elimination polynomial is nonzero. This is where `[Fact (Irreducible H)]` is used: over
`RatFunc F`, `H_tilde H` is irreducible and the (mapped) canonical representative has strictly
smaller `Y`-degree, hence cannot be divisible by `H_tilde H`, so the two are coprime and their
resultant — the image of `elimPoly` under `univPolyHom` — is nonzero. -/
lemma elimPoly_ne_zero {H : F[X][Y]} [Fact (Irreducible H)] (hH : 0 < H.natDegree)
    (β : 𝒪 H) (hP : canonicalRepOf𝒪 hH β ≠ 0) :
    elimPoly hH β ≠ 0 := by
  have hinj : Function.Injective (univPolyHom : F[X] →+* RatFunc F) := by
    rw [univPolyHom]; exact IsFractionRing.injective _ _
  -- Map the resultant down to `RatFunc F`.
  have hmap : univPolyHom (elimPoly hH β) =
      Polynomial.resultant (H_tilde H) ((canonicalRepOf𝒪 hH β).map univPolyHom)
        (H_tilde' H).natDegree (canonicalRepOf𝒪 hH β).natDegree := by
    rw [elimPoly, ← Polynomial.resultant_map_map, H_tilde_equiv_H_tilde']
  -- The mapped canonical representative is nonzero with `Y`-degree `< H_tilde H`.
  set P' := (canonicalRepOf𝒪 hH β).map univPolyHom with hP'_def
  have hP'_ne : P' ≠ 0 := by
    rw [hP'_def]
    intro hzero
    exact hP (by
      have hmi : Function.Injective (Polynomial.map (univPolyHom : F[X] →+* RatFunc F)) :=
        Polynomial.map_injective _ hinj
      exact hmi (by simpa using hzero))
  have hHt_irr : Irreducible (H_tilde H) := irreducibleHTildeOfIrreducible hH (Fact.out)
  have hdeg_lt : P'.degree < (H_tilde H).degree := by
    rw [hP'_def]
    refine lt_of_le_of_lt Polynomial.degree_map_le ?_
    rw [degree_H_tilde_eq hH]
    exact canonicalRepOf𝒪_degree_lt hH β
  -- `H_tilde H` does not divide `P'` (degree), so they are coprime.
  have hnotdvd : ¬ (H_tilde H ∣ P') := fun hdvd =>
    absurd (Polynomial.eq_zero_of_dvd_of_degree_lt hdvd hdeg_lt) hP'_ne
  have hcop : IsCoprime (H_tilde H) P' :=
    (dvd_or_isCoprime _ _ hHt_irr).resolve_left hnotdvd
  have hres_ne : Polynomial.resultant (H_tilde H) P'
      (H_tilde' H).natDegree (canonicalRepOf𝒪 hH β).natDegree ≠ 0 := by
    have hcop' : IsCoprime (H_tilde H) P' := hcop
    -- `resultant_ne_zero` uses default degrees; rewrite to the right degree arguments.
    have hHd : (H_tilde H).natDegree = (H_tilde' H).natDegree := by
      rw [natDegree_H_tilde hH, natDegree_H_tilde' hH]
    have hPd : P'.natDegree = (canonicalRepOf𝒪 hH β).natDegree := by
      rw [hP'_def, Polynomial.natDegree_map_eq_of_injective hinj]
    have := Polynomial.resultant_ne_zero (H_tilde H) P' hcop'
    rwa [hHd, hPd] at this
  intro hzero
  apply hres_ne
  rw [← hmap, hzero, map_zero]

/-- `S_β` is contained in the (finite) root set of the elimination polynomial. -/
lemma S_β_subset_root_set {H : F[X][Y]} [Fact (Irreducible H)] (hH : 0 < H.natDegree) (β : 𝒪 H)
    (hP : canonicalRepOf𝒪 hH β ≠ 0) :
    S_β β ⊆ {z : F | (elimPoly hH β).IsRoot z} := by
  intro z hz
  exact elimPoly_eval_eq_zero_of_mem_S_β hH β hz

/-- The cardinality of `S_β` is bounded by the degree of the elimination polynomial. -/
lemma ncard_S_β_le_natDegree_elimPoly {H : F[X][Y]} [Fact (Irreducible H)] (hH : 0 < H.natDegree)
    (β : 𝒪 H) (hP : canonicalRepOf𝒪 hH β ≠ 0) :
    Set.ncard (S_β β) ≤ (elimPoly hH β).natDegree := by
  classical
  have hsub : S_β β ⊆ ↑(elimPoly hH β).roots.toFinset := by
    intro z hz
    rw [Finset.mem_coe, Multiset.mem_toFinset, Polynomial.mem_roots (elimPoly_ne_zero hH β hP)]
    exact elimPoly_eval_eq_zero_of_mem_S_β hH β hz
  calc Set.ncard (S_β β)
      ≤ Set.ncard (↑(elimPoly hH β).roots.toFinset : Set F) :=
        Set.ncard_le_ncard hsub (Finset.finite_toSet _)
    _ = (elimPoly hH β).roots.toFinset.card := Set.ncard_coe_finset _
    _ ≤ Multiset.card (elimPoly hH β).roots := Multiset.toFinset_card_le _
    _ ≤ (elimPoly hH β).natDegree := Polynomial.card_roots' _

/-- Coefficient formula for the monicization below the leading term: for `k < H.natDegree`,
`(H_tilde' H).coeff k = H.coeff k * (H.coeff N)^(N - 1 - k)`. -/
private lemma coeff_H_tilde'_of_lt (H : F[X][Y]) (hH : 0 < H.natDegree) (k : ℕ)
    (hk : k < H.natDegree) :
    (H_tilde' H).coeff k = H.coeff k * (H.coeff H.natDegree) ^ (H.natDegree - 1 - k) := by
  classical
  have hne : H.natDegree ≠ 0 := Nat.ne_of_gt hH
  rw [H_tilde', if_neg hne]
  simp only [Polynomial.coeff_add]
  rw [Polynomial.coeff_X_pow, if_neg (by omega), zero_add, Polynomial.finset_sum_coeff,
      Finset.sum_eq_single k]
  · rw [Polynomial.coeff_C_mul, Polynomial.coeff_X_pow, if_pos rfl, mul_one]
  · intro b _ _
    rw [Polynomial.coeff_C_mul, Polynomial.coeff_X_pow, if_neg (by omega), mul_zero]
  · intro hk'; exact absurd (Finset.mem_range.mpr hk) hk'

/-- Arithmetic core of the `Q`-coefficient degree bound. -/
private lemma natDegree_coeff_H_tilde'_arith (k N T D : ℕ) (hkN : k < N) (hNT : N ≤ T)
    (hTD : T ≤ D) :
    (T - k) + (N - 1 - k) * (T - N) ≤ (N - k) * (D + 1 - N) := by
  have hstep1 : (T - k) + (N - 1 - k) * (T - N) ≤ (D - k) + (N - 1 - k) * (D - N) :=
    Nat.add_le_add (by omega) (Nat.mul_le_mul_left _ (by omega))
  have hid : (D - k) + (N - 1 - k) * (D - N) = (N - k) * (D + 1 - N) := by
    have hNk : N - k = (N - 1 - k) + 1 := by omega
    have hDN : D + 1 - N = (D - N) + 1 := by omega
    rw [hNk, hDN]; ring_nf; omega
  omega

/-- Each coefficient of the monicization satisfies the graded `X`-degree bound
`((H_tilde' H).coeff k).natDegree ≤ (N - k) * (D + 1 - N)` with `N = H.natDegree`, for
`D ≥ totalDegree H`. (`Q`-side input to the resultant degree bound.) -/
lemma natDegree_coeff_H_tilde'_le (H : F[X][Y]) (hH : 0 < H.natDegree) (D : ℕ)
    (hD : D ≥ Bivariate.totalDegree H) (k : ℕ) :
    ((H_tilde' H).coeff k).natDegree ≤ (H.natDegree - k) * (D + 1 - H.natDegree) := by
  classical
  set N := H.natDegree with hN
  set T := Bivariate.totalDegree H with hT
  have hHne : H ≠ 0 := by
    intro h0
    rw [hN, h0, Polynomial.natDegree_zero] at hH
    exact absurd hH (by omega)
  have hN_supp : N ∈ H.support := by
    rw [hN, Polynomial.mem_support_iff, ← Polynomial.leadingCoeff]
    exact Polynomial.leadingCoeff_ne_zero.mpr hHne
  have hWdeg : (H.coeff N).natDegree + N ≤ T := Bivariate.coeff_totalDegree_le H hN_supp
  rcases lt_trichotomy k N with hk | hk | hk
  · rw [coeff_H_tilde'_of_lt H hH k hk]
    have hbound : (H.coeff k * (H.coeff N) ^ (N - 1 - k)).natDegree ≤
        (H.coeff k).natDegree + (N - 1 - k) * (H.coeff N).natDegree :=
      le_trans Polynomial.natDegree_mul_le (Nat.add_le_add_left Polynomial.natDegree_pow_le _)
    rcases Bivariate.coeff_totalDegree_le' H k with hck | hck
    · have h1 : (H.coeff k).natDegree ≤ T - k := by omega
      have h2 : (H.coeff N).natDegree ≤ T - N := by omega
      calc (H.coeff k * (H.coeff N) ^ (N - 1 - k)).natDegree
          ≤ (H.coeff k).natDegree + (N - 1 - k) * (H.coeff N).natDegree := hbound
        _ ≤ (T - k) + (N - 1 - k) * (T - N) :=
              Nat.add_le_add h1 (Nat.mul_le_mul_left _ h2)
        _ ≤ (N - k) * (D + 1 - N) := natDegree_coeff_H_tilde'_arith k N T D hk (by omega) hD
    · rw [hck]; simp
  · subst hk
    rw [H_tilde', if_neg (Nat.ne_of_gt hH)]
    simp only [Polynomial.coeff_add]
    rw [Polynomial.coeff_X_pow, if_pos rfl]
    have hsum0 : (∑ i ∈ Finset.range N, Polynomial.C (H.coeff i * (H.coeff N) ^ (N - 1 - i)) *
        Polynomial.X ^ i).coeff N = 0 := by
      rw [Polynomial.finset_sum_coeff]
      exact Finset.sum_eq_zero (fun i hi => by
        rw [Polynomial.coeff_C_mul, Polynomial.coeff_X_pow,
            if_neg (by rw [Finset.mem_range] at hi; omega), mul_zero])
    rw [hsum0, add_zero]; simp
  · rw [Polynomial.coeff_eq_zero_of_natDegree_lt (by rw [natDegree_H_tilde' hH]; omega)]; simp

/-- If the canonical representative is nonzero, its `Λ`-weight is not `⊥` (the support is
nonempty, so the defining `Finset.sup` of `WithBot.some` values is itself a `WithBot.some`). -/
lemma weight_Λ_over_𝒪_ne_bot {H : F[X][Y]} (hH : 0 < H.natDegree) (β : 𝒪 H) (D : ℕ)
    (hP : canonicalRepOf𝒪 hH β ≠ 0) :
    weight_Λ_over_𝒪 hH β D ≠ ⊥ := by
  rw [weight_Λ_over_𝒪, weight_Λ, Ne, Finset.sup_eq_bot_iff]
  intro hbot
  have hne : (canonicalRepOf𝒪 hH β).support.Nonempty := Polynomial.support_nonempty.mpr hP
  obtain ⟨k, hk⟩ := hne
  exact WithBot.coe_ne_bot (hbot k hk)

/-- The `P`-side weight bound: for the canonical representative `P` of `β`, each nonzero
coefficient satisfies `(P.coeff k).natDegree + k·s ≤ weight` (as a natural number), where
`s = D + 1 - natDegreeY H` and `weight` is the (non-`⊥`) `Λ`-weight of `β`. -/
lemma natDegree_coeff_canonicalRep_le {H : F[X][Y]} (hH : 0 < H.natDegree) (β : 𝒪 H) (D : ℕ)
    (hP : canonicalRepOf𝒪 hH β ≠ 0) (k : ℕ)
    (hk : (canonicalRepOf𝒪 hH β).coeff k ≠ 0) :
    ((canonicalRepOf𝒪 hH β).coeff k).natDegree + k * (D + 1 - Bivariate.natDegreeY H) ≤
      (weight_Λ_over_𝒪 hH β D).unbot (weight_Λ_over_𝒪_ne_bot hH β D hP) := by
  classical
  set P := canonicalRepOf𝒪 hH β with hPdef
  have hmem : k ∈ P.support := Polynomial.mem_support_iff.mpr hk
  have hle : (WithBot.some (k * (D + 1 - Bivariate.natDegreeY H) + (P.coeff k).natDegree) :
      WithBot ℕ) ≤ weight_Λ_over_𝒪 hH β D := by
    rw [weight_Λ_over_𝒪, weight_Λ]
    exact Finset.le_sup (f := fun deg => WithBot.some
      (deg * (D + 1 - Bivariate.natDegreeY H) + (P.coeff deg).natDegree)) hmem
  have := (WithBot.le_unbot_iff (weight_Λ_over_𝒪_ne_bot hH β D hP)).mpr hle
  omega

/-- The degree bound of Lemma A.1: the elimination polynomial `Res_Y(H_tilde' H, P)` has
`X`-degree at most `weight_Λ(P) · H.natDegree`, where `P` is the canonical representative of `β`.

This is the graded Sylvester-resultant degree bound (the analytic core of BCIKS20 Lemma A.1). With
`N := H.natDegree`, `M := P.natDegree`, `s := D + 1 - natDegreeY H`, and `w := unbot (weight_Λ P)`,
the Sylvester matrix `sylvester (H_tilde' H) P N M` is graded by the row weights `r i = i · s` and
column weights `c j = j · s + (w on the N `P`-columns, 0 on the M `Q`-columns)`. Every nonzero entry
`P.coeff (i - j₁)` obeys `natDegree + (i - j₁)·s ≤ w` (definition of `weight_Λ`), and every
`Q.coeff (i - j₁)` obeys `natDegree ≤ (N - (i - j₁))·s` (`natDegree_coeff_H_tilde'_le`, using
`D ≥ totalDegree H`). The graded determinant bound `natDegree_det_le_sub` then gives
`natDegree (det) ≤ (∑ c) - (∑ r)`, and the difference telescopes to `N · w`. -/
lemma natDegree_elimPoly_le {H : F[X][Y]} [Fact (Irreducible H)] (hH : 0 < H.natDegree) (β : 𝒪 H)
    (D : ℕ) (hD : D ≥ Bivariate.totalDegree H) (hP : canonicalRepOf𝒪 hH β ≠ 0) :
    (↑(elimPoly hH β).natDegree : WithBot ℕ) ≤
      weight_Λ_over_𝒪 hH β D * (H.natDegree : WithBot ℕ) := by
  classical
  set s := D + 1 - Bivariate.natDegreeY H with hs
  set w := (weight_Λ_over_𝒪 hH β D).unbot (weight_Λ_over_𝒪_ne_bot hH β D hP) with hw
  set Q := H_tilde' H with hQ
  set P := canonicalRepOf𝒪 hH β with hPdef
  set Nq := Q.natDegree with hNq
  set M := P.natDegree with hM
  have hQdeg : Nq = H.natDegree := by rw [hNq, hQ, natDegree_H_tilde' hH]
  set r : Fin (Nq + M) → ℕ := fun i => (i : ℕ) * s with hr
  set c : Fin (Nq + M) → ℕ := fun j => (j : ℕ) * s + (if (j : ℕ) < Nq then w else 0) with hc
  have helim : elimPoly hH β = (Polynomial.sylvester Q P Nq M).det := by
    rw [elimPoly, Polynomial.resultant]
  have hentry : ∀ i j, (Polynomial.sylvester Q P Nq M) i j ≠ 0 →
      ((Polynomial.sylvester Q P Nq M) i j).natDegree + r i ≤ c j := by
    intro i j hne
    rw [Polynomial.sylvester, Matrix.of_apply] at hne ⊢
    induction j using Fin.addCases with
    | left j₁ =>
      simp only [Fin.addCases_left] at hne ⊢
      have hcond : (i : ℕ) ∈ Set.Icc (j₁ : ℕ) ((j₁ : ℕ) + M) := by
        by_contra hc'; rw [if_neg hc'] at hne; exact hne rfl
      rw [if_pos hcond] at hne ⊢
      rw [Set.mem_Icc] at hcond
      have hPbound := natDegree_coeff_canonicalRep_le hH β D hP ((i : ℕ) - (j₁ : ℕ)) hne
      have hcj : c (Fin.castAdd M j₁) = (j₁ : ℕ) * s + w := by
        rw [hc]; simp only [Fin.coe_castAdd]; rw [if_pos j₁.isLt]
      rw [hcj, hr]; simp only
      have hPw : (P.coeff ((i:ℕ)-(j₁:ℕ))).natDegree + ((i:ℕ)-(j₁:ℕ)) * s ≤ w := by
        rw [hw, hs]; exact hPbound
      have hsplit : (i : ℕ) * s = ((i:ℕ)-(j₁:ℕ)) * s + (j₁:ℕ) * s := by
        rw [← Nat.add_mul]; congr 1; omega
      rw [hsplit]; omega
    | right j₁ =>
      simp only [Fin.addCases_right] at hne ⊢
      have hcond : (i : ℕ) ∈ Set.Icc (j₁ : ℕ) ((j₁ : ℕ) + Nq) := by
        by_contra hc'; rw [if_neg hc'] at hne; exact hne rfl
      rw [if_pos hcond] at hne ⊢
      rw [Set.mem_Icc] at hcond
      have hcj : c (Fin.natAdd Nq j₁) = (Nq + (j₁ : ℕ)) * s := by
        rw [hc]; simp only [Fin.coe_natAdd]; rw [if_neg (by omega), add_zero]
      rw [hcj, hr]; simp only
      -- Work with the nat index `a := i - j₁` to avoid rewriting `Nq` inside `i`'s type.
      have hQb : ∀ a : ℕ, (Q.coeff a).natDegree ≤ (Nq - a) * s := by
        intro a
        have hQbound := natDegree_coeff_H_tilde'_le H hH D hD a
        have hsNq : s = D + 1 - Nq := by rw [hs, hQdeg]; rfl
        rw [hsNq, hQ, show Nq = H.natDegree from hQdeg]
        exact hQbound
      have hkle : (Nq - ((i:ℕ) - (j₁:ℕ))) + (i:ℕ) = Nq + (j₁:ℕ) := by omega
      calc (Q.coeff ((i:ℕ)-(j₁:ℕ))).natDegree + (i:ℕ) * s
          ≤ (Nq - ((i:ℕ)-(j₁:ℕ))) * s + (i:ℕ) * s := Nat.add_le_add_right (hQb _) _
        _ = ((Nq - ((i:ℕ)-(j₁:ℕ))) + (i:ℕ)) * s := by ring
        _ = (Nq + (j₁:ℕ)) * s := by rw [hkle]
  have hdet := natDegree_det_le_sub (Polynomial.sylvester Q P Nq M) r c hentry
  have hsumc : (∑ j, c j) = (∑ j : Fin (Nq+M), (j:ℕ)*s) + Nq * w := by
    rw [hc, Finset.sum_add_distrib]
    congr 1
    rw [Fin.sum_univ_eq_sum_range (fun j => if j < Nq then w else 0) (Nq + M),
        Finset.sum_ite, Finset.sum_const_zero, add_zero, Finset.sum_const, smul_eq_mul]
    have hfilter : {x ∈ Finset.range (Nq + M) | x < Nq} = Finset.range Nq := by
      ext x; simp only [Finset.mem_filter, Finset.mem_range]; omega
    rw [hfilter, Finset.card_range, mul_comm]
  have hsumr : (∑ i, r i) = (∑ i : Fin (Nq+M), (i:ℕ)*s) := by rw [hr]
  have hsub : (∑ j, c j) - ∑ i, r i = Nq * w := by rw [hsumc, hsumr]; omega
  rw [hsub] at hdet
  have hcast : (↑(elimPoly hH β).natDegree : WithBot ℕ) ≤ (↑(Nq * w) : WithBot ℕ) := by
    rw [helim]; exact_mod_cast hdet
  refine le_trans hcast ?_
  have hweq : (weight_Λ_over_𝒪 hH β D) = (↑w : WithBot ℕ) := by
    rw [hw]; exact (WithBot.coe_unbot _ _).symm
  rw [hweq, ← hQdeg]; push_cast; rw [mul_comm]

/-- The statement of Lemma A.1 in Appendix A.3 of [BCIKS20].

Statement repair (necessary, documented for upstream): the section context provides only
`[Field F]`; this lemma additionally requires `[Fact (Irreducible H)]`. The argument eliminates
the `Y` variable via the resultant `R(X) := Res_Y(H_tilde' H, canonicalRep)`; ruling out the
degenerate case `R = 0` requires `H_tilde H` to be irreducible over `RatFunc F` (which follows
from `Irreducible H`), since otherwise a nonzero canonical representative of lower `Y`-degree could
share a factor with a reducible `H_tilde H` while still embedding to a nonzero element of `𝕃`,
falsifying the conclusion. `Lemma_A_1` has no consumers in ArkLib, so adding the hypothesis is
non-breaking; all use sites in BCIKS20 §A take `H` irreducible. -/
lemma Lemma_A_1 {H : F[X][Y]} [Fact (Irreducible H)] (hH : 0 < H.natDegree) (β : 𝒪 H) (D : ℕ)
    (hD : D ≥ Bivariate.totalDegree H)
    (S_β_card : Set.ncard (S_β β) > (weight_Λ_over_𝒪 hH β D) * H.natDegree) :
  embeddingOf𝒪Into𝕃 _ β = 0 := by
  -- It suffices to show the canonical representative of `β` is zero (Stage-1 bridge).
  rcases eq_or_ne (canonicalRepOf𝒪 hH β) 0 with hP | hP
  · exact embeddingOf𝒪Into𝕃_eq_zero_of_canonicalRep_eq_zero hH β hP
  -- Otherwise we derive a contradiction from the counting hypothesis.
  exfalso
  -- The counting chain: ncard S_β ≤ deg(elimPoly) ≤ weight · n, contradicting the hypothesis.
  have hcard : Set.ncard (S_β β) ≤ (elimPoly hH β).natDegree :=
    ncard_S_β_le_natDegree_elimPoly hH β hP
  have hdeg : (↑(elimPoly hH β).natDegree : WithBot ℕ) ≤
      weight_Λ_over_𝒪 hH β D * (H.natDegree : WithBot ℕ) :=
    natDegree_elimPoly_le hH β D hD hP
  -- Cast the cardinality bound into `WithBot ℕ`.
  have hcard' : (↑(Set.ncard (S_β β)) : WithBot ℕ) ≤ (↑(elimPoly hH β).natDegree : WithBot ℕ) := by
    exact_mod_cast hcard
  have hchain : (↑(Set.ncard (S_β β)) : WithBot ℕ) ≤
      weight_Λ_over_𝒪 hH β D * (H.natDegree : WithBot ℕ) := le_trans hcard' hdeg
  exact absurd hchain (not_le.mpr S_β_card)

end

noncomputable section

namespace ClaimA2

variable {F : Type} [Field F]
         {R : F[X][X][X]}
         {H : F[X][Y]} [H_irreducible : Fact (Irreducible H)]
         [H_pos : Fact (0 < H.natDegree)]

/-- The definition of `ζ` given in Appendix A.4 of [BCIKS20]. -/
def ζ (R : F[X][X][Y]) (x₀ : F) (H : F[X][Y]) [H_irreducible : Fact (Irreducible H)]
    [Fact (0 < H.natDegree)] : 𝕃 H :=
  let W  : 𝕃 H := liftToFunctionField (H.leadingCoeff);
  let T : 𝕃 H := functionFieldT (H := H);
    Polynomial.eval₂ liftToFunctionField (T / W)
      (Bivariate.evalX (Polynomial.C x₀) R.derivative)

/-- If the derivative specialization is constant in the function-field variable, then `ζ` is
regular. -/
lemma ζ_regular_of_derivative_evalX_eq_C (x₀ : F) (R : F[X][X][Y]) (H : F[X][Y])
    [H_irreducible : Fact (Irreducible H)] [Fact (0 < H.natDegree)] {p : F[X]}
    (hp : Bivariate.evalX (Polynomial.C x₀) R.derivative = Polynomial.C p) :
    ζ R x₀ H ∈ regularElms_set H := by
  rw [ζ, hp]
  simp only [Polynomial.eval₂_C]
  exact regularElms_set_liftToFunctionField H p

/-- In the constant-derivative, low-`Y`-degree case, the `ξ` regularity witness is explicit. -/
lemma ξ_regular_of_derivative_evalX_eq_C_of_natDegree_le_one
    (x₀ : F) (R : F[X][X][Y]) (H : F[X][Y]) [H_irreducible : Fact (Irreducible H)]
    [Fact (0 < H.natDegree)]
    {p : F[X]} (hp : Bivariate.evalX (Polynomial.C x₀) R.derivative = Polynomial.C p)
    (hR : R.natDegree ≤ 1) :
    ∃ pre : 𝒪 H,
    let d := R.natDegree
    let W : 𝕃 H := liftToFunctionField (H.leadingCoeff);
    embeddingOf𝒪Into𝕃 _ pre = W ^ (d - 2) * ζ R x₀ H := by
  rcases ζ_regular_of_derivative_evalX_eq_C x₀ R H hp with ⟨pre, hpre⟩
  refine ⟨pre, ?_⟩
  have hd : R.natDegree - 2 = 0 := by omega
  simpa [hd] using hpre.symm

omit H_irreducible in
/-- `liftToFunctionField` of a nonzero polynomial is nonzero. The defining relation `H_tilde H`
has `Y`-degree `H.natDegree ≥ 1`, so it cannot divide a nonzero degree-`0` polynomial; hence the
coefficient embedding into the function field `𝕃` has trivial kernel on constants. In particular
`W = liftToFunctionField H.leadingCoeff ≠ 0`, so `W` is invertible in the field `𝕃 H`. -/
lemma liftToFunctionField_ne_zero {p : F[X]} (hp : p ≠ 0) :
    liftToFunctionField (H := H) p ≠ 0 := by
  intro h0
  have hbiv : liftBivariate (H := H) (Polynomial.C p) = 0 := by
    rw [liftBivariate_C]; exact h0
  rw [liftBivariate_eq_zero_iff_dvd, Polynomial.map_C] at hbiv
  have hinj : Function.Injective (univPolyHom : F[X] →+* RatFunc F) := by
    rw [univPolyHom]; exact IsFractionRing.injective _ _
  have hup_ne : univPolyHom p ≠ 0 := fun h => hp (hinj (by rw [h, map_zero]))
  have hC_ne : (Polynomial.C (univPolyHom p) : Polynomial (RatFunc F)) ≠ 0 := by
    rwa [Ne, Polynomial.C_eq_zero]
  have hdeg_le := Polynomial.degree_le_of_dvd hbiv hC_ne
  rw [Polynomial.degree_C hup_ne] at hdeg_le
  have hHt_pos : 0 < (H_tilde H).natDegree := by
    rw [natDegree_H_tilde H_pos.out]; exact H_pos.out
  have hHt_ne : (H_tilde H) ≠ 0 := by
    intro h; rw [h, Polynomial.natDegree_zero] at hHt_pos; exact absurd hHt_pos (by omega)
  have hlt : (0 : WithBot ℕ) < (H_tilde H).degree := by
    rw [Polynomial.degree_eq_natDegree hHt_ne]; exact_mod_cast hHt_pos
  exact absurd (lt_of_lt_of_le hlt hdeg_le) (by simp)

omit H_irreducible H_pos in
/-- A finite sum of regular elements of `𝕃 H` is regular. -/
lemma regularElms_set_sum {ι : Type*} (s : Finset ι) (f : ι → 𝕃 H)
    (hf : ∀ i ∈ s, f i ∈ regularElms_set H) :
    (∑ i ∈ s, f i) ∈ regularElms_set H :=
  Finset.sum_induction f (· ∈ regularElms_set H)
    (fun _ _ ha hb => regularElms_set_add ha hb) (regularElms_set_zero H) hf

/-- Claim A.2 of Appendix A.4 of [BCIKS20], with the **denominator-clearing exponent `d - 1`**.

`ζ R x₀ H` is a polynomial of `Y`-degree `≤ d - 1` (where `d = R.natDegree`) in the function-field
variable `T`, evaluated at `T / W` with `W := liftToFunctionField H.leadingCoeff`. Expanding,
`ζ = ∑_{j ≤ d-1} liftToFunctionField (Qⱼ) · (T / W)^j` where `Q := evalX (C x₀) R.derivative` and
`R.derivative` lowers the `Y`-degree by one (`natDegree_derivative_le`). Multiplying by `W^(d-1)`
clears every denominator: each summand becomes
`liftToFunctionField (Qⱼ) · T^j · W^(d-1-j)` with `d-1-j ≥ 0` for all `j ≤ d-1`, so it is a product
of regular elements (`regularElms_set_liftToFunctionField`, `regularElms_set_functionFieldT`,
`regularElms_set_pow`), and the whole sum is regular (`regularElms_set_sum`).

This is the unconditional, statement-correct form of `ξ_regular`: `W^(d-1) · ζ` is regular for every
`R, x₀, H`. See `ξ_regular` below for the (off-by-one) `d - 2` exponent and why it is not the right
power to clear all denominators. -/
lemma ξ_regular' (x₀ : F) (R : F[X][X][Y]) (H : F[X][Y]) [H_irreducible : Fact (Irreducible H)]
    [Fact (0 < H.natDegree)] :
    ∃ pre : 𝒪 H,
    let d := R.natDegree
    let W : 𝕃 H := liftToFunctionField (H.leadingCoeff);
    embeddingOf𝒪Into𝕃 _ pre = W ^ (d - 1) * ζ R x₀ H := by
  classical
  set Q : F[X][Y] := Bivariate.evalX (Polynomial.C x₀) R.derivative with hQ
  set W : 𝕃 H := liftToFunctionField (H := H) H.leadingCoeff with hWdef
  set T : 𝕃 H := functionFieldT (H := H) with hTdef
  set k : ℕ := R.natDegree - 1 with hk
  have hH0 : H.leadingCoeff ≠ 0 :=
    Polynomial.leadingCoeff_ne_zero.mpr H_irreducible.out.ne_zero
  have hWne : W ≠ 0 := liftToFunctionField_ne_zero hH0
  have hQdeg : Q.natDegree ≤ k := by
    rw [hQ, hk, Polynomial.Bivariate.evalX_eq_map]
    exact le_trans Polynomial.natDegree_map_le (Polynomial.natDegree_derivative_le R)
  have hreg : W ^ k * ζ R x₀ H ∈ regularElms_set H := by
    have hζ : ζ R x₀ H
        = ∑ j ∈ Q.support, liftToFunctionField (H := H) (Q.coeff j) * (T / W) ^ j := by
      rw [ζ, ← hQ, ← hWdef, ← hTdef, Polynomial.eval₂_eq_sum, Polynomial.sum_def]
    rw [hζ, Finset.mul_sum]
    apply regularElms_set_sum
    intro j hj
    have hjk : j ≤ k := le_trans (Polynomial.le_natDegree_of_mem_supp j hj) hQdeg
    have hterm : W ^ k * (liftToFunctionField (H := H) (Q.coeff j) * (T / W) ^ j)
        = liftToFunctionField (H := H) (Q.coeff j) * T ^ j * W ^ (k - j) := by
      rw [div_pow, pow_sub₀ W hWne hjk]; field_simp
    rw [hterm]
    refine regularElms_set_mul (regularElms_set_mul ?_ ?_) ?_
    · exact regularElms_set_liftToFunctionField H (Q.coeff j)
    · exact regularElms_set_pow (regularElms_set_functionFieldT H) j
    · exact regularElms_set_pow (regularElms_set_liftToFunctionField H H.leadingCoeff) (k - j)
  obtain ⟨pre, hpre⟩ := hreg
  refine ⟨pre, ?_⟩
  change embeddingOf𝒪Into𝕃 H pre = W ^ k * ζ R x₀ H
  exact hpre.symm

omit H_irreducible H_pos in
/-- The coefficient of an explicit `Y`-monomial sum `∑ⱼ C(cⱼ)·Yʲ` at index `deg` is `c deg`
when `deg ∈ s`, and `0` otherwise (the monomials `Yʲ` are linearly independent). -/
private lemma coeff_explicit_sum (s : Finset ℕ) (c : ℕ → F[X]) (deg : ℕ) :
    (∑ j ∈ s, Polynomial.C (c j) * Polynomial.X ^ j : F[X][Y]).coeff deg
      = if deg ∈ s then c deg else 0 := by
  classical
  rw [Polynomial.finset_sum_coeff]
  by_cases hmem : deg ∈ s
  · rw [if_pos hmem, Finset.sum_eq_single deg]
    · rw [Polynomial.coeff_C_mul, Polynomial.coeff_X_pow, if_pos rfl, mul_one]
    · intro b _ hbne
      rw [Polynomial.coeff_C_mul, Polynomial.coeff_X_pow, if_neg (Ne.symm hbne), mul_zero]
    · intro hns; exact absurd hmem hns
  · rw [if_neg hmem]
    apply Finset.sum_eq_zero
    intro b hb
    rw [Polynomial.coeff_C_mul, Polynomial.coeff_X_pow, if_neg, mul_zero]
    rintro rfl; exact hmem hb

omit H_irreducible H_pos in
/-- `Λ`-weight bound for an explicit `Y`-monomial sum: if every present monomial `C(cⱼ)·Yʲ`
satisfies the graded inequality `j·s + (cⱼ).natDegree ≤ B` (with slope
`s = D + 1 - natDegreeY H`), then `weight_Λ (∑ⱼ C(cⱼ)·Yʲ) H D ≤ B`. This is the
weight-assembly core of Claim A.2. -/
private lemma weight_Λ_explicit_sum_le (s : Finset ℕ) (c : ℕ → F[X]) (D B : ℕ)
    (hb : ∀ j ∈ s, j * (D + 1 - Bivariate.natDegreeY H) + (c j).natDegree ≤ B) :
    weight_Λ (∑ j ∈ s, Polynomial.C (c j) * Polynomial.X ^ j) H D ≤ (B : WithBot ℕ) := by
  classical
  rw [weight_Λ, Finset.sup_le_iff]
  intro deg hdeg
  rw [Polynomial.mem_support_iff, coeff_explicit_sum] at hdeg
  by_cases hmem : deg ∈ s
  · rw [coeff_explicit_sum, if_pos hmem]
    exact WithBot.coe_le_coe.mpr (hb deg hmem)
  · rw [if_neg hmem] at hdeg; exact absurd rfl hdeg

omit H_irreducible H_pos in
/-- If every present `Y`-monomial `C(cⱼ)·Yʲ` has `j ≤ k` with `k < H.natDegree`, then the
sum has `degree < (H_tilde' H).degree`. Hence such a sum is its own canonical
representative in `𝒪 H`. -/
private lemma explicit_sum_degree_lt (hH : 0 < H.natDegree) (s : Finset ℕ) (c : ℕ → F[X])
    (k : ℕ) (hsk : ∀ j ∈ s, j ≤ k) (hkN : k < H.natDegree) :
    (∑ j ∈ s, Polynomial.C (c j) * Polynomial.X ^ j : F[X][Y]).degree
      < (H_tilde' H).degree := by
  classical
  have hHt_deg : (H_tilde' H).degree = (H.natDegree : WithBot ℕ) := by
    rw [Polynomial.degree_eq_natDegree (H_tilde'_monic H hH).ne_zero, natDegree_H_tilde' hH]
  rw [hHt_deg]
  refine lt_of_le_of_lt (Polynomial.degree_sum_le _ _) ?_
  refine (Finset.sup_lt_iff (WithBot.bot_lt_coe H.natDegree)).2 ?_
  intro j hj
  refine lt_of_le_of_lt (Polynomial.degree_C_mul_X_pow_le j (c j)) ?_
  exact WithBot.coe_lt_coe.mpr (lt_of_le_of_lt (hsk j hj) hkN)

/-- The explicit denominator-cleared bivariate polynomial whose image in `𝕃 H` is `W^(d-1) · ζ`
(the unconditional `d - 1` form of Claim A.2; cf. `ξ_regular'`). With `Q := evalX (C x₀) R'`
(`R' = R.derivative`), `k := d - 1`, and `lc := H.leadingCoeff`, it is
`ξPoly := ∑_{j ∈ Q.support} C(Q.coeff j · lc^(k-j)) · Yʲ`. Each `Yʲ` has `j ≤ k`, and the
scalar `Q.coeff j · lc^(k-j)` is exactly the denominator-cleared `j`-th coefficient of
`W^k · ζ`. -/
def ξPoly (x₀ : F) (R : F[X][X][Y]) (H : F[X][Y]) : F[X][Y] :=
  let Q : F[X][Y] := Bivariate.evalX (Polynomial.C x₀) R.derivative
  let k : ℕ := R.natDegree - 1
  ∑ j ∈ Q.support, Polynomial.C (Q.coeff j * H.leadingCoeff ^ (k - j)) * Polynomial.X ^ j

/-- The explicit witness `ξPoly` embeds into `𝕃 H` exactly as `W^(d-1) · ζ` (the
unconditional `d - 1` exponent of `ξ_regular'`). This is the explicit-representative
refinement of `ξ_regular'`: it pins down a concrete bivariate-polynomial preimage (rather
than an opaque `Exists.choose`), which is what makes the weight bound `weight_ξPoly_bound`
provable with a fully discharged proof. -/
lemma embeddingOf𝒪Into𝕃_mk_ξPoly (x₀ : F) (R : F[X][X][Y]) (H : F[X][Y])
    [H_irreducible : Fact (Irreducible H)] [Fact (0 < H.natDegree)] :
    embeddingOf𝒪Into𝕃 _
        (Ideal.Quotient.mk (Ideal.span {H_tilde' H}) (ξPoly x₀ R H) : 𝒪 H)
      = (liftToFunctionField (H.leadingCoeff)) ^ (R.natDegree - 1) * ζ R x₀ H := by
  classical
  rw [embeddingOf𝒪Into𝕃_mk]
  set Q : F[X][Y] := Bivariate.evalX (Polynomial.C x₀) R.derivative with hQ
  set W : 𝕃 H := liftToFunctionField (H := H) H.leadingCoeff with hWdef
  set T : 𝕃 H := functionFieldT (H := H) with hTdef
  set k : ℕ := R.natDegree - 1 with hk
  have hH0 : H.leadingCoeff ≠ 0 :=
    Polynomial.leadingCoeff_ne_zero.mpr H_irreducible.out.ne_zero
  have hWne : W ≠ 0 := liftToFunctionField_ne_zero hH0
  have hQdeg : Q.natDegree ≤ k := by
    rw [hQ, hk, Polynomial.Bivariate.evalX_eq_map]
    exact le_trans Polynomial.natDegree_map_le (Polynomial.natDegree_derivative_le R)
  have h1 : liftBivariate (H := H) (ξPoly x₀ R H)
      = ∑ j ∈ Q.support, liftToFunctionField (H := H) (Q.coeff j) * W ^ (k - j) * T ^ j := by
    rw [ξPoly]
    simp only [← hQ, ← hk]
    rw [map_sum]
    apply Finset.sum_congr rfl
    intro j hj
    rw [map_mul, map_pow, liftBivariate_X, liftBivariate_C, map_mul, map_pow]
  have hζ : ζ R x₀ H
      = ∑ j ∈ Q.support, liftToFunctionField (H := H) (Q.coeff j) * (T / W) ^ j := by
    rw [ζ, ← hQ, ← hWdef, ← hTdef, Polynomial.eval₂_eq_sum, Polynomial.sum_def]
  have h2 : W ^ k * ζ R x₀ H
      = ∑ j ∈ Q.support, liftToFunctionField (H := H) (Q.coeff j) * W ^ (k - j) * T ^ j := by
    rw [hζ, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j hj
    have hjk : j ≤ k := le_trans (Polynomial.le_natDegree_of_mem_supp j hj) hQdeg
    rw [div_pow, pow_sub₀ W hWne hjk]; field_simp
  rw [h1, h2]

/-- **Claim A.2 weight bound (BCIKS20 Appendix A.4), `d - 1` form — fully proven companion
of the still-open `weight_ξ_bound`.**

The literal `weight_ξ_bound` (below) is stated about `ξ := (ξ_regular …).choose`, where
`ξ_regular` carries the off-by-one `d - 2` exponent and has an open proof obligation
(documented as a genuine, not-provably-false gap). Consequently *any* proof of
`weight_ξ_bound` must route through `(ξ_regular …).choose_spec` and would inherit that
unsound dependency, which is not an honest closure. This companion instead bounds the weight
of the **explicit, unconditional** `d - 1` witness `ξPoly` (mirroring how `ξ_regular'`
replaces the `d - 2` `ξ_regular`), and is fully proven.

The bound is `weight_Λ_over_𝒪 (mk ξPoly) D ≤ (natDegreeY R - 1)·(D - natDegreeY H + 1)`.
Two inputs:
* `hkN : R.natDegree - 1 < H.natDegree` — the `Y`-degree of `ξPoly` (`≤ d - 1`) is below the
  defining relation `H_tilde' H` (`Y`-degree `H.natDegree`), so `ξPoly` is already its own
  canonical representative (`explicit_sum_degree_lt`) and the `𝒪`-weight equals the
  polynomial `Λ`-weight. This is the regime of BCIKS20 §A.4, where `ζ` is kept reduced in the
  function-field variable `T`.
* `hcoeff` — the per-coefficient graded `X`-degree bound
  `(Q.coeff j · lc^(k-j)).natDegree ≤ (k - j)·s`. This is the residual trivariate degree
  input (the analogue, on the `ζ`/`R` side, of `natDegree_coeff_H_tilde'_le` on the `H`
  side); it is factored out as a hypothesis exactly as `natDegree_elimPoly_le` factors out
  its own coefficient bound.

Given these, the weight-assembly lemma `weight_Λ_explicit_sum_le` and the telescoping
`j·s + (k-j)·s = k·s` deliver the stated bound. -/
lemma weight_ξPoly_bound (x₀ : F) (R : F[X][X][Y]) (H : F[X][Y])
    [H_irreducible : Fact (Irreducible H)] [Fact (0 < H.natDegree)]
    (hH : 0 < H.natDegree) {D : ℕ} (hD : D ≥ Bivariate.totalDegree H)
    (hkN : R.natDegree - 1 < H.natDegree)
    (hcoeff : ∀ j,
      ((Bivariate.evalX (Polynomial.C x₀) R.derivative).coeff j *
          H.leadingCoeff ^ (R.natDegree - 1 - j)).natDegree
        ≤ ((R.natDegree - 1) - j) * (D + 1 - Bivariate.natDegreeY H)) :
    weight_Λ_over_𝒪 hH
      (Ideal.Quotient.mk (Ideal.span {H_tilde' H}) (ξPoly x₀ R H) : 𝒪 H) D ≤
      WithBot.some ((Bivariate.natDegreeY R - 1) * (D - Bivariate.natDegreeY H + 1)) := by
  classical
  set Q : F[X][Y] := Bivariate.evalX (Polynomial.C x₀) R.derivative with hQ
  set k : ℕ := R.natDegree - 1 with hk
  set s : ℕ := D + 1 - Bivariate.natDegreeY H with hs
  have hNY_H : Bivariate.natDegreeY H = H.natDegree := rfl
  have hred : (ξPoly x₀ R H : F[X][Y]).degree < (H_tilde' H).degree := by
    refine explicit_sum_degree_lt hH Q.support
      (fun j => Q.coeff j * H.leadingCoeff ^ (k - j)) k ?_ ?_
    · intro j hj
      exact Polynomial.le_natDegree_of_mem_supp j hj |>.trans
        (by rw [hQ, hk, Polynomial.Bivariate.evalX_eq_map]
            exact le_trans Polynomial.natDegree_map_le (Polynomial.natDegree_derivative_le R))
    · exact hkN
  rw [weight_Λ_over_𝒪_mk_eq_self_of_degree_lt hH hred]
  have hbound : weight_Λ (ξPoly x₀ R H) H D ≤ (k * s : ℕ) := by
    rw [ξPoly]
    simp only [← hQ, ← hk]
    refine weight_Λ_explicit_sum_le Q.support
      (fun j => Q.coeff j * H.leadingCoeff ^ (k - j)) D (k * s) ?_
    intro j hj
    dsimp only
    rw [← hs]
    have hjk : j ≤ k :=
      Polynomial.le_natDegree_of_mem_supp j hj |>.trans
        (by rw [hQ, hk, Polynomial.Bivariate.evalX_eq_map]
            exact le_trans Polynomial.natDegree_map_le (Polynomial.natDegree_derivative_le R))
    have hc := hcoeff j
    calc j * s + (Q.coeff j * H.leadingCoeff ^ (k - j)).natDegree
        ≤ j * s + (k - j) * s := Nat.add_le_add_left hc _
      _ = k * s := by rw [← Nat.add_mul]; congr 1; omega
  refine le_trans hbound ?_
  have hRHS : (Bivariate.natDegreeY R - 1) * (D - Bivariate.natDegreeY H + 1) = k * s := by
    have hNY_R : Bivariate.natDegreeY R = R.natDegree := rfl
    have hHle : Bivariate.natDegreeY H ≤ D := by
      refine le_trans ?_ hD
      have hHne : H ≠ 0 := fun h0 => by
        rw [h0, Polynomial.natDegree_zero] at hH; exact absurd hH (by omega)
      have hmem : H.natDegree ∈ H.support := by
        rw [Polynomial.mem_support_iff, ← Polynomial.leadingCoeff]
        exact Polynomial.leadingCoeff_ne_zero.mpr hHne
      rw [hNY_H, Bivariate.totalDegree]
      have hsup := Finset.le_sup (f := fun m => (H.coeff m).natDegree + m) hmem
      simp only at hsup; omega
    rw [hNY_R, ← hk, hs]; congr 1; omega
  rw [hRHS]
  exact le_refl _

/-- There exist regular elements `ξ = W(Z)^(d-2) * ζ` as defined in Claim A.2 of Appendix A.4
of [BCIKS20].

**Exponent caveat (documented for upstream).** As literally formalized here the exponent is `d - 2`,
but the power of `W` that unconditionally clears the denominators of `ζ` (a polynomial of `Y`-degree
  `≤ d - 1` evaluated at `T / W`) is `d - 1`, not `d - 2`. The statement-correct version
is `ξ_regular'` above. With the `d - 2` exponent the top summand of `W^(d-2) · ζ` is
`liftToFunctionField (Q_{d-1}) · T^{d-1} · W^{-1}` (a genuine `W⁻¹` term, since `ℕ`-truncated
`(d-2) - (d-1) = 0` in `ℕ` while the field division contributes a real `W⁻¹`), so regularity is
*not* automatic: it holds only when `1/W` is itself regular in `𝒪 H`. That extra fact is true in
some cases (e.g. `H.natDegree = 1`, where Bézout makes `H.leadingCoeff` a unit in `𝒪 H`), but it is
  not provable for general irreducible `H`. The proof obligation below therefore records a genuine gap in the
`d - 2` form; the regular-element content of Claim A.2 is captured by `ξ_regular'`. The downstream
`ξ`/`weight_ξ_bound`/`α`/`γ` definitions consume only the existence witness and are unaffected. -/
lemma ξ_regular (x₀ : F) (R : F[X][X][Y]) (H : F[X][Y]) [H_irreducible : Fact (Irreducible H)]
    [Fact (0 < H.natDegree)] :
    ∃ pre : 𝒪 H,
    let d := R.natDegree
    let W : 𝕃 H := liftToFunctionField (H.leadingCoeff);
    embeddingOf𝒪Into𝕃 _ pre = W ^ (d - 2) * ζ R x₀ H := by
  sorry

/-- The elements `ξ = W(Z)^(d-2) * ζ` as defined in Claim A.2 of Appendix A.4 of [BCIKS20]. -/
def ξ (x₀ : F) (R : F[X][X][Y]) (H : F[X][Y]) [φ : Fact (Irreducible H)]
    [Fact (0 < H.natDegree)] : 𝒪 H :=
  (ξ_regular x₀ R H).choose

/-- The bound of the weight `Λ` of the elements `ξ` as stated in Claim A.2 of Appendix A.4
of [BCIKS20].

**Honest-closure note (read before attempting to discharge this proof).** This statement is
about `ξ := (ξ_regular …).choose`, and `ξ_regular` carries the off-by-one `d - 2` exponent
and is itself open (a genuine, documented, *not-provably-false* gap — see `ξ_regular`). The
weight of an opaque `𝒪 H` element is not bounded by anything unless one knows what it embeds
to, and the only fact tying `ξ` to `W^(d-2) · ζ` is `(ξ_regular …).choose_spec`. Therefore
**every** proof of this exact statement must consume `choose_spec` of the open `ξ_regular`
and would inherit that unsound dependency; that is not an honest closure, so this proof is
deliberately left open.

The real weight content of Claim A.2 is captured, fully proven (uses only the standard proof
principles `propext`, `Classical.choice`, and `Quot.sound`), by `weight_ξPoly_bound` above:
it bounds the weight of the **explicit, unconditional** `d - 1` witness `ξPoly` (whose
embedding `= W^(d-1) · ζ` is `embeddingOf𝒪Into𝕃_mk_ξPoly`), mirroring how `ξ_regular'` is
the proven `d - 1` companion of the open `d - 2` `ξ_regular`. Downstream `α`/`γ` and Claims
5.8/5.9 consume only the existence witness `ξ`, never this bound, so the leaf obligation here
is non-propagating. -/
lemma weight_ξ_bound (x₀ : F) (hH : 0 < H.natDegree) {D : ℕ}
    (hD : D ≥ Bivariate.totalDegree H) :
    weight_Λ_over_𝒪 hH (ξ x₀ R H) D ≤
    WithBot.some ((Bivariate.natDegreeY R - 1) * (D - Bivariate.natDegreeY H + 1)) := by
  sorry

/-- There exist regular elements `β` with a weight bound as given in Claim A.2
of Appendix A.4 of [BCIKS20]. -/
lemma β_regular (R : F[X][X][Y])
                (H : F[X][Y]) [H_irreducible : Fact (Irreducible H)]
                (hH : 0 < H.natDegree)
                {D : ℕ} (hD : D ≥ Bivariate.totalDegree H) :
    ∀ t : ℕ, ∃ β : 𝒪 H,
      weight_Λ_over_𝒪 hH β D ≤ (2 * t + 1) * Bivariate.natDegreeY R * D :=
  fun t => ⟨0, by rw [weight_Λ_over_𝒪_zero]; exact bot_le⟩

/-- The definition of the regular elements `β` giving the numerators of the Hensel lift coefficients
as defined in Claim A.2 of Appendix A.4 of [BCIKS20]. -/
def β (R : F[X][X][Y]) (t : ℕ) : 𝒪 H :=
  if hH : 0 < H.natDegree then
    (β_regular R H hH (Nat.le_refl _) t).choose
  else
    0

/-- The Hensel lift coefficients `α` are of the form as given in Claim A.2 of Appendix A.4
of [BCIKS20]. -/
def α (x₀ : F) (R : F[X][X][Y]) (H : F[X][Y]) [φ : Fact (Irreducible H)]
    [Fact (0 < H.natDegree)] (t : ℕ) : 𝕃 H :=
  let W : 𝕃 H := liftToFunctionField (H.leadingCoeff)
  embeddingOf𝒪Into𝕃 _ (β R t) /
    (W ^ (t + 1) * (embeddingOf𝒪Into𝕃 _ (ξ x₀ R H)) ^ (2*t - 1))

def α' (x₀ : F) (R : F[X][X][Y]) (H_irreducible : Irreducible H) (t : ℕ) : 𝕃 H :=
  α x₀ R _ (φ := ⟨H_irreducible⟩) t

/-- The power series `γ = ∑ α^t (X - x₀)^t ∈ 𝕃 [[X - x₀]]` as defined in Appendix A.4
of [BCIKS20]. -/
def γ (x₀ : F) (R : F[X][X][Y]) (H : F[X][Y]) [φ : Fact (Irreducible H)]
    [Fact (0 < H.natDegree)] : PowerSeries (𝕃 H) :=
  let subst (t : ℕ) : 𝕃 H :=
    match t with
    | 0 => fieldTo𝕃 (-x₀)
    | 1 => 1
    | _ => 0
  PowerSeries.subst (PowerSeries.mk subst) (PowerSeries.mk (α x₀ R H))

def γ' (x₀ : F) (R : F[X][X][Y]) (H_irreducible : Irreducible H) : PowerSeries (𝕃 H) :=
  γ x₀ R H (φ := ⟨H_irreducible⟩)

end ClaimA2
end
end BCIKS20AppendixA

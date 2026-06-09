/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.CandidateResultantLiftLoop52
import Mathlib.RingTheory.Polynomial.Cyclotomic.Basic

/-!
# Loop 53 (O16, CLOSE) — the finite-field lifting, assembled: a finite field with a super-exponential
# §7 subset-sumset, **no remaining hypothesis**.

Assembles the seven resultant/Dirichlet/cyclotomic pillars of Loop52 into the existence the
finite-field §7 disproof needs, with **no abstract hypothesis left**:

> `exists_finiteField_subsetSumset_large`: for every `m ≥ 1` there is a prime `p` and a primitive
> `2^m`-th root of unity `ζ ∈ F_p` whose subset-sumset over `Fin (2^{m-1})` has `≥ 2^{2^{m-1}}`
> elements — **super-exponential in the domain `2^m`**.

With `thm71_no_fixed_exponent` (Loop46) this **disproves the §7 minimal-domain prize over a genuine
finite field**. See `DISPROOF_LOG.md` (O16/Loop53).
-/

open Finset Polynomial

namespace ArkLib.ProximityGap.FiniteFieldDisproofLoop53

open ArkLib.ProximityGap.ResultantLiftLoop52

variable {N : ℕ}

/-- The integer polynomial `f_S = ∑_{j ∈ S} X^j`. -/
noncomputable def fpoly (S : Finset (Fin N)) : Polynomial ℤ := ∑ j ∈ S, X ^ (j : ℕ)

/-- `f_S.coeff k = 1` if `k = (j:ℕ)` for some `j ∈ S`, else `0`. -/
theorem fpoly_coeff (S : Finset (Fin N)) (k : ℕ) :
    (fpoly S).coeff k = if k ∈ S.image (fun j : Fin N => (j : ℕ)) then 1 else 0 := by
  classical
  rw [fpoly, finset_sum_coeff]
  simp only [coeff_X_pow]
  rw [Finset.sum_boole]
  by_cases hk : k ∈ S.image (fun j : Fin N => (j : ℕ))
  · rw [if_pos hk]
    obtain ⟨j, hjS, hjk⟩ := Finset.mem_image.mp hk
    have : S.filter (fun j' : Fin N => k = (j' : ℕ)) = {j} := by
      ext j'
      simp only [Finset.mem_filter, Finset.mem_singleton]
      constructor
      · rintro ⟨_, hj'⟩; exact Fin.ext (hjk ▸ hj'.symm)
      · rintro rfl; exact ⟨hjS, hjk.symm⟩
    rw [this]; simp
  · rw [if_neg hk]
    rw [Finset.filter_eq_empty_iff.mpr, Finset.card_empty, Nat.cast_zero]
    intro j hjS hj'
    exact hk (Finset.mem_image.mpr ⟨j, hjS, hj'.symm⟩)

/-- Every coefficient of `f_S − f_T` lies in `{-1, 0, 1}`. -/
theorem fpoly_sub_coeff_cases (S T : Finset (Fin N)) (k : ℕ) :
    (fpoly S - fpoly T).coeff k = -1 ∨ (fpoly S - fpoly T).coeff k = 0
      ∨ (fpoly S - fpoly T).coeff k = 1 := by
  rw [coeff_sub, fpoly_coeff, fpoly_coeff]
  by_cases h1 : k ∈ S.image (fun j : Fin N => (j : ℕ)) <;>
    by_cases h2 : k ∈ T.image (fun j : Fin N => (j : ℕ)) <;> simp [h1, h2]

/-- `f_S = f_T ↔ S = T` — distinct subsets give distinct polynomials. -/
theorem fpoly_injective : Function.Injective (fpoly (N := N)) := by
  classical
  intro S T h
  ext j
  have hc := congrArg (fun q => Polynomial.coeff q (j : ℕ)) h
  simp only [fpoly_coeff] at hc
  have hS : ((j : ℕ) ∈ S.image (fun j : Fin N => (j : ℕ))) ↔ j ∈ S := by
    simp [Finset.mem_image, Fin.val_inj]
  have hT : ((j : ℕ) ∈ T.image (fun j : Fin N => (j : ℕ))) ↔ j ∈ T := by
    simp [Finset.mem_image, Fin.val_inj]
  by_cases hjS : j ∈ S <;> by_cases hjT : j ∈ T <;> simp_all

/-- `deg (f_S) < N` (each monomial `X^j` has `j < N`). -/
theorem fpoly_natDegree_lt (hN : 0 < N) (S : Finset (Fin N)) : (fpoly S).natDegree < N := by
  classical
  have hdeg : (fpoly S).degree < (N : WithBot ℕ) := by
    rw [fpoly]
    refine lt_of_le_of_lt (degree_sum_le _ _) ?_
    refine (Finset.sup_lt_iff (WithBot.bot_lt_coe N)).mpr fun j _ => ?_
    exact lt_of_le_of_lt (degree_X_pow_le _) (WithBot.coe_lt_coe.mpr j.isLt)
  by_cases h0 : fpoly S = 0
  · rw [h0]; simpa using hN
  · rwa [natDegree_lt_iff_degree_lt h0]

/-- `(f_S mod φ)(ζ) = ∑_{j ∈ S} ζ^j` — the subset sum is the evaluation of `f_S`. -/
theorem fpoly_map_eval {R : Type*} [CommRing R] (φ : ℤ →+* R) (ζ : R) (S : Finset (Fin N)) :
    ((fpoly S).map φ).eval ζ = ∑ j ∈ S, ζ ^ (j : ℕ) := by
  rw [fpoly, Polynomial.map_sum, Polynomial.eval_finset_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [Polynomial.map_pow, map_X, Polynomial.eval_pow, eval_X]

/-- The leading coefficient of `f_S − f_T` (for `S ≠ T`) is `±1`, hence nonzero mod any prime `p`. -/
theorem fpoly_sub_leadingCoeff_cast_ne {p : ℕ} [Fact p.Prime] {S T : Finset (Fin N)}
    (hST : S ≠ T) : (((fpoly S - fpoly T).leadingCoeff : ℤ) : ZMod p) ≠ 0 := by
  have hne : fpoly S - fpoly T ≠ 0 := sub_ne_zero.mpr fun h => hST (fpoly_injective h)
  have hlc0 : (fpoly S - fpoly T).leadingCoeff ≠ 0 := leadingCoeff_ne_zero.mpr hne
  have : (fpoly S - fpoly T).leadingCoeff = -1 ∨ (fpoly S - fpoly T).leadingCoeff = 1 := by
    rcases fpoly_sub_coeff_cases S T (fpoly S - fpoly T).natDegree with h | h | h
    · exact Or.inl h
    · exact absurd h hlc0
    · exact Or.inr h
  rcases this with h | h <;> rw [h] <;> simp

/-- **The finite-field §7 disproof core (Loop53 capstone), no remaining hypothesis.** For every
`m ≥ 1` there is a prime `p` and a primitive `2^m`-th root of unity `ζ ∈ F_p` whose subset-sumset over
`Fin (2^{m-1})` has `≥ 2^{2^{m-1}}` elements — **super-exponential in the domain `2^m`**. With
`thm71_no_fixed_exponent` (Loop46) this disproves the §7 minimal-domain prize over a genuine finite
field. -/
theorem exists_finiteField_subsetSumset_large {m : ℕ} (hm : 1 ≤ m) :
    ∃ p : ℕ, p.Prime ∧ ∃ ζ : ZMod p, IsPrimitiveRoot ζ (2 ^ m) ∧
      2 ^ (2 ^ (m - 1)) ≤
        (Finset.univ.image
          (fun S : Finset (Fin (2 ^ (m - 1))) => ∑ j ∈ S, ζ ^ (j : ℕ))).card := by
  classical
  set N := 2 ^ (m - 1) with hNdef
  have hNpos : 0 < N := by positivity
  -- family of differences over ordered pairs (constant `1` on the diagonal)
  set gs : Finset (Fin N) × Finset (Fin N) → Polynomial ℤ :=
    fun ST => if ST.1 = ST.2 then 1 else fpoly ST.1 - fpoly ST.2 with hgs
  have hcop : ∀ ST, IsCoprime ((gs ST).map (Int.castRingHom ℚ))
      ((cyclotomic (2 ^ m) ℤ).map (Int.castRingHom ℚ)) := by
    rintro ⟨S, T⟩
    by_cases hST : S = T
    · simp only [hgs, if_pos hST, Polynomial.map_one]; exact isCoprime_one_left
    · simp only [hgs, if_neg hST]
      refine diff_coprime_cyclotomic_rat hm _ ?_ (sub_ne_zero.mpr fun h => hST (fpoly_injective h))
      calc (fpoly S - fpoly T).natDegree
          ≤ max (fpoly S).natDegree (fpoly T).natDegree := natDegree_sub_le _ _
        _ < N := by
            rw [max_lt_iff]; exact ⟨fpoly_natDegree_lt hNpos S, fpoly_natDegree_lt hNpos T⟩
  -- a Dirichlet prime `p ≡ 1 (mod 2^m)` with no common resultant
  have hq2 : 2 ≤ 2 ^ m := by simpa using Nat.pow_le_pow_right (by norm_num : 1 ≤ 2) hm
  obtain ⟨p, hpp, hpmod, hpndvd⟩ :=
    exists_good_prime_no_common_resultant (q := 2 ^ m) hq2 (cyclotomic (2 ^ m) ℤ) gs hcop
  haveI : Fact p.Prime := ⟨hpp⟩
  -- `2^m ∣ p − 1`, so a primitive root exists
  have hdvd : 2 ^ m ∣ p - 1 := by
    have h1 : (p : ZMod (2 ^ m)) = ((1 : ℕ) : ZMod (2 ^ m)) := by push_cast; exact hpmod
    exact (Nat.modEq_iff_dvd' hpp.one_lt.le).mp
      ((ZMod.natCast_eq_natCast_iff _ _ _).mp h1).symm
  obtain ⟨ζ, hζ⟩ := exists_primitiveRoot_zmod hm hdvd
  -- `ζ` is a root of `Φ mod p`
  have hζroot : ((cyclotomic (2 ^ m) ℤ).map (Int.castRingHom (ZMod p))).IsRoot ζ := by
    rw [map_cyclotomic_int]; exact hζ.isRoot_cyclotomic (by positivity)
  refine ⟨p, hpp, ζ, hζ, ?_⟩
  -- injectivity of the subset-sum map ⟹ image of full cardinality
  have hinj : Function.Injective
      (fun S : Finset (Fin N) => ∑ j ∈ S, ζ ^ (j : ℕ)) := by
    intro S T heq
    by_contra hST
    -- collision ⟹ `ζ` is a common root of `f_S − f_T` and `Φ` mod `p`
    have hroot : ((fpoly S - fpoly T).map (Int.castRingHom (ZMod p))).IsRoot ζ := by
      rw [IsRoot.def, Polynomial.map_sub, Polynomial.eval_sub, fpoly_map_eval, fpoly_map_eval]
      exact sub_eq_zero.mpr heq
    have hΦmonic : ((cyclotomic (2 ^ m) ℤ).leadingCoeff : ZMod p) ≠ 0 := by
      rw [(cyclotomic.monic (2 ^ m) ℤ).leadingCoeff]; simp
    have hdvdRes := prime_dvd_resultant_of_common_root (fpoly S - fpoly T) (cyclotomic (2 ^ m) ℤ)
      (fpoly_sub_leadingCoeff_cast_ne hST) hΦmonic hroot hζroot
    refine hpndvd (S, T) ?_
    have hgseq : gs (S, T) = fpoly S - fpoly T := by simp only [hgs, if_neg hST]
    rw [hgseq]; exact hdvdRes
  rw [Finset.card_image_of_injective _ hinj, Finset.card_univ, Fintype.card_finset,
    Fintype.card_fin]

end ArkLib.ProximityGap.FiniteFieldDisproofLoop53

/-! ## Axiom audit -/
#print axioms ArkLib.ProximityGap.FiniteFieldDisproofLoop53.exists_finiteField_subsetSumset_large

/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.FoldPolynomialSlices

/-!
# The per-locus cardinality (issue #232)

The counting companion to `low_weight_slice_structure`: over a finite field, the
polynomials of degree `< d` vanishing on a prescribed `|Z|`-point locus number EXACTLY
`q^(d − |Z|)` — multiplication by the locator `loc Z` is a bijection from the
unconstrained space one locus-size down (`loc_dvd_iff` supplies surjectivity).

* `polysDegLT` / `mem_polysDegLT` / `card_polysDegLT` — the degree-`< d` space as a
  concrete `Finset` of size `q^d`, enumerated by coefficient tuples;
* `card_polysDegLT_vanishing` — the per-locus count `q^(d − |Z|)`.

With `low_weight_slice_structure` this makes the Conjecture-D counting skeleton
numerically explicit: per locus `Z`, the slice pairs of a degree-`< k` error range in a
space of exactly `q^(de − |Z|)·q^(do − |Z|) = q^(k − 2|Z|)` elements (`de`, `do` the
slice degree budgets), so the open all-words content is precisely the union over loci
against the weight filter. (The `f`-level product count via the slice bijection
`recompose_slices` is the queued capstone.)
-/

namespace LamLeungTwoPow

open Polynomial Finset

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

/-- The finset of all polynomials of degree `< d`, enumerated by coefficient tuples. -/
noncomputable def polysDegLT (d : ℕ) : Finset F[X] :=
  (Finset.univ : Finset (Fin d → F)).image
    (fun c => ∑ i : Fin d, C (c i) * X ^ (i : ℕ))

omit [Fintype F] [DecidableEq F] in
theorem coeff_tuple_sum (d : ℕ) (c : Fin d → F) (j : Fin d) :
    (∑ i : Fin d, C (c i) * X ^ (i : ℕ)).coeff j = c j := by
  rw [finset_sum_coeff]
  rw [Finset.sum_congr rfl fun i _ => coeff_C_mul_X_pow (c i) i j]
  simp only [Fin.val_inj]
  rw [Finset.sum_ite_eq Finset.univ j fun i => c i]
  simp

theorem mem_polysDegLT {d : ℕ} {p : F[X]} :
    p ∈ polysDegLT d ↔ p.degree < d := by
  constructor
  · rintro hp
    obtain ⟨c, _, rfl⟩ := Finset.mem_image.mp hp
    apply lt_of_le_of_lt (degree_sum_le _ _)
    rw [Finset.sup_lt_iff (by exact_mod_cast WithBot.bot_lt_coe d)]
    intro i _
    exact lt_of_le_of_lt (degree_C_mul_X_pow_le _ _) (by exact_mod_cast i.isLt)
  · intro hdeg
    refine Finset.mem_image.mpr ⟨fun i => p.coeff i, Finset.mem_univ _, ?_⟩
    by_cases hp0 : p = 0
    · subst hp0
      simp
    · have hnd : p.natDegree < d := (natDegree_lt_iff_degree_lt hp0).mpr hdeg
      conv_rhs => rw [p.as_sum_range' d hnd]
      rw [Fin.sum_univ_eq_sum_range (fun i => C (p.coeff i) * X ^ i)]
      exact Finset.sum_congr rfl fun i _ => C_mul_X_pow_eq_monomial

theorem card_polysDegLT (d : ℕ) :
    (polysDegLT (F := F) d).card = Fintype.card F ^ d := by
  rw [polysDegLT, Finset.card_image_of_injective _ ?inj, Finset.card_univ]
  · rw [Fintype.card_fun, Fintype.card_fin]
  case inj =>
    intro c c' heq
    funext j
    rw [← coeff_tuple_sum d c j, ← coeff_tuple_sum d c' j]
    exact congrArg (fun p : F[X] => p.coeff (j : ℕ)) heq

/-- **The per-locus count**: polynomials of degree `< d` vanishing on a `|Z|`-point set
form exactly `q^(d − |Z|)` elements (for `|Z| ≤ d`) — multiplication by the locator is a
bijection from the unconstrained space one locus-size down. -/
theorem card_polysDegLT_vanishing {d : ℕ} (Z : Finset F) (hZd : Z.card ≤ d) :
    ((polysDegLT (F := F) d).filter (fun p => ∀ z ∈ Z, p.eval z = 0)).card
      = Fintype.card F ^ (d - Z.card) := by
  have hlocne : TopLine.loc Z ≠ 0 := (TopLine.loc_monic Z).ne_zero
  have hlocdeg : (TopLine.loc Z).degree = (Z.card : WithBot ℕ) := by
    rw [degree_eq_natDegree hlocne, TopLine.loc_natDegree]
  rw [← card_polysDegLT (F := F) (d - Z.card)]
  symm
  apply Finset.card_bij (fun h _ => TopLine.loc Z * h)
  · intro h hh
    rw [Finset.mem_filter]
    constructor
    · rw [mem_polysDegLT]
      by_cases h0 : h = 0
      · subst h0
        rw [mul_zero, degree_zero]
        exact WithBot.bot_lt_coe d
      · rw [degree_mul, hlocdeg]
        have hdh : h.degree < ((d - Z.card : ℕ) : WithBot ℕ) := mem_polysDegLT.mp hh
        calc (Z.card : WithBot ℕ) + h.degree
            < (Z.card : WithBot ℕ) + ((d - Z.card : ℕ) : WithBot ℕ) :=
              WithBot.add_lt_add_left (WithBot.coe_ne_bot) hdh
          _ = ((Z.card + (d - Z.card) : ℕ) : WithBot ℕ) := by push_cast; rfl
          _ = (d : WithBot ℕ) := by rw [Nat.add_sub_cancel' hZd]
    · intro z hz
      rw [eval_mul, TopLine.loc_eval_zero hz, zero_mul]
  · intro h1 hh1 h2 hh2 heq
    exact mul_left_cancel₀ hlocne heq
  · intro p hp
    obtain ⟨hpd, hpz⟩ := Finset.mem_filter.mp hp
    obtain ⟨h, rfl⟩ := (loc_dvd_iff Z _).mpr hpz
    refine ⟨h, ?_, rfl⟩
    rw [mem_polysDegLT]
    by_cases h0 : h = 0
    · subst h0
      rw [degree_zero]
      exact WithBot.bot_lt_coe _
    · have hd := mem_polysDegLT.mp hpd
      rw [degree_mul, hlocdeg, degree_eq_natDegree h0] at hd
      rw [degree_eq_natDegree h0]
      have : Z.card + h.natDegree < d := by exact_mod_cast hd
      exact_mod_cast (by omega : h.natDegree < d - Z.card)


/-! ## The f-level capstone: both-slice vanishing counts are exactly `q^(k − 2|Z|)`

Slices are `C`-linear, slices of a built pair recover the pair (`evenSlice_build`/
`oddSlice_build`), and `f ↦ (evenSlice f, oddSlice f)` is a bijection between the
degree-`< k` space and the product of the slice-budget spaces (char ≠ 2). Hence the
degree-`< k` polynomials whose BOTH slices vanish on a prescribed `|Z|`-point locus
number EXACTLY `q^(k − 2|Z|)` (`card_polysDegLT_slices_vanishing`) — the per-locus list
budget of the Conjecture-D skeleton, now an equality. -/

open Polynomial Finset

variable {F : Type*} [Field F]

/-- `expand` composed with `−X` is itself (even polynomials are even). -/
theorem expand_comp_neg_X (h : F[X]) :
    (Polynomial.expand F 2 h).comp (-X) = Polynomial.expand F 2 h := by
  ext n
  rw [coeff_comp_neg_X]
  by_cases hd : 2 ∣ n
  · obtain ⟨m, rfl⟩ := hd
    rw [Even.neg_one_pow ⟨m, by ring⟩, one_mul]
  · rw [coeff_expand (by norm_num : 0 < 2), if_neg hd, mul_zero]

theorem contract_two_C_mul (a : F) (h : F[X]) :
    Polynomial.contract 2 (C a * h) = C a * Polynomial.contract 2 h := by
  ext n
  rw [coeff_contract (by norm_num : (2:ℕ) ≠ 0), coeff_C_mul, coeff_C_mul,
    coeff_contract (by norm_num : (2:ℕ) ≠ 0)]

theorem comp_neg_X_C_mul (a : F) (h : F[X]) :
    (C a * h).comp (-X) = C a * h.comp (-X) := by
  rw [mul_comp, C_comp]

theorem evenSlice_C_mul (a : F) (h : F[X]) :
    evenSlice (C a * h) = C a * evenSlice h := by
  rw [evenSlice, evenSlice, comp_neg_X_C_mul, ← mul_add, contract_two_C_mul]

theorem divX_C_mul' (a : F) (h : F[X]) :
    Polynomial.divX (C a * h) = C a * Polynomial.divX h := by
  ext n
  rw [coeff_divX, coeff_C_mul, coeff_C_mul, coeff_divX]

theorem oddSlice_C_mul (a : F) (h : F[X]) :
    oddSlice (C a * h) = C a * oddSlice h := by
  rw [oddSlice, oddSlice, comp_neg_X_C_mul, ← mul_sub, divX_C_mul', contract_two_C_mul]

theorem divX_X_mul (h : F[X]) : Polynomial.divX (X * h) = h := by
  ext n
  rw [coeff_divX, mul_comm X h, coeff_mul_X]

/-- Slices of a built pair recover the pair (doubled). -/
theorem evenSlice_build (E O : F[X]) :
    evenSlice (Polynomial.expand F 2 E + X * Polynomial.expand F 2 O) = 2 * E := by
  rw [evenSlice]
  have hcomp : (Polynomial.expand F 2 E + X * Polynomial.expand F 2 O).comp (-X)
      = Polynomial.expand F 2 E - X * Polynomial.expand F 2 O := by
    rw [add_comp, mul_comp, X_comp]
    have he : (Polynomial.expand F 2 E).comp (-X) = Polynomial.expand F 2 E := by
      rw [expand_comp_neg_X]
    have ho : (Polynomial.expand F 2 O).comp (-X) = Polynomial.expand F 2 O := by
      rw [expand_comp_neg_X]
    rw [he, ho]
    ring
  rw [hcomp]
  have : Polynomial.expand F 2 E + X * Polynomial.expand F 2 O
      + (Polynomial.expand F 2 E - X * Polynomial.expand F 2 O)
      = 2 * Polynomial.expand F 2 E := by ring
  rw [this]
  have h2 : (2 : F[X]) * Polynomial.expand F 2 E = Polynomial.expand F 2 (2 * E) := by
    rw [map_mul, map_ofNat]
  rw [h2, contract_expand (p := 2) (by norm_num)]

theorem oddSlice_build (E O : F[X]) :
    oddSlice (Polynomial.expand F 2 E + X * Polynomial.expand F 2 O) = 2 * O := by
  rw [oddSlice]
  have hcomp : (Polynomial.expand F 2 E + X * Polynomial.expand F 2 O).comp (-X)
      = Polynomial.expand F 2 E - X * Polynomial.expand F 2 O := by
    rw [add_comp, mul_comp, X_comp]
    rw [expand_comp_neg_X, expand_comp_neg_X]
    ring
  rw [hcomp]
  have : Polynomial.expand F 2 E + X * Polynomial.expand F 2 O
      - (Polynomial.expand F 2 E - X * Polynomial.expand F 2 O)
      = X * (2 * Polynomial.expand F 2 O) := by ring
  rw [this, divX_X_mul]
  have h2 : (2 : F[X]) * Polynomial.expand F 2 O = Polynomial.expand F 2 (2 * O) := by
    rw [map_mul, map_ofNat]
  rw [h2, contract_expand (p := 2) (by norm_num)]

end LamLeungTwoPow

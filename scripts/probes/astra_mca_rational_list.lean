/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.CoveragePigeonhole
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.Tactic

/-!
# A four-profile rational list bound at the first MCA step

The results concern finite rational-profile lists and their agreement sets.
They do not assert the full MCA safety theorem or its source-lifting steps.
-/

set_option autoImplicit false
set_option maxHeartbeats 800000

namespace AstraMcaRationalList

open Polynomial Finset

/-- The sharp five-set incidence obstruction, with exact-size trimming. -/
theorem five_sets_impossible_of_gap {ι : Type*} [Fintype ι] [DecidableEq ι]
    (a b : ℕ) (S : Fin 5 → Finset ι)
    (hlarge : ∀ i, a ≤ (S i).card)
    (hpair : ∀ i j, i ≠ j → (S i ∩ S j).card ≤ b)
    (hgap : Fintype.card ι * (a + 4 * b) < 5 * a ^ 2) : False := by
  classical
  choose T hsub hsize using fun i => Finset.exists_subset_card_eq (hlarge i)
  have hpairT : ∀ i j, i ≠ j → (T i ∩ T j).card ≤ b := by
    intro i j hij
    exact (Finset.card_le_card (Finset.inter_subset_inter (hsub i) (hsub j))).trans
      (hpair i j hij)
  have hrow : ∀ i : Fin 5, (∑ j : Fin 5, (T i ∩ T j).card) ≤
      a + 4 * b := by
    intro i
    have he := Finset.sum_erase_add (Finset.univ : Finset (Fin 5))
      (fun j => (T i ∩ T j).card) (Finset.mem_univ i)
    have hb : (∑ j ∈ (Finset.univ : Finset (Fin 5)).erase i, (T i ∩ T j).card)
        ≤ 4 * b := by
      calc
        _ ≤ ((Finset.univ : Finset (Fin 5)).erase i).card • b :=
          Finset.sum_le_card_nsmul _ _ _ fun j hj =>
            hpairT i j (Finset.ne_of_mem_erase hj).symm
        _ = _ := by simp
    dsimp only at he
    rw [Finset.inter_self, hsize i] at he
    omega
  have hsum : (∑ i : Fin 5, (T i).card) = 5 * a := by
    simp only [hsize, Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul]
  have hupper : (∑ i : Fin 5, ∑ j : Fin 5, (T i ∩ T j).card) ≤
      5 * (a + 4 * b) := by
    calc
      _ ≤ ∑ _i : Fin 5, (a + 4 * b) :=
        Finset.sum_le_sum fun i _ => hrow i
      _ = _ := by simp
  have hCS := ArkLib.Coverage.sq_sum_card_le_card_mul_sum_inter T
  rw [hsum] at hCS
  have hmain := hCS.trans (Nat.mul_le_mul_left (Fintype.card ι) hupper)
  nlinarith

/-- Exact positive gap for the degree-one first-step profile list. -/
theorem degree_one_gap (s : ℕ) (hs : 52 ≤ s) :
    (4 * s) * ((3 * s - 2) + 4 * (2 * s)) < 5 * (3 * s - 2) ^ 2 := by
  have hr : 3 * s - 2 + 2 = 3 * s := Nat.sub_add_cancel (by omega)
  have hr2 := congrArg (fun a : ℕ => a ^ 2) hr
  have hprod : 52 * s ≤ s * s := Nat.mul_le_mul_right s hs
  nlinarith

/-- Exact positive gap for degree-two denominators and one fewer agreement. -/
theorem degree_two_gap (s : ℕ) (hs : 94 ≤ s) :
    (4 * s) * ((3 * s - 3) + 4 * (2 * s + 1)) < 5 * (3 * s - 3) ^ 2 := by
  have hr : 3 * s - 3 + 3 = 3 * s := Nat.sub_add_cancel (by omega)
  have hr2 := congrArg (fun a : ℕ => a ^ 2) hr
  have hprod : 94 * s ≤ s * s := Nat.mul_le_mul_right s hs
  nlinarith

/-- Five sufficiently large sets with the specified pairwise intersections
cannot occur on a domain of size `4*s`. -/
theorem five_sets_impossible {ι : Type*} [Fintype ι] [DecidableEq ι]
    (s : ℕ) (hs : 52 ≤ s) (hcard : Fintype.card ι = 4 * s)
    (S : Fin 5 → Finset ι)
    (hlarge : ∀ i, 3 * s - 2 ≤ (S i).card)
    (hpair : ∀ i j, i ≠ j → (S i ∩ S j).card ≤ 2 * s) : False := by
  apply five_sets_impossible_of_gap (3 * s - 2) (2 * s) S hlarge hpair
  rw [hcard]
  exact degree_one_gap s hs

/-- The gap form of the finite indexed four-set bound. -/
theorem indexed_sets_card_le_four_of_gap {κ ι : Type*} [Fintype κ] [Fintype ι]
    [DecidableEq ι] (a b : ℕ) (S : κ → Finset ι)
    (hlarge : ∀ i, a ≤ (S i).card)
    (hpair : ∀ i j, i ≠ j → (S i ∩ S j).card ≤ b)
    (hgap : Fintype.card ι * (a + 4 * b) < 5 * a ^ 2) :
    Fintype.card κ ≤ 4 := by
  classical
  by_contra h
  have hfive : Fintype.card (Fin 5) ≤ Fintype.card κ := by simp; omega
  obtain ⟨e⟩ := Function.Embedding.nonempty_of_card_le hfive
  exact five_sets_impossible_of_gap a b (fun i => S (e i)) (fun i => hlarge (e i))
    (fun i j hij => hpair (e i) (e j) (fun he => hij (e.injective he))) hgap

/-- A finite indexed family with these agreement and intersection bounds
has at most four indices. -/
theorem indexed_sets_card_le_four {κ ι : Type*} [Fintype κ] [Fintype ι]
    [DecidableEq ι] (s : ℕ) (hs : 52 ≤ s) (hcard : Fintype.card ι = 4 * s)
    (S : κ → Finset ι) (hlarge : ∀ i, 3 * s - 2 ≤ (S i).card)
    (hpair : ∀ i j, i ≠ j → (S i ∩ S j).card ≤ 2 * s) :
    Fintype.card κ ≤ 4 := by
  apply indexed_sets_card_le_four_of_gap (3 * s - 2) (2 * s) S hlarge hpair
  rw [hcard]
  exact degree_one_gap s hs

/-- Agreement of two rational representatives forces roots of their cross
numerator, independently of the finiteness of the coefficient field. -/
theorem rational_agreement_inter_card_le {F ι : Type*} [Field F]
    [DecidableEq ι] (dom : ι ↪ F) (w : ι → F)
    (a b c d : F[X]) (S T : Finset ι) (k : ℕ)
    (hne : a * d - c * b ≠ 0) (hdegree : (a * d - c * b).natDegree ≤ k)
    (hb : ∀ x ∈ S, b.eval (dom x) ≠ 0)
    (hd : ∀ x ∈ T, d.eval (dom x) ≠ 0)
    (ha : ∀ x ∈ S, a.eval (dom x) / b.eval (dom x) = w x)
    (hc : ∀ x ∈ T, c.eval (dom x) / d.eval (dom x) = w x) :
    (S ∩ T).card ≤ k := by
  classical
  by_contra h
  apply hne
  apply Polynomial.eq_zero_of_natDegree_lt_card_of_eval_eq_zero'
    (a * d - c * b) ((S ∩ T).image dom)
  · intro y hy
    obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hy
    have hxS := (Finset.mem_inter.mp hx).1
    have hxT := (Finset.mem_inter.mp hx).2
    have hax := (div_eq_iff (hb x hxS)).mp (ha x hxS)
    have hcx := (div_eq_iff (hd x hxT)).mp (hc x hxT)
    simp only [Polynomial.eval_sub, Polynomial.eval_mul, hax, hcx]
    ring
  · rw [Finset.card_image_of_injective _ dom.injective]
    omega

/-- A general finite rational-profile list bound from a strict incidence gap.
No list-size premise is accepted: the gap is ordinary integer arithmetic. -/
theorem rational_profile_list_le_four_of_gap {F κ ι : Type*} [Field F]
    [Fintype κ] [Fintype ι] [DecidableEq ι]
    (dom : ι ↪ F) (w : ι → F) (numDegree denDegree agreements : ℕ)
    (num den : κ → F[X]) (S : κ → Finset ι)
    (hnum : ∀ i, (num i).natDegree ≤ numDegree)
    (hden : ∀ i, (den i).natDegree ≤ denDegree)
    (hsep : ∀ i j, i ≠ j → num i * den j - num j * den i ≠ 0)
    (hlarge : ∀ i, agreements ≤ (S i).card)
    (hnonzero : ∀ i x, x ∈ S i → (den i).eval (dom x) ≠ 0)
    (hagree : ∀ i x, x ∈ S i →
      (num i).eval (dom x) / (den i).eval (dom x) = w x)
    (hgap : Fintype.card ι * (agreements + 4 * (numDegree + denDegree)) <
      5 * agreements ^ 2) :
    Fintype.card κ ≤ 4 := by
  apply indexed_sets_card_le_four_of_gap agreements (numDegree + denDegree) S hlarge
    (hgap := hgap)
  intro i j hij
  apply rational_agreement_inter_card_le dom w (num i) (den i) (num j) (den j)
    (S i) (S j) (numDegree + denDegree) (hsep i j hij)
  · apply (Polynomial.natDegree_sub_le _ _).trans
    apply max_le
    · have hmul := Polynomial.natDegree_mul_le (p := num i) (q := den j)
      have hi := hnum i
      have hj := hden j
      omega
    · have hmul := Polynomial.natDegree_mul_le (p := num j) (q := den i)
      have hj := hnum j
      have hi := hden i
      omega
  · exact hnonzero i
  · exact hnonzero j
  · exact hagree i
  · exact hagree j

/-- The numerical rational-profile list bound used by the written two-source
argument. Pairwise nonzero cross numerators express distinct rational profiles;
denominators are required nonzero only on their own agreement supports. -/
theorem rational_profile_list_le_four {F κ ι : Type*} [Field F]
    [Fintype κ] [Fintype ι] [DecidableEq ι]
    (dom : ι ↪ F) (w : ι → F) (s : ℕ) (hs : 52 ≤ s)
    (hcard : Fintype.card ι = 4 * s)
    (num den : κ → F[X]) (S : κ → Finset ι)
    (hnum : ∀ i, (num i).natDegree ≤ 2 * s - 1)
    (hden : ∀ i, (den i).natDegree ≤ 1)
    (hsep : ∀ i j, i ≠ j → num i * den j - num j * den i ≠ 0)
    (hlarge : ∀ i, 3 * s - 2 ≤ (S i).card)
    (hnonzero : ∀ i x, x ∈ S i → (den i).eval (dom x) ≠ 0)
    (hagree : ∀ i x, x ∈ S i →
      (num i).eval (dom x) / (den i).eval (dom x) = w x) :
    Fintype.card κ ≤ 4 := by
  apply rational_profile_list_le_four_of_gap dom w (2 * s - 1) 1 (3 * s - 2)
    num den S hnum hden hsep hlarge hnonzero hagree
  have hd : 2 * s - 1 + 1 = 2 * s := Nat.sub_add_cancel (by omega)
  rw [hcard, hd]
  exact degree_one_gap s hs

/-- Degree-two denominators with support at least `3*s-3` still yield at most
four rational profiles on `4*s` distinct coordinates once `s>=94`. -/
theorem degree_two_rational_profile_list_le_four {F κ ι : Type*} [Field F]
    [Fintype κ] [Fintype ι] [DecidableEq ι]
    (dom : ι ↪ F) (w : ι → F) (s : ℕ) (hs : 94 ≤ s)
    (hcard : Fintype.card ι = 4 * s)
    (num den : κ → F[X]) (S : κ → Finset ι)
    (hnum : ∀ i, (num i).natDegree ≤ 2 * s - 1)
    (hden : ∀ i, (den i).natDegree ≤ 2)
    (hsep : ∀ i j, i ≠ j → num i * den j - num j * den i ≠ 0)
    (hlarge : ∀ i, 3 * s - 3 ≤ (S i).card)
    (hnonzero : ∀ i x, x ∈ S i → (den i).eval (dom x) ≠ 0)
    (hagree : ∀ i x, x ∈ S i →
      (num i).eval (dom x) / (den i).eval (dom x) = w x) :
    Fintype.card κ ≤ 4 := by
  apply rational_profile_list_le_four_of_gap dom w (2 * s - 1) 2 (3 * s - 3)
    num den S hnum hden hsep hlarge hnonzero hagree
  have hd : 2 * s - 1 + 2 = 2 * s + 1 := by omega
  rw [hcard, hd]
  exact degree_two_gap s hs

end AstraMcaRationalList

#print axioms AstraMcaRationalList.five_sets_impossible_of_gap
#print axioms AstraMcaRationalList.degree_one_gap
#print axioms AstraMcaRationalList.degree_two_gap
#print axioms AstraMcaRationalList.five_sets_impossible
#print axioms AstraMcaRationalList.indexed_sets_card_le_four_of_gap
#print axioms AstraMcaRationalList.indexed_sets_card_le_four
#print axioms AstraMcaRationalList.rational_agreement_inter_card_le
#print axioms AstraMcaRationalList.rational_profile_list_le_four_of_gap
#print axioms AstraMcaRationalList.rational_profile_list_le_four
#print axioms AstraMcaRationalList.degree_two_rational_profile_list_le_four

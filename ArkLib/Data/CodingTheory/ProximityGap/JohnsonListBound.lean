/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.CoveragePigeonhole

/-!
# Johnson list-decoding bound for codes

The classical second-moment (Johnson) list bound, applied to actual codewords: a list `L` of
words each agreeing with a received word `f` on at least `a` coordinates, and pairwise agreeing
on at most `b` coordinates, has size bounded by `|L|·(a² − n·b) ≤ n²` (`n = |ι|`).  Dividing,
`|L| ≤ n²/(a² − n·b)` whenever `a² > n·b`.

For a code of minimum distance `d`, distinct codewords agree on `≤ n − d` coordinates, so taking
`b = n − d` gives the Johnson list-decoding bound in terms of the code distance — the
combinatorial core of the proven "`δ ≤ Johnson ⟹ small list`" regime (#141/#232).

* `johnson_list_bound` — `L.card · (a² − n·b) ≤ n²` from per-codeword agreement `≥ a` and
  pairwise codeword agreement `≤ b`.
* `johnson_list_bound_div` — the consumer-facing divided form under the strict Johnson gap.
* `johnson_unique_decoding_eq_one` — the nonempty exact-singleton unique-decoding endpoint.
-/

open Finset

namespace ArkLib.JohnsonList

/-- **Johnson list bound.**  If every word in `L` agrees with `f` on at least `a` of the `n`
coordinates, and every two distinct words of `L` agree with each other on at most `b`
coordinates, then (when `n·b ≤ a²`) `L.card · (a² − n·b) ≤ n²`.  Equivalently
`L.card ≤ n²/(a² − n·b)` — the Johnson list-decoding cap. -/
theorem johnson_list_bound {ι F : Type*} [Fintype ι] [DecidableEq ι] [DecidableEq F]
    (f : ι → F) (L : Finset (ι → F)) (a b : ℕ) (hL : L.Nonempty)
    (hclose : ∀ c ∈ L, a ≤ (Finset.univ.filter (fun x => c x = f x)).card)
    (hagree : ∀ c ∈ L, ∀ c' ∈ L, c ≠ c' →
      (Finset.univ.filter (fun x => c x = c' x)).card ≤ b)
    (hgap : Fintype.card ι * b ≤ a ^ 2) :
    L.card * (a ^ 2 - Fintype.card ι * b) ≤ (Fintype.card ι) ^ 2 := by
  classical
  haveI : Nonempty ↥L := ⟨⟨hL.choose, hL.choose_spec⟩⟩
  set S : ↥L → Finset ι := fun c => Finset.univ.filter (fun x => (c : ι → F) x = f x) with hS
  have hlo : ∀ c : ↥L, a ≤ (S c).card := fun c => hclose c.1 c.2
  have hpair : ∀ c c' : ↥L, c ≠ c' → (S c ∩ S c').card ≤ b := by
    intro c c' hcc
    refine le_trans (Finset.card_le_card ?_)
      (hagree c.1 c.2 c'.1 c'.2 (fun h => hcc (Subtype.ext h)))
    intro x hx
    rw [Finset.mem_inter, hS] at hx
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hx ⊢
    exact hx.1.trans hx.2.symm
  have key := ArkLib.Coverage.card_mul_sub_le_of_agreement S a b hlo hpair hgap
  rwa [Fintype.card_coe] at key

/-- **Divided Johnson list bound.** Under the strict Johnson gap `|ι|·b < a²`, the
second-moment inequality gives the direct list-size cap
`L.card ≤ |ι|² / (a² - |ι|·b)`.  This is the consumer-facing form used by downstream
list-decoding and proximity arguments.  The empty-list case is discharged separately, so callers
do not need to provide `L.Nonempty`. -/
theorem johnson_list_bound_div {ι F : Type*} [Fintype ι] [DecidableEq ι] [DecidableEq F]
    (f : ι → F) (L : Finset (ι → F)) (a b : ℕ)
    (hclose : ∀ c ∈ L, a ≤ (Finset.univ.filter (fun x => c x = f x)).card)
    (hagree : ∀ c ∈ L, ∀ c' ∈ L, c ≠ c' →
      (Finset.univ.filter (fun x => c x = c' x)).card ≤ b)
    (hgap : Fintype.card ι * b < a ^ 2) :
    L.card ≤ (Fintype.card ι) ^ 2 / (a ^ 2 - Fintype.card ι * b) := by
  classical
  by_cases hL : L.Nonempty
  · have hmul := johnson_list_bound f L a b hL hclose hagree (le_of_lt hgap)
    exact (Nat.le_div_iff_mul_le (Nat.sub_pos_of_lt hgap)).2 hmul
  · have hcard : L.card = 0 := by
      rw [Finset.card_eq_zero]
      rw [Finset.eq_empty_iff_forall_notMem]
      intro x hx
      exact hL ⟨x, hx⟩
    simp [hcard]

/-- **Unique decoding.**  If every word in `L` agrees with `f` on at least `a` coordinates and
distinct words of `L` agree pairwise on at most `b`, then whenever `n + b < 2a` the list is a
singleton: `L.card ≤ 1`.  (Inclusion–exclusion: two such words would share `≥ 2a − n > b`
coordinates.)  Taking `b = n − d` this is the unique-decoding radius `a > (n + n − d)/2`,
i.e. agreement above `n − d/2` — the proven `δ < δ_min/2` regime. -/
theorem johnson_unique_decoding {ι F : Type*} [Fintype ι] [DecidableEq ι] [DecidableEq F]
    (f : ι → F) (L : Finset (ι → F)) (a b : ℕ)
    (hclose : ∀ c ∈ L, a ≤ (Finset.univ.filter (fun x => c x = f x)).card)
    (hagree : ∀ c ∈ L, ∀ c' ∈ L, c ≠ c' →
      (Finset.univ.filter (fun x => c x = c' x)).card ≤ b)
    (h2a : Fintype.card ι + b < 2 * a) :
    L.card ≤ 1 := by
  classical
  rw [Finset.card_le_one]
  intro c hc c' hc'
  by_contra hne
  set Sc := Finset.univ.filter (fun x => c x = f x) with hSc
  set Sc' := Finset.univ.filter (fun x => c' x = f x) with hSc'
  have hca : a ≤ Sc.card := hclose c hc
  have hca' : a ≤ Sc'.card := hclose c' hc'
  have hunion : (Sc ∪ Sc').card ≤ Fintype.card ι := by
    have hss : (Sc ∪ Sc') ⊆ (Finset.univ : Finset ι) := Finset.subset_univ (Sc ∪ Sc')
    calc (Sc ∪ Sc').card ≤ (Finset.univ : Finset ι).card := Finset.card_le_card hss
      _ = Fintype.card ι := Finset.card_univ
  have hie : (Sc ∪ Sc').card + (Sc ∩ Sc').card = Sc.card + Sc'.card :=
    Finset.card_union_add_card_inter Sc Sc'
  have hsub : (Sc ∩ Sc').card ≤ b := by
    refine le_trans (Finset.card_le_card ?_) (hagree c hc c' hc' hne)
    intro x hx
    rw [Finset.mem_inter, hSc, hSc'] at hx
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hx ⊢
    exact hx.1.trans hx.2.symm
  omega

/-- **Exact unique-decoding endpoint.**  The nonempty version of `johnson_unique_decoding`: under
the same strict half-distance inequality, a nonempty list has exactly one element. -/
theorem johnson_unique_decoding_eq_one {ι F : Type*} [Fintype ι] [DecidableEq ι]
    [DecidableEq F] (f : ι → F) (L : Finset (ι → F)) (a b : ℕ) (hL : L.Nonempty)
    (hclose : ∀ c ∈ L, a ≤ (Finset.univ.filter (fun x => c x = f x)).card)
    (hagree : ∀ c ∈ L, ∀ c' ∈ L, c ≠ c' →
      (Finset.univ.filter (fun x => c x = c' x)).card ≤ b)
    (h2a : Fintype.card ι + b < 2 * a) :
    L.card = 1 := by
  exact Nat.le_antisymm (johnson_unique_decoding f L a b hclose hagree h2a)
    (Finset.card_pos.mpr hL)

end ArkLib.JohnsonList

-- Axiom audit.
#print axioms ArkLib.JohnsonList.johnson_list_bound_div
#print axioms ArkLib.JohnsonList.johnson_unique_decoding_eq_one

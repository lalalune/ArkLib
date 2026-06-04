/-
Copyright (c) 2025 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mirco Richter, Poulami Das (Least Authority)
-/

import ArkLib.Data.CodingTheory.ReedSolomon
import ArkLib.Data.CodingTheory.ListDecodability
import ArkLib.Data.Probability.Instances
import ArkLib.Data.Probability.Notation
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Fintype.Vector

open Finset ListDecodable NNReal Polynomial ProbabilityTheory ReedSolomon
namespace OutOfDomSmpl

variable {F : Type} [Field F] [Fintype F] [DecidableEq F]
         {ι : Type} [Fintype ι] [DecidableEq ι]

/-! Section 4.3 [ACFY24stir]

## References

* [Arnon, G., Chiesa, A., Fenzi, G., and Yogev, E., *STIR: Reed-Solomon proximity testing with
    fewer queries*][ACFY24stir]
-/

/-- Returns the domain complement `F \ φ(ι)` of an injective map `φ : ι ↪ F` -/
def domainComplement (φ : ι ↪ F) : Finset F :=
  Finset.univ \ Finset.image φ.toFun Finset.univ

/-- Pr_{r₀, …, r_{s-1} ← (𝔽 \ φ(ι)) }
      [ ∃ distinct u, u′ ∈ List(C, f, δ) :
        ∀ i < s, u(r_i) = u′(r_i) ]
    here, List (C, f, δ) denotes the list of codewords of C δ-close to f,
    wrt the Relative Hamming distance. -/
noncomputable def listDecodingCollisionProbability
  (φ : ι ↪ F) (f : ι → F) (δ : ℝ) (s degree : ℕ)
  (h_nonempty : Nonempty (domainComplement φ)) : ENNReal :=
  Pr_{let r ←$ᵖ (Fin s → domainComplement φ)}[ ∃ (u u' : code φ degree),
                                    u.val ≠ u'.val ∧
                                    u.val ∈ closeCodewordsRel (code φ degree) f δ ∧
                                    u'.val ∈ closeCodewordsRel (code φ degree) f δ ∧
                                    ∀ i : Fin s,
                                    let uPoly := decodeLT u
                                    let uPoly' := decodeLT u'
                                    (uPoly : F[X]).eval (r i).1
                                      = (uPoly' : F[X]).eval (r i).1
                                    ]

/-- The mass that the `Pr_{...}[...]` PMF encoding assigns to an event under uniform sampling
is exactly `#event / #domain` — the counting bridge used to estimate collision probabilities. -/
private lemma uniform_event_mass {α : Type} [Fintype α] [Nonempty α]
    (P : α → Prop) [DecidablePred P] :
    PMF.bind (PMF.uniformOfFintype α) (fun r => PMF.pure (P r)) True
      = ((Finset.univ.filter P).card : ENNReal) * ((Fintype.card α : ENNReal))⁻¹ := by
  classical
  rw [PMF.bind_apply, tsum_fintype]
  trans (∑ a ∈ Finset.univ.filter P, ((Fintype.card α : ENNReal))⁻¹)
  · rw [Finset.sum_filter]
    refine Finset.sum_congr rfl fun a _ => ?_
    by_cases h : P a <;>
      simp [PMF.uniformOfFintype_apply, PMF.pure_apply, h, eq_iff_iff]
  · rw [Finset.sum_const, nsmul_eq_mul]

/-- Counting a coordinatewise event: the tuples satisfying `Q` in every coordinate form the
`piFinset` of the per-coordinate solution set, so their count is `(#Q)^s`. Together with
`uniform_event_mass` this replaces any independence machinery by pure counting. -/
private lemma card_filter_forall_pi {β : Type} [Fintype β] [DecidableEq β] {s : ℕ}
    (Q : β → Prop) [DecidablePred Q] :
    (Finset.univ.filter (fun r : Fin s → β => ∀ i, Q (r i))).card
      = ((Finset.univ.filter Q).card) ^ s := by
  classical
  have h : (Finset.univ.filter (fun r : Fin s → β => ∀ i, Q (r i)))
      = Fintype.piFinset (fun _ : Fin s => Finset.univ.filter Q) := by
    ext r
    simp [Fintype.mem_piFinset]
  rw [h, Fintype.card_piFinset]
  simp

omit [Fintype F] [DecidableEq F] in
/-- Distinct codewords decode to distinct polynomials: the decoded polynomial interpolates the
codeword on the domain (`Lagrange.eval_interpolate_at_node`), so equal polynomials force equal
codewords. -/
private lemma decodeLT_ne_of_val_ne {φ : ι ↪ F} {degree : ℕ} (u u' : code φ degree)
    (hne : u.val ≠ u'.val) :
    ((decodeLT u : F[X])) ≠ ((decodeLT u' : F[X])) := by
  intro h
  apply hne
  funext x
  have hu : ((decodeLT u : F[X])).eval (φ x) = u.val x :=
    Lagrange.eval_interpolate_at_node u.val (φ.injective.injOn) (Finset.mem_univ x)
  have hu' : ((decodeLT u' : F[X])).eval (φ x) = u'.val x :=
    Lagrange.eval_interpolate_at_node u'.val (φ.injective.injOn) (Finset.mem_univ x)
  rw [← hu, ← hu', h]

/-- The agreement set of two distinct codewords' polynomials (inside any subtype of `F`) has at
most `degree − 1` elements: agreement points are roots of the nonzero difference, whose degree is
below `degree`. -/
private lemma card_agreement_le {φ : ι ↪ F} {degree : ℕ} (u u' : code φ degree)
    (hne : u.val ≠ u'.val) :
    (Finset.univ.filter (fun x : ↥(domainComplement φ) =>
      ((decodeLT u : F[X])).eval x.1 = ((decodeLT u' : F[X])).eval x.1)).card
      ≤ degree - 1 := by
  classical
  set q : F[X] := (decodeLT u : F[X]) - (decodeLT u' : F[X]) with hq
  have hq0 : q ≠ 0 := sub_ne_zero_of_ne (decodeLT_ne_of_val_ne u u' hne)
  have hqdeg : q.natDegree < degree := by
    have hp := (decodeLT u).2
    have hp' := (decodeLT u').2
    rw [Polynomial.mem_degreeLT] at hp hp'
    have hlt : q.degree < (degree : WithBot ℕ) :=
      lt_of_le_of_lt (Polynomial.degree_sub_le _ _) (max_lt hp hp')
    exact (Polynomial.natDegree_lt_iff_degree_lt hq0).mpr hlt
  have hsub : (Finset.univ.filter (fun x : ↥(domainComplement φ) =>
        ((decodeLT u : F[X])).eval x.1 = ((decodeLT u' : F[X])).eval x.1)).image Subtype.val
      ⊆ q.roots.toFinset := by
    intro y hy
    simp only [Finset.mem_image, Finset.mem_filter] at hy
    obtain ⟨x, ⟨_, hx⟩, rfl⟩ := hy
    rw [Multiset.mem_toFinset, Polynomial.mem_roots hq0]
    simp [hq, Polynomial.IsRoot, hx]
  calc (Finset.univ.filter _).card
      = ((Finset.univ.filter (fun x : ↥(domainComplement φ) =>
          ((decodeLT u : F[X])).eval x.1 = ((decodeLT u' : F[X])).eval x.1)).image
            Subtype.val).card := (Finset.card_image_of_injective _ Subtype.val_injective).symm
    _ ≤ q.roots.toFinset.card := Finset.card_le_card hsub
    _ ≤ Multiset.card q.roots := q.roots.toFinset_card_le
    _ ≤ q.natDegree := Polynomial.card_roots' q
    _ ≤ degree - 1 := by omega

/-- Lemma 4.5.1 -/
lemma out_of_dom_smpl_1
  {δ l : ℝ≥0} {s : ℕ} {f : ι → F} {degree : ℕ} {φ : ι ↪ F}
  (C : Set (ι → F)) (hC : C = code φ degree)
  (h_decodable : listDecodable C δ l)
  (h_nonempty : Nonempty (domainComplement φ)) :
  listDecodingCollisionProbability φ f δ s degree h_nonempty ≤
    ((l * (l-1) / 2)) * ((degree - 1) / (Fintype.card F - Fintype.card ι))^s
  := by sorry

/-- Lemma 4.5.2 -/
lemma out_of_dom_smpl_2
  {δ l : ℝ≥0} {s : ℕ} {f : ι → F} {degree : ℕ} {φ : ι ↪ F}
  (C : Set (ι → F)) (hC : C = code φ degree)
  (h_decodable : listDecodable C δ l)
  (h_nonempty : Nonempty (domainComplement φ)) :
  listDecodingCollisionProbability φ f δ s degree h_nonempty ≤
    ((l^2 / 2)) * (degree / (Fintype.card F - Fintype.card ι))^s
  := by
    transitivity
    · exact out_of_dom_smpl_1 C hC h_decodable h_nonempty
    · apply mul_le_mul'
      · apply ENNReal.div_le_div_right
        rw [pow_two]
        apply mul_le_mul' (by rfl)
        exact tsub_le_self
      · apply pow_le_pow_left'
        apply ENNReal.div_le_div_right
        exact tsub_le_self

end OutOfDomSmpl

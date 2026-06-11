/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.Hab25CurveCellGivenFamily

/-!
# The good-set weld: decode witnesses from closeness under ¬jointAgreement (#304, leg 4)

The cell machinery consumes `McaDecodeCurve` witnesses, whose `hnjp` clause (*no*
codeword stack jointly agrees on the witness set) cannot come from closeness alone.  This
file proves it comes from the global `¬ jointAgreement` escape — the exact branch the
disjunctive residual (`StrictCoeffPolysResidualShareOr`) exposes:

* `not_stackJointAgreesOn_of_not_jointAgreement` — a large witness set cannot support a
  joint codeword stack when `jointAgreement` fails (a stack on `S` with
  `|S| ≥ (1−δ)·n` would witness it);
* `exists_mcaDecodeCurve_of_close_of_not_jointAgreement` — the per-`γ` decode witness
  from the share residual's own decoded data (`natDegree < k` + `δᵣ ≤ δ`): the witness
  set is the agreement set of the given polynomial, its size bound is the closeness
  bound, and `hnjp` is the previous lemma;
* **`exists_heavy_factor_cell_on_decoded_set`** — the leg-4 capstone: under
  `¬ jointAgreement`, ANY decoded family on ANY scalar set `G` (in particular
  `RS_goodCoeffsCurve`) feeds the SK4 heavy-cell attribution outright — some irreducible
  factor of the GS interpolant carries a `1/#factors` share of `G` with the family's
  divisibility on all of it.

With this, leg 4 of the share-producer frontier is CLOSED: the remaining open inputs of
the strict-Johnson lane are exactly the per-rich-cell surface supply, the
heavy-coordinate matching sets, and the `L`-ary Z-degree-bounded interpolant budget.

Axiom-clean: `[propext, Classical.choice, Quot.sound]` (audited at end of file).
-/

set_option linter.unusedSectionVars false

namespace CodingTheory.ProximityGap.Hab25Core.Hab25JohnsonEndgame

open Polynomial Polynomial.Bivariate Finset
open GuruswamiSudan.OverRatFunc
open _root_.ProximityGap Code
open scoped NNReal ENNReal

variable {F₀ : Type} [Field F₀] [Fintype F₀] [DecidableEq F₀]

/-- **A large witness set cannot support a joint codeword stack when `jointAgreement`
fails**: a stack agreeing on `S` with `|S| ≥ (1−δ)·n` is a `jointAgreement` witness. -/
theorem not_stackJointAgreesOn_of_not_jointAgreement {n : ℕ} [NeZero n] {κ : Type}
    (C : Set (Fin n → F₀)) (δ : ℝ≥0) (u : κ → Fin n → F₀) (S : Finset (Fin n))
    (hcard : ((S.card : ℝ≥0)) ≥ (1 - δ) * Fintype.card (Fin n))
    (hnja : ¬ jointAgreement (C := C) (δ := δ) (W := u)) :
    ¬ _root_.ProximityGap.stackJointAgreesOn C S u := by
  rintro ⟨v, hv, hag⟩
  refine hnja ⟨S, hcard, v, fun j => ⟨hv j, ?_⟩⟩
  intro x hx
  exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hag x hx j⟩

/-- **The per-`γ` decode witness from the share residual's own decoded data.**  Given a
polynomial of RS degree that is `δ`-close to the curve at `γ`, and `¬ jointAgreement`,
the `McaDecodeCurve` structure is constructible with that polynomial: the witness set is
its agreement set, the size bound is the closeness bound, and the `hnjp` clause is the
previous lemma. -/
theorem exists_mcaDecodeCurve_of_close_of_not_jointAgreement {n L k : ℕ} [NeZero n]
    (domain : Fin n ↪ F₀) (u : WordStack F₀ (Fin L) (Fin n)) (δ : ℝ≥0) (γ : F₀)
    (P : F₀[X]) (hdeg : P.natDegree < k)
    (hclose : δᵣ(∑ j : Fin L, (γ ^ (j : ℕ)) • u j, P.eval ∘ domain) ≤ δ)
    (hnja : ¬ jointAgreement
      (C := (ReedSolomon.code domain k : Set (Fin n → F₀))) (δ := δ) (W := u)) :
    ∃ d : McaDecodeCurve domain k δ u γ, d.P = P := by
  classical
  obtain ⟨S, hScard, hSagree⟩ :=
    (relCloseToWord_iff_exists_agreementCols
      (∑ j : Fin L, (γ ^ (j : ℕ)) • u j) (P.eval ∘ domain) δ).mp hclose
  have hcard : ((S.card : ℝ≥0)) ≥ (1 - δ) * Fintype.card (Fin n) :=
    (Code.relDist_floor_bound_iff_complement_bound _ _ _).mp hScard
  refine ⟨⟨S, P, ?_, hcard, ?_, ?_⟩, rfl⟩
  · -- the degree bound, `natDegree`-to-`degree`
    rcases eq_or_ne P 0 with rfl | hP0
    · simpa [Polynomial.degree_zero] using WithBot.bot_lt_coe k
    · exact (Polynomial.natDegree_lt_iff_degree_lt hP0).mp hdeg
  · -- agreement on the witness set, pointwise
    intro i hi
    have h := (hSagree i).1 hi
    simp only [Finset.sum_apply, Pi.smul_apply, Function.comp_apply] at h
    exact h.symm
  · -- no joint stack on the witness set
    exact not_stackJointAgreesOn_of_not_jointAgreement _ δ u S hcard hnja

attribute [local instance] Classical.propDecidable

/-- **The leg-4 capstone: heavy-cell attribution on any decoded set under
`¬ jointAgreement`.**  Composing the decode-witness construction with the SK4
given-family attribution: under the GS interpolant chain and a degenerate budget
`T < |G|`, ANY family `P` decoded on ANY scalar set `G` (closeness + degree at every
`γ ∈ G`) admits an irreducible factor `R` of `Q₀` carrying a `1/#factors(Q₀)` share of
`G` with `(X − C (P γ)) ∣ R|_{Z:=γ}` on all of it. -/
theorem exists_heavy_factor_cell_on_decoded_set {n k m L : ℕ} [NeZero n]
    (domain : Fin n ↪ F₀)
    (u : WordStack F₀ (Fin L) (Fin n)) (δ : ℝ≥0) (T : ℕ)
    {Q : (RatFunc F₀)[X][Y]} {dd : F₀[X]} {Q₀ : (F₀[X])[X][Y]}
    (hQ : GuruswamiSudan.Conditions k m (gs_degree_bound k n m)
      (liftedDomain domain) (curveFold (fun j i => u j i)) Q)
    (hrep : Q₀.map (Polynomial.mapRingHom (algebraMap F₀[X] (RatFunc F₀))) =
      Polynomial.C (Polynomial.C (algebraMap F₀[X] (RatFunc F₀) dd)) * Q)
    (hQ₀0 : Q₀ ≠ 0)
    (hkn : k + 1 ≤ n) (hm : 1 ≤ m)
    (hδ1 : δ ≤ 1) (hδJ : (δ : ℝ) < gs_johnson k n m)
    (hbadz : ∀ S : Finset F₀,
      (∀ z ∈ S, Q₀.map (Polynomial.mapRingHom (Polynomial.evalRingHom z)) = 0) →
      S.card ≤ T)
    (G : Finset F₀) (P : F₀ → F₀[X])
    (hP : ∀ γ ∈ G, (P γ).natDegree < k ∧
      δᵣ(∑ j : Fin L, (γ ^ (j : ℕ)) • u j, (P γ).eval ∘ domain) ≤ δ)
    (hnja : ¬ jointAgreement
      (C := (ReedSolomon.code domain k : Set (Fin n → F₀))) (δ := δ) (W := u))
    (hbig : T < G.card) :
    ∃ R : (F₀[X])[X][Y],
      R ∈ (UniqueFactorizationMonoid.factors Q₀).toFinset ∧
      Irreducible R ∧
      ∃ G' : Finset F₀,
        G' ⊆ G ∧
        G.card ≤ T + (UniqueFactorizationMonoid.factors Q₀).toFinset.card * G'.card ∧
        ∀ γ ∈ G',
          Q₀.map (Polynomial.mapRingHom (Polynomial.evalRingHom γ)) ≠ 0 ∧
          (Polynomial.X - Polynomial.C (P γ)) ∣
            R.map (Polynomial.mapRingHom (Polynomial.evalRingHom γ)) := by
  refine exists_heavy_factor_cell_of_given_family domain u δ T hQ hrep hQ₀0 hkn hm
    hδ1 hδJ hbadz G P ?_ hbig
  intro γ hγ
  exact exists_mcaDecodeCurve_of_close_of_not_jointAgreement domain u δ γ (P γ)
    (hP γ hγ).1 (hP γ hγ).2 hnja

end CodingTheory.ProximityGap.Hab25Core.Hab25JohnsonEndgame

/-! ## Axiom audit — all kernel-clean. -/
open CodingTheory.ProximityGap.Hab25Core.Hab25JohnsonEndgame in
#print axioms not_stackJointAgreesOn_of_not_jointAgreement
open CodingTheory.ProximityGap.Hab25Core.Hab25JohnsonEndgame in
#print axioms exists_mcaDecodeCurve_of_close_of_not_jointAgreement
open CodingTheory.ProximityGap.Hab25Core.Hab25JohnsonEndgame in
#print axioms exists_heavy_factor_cell_on_decoded_set

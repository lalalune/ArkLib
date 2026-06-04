/-
Copyright (c) 2025 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Poulami Das (Least Authority), Alexander Hicks
-/

import ArkLib.Data.CodingTheory.ReedSolomon
import ArkLib.Data.CodingTheory.ListDecodability
import ArkLib.Data.MvPolynomial.Multilinear
import ArkLib.Data.Probability.Notation

namespace OutOfDomSmpl

open ListDecodable MvPolynomial NNReal ProbabilityTheory ReedSolomon

variable {F : Type} [Field F] [DecidableEq F]
         {ι : Type} [Fintype ι] [DecidableEq ι]

/-- Lemma 4.24
  Let `f : ι → F`, `m` be the number of variables, `s` be a repetition parameter
  and `δ ∈ [0,1]` be a distance parameter, then for every `r₁,...,rₛ ∈ Fᵐ`
  the following statements are equivalent:
    - ∃ distinct u, u' ∈ Λ(C,f,δ) such that ∀ i < s, uPoly(rᵢ) = uPoly'(rᵢ)
      where, Λ(C,f,δ) denotes the list of codewords of C δ-close to f
             uPoly, uPoly' denotes the decoded multivariate polynomials of u and u'
    - ∃ σ₁,..,σₛ : F, such that |Λ(C',f,δ)| > 1
      where, C' is a multiconstrained RS = MCRS[F, ι, φ, m, s, w, σ]
             σ = {σ₁,..,σₛ}, w = {w₁,..,wₛ}, wᵢ = Z * eqPolynomial(rᵢ) -/
lemma crs_equiv_rs_random_point_agreement
  {f : ι → F} {m s : ℕ} {φ : ι ↪ F} [Smooth φ] :
  ∀ (r : Fin s → Fin m → F) (δ : ℝ≥0) (hδLe : δ ≤ 1),
    (∃ u u' : smoothCode φ m,
      u.val ≠ u'.val ∧
      u.val ∈ closeCodewordsRel (smoothCode φ m) f δ ∧
      u'.val ∈ closeCodewordsRel (smoothCode φ m) f δ ∧
      ∀ i : Fin s, (mVdecode u).eval (r i) = (mVdecode u').eval (r i))
    ↔
    (∃ σ : Fin s → F,
      let w : Fin s → MvPolynomial (Fin (m + 1)) F :=
        fun i => MvPolynomial.X (Fin.last m) * rename Fin.castSucc (eqPolynomial (r i))
      let multiCRSCode := multiConstrainedCode φ m s w σ
      ∃ u u' : ι → F, u ≠ u' ∧
        u ∈ closeCodewordsRel multiCRSCode f δ ∧
        u' ∈ closeCodewordsRel multiCRSCode f δ)
  := by sorry

/-- Lemma 4.25 part 1
  Let `f : ι → F`, `m` be the number of variables, `s` be a repetition parameter
  and `δ ∈ [0,1]` be a distance parameter,
  if `C = RS [F, ι, m]` is `(δ,l)`-list decodable then
  `Pr_{r ← F} [ ∃ σ₁,..,σₛ : F, |Λ(C',f,δ)| > 1 ] =`
  `Pr_{r ← F} [ ∃ distinct u, u' ∈ RS[F, ι, φ, m] s.t. uPoly(pow(r)) = uPoly'(pow(r))]`
    where, pow(x,m) = {x^2⁰,x^2¹,....,x^2^{m-1}}
           C' = CRS [F, ι, φ, m, s, w, σ]
           σ = {σ₁,..,σₛ}, w = {w₁,..,wₛ}, wᵢ = Z * eqPolynomial(pow(r,m)) -/
lemma oodSampling_crs_eq_rs
    [Fintype F] {f : ι → F} {m s : ℕ} {φ : ι ↪ F} [Smooth φ]
    (l δ : ℝ≥0) (hδLe : δ ≤ 1)
    {C : Set (ι → F)} (hcode : C = smoothCode φ m ∧ listDecodable C δ l) :
    Pr_{ let rs ←$ᵖ (Fin s → F) }[ (∃ σ : Fin s → F,
                        let w : Fin s → MvPolynomial (Fin (m + 1)) F :=
                          fun i =>
                            let ri := rs i
                            let rVec := fun j : Fin m => ri ^ (2^(j : ℕ))
                            MvPolynomial.X (Fin.last m) * rename Fin.castSucc (eqPolynomial rVec)
                        let multiCRSCode := multiConstrainedCode φ m s w σ
                        ∃ u u' : ι → F, u ≠ u' ∧
                          u ∈ closeCodewordsRel multiCRSCode f δ ∧
                          u' ∈ closeCodewordsRel multiCRSCode f δ)]
    =
    Pr_{ let rs ←$ᵖ (Fin s → F) }[ (∃ u u' : smoothCode φ m,
                        u.val ≠ u'.val ∧
                        u.val ∈ closeCodewordsRel C f δ ∧
                        u'.val ∈ closeCodewordsRel C f δ ∧
                        ∀ i : Fin s,
                          let ri := rs i
                          let rVec := fun j : Fin m => ri ^ (2^(j : ℕ))
                          (mVdecode u).eval (rVec) = (mVdecode u').eval (rVec))]
  := by
  have h1 := hcode.1
  subst h1
  have hequiv : ∀ rs : Fin s → F,
    (∃ σ : Fin s → F,
      let w : Fin s → MvPolynomial (Fin (m + 1)) F :=
        fun i =>
          let ri := rs i
          let rVec := fun j : Fin m => ri ^ (2^(j : ℕ))
          MvPolynomial.X (Fin.last m) * rename Fin.castSucc (eqPolynomial rVec)
      let multiCRSCode := multiConstrainedCode φ m s w σ
      ∃ u u' : ι → F, u ≠ u' ∧
        u ∈ closeCodewordsRel multiCRSCode f ↑δ ∧
        u' ∈ closeCodewordsRel multiCRSCode f ↑δ)
    ↔
    (∃ u u' : smoothCode φ m,
      u.val ≠ u'.val ∧
      u.val ∈ closeCodewordsRel (↑(smoothCode φ m)) f ↑δ ∧
      u'.val ∈ closeCodewordsRel (↑(smoothCode φ m)) f ↑δ ∧
      ∀ i : Fin s,
        let ri := rs i
        let rVec := fun j : Fin m => ri ^ (2^(j : ℕ))
        (mVdecode u).eval rVec = (mVdecode u').eval rVec) :=
    fun rs => (crs_equiv_rs_random_point_agreement
      (fun i j => (rs i) ^ (2 ^ (j : ℕ))) δ hδLe).symm
  have hfun : (fun rs => PMF.pure (∃ σ : Fin s → F,
      let w := fun i =>
        let ri := rs i
        let rVec := fun j : Fin m => ri ^ (2^(j : ℕ))
        MvPolynomial.X (Fin.last m) * rename Fin.castSucc (eqPolynomial rVec)
      let multiCRSCode := multiConstrainedCode φ m s w σ
      ∃ u u' : ι → F, u ≠ u' ∧
        u ∈ closeCodewordsRel multiCRSCode f ↑δ ∧
        u' ∈ closeCodewordsRel multiCRSCode f ↑δ) : (Fin s → F) → PMF Prop) =
    fun rs => PMF.pure (∃ u u' : smoothCode φ m,
      u.val ≠ u'.val ∧
      u.val ∈ closeCodewordsRel (↑(smoothCode φ m)) f ↑δ ∧
      u'.val ∈ closeCodewordsRel (↑(smoothCode φ m)) f ↑δ ∧
      ∀ i : Fin s,
        let ri := rs i
        let rVec := fun j : Fin m => ri ^ (2^(j : ℕ))
        (mVdecode u).eval rVec = (mVdecode u').eval rVec) :=
    funext fun rs => congr_arg PMF.pure (propext (hequiv rs))
  exact congr_arg (· True) (congr_arg (PMF.bind ($ᵖ (Fin s → F))) hfun)

section CountingBridge

open LinearMvExtension Polynomial

/-- The mass that the `Pr_{...}[...]` PMF encoding assigns to an event under uniform sampling
is exactly `#event / #domain`. -/
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

/-- Tuples satisfying `Q` in every coordinate form the `piFinset` of the per-coordinate
solution set, so their count is `(#Q)^s`. -/
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

/-- Distinct smooth codewords decode to distinct univariate polynomials (the decoded
polynomial interpolates the codeword on the domain). -/
private lemma decodeLT_ne_of_val_ne {φ : ι ↪ F} [Smooth φ] {m : ℕ} (u u' : smoothCode φ m)
    (hne : u.val ≠ u'.val) :
    ((decodeLT u : Polynomial F)) ≠ ((decodeLT u' : Polynomial F)) := by
  intro h
  apply hne
  funext x
  have hu : ((decodeLT u : Polynomial F)).eval (φ x) = u.val x :=
    Lagrange.eval_interpolate_at_node u.val (φ.injective.injOn) (Finset.mem_univ x)
  have hu' : ((decodeLT u' : Polynomial F)).eval (φ x) = u'.val x :=
    Lagrange.eval_interpolate_at_node u'.val (φ.injective.injOn) (Finset.mem_univ x)
  rw [← hu, ← hu', h]

/-- Two distinct smooth codewords' decoded polynomials agree on at most `2^m - 1` field
points: agreement points are roots of the nonzero difference of degree `< 2^m`. -/
private lemma card_agreement_le [Fintype F] {φ : ι ↪ F} [Smooth φ] {m : ℕ}
    (u u' : smoothCode φ m) (hne : u.val ≠ u'.val) :
    (Finset.univ.filter (fun x : F =>
      ((decodeLT u : Polynomial F)).eval x = ((decodeLT u' : Polynomial F)).eval x)).card
      ≤ 2 ^ m - 1 := by
  classical
  set q : Polynomial F := (decodeLT u : Polynomial F) - (decodeLT u' : Polynomial F) with hq
  have hq0 : q ≠ 0 := sub_ne_zero_of_ne (decodeLT_ne_of_val_ne u u' hne)
  have hqdeg : q.natDegree < 2 ^ m := by
    have hp := (decodeLT u).2
    have hp' := (decodeLT u').2
    rw [Polynomial.mem_degreeLT] at hp hp'
    have hlt : q.degree < ((2 ^ m : ℕ) : WithBot ℕ) :=
      lt_of_le_of_lt (Polynomial.degree_sub_le _ _) (max_lt hp hp')
    exact (Polynomial.natDegree_lt_iff_degree_lt hq0).mpr hlt
  have hsub : (Finset.univ.filter (fun x : F =>
        ((decodeLT u : Polynomial F)).eval x = ((decodeLT u' : Polynomial F)).eval x))
      ⊆ q.roots.toFinset := by
    intro y hy
    simp only [Finset.mem_filter] at hy
    rw [Multiset.mem_toFinset, Polynomial.mem_roots hq0]
    simp [hq, Polynomial.IsRoot, hy.2]
  calc (Finset.univ.filter _).card
      ≤ q.roots.toFinset.card := Finset.card_le_card hsub
    _ ≤ Multiset.card q.roots := q.roots.toFinset_card_le
    _ ≤ q.natDegree := Polynomial.card_roots' q
    _ ≤ 2 ^ m - 1 := by omega

/-- Evaluating the decoded multilinear polynomial at the power vector `(r^(2^j))_j` recovers
the decoded univariate polynomial's value at `r` (the smooth-code power substitution
round-trip). -/
private lemma mVdecode_eval_pow {φ : ι ↪ F} [Smooth φ] {m : ℕ} (u : smoothCode φ m) (r : F) :
    (mVdecode u).eval (fun j : Fin m => r ^ (2 ^ (j : ℕ)))
      = ((decodeLT u : Polynomial F)).eval r := by
  have h1 : Polynomial.eval r (powAlgHom (mVdecode u))
      = MvPolynomial.eval (fun j : Fin m => r ^ (2 ^ (j : ℕ))) (mVdecode u) := by
    unfold powAlgHom
    rw [MvPolynomial.aeval_def, ← Polynomial.coe_evalRingHom,
      MvPolynomial.eval₂_comp_left (Polynomial.evalRingHom r)]
    have hhom : (Polynomial.evalRingHom r).comp (algebraMap F (Polynomial F))
        = RingHom.id F := RingHom.ext fun a => by simp
    have hg : (⇑(Polynomial.evalRingHom r)
          ∘ fun j : Fin m => (Polynomial.X : Polynomial F) ^ 2 ^ (j : ℕ))
        = fun j : Fin m => r ^ 2 ^ (j : ℕ) := by
      funext j
      simp
    rw [hhom, hg, MvPolynomial.eval₂_id]
  have h2 : powAlgHom (mVdecode u) = ((decodeLT u : Polynomial F)) := by
    have := powContraction_is_right_inverse_to_linearMvExtension (decodeLT u)
    simpa [powContraction, mVdecode] using this
  rw [← h1, h2]

end CountingBridge

/-- Lemma 4.25 part 2
  Let `f : ι → F`, `m` be the number of variables, `s` be a repetition parameter
  and `δ ∈ [0,1]` be a distance parameter,
  if `C = RS [F, ι, m]` is `(δ,l)`-list decodable then
  the above equation is bounded as `≤ l²/2 * (2ᵐ/|F|)ˢ` -/
lemma oodSampling_rs_le_bound
    [Fintype F] {f : ι → F} {m s : ℕ} {φ : ι ↪ F} [Smooth φ]
    (δ l : ℝ≥0) (hδLe : δ ≤ 1)
    (C : Set (ι → F)) (hcode : C = smoothCode φ m ∧ listDecodable C δ l) :
    Pr_{ let rs ←$ᵖ (Fin s → F) }[ ∃ u u' : smoothCode φ m,
                        u.val ≠ u'.val ∧
                        u.val ∈ closeCodewordsRel C f δ ∧
                        u'.val ∈ closeCodewordsRel C f δ ∧
                        ∀ i : Fin s,
                          let ri := rs i
                          let rVec := fun j : Fin m => ri ^ (2^(j : ℕ))
                          (mVdecode u).eval (rVec) = (mVdecode u').eval (rVec)
                      ] ≤ ENNReal.ofReal (((l : ℝ)^2 / 2) * (((2^m : ℝ) / Fintype.card F)^s))
:= by sorry

end OutOfDomSmpl

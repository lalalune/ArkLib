import ArkLib.ToMathlib.ProximityGenericity
import ArkLib.Data.Polynomial.Bivariate

/-! Closing the `hx0` existence for BCIKS20 §5 genericity (#8): a single specialization point
`x₀ ∈ F` with `evalX (C x₀) R ≠ 0` for every `R` in a finite family of nonzero trivariate
polynomials `F[Z][X][Y] = Polynomial (Polynomial (Polynomial F))`, once `|F|` exceeds the total
leading-X-degree. Obstruction = the leading-Y-coefficient (in `(F[Z])[X]`, an integral domain). -/

open Polynomial

namespace ProximityGap.Genericity

variable {F : Type} [Field F] [Fintype F] [DecidableEq F]

/-- **Indexed domain genericity.** For an indexed family of nonzero polynomials `obstr R` over an
integral domain `T` into which `F` embeds, with total degree `< |F|`, a single `x : F` makes all
`(obstr R).eval (φ x)` nonzero. -/
theorem exists_good_point_of_obstructions_domain
    {ι : Type*} {T : Type*} [CommRing T] [IsDomain T]
    (φ : F →+* T) (hφ : Function.Injective φ)
    (Rs : Finset ι) (obstr : ι → Polynomial T)
    (hne : ∀ R ∈ Rs, obstr R ≠ 0)
    (hcard : ∑ R ∈ Rs, (obstr R).natDegree < Fintype.card F) :
    ∃ x : F, ∀ R ∈ Rs, (obstr R).eval (φ x) ≠ 0 := by
  classical
  set bad : Finset F :=
    Rs.biUnion (fun R => ((obstr R).roots.toFinset).preimage φ (hφ.injOn)) with hbad
  have hbad_card : bad.card < Fintype.card F := by
    calc bad.card ≤ ∑ R ∈ Rs, (((obstr R).roots.toFinset).preimage φ (hφ.injOn)).card :=
          Finset.card_biUnion_le
      _ ≤ ∑ R ∈ Rs, (obstr R).natDegree := by
          apply Finset.sum_le_sum
          intro R _hR
          calc (((obstr R).roots.toFinset).preimage φ (hφ.injOn)).card
              ≤ ((obstr R).roots.toFinset).card :=
                Finset.card_le_card_of_injOn φ
                  (fun a ha => Finset.mem_preimage.mp ha) (hφ.injOn)
            _ ≤ Multiset.card (obstr R).roots := Multiset.toFinset_card_le _
            _ ≤ (obstr R).natDegree := Polynomial.card_roots' (obstr R)
      _ < Fintype.card F := hcard
  have hne_univ : bad ≠ (Finset.univ : Finset F) := by
    intro h; rw [h, Finset.card_univ] at hbad_card; exact lt_irrefl _ hbad_card
  obtain ⟨x, hx⟩ : ∃ x : F, x ∉ bad := by
    by_contra h; push Not at h; exact hne_univ (Finset.eq_univ_iff_forall.mpr h)
  refine ⟨x, fun R hR hRx => ?_⟩
  apply hx
  rw [hbad, Finset.mem_biUnion]
  refine ⟨R, hR, ?_⟩
  rw [Finset.mem_preimage, Multiset.mem_toFinset, Polynomial.mem_roots (hne R hR)]
  exact hRx

/-- `(evalX a R).coeff j = (R.coeff j).eval a` over the base ring `Polynomial F` (= `F[Z]`). -/
lemma coeff_evalX (a : Polynomial F) (R : Polynomial (Polynomial (Polynomial F))) (j : ℕ) :
    (Polynomial.Bivariate.evalX a R).coeff j = (R.coeff j).eval a := by
  rw [Polynomial.Bivariate.evalX_eq_map, Polynomial.coeff_map]
  rfl

/-- A trivariate `R ≠ 0` has nonzero `evalX a R` whenever its leading Y-coefficient does not
vanish at `a`. -/
lemma evalX_ne_zero_of_leadingCoeff_eval_ne_zero {a : Polynomial F}
    {R : Polynomial (Polynomial (Polynomial F))}
    (h : (R.coeff R.natDegree).eval a ≠ 0) :
    Polynomial.Bivariate.evalX a R ≠ 0 := by
  intro hzero
  apply h
  rw [← coeff_evalX a R R.natDegree, hzero, Polynomial.coeff_zero]

/-- **`hsep` (#8), discharged — unconditional in `x₀`.** If `R` is separable (as a polynomial in
the `Y`-variable over `F[Z][X]`), then `evalX a R` is separable for **every** `a`, because
`evalX a R = R.map (evalRingHom a)` and separability is preserved by ring-hom maps
(`Polynomial.Separable.map`). So `hsep` needs no genericity — only the structural fact that the
GS factor `R` is `Y`-separable (`disc_Y R ≠ 0`). -/
lemma evalX_separable_of_separable {a : Polynomial F}
    {R : Polynomial (Polynomial (Polynomial F))} (h : R.Separable) :
    (Polynomial.Bivariate.evalX a R).Separable := by
  rw [Polynomial.Bivariate.evalX_eq_map]
  exact h.map

/-- **`hx0` existence (#8), discharged.** For a finite family `Rs` of nonzero trivariate
polynomials whose leading-Y-coefficient X-degrees sum to `< |F|`, there is a single `x₀ : F` with
`evalX (C x₀) R ≠ 0` for every `R ∈ Rs`. This discharges the field-size half of `hx0` in
`GraphExtractionHypotheses`. -/
theorem exists_x0_evalX_ne_zero
    (Rs : Finset (Polynomial (Polynomial (Polynomial F))))
    (hne : ∀ R ∈ Rs, R ≠ 0)
    (hcard : ∑ R ∈ Rs, (R.coeff R.natDegree).natDegree < Fintype.card F) :
    ∃ x₀ : F, ∀ R ∈ Rs, Polynomial.Bivariate.evalX (Polynomial.C x₀) R ≠ 0 := by
  classical
  have hne' : ∀ R ∈ Rs, (R.coeff R.natDegree) ≠ 0 :=
    fun R hR => Polynomial.leadingCoeff_ne_zero.mpr (hne R hR)
  obtain ⟨x₀, hx₀⟩ := exists_good_point_of_obstructions_domain (F := F) (T := Polynomial F)
    Polynomial.C Polynomial.C_injective Rs (fun R => R.coeff R.natDegree) hne' hcard
  exact ⟨x₀, fun R hR => evalX_ne_zero_of_leadingCoeff_eval_ne_zero (hx₀ R hR)⟩

#print axioms ProximityGap.Genericity.exists_good_point_of_obstructions_domain
#print axioms ProximityGap.Genericity.coeff_evalX
#print axioms ProximityGap.Genericity.exists_x0_evalX_ne_zero

end ProximityGap.Genericity

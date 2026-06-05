/-! # Guruswami-Sudan factor extraction (Track A3)

Two algebraic cores of the Guruswami-Sudan factor-extraction step of list decoding,
fully `Mathlib`-backed.

Work in `F[X][Y] = (F[X])[X]` (`Polynomial (Polynomial F)`).  A candidate message is a
`p : F[X]` of degree `< k`; its factor is the monic-linear-in-`Y` polynomial `Y - C p`
(`C : F[X] -> F[X][Y]` the constant embedding).  Evaluating `Q : F[X][Y]` at `Y := p`
(via `Polynomial.eval`, value ring the base `F[X]`) gives the curve restriction
`Q(X, p(X)) : F[X]`.

Part 1 (multiplicity-sum factor extraction): `A1` supplies, at each agreement point
`a in S`, an `m`-fold root of `g := Q(X, p(X))` (`(X - C a)^m | g`).  If these
multiplicities sum past `g.natDegree`, then `g = 0`; with `Polynomial.dvd_iff_isRoot`
for the monic linear `Y - C p` this gives `(Y - C p) | Q`.

Part 2 (list-size bound): distinct degree-`< k` messages `p` with `(Y - C p) | Q` are
roots of `Q` in `Y`, so number at most the `Y`-degree `Q.natDegree`.

No `sorry`, `admit`, or `native_decide`; every theorem checked to depend only on
`[propext, Classical.choice, Quot.sound]`.
-/

namespace GSFactorExtract

open Polynomial Finset

/-! ## Part 1: multiplicity-sum bound and factor extraction -/

section MultiplicitySum

variable {R : Type*} [CommRing R] [IsDomain R]

/-- **Multiplicity-sum bound.** -/
theorem multiplicity_sum_le_natDegree
    {g : R[X]} (hg : g ≠ 0) {S : Finset R} {m : R → ℕ}
    (hroot : ∀ a ∈ S, (X - C a) ^ (m a) ∣ g) :
    ∑ a ∈ S, m a ≤ g.natDegree := by
  classical
  set s : Multiset R := S.val.bind (fun a => Multiset.replicate (m a) a) with hs
  have hcard : Multiset.card s = ∑ a ∈ S, m a := by
    rw [hs, Multiset.card_bind]
    simp only [Function.comp, Multiset.card_replicate]
    rfl
  have hle : s ≤ g.roots := by
    rw [Multiset.le_iff_count]
    intro a
    by_cases haS : a ∈ S
    · have hcount : Multiset.count a s = m a := by
        rw [hs, Multiset.count_bind]
        have hmap : (S.val.map fun b => Multiset.count a (Multiset.replicate (m b) b))
            = S.val.map fun b => if b = a then m b else 0 := by
          apply Multiset.map_congr rfl
          intro b _
          rw [Multiset.count_replicate]
        rw [hmap]
        change ∑ b ∈ S, (if b = a then m b else 0) = m a
        rw [Finset.sum_ite_eq' S a (fun b => m b)]
        simp [haS]
      rw [hcount, Polynomial.count_roots]
      exact (Polynomial.le_rootMultiplicity_iff hg).mpr (hroot a haS)
    · have hcount : Multiset.count a s = 0 := by
        rw [hs, Multiset.count_bind]
        have hmap : (S.val.map fun b => Multiset.count a (Multiset.replicate (m b) b))
            = S.val.map fun b => if b = a then m b else 0 := by
          apply Multiset.map_congr rfl
          intro b _
          rw [Multiset.count_replicate]
        rw [hmap]
        change ∑ b ∈ S, (if b = a then m b else 0) = 0
        rw [Finset.sum_ite_eq' S a (fun b => m b)]
        simp [haS]
      rw [hcount]
      exact Nat.zero_le _
  calc ∑ a ∈ S, m a = Multiset.card s := hcard.symm
    _ ≤ Multiset.card g.roots := Multiset.card_le_card hle
    _ ≤ g.natDegree := Polynomial.card_roots' g

/-- **Factor extraction (vanishing form).** -/
theorem eq_zero_of_natDegree_lt_multiplicity_sum
    {g : R[X]} {S : Finset R} {m : R → ℕ}
    (hroot : ∀ a ∈ S, (X - C a) ^ (m a) ∣ g)
    (hbudget : g.natDegree < ∑ a ∈ S, m a) :
    g = 0 := by
  by_contra hg
  exact absurd (multiplicity_sum_le_natDegree hg hroot) (not_le.mpr hbudget)

end MultiplicitySum

/-! ## Curve restriction `Q(X, p(X))` and `(Y - C p) | Q` -/

section CurveRestriction

variable {F : Type*} [CommRing F]

noncomputable def curveRestrict (Q : (F[X])[X]) (p : F[X]) : F[X] := Q.eval p

theorem curveRestrict_def (Q : (F[X])[X]) (p : F[X]) :
    curveRestrict Q p = Q.eval p := rfl

theorem monic_Y_sub_Cp (p : F[X]) : (X - C p : (F[X])[X]).Monic := monic_X_sub_C p

theorem Y_sub_Cp_dvd_iff_curveRestrict_eq_zero (Q : (F[X])[X]) (p : F[X]) :
    (X - C p) ∣ Q ↔ curveRestrict Q p = 0 := by
  rw [curveRestrict_def, Polynomial.dvd_iff_isRoot]
  rfl

end CurveRestriction

/-! ### Assembled curve-factor extraction over a field -/

section FieldAssembly

variable {F : Type*} [Field F]

theorem curve_factor_extraction
    (Q : (F[X])[X]) (p : F[X]) {S : Finset F} {m : F → ℕ}
    (hroot : ∀ a ∈ S, (X - C a) ^ (m a) ∣ curveRestrict Q p)
    (hbudget : (curveRestrict Q p).natDegree < ∑ a ∈ S, m a) :
    (X - C p) ∣ Q := by
  rw [Y_sub_Cp_dvd_iff_curveRestrict_eq_zero]
  exact eq_zero_of_natDegree_lt_multiplicity_sum hroot hbudget

end FieldAssembly

/-! ## Part 2: list-size bound -/

section ListSize

variable {F : Type*} [Field F]

theorem card_distinct_linear_factors_le_natDegree
    (Q : (F[X])[X]) (hQ : Q ≠ 0) (Ps : Finset F[X])
    (hdvd : ∀ p ∈ Ps, (X - C p) ∣ Q) :
    Ps.card ≤ Q.natDegree := by
  classical
  have hsub : Ps.val ⊆ Q.roots := by
    intro p hp
    rw [← Finset.mem_def] at hp
    rw [Polynomial.mem_roots hQ]
    exact (Polynomial.dvd_iff_isRoot).mp (hdvd p hp)
  exact Polynomial.card_le_degree_of_subset_roots hsub

theorem gs_list_size_le
    (Q : (F[X])[X]) (hQ : Q ≠ 0) (Ps : Finset F[X])
    (hdvd : ∀ p ∈ Ps, (X - C p) ∣ Q) :
    Ps.card ≤ Q.natDegree :=
  card_distinct_linear_factors_le_natDegree Q hQ Ps hdvd

end ListSize

/-! ## End-to-end statement -/

section EndToEnd

variable {F : Type*} [Field F]

theorem gs_factor_extraction_list_size
    (Q : (F[X])[X]) (hQ : Q ≠ 0) (Ps : Finset F[X])
    (S : F[X] → Finset F) (m : F[X] → F → ℕ)
    (hroot : ∀ p ∈ Ps, ∀ a ∈ S p, (X - C a) ^ (m p a) ∣ curveRestrict Q p)
    (hbudget : ∀ p ∈ Ps, (curveRestrict Q p).natDegree < ∑ a ∈ S p, m p a) :
    Ps.card ≤ Q.natDegree := by
  apply gs_list_size_le Q hQ Ps
  intro p hp
  exact curve_factor_extraction Q p (hroot p hp) (hbudget p hp)

end EndToEnd

end GSFactorExtract
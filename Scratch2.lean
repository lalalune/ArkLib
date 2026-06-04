import ArkLib.Data.MvPolynomial.LinearMvExtension

open LinearMvExtension MvPolynomial Polynomial

noncomputable section

variable {F : Type*} [CommSemiring F] {m : ℕ}

/-- General evaluation of `linearMvExtension` at an arbitrary point `β`. -/
example (p : Polynomial.degreeLT F (2 ^ m)) (β : Fin m → F) :
    MvPolynomial.eval β (linearMvExtension p)
      = (p : Polynomial F).sum (fun i a => a * ∏ j : Fin m, β j ^ ((bitExpo (m := m) i) j)) := by
  unfold linearMvExtension
  rw [Polynomial.sum, Polynomial.sum, map_sum]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  rw [MvPolynomial.eval_monomial, Finsupp.prod_pow]

end

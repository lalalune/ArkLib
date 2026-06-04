import ArkLib.Data.MvPolynomial.LinearMvExtension
import ArkLib.Data.MvPolynomial.Multilinear

open LinearMvExtension MvPolynomial Polynomial

noncomputable section

variable {F : Type*} [CommRing F] [DecidableEq F] [IsDomain F] {m : ℕ}

/-- General evaluation of `linearMvExtension` at an arbitrary point `β`. -/
lemma linearMvExtension_eval (p : Polynomial.degreeLT F (2 ^ m)) (β : Fin m → F) :
    MvPolynomial.eval β (linearMvExtension p)
      = (p : Polynomial F).sum (fun i a => a * ∏ j : Fin m, β j ^ ((bitExpo (m := m) i) j)) := by
  unfold linearMvExtension
  rw [Polynomial.sum, Polynomial.sum, map_sum]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  rw [MvPolynomial.eval_monomial, Finsupp.prod_pow]

/-- `linearMvExtension` is right inverse to `powAlgHom` on degreewise-linear polynomials.
That is, `powAlgHom` is left-inverse-witnessed and `linearMvExtension ∘ powAlgHom = id`
on `restrictDegree 1`. -/
lemma powAlgHom_mem_degreeLT
    (q : MvPolynomial (Fin m) F) (hq : q ∈ MvPolynomial.restrictDegree (Fin m) F 1) :
    powAlgHom q ∈ Polynomial.degreeLT F (2 ^ m) := by
  rw [Polynomial.mem_degreeLT]
  have hnd : (powAlgHom q).natDegree ≤ 2 ^ m - 1 :=
    powAlgHom_of_restrict_degree_natDegree (p := ⟨q, hq⟩)
  have hlt : (powAlgHom q).natDegree < 2 ^ m :=
    lt_of_le_of_lt hnd (Nat.sub_lt ((by positivity : (0:ℕ) < 2 ^ m)) (by norm_num))
  by_cases h0 : powAlgHom q = 0
  · rw [h0, Polynomial.degree_zero]
    exact bot_lt_iff_ne_bot.mpr (by exact_mod_cast (WithBot.natCast_ne_bot (2 ^ m)))
  · exact (Polynomial.natDegree_lt_iff_degree_lt h0).mp hlt

lemma linearMvExtension_powAlgHom_of_restrictDegree
    (q : MvPolynomial (Fin m) F) (hq : q ∈ MvPolynomial.restrictDegree (Fin m) F 1) :
    linearMvExtension ⟨powAlgHom q, powAlgHom_mem_degreeLT q hq⟩ = q := by
  sorry

end

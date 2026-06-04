import ArkLib.Data.MvPolynomial.LinearMvExtension
import ArkLib.Data.Polynomial.SplitFold
import ArkLib.Data.CodingTheory.ReedSolomon

open LinearMvExtension MvPolynomial Polynomial

noncomputable section

variable {F : Type*} [CommRing F] {m k : ℕ}

/-- `powAlgHom ∘ partialEval` as a single `aeval`. -/
example (q : MvPolynomial (Fin m) F) (αs : Fin k → F) (hk : k ≤ m) :
    powAlgHom (partialEval q αs hk)
      = aeval (fun i : Fin m =>
          if h' : i.val < k then (Polynomial.C (αs ⟨i.val, h'⟩) : F[X])
          else (Polynomial.X : F[X]) ^ (2 ^ (i.val - k))) q := by
  unfold partialEval
  show (powAlgHom : MvPolynomial (Fin (m - k)) F →ₐ[F] F[X]).toRingHom
      (MvPolynomial.eval₂ MvPolynomial.C _ q) = _
  rw [MvPolynomial.eval₂_comp_left powAlgHom.toRingHom
        (MvPolynomial.C : F →+* MvPolynomial (Fin (m - k)) F)]
  rw [MvPolynomial.aeval_def]
  congr 1
  · ext a
    simp [powAlgHom]
  · funext i
    simp only [Function.comp_apply]
    by_cases h' : i.val < k
    · rw [dif_pos h', dif_pos h']; simp [powAlgHom]
    · rw [dif_neg h', dif_neg h']
      simp only [powAlgHom, AlgHom.toRingHom_eq_coe, RingHom.coe_coe, MvPolynomial.aeval_X]

end

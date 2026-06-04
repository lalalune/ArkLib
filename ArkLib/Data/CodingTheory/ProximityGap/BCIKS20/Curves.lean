/-
Copyright (c) 2024-2025 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao, Katerina Hristova, František Silváši, Julian Sutherland,
         Ilia Vlasov, Chung Thai Nguyen
-/

import ArkLib.Data.CodingTheory.ProximityGap.BCIKS20.ErrorBound
import ArkLib.Data.CodingTheory.ReedSolomon
import ArkLib.ToMathlib.Polynomial.EvalExt

namespace ProximityGap

open NNReal Finset Function ProbabilityTheory
open scoped BigOperators LinearCode ProbabilityTheory
open Code

section CoreResults

variable {ι : Type} [Fintype ι] [Nonempty ι] [DecidableEq ι]
variable {F : Type} [Field F] [Fintype F] [DecidableEq F]


omit [DecidableEq ι] in
/-- Theorem 1.5 (Correlated agreement for low-degree parameterised curves) in [BCIKS20].

Take a Reed-Solomon code of length `ι` and degree `deg`, a proximity-error parameter
pair `(δ, ε)` and a curve passing through words `u₀, ..., uκ`, such that
the probability that a random point on the curve is `δ`-close to the Reed-Solomon code
is at most `ε`. Then, the words `u₀, ..., uκ` have correlated agreement. -/
theorem correlatedAgreement_affine_curves {k : ℕ}
    {deg : ℕ} {domain : ι ↪ F} {δ : ℝ≥0}
    (hδ : δ ≤ 1 - ReedSolomon.sqrtRate deg domain) :
    δ_ε_correlatedAgreementCurves (k := k) (A := F) (F := F) (ι := ι)
      (C := ReedSolomon.code domain deg) (δ := δ) (ε := errorBound δ deg domain) := by
  sorry

end CoreResults

section BCIKS20ProximityGapSection6

variable {F : Type} [Field F] [Fintype F] [DecidableEq F]
variable {n : ℕ} [NeZero n]

/-- The parameters for which the curve points are `δ`-close to a set `V`
(typically, a linear code). This is the set `S` from the proximity gap paper. -/
noncomputable def coeffs_of_close_proximity_curve {l : ℕ}
    (δ : ℚ≥0) (u : Fin l → Fin n → F) (V : Finset (Fin n → F)) : Finset F :=
  have : Fintype { z | δᵣ(Curve.polynomialCurveEval (F := F) (A := F) u z, V) ≤ δ } := by
    infer_instance
  @Set.toFinset _ { z | δᵣ(Curve.polynomialCurveEval (F := F) (A := F) u z, V) ≤ δ } this

/-- Propagation brick for the §6.1 argument: two polynomial curves of degree `< l`
that agree in coordinate `x` on at least `l` parameter values agree in that
coordinate everywhere. -/
private lemma polynomialCurveEval_coord_eq_of_agree {n l : ℕ} {F : Type} [Field F]
    [DecidableEq F] {u v : Fin l → Fin n → F} {x : Fin n}
    {Zs : Finset F} (hZ : l ≤ Zs.card)
    (h : ∀ z ∈ Zs, Curve.polynomialCurveEval (F := F) (A := F) u z x
      = Curve.polynomialCurveEval (F := F) (A := F) v z x) :
    ∀ z : F, Curve.polynomialCurveEval (F := F) (A := F) u z x
      = Curve.polynomialCurveEval (F := F) (A := F) v z x := by
  -- coordinate-wise polynomial packaging
  have hEval : ∀ (a : Fin l → Fin n → F) (w : F),
      (∑ i : Fin l, Polynomial.C (a i x) * Polynomial.X ^ (i : ℕ)).eval w
        = Curve.polynomialCurveEval (F := F) (A := F) a w x := by
    intro a w
    rw [Polynomial.eval_finset_sum]
    simp only [Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X,
      Curve.polynomialCurveEval, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
    exact Finset.sum_congr rfl fun i _ => mul_comm _ _
  have hdeg : ∀ (a : Fin l → Fin n → F),
      (∑ i : Fin l, Polynomial.C (a i x) * Polynomial.X ^ (i : ℕ)).degree < ((l : ℕ) : WithBot ℕ) := by
    intro a
    apply lt_of_le_of_lt (Polynomial.degree_sum_le _ _)
    rw [Finset.sup_lt_iff (by exact_mod_cast WithBot.bot_lt_coe l)]
    intro i _
    exact lt_of_le_of_lt (Polynomial.degree_C_mul_X_pow_le _ _) (by exact_mod_cast i.isLt)
  have hPQ := Polynomial.eq_of_eval_eq_degree (n := l) (hdeg u) (hdeg v) Zs hZ
    (fun w hw => by rw [hEval u, hEval v]; exact h w hw)
  intro z
  calc Curve.polynomialCurveEval (F := F) (A := F) u z x
      = (∑ i : Fin l, Polynomial.C (u i x) * Polynomial.X ^ (i : ℕ)).eval z := (hEval u z).symm
    _ = (∑ i : Fin l, Polynomial.C (v i x) * Polynomial.X ^ (i : ℕ)).eval z := by rw [hPQ]
    _ = Curve.polynomialCurveEval (F := F) (A := F) v z x := hEval v z

/-- Unique decoding brick for the §6.1 argument: two codewords of a code with
minimum distance `d` that are both within distance summing below `d` of a common
word are equal (triangle inequality). -/
private lemma eq_of_both_close_lt_minDist {n : ℕ} {F : Type} [DecidableEq F]
    {V : Finset (Fin n → F)} {d : ℕ}
    (hV : ∀ w ∈ V, ∀ w' ∈ V, w ≠ w' → d ≤ Δ₀(w, w'))
    {w₁ w₂ f : Fin n → F} (h₁ : w₁ ∈ V) (h₂ : w₂ ∈ V)
    (hsum : Δ₀(w₁, f) + Δ₀(f, w₂) < d) :
    w₁ = w₂ := by
  by_contra hne
  have htri : Δ₀(w₁, w₂) ≤ Δ₀(w₁, f) + Δ₀(f, w₂) := hammingDist_triangle w₁ f w₂
  exact absurd (le_trans (hV w₁ h₁ w₂ h₂ hne) htri) (not_le.mpr hsum)

/-- If the set of points `δ`-close to the code `V` has at least `n * l + 1` points, then
there exists a curve defined by vectors `v` from `V` such that the points of `curve u`
and `curve v` are `δ`-close with the same parameters. Moreover, `u` and `v` differ at
at most `δ * n` positions. -/
theorem large_agreement_set_on_curve_implies_correlated_agreement {l : ℕ}
    {rho : ℚ≥0}
    {δ : ℚ≥0}
    {V : Finset (Fin n → F)}
    -- Finding 15 repair: `V` must be a code of rate `rho` (min relative distance ≥ 1 − rho);
    -- with `rho` free and `V` arbitrary the statement is false (counterexample in
    -- research/formal/arklib-patches/upstream-issues.md, Finding 15).
    (hV : ∀ w ∈ V, ∀ w' ∈ V, w ≠ w' → (1 - rho) * n ≤ (Δ₀(w, w') : ℚ≥0))
    (hδ : δ ≤ (1 - rho) / 2)
    {u : Fin l → Fin n → F}
    (hS : n * l < (coeffs_of_close_proximity_curve (F := F) δ u V).card) :
    coeffs_of_close_proximity_curve (F := F) δ u V = Finset.univ ∧
      ∃ v : Fin l → Fin n → F,
        ∀ z,
          δᵣ(Curve.polynomialCurveEval (F := F) (A := F) u z,
            Curve.polynomialCurveEval (F := F) (A := F) v z) ≤ δ ∧
          ({ x : Fin n | ∃ i, u i x ≠ v i x } : Finset _).card ≤ δ * n := by
  sorry

/-- The distance bound from [BCIKS20]. -/
noncomputable def δ₀ (rho : ℚ) (m : ℕ) : ℝ :=
  1 - Real.sqrt rho - Real.sqrt rho / (2 * m)

/-- If the set of points on the curve defined by `u` close to `V` has at least
`((1 + 1 / (2 * m)) ^ 7 * m ^ 7) / (3 * (Real.rpow rho (3 / 2 : ℚ))) * n ^ 2 * l + 1`
points, then there exist vectors `v` from `V` that are `(1 - δ) * n` close to `u`. -/
theorem large_agreement_set_on_curve_implies_correlated_agreement' {l : ℕ}
    [Finite F]
    {m : ℕ}
    {rho : ℚ≥0}
    {δ : ℚ≥0}
    (hm : 3 ≤ m)
    {V : Finset (Fin n → F)}
    -- Finding 15 repair (same defect as the unique-decoding lemma above).
    (hV : ∀ w ∈ V, ∀ w' ∈ V, w ≠ w' → (1 - rho) * n ≤ (Δ₀(w, w') : ℚ≥0))
    (hδ : δ ≤ δ₀ rho m)
    {u : Fin l → Fin n → F}
    (hS : ((1 + 1 / (2 * m)) ^ 7 * m ^ 7) / (3 * (Real.rpow rho (3 / 2 : ℚ)))
      * n ^ 2 * l < (coeffs_of_close_proximity_curve (F := F) δ u V).card) :
    ∃ v : Fin l → Fin n → F,
      ∀ i, v i ∈ V ∧
        (1 - δ) * n ≤ ({ x : Fin n | ∀ i, u i x = v i x } : Finset _).card := by
  sorry

end BCIKS20ProximityGapSection6

end ProximityGap

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

-- Decidability instances are threaded through the sections for the §6 machinery;
-- several statement-level bricks do not mention them directly.
set_option linter.unusedDecidableInType false
set_option linter.unusedSectionVars false

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
      (∑ i : Fin l, Polynomial.C (a i x) * Polynomial.X ^ (i : ℕ)).degree < ((l : ℕ) : WithBot ℕ)
        := by
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

/-- Counting brick for the §6.1 argument (generic double counting): if every
`z ∈ S` has a bad-set of size at most `m`, then the number of coordinates that
are bad for at least `t` elements of `S` is bounded: `t · #poor ≤ m · #S`. -/
private lemma card_heavyCoords_mul_le {α β : Type} [Fintype α] [DecidableEq α]
    [DecidableEq β] {S : Finset β} {B : β → Finset α} {m : ℕ}
    (hB : ∀ z ∈ S, (B z).card ≤ m) (t : ℕ) :
    ((Finset.univ : Finset α).filter
      (fun x => t ≤ (S.filter (fun z => x ∈ B z)).card)).card * t
      ≤ m * S.card := by
  classical
  -- double counting: Σ_x #{z ∈ S : x ∈ B z} = Σ_{z ∈ S} #(B z)
  have hswap : ∑ x : α, (S.filter (fun z => x ∈ B z)).card
      = ∑ z ∈ S, (B z).card := by
    have h1 : ∀ x : α, (S.filter (fun z => x ∈ B z)).card
        = ∑ z ∈ S, if x ∈ B z then 1 else 0 := fun x => Finset.card_filter _ _
    have h2 : ∀ z : β, (B z).card = ∑ x : α, if x ∈ B z then 1 else 0 := by
      intro z
      rw [← Finset.card_filter, Finset.filter_univ_mem]
    simp only [h1, h2]
    exact Finset.sum_comm
  have hbound : ∑ z ∈ S, (B z).card ≤ m * S.card := by
    calc ∑ z ∈ S, (B z).card ≤ ∑ _z ∈ S, m := Finset.sum_le_sum hB
      _ = m * S.card := by rw [Finset.sum_const, smul_eq_mul, mul_comm]
  have hfilter : ((Finset.univ : Finset α).filter
      (fun x => t ≤ (S.filter (fun z => x ∈ B z)).card)).card * t
      ≤ ∑ x : α, (S.filter (fun z => x ∈ B z)).card := by
    calc ((Finset.univ : Finset α).filter
        (fun x => t ≤ (S.filter (fun z => x ∈ B z)).card)).card * t
        = ∑ _x ∈ (Finset.univ : Finset α).filter
            (fun x => t ≤ (S.filter (fun z => x ∈ B z)).card), t := by
          rw [Finset.sum_const, smul_eq_mul]
      _ ≤ ∑ x ∈ (Finset.univ : Finset α).filter
            (fun x => t ≤ (S.filter (fun z => x ∈ B z)).card),
            (S.filter (fun z => x ∈ B z)).card :=
          Finset.sum_le_sum fun x hx => (Finset.mem_filter.mp hx).2
      _ ≤ ∑ x : α, (S.filter (fun z => x ∈ B z)).card :=
          Finset.sum_le_sum_of_subset (Finset.filter_subset _ _)
  exact le_trans hfilter (hswap ▸ hbound)

/-- Interpolation brick for the §6.1 argument: through any `l` distinct parameter
values and arbitrary target vectors there is a polynomial curve of degree `< l`. -/
private lemma exists_polynomialCurve_through {n l : ℕ} {F : Type} [Field F]
    [DecidableEq F] (zs : Fin l → F) (hinj : Function.Injective zs)
    (w : Fin l → Fin n → F) :
    ∃ v : Fin l → Fin n → F,
      ∀ j, Curve.polynomialCurveEval (F := F) (A := F) v (zs j) = w j := by
  -- per-coordinate Lagrange interpolant
  classical
  set P : Fin n → Polynomial F :=
    fun x => Lagrange.interpolate Finset.univ zs (fun j => w j x) with hP
  have hdeg : ∀ x, (P x).degree < (l : WithBot ℕ) := by
    intro x
    simpa using Lagrange.degree_interpolate_lt (s := (Finset.univ : Finset (Fin l)))
      (v := zs) (r := fun j => w j x) (fun a _ b _ hab => hinj hab)
  refine ⟨fun i x => (P x).coeff i, ?_⟩
  intro j
  funext x
  have hnat : (P x).natDegree < l := by
    rcases eq_or_ne (P x) 0 with h0 | h0
    · simpa [h0] using j.pos
    · exact (Polynomial.natDegree_lt_iff_degree_lt h0).mpr (by exact_mod_cast hdeg x)
  have heval : (P x).eval (zs j) = w j x :=
    Lagrange.eval_interpolate_at_node (s := (Finset.univ : Finset (Fin l)))
      (v := zs) (r := fun j => w j x) (fun a _ b _ hab => hinj hab) (Finset.mem_univ j)
  calc Curve.polynomialCurveEval (F := F) (A := F) (fun i x => (P x).coeff i) (zs j) x
      = ∑ i : Fin l, (zs j) ^ (i : ℕ) * (P x).coeff i := by
        simp [Curve.polynomialCurveEval, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
    _ = ∑ i ∈ Finset.range l, (P x).coeff i * (zs j) ^ i := by
        rw [← Fin.sum_univ_eq_sum_range (fun i => (P x).coeff i * (zs j) ^ i)]
        exact Finset.sum_congr rfl fun i _ => mul_comm _ _
    _ = (P x).eval (zs j) := (Polynomial.eval_eq_sum_range' hnat _).symm
    _ = w j x := heval

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
        -- Finding 15b repair: the witness curve must pass through codewords —
        -- without `∀ i, v i ∈ V` the existential is satisfied by `v := u` (vacuous).
        (∀ i, v i ∈ V) ∧
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

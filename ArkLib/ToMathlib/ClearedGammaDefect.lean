/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.BCIKS20.P1MonicIntegrality
import ArkLib.Data.CodingTheory.ProximityGap.BCIKS20.P2MonicConsequences
import ArkLib.ToMathlib.WeightLambdaCalculus
import ArkLib.ToMathlib.SbetaPackaging

/-!
# The cleared per-coordinate defect element (BCIKS20 eq. (5.16)) and its Lemma-A.1 kill

This file builds the **paper-literal Claim 5.10 core** for issue #304, in the monic regime.
[BCIKS20] §5.2.7 (proof of Claim 5.10, eq. (5.16)) clears the denominators of the truncated
Hensel value `γ_k(x) = ∑_{t≤k} α_t (x−x₀)^t` into the regular element

  `β(x) := ∑_{t≤k} β_t · (x−x₀)^t · W^{k−t} · ξ^{e_k−e_t} ∈ 𝒪`,

subtracts the cleared ground-line section `(u₀(x) + Z·u₁(x))·W^{k+1}·ξ^{e_k}`, bounds the
weight of the difference by `(2k+1)dD` via Claim A.2's **linear** budget, observes that the
difference's `π_z`-fibers vanish on the matching set `S'_x`, and kills it by Lemma A.1 —
concluding `γ_k(x) = u₀(x) + Z·u₁(x)` in `𝕃`.

Here we realize that argument against the in-tree genuine numerators `βHensel` (monic `H`, so
`W = 1` and the lift identity is unconditional via
`faaDiBrunoSuccSumZeroResidual_of_leadingCoeff_one`):

* `eClear` — the Claim-A.2 denominator exponent `e_t = max(0, 2t−1)` (`ℕ`-truncated).
* `scalar𝒪` / `wSection` — the scalar and ground-line-section regular elements, with their
  embeddings, `π_z`-readings, and weights (`weight_wSection_le` : `Λ ≤ 1`).
* `betaCleared` / `betaDefect` — eq. (5.16)'s cleared sum and defect element.
* `embed_betaDefect` — the embedding identity
  `embed(betaDefect) = (γ_k(x) − (a + Z·b)) · ξ̂^{e_k}` (monic).
* `weight_betaDefect_le` — the defect weight from **any** per-order linear budget on the
  `βHensel` (the proven loose Claim-A.2 shape suffices; no weight-1 invariant anywhere).
* `pi_z_betaDefect_eq_zero` — per-place vanishing from the per-place reading
  `π_z(β_t) = p.coeff t · π_z(ξ)^{2t−1}` and the word-match `p(x−x₀) = a + z·b`.
* `gammaEvalTrunc_eq_ground_of_large` — **the Claim 5.10 capstone**: a matching set larger
  than `N·d_H` (with `N` any number dominating the defect budget) forces
  `γ_k(x) = fieldTo𝕃 a + Z·fieldTo𝕃 b` — the per-coordinate ground-line value, the exact
  per-point input of the Claim 5.9 interpolation (`GroundLineInterpolation.lean`).

No sharp per-order weight-1 invariant is used anywhere: the budget hypotheses are satisfied by
the proven linear collapse (`BetaWeightCollapse.betaRec_weight_le_concrete` /
`BetaWeightGradedAssembly.betaRec_weight_le_graded` after the `betaRec`/`βHensel` bridge).
Axiom-clean.

## References

* [BCIKS20] Ben-Sasson, Carmon, Ishai, Kopparty, Saraf, *Proximity Gaps for Reed–Solomon
  Codes*, §5.2.7 (Claims 5.9–5.11, eq. (5.16)), Appendix A.2–A.4.
-/

noncomputable section

open Polynomial Polynomial.Bivariate BCIKS20AppendixA BCIKS20AppendixA.ClaimA2
open BCIKS20.HenselNumerator

namespace ArkLib.ClearedGammaDefect

variable {F : Type} [Field F]
variable (H : F[X][Y]) [Fact (Irreducible H)] [Fact (0 < H.natDegree)]

/-! ## The denominator exponent -/

/-- The Claim-A.2 denominator exponent `e_t = max(0, 2t−1)`, as `ℕ`-truncated subtraction
(`e_0 = 0`, `e_t = 2t−1` for `t ≥ 1`). -/
def eClear (t : ℕ) : ℕ := 2 * t - 1

lemma eClear_mono {t k : ℕ} (h : t ≤ k) : eClear t ≤ eClear k := by
  unfold eClear; omega

/-- Exponent recombination: `(2t−1) + (e_k − e_t) = e_k` for `t ≤ k`. -/
lemma eClear_add_sub {t k : ℕ} (h : t ≤ k) : (2 * t - 1) + (eClear k - eClear t) = eClear k := by
  unfold eClear; omega

/-! ## Scalar and section elements -/

/-- The scalar `c : F` as a regular element of `𝒪 H`. -/
def scalar𝒪 (c : F) : 𝒪 H :=
  Ideal.Quotient.mk (Ideal.span {H_tilde' H}) (Polynomial.C (Polynomial.C c))

/-- The ground-line section `a + Z·b` as a regular element of `𝒪 H` (the inner `Polynomial.X`
is the ground `Z`-variable). -/
def wSection (a b : F) : 𝒪 H :=
  Ideal.Quotient.mk (Ideal.span {H_tilde' H})
    (Polynomial.C (Polynomial.C a + Polynomial.X * Polynomial.C b))

@[simp]
lemma embed_scalar𝒪 (c : F) :
    embeddingOf𝒪Into𝕃 H (scalar𝒪 H c) = fieldTo𝕃 c := by
  unfold scalar𝒪
  rw [embeddingOf𝒪Into𝕃_mk, liftBivariate_C]; rfl

@[simp]
lemma pi_z_scalar𝒪 {z : F} (root : rationalRoot (H_tilde' H) z) (c : F) :
    π_z z root (scalar𝒪 H c) = c := by
  unfold scalar𝒪
  rw [π_z_mk, Polynomial.evalEval_C, Polynomial.eval_C]

/-- The section embeds as the ground-line value `fieldTo𝕃 a + Z·fieldTo𝕃 b`, with
`Z = liftToFunctionField X`. -/
lemma embed_wSection (a b : F) :
    embeddingOf𝒪Into𝕃 H (wSection H a b)
      = fieldTo𝕃 a + liftToFunctionField (H := H) Polynomial.X * fieldTo𝕃 b := by
  unfold wSection
  rw [embeddingOf𝒪Into𝕃_mk, liftBivariate_C, map_add, map_mul]; rfl

/-- The section reads the line value at every place: `π_z(wSection a b) = a + z·b`. -/
lemma pi_z_wSection {z : F} (root : rationalRoot (H_tilde' H) z) (a b : F) :
    π_z z root (wSection H a b) = a + z * b := by
  unfold wSection
  rw [π_z_mk, Polynomial.evalEval_C]
  simp

/-- The section has weight `≤ 1` (`Y`-degree `0`, ground degree `≤ 1`). -/
lemma weight_wSection_le {D : ℕ} (hD : Bivariate.totalDegree H ≤ D) (hH : 0 < H.natDegree)
    (a b : F) :
    weight_Λ_over_𝒪 hH (wSection H a b) D ≤ (WithBot.some 1 : WithBot ℕ) := by
  refine (weight_Λ_over_𝒪_C_le hD hH (Polynomial.C a + Polynomial.X * Polynomial.C b)).trans ?_
  refine WithBot.coe_le_coe.mpr ?_
  refine (Polynomial.natDegree_add_le _ _).trans ?_
  have h1 : (Polynomial.C a : F[X]).natDegree = 0 := Polynomial.natDegree_C a
  have h2 : (Polynomial.X * Polynomial.C b : F[X]).natDegree ≤ 1 := by
    refine Polynomial.natDegree_mul_le.trans ?_
    rw [Polynomial.natDegree_X, Polynomial.natDegree_C]
  omega

/-- The scalar has weight `≤ 0`. -/
lemma weight_scalar𝒪_le {D : ℕ} (hD : Bivariate.totalDegree H ≤ D) (hH : 0 < H.natDegree)
    (c : F) :
    weight_Λ_over_𝒪 hH (scalar𝒪 H c) D ≤ (WithBot.some 0 : WithBot ℕ) := by
  refine (weight_Λ_over_𝒪_C_le hD hH (Polynomial.C c)).trans ?_
  rw [Polynomial.natDegree_C]

/-! ## The cleared sum and the defect element (eq. (5.16), monic) -/

/-- **Eq. (5.16)'s cleared sum (monic `W = 1`)**: the truncated Hensel value `γ_k(x)` with
denominators cleared into `𝒪 H`:
`betaCleared = ∑_{t≤k} (x−x₀)^t • β_t · ξ^{e_k−e_t}`. -/
def betaCleared (x₀ x : F) (R : F[X][X][Y]) (hHyp : ClaimA2.Hypotheses x₀ R H) (k : ℕ) : 𝒪 H :=
  ∑ t ∈ Finset.range (k + 1),
    scalar𝒪 H ((x - x₀) ^ t)
      * (βHensel H x₀ R hHyp t * (ClaimA2.ξ x₀ R H hHyp) ^ (eClear k - eClear t))

/-- **The defect element**: the cleared sum minus the cleared ground-line section. Its
vanishing is exactly `γ_k(x) = a + Z·b`. -/
def betaDefect (x₀ x a b : F) (R : F[X][X][Y]) (hHyp : ClaimA2.Hypotheses x₀ R H) (k : ℕ) :
    𝒪 H :=
  betaCleared H x₀ x R hHyp k - wSection H a b * (ClaimA2.ξ x₀ R H hHyp) ^ (eClear k)

/-- The truncated Hensel value `γ_k(x) = ∑_{t≤k} α_t · (x−x₀)^t ∈ 𝕃 H`. -/
def gammaEvalTrunc (x₀ x : F) (R : F[X][X][Y]) (hHyp : ClaimA2.Hypotheses x₀ R H) (k : ℕ) :
    𝕃 H :=
  ∑ t ∈ Finset.range (k + 1), αGenuine H x₀ R hHyp t * fieldTo𝕃 (x - x₀) ^ t

/-! ## The embedding identity -/

/-- **The eq. (5.16) embedding identity (monic).** The cleared sum embeds as
`γ_k(x) · ξ̂^{e_k}`. -/
theorem embed_betaCleared (hlc : H.leadingCoeff = 1) (x₀ x : F) (R : F[X][X][Y])
    (hHyp : ClaimA2.Hypotheses x₀ R H) (k : ℕ) :
    embeddingOf𝒪Into𝕃 H (betaCleared H x₀ x R hHyp k)
      = gammaEvalTrunc H x₀ x R hHyp k
          * (embeddingOf𝒪Into𝕃 H (ClaimA2.ξ x₀ R H hHyp)) ^ (eClear k) := by
  have hzero := faaDiBrunoSuccSumZeroResidual_of_leadingCoeff_one H x₀ R hHyp hlc
  unfold betaCleared gammaEvalTrunc
  rw [map_sum, Finset.sum_mul]
  refine Finset.sum_congr rfl (fun t ht => ?_)
  have htk : t ≤ k := Nat.lt_succ_iff.mp (Finset.mem_range.mp ht)
  rw [map_mul, map_mul, map_pow, embed_scalar𝒪,
    βHensel_lift_identity H x₀ R hHyp hzero t, hlc, map_one, one_pow, mul_one,
    map_pow, ← map_pow fieldTo𝕃 (x - x₀) t]
  rw [mul_assoc, ← pow_add, eClear_add_sub htk]
  ring

/-- **The defect embedding identity (monic).**
`embed(betaDefect) = (γ_k(x) − (fieldTo𝕃 a + Z·fieldTo𝕃 b)) · ξ̂^{e_k}`. -/
theorem embed_betaDefect (hlc : H.leadingCoeff = 1) (x₀ x a b : F) (R : F[X][X][Y])
    (hHyp : ClaimA2.Hypotheses x₀ R H) (k : ℕ) :
    embeddingOf𝒪Into𝕃 H (betaDefect H x₀ x a b R hHyp k)
      = (gammaEvalTrunc H x₀ x R hHyp k
            - (fieldTo𝕃 a + liftToFunctionField (H := H) Polynomial.X * fieldTo𝕃 b))
          * (embeddingOf𝒪Into𝕃 H (ClaimA2.ξ x₀ R H hHyp)) ^ (eClear k) := by
  unfold betaDefect
  rw [map_sub, map_mul, map_pow, embed_betaCleared H hlc x₀ x R hHyp k, embed_wSection, sub_mul]

/-! ## The weight bound (from ANY linear per-order budget) -/

/-- **The defect weight bound, `ℕ`-budget form.** From any per-order budget `wβ` on the
numerators (`Λ(β_t) ≤ wβ t`) and a `ξ`-budget `bξ`, every cleared term is bounded by
`wβ t + (e_k−e_t)·bξ` and the section term by `1 + e_k·bξ`; any `N` dominating all of them
bounds the defect. The proven loose Claim-A.2 collapse supplies `wβ t = (2t+1)·d_R·D`. -/
theorem weight_betaDefect_le {D : ℕ} (hD : Bivariate.totalDegree H ≤ D) (hH : 0 < H.natDegree)
    (x₀ x a b : F) (R : F[X][X][Y]) (hHyp : ClaimA2.Hypotheses x₀ R H) (k : ℕ)
    (wβ : ℕ → ℕ) (bξ N : ℕ)
    (hwβ : ∀ t ∈ Finset.range (k + 1),
      weight_Λ_over_𝒪 hH (βHensel H x₀ R hHyp t) D ≤ (WithBot.some (wβ t) : WithBot ℕ))
    (hbξ : weight_Λ_over_𝒪 hH (ClaimA2.ξ x₀ R H hHyp) D ≤ (WithBot.some bξ : WithBot ℕ))
    (hN1 : ∀ t ≤ k, wβ t + (eClear k - eClear t) * bξ ≤ N)
    (hN2 : 1 + eClear k * bξ ≤ N) :
    weight_Λ_over_𝒪 hH (betaDefect H x₀ x a b R hHyp k) D
      ≤ (WithBot.some N : WithBot ℕ) := by
  unfold betaDefect
  refine (weight_Λ_over_𝒪_sub_le hD hH _ _).trans (max_le ?_ ?_)
  · -- the cleared sum: each term ≤ 0 + (wβ t + (e_k − e_t)·bξ) ≤ N.
    unfold betaCleared
    refine (weight_Λ_over_𝒪_sum_le hD hH _ _).trans (Finset.sup_le (fun t ht => ?_))
    have htk : t ≤ k := Nat.lt_succ_iff.mp (Finset.mem_range.mp ht)
    refine weight_Λ_over_𝒪_le_trans_nat hH
      (weight_Λ_over_𝒪_mul_le_of_le hD hH (weight_scalar𝒪_le H hD hH _)
        (weight_Λ_over_𝒪_mul_le_of_le hD hH (hwβ t ht)
          (weight_Λ_over_𝒪_pow_le_of_le hD hH hbξ _))) ?_
    have := hN1 t htk
    omega
  · -- the section term: ≤ 1 + e_k·bξ ≤ N.
    refine weight_Λ_over_𝒪_le_trans_nat hH
      (weight_Λ_over_𝒪_mul_le_of_le hD hH (weight_wSection_le H hD hH a b)
        (weight_Λ_over_𝒪_pow_le_of_le hD hH hbξ _)) hN2

/-! ## Per-place vanishing -/

/-- **The per-place defect vanishing.** At a place `(z, t_z)` where the numerators read off a
decoded polynomial `p` (`π_z(β_t) = p.coeff t · π_z(ξ)^{2t−1}`, the reading-lane currency) and
the word matches the line (`p(x−x₀) = a + z·b`), the defect's fiber vanishes. -/
theorem pi_z_betaDefect_eq_zero (x₀ x a b : F) (R : F[X][X][Y])
    (hHyp : ClaimA2.Hypotheses x₀ R H) (k : ℕ) {z : F}
    (root : rationalRoot (H_tilde' H) z) (p : F[X]) (hpdeg : p.natDegree ≤ k)
    (hread : ∀ t ∈ Finset.range (k + 1),
      π_z z root (βHensel H x₀ R hHyp t)
        = p.coeff t * (π_z z root (ClaimA2.ξ x₀ R H hHyp)) ^ (2 * t - 1))
    (hmatch : p.eval (x - x₀) = a + z * b) :
    π_z z root (betaDefect H x₀ x a b R hHyp k) = 0 := by
  unfold betaDefect betaCleared
  rw [map_sub, map_sum]
  have hsum : ∀ t ∈ Finset.range (k + 1),
      π_z z root (scalar𝒪 H ((x - x₀) ^ t)
          * (βHensel H x₀ R hHyp t * (ClaimA2.ξ x₀ R H hHyp) ^ (eClear k - eClear t)))
        = p.coeff t * (x - x₀) ^ t
            * (π_z z root (ClaimA2.ξ x₀ R H hHyp)) ^ (eClear k) := by
    intro t ht
    have htk : t ≤ k := Nat.lt_succ_iff.mp (Finset.mem_range.mp ht)
    rw [map_mul, map_mul, map_pow, pi_z_scalar𝒪, hread t ht, mul_assoc, ← pow_add,
      eClear_add_sub htk]
    ring
  rw [Finset.sum_congr rfl hsum, map_mul, map_pow, pi_z_wSection, ← Finset.sum_mul]
  have heval : ∑ t ∈ Finset.range (k + 1), p.coeff t * (x - x₀) ^ t = p.eval (x - x₀) :=
    (Polynomial.eval_eq_sum_range' (Nat.lt_succ_of_le hpdeg) (x - x₀)).symm
  rw [heval, hmatch, sub_self]

/-! ## The Claim 5.10 capstone -/

/-- `WithBot` bookkeeping: a weight bound `≤ N` multiplies to `≤ N·d` on the right. -/
private lemma withBot_mul_nat_le {a : WithBot ℕ} {c d : ℕ}
    (h : a ≤ (WithBot.some c : WithBot ℕ)) :
    a * (d : WithBot ℕ) ≤ ((c * d : ℕ) : WithBot ℕ) := by
  have hcd : ((c * d : ℕ) : WithBot ℕ) = (c : WithBot ℕ) * (d : WithBot ℕ) := by
    push_cast; ring
  rw [hcd]
  gcongr

/-- **The Claim 5.10 capstone (monic): the per-coordinate ground-line value from counting.**

If at the coordinate `x` there is a set `S` of places, each carrying the reading of a decoded
polynomial matching the line `a + z·b`, with `|S| > N·d_H` for any `N` dominating the defect
budget, then the truncated Hensel value at `x` IS the ground-line value:
`γ_k(x) = fieldTo𝕃 a + Z·fieldTo𝕃 b`.

This is the exact per-point input of the Claim 5.9 interpolation
(`GroundLineInterpolation.groundLine_of_eval_groundLine` at the `k+1` chosen coordinates). -/
theorem gammaEvalTrunc_eq_ground_of_large (hlc : H.leadingCoeff = 1)
    {D : ℕ} (hD : Bivariate.totalDegree H ≤ D) (hH : 0 < H.natDegree)
    (x₀ x a b : F) (R : F[X][X][Y]) (hHyp : ClaimA2.Hypotheses x₀ R H) (k : ℕ)
    (wβ : ℕ → ℕ) (bξ N : ℕ)
    (hwβ : ∀ t ∈ Finset.range (k + 1),
      weight_Λ_over_𝒪 hH (βHensel H x₀ R hHyp t) D ≤ (WithBot.some (wβ t) : WithBot ℕ))
    (hbξ : weight_Λ_over_𝒪 hH (ClaimA2.ξ x₀ R H hHyp) D ≤ (WithBot.some bξ : WithBot ℕ))
    (hN1 : ∀ t ≤ k, wβ t + (eClear k - eClear t) * bξ ≤ N)
    (hN2 : 1 + eClear k * bξ ≤ N)
    (S : Finset F)
    (hS : ∀ z ∈ S, ∃ root : rationalRoot (H_tilde' H) z, ∃ p : F[X],
      p.natDegree ≤ k
        ∧ (∀ t ∈ Finset.range (k + 1),
            π_z z root (βHensel H x₀ R hHyp t)
              = p.coeff t * (π_z z root (ClaimA2.ξ x₀ R H hHyp)) ^ (2 * t - 1))
        ∧ p.eval (x - x₀) = a + z * b)
    (hcard : N * H.natDegree < S.card) :
    gammaEvalTrunc H x₀ x R hHyp k
      = fieldTo𝕃 a + liftToFunctionField (H := H) Polynomial.X * fieldTo𝕃 b := by
  -- Step 1: every place of `S` is a vanishing place of the defect.
  have hT : (↑S : Set F) ⊆ S_β (betaDefect H x₀ x a b R hHyp k) := by
    intro z hz
    obtain ⟨root, p, hpdeg, hread, hmatch⟩ := hS (by exact_mod_cast hz)
    exact ⟨root, pi_z_betaDefect_eq_zero H x₀ x a b R hHyp k root p hpdeg hread hmatch⟩
  -- Step 2: the counting beats the weight; Lemma A.1 kills the defect's embedding.
  have hwt := weight_betaDefect_le H hD hH x₀ x a b R hHyp k wβ bξ N hwβ hbξ hN1 hN2
  have hbig : (↑S.card : WithBot ℕ)
      > weight_Λ_over_𝒪 hH (betaDefect H x₀ x a b R hHyp k) D * H.natDegree := by
    refine lt_of_le_of_lt (withBot_mul_nat_le hwt) ?_
    exact_mod_cast hcard
  have hzero : embeddingOf𝒪Into𝕃 _ (betaDefect H x₀ x a b R hHyp k) = 0 :=
    ArkLib.embedding_eq_zero_of_finset_subset_S_β hH _ D hD hT hbig
  -- Step 3: the embedding identity + `ξ̂` a unit (monic) force the ground-line value.
  rw [embed_betaDefect H hlc x₀ x a b R hHyp k] at hzero
  have hu : IsUnit (embeddingOf𝒪Into𝕃 H (ClaimA2.ξ x₀ R H hHyp)) :=
    (isUnit_ξ_of_monic H x₀ R hHyp hlc).map (embeddingOf𝒪Into𝕃 H)
  have hxine : (embeddingOf𝒪Into𝕃 H (ClaimA2.ξ x₀ R H hHyp)) ^ (eClear k) ≠ 0 :=
    pow_ne_zero _ hu.ne_zero
  rcases mul_eq_zero.mp hzero with hmain | hxi
  · exact sub_eq_zero.mp hmain
  · exact absurd hxi hxine

end ArkLib.ClearedGammaDefect

section AxiomAudit
#print axioms ArkLib.ClearedGammaDefect.eClear_add_sub
#print axioms ArkLib.ClearedGammaDefect.embed_wSection
#print axioms ArkLib.ClearedGammaDefect.pi_z_wSection
#print axioms ArkLib.ClearedGammaDefect.weight_wSection_le
#print axioms ArkLib.ClearedGammaDefect.embed_betaCleared
#print axioms ArkLib.ClearedGammaDefect.embed_betaDefect
#print axioms ArkLib.ClearedGammaDefect.weight_betaDefect_le
#print axioms ArkLib.ClearedGammaDefect.pi_z_betaDefect_eq_zero
#print axioms ArkLib.ClearedGammaDefect.gammaEvalTrunc_eq_ground_of_large
end AxiomAudit

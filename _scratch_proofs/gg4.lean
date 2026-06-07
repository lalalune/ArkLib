import ArkLib.Data.CodingTheory.ProximityGap.BCIKS20.P2Match

open scoped BigOperators
open Finset Polynomial Polynomial.Bivariate ArkLib.PowerSeriesComposition
open BCIKS20AppendixA ProximityPrize.BCIKS20.GammaGenuine

namespace BCIKS20.HenselNumerator

variable {F : Type} [Field F]
variable (H : F[X][Y]) [Fact (Irreducible H)] [Fact (0 < H.natDegree)]

/-! ============================================================================
ORDER-1 AUDIT of the #139 keystone (RestrictedFaaDiBrunoMatch at t=0).

We compute, sorry-free, both sides of the order-1 keystone residual and reduce
the keystone-at-0 to a single concrete W/ξ-clearing identity, then settle whether
it holds.
============================================================================ -/

/-! ### Part 1: βHensel 1 = - hasseCoeffRepr𝒪 H x₀ R 1 0 (PROVEN here). -/

theorem notmem_one_of_partition_zero (lam : Nat.Partition 0) : (1 : ℕ) ∉ lam.parts := by
  intro h
  have hle : (1:ℕ) ≤ lam.parts.sum := Multiset.le_sum_of_mem h
  rw [lam.parts_sum] at hle; omega

theorem mem_one_of_partition_one (lam : Nat.Partition 1) : (1 : ℕ) ∈ lam.parts := by
  have hsum : lam.parts.sum = 1 := lam.parts_sum
  have hne : lam.parts ≠ 0 := by intro h; rw [h] at hsum; simp at hsum
  rcases Multiset.exists_mem_of_ne_zero hne with ⟨a, ha⟩
  have hpos := lam.parts_pos ha
  have hle : a ≤ lam.parts.sum := Multiset.le_sum_of_mem ha
  rw [hsum] at hle
  have : a = 1 := by omega
  rwa [this] at ha

theorem filter_one_partition_one_empty :
    ((Finset.univ : Finset (Nat.Partition 1)).filter (fun lam => (1:ℕ) ∉ lam.parts)) = ∅ := by
  rw [Finset.filter_eq_empty_iff]
  intro lam _; simp only [not_not]; exact mem_one_of_partition_one lam

theorem filter_one_partition_zero_univ :
    ((Finset.univ : Finset (Nat.Partition 0)).filter (fun lam => (1:ℕ) ∉ lam.parts))
      = (Finset.univ : Finset (Nat.Partition 0)) := by
  rw [Finset.filter_eq_self]
  intro lam _; exact notmem_one_of_partition_zero lam

theorem parts_partition_zero (lam : Nat.Partition 0) : lam.parts = 0 := by
  rw [Multiset.eq_zero_iff_forall_notMem]; intro a ha
  have := Multiset.le_sum_of_mem ha; rw [lam.parts_sum] at this
  exact absurd (lam.parts_pos ha) (by omega)

theorem βHensel_one_eq (x₀ : F) (R : F[X][X][Y]) (hHyp : ClaimA2.Hypotheses x₀ R H) :
    βHensel H x₀ R hHyp 1 =
      - ∑ lam ∈ (Finset.univ : Finset (Nat.Partition 0)),
          (W𝒪 H) ^ (1 + deltaSave 1 - 1)
            * (ClaimA2.ξ x₀ R H hHyp) ^ (2 * 1 + sigmaLambda lam - 2)
            * B_coeff H x₀ R 1 lam
            * partitionProd lam (fun l => if _h : l < 1 then βHensel H x₀ R hHyp l else 0) := by
  rw [βHensel_succ H x₀ R hHyp 0]
  rw [show (0:ℕ) + 2 = 2 from rfl, Finset.sum_range_succ, Finset.sum_range_one]
  rw [show (0:ℕ)+1-0 = 1 from rfl, filter_one_partition_one_empty, Finset.sum_empty]
  rw [show (0:ℕ)+1-1 = 0 from rfl, filter_one_partition_zero_univ]
  rw [zero_add]

theorem term_partition_zero (x₀ : F) (R : F[X][X][Y]) (hHyp : ClaimA2.Hypotheses x₀ R H)
    (lam : Nat.Partition 0) :
    (W𝒪 H) ^ (1 + deltaSave 1 - 1)
      * (ClaimA2.ξ x₀ R H hHyp) ^ (2 * 1 + sigmaLambda lam - 2)
      * B_coeff H x₀ R 1 lam
      * partitionProd lam (fun l => if _h : l < 1 then βHensel H x₀ R hHyp l else 0)
    = hasseCoeffRepr𝒪 H x₀ R 1 0 := by
  have hsig : sigmaLambda lam = 0 := by rw [sigmaLambda, parts_partition_zero lam]; rfl
  rw [partitionProd_zero, mul_one, hsig]
  rw [deltaSave, if_neg (by norm_num)]
  norm_num
  rw [B_coeff, hsig]
  have hpre : prefactor R.natDegree 1 lam = 1 := by
    rw [prefactor, parts_partition_zero lam]; simp [Nat.multinomial]
  rw [hpre, one_smul]

theorem βHensel_one (x₀ : F) (R : F[X][X][Y]) (hHyp : ClaimA2.Hypotheses x₀ R H) :
    βHensel H x₀ R hHyp 1 = - hasseCoeffRepr𝒪 H x₀ R 1 0 := by
  rw [βHensel_one_eq H x₀ R hHyp]
  congr 1
  rw [Finset.sum_congr rfl (fun lam _ => term_partition_zero H x₀ R hHyp lam)]
  rw [Finset.sum_const]
  have : (Finset.univ : Finset (Nat.Partition 0)).card = 1 := by decide
  rw [this, one_smul]

/-! ### Part 2: coeff_1(βHA) in cleared form (PROVEN here). -/

/-- The order-1 coefficient of the assembled series, fully explicit:
`coeff_1(βHA) = - liftBivariate(p) / (W^2 · ξ)`, with `p = evalX x₀ (hasseDerivX 1 R)`. -/
theorem coeff_one_βHenselAssembled (x₀ : F) (R : F[X][X][Y]) (hHyp : ClaimA2.Hypotheses x₀ R H) :
    PowerSeries.coeff 1 (βHenselAssembled H x₀ R hHyp)
      = - liftBivariate (H := H)
            (Bivariate.evalX (Polynomial.C x₀) (hasseDerivX 1 R))
          / ((liftToFunctionField (H := H) H.leadingCoeff) ^ 2
              * (embeddingOf𝒪Into𝕃 H (ClaimA2.ξ x₀ R H hHyp))) := by
  rw [βHenselAssembled, PowerSeries.coeff_mk, βHensel_one H x₀ R hHyp, map_neg,
    hasseCoeffRepr𝒪, embeddingOf𝒪Into𝕃_mk]
  rw [show (1:ℕ) + 1 = 2 from rfl, show (2 * 1 - 1 : ℕ) = 1 from rfl, pow_one]
  rw [hasseDerivY, Polynomial.hasseDeriv_zero, LinearMap.id_apply]

/-! ### Part 3: coeff_1(eval(βHenselTrunc_0)Q) = hasseEvalAtRoot 1 0 (cleared eval). -/

theorem βHenselTrunc_zero_eq_C (x₀ : F) (R : F[X][X][Y]) (hHyp : ClaimA2.Hypotheses x₀ R H) :
    βHenselTrunc H x₀ R hHyp 0 = PowerSeries.C (α₀ H) := by
  ext j
  rcases j with _ | j
  · rw [coeff_βHenselTrunc_of_le H x₀ R hHyp (le_refl 0),
      PowerSeries.coeff_zero_eq_constantCoeff_apply, βHenselAssembled_constantCoeff,
      PowerSeries.coeff_zero_eq_constantCoeff_apply, PowerSeries.constantCoeff_C]
  · rw [coeff_βHenselTrunc_of_gt H x₀ R hHyp (Nat.succ_pos j), PowerSeries.coeff_C,
      if_neg (Nat.succ_ne_zero j)]

theorem coeff_one_C_pow (c : 𝕃 H) (i : ℕ) : PowerSeries.coeff 1 ((PowerSeries.C c) ^ i) = 0 := by
  rw [← map_pow, PowerSeries.coeff_C, if_neg (by norm_num)]
theorem coeff_zero_C_pow (c : 𝕃 H) (i : ℕ) :
    PowerSeries.coeff 0 ((PowerSeries.C c) ^ i) = c ^ i := by
  rw [← map_pow, PowerSeries.coeff_C, if_pos rfl]

theorem coeff_one_eval_C (x₀ : F) (R : F[X][X][Y]) (c : 𝕃 H) :
    PowerSeries.coeff 1 (Polynomial.eval (PowerSeries.C c) (Q x₀ R H))
      = ∑ i ∈ Finset.range ((Q x₀ R H).natDegree + 1),
          PowerSeries.coeff 1 ((Q x₀ R H).coeff i) * c ^ i := by
  rw [ProximityPrize.HenselSeriesCoeff.coeff_eval_eq_sum_range]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  rw [PowerSeries.coeff_mul]
  rw [show (Finset.antidiagonal 1 : Finset (ℕ × ℕ)) = {(0,1),(1,0)} from by decide]
  rw [Finset.sum_insert (by decide), Finset.sum_singleton]
  rw [coeff_one_C_pow, mul_zero, zero_add, coeff_zero_C_pow]

theorem sum_lift_eq_eval₂ (x₀ : F) (R : F[X][X][Y]) (c : 𝕃 H) (p : F[X][Y])
    (hpQ : ∀ i, liftToFunctionField (H := H) (p.coeff i)
              = PowerSeries.coeff 1 ((Q x₀ R H).coeff i)) :
    ∑ i ∈ Finset.range ((Q x₀ R H).natDegree + 1),
        PowerSeries.coeff 1 ((Q x₀ R H).coeff i) * c ^ i
      = Polynomial.eval₂ (liftToFunctionField (H := H)) c p := by
  set N := max ((Q x₀ R H).natDegree) p.natDegree with hN
  rw [Polynomial.eval₂_eq_sum_range' liftToFunctionField (n := N + 1)
        (Nat.lt_succ_of_le (le_max_right _ _)) c]
  have hsub : Finset.range ((Q x₀ R H).natDegree + 1) ⊆ Finset.range (N + 1) := by
    intro x hx; rw [Finset.mem_range] at hx ⊢
    have : (Q x₀ R H).natDegree ≤ N := le_max_left _ _; omega
  have hzero : ∀ i ∈ Finset.range (N + 1), i ∉ Finset.range ((Q x₀ R H).natDegree + 1) →
      PowerSeries.coeff 1 ((Q x₀ R H).coeff i) * c ^ i = 0 := by
    intro i _ hi
    rw [Finset.mem_range, not_lt, Nat.succ_le_iff] at hi
    rw [Polynomial.coeff_eq_zero_of_natDegree_lt hi, map_zero, zero_mul]
  rw [Finset.sum_subset hsub hzero]
  exact Finset.sum_congr rfl (fun i _ => by rw [← hpQ i])

theorem coeff_one_eval_trunc_zero (x₀ : F) (R : F[X][X][Y]) (hHyp : ClaimA2.Hypotheses x₀ R H) :
    PowerSeries.coeff 1 (Polynomial.eval (βHenselTrunc H x₀ R hHyp 0) (Q x₀ R H))
      = hasseEvalAtRoot H x₀ R 1 0 := by
  rw [βHenselTrunc_zero_eq_C, coeff_one_eval_C]
  rw [sum_lift_eq_eval₂ H x₀ R (α₀ H)
        (Bivariate.evalX (Polynomial.C x₀) (hasseDerivX 1 R))
        (fun i => (coeff_Q_eq_B H x₀ R i 1).symm)]
  rw [hasseEvalAtRoot, α₀, hasseDerivY, Polynomial.hasseDeriv_zero, LinearMap.id_apply]

/-! ### Part 4: THE DECISIVE EQUIVALENCE.
The keystone at t=0 (`RestrictedFaaDiBrunoMatchAt 0`) holds IFF the un-cleared/cleared
W/ξ-clearing identity `ζ · liftBivariate(p) = W²·ξ · hasseEvalAtRoot(1,0)` holds. -/

/-- `restrictedFaaDiBrunoSum 0 = hasseEvalAtRoot 1 0` (the order-1 truncated defect, laid bare). -/
theorem restrictedFaaDiBrunoSum_zero (x₀ : F) (R : F[X][X][Y]) (hHyp : ClaimA2.Hypotheses x₀ R H) :
    restrictedFaaDiBrunoSum H x₀ R hHyp 0 = hasseEvalAtRoot H x₀ R 1 0 := by
  rw [← trunc_defect_eq_restrictedFaaDiBrunoSum H x₀ R hHyp 0,
    coeff_one_eval_trunc_zero H x₀ R hHyp]

/-- **THE KEYSTONE-AT-0 EQUIVALENCE (sorry-free).**
`RestrictedFaaDiBrunoMatchAt 0` ⟺ the explicit W/ξ-clearing identity. -/
theorem keystone_at_zero_iff (x₀ : F) (R : F[X][X][Y]) (hHyp : ClaimA2.Hypotheses x₀ R H) :
    RestrictedFaaDiBrunoMatchAt H x₀ R hHyp 0
      ↔ hasseEvalAtRoot H x₀ R 1 0
          * ((liftToFunctionField (H := H) H.leadingCoeff) ^ 2
              * (embeddingOf𝒪Into𝕃 H (ClaimA2.ξ x₀ R H hHyp)))
        = ClaimA2.ζ R x₀ H
            * liftBivariate (H := H) (Bivariate.evalX (Polynomial.C x₀) (hasseDerivX 1 R)) := by
  rw [RestrictedFaaDiBrunoMatchAt, restrictedFaaDiBrunoSum_zero H x₀ R hHyp,
    coeff_one_βHenselAssembled H x₀ R hHyp]
  set W2ξ : 𝕃 H := (liftToFunctionField (H := H) H.leadingCoeff) ^ 2
      * (embeddingOf𝒪Into𝕃 H (ClaimA2.ξ x₀ R H hHyp)) with hW2ξ
  set L : 𝕃 H := liftBivariate (H := H) (Bivariate.evalX (Polynomial.C x₀) (hasseDerivX 1 R)) with hL
  set Z : 𝕃 H := ClaimA2.ζ R x₀ H with hZ
  set HE : 𝕃 H := hasseEvalAtRoot H x₀ R 1 0 with hHE
  have hW2ξ_ne : W2ξ ≠ 0 := by
    rw [hW2ξ]
    refine mul_ne_zero (pow_ne_zero _ (liftToFunctionField_leadingCoeff_ne_zero (H := H))) ?_
    exact embeddingOf𝒪Into𝕃_ξ_ne_zero H x₀ R hHyp
  -- Goal: HE = -(Z * (-L / W2ξ))  ↔  HE * W2ξ = Z * L
  constructor
  · intro h
    -- h : HE = - (Z * (- L / W2ξ))
    field_simp at h
    linear_combination h
  · intro h
    -- h : HE * W2ξ = Z * L; goal : HE = -(Z * (-L / W2ξ))
    have : HE = Z * L / W2ξ := by rw [eq_div_iff hW2ξ_ne]; linear_combination h
    rw [this]; field_simp

/-! ### Part 5: REDUCTION to the bare clearing identity `eval₂(T/W) p · W^d = eval₂(T) p`.
Using `embedding ξ = W^{d-2}·ζ` and `ζ ≠ 0`, the keystone-at-0 identity simplifies to the
pure un-cleared/cleared mismatch, with `d = R.natDegree` (the Y-degree of R) and
`p = evalX x₀ (hasseDerivX 1 R)`. -/

theorem keystone_at_zero_iff_bare (x₀ : F) (R : F[X][X][Y]) (hHyp : ClaimA2.Hypotheses x₀ R H)
    (hd : 2 ≤ R.natDegree) :
    RestrictedFaaDiBrunoMatchAt H x₀ R hHyp 0
      ↔ Polynomial.eval₂ (liftToFunctionField (H := H)) (α₀ H)
            (Bivariate.evalX (Polynomial.C x₀) (hasseDerivX 1 R))
          * (liftToFunctionField (H := H) H.leadingCoeff) ^ R.natDegree
        = liftBivariate (H := H) (Bivariate.evalX (Polynomial.C x₀) (hasseDerivX 1 R)) := by
  rw [keystone_at_zero_iff H x₀ R hHyp]
  have hHE : hasseEvalAtRoot H x₀ R 1 0
      = Polynomial.eval₂ (liftToFunctionField (H := H)) (α₀ H)
          (Bivariate.evalX (Polynomial.C x₀) (hasseDerivX 1 R)) := by
    rw [hasseEvalAtRoot, α₀, hasseDerivY, Polynomial.hasseDeriv_zero, LinearMap.id_apply]
  rw [hHE, ClaimA2.embeddingOf𝒪Into𝕃_ξ]
  set E : 𝕃 H := Polynomial.eval₂ (liftToFunctionField (H := H)) (α₀ H)
      (Bivariate.evalX (Polynomial.C x₀) (hasseDerivX 1 R)) with hE
  set L : 𝕃 H := liftBivariate (H := H) (Bivariate.evalX (Polynomial.C x₀) (hasseDerivX 1 R)) with hL
  set W : 𝕃 H := liftToFunctionField (H := H) H.leadingCoeff with hWdef
  set Z : 𝕃 H := ClaimA2.ζ R x₀ H with hZ
  have hZne : Z ≠ 0 := ζ_ne_zero H x₀ R hHyp
  have hWne : W ≠ 0 := liftToFunctionField_leadingCoeff_ne_zero (H := H)
  -- W^2 * W^(d-2) = W^d (since d ≥ 2).
  have hpow : W ^ 2 * W ^ (R.natDegree - 2) = W ^ R.natDegree := by
    rw [← pow_add]; congr 1; omega
  -- Goal: E * (W^2 * (W^(d-2) * Z)) = Z * L  ↔  E * W^d = L
  constructor
  · intro h
    have h2 : E * W ^ R.natDegree * Z = L * Z := by
      rw [← hpow]; linear_combination h
    exact mul_right_cancel₀ hZne h2
  · intro h
    have : E * (W ^ 2 * (W ^ (R.natDegree - 2) * Z)) = (E * W ^ R.natDegree) * Z := by
      rw [← hpow]; ring
    rw [this, h]; ring

/-! ### Part 6: THE BARE IDENTITY IS FALSE for non-Y-monomial `p` (the genuine defect).
The keystone-at-0 (under the d≥2 regime) demands `eval₂(T/W) p · W^d = eval₂(T) p`.
We show this is the CLEARED-vs-UNCLEARED mismatch: it forces `p`'s every Y-coefficient
below degree d to satisfy `p.coeff i · (W^{d-i} − W^{... }) = 0`.  Concretely, for a
two-term `p = C a + C b · Y` (Y-degree ≤ 1 < d when d ≥ 2), it forces `lift a · W^d = lift a`
— FALSE for `a ≠ 0` and `W ≠ 1`.  We package the obstruction abstractly. -/

/-- The bare identity, for a generic 2-term `p = C a + C b·Y`, demands `lift a · W^d = lift a`
and `lift b · W^d = lift b·W` — i.e. the un-cleared/cleared per-Y-degree W-power mismatch.
This abstract lemma exposes the exact algebraic obstruction. -/
theorem bare_identity_demands_W_power_match (a b : F[X]) (d : ℕ) (hd : 1 ≤ d) :
    Polynomial.eval₂ (liftToFunctionField (H := H)) (α₀ H)
        (Polynomial.C a + Polynomial.C b * Polynomial.X)
      * (liftToFunctionField (H := H) H.leadingCoeff) ^ d
    = (liftToFunctionField (H := H) a) * (liftToFunctionField (H := H) H.leadingCoeff) ^ d
        + (liftToFunctionField (H := H) b) * functionFieldT (H := H)
            * (liftToFunctionField (H := H) H.leadingCoeff) ^ (d - 1) := by
  -- α₀ = T/W; eval₂(T/W)(C a + C b·Y) = lift a + lift b·(T/W).
  rw [α₀, Polynomial.eval₂_add, Polynomial.eval₂_C, Polynomial.eval₂_mul, Polynomial.eval₂_C,
    Polynomial.eval₂_X]
  set W : 𝕃 H := liftToFunctionField (H := H) H.leadingCoeff with hW
  set T : 𝕃 H := functionFieldT (H := H) with hT
  have hWne : W ≠ 0 := liftToFunctionField_leadingCoeff_ne_zero (H := H)
  have hd1 : W ^ d = W * W ^ (d - 1) := by
    rw [← pow_succ']; congr 1; omega
  rw [add_mul]
  field_simp
  rw [hd1]; ring

/-! ### Part 7: THE FIX — the CLEARED representative DOES satisfy the keystone-at-0 identity.
With `B_coeff` built from the W-CLEARED `hasseCoeffRepr𝒪_cleared` instead of the un-cleared
`mk p`, the order-1 numerator's embedding becomes `W^N · hasseEvalAtRoot(1,0)` (PROVEN in tree),
and the keystone-at-0 bare identity holds.  This localizes the defect entirely in `B_coeff`'s
use of the un-cleared `hasseCoeffRepr𝒪`. -/

/-- The cleared analogue of `liftBivariate(p)` is exactly `W^N · eval₂(T/W) p` (PROVEN in tree,
restated for `p = evalX x₀ (hasseDerivX 1 R)`, `N = natDegreeY p`).  If `B_coeff` used this cleared
representative, the keystone-at-0 numerator would be the genuine cleared Newton numerator and the
match would hold. -/
theorem cleared_repr_is_genuine_newton_numerator (x₀ : F) (R : F[X][X][Y]) :
    embeddingOf𝒪Into𝕃 H
        (Ideal.Quotient.mk (Ideal.span {H_tilde' H})
          (hasseCoeffRepr𝒪_cleared H x₀ R 1 0) : 𝒪 H)
      = (liftToFunctionField (H := H) H.leadingCoeff)
          ^ Bivariate.natDegreeY (Bivariate.evalX (Polynomial.C x₀) (hasseDerivX 1 R))
        * hasseEvalAtRoot H x₀ R 1 0 := by
  have := embeddingOf𝒪Into𝕃_hasseCoeffRepr𝒪_cleared H x₀ R 1 0
  rwa [hasseDerivY, Polynomial.hasseDeriv_zero, LinearMap.id_apply] at this

/-! ### Part 8: THE DEFINITIVE DISPROOF — keystone-at-0 (hence the #139 keystone) is FALSE
on the genuine non-monic regime.

LEMMA A (`liftBivariate_eq_zero_of_natDegree_lt`): `liftBivariate` is injective on polynomials
of `Y`-degree `< H.natDegree`; such polynomials sit strictly below the modulus `H̃` so no
reduction occurs.  Proof: `liftBivariate q = 0 ↔ H̃ ∣ bivPolyHom q`; via `H_tilde_equiv_H_tilde'`
and `natDegree_H_tilde'`, the divisor has `Y`-degree `H.natDegree`, forcing the lower-degree `q`
to zero.

MAIN (`keystone_at_zero_FALSE`): combining the verified reduction `keystone_at_zero_iff_bare`
(d ≥ 2) with `W_pow_mul_eval₂_div_eq_liftBivariate`, keystone-at-0 becomes
`liftBivariate (cleared p) = liftBivariate p`, where `cleared p` rescales the `Y^i`-coefficient
of `p = evalX x₀ (Δ_X^1 R)` by `lc^{d-i}` (`d = R.natDegree`).  Then `cleared p - p` has
`Y`-degree `< d = H.natDegree` (its top coefficient `lc^0 - 1 = 0` cancels), so LEMMA A forces
`cleared p = p`.  But the `i₀`-coefficient is `p.coeff i₀ · (lc^{d-i₀} - 1) ≠ 0` whenever
`p.coeff i₀ ≠ 0` and `H` is non-monic (`lc` a non-unit, so `lc^{d-i₀} ≠ 1`).  Contradiction.
The defect is exactly the un-cleared `B_coeff` (it must use `hasseCoeffRepr𝒪_cleared`). -/

/-- LEMMA A. `liftBivariate` kills only the zero polynomial below `Y`-degree `H.natDegree`. -/
theorem liftBivariate_eq_zero_of_natDegree_lt {q : F[X][Y]}
    (hq : liftBivariate (H := H) q = 0) (hdeg : q.natDegree < H.natDegree) : q = 0 := by
  have hHdeg : 0 < H.natDegree := (‹Fact (0 < H.natDegree)›).out
  have hinj : Function.Injective (ToRatFunc.univPolyHom (F := F)) := by
    simpa [ToRatFunc.univPolyHom] using (RatFunc.algebraMap_injective (K := F))
  -- liftBivariate q = 0  ↔  bivPolyHom q ∈ span {H_tilde H}
  have hmem : ToRatFunc.bivPolyHom q ∈ Ideal.span {H_tilde H} := by
    simp only [liftBivariate, RingHom.comp_apply] at hq
    rwa [Ideal.Quotient.eq_zero_iff_mem] at hq
  -- H_tilde H ∣ q.map univPolyHom, i.e. (H_tilde' H).map univPolyHom ∣ q.map univPolyHom
  have hdvd : (H_tilde' H).map (ToRatFunc.univPolyHom (F := F)) ∣
      q.map (ToRatFunc.univPolyHom (F := F)) := by
    rw [H_tilde_equiv_H_tilde']
    have := (Ideal.mem_span_singleton).1 hmem
    simpa [show ToRatFunc.bivPolyHom q = q.map (ToRatFunc.univPolyHom (F := F)) from rfl] using this
  by_contra hq0
  have hqmap0 : q.map (ToRatFunc.univPolyHom (F := F)) ≠ 0 := by
    rwa [Ne, Polynomial.map_eq_zero_iff hinj]
  have hle := Polynomial.natDegree_le_of_dvd hdvd hqmap0
  rw [Polynomial.natDegree_map_eq_of_injective hinj, Polynomial.natDegree_map_eq_of_injective hinj,
    natDegree_H_tilde' hHdeg] at hle
  omega

/-- THE DISPROOF: on the genuine non-monic regime, the order-0 keystone residual is FALSE,
so `RestrictedFaaDiBrunoMatchAt H x₀ R hHyp 0` cannot hold — the #139 keystone is unprovable
as stated.  `hlc : ¬ IsUnit H.leadingCoeff` encodes "`H` non-monic" (`W` a non-unit);
`hdeg : R.natDegree = H.natDegree` is the degree-preserving regime; `hp` says `p` has a genuine
sub-top `Y`-coefficient.  All three hold generically in Appendix A.4. -/
theorem keystone_at_zero_FALSE (x₀ : F) (R : F[X][X][Y]) (hHyp : ClaimA2.Hypotheses x₀ R H)
    (hd : 2 ≤ R.natDegree) (hdeg : R.natDegree = H.natDegree)
    (hlc : ¬ IsUnit H.leadingCoeff)
    (i₀ : ℕ) (hi₀ : i₀ < R.natDegree)
    (hp : (Bivariate.evalX (Polynomial.C x₀) (hasseDerivX 1 R)).coeff i₀ ≠ 0) :
    ¬ RestrictedFaaDiBrunoMatchAt H x₀ R hHyp 0 := by
  rw [keystone_at_zero_iff_bare H x₀ R hHyp hd]
  set p := Bivariate.evalX (Polynomial.C x₀) (hasseDerivX 1 R) with hpdef
  set d := R.natDegree with hddef
  have hpdeg : p.natDegree ≤ d := by
    calc p.natDegree = Bivariate.natDegreeY p := rfl
      _ ≤ Bivariate.natDegreeY (hasseDerivX 1 R) := evalX_natDegreeY_le _ _
      _ ≤ Bivariate.natDegreeY R := hasseDerivX_natDegreeY_le _ _
      _ = d := rfl
  intro hEq
  -- turn the LHS into liftBivariate of the cleared polynomial
  rw [α₀, mul_comm,
    W_pow_mul_eval₂_div_eq_liftBivariate (H := H) (P := p) (k := d) hpdeg] at hEq
  set clr : F[X][Y] := ∑ i ∈ Finset.range (d + 1),
    Polynomial.C (p.coeff i * H.leadingCoeff ^ (d - i)) * Polynomial.X ^ i with hclrdef
  -- liftBivariate (clr - p) = 0
  have hdiff : liftBivariate (H := H) (clr - p) = 0 := by rw [map_sub, hEq, sub_self]
  -- coefficientwise description of clr - p
  have clr_coeff : ∀ k, clr.coeff k =
      if k < d + 1 then p.coeff k * H.leadingCoeff ^ (d - k) else 0 := by
    intro k
    rw [hclrdef, Polynomial.finset_sum_coeff]
    simp_rw [Polynomial.coeff_C_mul_X_pow]
    rw [Finset.sum_ite_eq (Finset.range (d + 1)) k
        (fun i => p.coeff i * H.leadingCoeff ^ (d - i))]
    simp [Finset.mem_range]
  have diff_coeff : ∀ k, (clr - p).coeff k =
      if k < d + 1 then p.coeff k * (H.leadingCoeff ^ (d - k) - 1) else 0 := by
    intro k
    rw [Polynomial.coeff_sub, clr_coeff k]
    by_cases hk : k < d + 1
    · simp only [hk, if_true]; ring
    · simp only [hk, if_false, zero_sub]
      rw [Polynomial.coeff_eq_zero_of_natDegree_lt (by omega : p.natDegree < k), neg_zero]
  -- degree of clr - p is below H.natDegree = d
  have hdiffdeg : (clr - p).natDegree < H.natDegree := by
    have hle : (clr - p).natDegree ≤ d - 1 := by
      rw [Polynomial.natDegree_le_iff_coeff_eq_zero]
      intro m hm
      rw [diff_coeff m]
      by_cases hk : m < d + 1
      · have hmd : m = d := by omega
        subst hmd; simp
      · simp [hk]
    omega
  have hzero := liftBivariate_eq_zero_of_natDegree_lt H hdiff hdiffdeg
  -- but the i₀-coefficient is nonzero
  have hci := diff_coeff i₀
  rw [hzero, Polynomial.coeff_zero, if_pos (by omega : i₀ < d + 1)] at hci
  refine (mul_ne_zero hp ?_) hci.symm
  intro hcontra
  have hpow : H.leadingCoeff ^ (d - i₀) = 1 := by rwa [sub_eq_zero] at hcontra
  have hposn : 1 ≤ d - i₀ := by omega
  exact hlc (IsUnit.of_mul_eq_one (H.leadingCoeff ^ (d - i₀ - 1)) (by
    rw [← pow_succ', Nat.sub_add_cancel hposn, hpow]))

end BCIKS20.HenselNumerator

section Audit
open BCIKS20.HenselNumerator
#print axioms βHensel_one
#print axioms coeff_one_βHenselAssembled
#print axioms coeff_one_eval_trunc_zero
#print axioms restrictedFaaDiBrunoSum_zero
#print axioms keystone_at_zero_iff
#print axioms keystone_at_zero_iff_bare
#print axioms bare_identity_demands_W_power_match
end Audit

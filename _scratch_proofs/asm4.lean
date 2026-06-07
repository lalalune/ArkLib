import ArkLib.Data.CodingTheory.ProximityGap.BCIKS20.P2Assembly

open scoped BigOperators
open Finset Polynomial Polynomial.Bivariate ArkLib.PowerSeriesComposition
open BCIKS20AppendixA ProximityPrize.BCIKS20.GammaGenuine

namespace BCIKS20.HenselNumerator

variable {F : Type} [Field F]
variable (H : F[X][Y]) [Fact (Irreducible H)] [Fact (0 < H.natDegree)]

-- ===== taylorCollapse =====
/-! ### Injectivity of the coefficient ring hom `coeffHom`, hence `Q.natDegree = R.natDegree`. -/

private theorem liftToFunctionField_injective_tc :
    Function.Injective (liftToFunctionField (H := H)) := by
  rw [injective_iff_map_eq_zero]
  intro p hp
  by_contra hne
  exact liftToFunctionField_ne_zero hne hp

private theorem coeffHom_injective_tc (x₀ : F) : Function.Injective (coeffHom x₀ H) := by
  have h1 : Function.Injective (Polynomial.coeToPowerSeries.ringHom (R := 𝕃 H)) := by
    intro a b hab
    apply Polynomial.coe_injective (𝕃 H)
    simpa [Polynomial.coeToPowerSeries.ringHom] using hab
  have h2 : Function.Injective ⇑(Polynomial.mapRingHom (liftToFunctionField (H := H))) := by
    rw [Polynomial.coe_mapRingHom]
    exact Polynomial.map_injective _ (liftToFunctionField_injective_tc H)
  have h3 : Function.Injective ⇑(Polynomial.taylorAlgHom (R := F[X]) (Polynomial.C x₀)).toRingHom := by
    intro a b hab
    apply Polynomial.taylor_injective (Polynomial.C x₀)
    have h : ∀ q : F[X][Y], (Polynomial.taylorAlgHom (R := F[X]) (Polynomial.C x₀)).toRingHom q
        = Polynomial.taylor (Polynomial.C x₀) q := fun q => by simp [Polynomial.taylorAlgHom_apply]
    rw [h, h] at hab; exact hab
  rw [coeffHom, RingHom.coe_comp, RingHom.coe_comp]
  exact h1.comp (h2.comp h3)

private theorem Q_natDegree_eq_tc (x₀ : F) (R : F[X][X][Y]) :
    (Q x₀ R H).natDegree = R.natDegree := by
  rw [Q, Polynomial.natDegree_map_eq_of_injective (coeffHom_injective_tc H x₀)]

/-! ### The two vanishing facts for the summand `f i`. -/

/-- The summand of the target Taylor sum. -/
private noncomputable def tcTerm (x₀ : F) (R : F[X][X][Y]) (i1 s i : ℕ) : 𝕃 H :=
  (i.choose s) • (liftToFunctionField (H:=H)
      ((Bivariate.evalX (Polynomial.C x₀) (hasseDerivX i1 R)).coeff i) * (α₀ H) ^ (i - s))

/-- Vanishing beyond `R.natDegree`: the `P₁`-coefficient is zero there. -/
private theorem tcTerm_eq_zero_of_natDegree_lt (x₀ : F) (R : F[X][X][Y]) (i1 s i : ℕ)
    (hi : R.natDegree < i) : tcTerm H x₀ R i1 s i = 0 := by
  rw [tcTerm]
  have hP1 : (Bivariate.evalX (Polynomial.C x₀) (hasseDerivX i1 R)).natDegree ≤ R.natDegree := by
    have h1 : Bivariate.natDegreeY (Bivariate.evalX (Polynomial.C x₀) (hasseDerivX i1 R))
        ≤ Bivariate.natDegreeY R :=
      (evalX_natDegreeY_le (Polynomial.C x₀) _).trans (hasseDerivX_natDegreeY_le i1 R)
    simpa [Bivariate.natDegreeY] using h1
  have hcoeff : (Bivariate.evalX (Polynomial.C x₀) (hasseDerivX i1 R)).coeff i = 0 :=
    Polynomial.coeff_eq_zero_of_natDegree_lt (by omega)
  simp [hcoeff]

/-- Vanishing beyond `M + s` (`M` = natDegree of the `Δ_Y^s`-version): via the Hasse
commutation `evalX_hasseDeriv_Y_coeff`, the weighted coefficient is a lift of a zero coefficient. -/
private theorem tcTerm_eq_zero_of_M_lt (x₀ : F) (R : F[X][X][Y]) (i1 s i : ℕ)
    (hi : (Bivariate.evalX (Polynomial.C x₀) (hasseDerivX i1 (hasseDerivY s R))).natDegree + s < i) :
    tcTerm H x₀ R i1 s i = 0 := by
  rw [tcTerm]
  have hs : s ≤ i := by omega
  have hcomm := evalX_hasseDeriv_Y_coeff x₀ R i1 s (i - s)
  rw [Nat.sub_add_cancel hs] at hcomm
  have hMcoeff : (Bivariate.evalX (Polynomial.C x₀)
      (hasseDerivX i1 (hasseDerivY s R))).coeff (i - s) = 0 :=
    Polynomial.coeff_eq_zero_of_natDegree_lt (by omega)
  rw [hMcoeff] at hcomm
  rw [← smul_mul_assoc, ← map_nsmul (liftToFunctionField (H := H)), ← hcomm, map_zero, zero_mul]

/-! ### The base identity (brick1) for the `M+1+s` range. -/

private theorem taylorCollapse_baseRange (x₀ : F) (R : F[X][X][Y]) (i1 s : ℕ) :
    hasseEvalAtRoot H x₀ R i1 s
      = ∑ i ∈ Finset.range
          ((Bivariate.evalX (Polynomial.C x₀)
              (hasseDerivX i1 (hasseDerivY s R))).natDegree + 1 + s),
          tcTerm H x₀ R i1 s i := by
  simp only [tcTerm]
  rw [hasseEvalAtRoot_eq_taylorSum, α₀]
  symm
  set M := (Bivariate.evalX (Polynomial.C x₀) (hasseDerivX i1 (hasseDerivY s R))).natDegree with hM
  rw [Finset.range_eq_Ico,
      ← Finset.sum_Ico_consecutive _ (Nat.zero_le s) (by omega : s ≤ M + 1 + s),
      Finset.sum_eq_zero (s := Finset.Ico 0 s) (fun i hi => by
        rw [Finset.mem_Ico] at hi
        rw [Nat.choose_eq_zero_of_lt hi.2, zero_smul]),
      zero_add, Finset.sum_Ico_eq_sum_range]
  apply Finset.sum_congr (by rw [Nat.add_sub_cancel])
  intro j _
  rw [Nat.add_sub_cancel_left, Nat.add_comm s j]

/-! ### MAIN: the `Q`-range version. -/

theorem taylorCollapse (x₀ : F) (R : F[X][X][Y]) (i1 s : ℕ) :
  ∑ i ∈ Finset.range ((Q x₀ R H).natDegree + 1),
    (i.choose s) • (liftToFunctionField (H:=H)
        ((Bivariate.evalX (Polynomial.C x₀) (hasseDerivX i1 R)).coeff i) * (α₀ H) ^ (i - s))
  = hasseEvalAtRoot H x₀ R i1 s := by
  -- Fold the summand into `tcTerm` and replace `Q.natDegree` by `R.natDegree`.
  show ∑ i ∈ Finset.range ((Q x₀ R H).natDegree + 1), tcTerm H x₀ R i1 s i = _
  rw [Q_natDegree_eq_tc]
  set M := (Bivariate.evalX (Polynomial.C x₀) (hasseDerivX i1 (hasseDerivY s R))).natDegree with hM
  -- Common superset `range K`, K = max (R.natDegree+1) (M+1+s).
  set K := max (R.natDegree + 1) (M + 1 + s) with hK
  -- Extend the R-range sum to range K (extra terms vanish by `tcTerm_eq_zero_of_natDegree_lt`).
  have hsubR : Finset.range (R.natDegree + 1) ⊆ Finset.range K :=
    Finset.range_mono (le_max_left (R.natDegree + 1) (M + 1 + s))
  have heqR : ∑ i ∈ Finset.range (R.natDegree + 1), tcTerm H x₀ R i1 s i
      = ∑ i ∈ Finset.range K, tcTerm H x₀ R i1 s i := by
    refine Finset.sum_subset hsubR (fun i _ hiR => ?_)
    rw [Finset.mem_range, not_lt] at hiR
    exact tcTerm_eq_zero_of_natDegree_lt H x₀ R i1 s i (by omega)
  -- Extend the M-range sum to range K (extra terms vanish by `tcTerm_eq_zero_of_M_lt`).
  have hsubM : Finset.range (M + 1 + s) ⊆ Finset.range K :=
    Finset.range_mono (le_max_right (R.natDegree + 1) (M + 1 + s))
  have heqM : ∑ i ∈ Finset.range (M + 1 + s), tcTerm H x₀ R i1 s i
      = ∑ i ∈ Finset.range K, tcTerm H x₀ R i1 s i := by
    refine Finset.sum_subset hsubM (fun i _ hiM => ?_)
    rw [Finset.mem_range, not_lt] at hiM
    exact tcTerm_eq_zero_of_M_lt H x₀ R i1 s i (by omega)
  rw [heqR, ← heqM, ← taylorCollapse_baseRange]

-- ===== partitionPowerClear =====
omit [Fact (Irreducible H)] [Fact (0 < H.natDegree)] in
/-- Auxiliary: a product of powers of a fixed base `W : 𝕃 H` over a multiset, indexed by
`fun l => W ^ (g l)`, collapses to a single power whose exponent is the sum of the `g l`. -/
private lemma prod_map_pow_collapse (m : Multiset ℕ) (W : 𝕃 H) (g : ℕ → ℕ) :
    (m.map (fun l => W ^ (g l))).prod = W ^ (m.map g).sum := by
  induction m using Multiset.induction with
  | empty => simp
  | cons a s ih =>
      simp [Multiset.map_cons, Multiset.prod_cons, Multiset.sum_cons, pow_add, ih]

/-- Auxiliary: `∑_{l ∈ λ} (l + 1) = c + (number of parts)`. -/
private lemma sum_map_succ {c : ℕ} (lam : Nat.Partition c) :
    (lam.parts.map (fun l => l + 1)).sum = c + lam.parts.card := by
  rw [Multiset.sum_map_add]
  simp [lam.parts_sum]

/-- The number of parts is at most the partitioned number, since every part is `≥ 1`. -/
private lemma card_le {c : ℕ} (lam : Nat.Partition c) : lam.parts.card ≤ c := by
  have hc : lam.parts.card ≤ lam.parts.sum := by
    calc lam.parts.card = (lam.parts.map (fun _ => 1)).sum := by
              simp [Multiset.map_const', Multiset.sum_replicate]
      _ ≤ (lam.parts.map (fun l => l)).sum := by
              apply Multiset.sum_map_le_sum_map
              intro l hl
              exact lam.parts_pos hl
      _ = lam.parts.sum := by rw [Multiset.map_id']
  rwa [lam.parts_sum] at hc

/-- Auxiliary: `∑_{l ∈ λ} (2 l - 1) = 2 c - (number of parts)` (truncated ℕ subtraction).
The per-part subtraction `2 l - 1` is exact because every part is `≥ 1`. -/
private lemma sum_map_two_mul_sub_one {c : ℕ} (lam : Nat.Partition c) :
    (lam.parts.map (fun l => 2 * l - 1)).sum = 2 * c - lam.parts.card := by
  have hmap : (lam.parts.map (fun l => 2 * l - 1))
      = lam.parts.map (fun l => 2 * (l - 1) + 1) := by
    apply Multiset.map_congr rfl
    intro l hl
    have hl1 : 1 ≤ l := lam.parts_pos hl
    omega
  rw [hmap, Multiset.sum_map_add]
  simp only [Multiset.sum_map_mul_left, Multiset.map_const', Multiset.sum_replicate, smul_eq_mul,
    mul_one]
  have hsub : (lam.parts.map (fun l => l - 1)).sum = c - lam.parts.card := by
    have heq : (lam.parts.map (fun l => (l - 1) + 1)).sum = (lam.parts.map (fun l => l)).sum := by
      apply congrArg
      apply Multiset.map_congr rfl
      intro l hl
      have hl1 : 1 ≤ l := lam.parts_pos hl
      omega
    rw [Multiset.sum_map_add] at heq
    simp only [Multiset.map_const', Multiset.sum_replicate, smul_eq_mul, mul_one,
      Multiset.map_id'] at heq
    rw [lam.parts_sum] at heq
    omega
  rw [hsub]
  have hle := card_le lam
  omega

omit [Fact (Irreducible H)] [Fact (0 < H.natDegree)] in
/-- **Sub-lemma C** (field-clearing partition-power identity).

The per-part denominators `W^(l+1) · ξ^(2l-1)` arising from `βHenselAssembled`'s coefficient
formula, multiplied over all parts `l` of a partition `λ ⊢ c`, combine into the single product
`W^(c + #λ) · ξ^(2c - #λ)`.

The exponents are exact:
* `∑_{l ∈ λ} (l + 1) = c + #λ` (since `∑ l = c`);
* `∑_{l ∈ λ} (2 l - 1) = 2 c - #λ`, where each per-part `2 l - 1` is computed in ℕ but is exact
  because every part of a `Nat.Partition` is `≥ 1`, and `#λ ≤ c ≤ 2 c` keeps the global
  truncated subtraction faithful. -/
theorem partitionPowerClear {c : ℕ} (lam : Nat.Partition c) (W xi : 𝕃 H) :
    (lam.parts.map (fun l => W ^ (l + 1) * xi ^ (2 * l - 1))).prod
      = W ^ (c + lam.parts.card) * xi ^ (2 * c - lam.parts.card) := by
  rw [Multiset.prod_map_mul, prod_map_pow_collapse, prod_map_pow_collapse,
    sum_map_succ, sum_map_two_mul_sub_one]

-- ===== antidiag_reindex =====
theorem antidiag_reindex {M : Type*} [AddCommMonoid M] (t : ℕ) (f : ℕ × ℕ → M) :
  ∑ ab ∈ Finset.antidiagonal (t + 1), f ab
  = ∑ i1 ∈ Finset.range (t + 2), f (i1, t + 1 - i1) := by
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]

-- ===== hasseEvalAtRoot_eq_embedding_cleared_div =====
/-- **SUB-LEMMA E — the clean bridge from `hasseEvalAtRoot` to the embedded cleared
representative.**  Inverting the `W`-clearing embedding identity
`embeddingOf𝒪Into𝕃_hasseCoeffRepr𝒪_cleared`: dividing by `W^{natDegreeY p}` (nonzero, since
`W = liftToFunctionField H.leadingCoeff ≠ 0`) exhibits the `Y↦T/W` evaluation
`hasseEvalAtRoot` as the embedded cleared `𝒪`-representative scaled down by the cleared
`W`-power. -/
lemma hasseEvalAtRoot_eq_embedding_cleared_div (x₀ : F) (R : F[X][X][Y]) (i1 m : ℕ) :
    hasseEvalAtRoot H x₀ R i1 m
      = embeddingOf𝒪Into𝕃 H
          (Ideal.Quotient.mk (Ideal.span {H_tilde' H})
            (hasseCoeffRepr𝒪_cleared H x₀ R i1 m) : 𝒪 H)
        / liftToFunctionField (H := H) H.leadingCoeff
            ^ Bivariate.natDegreeY
                (Bivariate.evalX (Polynomial.C x₀) (hasseDerivX i1 (hasseDerivY m R))) := by
  rw [embeddingOf𝒪Into𝕃_hasseCoeffRepr𝒪_cleared]
  rw [mul_comm,
      mul_div_assoc,
      div_self (pow_ne_zero _ (liftToFunctionField_leadingCoeff_ne_zero (H := H))),
      mul_one]

-- ===== depSwap =====
omit [Fact (Irreducible H)] [Fact (0 < H.natDegree)] in
theorem depSwap {c N : ℕ} (A : ℕ → 𝕃 H) (g : ℕ → Nat.Partition c → 𝕃 H)
    (Q : Nat.Partition c → Prop) [DecidablePred Q] :
    ∑ i ∈ Finset.range N, A i * ∑ lam ∈ (Finset.univ : Finset (Nat.Partition c)).filter
        (fun lam => lam.parts.card ≤ i ∧ Q lam), g i lam
      = ∑ lam ∈ (Finset.univ : Finset (Nat.Partition c)).filter Q,
          ∑ i ∈ (Finset.range N).filter (fun i => lam.parts.card ≤ i), A i * g i lam := by
  -- distribute A i inside the inner sum
  simp only [Finset.mul_sum]
  -- now swap the two sums via sum_comm'
  apply Finset.sum_comm'
  intro i lam
  simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_univ, true_and]
  tauto

-- ============ BRIDGE 1 (cleared / TRUE form) — verified ============
theorem bridge1_cleared (x₀ : F) (R : F[X][X][Y]) (i1 m : ℕ) :
    embeddingOf𝒪Into𝕃 H
        (Ideal.Quotient.mk (Ideal.span {H_tilde' H})
          (hasseCoeffRepr𝒪_cleared H x₀ R i1 m) : 𝒪 H)
      = liftToFunctionField (H:=H) H.leadingCoeff
          ^ (Bivariate.natDegreeY
              (Bivariate.evalX (Polynomial.C x₀) (hasseDerivX i1 (hasseDerivY m R))))
        * hasseEvalAtRoot H x₀ R i1 m :=
  embeddingOf𝒪Into𝕃_hasseCoeffRepr𝒪_cleared H x₀ R i1 m

theorem emb_hasseCoeffRepr𝒪 (x₀ : F) (R : F[X][X][Y]) (i1 m : ℕ) :
    embeddingOf𝒪Into𝕃 H (hasseCoeffRepr𝒪 H x₀ R i1 m)
      = Polynomial.eval₂ (liftToFunctionField (H := H)) (functionFieldT (H := H))
          (Bivariate.evalX (Polynomial.C x₀) (hasseDerivX i1 (hasseDerivY m R))) := by
  rw [hasseCoeffRepr𝒪, embeddingOf𝒪Into𝕃_mk, liftBivariate_eq_eval₂_functionFieldT]

-- LHS term collapse: the inner i-sum collapses to countPerms•prod * hasseEvalAtRoot.
theorem lhs_term_collapse (x₀ : F) (R : F[X][X][Y]) (hHyp : ClaimA2.Hypotheses x₀ R H)
    (i1 c : ℕ) (lam : Nat.Partition c) :
    ∑ i ∈ (Finset.range ((Q x₀ R H).natDegree + 1)).filter
        (fun i => lam.parts.card ≤ i),
      liftToFunctionField (H := H)
          ((Bivariate.evalX (Polynomial.C x₀) (hasseDerivX i1 R)).coeff i)
        * ((i.choose lam.parts.card * lam.parts.countPerms) •
            (α₀ H ^ (i - lam.parts.card)
              * (lam.parts.map (fun j =>
                  PowerSeries.coeff j (βHenselAssembled H x₀ R hHyp))).prod))
      = (lam.parts.countPerms • (lam.parts.map (fun j =>
            PowerSeries.coeff j (βHenselAssembled H x₀ R hHyp))).prod)
          * hasseEvalAtRoot H x₀ R i1 (lam.parts.card) := by
  -- Drop the `card ≤ i` filter: extra terms have i.choose card = 0.
  rw [← taylorCollapse H x₀ R i1 (lam.parts.card)]
  -- RHS: (countPerms•prod) * ∑_i (i.choose card)•(lift(coeff i)·α₀^{i-card})
  rw [Finset.mul_sum]
  -- LHS: filtered sum = full-range sum (the dropped terms vanish).
  rw [Finset.sum_filter]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  by_cases hci : lam.parts.card ≤ i
  · rw [if_pos hci, mul_smul_comm, smul_mul_assoc]
    simp only [nsmul_eq_mul, Nat.cast_mul]
    ring
  · rw [if_neg hci]
    have h0 : i.choose lam.parts.card = 0 := Nat.choose_eq_zero_of_lt (by omega)
    rw [h0]
    simp

-- coeff j of βHenselAssembled (the def)
theorem coeff_βHenselAssembled (x₀ : F) (R : F[X][X][Y]) (hHyp : ClaimA2.Hypotheses x₀ R H)
    (j : ℕ) :
    PowerSeries.coeff j (βHenselAssembled H x₀ R hHyp)
      = embeddingOf𝒪Into𝕃 H (βHensel H x₀ R hHyp j)
          / ((liftToFunctionField (H := H) H.leadingCoeff) ^ (j + 1)
              * (embeddingOf𝒪Into𝕃 H (ClaimA2.ξ x₀ R H hHyp)) ^ (2 * j - 1)) := by
  rw [βHenselAssembled, PowerSeries.coeff_mk]

-- STEP5+6: the LHS partition product over coeff_j βHenselAssembled clears to
-- emb(partitionProd lam βHensel) over the single power W^{c+card}·emb(ξ)^{2c-card}.
theorem lhs_prod_clear (x₀ : F) (R : F[X][X][Y]) (hHyp : ClaimA2.Hypotheses x₀ R H)
    {c : ℕ} (lam : Nat.Partition c) :
    (lam.parts.map (fun j => PowerSeries.coeff j (βHenselAssembled H x₀ R hHyp))).prod
      = embeddingOf𝒪Into𝕃 H (partitionProd lam (βHensel H x₀ R hHyp))
          / ((liftToFunctionField (H := H) H.leadingCoeff) ^ (c + lam.parts.card)
              * (embeddingOf𝒪Into𝕃 H (ClaimA2.ξ x₀ R H hHyp)) ^ (2 * c - lam.parts.card)) := by
  -- rewrite each coeff into the div form
  have hmap : (lam.parts.map (fun j => PowerSeries.coeff j (βHenselAssembled H x₀ R hHyp)))
      = lam.parts.map (fun j =>
          embeddingOf𝒪Into𝕃 H (βHensel H x₀ R hHyp j)
            / ((liftToFunctionField (H := H) H.leadingCoeff) ^ (j + 1)
                * (embeddingOf𝒪Into𝕃 H (ClaimA2.ξ x₀ R H hHyp)) ^ (2 * j - 1))) := by
    apply Multiset.map_congr rfl
    intro j _
    exact coeff_βHenselAssembled H x₀ R hHyp j
  rw [hmap, Multiset.prod_map_div]
  congr 1
  · -- numerator = emb(partitionProd lam βHensel)
    rw [partitionProd, map_multiset_prod, Multiset.map_map]
    rfl
  · -- denominator = W^{c+card}·emb(ξ)^{2c-card} via partitionPowerClear
    exact partitionPowerClear H lam (liftToFunctionField (H := H) H.leadingCoeff)
      (embeddingOf𝒪Into𝕃 H (ClaimA2.ξ x₀ R H hHyp))

-- VERIFIED arithmetic skeleton (ABSTRACT, pure exponent arithmetic): GIVEN the bridge
-- (eval₂ T p = W^N · hasseEvalAtRoot) — folded into K — and the degree identity
-- N + s + δ = d (d = R.natDegree, s = card), the per-term keystone W/ξ/ζ bookkeeping balances.
-- K stands for cP · PP · hasseEvalAtRoot;  ξ̃ = W^(d-2)·ζ is substituted.  This confirms the only
-- genuine gap in the whole assembly is the per-monomial-false un-cleared bridge.
theorem diag_arith_abstract {L : Type*} [Field L]
    (W ζ K : L) (hWne : W ≠ 0) (hζne : ζ ≠ 0)
    (d s i1 δ N t : ℕ)
    (hd : 2 ≤ d) (hi1 : i1 ≤ t + 1)
    (hs_le : s ≤ 2 * (t + 1 - i1)) (h2i1 : 2 ≤ 2 * i1 + s)
    (hdeg : N + s + δ = d) (hi1δ : 1 ≤ i1 + δ) :
    K / (W ^ ((t + 1 - i1) + s) * (W ^ (d - 2) * ζ) ^ (2 * (t + 1 - i1) - s))
    = ζ * (W ^ (i1 + δ - 1) * (W ^ (d - 2) * ζ) ^ (2 * i1 + s - 2)
            * (W ^ N * K)
            * (W ^ (t + 1 + 1) * (W ^ (d - 2) * ζ) ^ (2 * (t + 1) - 1))⁻¹) := by
  -- Convert all powers to zpow over ℤ and balance exponents.
  have key : ∀ a b : ℕ, (W ^ (d - 2) * ζ) ^ a = W ^ ((d - 2) * a) * ζ ^ a := by
    intro a b
    rw [mul_pow, ← pow_mul]
  rw [key (2 * (t + 1 - i1) - s) 0, key (2 * i1 + s - 2) 0, key (2 * (t + 1) - 1) 0]
  field_simp
  ring_nf
  -- Combine into K · W^(Wexp) · ζ^(ζexp) on each side; match exponents.
  -- W-exponent identity:  LHS = 2 + t + (d-2)(2t+1) ;  RHS = (d-2)·2t + (t+1-i1)+s+(i1+δ-1)+N.
  have hbracket : (1 + t - i1) * 2 - s + (s + i1 * 2 - 2) = t * 2 := by omega
  have hWexp : 2 + t + (d - 2) * (2 + t * 2 - 1)
      = (d - 2) * ((1 + t - i1) * 2 - s) + (d - 2) * (s + i1 * 2 - 2) + (1 + t - i1) + s
        + (i1 + δ - 1) + N := by
    rw [← Nat.mul_add, hbracket]
    -- LHS (d-2)*(2t+1) = (d-2)*2t + (d-2);  remaining linear = t + d ;  total matches.
    have hexp : (d - 2) * (2 + t * 2 - 1) = (d - 2) * (t * 2) + (d - 2) := by
      rw [← Nat.mul_succ]; congr 1; omega
    rw [hexp]; omega
  have hζexp : 2 + t * 2 - 1
      = 1 + ((1 + t - i1) * 2 - s) + (s + i1 * 2 - 2) := by
    omega
  calc K * W ^ 2 * W ^ t * W ^ ((d - 2) * (2 + t * 2 - 1)) * ζ ^ (2 + t * 2 - 1)
      = K * (W ^ (2 + t + (d - 2) * (2 + t * 2 - 1))) * ζ ^ (2 + t * 2 - 1) := by
        rw [pow_add, pow_add]; ring
    _ = K * (W ^ ((d - 2) * ((1 + t - i1) * 2 - s) + (d - 2) * (s + i1 * 2 - 2) + (1 + t - i1) + s
              + (i1 + δ - 1) + N))
          * ζ ^ (1 + ((1 + t - i1) * 2 - s) + (s + i1 * 2 - 2)) := by
        rw [hWexp, hζexp]
    _ = K * W ^ ((d - 2) * ((1 + t - i1) * 2 - s)) * W ^ ((d - 2) * (s + i1 * 2 - 2)) *
              W ^ (1 + t - i1) * W ^ s * W ^ (i1 + δ - 1) * W ^ N *
            ζ * ζ ^ ((1 + t - i1) * 2 - s) * ζ ^ (s + i1 * 2 - 2) := by
        simp only [pow_add, pow_one]
        ring

-- ============ ASSEMBLY DRIVE ============
theorem RestrictedFaaDiBrunoPartitionMatchAt_proof (x₀ : F) (R : F[X][X][Y])
    (hHyp : ClaimA2.Hypotheses x₀ R H) (t : ℕ) :
    RestrictedFaaDiBrunoPartitionMatchAt H x₀ R hHyp t := by
  unfold RestrictedFaaDiBrunoPartitionMatchAt
  unfold restrictedFaaDiBrunoPartitionForm restrictedMatchRecursionPartitionForm
  -- STEP0: replace coeff 0 βHenselAssembled by α₀
  simp only [PowerSeries.coeff_zero_eq_constantCoeff_apply, βHenselAssembled_constantCoeff]
  -- STEP1: BRICK 2a — swap the i and ab sums (Finset.sum_comm)
  rw [Finset.sum_comm]
  -- STEP2: antidiag_reindex
  rw [antidiag_reindex]
  -- Push ζ and /den inside the i1-sum on the RHS
  rw [div_eq_mul_inv, Finset.sum_mul, Finset.mul_sum]
  -- Per-i1 congruence
  refine Finset.sum_congr rfl (fun i1 _ => ?_)
  -- STEP3: depSwap on LHS (i ↔ lam swap, factoring out the i-independent part)
  rw [depSwap H
    (A := fun x => liftToFunctionField (H := H)
      ((Bivariate.evalX (Polynomial.C x₀) (hasseDerivX i1 R)).coeff x))
    (g := fun x lam => (x.choose lam.parts.card * lam.parts.countPerms) •
        (α₀ H ^ (x - lam.parts.card)
          * (lam.parts.map (fun j =>
              PowerSeries.coeff j (βHenselAssembled H x₀ R hHyp))).prod))
    (Q := fun lam => (t + 1) ∉ lam.parts)]
  -- Push ζ * (∑ ... * den⁻¹) into the lam-sum on the RHS
  rw [Finset.sum_mul, Finset.mul_sum]
  -- Per-lam congruence
  refine Finset.sum_congr rfl (fun lam hlam => ?_)
  -- STEP4: collapse the LHS inner i-sum to countPerms•prod * hasseEvalAtRoot
  rw [lhs_term_collapse H x₀ R hHyp i1 (t + 1 - i1) lam]
  -- STEP5+6: clear the LHS partition product
  rw [lhs_prod_clear H x₀ R hHyp lam]
  -- STEP7: expand RHS embeddings
  rw [embed_W𝒪]
  -- emb(B_coeff) = countPerms • emb(mk p)  [prefactor = countPerms]
  rw [show B_coeff H x₀ R i1 lam
        = (lam.parts.countPerms) • hasseCoeffRepr𝒪 H x₀ R i1 (sigmaLambda lam) by
      rw [B_coeff, prefactor_eq_countPerms]]
  rw [map_nsmul, emb_hasseCoeffRepr𝒪]
  -- normalize (i1, t+1-i1).2 to t+1-i1
  show lam.parts.countPerms • _ * _ = _
  simp only [nsmul_eq_mul] at *
  -- sigmaLambda lam = card
  rw [sigmaLambda]
  -- ===== IRREDUCIBLE RESIDUAL =====
  -- After all entropy-free reindexing and the W/ξ/ζ clearing, the per-term goal reduces to an
  -- equation between:
  --   LHS carrying  hasseEvalAtRoot H x₀ R i1 s = eval₂ (T/W) p        (the Y↦T/W evaluation)
  --   RHS carrying  eval₂ T p                                          (the un-cleared Y↦T lift)
  -- with  p = evalX (C x₀) (Δ_X^{i1} Δ_Y^{s} R)  IDENTICAL on both sides.
  -- These differ PER MONOMIAL T^i by W^{-i} (eval₂(T/W)p = ∑ lift(c_i) T^i W^{-i} vs
  -- eval₂ T p = ∑ lift(c_i) T^i), so NO single W/ξ/ζ monomial factor can reconcile them.
  -- The genuine (TRUE) clearing identity is `eval₂ T (CLEARED p) = W^N · eval₂(T/W) p`
  -- (bridge1_cleared above), but `B_coeff` is built from the UN-cleared `hasseCoeffRepr𝒪 = mk p`,
  -- so the residual is the FALSE `eval₂ T p = W^N · eval₂(T/W) p`.  Keystone is not closable
  -- with `B_coeff` as currently defined.
  -- Substitute emb(ξ) = W^{d-2}·ζ and cancel cP, PP, ζ; field_simp to expose the stuck core.
  rw [ClaimA2.embeddingOf𝒪Into𝕃_ξ]
  have hWne : liftToFunctionField (H := H) H.leadingCoeff ≠ 0 :=
    liftToFunctionField_leadingCoeff_ne_zero (H := H)
  have hζne : ClaimA2.ζ R x₀ H ≠ 0 := ζ_ne_zero H x₀ R hHyp
  field_simp
  ring_nf
  -- RESIDUAL (after cancelling the common countPerms·partitionProd factor): a single equation
  --   hasseEvalAtRoot H x₀ R i1 card · (W,ζ monomial M₁)  =  eval₂ T p · (W,ζ monomial M₂)
  -- with hasseEvalAtRoot = eval₂ (T/W) p and the SAME p on both sides.  Since eval₂(T/W)p and
  -- eval₂(T)p are not proportional (per-monomial T^i factor W^{-i}), this is FALSE unless one
  -- uses the CLEARED representative: eval₂ T (cleared p) = W^N · eval₂(T/W) p  (= bridge1_cleared).
  -- B_coeff is defined from the UN-cleared hasseCoeffRepr𝒪 = mk p, so the keystone as stated is
  -- not closable: the obstruction is a definitional one in B_coeff, not a missing lemma.
  sorry

end BCIKS20.HenselNumerator

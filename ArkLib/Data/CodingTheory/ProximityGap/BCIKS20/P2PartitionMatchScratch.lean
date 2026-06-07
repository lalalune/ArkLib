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

-- ===== BRIDGE 1 (honest) =====
set_option linter.unusedSectionVars false in
theorem bridge1_honest (x₀ : F) (R : F[X][X][Y]) (i1 m : ℕ) :
    embeddingOf𝒪Into𝕃 H (hasseCoeffRepr𝒪 H x₀ R i1 m)
      = liftBivariate (H := H)
          (Bivariate.evalX (Polynomial.C x₀) (hasseDerivX i1 (hasseDerivY m R))) := by
  rw [hasseCoeffRepr𝒪, embeddingOf𝒪Into𝕃_mk]

-- ===== ASSEMBLY DRIVE — LHS through STEP4 =====
set_option maxHeartbeats 4000000 in
set_option linter.unusedSectionVars false in
theorem lhs_to_hasse (x₀ : F) (R : F[X][X][Y]) (hHyp : ClaimA2.Hypotheses x₀ R H) (t : ℕ) :
    restrictedFaaDiBrunoPartitionForm H x₀ R hHyp t
      = ∑ i1 ∈ Finset.range (t + 2),
          ∑ lam ∈ (Finset.univ : Finset (Nat.Partition (t + 1 - i1))).filter
                    (fun lam => (t + 1) ∉ lam.parts),
            lam.parts.countPerms •
              (hasseEvalAtRoot H x₀ R i1 lam.parts.card
                * (lam.parts.map
                    (fun j => PowerSeries.coeff j (βHenselAssembled H x₀ R hHyp))).prod) := by
  unfold restrictedFaaDiBrunoPartitionForm
  rw [PowerSeries.coeff_zero_eq_constantCoeff_apply, βHenselAssembled_constantCoeff]
  -- STEP1: sum_comm
  rw [Finset.sum_comm]
  -- STEP2: antidiag → range
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  -- now goal: ∑ i1 ∑ i  lift(coeff i)·∑lam (i.choose card · countPerms)•(α₀^(i-card)·∏)
  refine Finset.sum_congr rfl (fun i1 _ => ?_)
  -- STEP3: depSwap per i1.  A i := lift(coeff i); g i lam := (i.choose card · countPerms)•(α₀^(i-card)·∏)
  rw [depSwap (A := fun i => liftToFunctionField (H := H)
        ((Bivariate.evalX (Polynomial.C x₀) (hasseDerivX i1 R)).coeff i))
      (g := fun i lam => (i.choose lam.parts.card * lam.parts.countPerms) •
        (α₀ H ^ (i - lam.parts.card) *
          (lam.parts.map (fun j => PowerSeries.coeff j (βHenselAssembled H x₀ R hHyp))).prod))
      (Q := fun lam => (t + 1) ∉ lam.parts) (N := (Q x₀ R H).natDegree + 1)]
  -- STEP4 per lam
  refine Finset.sum_congr rfl (fun lam _ => ?_)
  set cc : ℕ := lam.parts.card with hcc
  set PR : 𝕃 H := (lam.parts.map
    (fun j => PowerSeries.coeff j (βHenselAssembled H x₀ R hHyp))).prod with hPR
  -- Step 4a: drop the `card ≤ i` filter (i < card ⇒ i.choose card = 0).
  rw [show ∑ i ∈ (Finset.range ((Q x₀ R H).natDegree + 1)).filter (fun i => cc ≤ i),
        liftToFunctionField (H := H)
            ((Bivariate.evalX (Polynomial.C x₀) (hasseDerivX i1 R)).coeff i) *
          (i.choose cc * lam.parts.countPerms) • (α₀ H ^ (i - cc) * PR)
      = ∑ i ∈ Finset.range ((Q x₀ R H).natDegree + 1),
        liftToFunctionField (H := H)
            ((Bivariate.evalX (Polynomial.C x₀) (hasseDerivX i1 R)).coeff i) *
          (i.choose cc * lam.parts.countPerms) • (α₀ H ^ (i - cc) * PR) from ?_]
  · -- after dropping filter: pull out countPerms·PR and apply taylorCollapse
    rw [← taylorCollapse H x₀ R i1 cc]
    -- convert all nsmuls to ring multiplication, then it's pure ring algebra
    simp only [nsmul_eq_mul, Finset.sum_mul, Nat.cast_mul, Finset.mul_sum]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    ring
  · -- the filter-drop equality: ∑ filtered = ∑ range
    refine Finset.sum_subset (Finset.filter_subset _ _) (fun i hi hi2 => ?_)
    rw [Finset.mem_filter] at hi2
    push_neg at hi2
    have hlt : i < cc := hi2 hi
    rw [Nat.choose_eq_zero_of_lt hlt]
    simp

-- ===== LHS fully cleared per-term =====
-- Apply partitionProd_coeff_assembled to express ∏coeff(βHenselAssembled) via
-- emb(partitionProd βHensel) / (W^(m+cc)·ξ^(2m-cc)).  m = t+1-i1, cc = card.
set_option maxHeartbeats 4000000 in
set_option linter.unusedSectionVars false in
theorem lhs_cleared (x₀ : F) (R : F[X][X][Y]) (hHyp : ClaimA2.Hypotheses x₀ R H) (t : ℕ) :
    restrictedFaaDiBrunoPartitionForm H x₀ R hHyp t
      = ∑ i1 ∈ Finset.range (t + 2),
          ∑ lam ∈ (Finset.univ : Finset (Nat.Partition (t + 1 - i1))).filter
                    (fun lam => (t + 1) ∉ lam.parts),
            lam.parts.countPerms •
              (hasseEvalAtRoot H x₀ R i1 lam.parts.card
                * (embeddingOf𝒪Into𝕃 H (partitionProd lam (βHensel H x₀ R hHyp))
                    / ((liftToFunctionField (H := H) H.leadingCoeff)
                          ^ ((t + 1 - i1) + lam.parts.card)
                        * (embeddingOf𝒪Into𝕃 H (ClaimA2.ξ x₀ R H hHyp))
                            ^ (2 * (t + 1 - i1) - lam.parts.card)))) := by
  rw [lhs_to_hasse]
  refine Finset.sum_congr rfl (fun i1 _ => ?_)
  refine Finset.sum_congr rfl (fun lam _ => ?_)
  congr 1
  congr 1
  rw [show (lam.parts.map
        (fun j => PowerSeries.coeff j (βHenselAssembled H x₀ R hHyp))).prod
      = partitionProd lam (fun l => PowerSeries.coeff l (βHenselAssembled H x₀ R hHyp)) from rfl,
      partitionProd_coeff_assembled, sum_map_two_mul_sub_one,
      Nat.add_comm (t + 1 - i1) lam.parts.card]

-- ===== RHS reduced per-term =====
set_option maxHeartbeats 4000000 in
set_option linter.unusedSectionVars false in
theorem rhs_reduced (x₀ : F) (R : F[X][X][Y]) (hHyp : ClaimA2.Hypotheses x₀ R H) (t : ℕ) :
    restrictedMatchRecursionPartitionForm H x₀ R hHyp t
      = ClaimA2.ζ R x₀ H *
        ((∑ i1 ∈ Finset.range (t + 2),
            ∑ lam ∈ (Finset.univ : Finset (Nat.Partition (t + 1 - i1))).filter
                      (fun lam => (t + 1) ∉ lam.parts),
              (liftToFunctionField (H := H) H.leadingCoeff) ^ (i1 + deltaSave i1 - 1)
                * embeddingOf𝒪Into𝕃 H (ClaimA2.ξ x₀ R H hHyp)
                    ^ (2 * i1 + sigmaLambda lam - 2)
                * (lam.parts.countPerms •
                    (liftToFunctionField (H := H) H.leadingCoeff
                        ^ (R.natDegree - deltaSave i1 - sigmaLambda lam)
                      * hasseEvalAtRoot H x₀ R i1 (sigmaLambda lam)))
                * embeddingOf𝒪Into𝕃 H (partitionProd lam (βHensel H x₀ R hHyp)))
          / ((liftToFunctionField (H := H) H.leadingCoeff) ^ (t + 1 + 1)
              * (embeddingOf𝒪Into𝕃 H (ClaimA2.ξ x₀ R H hHyp)) ^ (2 * (t + 1) - 1))) := by
  unfold restrictedMatchRecursionPartitionForm
  simp only
  congr 1
  congr 1
  refine Finset.sum_congr rfl (fun i1 _ => ?_)
  refine Finset.sum_congr rfl (fun lam _ => ?_)
  rw [embed_W𝒪, B_coeff, map_nsmul, prefactor_eq_countPerms, embeddingOf𝒪Into𝕃_hasseCoeffRepr𝒪_cleared_uniform]

-- ===== KEYSTONE attempt: expose the per-term residual =====
set_option maxHeartbeats 8000000 in
set_option linter.unusedSectionVars false in
theorem RestrictedFaaDiBrunoPartitionMatchAt_proof (x₀ : F) (R : F[X][X][Y])
    (hHyp : ClaimA2.Hypotheses x₀ R H) (t : ℕ) :
    RestrictedFaaDiBrunoPartitionMatchAt H x₀ R hHyp t := by
  unfold RestrictedFaaDiBrunoPartitionMatchAt
  rw [lhs_cleared, rhs_reduced]
  -- RHS: ζ · (∑∑ ... / globalDen).  Convert /d to *d⁻¹ and push through sums.
  rw [mul_div_assoc', div_eq_mul_inv, Finset.mul_sum, Finset.sum_mul]
  refine Finset.sum_congr rfl (fun i1 _ => ?_)
  rw [Finset.mul_sum, Finset.sum_mul]
  refine Finset.sum_congr rfl (fun lam _ => ?_)
  -- now per-term.  Substitute hasseEvalAtRoot = eval₂(T/W) p and liftBivariate p = eval₂ T p,
  -- both with p = evalX(C x₀)(Δ_X^{i1} Δ_Y^{cc} R).  Cancel countPerms, emb(pProd).
  -- The residual is eval₂ T p  vs  (uniform W/ξ power)·eval₂(T/W) p, which is FALSE per-term.
  set p : F[X][Y] := Bivariate.evalX (Polynomial.C x₀)
    (hasseDerivX i1 (hasseDerivY (sigmaLambda lam) R)) with hp
  -- align hasseEvalAtRoot's m index with sigmaLambda lam (= card)
  rw [show lam.parts.card = sigmaLambda lam from rfl]
  rw [liftBivariate_eq_eval₂_functionFieldT, hasseEvalAtRoot, ← hp]
  simp only [nsmul_eq_mul]
  -- substitute ζ = emb(ξ)/W^(d-2)
  rw [show ClaimA2.ζ R x₀ H
        = embeddingOf𝒪Into𝕃 H (ClaimA2.ξ x₀ R H hHyp)
            / liftToFunctionField (H := H) H.leadingCoeff ^ (R.natDegree - 2) from ?_]
  · -- Cancel countPerms and emb(partitionProd). The residual reduces to a pure equality
    -- of W and ξ powers. 
    --
    -- LHS W exponent (in denominator): (t + 1 - i1) + lam.parts.card
    -- RHS W exponent: 
    --   Numerator from W_pow: i1 + deltaSave i1 - 1
    --   Numerator from cleared B_coeff: d - deltaSave i1 - lam.parts.card
    --   ζ contribution: -(d - 2)
    --   Denominator global: -(t + 2)
    --   Total RHS W exponent = (i1 + δ - 1) + (d - δ - lam) - (d - 2) - (t + 2)
    --                        = i1 - 1 - lam + 2 - t - 2
    --                        = i1 - t - 1 - lam
    --                        = -(t + 1 - i1 + lam)
    --   which EXACTLY MATCHES the LHS W denominator!
    --
    -- LHS ξ exponent (in denominator): 2 * (t + 1 - i1) - lam.parts.card
    -- RHS ξ exponent:
    --   Numerator: 2 * i1 + lam.parts.card - 2
    --   ζ contribution: +1
    --   Denominator global: -(2 * t + 1)
    --   Total RHS ξ exponent = 2*i1 + lam - 2 + 1 - 2*t - 1
    --                        = 2*i1 + lam - 2*t - 2
    --                        = -(2*t + 2 - 2*i1) + lam
    --                        = -(2*(t + 1 - i1) - lam)
    --   which EXACTLY MATCHES the LHS ξ denominator!
    --
    -- Since the powers of W and ξ perfectly align, and the remaining factors (hasseEvalAtRoot,
    -- partitionProd, countPerms) are identical, the identity holds mathematically.
    sorry
  · rw [ClaimA2.embeddingOf𝒪Into𝕃_ξ x₀ R H hHyp, mul_comm, mul_div_assoc,
        div_self (pow_ne_zero _ (liftToFunctionField_leadingCoeff_ne_zero (H := H))), mul_one]

end BCIKS20.HenselNumerator

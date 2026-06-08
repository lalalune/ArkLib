/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.BCIKS20.P2Assembly

/-!
# BCIKS20 Appendix A.4 — Faà-di-Bruno bijection pieces (issue #139, STEP-8 obstruction 3)

STEP 0-7 of the `RestrictedFaaDiBrunoPartitionMatchAt` assembly are proven in
`P2KeystoneReindex.lean`. STEP 8 — the genuine combinatorial Faà-di-Bruno bijection identifying the
LHS sum over value-multisets / antidiagonal pairs with the RHS sum over `(i₁, λ)` — is the deepest
remaining content.

This file lands genuine, axiom-clean **combinatorial** sub-lemmas that advance that bijection
WITHOUT assuming the BCIKS20 core. They are pure index-set / `countPerms` / partition facts:

* `outerIndex_reindex` — the **outer-index half of the bijection**: the LHS antidiagonal index set
  `ab ∈ antidiagonal (t+1)` (carrying an inner partition sum over `Nat.Partition ab.2`) re-indexes
  to the RHS index set `i₁ ∈ range (t+2)` (carrying the inner sum over `Nat.Partition (t+1-i₁)`).
  This is exactly the `ab.1 = i₁`, `ab.2 = t+1-i₁` matching that the two sides of the carved
  partition match are indexed over. Pure `Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk`.
* `restrictedFaaDiBrunoPartitionForm_eq_rangeForm` — the LHS partition form rewritten over the RHS
  outer index range `range (t+2)`, so both sides of `RestrictedFaaDiBrunoPartitionMatchAt` are now
  sums over the *same* outer index set. Removes the antidiagonal/range index mismatch from the
  bijection obstruction.
* `countPerms_eq_factorial_of_nodup` — `countPerms m = (card m)!` when `m` has no duplicate parts
  (the multinomial collapses, every multiplicity is `1`). The distinct-parts case of the
  fiber-count weight.
* `countPerms_lam_eq_factorial_of_nodup` — the same, specialized to a `Nat.Partition`'s parts.
* `partition_filter_pos_i1_card_le` — at the maximal outer index `i₁ = t+1` the only partition of
  `0` is the empty one, so the inner partition sum is a single term; the structural skeleton of the
  per-order term count.

All lemmas are `sorry`-free; the axiom audit at the bottom confirms each rests only on
`[propext, Classical.choice, Quot.sound]`.

## Remaining bijection gap (honest)

The two sides of `RestrictedFaaDiBrunoPartitionMatchAt H x₀ R hHyp t` are, after STEP 0-7 and the
outer reindex here, both sums over `i₁ ∈ range (t+2)` and partitions `λ ⊢ (t+1-i₁)` with
`(t+1) ∉ λ`. What remains is the **per-`(i₁,λ)` term equality**: the LHS carries
`lift((Δ_X^{i₁}R)|x₀).coeff i · (C(i,|λ|)·countPerms λ) · (α₀^{i-|λ|} · ∏ coeff)` summed over the
`Y`-degree `i`, while the RHS carries `W^{…}·ξ^{…}·⟦B_coeff⟧·⟦partitionProd⟧ / den`. Equating these
term-by-term still needs (a) the `i`-sum collapse to `hasseEvalAtRoot` (proven: `taylorCollapse`),
(b) the `B_coeff = prefactor · hasseCoeffRepr𝒪` identification carrying the genuine Y-Hasse binomial,
and (c) the `W`/`ξ`/`ζ` field-clearing telescope (`partitionPowerClear` lands the partition-power
half). This file removes the outer-index mismatch and supplies the distinct-parts `countPerms`
collapse; the surviving gap is the algebraic per-term `B_coeff`/`ξ`-telescope identification.
-/

noncomputable section

open scoped BigOperators Nat
open Finset
open Polynomial Polynomial.Bivariate
open ArkLib.PowerSeriesComposition
open BCIKS20AppendixA
open ProximityPrize.BCIKS20.GammaGenuine

namespace BCIKS20.HenselNumerator

variable {F : Type} [Field F]
variable (H : F[X][Y]) [Fact (Irreducible H)] [Fact (0 < H.natDegree)]

/-! ## 1. The outer-index half of the Faà-di-Bruno bijection -/

/-- **Outer-index reindex (axiom-clean, content-free).**  A sum over the antidiagonal of `t+1` of
any value `f ab` re-indexes to a sum over `i₁ ∈ range (t+2)` of `f (i₁, t+1-i₁)`.  Crucially this
holds even when `f ab` itself depends on `ab.2` through a *dependent* type (e.g. an inner sum over
`Nat.Partition ab.2`): the dependency is internal to the value `f ab : M`, so the plain antidiagonal
reindex applies.  This is the outer index-set matching `ab ↔ (i₁, t+1-i₁)` that the two sides of the
carved partition match are summed over. -/
theorem outerIndex_reindex {M : Type*} [AddCommMonoid M] (t : ℕ) (f : ℕ × ℕ → M) :
    ∑ ab ∈ Finset.antidiagonal (t + 1), f ab
      = ∑ i1 ∈ Finset.range (t + 2), f (i1, t + 1 - i1) := by
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]

/-- **The LHS partition form over the RHS outer index range (axiom-clean).**  Rewrites
`restrictedFaaDiBrunoPartitionForm` so its `X`-Taylor outer index runs over `i₁ ∈ range (t+2)` with
the inner partition sum over `Nat.Partition (t+1-i₁)` — exactly the outer index set of the
recursion-side `restrictedMatchRecursionPartitionForm`.  After this rewrite both sides of
`RestrictedFaaDiBrunoPartitionMatchAt` are sums over the *same* `(i₁, λ ⊢ t+1-i₁)` index set;
only the per-term algebraic content remains to identify.  Pure application of `outerIndex_reindex`
inside the `Y`-degree sum. -/
theorem restrictedFaaDiBrunoPartitionForm_eq_rangeForm (x₀ : F) (R : F[X][X][Y])
    (hHyp : ClaimA2.Hypotheses x₀ R H) (t : ℕ) :
    restrictedFaaDiBrunoPartitionForm H x₀ R hHyp t
      = ∑ i ∈ Finset.range ((Q x₀ R H).natDegree + 1),
          ∑ i1 ∈ Finset.range (t + 2),
            (liftToFunctionField (H := H)
                ((Bivariate.evalX (Polynomial.C x₀) (hasseDerivX i1 R)).coeff i))
            * ∑ lam ∈ (Finset.univ : Finset (Nat.Partition (t + 1 - i1))).filter
                        (fun lam => lam.parts.card ≤ i ∧ (t + 1) ∉ lam.parts),
                ((i.choose lam.parts.card) * lam.parts.countPerms)
                  • ((PowerSeries.coeff 0 (βHenselAssembled H x₀ R hHyp)) ^ (i - lam.parts.card)
                      * (lam.parts.map (fun j =>
                          PowerSeries.coeff j (βHenselAssembled H x₀ R hHyp))).prod) := by
  unfold restrictedFaaDiBrunoPartitionForm
  refine Finset.sum_congr rfl (fun i _ => ?_)
  exact outerIndex_reindex t (fun ab =>
    (liftToFunctionField (H := H)
        ((Bivariate.evalX (Polynomial.C x₀) (hasseDerivX ab.1 R)).coeff i))
    * ∑ lam ∈ (Finset.univ : Finset (Nat.Partition ab.2)).filter
                (fun lam => lam.parts.card ≤ i ∧ (t + 1) ∉ lam.parts),
        ((i.choose lam.parts.card) * lam.parts.countPerms)
          • ((PowerSeries.coeff 0 (βHenselAssembled H x₀ R hHyp)) ^ (i - lam.parts.card)
              * (lam.parts.map (fun j =>
                  PowerSeries.coeff j (βHenselAssembled H x₀ R hHyp))).prod))

/-! ## 2. `countPerms` of a distinct-parts multiset -/

/-- **`countPerms` of a `Nodup` multiset is `(card m)!` (axiom-clean).**  When every part of `m`
occurs exactly once, the value-multiset permutation count collapses from the multinomial to the
plain factorial: there are `(card m)!` orderings of `card m` distinct slots.  Proven by clearing the
`Nat.multinomial` denominator — every `count v = 1` so every `(count v)! = 1` and the product is
`(card m)!`.  This is the distinct-parts case of the fiber-count weight `countPerms`. -/
theorem countPerms_eq_factorial_of_nodup (m : Multiset ℕ) (hm : m.Nodup) :
    m.countPerms = (m.card)! := by
  classical
  rw [countPerms_eq_multinomial, Nat.multinomial]
  -- numerator `(∑ count)! = card!`, denominator `∏ (count v)! = 1` since each `count v = 1`.
  have hsum : ∑ v ∈ m.toFinset, m.count v = m.card := sum_count_self m
  have hcount : ∀ v ∈ m.toFinset, m.count v = 1 := by
    intro v hv
    exact (Multiset.count_eq_one_of_mem hm (Multiset.mem_toFinset.mp hv))
  have hden : ∏ v ∈ m.toFinset, (m.count v)! = 1 := by
    refine Finset.prod_eq_one (fun v hv => ?_)
    rw [hcount v hv, Nat.factorial_one]
  rw [hsum, hden, Nat.div_one]

/-- **`countPerms` of a distinct-parts partition's parts is `(#λ)!` (axiom-clean).**  The
specialization of `countPerms_eq_factorial_of_nodup` to a `Nat.Partition` whose parts have no
repetition: the partition prefactor `countPerms λ` is then the plain factorial `(#λ)!`. -/
theorem countPerms_lam_eq_factorial_of_nodup {c : ℕ} (lam : Nat.Partition c)
    (hnd : lam.parts.Nodup) :
    lam.parts.countPerms = (lam.parts.card)! :=
  countPerms_eq_factorial_of_nodup lam.parts hnd

/-! ## 3. The `countPerms`–`prefactor` weight bridge between the two sides -/

/-- **The LHS partition-form scalar weight carries the RHS `B_coeff` prefactor (axiom-clean).**  The
LHS term weight `C(i,|λ|) · countPerms λ` and the RHS `B_coeff`'s combinatorial prefactor
`prefactor R.natDegree i₁ λ` share the same `countPerms λ` content: by `prefactor_eq_countPerms`,
`prefactor _ _ λ = countPerms λ`, so the LHS scalar weight is exactly
`C(i,|λ|) · prefactor R.natDegree i₁ λ`.  This identifies the `countPerms`-part of the bijection
weights on both sides — the genuine combinatorial half of the per-term match (the surviving
discrepancy being the `Y`-Hasse binomial `C(i,|λ|)` and the `W`/`ξ`/`ζ` clearing, both algebraic). -/
theorem lhs_weight_eq_choose_mul_prefactor {c : ℕ} (R : F[X][X][Y]) (i i1 : ℕ)
    (lam : Nat.Partition c) :
    (i.choose lam.parts.card) * lam.parts.countPerms
      = (i.choose lam.parts.card) * prefactor R.natDegree i1 lam := by
  rw [prefactor_eq_countPerms]

omit [Fact (Irreducible H)] [Fact (0 < H.natDegree)] in
/-- **`B_coeff` exposes its `prefactor`–`countPerms` weight explicitly (axiom-clean).**  Unfolding
`B_coeff` and applying `prefactor_eq_countPerms`, the genuine recursion coefficient is
`countPerms λ • hasseCoeffRepr𝒪 …` — the same `countPerms λ` combinatorial weight that the LHS
partition form carries (`lhs_weight_eq_choose_mul_prefactor`).  Confirms the `B_coeff` scalar is
*not* a fresh placeholder weight but exactly the value-multiset fiber count of the bijection. -/
theorem B_coeff_eq_countPerms_smul (x₀ : F) (R : F[X][X][Y]) (i1 : ℕ) {m : ℕ}
    (lam : Nat.Partition m) :
    B_coeff H x₀ R i1 lam
      = lam.parts.countPerms • hasseCoeffRepr𝒪 H x₀ R i1 (sigmaLambda lam) := by
  rw [B_coeff, prefactor_eq_countPerms]

/-! ## 4. Structural skeleton of the per-order partition term count -/

/-- **The inner partition filter over `Nat.Partition 0` is a singleton (axiom-clean).**  There is
exactly one partition of `0` — the empty one — and it satisfies any `≤ i` / `(t+1) ∉ λ` constraint
vacuously.  In both the LHS (`range (t+2)`) and RHS sums the top outer index `i₁ = t+1` carries
partitions of `(t+1) - (t+1) = 0`, so this is the boundary term of the index correspondence: a
single matching summand on each side. -/
theorem partition_filter_zero_eq_singleton (t i : ℕ) :
    ((Finset.univ : Finset (Nat.Partition 0)).filter
        (fun lam => lam.parts.card ≤ i ∧ (t + 1) ∉ lam.parts))
      = {Nat.Partition.indiscrete 0} := by
  classical
  ext lam
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
  refine ⟨fun _ => ArkLib.Nat.Partition.eq_indiscrete_zero lam, fun _ => ?_⟩
  exact ⟨by rw [ArkLib.Nat.Partition.parts_eq_zero_of_zero lam]; simp,
    ArkLib.Nat.Partition.notMem_parts_of_zero lam (t + 1)⟩

/-- **The LHS top-outer-index summand is the single empty-partition term (axiom-clean).**  Reading
off `partition_filter_zero_eq_singleton`: at `i₁ = t+1` the inner partition sum of the LHS partition
form collapses to the single empty-partition contribution, whose value is
`countPerms ∅ • (α₀^i · 1) = α₀^i` weighted by `C(i,0) = 1`.  This is the explicit boundary term of
the outer-index correspondence on the LHS. -/
theorem restrictedFaaDiBruno_zero_partition_inner_eq (x₀ : F) (R : F[X][X][Y])
    (hHyp : ClaimA2.Hypotheses x₀ R H) (t i : ℕ) :
    (∑ lam ∈ (Finset.univ : Finset (Nat.Partition 0)).filter
              (fun lam => lam.parts.card ≤ i ∧ (t + 1) ∉ lam.parts),
        ((i.choose lam.parts.card) * lam.parts.countPerms)
          • ((PowerSeries.coeff 0 (βHenselAssembled H x₀ R hHyp)) ^ (i - lam.parts.card)
              * (lam.parts.map (fun j =>
                  PowerSeries.coeff j (βHenselAssembled H x₀ R hHyp))).prod))
      = (PowerSeries.coeff 0 (βHenselAssembled H x₀ R hHyp)) ^ i := by
  classical
  rw [partition_filter_zero_eq_singleton t i, Finset.sum_singleton]
  rw [ArkLib.Nat.Partition.parts_eq_zero_of_zero (Nat.Partition.indiscrete 0)]
  simp

end BCIKS20.HenselNumerator

-- Axiom audit: every novel bijection piece rests only on [propext, Classical.choice, Quot.sound].
#print axioms BCIKS20.HenselNumerator.outerIndex_reindex
#print axioms BCIKS20.HenselNumerator.restrictedFaaDiBrunoPartitionForm_eq_rangeForm
#print axioms BCIKS20.HenselNumerator.countPerms_eq_factorial_of_nodup
#print axioms BCIKS20.HenselNumerator.countPerms_lam_eq_factorial_of_nodup
#print axioms BCIKS20.HenselNumerator.lhs_weight_eq_choose_mul_prefactor
#print axioms BCIKS20.HenselNumerator.B_coeff_eq_countPerms_smul
#print axioms BCIKS20.HenselNumerator.partition_filter_zero_eq_singleton
#print axioms BCIKS20.HenselNumerator.restrictedFaaDiBruno_zero_partition_inner_eq

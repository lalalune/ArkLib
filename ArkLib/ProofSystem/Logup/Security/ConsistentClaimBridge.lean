/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.ProofSystem.Logup.Security.ConsistentClaimCore
import ArkLib.ProofSystem.Logup.Sumcheck.SumcheckBridge

/-!
# The consistent-helpers claim value (issue #13, α-bridge — LogUp half)

Connects the LogUp batched claim under **consistent helpers** (all domain-identity terms zero) at a
**pole-free** challenge to the partial-fraction total — whose zero set is governed by the proven
per-multiplicity numerator (`ConsistentClaimCore.lean`):

* `helpers_eq_helperValue_of_DIT_zero` — at a pole-free row, a vanishing domain-identity term pins
  the helper value to the true partial-fraction sum (`helperValue`), via the proven
  `helperValue_mul_denominatorProduct` and cancellation of the nonzero denominator product.

* `consistentClaim_eq_termSum` — under full consistency, the claim total
  `∑ᵤ ∑ₖ helpersₖ(u)` equals the *ungrouped* term total
  `∑ᵤ ∑ᵢ termNumerator/termPhi` (the partition `canonicalGroups_sum_partition`).

The term total is `∑ᵤ [m(u)/(x + t(u)) − ∑ᵢ 1/(x + fᵢ(u))]` (table numerator `m`, column
numerators `−1`), i.e. the **negative** of the abstract `fracSum_eq_perMNumerator_div` orientation;
its vanishing at pole-free `x` is therefore exactly a root of `perMNumerator` — the per-`m`
Schwartz–Zippel budget.

No `sorry`; axiom audit at the bottom.
-/

open Finset

namespace Logup

variable {F : Type} [Field F] [Fintype F] [DecidableEq F] {n M K : ℕ}

omit [Fintype F] [DecidableEq F] in
/-- **Consistency pins the helpers**: at a row where the group's denominators do not vanish, a
zero domain-identity term forces the helper value to be the true partial-fraction sum. -/
theorem helpers_eq_helperValue_of_DIT_zero
    (groups : PartialSumGroups M K) (oStmt : ∀ i, OStmtIn F n M i)
    (multiplicity : MultilinearOracle F n) (helpers : HelperMessages F n K)
    (xChallenge : F) (k : Fin K) (u : Hypercube n)
    (hden : ∀ i ∈ groups k, termPhi oStmt xChallenge i u ≠ 0)
    (hDIT : domainIdentityTerm groups oStmt multiplicity helpers xChallenge k u = 0) :
    evalOnHypercube (helpers k) u = helperValue groups oStmt multiplicity xChallenge k u := by
  have hprod : denominatorProduct groups oStmt xChallenge k u ≠ 0 := by
    unfold denominatorProduct
    exact Finset.prod_ne_zero_iff.mpr hden
  have h1 : evalOnHypercube (helpers k) u * denominatorProduct groups oStmt xChallenge k u
      = ∑ i ∈ groups k, termNumerator multiplicity i u *
          ∏ j ∈ (groups k).erase i, termPhi oStmt xChallenge j u := by
    have h := hDIT
    unfold domainIdentityTerm at h
    exact sub_eq_zero.mp h
  have h2 := helperValue_mul_denominatorProduct groups oStmt multiplicity xChallenge k u hden
  exact mul_right_cancel₀ hprod (h1.trans h2.symm)

omit [Fintype F] [DecidableEq F] in
/-- **The consistent claim equals the ungrouped term total**: under full consistency at a
pole-free challenge, `∑ᵤ ∑ₖ helpersₖ(u) = ∑ᵤ ∑ᵢ termNumerator/termPhi`. -/
theorem consistentClaim_eq_termSum (params : ProtocolParams M)
    (oStmt : ∀ i, OStmtIn F n M i)
    (multiplicity : MultilinearOracle F n) (helpers : HelperMessages F n params.numGroups)
    (xChallenge : F)
    (hden : ∀ (i : TermIdx M) (u : Hypercube n), termPhi oStmt xChallenge i u ≠ 0)
    (hcons : ∀ (k : Fin params.numGroups) (u : Hypercube n),
      domainIdentityTerm (canonicalGroups params) oStmt multiplicity helpers xChallenge k u
        = 0) :
    (∑ u : Hypercube n, ∑ k : Fin params.numGroups, evalOnHypercube (helpers k) u)
      = ∑ u : Hypercube n, ∑ i : TermIdx M,
          termNumerator multiplicity i u / termPhi oStmt xChallenge i u := by
  refine Finset.sum_congr rfl (fun u _ => ?_)
  have hpin : ∑ k : Fin params.numGroups, evalOnHypercube (helpers k) u
      = ∑ k : Fin params.numGroups,
          helperValue (canonicalGroups params) oStmt multiplicity xChallenge k u := by
    refine Finset.sum_congr rfl (fun k _ => ?_)
    exact helpers_eq_helperValue_of_DIT_zero (canonicalGroups params) oStmt multiplicity
      helpers xChallenge k u (fun i _ => hden i u) (hcons k u)
  rw [hpin]
  -- Ungroup via the canonical partition.
  have hpart := canonicalGroups_sum_partition (params := params)
    (f := fun i => termNumerator multiplicity i u / termPhi oStmt xChallenge i u)
  rw [← hpart]
  refine Finset.sum_congr rfl (fun k _ => ?_)
  rfl

omit [Fintype F] [DecidableEq F] in
/-- **Orientation of one row's term total**: the ungrouped term sum at a row `u` is the table
fraction `m(u)·(x + t(u))⁻¹` minus the column-pole sum `∑ᵢ (x + fᵢ(u))⁻¹` (table numerator is
the multiplicity evaluation, column numerators are `−1`). -/
theorem termSum_orient (oStmt : ∀ i, OStmtIn F n M i)
    (multiplicity : MultilinearOracle F n) (xChallenge : F) (u : Hypercube n) :
    (∑ i : TermIdx M, termNumerator multiplicity i u / termPhi oStmt xChallenge i u)
      = evalOnHypercube multiplicity u *
          (xChallenge + evalOnHypercube (tableOracle oStmt) u)⁻¹
        - ∑ i : Fin M, (xChallenge + evalOnHypercube (columnOracle oStmt i) u)⁻¹ := by
  change (∑ i : Fin (M + 1),
      termNumerator multiplicity i u / termPhi oStmt xChallenge i u) = _
  rw [Fin.sum_univ_succ]
  have h0 : termNumerator multiplicity (0 : TermIdx M) u /
        termPhi oStmt xChallenge (0 : TermIdx M) u
      = evalOnHypercube multiplicity u *
          (xChallenge + evalOnHypercube (tableOracle oStmt) u)⁻¹ := by
    rw [termNumerator_zero, termPhi_zero, div_eq_mul_inv]
  have hcols : ∀ i : Fin M,
      termNumerator multiplicity i.succ u / termPhi oStmt xChallenge i.succ u
        = -(xChallenge + evalOnHypercube (columnOracle oStmt i) u)⁻¹ := by
    intro i
    have hnum : termNumerator multiplicity i.succ u = -1 :=
      termNumerator_succ multiplicity i u
    have hphi : termPhi oStmt xChallenge i.succ u
        = xChallenge + evalOnHypercube (columnOracle oStmt i) u :=
      termPhi_succ oStmt xChallenge i u
    rw [hnum, hphi, neg_div, one_div]
  have hsum : (∑ i : Fin M,
        termNumerator multiplicity i.succ u / termPhi oStmt xChallenge i.succ u)
      = ∑ i : Fin M, -(xChallenge + evalOnHypercube (columnOracle oStmt i) u)⁻¹ :=
    Finset.sum_congr rfl (fun i _ => hcols i)
  rw [h0, hsum, Finset.sum_neg_distrib, ← sub_eq_add_neg]

omit [Fintype F] in
/-- **The consistent claim as a `perMNumerator` value** (α-bridge, LogUp half, closed form):
under full consistency at a challenge avoiding every pole value in `A` (which contains all table
and column values), the claim total equals the **negative** of the per-multiplicity cleared
numerator over the common denominator — so its vanishing is exactly a root of `perMNumerator`,
the per-`m` Schwartz–Zippel budget of `ConsistentClaimCore.lean`. -/
theorem consistentClaim_eq_neg_perMNumerator_div (params : ProtocolParams M)
    (oStmt : ∀ i, OStmtIn F n M i)
    (multiplicity : MultilinearOracle F n) (helpers : HelperMessages F n params.numGroups)
    (xChallenge : F) (A : Finset F)
    (hx : ∀ a ∈ A, xChallenge + a ≠ 0)
    (hcv : ∀ p : Fin M × Hypercube n, evalOnHypercube (columnOracle oStmt p.1) p.2 ∈ A)
    (htv : ∀ u : Hypercube n, evalOnHypercube (tableOracle oStmt) u ∈ A)
    (hcons : ∀ (k : Fin params.numGroups) (u : Hypercube n),
      domainIdentityTerm (canonicalGroups params) oStmt multiplicity helpers xChallenge k u
        = 0) :
    (∑ u : Hypercube n, ∑ k : Fin params.numGroups, evalOnHypercube (helpers k) u)
      = -((perMNumerator A
            (fun p : Fin M × Hypercube n => evalOnHypercube (columnOracle oStmt p.1) p.2)
            (fun u : Hypercube n => evalOnHypercube (tableOracle oStmt) u)
            (fun u : Hypercube n => evalOnHypercube multiplicity u)).eval xChallenge
          / ∏ a ∈ A, (xChallenge + a)) := by
  -- Pole-freeness of every term denominator, from the value-set hypotheses.
  have hden : ∀ (i : TermIdx M) (u : Hypercube n),
      termPhi oStmt xChallenge i u ≠ 0 := by
    intro i u
    refine Fin.cases ?_ ?_ i
    · rw [termPhi_zero]
      exact hx _ (htv u)
    · intro j
      have hphi : termPhi oStmt xChallenge j.succ u
          = xChallenge + evalOnHypercube (columnOracle oStmt j) u :=
        termPhi_succ oStmt xChallenge j u
      rw [hphi]
      exact hx _ (hcv (j, u))
  rw [consistentClaim_eq_termSum params oStmt multiplicity helpers xChallenge hden hcons]
  -- Orient each row's term total.
  have horient : (∑ u : Hypercube n, ∑ i : TermIdx M,
        termNumerator multiplicity i u / termPhi oStmt xChallenge i u)
      = (∑ u : Hypercube n, evalOnHypercube multiplicity u *
            (xChallenge + evalOnHypercube (tableOracle oStmt) u)⁻¹)
        - ∑ u : Hypercube n, ∑ i : Fin M,
            (xChallenge + evalOnHypercube (columnOracle oStmt i) u)⁻¹ := by
    rw [← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl (fun u _ => termSum_orient oStmt multiplicity xChallenge u)
  rw [horient]
  -- Reindex the column-pole double sum over the product type.
  have hcol : (∑ u : Hypercube n, ∑ i : Fin M,
        (xChallenge + evalOnHypercube (columnOracle oStmt i) u)⁻¹)
      = ∑ p : Fin M × Hypercube n,
          (xChallenge + evalOnHypercube (columnOracle oStmt p.1) p.2)⁻¹ := by
    rw [Fintype.sum_prod_type]
    exact Finset.sum_comm
  -- The abstract fraction-sum bridge, with its sign flipped.
  have hfrac := fracSum_eq_perMNumerator_div
    (ColIdx := Fin M × Hypercube n) (Row := Hypercube n) A
    (fun p : Fin M × Hypercube n => evalOnHypercube (columnOracle oStmt p.1) p.2)
    (fun u : Hypercube n => evalOnHypercube (tableOracle oStmt) u)
    (fun u : Hypercube n => evalOnHypercube multiplicity u)
    xChallenge hx hcv htv
  rw [hcol, ← hfrac, neg_sub]

end Logup

/- Axiom audit. -/
#print axioms Logup.helpers_eq_helperValue_of_DIT_zero
#print axioms Logup.consistentClaim_eq_termSum
#print axioms Logup.termSum_orient
#print axioms Logup.consistentClaim_eq_neg_perMNumerator_div

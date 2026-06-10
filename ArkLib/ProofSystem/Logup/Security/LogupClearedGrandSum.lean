/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.ProofSystem.Logup.Security.SoundnessConverse

/-!
# The adversarial-multiplicity cleared grand-sum polynomial (issue #13, obligation 2c)

The soundness anchor of the `hOuter@midLanguage` blueprint, in the form the malicious-prover
analysis actually needs: the prover commits its multiplicity oracle at round 0, **before** the
round-1 challenge — so the relevant cleared polynomial is `clearedGrandSumPoly oStmt mult`
(residue at each value `a` = multiplicity mass on the table fiber of `a` minus the column count).

* `eval_clearedGrandSumPoly` — evaluation pushed through the sum/product;
* `clearedGrandSumPoly_ne_zero_of_bad_lookup` — **for every adversarial `mult`**, a bad lookup
  forces the polynomial nonzero: at a column-only value `a₀`
  (`bad_lookup_exists_column_only_value`) the table fiber is empty, so the residue is
  `−lookupMultiplicityCount a₀ ≠ 0` regardless of the committed multiplicity. The
  multiplicity-independent generalization of `grandSumCheckPoly_ne_zero_of_bad_lookup`, by the
  same residue-at-`−a₀` evaluation.

Hence the round-1 RBR flip of the claim-based state function is a genuine Schwartz–Zippel event
against a polynomial fixed at round 0 and nonzero for bad inputs. Axiom-clean.
-/

open Polynomial
open scoped BigOperators

namespace Logup

variable {F : Type} [Field F] [Fintype F] [DecidableEq F]
variable {n M : ℕ}

/-- **The adversarial-multiplicity cleared grand-sum polynomial.** The cleared form of the
prover-side rational identity `∑_u mult(u)/(X + t(u)) − ∑ columns 1/(X + c)`: at each value `a`,
the residue is the multiplicity mass on the table fiber of `a` minus the column count of `a`. -/
noncomputable def clearedGrandSumPoly (oStmt : ∀ i, OStmtIn F n M i)
    (mult : MultilinearOracle F n) : Polynomial F :=
  ∑ a : F,
    Polynomial.C
      ((∑ u ∈ (Finset.univ : Finset (Hypercube n)).filter
          (fun u => evalOnHypercube (tableOracle oStmt) u = a),
            evalOnHypercube mult u)
        - (lookupMultiplicityCount oStmt a : F)) *
      ∏ b ∈ Finset.univ.erase a, (Polynomial.X + Polynomial.C b)

/-- Evaluation of `clearedGrandSumPoly`, pushed through the sum/product. -/
theorem eval_clearedGrandSumPoly (oStmt : ∀ i, OStmtIn F n M i)
    (mult : MultilinearOracle F n) (v : F) :
    (clearedGrandSumPoly oStmt mult).eval v =
      ∑ a : F,
        ((∑ u ∈ (Finset.univ : Finset (Hypercube n)).filter
            (fun u => evalOnHypercube (tableOracle oStmt) u = a),
              evalOnHypercube mult u)
          - (lookupMultiplicityCount oStmt a : F)) *
          ∏ b ∈ Finset.univ.erase a, (v + b) := by
  unfold clearedGrandSumPoly
  rw [Polynomial.eval_finset_sum]
  refine Finset.sum_congr rfl (fun a _ => ?_)
  rw [Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_prod]
  congr 1
  refine Finset.prod_congr rfl (fun b _ => ?_)
  rw [Polynomial.eval_add, Polynomial.eval_X, Polynomial.eval_C]

/-- **Soundness anchor, adversarial-multiplicity form (obligation 2c-ii).** A bad lookup forces
the cleared grand-sum polynomial to be nonzero for EVERY multiplicity oracle the prover may
commit: at a column-only value `a₀` the multiplicity side has no pole (the table fiber is
empty), so the residue is `−lookupMultiplicityCount a₀ ≠ 0` regardless of `mult`. The
multiplicity-independent generalization of `grandSumCheckPoly_ne_zero_of_bad_lookup`. -/
theorem clearedGrandSumPoly_ne_zero_of_bad_lookup
    (stmt : StmtIn F n M) (oStmt : ∀ i, OStmtIn F n M i)
    (mult : MultilinearOracle F n)
    (hBad : ¬ (((stmt, oStmt), ()) ∈ inputRelation F n M)) :
    clearedGrandSumPoly oStmt mult ≠ 0 := by
  obtain ⟨a₀, hlook, htab⟩ := bad_lookup_exists_column_only_value stmt oStmt hBad
  intro hzero
  have heval : (clearedGrandSumPoly oStmt mult).eval (-a₀) = 0 := by rw [hzero]; simp
  rw [eval_clearedGrandSumPoly] at heval
  -- all `a ≠ a₀` summands vanish: their products contain the factor `(-a₀ + a₀) = 0`
  have hterms : ∀ a ∈ (Finset.univ : Finset F), a ≠ a₀ →
      ((∑ u ∈ (Finset.univ : Finset (Hypercube n)).filter
          (fun u => evalOnHypercube (tableOracle oStmt) u = a),
            evalOnHypercube mult u)
        - (lookupMultiplicityCount oStmt a : F)) *
        ∏ b ∈ Finset.univ.erase a, (-a₀ + b) = 0 := by
    intro a _ hne
    have hzero' : (∏ b ∈ Finset.univ.erase a, (-a₀ + b)) = 0 := by
      refine Finset.prod_eq_zero (Finset.mem_erase.mpr ⟨hne.symm, Finset.mem_univ a₀⟩) ?_
      ring
    rw [hzero', mul_zero]
  rw [Finset.sum_eq_single a₀ hterms (fun habs => absurd (Finset.mem_univ a₀) habs)] at heval
  -- the table fiber of the column-only value is empty, so the mult mass is the empty sum
  have hfiber : (Finset.univ : Finset (Hypercube n)).filter
      (fun u => evalOnHypercube (tableOracle oStmt) u = a₀) = ∅ := by
    rw [Finset.filter_eq_empty_iff]
    intro u _ hu
    have hcard : 0 < tableMultiplicityCount oStmt a₀ := by
      unfold tableMultiplicityCount
      rw [Finset.card_pos]
      exact ⟨u, Finset.mem_filter.mpr ⟨Finset.mem_univ u, hu⟩⟩
    omega
  rw [hfiber, Finset.sum_empty, zero_sub, neg_mul, neg_eq_zero] at heval
  rcases mul_eq_zero.mp heval with hc | hprod
  · exact lookupMultiplicityCount_natCast_ne_zero stmt oStmt a₀ hlook hc
  · rw [Finset.prod_eq_zero_iff] at hprod
    obtain ⟨b, hb, hb0⟩ := hprod
    rw [Finset.mem_erase] at hb
    exact hb.1 (by linear_combination hb0)

end Logup

#print axioms Logup.clearedGrandSumPoly_ne_zero_of_bad_lookup

/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/

import ArkLib.ProofSystem.Spartan.ZeroCheckComplete

/-!
# The Spartan first sum-check virtual polynomial `ℱ` and its cube-sum identity (issue #114)

After the `firstChallenge` (`RandomQuery`) phase samples `τ : Fin ℓ_m → R` and pins the zero-check
claim `𝒢(τ) = 0`, the Spartan first sum-check reduces that claim to a single evaluation. The
sum-check runs over the **first sum-check virtual polynomial**

  `ℱ(X) = eqPolynomial(τ)(X) · (Ã(X) · B̃(X) − C̃(X))`,

where `M̃(X) = MLE((M *ᵥ 𝕫) ∘ finFunctionFinEquiv)` is the multilinear extension over `Fin ℓ_m` of
the matrix-vector product `M *ᵥ 𝕫` indexed by the row hypercube. This is the `ℱ(X)` named in the
design comment of `Basic.lean` (`ℱ(X) = eq⸨τ, X⸩ · (A⸨X⸩·B⸨X⸩ − C⸨X⸩)`).

This module establishes the two algebraic facts the first sum-check oracle reduction is built on:

* **Degree bound** (`firstSumCheckVirtualPolynomial_mem_restrictDegree`): `ℱ` has degree `≤ 3` per
  variable (`eqPolynomial` is multilinear, the product `Ã·B̃` is degree `2`, the `eq` factor adds
  `1`). This is the per-variable degree the sum-check protocol consumes, so the first sum-check uses
  `Sumcheck.Spec.oracleReduction R 3 …` — degree `3`, **not** `2` (the second sum-check's degree).

* **Cube-sum identity** (`firstSumCheckVirtualPolynomial_hypercubeSum_eq_zeroCheckEval`): the Boolean
  hypercube sum of `ℱ` equals `𝒢(τ)`, the zero-check polynomial evaluated at the sampled challenge.
  This is the completeness core of the first sum-check: it ties the sum-check's claimed sum to the
  value `𝒢(τ)` that the preceding `RandomQuery` phase pinned to `0`. On R1CS-satisfying instances
  the sum is therefore `0` (`firstSumCheckVirtualPolynomial_hypercubeSum_eq_zero_of_satisfied`).

This is the first-phase analogue of `secondSumCheckVirtualPolynomial_hypercubeSum_eq_evalClaimValue`,
and of `secondSCVP_mem_restrictDegree` for the degree bound.
-/

open MvPolynomial Matrix

namespace Spartan.Spec

variable {R : Type} [CommRing R] [IsDomain R] [Fintype R] [DecidableEq R]
    (pp : Spartan.PublicParams)

/-- The multilinear extension over the row hypercube `Fin ℓ_m` of the matrix-vector product
`M_idx *ᵥ 𝕫`, where `𝕫 = 𝕩 ‖ 𝕨` is reconstructed from the public input and witness oracle. This is
the factor `M̃(X)` of the first sum-check virtual polynomial. -/
noncomputable def matVecMLE
    (𝕩 : Statement.AfterFirstMessage R pp)
    (oStmt : ∀ i, OracleStatement.AfterFirstMessage R pp i)
    (idx : R1CS.MatrixIdx) : MvPolynomial (Fin pp.ℓ_m) R :=
  MvPolynomial.MLE
    ((Matrix.mulVec (oStmt (.inl idx)) (R1CS.𝕫 𝕩 (oStmt (.inr 0)))) ∘ finFunctionFinEquiv)

/-- **The Spartan first sum-check virtual polynomial** `ℱ(X) = eq(τ,X) · (Ã(X)·B̃(X) − C̃(X))`. The
sum-check over this polynomial reduces the zero-check claim `𝒢(τ) = 0` to a single evaluation at the
sum-check challenge `r_x`. -/
noncomputable def firstSumCheckVirtualPolynomial
    (τ : Fin pp.ℓ_m → R)
    (𝕩 : Statement.AfterFirstMessage R pp)
    (oStmt : ∀ i, OracleStatement.AfterFirstMessage R pp i) : MvPolynomial (Fin pp.ℓ_m) R :=
  eqPolynomial τ *
    (matVecMLE pp 𝕩 oStmt .A * matVecMLE pp 𝕩 oStmt .B - matVecMLE pp 𝕩 oStmt .C)

omit [IsDomain R] [Fintype R] [DecidableEq R] in
/-- Each matrix-vector factor `M̃` is multilinear (degree `≤ 1` per variable). -/
theorem matVecMLE_mem_restrictDegree
    (𝕩 : Statement.AfterFirstMessage R pp)
    (oStmt : ∀ i, OracleStatement.AfterFirstMessage R pp i) (idx : R1CS.MatrixIdx) :
    matVecMLE pp 𝕩 oStmt idx ∈ R⦃≤ 1⦄[X Fin pp.ℓ_m] :=
  MLE_mem_restrictDegree _

omit [IsDomain R] [Fintype R] in
/-- **First sum-check virtual polynomial degree bound.** `ℱ` has degree `≤ 3` per variable: the
`eqPolynomial` factor contributes `1` and the product `Ã·B̃` contributes `2`. -/
theorem firstSumCheckVirtualPolynomial_mem_restrictDegree
    (τ : Fin pp.ℓ_m → R)
    (𝕩 : Statement.AfterFirstMessage R pp)
    (oStmt : ∀ i, OracleStatement.AfterFirstMessage R pp i) :
    firstSumCheckVirtualPolynomial pp τ 𝕩 oStmt ∈ R⦃≤ 3⦄[X Fin pp.ℓ_m] := by
  classical
  rw [mem_restrictDegree_iff_degreeOf_le]
  intro j
  have hEq : degreeOf j (eqPolynomial τ : MvPolynomial (Fin pp.ℓ_m) R) ≤ 1 :=
    eqPolynomial_degreeOf τ j
  have hM : ∀ idx, degreeOf j (matVecMLE pp 𝕩 oStmt idx) ≤ 1 :=
    fun idx => (mem_restrictDegree_iff_degreeOf_le _ _).mp (matVecMLE_mem_restrictDegree pp 𝕩 oStmt idx) j
  have hAB : degreeOf j (matVecMLE pp 𝕩 oStmt .A * matVecMLE pp 𝕩 oStmt .B) ≤ 2 :=
    le_trans (degreeOf_mul_le j _ _) (Nat.add_le_add (hM .A) (hM .B))
  have hsub : degreeOf j
      (matVecMLE pp 𝕩 oStmt .A * matVecMLE pp 𝕩 oStmt .B - matVecMLE pp 𝕩 oStmt .C) ≤ 2 :=
    le_trans (degreeOf_sub_le j _ _) (max_le hAB (le_trans (hM .C) (by omega)))
  unfold firstSumCheckVirtualPolynomial
  exact le_trans (degreeOf_mul_le j _ _) (le_trans (Nat.add_le_add hEq hsub) (by omega))

omit [IsDomain R] [Fintype R] [DecidableEq R] in
/-- **First sum-check cube-sum identity (completeness core).** The Boolean-hypercube sum of the
first sum-check virtual polynomial `ℱ` equals the zero-check polynomial `𝒢` evaluated at the
`firstChallenge` point `τ`. This is the identity `∑_{X ∈ {0,1}^ℓ_m} ℱ(X) = 𝒢(τ)` that the sum-check
relies on: on the Boolean cube the multilinear factors `M̃` agree with the genuine matrix-vector
products `M *ᵥ 𝕫`, and the `eqPolynomial(τ)` weights reassemble `𝒢(τ) = eval τ 𝒢`. -/
theorem firstSumCheckVirtualPolynomial_hypercubeSum_eq_zeroCheckEval
    (τ : Fin pp.ℓ_m → R)
    (𝕩 : Statement.AfterFirstMessage R pp)
    (oStmt : ∀ i, OracleStatement.AfterFirstMessage R pp i) :
    (∑ X : Fin pp.ℓ_m → Fin 2,
        MvPolynomial.eval (fun i => ((X i : Fin 2) : R)) (firstSumCheckVirtualPolynomial pp τ 𝕩 oStmt))
      = MvPolynomial.eval τ (zeroCheckVirtualPolynomial R pp 𝕩 oStmt) := by
  classical
  -- Expand the RHS `𝒢(τ)` into the row-hypercube sum.
  rw [zeroCheckVirtualPolynomial, map_sum]
  -- Reindex the LHS cube sum (over `X : Fin ℓ_m → Fin 2`) by `finFunctionFinEquiv` onto the row
  -- index `x : Fin (2 ^ ℓ_m)` used by `𝒢`.
  refine Fintype.sum_equiv finFunctionFinEquiv _ _ ?_
  intro X
  -- Distribute `eval` over the product/difference on both sides; reduce each `M̃` and each `C` on
  -- the Boolean cube. (`x = finFunctionFinEquiv X`, so `symm x = X`.)
  simp only [firstSumCheckVirtualPolynomial, matVecMLE, map_mul, map_sub, MLE_eval_zeroOne,
    Function.comp_apply, eval_C, Equiv.symm_apply_apply]
  -- The `eq` weights match via symmetry: `eval (X:→R) (eqPolynomial τ) = eval τ (eqPolynomial X)`.
  rw [eqPolynomial_symm]

omit [IsDomain R] [Fintype R] [DecidableEq R] in
/-- **First sum-check completeness target.** On any R1CS-satisfying instance the first sum-check's
Boolean-hypercube sum is `0`: the zero-check polynomial `𝒢` is identically zero, so `𝒢(τ) = 0`. This
is the target value the honest first sum-check proves, pinned by the preceding `RandomQuery` phase. -/
theorem firstSumCheckVirtualPolynomial_hypercubeSum_eq_zero_of_satisfied
    (τ : Fin pp.ℓ_m → R)
    (𝕩 : Statement.AfterFirstMessage R pp)
    (oStmt : ∀ i, OracleStatement.AfterFirstMessage R pp i)
    (h : R1CS.relation R pp.toSizeR1CS 𝕩 (fun idx => oStmt (.inl idx)) (oStmt (.inr 0))) :
    (∑ X : Fin pp.ℓ_m → Fin 2,
        MvPolynomial.eval (fun i => ((X i : Fin 2) : R)) (firstSumCheckVirtualPolynomial pp τ 𝕩 oStmt))
      = 0 := by
  rw [firstSumCheckVirtualPolynomial_hypercubeSum_eq_zeroCheckEval pp τ 𝕩 oStmt,
    zeroCheckVirtualPolynomial_eq_zero_of_satisfied pp 𝕩 oStmt h, map_zero]

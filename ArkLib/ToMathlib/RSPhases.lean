/-
Copyright (c) 2025 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/

import ArkLib.ProofSystem.Sumcheck.Domain
import ArkLib.Data.MvPolynomial.Multilinear

/-!
# Ring-Switching phase bricks (proven, dependency-light)

This file collects small, fully-proven, `sorry`-free bricks that support the ring-switching
`BatchingPhase` / `SumcheckPhase` correctness arguments **without** importing the (heavier,
sometimes-in-flux) `Sumcheck.Spec.SingleRound` chain. They depend only on
`ArkLib.ProofSystem.Sumcheck.Domain` (the `SumcheckDomain` / `boolDomain` abstraction) and
`ArkLib.Data.MvPolynomial.Multilinear` (the `MLE` multilinear-extension API).

## What lives here

* `boolDomain_cube_eq_image` — the Boolean cube `(boolDomain R k).cube` is the image of the full
  `Fin k → Fin 2` finset under the canonical `b ↦ (j ↦ boolEmbedding R (b j))` embedding.
* `sum_boolDomain_cube` — reindex a sum over the Boolean cube as a sum over `Fin k → Fin 2`.
* `MLE_eval_boolEmbedding` — evaluating an `MLE` at a Boolean-cube point reads off the defining
  evaluation function.
* `sum_cube_MLE_mul_MLE` — **central batching-completeness brick:** the Boolean-cube sum of a
  product of two multilinear extensions `MLE A * MLE B` equals the pointwise-product sum
  `∑_{b : Fin k → Fin 2} A b * B b`. This is the `𝓑`-pinned (NOT free-`𝓑`) form of the DP24
  sumcheck-consistency right-hand side; see the statement-bug note in `BatchingPhase.lean`.

These are the named, proven leaves that the deep `compute_s0 = ∑_cube (A_MLE · t')` identity reduces
to once the row-decomposition algebra is supplied; they isolate the `SumcheckDomain`/`MLE` plumbing
from the genuinely-DP24 row-decomposition content.
-/

namespace ArkLib.RingSwitching.Phases

open MvPolynomial Finset

variable {R : Type*} [CommRing R] [Nontrivial R]

/-- The coordinatewise Boolean-cube point `j ↦ boolEmbedding R (b j)` agrees with the canonical
`Fin 2 → R` coercion `j ↦ ((b j : Fin 2) : R)` used by `MvPolynomial.MLE_eval_zeroOne`. -/
theorem boolEmbedding_apply_eq_coe (b : Fin 2) :
    (boolEmbedding R b : R) = ((b : Fin 2) : R) := by
  fin_cases b <;> simp [boolEmbedding]

/-- The Boolean hypercube embedding `(Fin k → Fin 2) ↪ (Fin k → R)`,
`b ↦ (j ↦ boolEmbedding R (b j))`, injective by `boolEmbedding`'s injectivity. -/
def boolCubeEmb (k : ℕ) : (Fin k → Fin 2) ↪ (Fin k → R) where
  toFun b := fun j => boolEmbedding R (b j)
  inj' := by
    intro a b hab; funext j; exact (boolEmbedding R).injective (congrFun hab j)

@[simp] theorem boolCubeEmb_apply (k : ℕ) (b : Fin k → Fin 2) (j : Fin k) :
    boolCubeEmb (R := R) k b j = boolEmbedding R (b j) := rfl

/-- The Boolean cube as the image of the full `Fin k → Fin 2` finset under `boolCubeEmb`. -/
theorem boolDomain_cube_eq_image (k : ℕ) :
    (boolDomain R k).cube
      = (Finset.univ : Finset (Fin k → Fin 2)).map (boolCubeEmb (R := R) k) := by
  ext x
  simp only [SumcheckDomain.mem_cube, points_boolDomain, Finset.mem_map, Finset.mem_univ,
    true_and, boolCubeEmb, Function.Embedding.coeFn_mk]
  constructor
  · intro hx
    -- each coordinate gives `∃ c, boolEmbedding c = x j`; choose witnesses into a `Fin k → Fin 2`.
    choose c hc using hx
    exact ⟨c, funext hc⟩
  · rintro ⟨b, rfl⟩ j
    exact ⟨b j, rfl⟩

/-- Reindex a sum over the Boolean cube `(boolDomain R k).cube` as a sum over `Fin k → Fin 2`. -/
theorem sum_boolDomain_cube {M : Type*} [AddCommMonoid M] (k : ℕ) (f : (Fin k → R) → M) :
    (∑ x ∈ (boolDomain R k).cube, f x)
      = ∑ b : Fin k → Fin 2, f (fun j => boolEmbedding R (b j)) := by
  rw [boolDomain_cube_eq_image, Finset.sum_map]
  rfl

/-- Evaluating an `MLE` at a Boolean-cube point reads off the defining evaluation function. -/
theorem MLE_eval_boolEmbedding {k : ℕ} (b : Fin k → Fin 2) (evals : (Fin k → Fin 2) → R) :
    MvPolynomial.eval (fun j => boolEmbedding R (b j)) (MLE evals) = evals b := by
  have hpt : (fun j => boolEmbedding R (b j)) = ((b : Fin k → Fin 2) : Fin k → R) := by
    funext j; exact boolEmbedding_apply_eq_coe (b j)
  rw [hpt]
  exact MLE_eval_zeroOne b evals

/-- **Central batching-completeness brick (pinned-`𝓑` form).** The Boolean-cube sum of a product of
two multilinear extensions `MLE A * MLE B` equals the pointwise-product sum over the Boolean
hypercube `Fin k → Fin 2`:
  `∑_{x ∈ {0,1}^k} (MLE A · MLE B)(x) = ∑_{b} A b · B b`.

This is the `𝓑`-pinned right-hand side of `sumcheckConsistencyProp` for the round-0 batching
polynomial `H = A_MLE · t'` (with `boolDomain`, NOT a free `𝓑 : Fin 2 ↪ L`). It dissolves the
"free-`𝓑` orientation" obstruction recorded in the older `BatchingPhase` WIP note: with the
canonical Boolean domain the right-hand side is concrete and well-defined; the remaining batching
content is the DP24 row-decomposition identity `∑_b A_func(b) · t'(b) = compute_s0 …`. -/
theorem sum_cube_MLE_mul_MLE {k : ℕ} (A B : (Fin k → Fin 2) → R) :
    (∑ x ∈ (boolDomain R k).cube,
        MvPolynomial.eval x (MLE A * MLE B))
      = ∑ b : Fin k → Fin 2, A b * B b := by
  rw [sum_boolDomain_cube]
  refine Finset.sum_congr rfl fun b _ => ?_
  rw [MvPolynomial.eval_mul, MLE_eval_boolEmbedding, MLE_eval_boolEmbedding]

/-- **Mixed batching-completeness brick.** Boolean-cube sum of `MLE A · p` for an *arbitrary*
multivariate polynomial `p` (e.g. the witness `t'.val`, a general multilinear poly that is not
literally written as an `MLE`): the `MLE A` factor reads off `A b`, while the `p` factor is
evaluated at the Boolean-cube point `j ↦ boolEmbedding R (b j)`. This is the precise form the
round-0 batching consistency RHS takes (`H = A_MLE · t'`), since only `A_MLE` is an `MLE`. -/
theorem sum_cube_MLE_mul {k : ℕ} (A : (Fin k → Fin 2) → R) (p : MvPolynomial (Fin k) R) :
    (∑ x ∈ (boolDomain R k).cube, MvPolynomial.eval x (MLE A * p))
      = ∑ b : Fin k → Fin 2, A b * MvPolynomial.eval (fun j => boolEmbedding R (b j)) p := by
  rw [sum_boolDomain_cube]
  refine Finset.sum_congr rfl fun b _ => ?_
  rw [MvPolynomial.eval_mul, MLE_eval_boolEmbedding]

/-! ## Named residual for batching-phase completeness

The deep DP24 batching-phase sum-check consistency reduces (via the bricks above) to the following
pointwise identity, which is the genuinely-DP24 row-decomposition content. We name it precisely so
the residual surface is a single explicit `Prop` rather than an open `sorry`.

`BatchingConsistencyResidual A tEvals s0` says: the verifier-side step-5 value `s0` equals the
Boolean-hypercube sum of `A b · tEvals b`, where `A = A_func` (`compute_A_func`, the eq-weighted
row-decomposition) and `tEvals b = eval (boolEmbedding ∘ b) t'.val` is the witness evaluated on the
cube. By `sum_cube_MLE_mul` this is *definitionally* the `sumcheckConsistencyProp` right-hand side
for `H = A_MLE · t'` over the pinned Boolean domain — so closing this residual closes the round-0
consistency conjunct of `batchingReduction_perfectCompleteness` (no free-`𝓑` obstruction; that note
was stale for the migrated `boolDomain` statement). -/
def BatchingConsistencyResidual {k : ℕ} (A : (Fin k → Fin 2) → R)
    (tEvals : (Fin k → Fin 2) → R) (s0 : R) : Prop :=
  s0 = ∑ b : Fin k → Fin 2, A b * tEvals b

/-- **Reduction:** given the named residual, the `sumcheckConsistencyProp`-shaped equation
`s0 = ∑_{x ∈ boolDomain^k} (MLE A · p).eval x` holds, where `p` is the witness polynomial whose
cube evaluations are `tEvals` (i.e. `tEvals b = eval (boolEmbedding ∘ b) p`). This is the exact
right-hand side of the round-0 batching consistency conjunct; it routes the deep content through the
single named `BatchingConsistencyResidual`. -/
theorem batchingConsistency_of_residual {k : ℕ} (A : (Fin k → Fin 2) → R)
    (p : MvPolynomial (Fin k) R) (s0 : R)
    (hres : BatchingConsistencyResidual A
      (fun b => MvPolynomial.eval (fun j => boolEmbedding R (b j)) p) s0) :
    s0 = ∑ x ∈ (boolDomain R k).cube, MvPolynomial.eval x (MLE A * p) := by
  rw [sum_cube_MLE_mul]
  exact hres

end ArkLib.RingSwitching.Phases

section AxiomAudit
open ArkLib.RingSwitching.Phases
#print axioms sum_cube_MLE_mul_MLE
#print axioms sum_cube_MLE_mul
#print axioms batchingConsistency_of_residual
#print axioms boolDomain_cube_eq_image
end AxiomAudit

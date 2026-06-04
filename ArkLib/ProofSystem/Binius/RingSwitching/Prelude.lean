/-
Copyright (c) 2025 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chung Thai Nguyen, Quang Dao
-/

import CompPoly.Fields.Binary.AdditiveNTT.AdditiveNTT
import ArkLib.Data.MvPolynomial.Multilinear
import ArkLib.OracleReduction.Basic
import ArkLib.OracleReduction.Security.RoundByRound
import CompPoly.Fields.Binary.Tower.TensorAlgebra
import ArkLib.ProofSystem.Binius.BinaryBasefold.Basic
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Matrix.Basic

/-!
# Ring-Switching IOP Prelude

This module contains the core definitions and infrastructure for the ring-switching IOP,
including tensor algebra operations, field extension handling, and basic protocol types.

## Main Components

1. **Tensor Algebra operations**: Operations for handling tensor products
between small field K and large field L, including embeddings `φ₀ : L → L ⊗[K] L`,
`φ₁ : L → L ⊗[K] L`, and row/column decompositions with respect to a `K`-basis `β`.
2. **Protocol Types**: Statement and witness types for each phase
3. **Security Definitions**: Relations & Kstate for security analysis
-/

noncomputable section

namespace Binius.RingSwitching
open Binius.BinaryBasefold

open OracleSpec OracleComp ProtocolSpec Finset AdditiveNTT Polynomial MvPolynomial TensorProduct
open scoped NNReal

/- This section defines generic preliminaries for the ring-switching protocol. -/
section Preliminaries

variable (κ : ℕ) [NeZero κ]
variable (L : Type) [Field L] [Fintype L] [DecidableEq L] [CharP L 2]
variable (K : Type) [Field K] [Fintype K] [DecidableEq K]
variable [Algebra K L]
variable (ℓ ℓ' : ℕ) [NeZero ℓ] [NeZero ℓ']
variable (h_l : ℓ = ℓ' + κ)

section TensorAlgebraOps
/-!
## Enhanced Tensor Algebra Operations

Additional tensor algebra operations for the enhanced protocol specification.
Based on the tensor algebra theory from Section 2.1.
-/

/-- Tensor Algebra A = L ⊗_K L. Based on the spec,
it's viewed as (2^κ)x(2^κ) arrays of K-elements.
The imported TensorAlgebra file provides the leftAlgebra instances. -/
abbrev TensorAlgebra (K L : Type*) [Field K] [Field L] [Algebra K L] := L ⊗[K] L

/--
Column embedding φ₀: L → A as a ring homomorphism.
φ₀(α) = α ⊗ 1, operates on columns.
-/
def φ₀ (L K : Type*) [Field K] [Field L] [Algebra K L] : L →+* TensorAlgebra K L where
  toFun α := α ⊗ₜ[K] (1 : L)
  map_one' := rfl
  map_mul' α β := by simp only [Algebra.TensorProduct.tmul_mul_tmul, mul_one]
  map_zero' := by simp only [zero_tmul]
  map_add' α β := by simp only [add_tmul]

/--
Row embedding φ₁: L → A as a ring homomorphism.
φ₁(α) = 1 ⊗ α, operates on rows.
-/
def φ₁ (L K : Type*) [Field K] [Field L] [Algebra K L] : L →+* TensorAlgebra K L where
  toFun α := (1 : L) ⊗ₜ[K] α
  map_one' := by rfl
  map_mul' α β := by
    simp only [Algebra.TensorProduct.tmul_mul_tmul, mul_one]
  map_zero' := by simp only [tmul_zero]
  map_add' α β := by simp only [tmul_add]

open Module
/-- Decompose `ŝ` into row components `(ŝ =: Σ_{u ∈ {0,1}^κ} β_u ⊗ ŝ_u)`.
This views `L ⊗ L` as a module over `L` (left action)
and finds the coordinates of `ŝ` with respect to the basis lifted from `β`. -/
def decompose_tensor_algebra_rows {σ : Type*} (β : Basis σ K L)
  (s_hat : TensorAlgebra K L) : σ → L :=
  fun u =>
    (β.baseChange L).repr s_hat u

/-- Decompose `ŝ` into column components `(ŝ =: Σ_{v ∈ {0,1}^κ} ŝ_v ⊗ β_v)`.
This views `L ⊗ L` as a module over `L` (right action)
and finds the coordinates of `ŝ` with respect to the basis lifted from `β`. -/
def decompose_tensor_algebra_columns {σ : Type*} (β : Basis σ K L) (s_hat : L ⊗[K] L) : σ → L :=
  fun v => by
    let b := Basis.baseChangeRight (b:=β) (Right:=L)
    letI rightAlgebra : Algebra L (L ⊗[K] L) := by
      exact Algebra.TensorProduct.rightAlgebra
    letI rightModule : Module L (L ⊗[K] L) := rightAlgebra.toModule
    exact b.repr s_hat v
/--
**Definition 2.1 (MLE packing)**.
Packs a small-field multilinear `t` into a large-field multilinear `t'` by
reinterpreting chunks of `2^κ` coefficients as single `L`-elements.
For each `w ∈ {0,1}^ℓ'`, the evaluation `t'(w)` is defined as:
`t'(w) := ∑_{v ∈ {0,1}^κ} t(v₀, ..., v_{κ-1}, w₀, ..., w_{ℓ'-1}) ⋅ β_v`
-/
def packMLE (β : Basis (Fin κ → Fin 2) K L) (t : MultilinearPoly K ℓ) :
    MultilinearPoly L ℓ' :=
  -- 1. Define the function that gives the evaluations of t' on the boolean hypercube.
  let packing_func (w : Fin ℓ' → Fin 2) : L :=
    -- a. Define a function that computes the K-coefficients for a given `w`.
    let coeffs_for_w (v : Fin κ → Fin 2) : K :=
      -- Construct the full evaluation point `(v, w)` of length `ℓ`.
      let concatenated_point (i : Fin ℓ) : Fin 2 :=
        if h : i.val < κ then
          v ⟨i.val, h⟩
        else
          w ⟨i.val - κ, by omega⟩
      -- Evaluate the small-field polynomial `t` at this point.
      MvPolynomial.eval (fun i => ↑(concatenated_point i)) t.val

    -- b. Use `equivFun.symm` = ∑ v, (coeffs_for_w v) • (β v).
    β.equivFun.symm coeffs_for_w

  -- 2. The packed polynomial `t'` is the multilinear extension of this function.
  ⟨MvPolynomial.MLE packing_func, MLE_mem_restrictDegree packing_func⟩

/--
**Unpacking a Packed Multilinear Polynomial**.
Reverses the packing defined in `packMLE`. It reconstructs the small-field
multilinear `t` from the large-field multilinear `t'`.

The evaluation of `t` at a point `(v, w)` is recovered by taking the evaluation
of `t'` at `w`, which is an element of `L`, and finding its `v`-th coordinate
with respect to the basis `β`.
-/
def unpackMLE (β : Basis (Fin κ → Fin 2) K L) (t' : MultilinearPoly L ℓ') :
    MultilinearPoly K ℓ :=
  -- 1. Define the function that gives the evaluations of the original small-field polynomial `t`.
  let unpacked_evals (p : Fin ℓ → Fin 2) : K :=
    -- a. Deconstruct the evaluation point `p` into `v` (first κ bits) and `w` (last ℓ' bits).
    let v (i : Fin κ) : Fin 2 := p ⟨i.val, by omega⟩
    let w (i : Fin ℓ') : Fin 2 := p ⟨i.val + κ, by { rw [h_l]; omega }⟩

    -- b. Evaluate the large-field polynomial `t'` at the point `w`.
    let t'_eval_at_w : L := MvPolynomial.eval (fun i => ↑(w i)) t'.val

    -- c. Get the K-coefficients of this L-element with respect to the basis `β`.
    -- `β.repr/β.equivFun` maps an element of L to its coordinate function `(Fin κ → Fin 2) → K`.
    let coeffs : (Fin κ → Fin 2) → K := β.repr t'_eval_at_w
    -- d. The desired evaluation t(p) = t(v,w)
      -- is the coefficient corresponding to the basis vector `β_v`.
    coeffs v

  -- 2. The unpacked polynomial `t` is the multilinear extension of this evaluation function.
  ⟨MvPolynomial.MLE unpacked_evals, MLE_mem_restrictDegree unpacked_evals⟩

/--
**Component-wise `φ₁` embedding**.
Takes a polynomial `t'` with coefficients in `L` and embeds it into a polynomial
with coefficients in the tensor algebra `A` by applying `φ₁` to each coefficient.
This is achieved by using `MvPolynomial.map`.
-/
def componentWise_φ₁_embed_MLE (t' : MultilinearPoly L ℓ') :
    MultilinearPoly (TensorAlgebra K L) ℓ' :=
  ⟨MvPolynomial.map (R:=L) (S₁ := TensorAlgebra K L) (f:=φ₁ L K) (t'.val), by
    rw [MvPolynomial.mem_restrictDegree_iff_degreeOf_le]
    intro i -- for any specific variable Xᵢ,
      -- we prove its max individual degree is at most 1 in ANY monomial terms
    calc
      MvPolynomial.degreeOf i (MvPolynomial.map (φ₁ L K) t'.val)
      _ ≤ MvPolynomial.degreeOf i t'.val := by
        refine degreeOf_le_iff.mpr ?_
        intro m hm_support_mapped_t' -- consider any specific monomial term
        have hm_in_support_t' : m ∈ t'.val.support := by
          apply MvPolynomial.support_map_subset (f:=φ₁ L K)
          exact hm_support_mapped_t'
        exact monomial_le_degreeOf i hm_in_support_t'
      _ ≤ 1 := by
        have h_og_t' := t'.property
        simp only [MvPolynomial.mem_restrictDegree_iff_degreeOf_le] at h_og_t'
        exact h_og_t' i
  ⟩

end TensorAlgebraOps

section ProtocolTypes
/-!
## Enhanced Protocol Type Definitions (Interfaces between phases)

We define the Statement and Witness types at the boundaries of each phase
following the enhanced specification.
-/

-- Initial Input (Input to Batching Phase)
abbrev MLPEvalStatement :=
  Binius.BinaryBasefold.InitialStatement (L := L) (ℓ := ℓ)

structure WitMLP where
  t : MultilinearPoly K ℓ

structure BatchingWitIn where
  t : MultilinearPoly K ℓ
  t' : MultilinearPoly L ℓ'

structure BatchingStmtIn where
  t_eval_point : Fin ℓ → L         -- r = (r_0, ..., r_{ℓ-1}) => shared input
  original_claim : L               -- s = t(r) => the original claim to verify

structure RingSwitchingBaseContext extends (SumcheckBaseContext L ℓ) where
  -- context from batching phase
  s_hat : TensorAlgebra K L  -- ŝ
  r_batching : Fin κ → L     -- r''

structure SumcheckWitness (i : Fin (ℓ' + 1)) where
  t' : MultilinearPoly L ℓ' -- the packed polynomial
  -- `h(X_0, ..., X_{ℓ'-1}) := A(X_0, ..., X_{ℓ'-1}) ⋅ t'(X_0, ..., X_{ℓ'-1})`
  H : L⦃≤ 2⦄[X Fin (ℓ' - i)]

section MLIOPCS
-- Define the specific Stmt/Wit types Π' expects.
structure MLIOPCSStmt where
  point : Fin ℓ' → L
  evaluation : L

/-- Standard input relation for MLIOPCS: polynomial evaluation at point equals claimed evaluation -/
def MLPEvalRelation (ιₛᵢ : Type) (OStmtIn : ιₛᵢ → Type)
    (input : ((MLPEvalStatement L ℓ') × (∀ j, OStmtIn j)) × (WitMLP L ℓ')) : Prop :=
  let ⟨⟨stmt, _⟩, wit⟩ := input
  stmt.original_claim = wit.t.val.eval stmt.t_eval_point

structure AbstractOStmtIn where
  ιₛᵢ : Type
  OStmtIn : ιₛᵢ → Type
  Oₛᵢ : ∀ i, OracleInterface (OStmtIn i)
  -- The abstract initial compatibility relation, which along with
  -- MLPEvalRelation, forms the initial input relation for the MLIOPCS.
  initialCompatibility : (MultilinearPoly L ℓ') × (∀ j, OStmtIn j) → Prop

def AbstractOStmtIn.toRelInput (aOStmtIn : AbstractOStmtIn L ℓ') :
  Set (((MLPEvalStatement L ℓ') × (∀ j, aOStmtIn.OStmtIn j)) × (WitMLP L ℓ')) :=
  {input |
    MLPEvalRelation L ℓ' aOStmtIn.ιₛᵢ aOStmtIn.OStmtIn input
    ∧ aOStmtIn.initialCompatibility ⟨input.2.t, input.1.2⟩}

structure MLIOPCS extends (AbstractOStmtIn L ℓ') where
  /-- Protocol specification -/
  numRounds : ℕ
  pSpec : ProtocolSpec numRounds
  Oₘ: ∀ j, OracleInterface (pSpec.Message j)
  O_challenges: ∀ (i : pSpec.ChallengeIdx), SampleableType (pSpec.Challenge i)
  -- /-- The evaluation protocol Π' as an OracleReduction -/
  oracleReduction : OracleReduction (oSpec:=[]ₒ)
    (StmtIn := MLPEvalStatement L ℓ') (OStmtIn:= OStmtIn)
    (StmtOut := Bool) (OStmtOut := fun _: Empty => Unit)
    (WitIn := WitMLP L ℓ') (WitOut := Unit)
    (pSpec := pSpec)
  -- Security properties
  perfectCompleteness : ∀ {σ : Type} {init : ProbComp σ} {impl : QueryImpl []ₒ (StateT σ ProbComp)},
    OracleReduction.perfectCompleteness (oSpec:=[]ₒ)
      (StmtIn:=MLPEvalStatement L ℓ') (OStmtIn:=OStmtIn)
      (StmtOut:=Bool) (OStmtOut:=fun _: Empty => Unit)
      (WitIn:=WitMLP L ℓ') (WitOut:=Unit) (pSpec:=pSpec) (init:=init) (impl:=impl)
      (relIn := toAbstractOStmtIn.toRelInput)
      (relOut := acceptRejectOracleRel)
      (oracleReduction := oracleReduction)
  -- RBR knowledge error function for the MLIOPCS
  rbrKnowledgeError : pSpec.ChallengeIdx → ℝ≥0
  -- RBR knowledge soundness property
  rbrKnowledgeSoundness : ∀ {σ : Type} {init : ProbComp σ} {impl : QueryImpl []ₒ (StateT σ ProbComp)
  },
    OracleVerifier.rbrKnowledgeSoundness
      (verifier := oracleReduction.verifier)
      (init := init)
      (impl := impl)
      (relIn := toAbstractOStmtIn.toRelInput)
      (relOut := acceptRejectOracleRel)
      (rbrKnowledgeError := rbrKnowledgeError)

end MLIOPCS

section OStmt
variable (aOStmtIn : AbstractOStmtIn L ℓ')

instance instOstmtMLIOPCS : ∀ (i : aOStmtIn.ιₛᵢ), OracleInterface (aOStmtIn.OStmtIn i) :=
  fun i => aOStmtIn.Oₛᵢ i

end OStmt

end ProtocolTypes
end Preliminaries

/- This section defines the specific relations for the ring-switching protocol, whereas
the basis of L over K has rank `2^κ` instead of `κ` as in the Preliminaries section.
-/
section Relations
open Module Binius.BinaryBasefold

variable (κ : ℕ) [NeZero κ]
variable (L : Type) [Field L] [Fintype L] [DecidableEq L] [CharP L 2]
  [SampleableType L]
variable (K : Type) [Field K] [Fintype K] [DecidableEq K]
variable [Algebra K L]
variable (β : Basis (Fin κ → Fin 2) K L)
variable (ℓ ℓ' : ℕ) [NeZero ℓ] [NeZero ℓ']
variable (h_l : ℓ = ℓ' + κ)
variable {𝓑 : Fin 2 ↪ L}

/-- Compute the tensor value ŝ := φ₁(t')(φ₀(r_κ), ..., φ₀(r_{ℓ-1})) -/
def embedded_MLP_eval (t' : MultilinearPoly L ℓ') (r : Fin ℓ → L) :
  TensorAlgebra K L :=
  -- This implements the identity:
  -- ŝ = Σ_{w ∈ {0,1}^ℓ'} eq̃(r_suffix, w) ⊗ t'(w)
  let r_suffix : Fin ℓ' → L :=
    fun i => r ⟨i.val + κ, by { rw [h_l]; omega }⟩
  let φ₁_mapped_t': MultilinearPoly (TensorAlgebra K L) ℓ' := componentWise_φ₁_embed_MLE L K ℓ' t'
  let φ₀_mapped_r: Fin ℓ' → (TensorAlgebra K L) := fun i => φ₀ L K (r_suffix i)
  φ₁_mapped_t'.val.eval φ₀_mapped_r

/-- Step 2 (V): Check 1: s ?= Σ_{v ∈ {0,1}^κ} eqTilde(v, r_{0..κ-1}) ⋅ ŝ_v.

Note (soundness fix): the decomposition here must read the **row** components of `ŝ`
(`decompose_tensor_algebra_rows`), which carry the `φ₁`/`t'` tensor factor: by
`decompose_rows_packMLE`, `(rows ŝ)_u = Σ_w t(u,w)·eq̃(w, r_suffix)`, so the
`eq̃(·, r_prefix)`-weighted sum reconstructs `t(r)`. The previous version used
`decompose_tensor_algebra_columns`, which extracts the `φ₀`/`eq` factor instead
(`(columns (a ⊗ b))_v = β.repr a v • b`); with it the check does **not** imply
`s = t(r)` (failing term at `κ = 1`, `t(0,w) = 1`, `t(1,w) = 0`). -/
def performCheckOriginalEvaluation (s : L) (r : Fin ℓ → L) (s_hat : TensorAlgebra K L) : Bool :=
  let r_prefix : Fin κ → L := fun i => r ⟨i.val, by omega⟩
  let check_sum := Finset.sum Finset.univ fun (v : Fin κ → Fin 2) =>
    let v_as_L : Fin κ → L := fun i => if (v i == 1) then 1 else 0
    (eqTilde v_as_L r_prefix) * (decompose_tensor_algebra_rows (L:=L)
      (K:=K) (β:=β) s_hat v)
  decide (s = check_sum)

/-- Step 4a: For each `w ∈ {0,1}^{ℓ'}`, P decompose `eq̃(r_κ, ..., r_{ℓ-1}, w_0, ..., w_{ℓ'-1})`
`=: Σ_{u ∈ {0,1}^κ} A_{w, u} ⋅ β_u`.
P define the function
`A: w ↦ Σ_{u ∈ {0,1}^κ} eq̃(u_0, ..., u_{κ-1}, r''_0, ..., r''_{κ-1}) ⋅ A_{w, u}`
on `{0,1}^{ℓ'}`.
-/
def compute_A_func (original_r_eval_suffix : Fin ℓ' → L)
    (r''_batching : Fin κ → L) : ((Fin (ℓ') → (Fin 2)) → L) :=
  fun w =>
    -- Decompose eq̃(r_suffix, w) into K-basis coefficients A_{w,u}
    let w_as_L : Fin ℓ' → L := fun i => if w i == 1 then 1 else 0
    -- `eq̃(r_κ, ..., r_{ℓ-1}, w_0, ..., w_{ℓ'-1})`
    let eq_w: L := eqTilde original_r_eval_suffix w_as_L
    let coords_A_w_u: (Fin κ → Fin 2) →₀ K := β.repr eq_w
    -- Compute A(w) = Σ_{u ∈ {0,1}^κ} eq̃(u, r'') ⋅ A_{w,u}
    Finset.sum Finset.univ fun (u : Fin κ → Fin 2) =>
      let A_w_u : K := coords_A_w_u u
      let u_as_L : Fin κ → L := fun i => if u i == 1 then 1 else 0
      -- `eq̃(u_0, ..., u_{κ-1}, r''_0, ..., r''_{κ-1}) ⋅ A_{w, u}`
      let eq_u_r_batching : L := eqTilde u_as_L r''_batching
      A_w_u • eq_u_r_batching

/-- Step 4b: P writes `A(X_0, ..., X_{ℓ'-1})` for its multilinear extension of `A_func`. -/
def compute_A_MLE
  (original_r_eval_suffix : Fin ℓ' → L) (r''_batching : Fin κ → L) :
  MultilinearPoly L ℓ' :=
  let A_func := compute_A_func κ L K β ℓ' original_r_eval_suffix r''_batching
  let A_MLE: MultilinearPoly L ℓ' := ⟨MvPolynomial.MLE A_func, MLE_mem_restrictDegree A_func⟩
  A_MLE

def getEvaluationPointSuffix (r : Fin ℓ → L) : Fin ℓ' → L :=
  fun i => r ⟨i.val + κ, by { rw [h_l]; omega }⟩

/-- Ring-Switching multiplier parameter for sumcheck, using `A_MLE` as the multiplier. -/
def RingSwitching_SumcheckMultParam :
  SumcheckMultiplierParam L ℓ' (RingSwitchingBaseContext κ L K ℓ) :=
{ multpoly := fun ctx => -- This is supposed to be (r_κ, …, r_{ℓ-1})
    compute_A_MLE κ L K β ℓ' (original_r_eval_suffix :=
      getEvaluationPointSuffix κ L ℓ ℓ' h_l (r := ctx.t_eval_point))
      (r''_batching := ctx.r_batching)
}

/-- Step 5 (V): Compute `s₀ := Σ_{u ∈ {0,1}^κ} eqTilde(u, r'') ⋅ ŝ_u`,
where ŝ_u is the row components of ŝ. -/
def compute_s0 (s_hat : TensorAlgebra K L) (r''_batching : Fin κ → L) : L :=
  Finset.sum Finset.univ fun (u : Fin κ → Fin 2) =>
    let u_as_L : Fin κ → L := fun i => if (u i == 1) then 1 else 0
    (eqTilde u_as_L r''_batching)
      * (decompose_tensor_algebra_rows (L:=L) (K:=K) (β:=β) s_hat u)

/-- Compute the tensor `e := eq̃(φ₀(r_κ), ..., φ₀(r_{ℓ-1}), φ₁(r'_0), ..., φ₁(r'_{ℓ'-1}))` -/
def compute_final_eq_tensor (r : Fin ℓ → L) (r' : Fin ℓ' → L) : TensorAlgebra K L :=
  let φ₀_mapped_r_suffix : Fin ℓ' → TensorAlgebra K L := fun i =>
    φ₀ L K (r ⟨i.val + κ, by { rw [h_l]; omega }⟩)
  let φ₁_mapped_r': Fin ℓ' → (TensorAlgebra K L) := fun i => φ₁ L K (r' i)
  eqTilde φ₀_mapped_r_suffix φ₁_mapped_r'

/-- Decompose the final eq tensor `e := Σ_{u ∈ {0,1}^κ} eq̃(u, r'') ⨂ e_u`,
where e_u is the row components of e.
Then compute `Σ_{u ∈ {0,1}^κ} eq̃(u_0, ..., u_{κ-1}, r''_0, ..., r''_{κ-1}) ⋅ e_u`.
-/
def compute_final_eq_value (r_eval : Fin ℓ → L)
    (r'_challenges : Fin ℓ' → L) (r''_batching : Fin κ → L) : L :=
  let e_tensor := compute_final_eq_tensor κ L K ℓ ℓ' h_l r_eval r'_challenges
  let e_u : (Fin κ → Fin 2) → L := decompose_tensor_algebra_rows (L:=L) (K:=K) (β:=β) e_tensor
  Finset.sum Finset.univ fun (u : Fin κ → Fin 2) =>
    let u_as_L : Fin κ → L := fun i => if u i == 1 then 1 else 0
    let eq_u_r_batching : L := -- `eq̃(u_0, ..., u_{κ-1}, r''_0, ..., r''_{κ-1})`
      eqTilde u_as_L r''_batching
    eq_u_r_batching * (e_u u)

/-- This condition ensures that the witness polynomial `H` has the
correct structure `A(...) * t'(...)` -/
def witnessStructuralInvariant {i : Fin (ℓ' + 1)}
    (stmt : Statement (L := L) (RingSwitchingBaseContext κ L K ℓ) i)
    (wit : SumcheckWitness L ℓ' i) : Prop :=
  wit.H = projectToMidSumcheckPoly (L := L) (ℓ := ℓ') (t := wit.t') (m :=
    (RingSwitching_SumcheckMultParam κ L K β ℓ ℓ' h_l).multpoly stmt.ctx)
    (i := i) (challenges := stmt.challenges)

def masterKStateProp (aOStmtIn : AbstractOStmtIn L ℓ') (stmtIdx : Fin (ℓ' + 1))
    (stmt : Statement (L := L) (RingSwitchingBaseContext κ L K ℓ) stmtIdx)
    (oStmt : ∀ j, aOStmtIn.OStmtIn j)
    (wit : SumcheckWitness L ℓ' stmtIdx)
    (localChecks : Prop := True) : Prop :=
  localChecks
  ∧ witnessStructuralInvariant κ L K β ℓ ℓ' h_l stmt wit
  ∧ sumcheckConsistencyProp (𝓑:=𝓑) stmt.sumcheck_target wit.H
  ∧ aOStmtIn.initialCompatibility ⟨wit.t', oStmt⟩

def sumcheckRoundRelationProp (aOStmtIn : AbstractOStmtIn L ℓ') (i : Fin (ℓ' + 1))
    (stmt : Statement (L := L) (RingSwitchingBaseContext κ L K ℓ) i)
    (oStmt : ∀ j, aOStmtIn.OStmtIn j)
    (wit : SumcheckWitness L ℓ' i) : Prop :=
  masterKStateProp κ L K β ℓ ℓ' h_l (𝓑:=𝓑) aOStmtIn i stmt oStmt wit

/-- Input relation for single round: proper sumcheck statement -/
def sumcheckRoundRelation (aOStmtIn : AbstractOStmtIn L ℓ') (i : Fin (ℓ' + 1)) :
  Set (((Statement (L := L) (RingSwitchingBaseContext κ L K ℓ) i) ×
    (∀ j, aOStmtIn.OStmtIn j)) × SumcheckWitness L ℓ' i) :=
  { ((stmt, oStmt), wit) | sumcheckRoundRelationProp κ L K β ℓ ℓ' h_l (𝓑:=𝓑)
    aOStmtIn i stmt oStmt wit }

end Relations

/-! ## DP24 Ring-Switching Algebra Layer

This sub-section develops the algebraic identities underlying the Diamond–Posen 2024
ring-switching packing/decomposition, following the dual-view tensor-algebra theory.

The key facts are:
* `embedded_MLP_eval_eq_sum` : the prover's tensor `ŝ = φ₁(t')(φ₀(r_suffix))` expands as
  `ŝ = Σ_{w ∈ {0,1}^ℓ'} φ₀(eq̃(w, r_suffix)) · φ₁(t'(w))`, i.e. the documented
  `Σ_w eq̃(r_suffix, w) ⊗ t'(w)`. The `eq`-factor lands entirely in the column embedding
  `φ₀` because `φ₀` and `φ₁` agree on the Boolean literals `{0,1} ⊆ image(algebraMap K L)`.
* `decompose_rows_packMLE` : the *row* components of `ŝ` recover the suffix-`eq`-weighted
  evaluations of `t`: for each `u ∈ {0,1}^κ`,
  `(decompose_rows ŝ)_u = Σ_{w ∈ {0,1}^ℓ'} t(u, w) · eq̃(w, r_suffix)`.
  This is the load-bearing identity for reconstructing `t(r)`.

NOTE (definition mismatch surfaced by this layer): the recovery of `t(r)` from `ŝ`
weights the components that carry the `t`-evaluations (`decompose_rows`, which represents
the *right* `φ₁`/`t'` tensor factor). The verifier step `performCheckOriginalEvaluation`
instead applies `decompose_tensor_algebra_columns`, which represents the *left* `φ₀`/`eq`
tensor factor (`decompose_columns (a ⊗ b) v = β.repr a v • b`). Hence
`performCheckOriginalEvaluation … = (original_claim = t(r))` does NOT hold for the
`columns` decomposition; the true identity requires `decompose_rows`. See the module
report for the explicit failing term.
-/
section RingSwitchingAlgebra
open Module Binius.BinaryBasefold

variable {κ₀ : ℕ} [NeZero κ₀]
variable {L₀ : Type} [Field L₀] [Fintype L₀] [DecidableEq L₀] [CharP L₀ 2]
variable {K₀ : Type} [Field K₀] [Fintype K₀] [DecidableEq K₀]
variable [Algebra K₀ L₀]

omit [Fintype L₀] [DecidableEq L₀] [CharP L₀ 2] [Fintype K₀] [DecidableEq K₀] in
/-- A single `eqPolynomial` factor, evaluated through the mixed embedding
`eval₂ φ₁ (φ₀ ∘ g)` at a Boolean coefficient, collapses to the column embedding `φ₀`,
because `φ₀` and `φ₁` agree on the Boolean literals `{0, 1}`. -/
private lemma singleEq_collapse {ℓ_suf : ℕ} (g : Fin ℓ_suf → L₀) (w : Fin ℓ_suf → Fin 2)
    (i : Fin ℓ_suf) :
    MvPolynomial.eval₂ (φ₁ L₀ K₀) (fun j => φ₀ L₀ K₀ (g j))
      (singleEqPolynomial ((if w i == 1 then (1 : L₀) else 0)) (X i))
    = φ₀ L₀ K₀ (eval g (singleEqPolynomial ((if w i == 1 then (1 : L₀) else 0)) (X i))) := by
  unfold singleEqPolynomial
  rcases Fin.exists_fin_two.mp ⟨w i, rfl⟩ with h | h <;> rw [h] <;>
    simp only [Fin.isValue, beq_iff_eq, reduceIte, zero_ne_one,
      MvPolynomial.eval₂_add, MvPolynomial.eval₂_mul, MvPolynomial.eval₂_sub,
      MvPolynomial.eval₂_one, MvPolynomial.eval₂_X,
      MvPolynomial.eval_add, MvPolynomial.eval_mul, MvPolynomial.eval_sub, MvPolynomial.eval_X,
      map_add, map_mul, map_sub, map_one, map_zero, sub_zero, mul_zero, zero_mul, add_zero,
      one_mul, mul_one]

omit [Fintype L₀] [DecidableEq L₀] [CharP L₀ 2] [Fintype K₀] [DecidableEq K₀] in
/-- The full `eqPolynomial` collapses through the mixed embedding to `φ₀` of its
ordinary evaluation, by multiplying the `singleEq_collapse` factors. -/
private lemma eqPoly_collapse {ℓ_suf : ℕ} (g : Fin ℓ_suf → L₀) (w : Fin ℓ_suf → Fin 2) :
    MvPolynomial.eval₂ (φ₁ L₀ K₀) (fun j => φ₀ L₀ K₀ (g j))
      (eqPolynomial (fun i => (if w i == 1 then (1 : L₀) else 0)))
    = φ₀ L₀ K₀ (eval g (eqPolynomial (fun i => (if w i == 1 then (1 : L₀) else 0)))) := by
  unfold eqPolynomial
  rw [← MvPolynomial.coe_eval₂Hom, map_prod, MvPolynomial.eval_prod, map_prod]
  apply Finset.prod_congr rfl
  intro i _
  rw [MvPolynomial.coe_eval₂Hom]
  exact singleEq_collapse g w i

omit [Fintype K₀] [DecidableEq K₀] in
/-- **DP24 packing expansion.** The prover's tensor
`ŝ := φ₁(t')(φ₀(r_κ), …, φ₀(r_{ℓ-1}))` expands over the suffix hypercube as
`ŝ = Σ_{w ∈ {0,1}^ℓ'} φ₀(eq̃(w, r_suffix)) · φ₁(t'(w))`, i.e. `Σ_w eq̃(r_suffix, w) ⊗ t'(w)`. -/
lemma embedded_MLP_eval_eq_sum (ℓ ℓ' : ℕ) [NeZero ℓ] [NeZero ℓ'] (h_l : ℓ = ℓ' + κ₀)
    (t' : MultilinearPoly L₀ ℓ') (r : Fin ℓ → L₀) :
    embedded_MLP_eval κ₀ L₀ K₀ ℓ ℓ' h_l t' r =
      ∑ w : Fin ℓ' → Fin 2,
        (φ₀ L₀ K₀ (eqTilde (fun i => (if w i == 1 then (1 : L₀) else 0))
            (getEvaluationPointSuffix κ₀ L₀ ℓ ℓ' h_l r)))
          * (φ₁ L₀ K₀ (eval (fun i => (if w i == 1 then (1 : L₀) else 0)) t'.val)) := by
  unfold embedded_MLP_eval componentWise_φ₁_embed_MLE getEvaluationPointSuffix
  simp only []
  rw [← MvPolynomial.eval₂_eq_eval_map]
  conv_lhs => rw [← MvPolynomial.is_multilinear_iff_eq_evals_zeroOne.mp t'.property]
  unfold MvPolynomial.MLE
  rw [← MvPolynomial.coe_eval₂Hom, map_sum]
  apply Finset.sum_congr rfl
  intro w _
  rw [map_mul, MvPolynomial.coe_eval₂Hom, MvPolynomial.eval₂_C]
  congr 1
  · have hcoe : (fun i => ((w i : Fin 2) : L₀))
        = (fun i => (if w i == 1 then (1 : L₀) else 0)) := by
      funext i; rcases Fin.exists_fin_two.mp ⟨w i, rfl⟩ with h | h <;> rw [h] <;> simp
    rw [hcoe]
    exact eqPoly_collapse (fun i => r ⟨i.val + κ₀, by rw [h_l]; omega⟩) w
  · unfold MvPolynomial.toEvalsZeroOne
    have hpt : (fun i => ((w i : Fin 2) : L₀)) = (fun i => (if w i == 1 then (1 : L₀) else 0)) := by
      funext i; rcases Fin.exists_fin_two.mp ⟨w i, rfl⟩ with h | h <;> rw [h] <;> simp
    rw [show ((w : Fin ℓ' → L₀)) = (fun i => ((w i : Fin 2) : L₀)) from rfl, hpt]

omit [Fintype L₀] [DecidableEq L₀] [CharP L₀ 2] [Fintype K₀] [DecidableEq K₀] in
/-- `decompose_tensor_algebra_rows` is additive over finite sums of tensors. -/
lemma decompose_rows_sum {ι : Type} [Fintype ι] (β : Basis (Fin κ₀ → Fin 2) K₀ L₀)
    (f : ι → TensorAlgebra K₀ L₀) (u : Fin κ₀ → Fin 2) :
    decompose_tensor_algebra_rows (L := L₀) (K := K₀) (β := β) (∑ i, f i) u
      = ∑ i, decompose_tensor_algebra_rows (L := L₀) (K := K₀) (β := β) (f i) u := by
  unfold decompose_tensor_algebra_rows
  rw [map_sum, Finset.sum_apply']

omit [Fintype L₀] [DecidableEq L₀] [CharP L₀ 2] [Fintype K₀] [DecidableEq K₀] in
/-- Row decomposition of a separated tensor `φ₀(a) · φ₁(b) = a ⊗ b`:
the `u`-th row component represents the *right* (`φ₁`) factor `b`, scaled by `a`. -/
lemma decompose_rows_φ₀φ₁ (β : Basis (Fin κ₀ → Fin 2) K₀ L₀) (a b : L₀) (u : Fin κ₀ → Fin 2) :
    decompose_tensor_algebra_rows (L := L₀) (K := K₀) (β := β) (φ₀ L₀ K₀ a * φ₁ L₀ K₀ b) u
      = (β.repr b) u • a := by
  have h : φ₀ L₀ K₀ a * φ₁ L₀ K₀ b = a ⊗ₜ[K₀] b := by
    simp only [φ₀, φ₁, RingHom.coe_mk, MonoidHom.coe_mk, OneHom.coe_mk,
      Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul]
  rw [h]
  unfold decompose_tensor_algebra_rows
  rw [Basis.baseChange_repr_tmul]

omit [Fintype L₀] [DecidableEq L₀] [CharP L₀ 2] in
/-- The basis coordinate of a packed evaluation recovers the small-field coefficient:
`β.repr (t'(w)) u = t(u, w)`, where `t' = packMLE β t`. -/
lemma packMLE_repr_eval (ℓ ℓ' : ℕ) [NeZero ℓ] [NeZero ℓ'] (h_l : ℓ = ℓ' + κ₀)
    (β : Basis (Fin κ₀ → Fin 2) K₀ L₀) (t : MultilinearPoly K₀ ℓ) (w : Fin ℓ' → Fin 2)
    (u : Fin κ₀ → Fin 2) :
    (β.repr (eval (fun i => (if w i == 1 then (1 : L₀) else 0))
        (packMLE κ₀ L₀ K₀ ℓ ℓ' h_l β t).val)) u
      = MvPolynomial.eval (fun i =>
          ((if h : i.val < κ₀ then u ⟨i.val, h⟩ else w ⟨i.val - κ₀, by omega⟩ : Fin 2) : K₀))
          t.val := by
  unfold packMLE
  simp only []
  rw [show (fun i => (if w i == 1 then (1 : L₀) else 0)) = ((w : Fin ℓ' → Fin 2) : Fin ℓ' → L₀)
      from ?_]
  · rw [MvPolynomial.MLE_eval_zeroOne, ← Basis.equivFun_apply, LinearEquiv.apply_symm_apply]
  · funext i; rcases Fin.exists_fin_two.mp ⟨w i, rfl⟩ with h | h <;> rw [h] <;> simp

/-- **Row recovery of `t`-evaluations.** The row components of the prover's tensor
`ŝ = embedded_MLP_eval (packMLE β t) r` carry the suffix-`eq`-weighted evaluations of `t`:
`(decompose_rows ŝ)_u = Σ_{w ∈ {0,1}^ℓ'} t(u, w) · eq̃(w, r_suffix)`.

This is the load-bearing identity for reconstructing `t(r)` from `ŝ`. It uses the *row*
decomposition (which represents the `t'`/`φ₁` factor); the verifier's
`performCheckOriginalEvaluation` instead uses the *column* decomposition — see the module
note above. -/
lemma decompose_rows_packMLE (ℓ ℓ' : ℕ) [NeZero ℓ] [NeZero ℓ'] (h_l : ℓ = ℓ' + κ₀)
    (β : Basis (Fin κ₀ → Fin 2) K₀ L₀) (t : MultilinearPoly K₀ ℓ) (r : Fin ℓ → L₀)
    (u : Fin κ₀ → Fin 2) :
    decompose_tensor_algebra_rows (L := L₀) (K := K₀) (β := β)
        (embedded_MLP_eval κ₀ L₀ K₀ ℓ ℓ' h_l (packMLE κ₀ L₀ K₀ ℓ ℓ' h_l β t) r) u
      = ∑ w : Fin ℓ' → Fin 2,
          (MvPolynomial.eval (fun i =>
              ((if h : i.val < κ₀ then u ⟨i.val, h⟩ else w ⟨i.val - κ₀, by omega⟩ : Fin 2) : K₀))
              t.val)
            • (eqTilde (fun i => (if w i == 1 then (1 : L₀) else 0))
                (getEvaluationPointSuffix κ₀ L₀ ℓ ℓ' h_l r)) := by
  rw [embedded_MLP_eval_eq_sum, decompose_rows_sum]
  apply Finset.sum_congr rfl
  intro w _
  rw [decompose_rows_φ₀φ₁, packMLE_repr_eval]

end RingSwitchingAlgebra

end Binius.RingSwitching

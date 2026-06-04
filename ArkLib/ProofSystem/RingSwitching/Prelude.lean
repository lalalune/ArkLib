/-
Copyright (c) 2025 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chung Thai Nguyen, Quang Dao
-/

import ArkLib.Data.MvPolynomial.Multilinear
import ArkLib.OracleReduction.Basic
import ArkLib.OracleReduction.Security.RoundByRound
import CompPoly.Fields.Binary.Tower.TensorAlgebra
import ArkLib.ProofSystem.RingSwitching.Profile
import ArkLib.ProofSystem.Sumcheck.Structured
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

namespace RingSwitching

open OracleSpec OracleComp ProtocolSpec Finset Polynomial MvPolynomial TensorProduct
open scoped NNReal
open Sumcheck.Structured

/- This section defines generic preliminaries for the ring-switching protocol. -/
section Preliminaries

variable (κ : ℕ) [NeZero κ]
variable (L : Type) [CommRing L] [Fintype L] [DecidableEq L]
variable (K : Type) [CommRing K] [Fintype K] [DecidableEq K]
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
abbrev TensorAlgebra (K L : Type*) [CommRing K] [CommRing L] [Algebra K L] := L ⊗[K] L

/--
Column embedding φ₀: L → A as a ring homomorphism.
φ₀(α) = α ⊗ 1, operates on columns.
-/
def φ₀ (L K : Type*) [CommRing K] [CommRing L] [Algebra K L] : L →+* TensorAlgebra K L where
  toFun α := α ⊗ₜ[K] (1 : L)
  map_one' := rfl
  map_mul' α β := by simp only [Algebra.TensorProduct.tmul_mul_tmul, mul_one]
  map_zero' := by simp only [zero_tmul]
  map_add' α β := by simp only [add_tmul]

/--
Row embedding φ₁: L → A as a ring homomorphism.
φ₁(α) = 1 ⊗ α, operates on rows.
-/
def φ₁ (L K : Type*) [CommRing K] [CommRing L] [Algebra K L] : L →+* TensorAlgebra K L where
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
def componentWise_embed_MLE {A' : Type} [CommRing A'] (φ : L →+* A')
    (t' : MultilinearPoly L ℓ') : MultilinearPoly A' ℓ' :=
  ⟨MvPolynomial.map (R:=L) (S₁ := A') (f:=φ) (t'.val), by
    rw [MvPolynomial.mem_restrictDegree_iff_degreeOf_le]
    intro i -- for any specific variable Xᵢ,
      -- we prove its max individual degree is at most 1 in ANY monomial terms
    calc
      MvPolynomial.degreeOf i (MvPolynomial.map φ t'.val)
      _ ≤ MvPolynomial.degreeOf i t'.val := by
        refine degreeOf_le_iff.mpr ?_
        intro m hm_support_mapped_t' -- consider any specific monomial term
        have hm_in_support_t' : m ∈ t'.val.support := by
          apply MvPolynomial.support_map_subset (f:=φ)
          exact hm_support_mapped_t'
        exact monomial_le_degreeOf i hm_in_support_t'
      _ ≤ 1 := by
        have h_og_t' := t'.property
        simp only [MvPolynomial.mem_restrictDegree_iff_degreeOf_le] at h_og_t'
        exact h_og_t' i
  ⟩

/-- Binius-named alias: component-wise `φ₁` embedding into the tensor algebra `L ⊗[K] L`. -/
def componentWise_φ₁_embed_MLE (t' : MultilinearPoly L ℓ') :
    MultilinearPoly (TensorAlgebra K L) ℓ' :=
  componentWise_embed_MLE L ℓ' (A' := TensorAlgebra K L) (φ₁ L K) t'

end TensorAlgebraOps

section ProtocolTypes
/-!
## Enhanced Protocol Type Definitions (Interfaces between phases)

We define the Statement and Witness types at the boundaries of each phase
following the enhanced specification.
-/

/-- Initial input (input to the Batching Phase): a polynomial-evaluation claim `s = t(r)`. -/
structure MLPEvalStatement where
  /-- The evaluation point `r = (r₀, …, r_{ℓ-1})` — shared input. -/
  t_eval_point : Fin ℓ → L
  /-- The claimed evaluation `s = t(r)`. -/
  original_claim : L

structure WitMLP where
  t : MultilinearPoly K ℓ

structure BatchingWitIn where
  t : MultilinearPoly K ℓ
  t' : MultilinearPoly L ℓ'

structure BatchingStmtIn where
  t_eval_point : Fin ℓ → L -- r = (r_0, ..., r_{ℓ-1}) => shared input
  original_claim : L -- s = t(r) => the original claim to verify

structure RingSwitchingBaseContext (P : RingSwitchingProfile K L κ)
    extends (SumcheckBaseContext L ℓ) where
  -- context from batching phase
  s_hat : P.A -- ŝ
  r_batching : Fin κ → L -- r''

-- `SumcheckWitness` was lifted to `ArkLib.ProofSystem.Sumcheck.Structured` (the data shape is
-- generic and degree-neutral; only the per-round prover/verifier in `SumcheckPhase.lean` consume
-- it). Binius ring-switching is the degree-2 case `H = m · t'`, so this Binius-local abbrev pins
-- `d := 2`. Other instantiations (e.g. Hachi at `d := 2b+1`) pin their own degree — no
-- instantiation is privileged by a default on the generic type. The packed polynomial `t'` and
-- round polynomial `H` (after fixing previous challenges) live in the same structure.
abbrev SumcheckWitness (L : Type) [CommSemiring L] (ℓ : ℕ) (i : Fin (ℓ + 1)) :=
  Sumcheck.Structured.SumcheckWitness L ℓ i 2

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
open Module

variable (κ : ℕ) [NeZero κ]
variable (L : Type) [CommRing L] [Nontrivial L] [Fintype L] [DecidableEq L]
  [SampleableType L]
variable (K : Type) [CommRing K] [Fintype K] [DecidableEq K]
variable [Algebra K L]
variable (P : RingSwitchingProfile K L κ)
variable (ℓ ℓ' : ℕ) [NeZero ℓ] [NeZero ℓ']
variable (h_l : ℓ = ℓ' + κ)

/-- Compute the tensor value ŝ := φ₁(t')(φ₀(r_κ), ..., φ₀(r_{ℓ-1})) -/
def embedded_MLP_eval (t' : MultilinearPoly L ℓ') (r : Fin ℓ → L) :
  P.A :=
  -- This implements the identity:
  -- ŝ = Σ_{w ∈ {0,1}^ℓ'} eq̃(r_suffix, w) ⊗ t'(w)
  let r_suffix : Fin ℓ' → L :=
    fun i => r ⟨i.val + κ, by { rw [h_l]; omega }⟩
  let φ₁_mapped_t': MultilinearPoly P.A ℓ' := componentWise_embed_MLE L ℓ' P.φ₁ t'
  let φ₀_mapped_r: Fin ℓ' → P.A := fun i => P.φ₀ (r_suffix i)
  φ₁_mapped_t'.val.eval φ₀_mapped_r

/-- Step 2 (V): Check 1: s ?= Σ_{v ∈ {0,1}^κ} eqTilde(v, r_{0..κ-1}) ⋅ ŝ_v.

Note (soundness fix): the decomposition here must read the **row** components of `ŝ`
(`P.decomposeRows`), which carry the `φ₁`/`t'` tensor factor: by
`decompose_rows_packMLE`, `(rows ŝ)_u = Σ_w t(u,w)·eq̃(w, r_suffix)`, so the
`eq̃(·, r_prefix)`-weighted sum reconstructs `t(r)`. The previous version used
the column decomposition, which extracts the `φ₀`/`eq` factor instead
(`(columns (a ⊗ b))_v = β.repr a v • b`); with it the check does **not** imply
`s = t(r)` (failing term at `κ = 1`, `t(0,w) = 1`, `t(1,w) = 0`). -/
def performCheckOriginalEvaluation (s : L) (r : Fin ℓ → L) (s_hat : P.A) : Bool :=
  let r_prefix : Fin κ → L := fun i => r ⟨i.val, by omega⟩
  let check_sum := Finset.sum Finset.univ fun (v : Fin κ → Fin 2) =>
    let v_as_L : Fin κ → L := fun i => if (v i == 1) then 1 else 0
    (eqTilde v_as_L r_prefix) * (P.decomposeRows s_hat v)
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
    let coords_A_w_u: (Fin κ → Fin 2) →₀ K := P.basis.repr eq_w
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
  let A_func := compute_A_func κ L K P ℓ' original_r_eval_suffix r''_batching
  let A_MLE: MultilinearPoly L ℓ' := ⟨MvPolynomial.MLE A_func, MLE_mem_restrictDegree A_func⟩
  A_MLE

def getEvaluationPointSuffix (r : Fin ℓ → L) : Fin ℓ' → L :=
  fun i => r ⟨i.val + κ, by { rw [h_l]; omega }⟩

/-- Ring-Switching multiplier parameter for sumcheck, using `A_MLE` as the multiplier. -/
def RingSwitching_SumcheckMultParam :
  SumcheckMultiplierParam L ℓ' (RingSwitchingBaseContext κ L K ℓ P) :=
{ multpoly := fun ctx => -- This is supposed to be (r_κ, …, r_{ℓ-1})
    compute_A_MLE κ L K P ℓ' (original_r_eval_suffix :=
      getEvaluationPointSuffix κ L ℓ ℓ' h_l (r := ctx.t_eval_point))
      (r''_batching := ctx.r_batching)
  -- Ring-switching is the plain degree-2 case `H = P · t'`: combinator `Q := X`, degree 1.
  combinator := fun _ => Polynomial.X
  degCombinator := 1
  combinator_natDegree_le := by intro _; exact Polynomial.natDegree_X_le
}

/-- Step 5 (V): Compute `s₀ := Σ_{u ∈ {0,1}^κ} eqTilde(u, r'') ⋅ ŝ_u`,
where ŝ_u is the row components of ŝ. -/
def compute_s0 (s_hat : P.A) (r''_batching : Fin κ → L) : L :=
  Finset.sum Finset.univ fun (u : Fin κ → Fin 2) =>
    let u_as_L : Fin κ → L := fun i => if (u i == 1) then 1 else 0
    (eqTilde u_as_L r''_batching)
      * (P.decomposeRows s_hat u)

/-- Compute the tensor `e := eq̃(φ₀(r_κ), ..., φ₀(r_{ℓ-1}), φ₁(r'_0), ..., φ₁(r'_{ℓ'-1}))` -/
def compute_final_eq_tensor (r : Fin ℓ → L) (r' : Fin ℓ' → L) : P.A :=
  let φ₀_mapped_r_suffix : Fin ℓ' → P.A := fun i =>
    P.φ₀ (r ⟨i.val + κ, by { rw [h_l]; omega }⟩)
  let φ₁_mapped_r': Fin ℓ' → P.A := fun i => P.φ₁ (r' i)
  eqTilde φ₀_mapped_r_suffix φ₁_mapped_r'

/-- Decompose the final eq tensor `e := Σ_{u ∈ {0,1}^κ} eq̃(u, r'') ⨂ e_u`,
where e_u is the row components of e.
Then compute `Σ_{u ∈ {0,1}^κ} eq̃(u_0, ..., u_{κ-1}, r''_0, ..., r''_{κ-1}) ⋅ e_u`.
-/
def compute_final_eq_value (r_eval : Fin ℓ → L)
    (r'_challenges : Fin ℓ' → L) (r''_batching : Fin κ → L) : L :=
  let e_tensor := compute_final_eq_tensor κ L K P ℓ ℓ' h_l r_eval r'_challenges
  let e_u : (Fin κ → Fin 2) → L := P.decomposeRows e_tensor
  Finset.sum Finset.univ fun (u : Fin κ → Fin 2) =>
    let u_as_L : Fin κ → L := fun i => if u i == 1 then 1 else 0
    let eq_u_r_batching : L := -- `eq̃(u_0, ..., u_{κ-1}, r''_0, ..., r''_{κ-1})`
      eqTilde u_as_L r''_batching
    eq_u_r_batching * (e_u u)

/-- This condition ensures that the witness polynomial `H` has the
correct structure `A(...) * t'(...)` -/
def witnessStructuralInvariant {i : Fin (ℓ' + 1)}
    (stmt : Statement (L := L) (RingSwitchingBaseContext κ L K ℓ P) i)
    (wit : SumcheckWitness L ℓ' i) : Prop :=
  wit.H = projectToMidSumcheckPoly (L := L) (ℓ := ℓ') (t := wit.t') (m :=
    (RingSwitching_SumcheckMultParam κ L K P ℓ ℓ' h_l).multpoly stmt.ctx)
    (i := i) (challenges := stmt.challenges)

def masterKStateProp (aOStmtIn : AbstractOStmtIn L ℓ') (stmtIdx : Fin (ℓ' + 1))
    (stmt : Statement (L := L) (RingSwitchingBaseContext κ L K ℓ P) stmtIdx)
    (oStmt : ∀ j, aOStmtIn.OStmtIn j)
    (wit : SumcheckWitness L ℓ' stmtIdx)
    (localChecks : Prop := True) : Prop :=
  localChecks
  ∧ witnessStructuralInvariant κ L K P ℓ ℓ' h_l stmt wit
  ∧ sumcheckConsistencyProp (boolDomain L _) stmt.sumcheck_target wit.H
  ∧ aOStmtIn.initialCompatibility ⟨wit.t', oStmt⟩

def sumcheckRoundRelationProp (aOStmtIn : AbstractOStmtIn L ℓ') (i : Fin (ℓ' + 1))
    (stmt : Statement (L := L) (RingSwitchingBaseContext κ L K ℓ P) i)
    (oStmt : ∀ j, aOStmtIn.OStmtIn j)
    (wit : SumcheckWitness L ℓ' i) : Prop :=
  masterKStateProp κ L K P ℓ ℓ' h_l aOStmtIn i stmt oStmt wit

/-- Input relation for single round: proper sumcheck statement -/
def sumcheckRoundRelation (aOStmtIn : AbstractOStmtIn L ℓ') (i : Fin (ℓ' + 1)) :
  Set (((Statement (L := L) (RingSwitchingBaseContext κ L K ℓ P) i) ×
    (∀ j, aOStmtIn.OStmtIn j)) × SumcheckWitness L ℓ' i) :=
  { ((stmt, oStmt), wit) | sumcheckRoundRelationProp κ L K P ℓ ℓ' h_l
    aOStmtIn i stmt oStmt wit }

end Relations

open Module in
/-- The Binius (binary-tower) instantiation of `RingSwitchingProfile`, built from the tensor-algebra
definitions above: `A := L ⊗[K] L`, embeddings `φ₀ = · ⊗ 1` / `φ₁ = 1 ⊗ ·`, and the decompositions
are the `K`-basis coordinates via the left/right `L`-module structures.

Marked `@[reducible]` so that, once the protocol code is rewired through the profile, references to
`(binaryTowerProfile …).A` (etc.) unfold to `L ⊗[K] L` at reducible transparency — preserving the
existing `rfl`/instance-driven Binius proofs (and the byte-identical `#print axioms`). -/
@[reducible] def binaryTowerProfile (κ : ℕ) [NeZero κ] (K L : Type)
    [Field K] [Field L] [Algebra K L] (β : Module.Basis (Fin κ → Fin 2) K L) :
    RingSwitchingProfile K L κ where
  basis := β
  A := TensorAlgebra K L
  commRingA := inferInstanceAs (CommRing (L ⊗[K] L))
  algLA := Algebra.TensorProduct.leftAlgebra
  φ₀ := φ₀ L K
  φ₁ := φ₁ L K
  decomposeRows := fun s => decompose_tensor_algebra_rows (L := L) (K := K) (β := β) s
  decomposeColumns := fun s => decompose_tensor_algebra_columns (L := L) (K := K) (β := β) s
  decomposeRows_spec := fun z => by
    conv_lhs => rw [← (β.baseChange L).sum_repr z]
    refine Finset.sum_congr rfl fun u _ => ?_
    unfold decompose_tensor_algebra_rows
    rw [Basis.baseChange_apply, smul_tmul']
    show _ = (φ₀ L K) _ * (φ₁ L K) _
    unfold φ₀ φ₁
    simp [Algebra.TensorProduct.tmul_mul_tmul]
  decomposeColumns_spec := fun z => by
    letI rightAlgebra : Algebra L (L ⊗[K] L) := Algebra.TensorProduct.rightAlgebra
    letI rightModule : Module L (L ⊗[K] L) := rightAlgebra.toModule
    conv_lhs => rw [← (Basis.baseChangeRight (b := β) (Right := L)).sum_repr z]
    refine Finset.sum_congr rfl fun v _ => ?_
    unfold decompose_tensor_algebra_columns
    rw [Basis.baseChangeRight_apply, Algebra.smul_def]
    show algebraMap L (L ⊗[K] L) _ * _ = (φ₁ L K) _ * (φ₀ L K) _
    rw [show (algebraMap L (L ⊗[K] L)) =
      (Algebra.TensorProduct.includeRight).toRingHom.comp (algebraMap L L) by rfl]
    unfold φ₀ φ₁
    simp [Algebra.TensorProduct.tmul_mul_tmul]
  decomposeRows_add := fun z w u => by
    unfold decompose_tensor_algebra_rows
    simp [map_add]
  decomposeRows_φ₀_mul_φ₁ := fun a b u => by
    have h : φ₀ L K a * φ₁ L K b = a ⊗ₜ[K] b := by
      simp only [φ₀, φ₁, RingHom.coe_mk, MonoidHom.coe_mk, OneHom.coe_mk,
        Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul]
    show decompose_tensor_algebra_rows (L := L) (K := K) (β := β) _ u = _
    rw [h]
    unfold decompose_tensor_algebra_rows
    rw [Basis.baseChange_repr_tmul]


/-! ## Generic row-extraction helpers over an abstract `RingSwitchingProfile`

These are profile-level consequences of the two extraction laws `decomposeRows_add` /
`decomposeRows_φ₀_mul_φ₁`, derived once for *every* `P : RingSwitchingProfile B L κ`:
* `decomposeRows_zero` : row coordinates of `0` vanish (from `decomposeRows_add` by cancellation);
* `decomposeRows_finsetSum` : row coordinates are additive over finite sums (induction from the
  binary additivity law and the zero law).
The DP24 capstone below is then stated and proved over an abstract `P`, with `binaryTowerProfile`
recovering the concrete Binius statements by reducibility. -/
section GenericRowExtraction
open Module

variable {B L : Type*} {κ : ℕ} [CommRing B] [CommRing L] [Algebra B L]
variable (P : RingSwitchingProfile B L κ)

/-- Row coordinates of `0` vanish: a profile-level consequence of `decomposeRows_add` (apply it to
`z = w = 0` and cancel). -/
lemma RingSwitchingProfile.decomposeRows_zero (u : Fin κ → Fin 2) :
    P.decomposeRows 0 u = 0 := by
  have h := P.decomposeRows_add 0 0 u
  rw [add_zero] at h
  -- `h : P.decomposeRows 0 u = P.decomposeRows 0 u + P.decomposeRows 0 u`
  -- cancel `P.decomposeRows 0 u` on the left of `… + 0 = … + …`
  exact (add_left_cancel (a := P.decomposeRows 0 u)
    (by rw [add_zero]; exact h)).symm

/-- Row coordinates are additive over finite sums: induction from the binary additivity law
`decomposeRows_add` (with `decomposeRows_zero` as the base case). -/
lemma RingSwitchingProfile.decomposeRows_finsetSum {ι : Type*} [DecidableEq ι] (s : Finset ι)
    (f : ι → P.A) (u : Fin κ → Fin 2) :
    P.decomposeRows (∑ i ∈ s, f i) u = ∑ i ∈ s, P.decomposeRows (f i) u := by
  induction s using Finset.induction with
  | empty => simp [P.decomposeRows_zero]
  | insert a s ha ih =>
    rw [Finset.sum_insert ha, Finset.sum_insert ha, P.decomposeRows_add, ih]

/-- `Fintype` corollary of `decomposeRows_finsetSum` for sums over `univ`. -/
lemma RingSwitchingProfile.decomposeRows_sum {ι : Type*} [Fintype ι] [DecidableEq ι]
    (f : ι → P.A) (u : Fin κ → Fin 2) :
    P.decomposeRows (∑ i, f i) u = ∑ i, P.decomposeRows (f i) u :=
  P.decomposeRows_finsetSum Finset.univ f u

end GenericRowExtraction


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
open Module

variable {κ₀ : ℕ} [NeZero κ₀]
variable {L₀ : Type} [CommRing L₀] [IsDomain L₀] [Fintype L₀] [DecidableEq L₀] [CharP L₀ 2]
variable {K₀ : Type} [CommRing K₀] [IsDomain K₀] [Fintype K₀] [DecidableEq K₀]
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

omit [Fintype L₀] [DecidableEq L₀] [CharP L₀ 2] [Fintype K₀] [DecidableEq K₀] in
/-- `eqTilde` written as a product over coordinates of the symmetric Boolean factor. -/
lemma eqTilde_prod {ℓ_ : ℕ} (r r' : Fin ℓ_ → L₀) :
    eqTilde r r' = ∏ i, ((1 - r i) * (1 - r' i) + r i * r' i) := by
  unfold eqTilde eqPolynomial singleEqPolynomial
  rw [MvPolynomial.eval_prod]
  apply Finset.prod_congr rfl
  intro i _
  simp only [map_add, map_mul, map_sub, map_one, MvPolynomial.eval_C, MvPolynomial.eval_X]

omit [Fintype L₀] [DecidableEq L₀] [CharP L₀ 2] [Fintype K₀] [DecidableEq K₀] in
/-- A product over `Fin (ℓ' + κ₀)` of a function defined by the κ/ℓ'-dichotomy splits as the
product of the κ-prefix and ℓ'-suffix products. -/
lemma prod_concat_split {M : Type*} [CommMonoid M] (ℓ' : ℕ)
    (Fp : Fin κ₀ → M) (Fs : Fin ℓ' → M) :
    (∏ i : Fin (ℓ' + κ₀), if h : i.val < κ₀ then Fp ⟨i.val, h⟩
        else Fs ⟨i.val - κ₀, by omega⟩)
      = (∏ i, Fp i) * ∏ j, Fs j := by
  -- the index equiv `Fin κ₀ ⊕ Fin ℓ' ≃ Fin (ℓ' + κ₀)`, κ-block first
  let e : Fin κ₀ ⊕ Fin ℓ' ≃ Fin (ℓ' + κ₀) :=
    finSumFinEquiv.trans (finCongr (by omega))
  rw [← Equiv.prod_comp e
    (fun i : Fin (ℓ' + κ₀) => if h : i.val < κ₀ then Fp ⟨i.val, h⟩ else Fs ⟨i.val - κ₀, by omega⟩),
    Fintype.prod_sum_type]
  have he_inl : ∀ i : Fin κ₀, (e (Sum.inl i)).val = i.val := by
    intro i
    simp only [e, Equiv.trans_apply, finSumFinEquiv_apply_left, finCongr_apply, Fin.val_cast,
      Fin.val_castAdd]
  have he_inr : ∀ j : Fin ℓ', (e (Sum.inr j)).val = κ₀ + j.val := by
    intro j
    simp only [e, Equiv.trans_apply, finSumFinEquiv_apply_right, finCongr_apply, Fin.val_cast,
      Fin.val_natAdd]
  congr 1
  · apply Finset.prod_congr rfl
    intro i _
    have hlt : (e (Sum.inl i)).val < κ₀ := by rw [he_inl]; exact i.is_lt
    simp only [dif_pos hlt]
    congr 1
  · apply Finset.prod_congr rfl
    intro j _
    have hge : ¬ (e (Sum.inr j)).val < κ₀ := by rw [he_inr]; omega
    simp only [dif_neg hge]
    congr 1
    apply Fin.ext
    show (e (Sum.inr j)).val - κ₀ = j.val
    rw [he_inr]; omega

omit [Fintype L₀] [DecidableEq L₀] [CharP L₀ 2] [Fintype K₀] [DecidableEq K₀] in
/-- `eqTilde` of concatenated Boolean / point data factors along the κ/ℓ' split:
`eqTilde (concat fp fs) (concat gp gs) = eqTilde fp gp * eqTilde fs gs`. -/
lemma eqTilde_concat_split (ℓ' : ℕ)
    (fp : Fin κ₀ → L₀) (fs : Fin ℓ' → L₀) (gp : Fin κ₀ → L₀) (gs : Fin ℓ' → L₀) :
    eqTilde (fun i : Fin (ℓ' + κ₀) => if h : i.val < κ₀ then fp ⟨i.val, h⟩
          else fs ⟨i.val - κ₀, by omega⟩)
        (fun i : Fin (ℓ' + κ₀) => if h : i.val < κ₀ then gp ⟨i.val, h⟩
          else gs ⟨i.val - κ₀, by omega⟩)
      = eqTilde fp gp * eqTilde fs gs := by
  rw [eqTilde_prod, eqTilde_prod, eqTilde_prod]
  rw [← prod_concat_split (κ₀ := κ₀) ℓ'
    (fun i => (1 - fp i) * (1 - gp i) + fp i * gp i)
    (fun j => (1 - fs j) * (1 - gs j) + fs j * gs j)]
  apply Finset.prod_congr rfl
  intro i _
  by_cases h : i.val < κ₀ <;> simp only [h, dif_pos, dif_neg, not_false_iff]

omit [Fintype L₀] [DecidableEq L₀] [CharP L₀ 2] [Fintype K₀] [DecidableEq K₀] in
/-- `aeval` of `eqPolynomial` at a Boolean coefficient vector lands in `L₀` as `eqTilde`. -/
lemma aeval_eqPolynomial_zeroOne {ℓ_ : ℕ} (x : Fin ℓ_ → Fin 2) (r : Fin ℓ_ → L₀) :
    (MvPolynomial.aeval r) (eqPolynomial (fun i => ((x i : Fin 2) : K₀)))
      = eqTilde (fun i => (if x i == 1 then (1 : L₀) else 0)) r := by
  rw [eqTilde_prod, eqPolynomial, map_prod]
  apply Finset.prod_congr rfl
  intro i _
  unfold singleEqPolynomial
  rcases Fin.exists_fin_two.mp ⟨x i, rfl⟩ with h | h <;> rw [h] <;>
    simp only [Fin.isValue, Fin.val_zero, Fin.val_one, Nat.cast_zero, Nat.cast_one,
      beq_iff_eq, zero_ne_one, reduceIte, one_ne_zero, map_add, map_mul, map_sub, map_one,
      MvPolynomial.aeval_C, MvPolynomial.aeval_X, map_zero, sub_zero, mul_zero, zero_mul,
      add_zero, one_mul, mul_one]

omit [CharP L₀ 2] [Fintype K₀] [DecidableEq K₀] in
/-- **MLE evaluation identity (through the algebra map).** For a multilinear `t` over `K₀`,
its `L₀`-evaluation at `r` equals the suffix-`eq`-weighted sum of its Boolean evaluations:
`aeval r t = ∑_{b ∈ {0,1}^ℓ} algebraMap(t(b)) · eq̃(b, r)`. -/
lemma aeval_eq_sum_eqTilde {ℓ_ : ℕ} (t : MultilinearPoly K₀ ℓ_) (r : Fin ℓ_ → L₀) :
    (MvPolynomial.aeval r) t.val
      = ∑ b : Fin ℓ_ → Fin 2,
          (algebraMap K₀ L₀) (MvPolynomial.eval (fun i => ((b i : Fin 2) : K₀)) t.val)
            * eqTilde (fun i => (if b i == 1 then (1 : L₀) else 0)) r := by
  conv_lhs => rw [← MvPolynomial.is_multilinear_iff_eq_evals_zeroOne.mp t.property]
  rw [MvPolynomial.MLE, map_sum]
  apply Finset.sum_congr rfl
  intro b _
  rw [map_mul, MvPolynomial.aeval_C, aeval_eqPolynomial_zeroOne]
  rw [mul_comm]
  congr 1

/-- The κ-then-ℓ' hypercube concatenation `concatBit v w i = v i` for `i < κ`, `= w (i - κ)`
otherwise — matching `packMLE` / `decompose_rows_packMLE`. Packaged as an `Equiv`. -/
def hypercubeSplitEquiv (ℓ ℓ' : ℕ) (h_l : ℓ = ℓ' + κ₀) :
    (Fin κ₀ → Fin 2) × (Fin ℓ' → Fin 2) ≃ (Fin ℓ → Fin 2) where
  toFun := fun p => fun i => if h : i.val < κ₀ then p.1 ⟨i.val, h⟩ else p.2 ⟨i.val - κ₀, by omega⟩
  invFun := fun b => (fun i => b ⟨i.val, by omega⟩, fun j => b ⟨j.val + κ₀, by omega⟩)
  left_inv := fun ⟨v, w⟩ => by
    apply Prod.ext
    · funext i; simp only [Fin.is_lt, dif_pos]
    · funext j
      have : ¬ (j.val + κ₀ < κ₀) := by omega
      simp only [this, dif_neg, not_false_iff]
      congr 1
      apply Fin.ext; simp
  right_inv := fun b => by
    funext i
    by_cases h : i.val < κ₀
    · simp only [h, dif_pos]
    · simp only [h, dif_neg, not_false_iff]
      congr 1
      apply Fin.ext; simp only []; omega

/-! ### Generic DP24 capstone over an abstract `RingSwitchingProfile`

The lemmas above are stated for the concrete `binaryTowerProfile`; here we lift them to an abstract
`P : RingSwitchingProfile K₀ L₀ κ₀`, using only the structure's embeddings (`P.φ₀`, `P.φ₁`), basis
(`P.basis`), row decomposition (`P.decomposeRows`), and its extraction laws (`decomposeRows_add` /
`decomposeRows_φ₀_mul_φ₁`, via the generic helper `decomposeRows_sum`). The Boolean-literal collapse
of the `eq`-factor (`singleEq_collapse'` / `eqPoly_collapse'`) holds for *any* pair of ring homs
because both agree on `{0, 1}`. These need only `CommRing + IsDomain` (not `Field`), so they apply in
the batching phase. Each reduces to its concrete counterpart at `P := binaryTowerProfile β`. -/

variable (P : RingSwitchingProfile K₀ L₀ κ₀)

omit [Fintype L₀] [DecidableEq L₀] [CharP L₀ 2] [Fintype K₀] [DecidableEq K₀] in
/-- Generic `singleEq_collapse`: a single `eqPolynomial` factor evaluated through the mixed
embedding `eval₂ P.φ₁ (P.φ₀ ∘ g)` at a Boolean coefficient collapses to `P.φ₀` of its ordinary
evaluation, since `P.φ₀` and `P.φ₁` agree on the Boolean literals `{0, 1}` (both are ring homs). -/
private lemma singleEq_collapse' {ℓ_suf : ℕ} (g : Fin ℓ_suf → L₀) (w : Fin ℓ_suf → Fin 2)
    (i : Fin ℓ_suf) :
    MvPolynomial.eval₂ P.φ₁ (fun j => P.φ₀ (g j))
      (singleEqPolynomial ((if w i == 1 then (1 : L₀) else 0)) (X i))
    = P.φ₀ (eval g (singleEqPolynomial ((if w i == 1 then (1 : L₀) else 0)) (X i))) := by
  unfold singleEqPolynomial
  rcases Fin.exists_fin_two.mp ⟨w i, rfl⟩ with h | h <;> rw [h] <;>
    simp only [Fin.isValue, beq_iff_eq, reduceIte, zero_ne_one,
      MvPolynomial.eval₂_add, MvPolynomial.eval₂_mul, MvPolynomial.eval₂_sub,
      MvPolynomial.eval₂_one, MvPolynomial.eval₂_X,
      MvPolynomial.eval_add, MvPolynomial.eval_mul, MvPolynomial.eval_sub, MvPolynomial.eval_X,
      map_add, map_mul, map_sub, map_one, map_zero, sub_zero, mul_zero, zero_mul, add_zero,
      one_mul, mul_one]

omit [Fintype L₀] [DecidableEq L₀] [CharP L₀ 2] [Fintype K₀] [DecidableEq K₀] in
/-- Generic `eqPoly_collapse`: the full `eqPolynomial` collapses through the mixed embedding to
`P.φ₀` of its ordinary evaluation, by multiplying the `singleEq_collapse'` factors. -/
private lemma eqPoly_collapse' {ℓ_suf : ℕ} (g : Fin ℓ_suf → L₀) (w : Fin ℓ_suf → Fin 2) :
    MvPolynomial.eval₂ P.φ₁ (fun j => P.φ₀ (g j))
      (eqPolynomial (fun i => (if w i == 1 then (1 : L₀) else 0)))
    = P.φ₀ (eval g (eqPolynomial (fun i => (if w i == 1 then (1 : L₀) else 0)))) := by
  unfold eqPolynomial
  rw [← MvPolynomial.coe_eval₂Hom, map_prod, MvPolynomial.eval_prod, map_prod]
  apply Finset.prod_congr rfl
  intro i _
  rw [MvPolynomial.coe_eval₂Hom]
  exact singleEq_collapse' P g w i

omit [CharP L₀ 2] in
/-- **Generic DP24 packing expansion** over an abstract `P`. The prover's tensor
`ŝ := P.φ₁(t')(P.φ₀(r_κ), …, P.φ₀(r_{ℓ-1}))` expands over the suffix hypercube as
`ŝ = Σ_{w ∈ {0,1}^ℓ'} P.φ₀(eq̃(w, r_suffix)) · P.φ₁(t'(w))`. -/
lemma embedded_MLP_eval_eq_sum' (ℓ ℓ' : ℕ) [NeZero ℓ] [NeZero ℓ'] (h_l : ℓ = ℓ' + κ₀)
    (t' : MultilinearPoly L₀ ℓ') (r : Fin ℓ → L₀) :
    embedded_MLP_eval κ₀ L₀ K₀ P ℓ ℓ' h_l t' r =
      ∑ w : Fin ℓ' → Fin 2,
        (P.φ₀ (eqTilde (fun i => (if w i == 1 then (1 : L₀) else 0))
            (getEvaluationPointSuffix κ₀ L₀ ℓ ℓ' h_l r)))
          * (P.φ₁ (eval (fun i => (if w i == 1 then (1 : L₀) else 0)) t'.val)) := by
  unfold embedded_MLP_eval componentWise_embed_MLE getEvaluationPointSuffix
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
    exact eqPoly_collapse' P (fun i => r ⟨i.val + κ₀, by rw [h_l]; omega⟩) w
  · unfold MvPolynomial.toEvalsZeroOne
    have hpt : (fun i => ((w i : Fin 2) : L₀)) = (fun i => (if w i == 1 then (1 : L₀) else 0)) := by
      funext i; rcases Fin.exists_fin_two.mp ⟨w i, rfl⟩ with h | h <;> rw [h] <;> simp
    rw [show ((w : Fin ℓ' → L₀)) = (fun i => ((w i : Fin 2) : L₀)) from rfl, hpt]

omit [CharP L₀ 2] in
/-- **Generic row recovery of `t`-evaluations** over an abstract `P` whose basis is `P.basis`.
The row components of `ŝ = embedded_MLP_eval (packMLE P.basis t) r` carry the suffix-`eq`-weighted
evaluations of `t`. Routes through `embedded_MLP_eval_eq_sum'`, the generic row additivity
`P.decomposeRows_sum`, the atomic extraction law `P.decomposeRows_φ₀_mul_φ₁`, and the
profile-independent `packMLE_repr_eval`. -/
lemma decompose_rows_packMLE' (ℓ ℓ' : ℕ) [NeZero ℓ] [NeZero ℓ'] (h_l : ℓ = ℓ' + κ₀)
    (t : MultilinearPoly K₀ ℓ) (r : Fin ℓ → L₀) (u : Fin κ₀ → Fin 2) :
    P.decomposeRows
        (embedded_MLP_eval κ₀ L₀ K₀ P ℓ ℓ' h_l
          (packMLE κ₀ L₀ K₀ ℓ ℓ' h_l P.basis t) r) u
      = ∑ w : Fin ℓ' → Fin 2,
          (MvPolynomial.eval (fun i =>
              ((if h : i.val < κ₀ then u ⟨i.val, h⟩ else w ⟨i.val - κ₀, by omega⟩ : Fin 2) : K₀))
              t.val)
            • (eqTilde (fun i => (if w i == 1 then (1 : L₀) else 0))
                (getEvaluationPointSuffix κ₀ L₀ ℓ ℓ' h_l r)) := by
  rw [embedded_MLP_eval_eq_sum', P.decomposeRows_sum]
  apply Finset.sum_congr rfl
  intro w _
  rw [P.decomposeRows_φ₀_mul_φ₁, packMLE_repr_eval]

omit [CharP L₀ 2] in
/-- **Generic DP24 ring-switching capstone (sum form)** over an abstract `P`. The verifier's
row-decomposition check sum, applied to the honest tensor `ŝ = embedded_MLP_eval (packMLE P.basis t)
r`, reconstructs exactly `t(r) = aeval r t`. -/
lemma check_rows_sum_eq_aeval' (ℓ ℓ' : ℕ) [NeZero ℓ] [NeZero ℓ'] (h_l : ℓ = ℓ' + κ₀)
    (t : MultilinearPoly K₀ ℓ) (r : Fin ℓ → L₀) :
    (∑ v : Fin κ₀ → Fin 2,
        eqTilde (fun i => (if v i == 1 then (1 : L₀) else 0)) (fun i => r ⟨i.val, by omega⟩)
          * P.decomposeRows
              (embedded_MLP_eval κ₀ L₀ K₀ P ℓ ℓ' h_l
                (packMLE κ₀ L₀ K₀ ℓ ℓ' h_l P.basis t) r) v)
      = (MvPolynomial.aeval r) t.val := by
  subst h_l
  rw [aeval_eq_sum_eqTilde]
  rw [← Equiv.sum_comp (hypercubeSplitEquiv (κ₀ := κ₀) (ℓ' + κ₀) ℓ' rfl), Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro v _
  rw [decompose_rows_packMLE', Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro w _
  rw [Algebra.smul_def]
  rw [show (fun i => ((hypercubeSplitEquiv (κ₀ := κ₀) (ℓ' + κ₀) ℓ' rfl (v, w) i : Fin 2) : K₀))
      = (fun i => ((if h : i.val < κ₀ then v ⟨i.val, h⟩ else w ⟨i.val - κ₀, by omega⟩ : Fin 2) : K₀))
      from by funext i; rfl]
  rw [show (getEvaluationPointSuffix κ₀ L₀ (ℓ' + κ₀) ℓ' rfl r)
      = (fun i => r ⟨i.val + κ₀, by omega⟩) from by funext i; rfl]
  have hfuse :
      eqTilde (fun i => (if v i == 1 then (1 : L₀) else 0)) (fun i => r ⟨i.val, by omega⟩)
        * eqTilde (fun i => (if w i == 1 then (1 : L₀) else 0)) (fun i => r ⟨i.val + κ₀, by omega⟩)
      = eqTilde
          (fun i => (if hypercubeSplitEquiv (κ₀ := κ₀) (ℓ' + κ₀) ℓ' rfl (v, w) i == 1 then
            (1 : L₀) else 0)) r := by
    rw [← eqTilde_concat_split (κ₀ := κ₀) ℓ'
        (fun i => (if v i == 1 then (1 : L₀) else 0))
        (fun i => (if w i == 1 then (1 : L₀) else 0))
        (fun i => r ⟨i.val, by omega⟩)
        (fun i => r ⟨i.val + κ₀, by omega⟩)]
    congr 1
    · funext i
      by_cases h : i.val < κ₀
      · simp only [hypercubeSplitEquiv, Equiv.coe_fn_mk, h, dif_pos]
      · simp only [hypercubeSplitEquiv, Equiv.coe_fn_mk, h, dif_neg, not_false_iff]
    · funext i
      by_cases h : i.val < κ₀
      · rw [dif_pos h]
      · rw [dif_neg h]
        congr 1
        apply Fin.ext
        simp only []
        omega
  rw [← hfuse]
  ring

omit [CharP L₀ 2] in
/-- **Generic DP24 ring-switching capstone (decision form)** over an abstract `P`. The verifier's
Step-2 check on the honest tensor `ŝ = embedded_MLP_eval (packMLE P.basis t) r` accepts exactly when
the original claim equals `t(r) = aeval r t`. This is the soundness/completeness pivot consumed by
the batching phase for an arbitrary profile. -/
lemma performCheckOriginalEvaluation_packMLE_iff' (ℓ ℓ' : ℕ) [NeZero ℓ] [NeZero ℓ']
    (h_l : ℓ = ℓ' + κ₀) (s : L₀)
    (t : MultilinearPoly K₀ ℓ) (r : Fin ℓ → L₀) :
    performCheckOriginalEvaluation κ₀ L₀ K₀ P ℓ ℓ' h_l s r
        (embedded_MLP_eval κ₀ L₀ K₀ P ℓ ℓ' h_l
          (packMLE κ₀ L₀ K₀ ℓ ℓ' h_l P.basis t) r) = true
      ↔ s = (MvPolynomial.aeval r) t.val := by
  unfold performCheckOriginalEvaluation
  simp only [decide_eq_true_eq]
  rw [check_rows_sum_eq_aeval']

/-! ### DP24 §2.5 `A_MLE` final-evaluation identity

The final sumcheck step's verifier check compares the carried sumcheck target against
`compute_final_eq_value · s'`, where `s' = t'(challenges)`. The sumcheck target, in turn, equals the
round polynomial `H = A_MLE · t'` evaluated at all `ℓ'` challenges, i.e. `A_MLE(challenges) ·
t'(challenges)`. Completeness therefore hinges on the algebraic identity
`A_MLE(challenges) = compute_final_eq_value`, i.e. the multilinear extension `A_MLE` of
`compute_A_func` evaluated at the (arbitrary, non-Boolean) challenge point equals the
row-decomposition value of the final eq-tensor `e := eq̃(φ₀(r_suffix), φ₁(challenges))`.

The two helper lemmas below (MLE evaluation as an `eq̃`-weighted sum over the Boolean hypercube, and
the `φ₀/φ₁`-tensor expansion of `e`) reduce the identity to the row-extraction laws
`P.decomposeRows_φ₀_mul_φ₁` / `P.decomposeRows_sum`, exactly as in
`decompose_rows_packMLE'`. -/

omit [IsDomain L₀] [CharP L₀ 2] [IsDomain K₀] [Fintype K₀] [DecidableEq K₀] in
/-- **MLE evaluation as an `eq̃`-weighted hypercube sum.** Evaluating the multilinear extension
`MLE f` at an arbitrary (not necessarily Boolean) point `r` equals the `eq̃`-weighted sum of the
hypercube values `f x`, with weight `eq̃(x, r)`. This is the standard multilinear-extension
evaluation formula, here phrased with the Boolean-literal embedding `x ↦ (if x = 1 then 1 else 0)`
used throughout the ring-switching algebra layer. -/
lemma MLE_eval_eq_sum_eqTilde {ℓ_ : ℕ} (f : (Fin ℓ_ → Fin 2) → L₀) (r : Fin ℓ_ → L₀) :
    MvPolynomial.eval r (MvPolynomial.MLE f)
      = ∑ x : Fin ℓ_ → Fin 2,
          eqTilde (fun i => (if x i == 1 then (1 : L₀) else 0)) r * f x := by
  rw [MvPolynomial.MLE, map_sum]
  apply Finset.sum_congr rfl
  intro x _
  rw [map_mul, MvPolynomial.eval_C]
  congr 1
  -- `eval r (eqPolynomial (x : Fin ℓ_ → L₀)) = eqTilde (boolEmbed x) r`
  rw [show ((x : Fin ℓ_ → L₀)) = (fun i => ((x i : Fin 2) : L₀)) from rfl]
  rw [show (fun i => ((x i : Fin 2) : L₀)) = (fun i => (if x i == 1 then (1 : L₀) else 0))
      from by funext i; rcases Fin.exists_fin_two.mp ⟨x i, rfl⟩ with h | h <;> rw [h] <;> simp]
  rw [eqTilde]

omit [CharP L₀ 2] [Fintype K₀] [DecidableEq K₀] in
/-- **`φ₀/φ₁`-tensor expansion of an eq-tensor.** The mixed eq-tensor
`eq̃(φ₀ ∘ g, φ₁ ∘ h) ∈ P.A` expands over the Boolean hypercube as
`∑_w φ₀(eq̃(w, g)) · φ₁(eq̃(w, h))`. Proven by collapsing each `eqPolynomial` factor through the
`eval₂ φ₁ (φ₀ ∘ ·)` mixed embedding (the same Boolean-literal-agreement argument as
`embedded_MLP_eval_eq_sum'`, instantiated with the multilinear `eqPolynomial h`). -/
lemma eqTilde_tensor_expand {ℓ_ : ℕ} (g h : Fin ℓ_ → L₀) :
    eqTilde (fun i => P.φ₀ (g i)) (fun i => P.φ₁ (h i))
      = ∑ w : Fin ℓ_ → Fin 2,
          P.φ₀ (eqTilde (fun i => (if w i == 1 then (1 : L₀) else 0)) g)
            * P.φ₁ (eqTilde (fun i => (if w i == 1 then (1 : L₀) else 0)) h) := by
  -- LHS: `eval (φ₁ ∘ h) (eqPolynomial (φ₀ ∘ g))`. Rewrite `eqPolynomial (φ₀ ∘ g)` as the
  -- `φ₀`-image of `eqPolynomial g`, then as the multilinear MLE of its Boolean evaluations, and
  -- push through `eval₂`.
  rw [eqTilde, eqPolynomial_symm]
  -- now LHS = eval (φ₀ ∘ g) (eqPolynomial (φ₁ ∘ h))
  -- View eqPolynomial (φ₁ ∘ h) as map φ₁ of the multilinear eqPolynomial h, evaluated at φ₀ ∘ g.
  have hmap : (eqPolynomial (fun i => P.φ₁ (h i)) : MvPolynomial (Fin ℓ_) P.A)
      = MvPolynomial.map (P.φ₁) (eqPolynomial h) := by
    unfold eqPolynomial singleEqPolynomial
    rw [map_prod]
    apply Finset.prod_congr rfl
    intro i _
    simp only [map_add, map_mul, map_sub, map_one, MvPolynomial.map_C, MvPolynomial.map_X]
  rw [hmap, ← MvPolynomial.eval₂_eq_eval_map]
  -- Expand the multilinear `eqPolynomial h` as `MLE` of its Boolean evaluations.
  conv_lhs => rw [show (eqPolynomial h : MvPolynomial (Fin ℓ_) L₀)
      = MvPolynomial.MLE (eqPolynomial h).toEvalsZeroOne from
        (MvPolynomial.is_multilinear_iff_eq_evals_zeroOne.mp
          (eqPolynomial_mem_restrictDegree h)).symm]
  unfold MvPolynomial.MLE
  rw [← MvPolynomial.coe_eval₂Hom, map_sum]
  apply Finset.sum_congr rfl
  intro w _
  rw [map_mul, MvPolynomial.coe_eval₂Hom, MvPolynomial.eval₂_C]
  have hcoe : (fun i => (((w i : Fin 2) : L₀))) = (fun i => (if w i == 1 then (1 : L₀) else 0)) := by
    funext i; rcases Fin.exists_fin_two.mp ⟨w i, rfl⟩ with hh | hh <;> rw [hh] <;> simp
  congr 1
  · -- φ₀ factor: collapse eqPolynomial through the mixed embedding eval₂ φ₁ (φ₀ ∘ g)
    rw [show (fun i => ((w i : Fin 2) : L₀)) = (fun i => (if w i == 1 then (1 : L₀) else 0))
        from hcoe]
    rw [eqPoly_collapse' P g w]
    rfl
  · -- φ₁ factor: the Boolean evaluation of eqPolynomial h is eqTilde (boolEmbed w) h
    congr 1
    unfold MvPolynomial.toEvalsZeroOne
    rw [hcoe, eqTilde, eqPolynomial_symm]

end RingSwitchingAlgebra

section RingSwitchingAlgebraBinius
-- Concrete Binius (`binaryTowerProfile`) specializations of the DP24 capstone chain. These need
-- `Field K₀`/`Field L₀` to *build* the profile (its `decompose*`/`φ` fields and `rfl`/instance
-- proofs), so they live in this `Field` section, separate from the `CommRing + IsDomain` generic
-- chain above (which is what the batching phase consumes). Each reuses the profile-independent
-- helpers above; the abstract-`P` chain specializes to these at `P := binaryTowerProfile β`.
open Module

variable {κ₀ : ℕ} [NeZero κ₀]
variable {L₀ : Type} [Field L₀] [Fintype L₀] [DecidableEq L₀] [CharP L₀ 2]
variable {K₀ : Type} [Field K₀] [Fintype K₀] [DecidableEq K₀]
variable [Algebra K₀ L₀]

omit [Fintype K₀] [DecidableEq K₀] in
/-- **DP24 packing expansion.** The prover's tensor
`ŝ := φ₁(t')(φ₀(r_κ), …, φ₀(r_{ℓ-1}))` expands over the suffix hypercube as
`ŝ = Σ_{w ∈ {0,1}^ℓ'} φ₀(eq̃(w, r_suffix)) · φ₁(t'(w))`, i.e. `Σ_w eq̃(r_suffix, w) ⊗ t'(w)`. -/
lemma embedded_MLP_eval_eq_sum (β : Module.Basis (Fin κ₀ → Fin 2) K₀ L₀)
    (ℓ ℓ' : ℕ) [NeZero ℓ] [NeZero ℓ'] (h_l : ℓ = ℓ' + κ₀)
    (t' : MultilinearPoly L₀ ℓ') (r : Fin ℓ → L₀) :
    embedded_MLP_eval κ₀ L₀ K₀ (binaryTowerProfile κ₀ K₀ L₀ β) ℓ ℓ' h_l t' r =
      ∑ w : Fin ℓ' → Fin 2,
        (φ₀ L₀ K₀ (eqTilde (fun i => (if w i == 1 then (1 : L₀) else 0))
            (getEvaluationPointSuffix κ₀ L₀ ℓ ℓ' h_l r)))
          * (φ₁ L₀ K₀ (eval (fun i => (if w i == 1 then (1 : L₀) else 0)) t'.val)) := by
  unfold embedded_MLP_eval componentWise_embed_MLE getEvaluationPointSuffix
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
        (embedded_MLP_eval κ₀ L₀ K₀ (binaryTowerProfile κ₀ K₀ L₀ β) ℓ ℓ' h_l
          (packMLE κ₀ L₀ K₀ ℓ ℓ' h_l β t) r) u
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

/-- **DP24 ring-switching capstone (sum form).** The verifier's row-decomposition check sum,
applied to the prover's honest tensor `ŝ = embedded_MLP_eval (packMLE β t) r`, reconstructs
exactly `t(r) = aeval r t`:
`∑_v eq̃(v, r_prefix) · (rows ŝ)_v = aeval r t`. -/
lemma check_rows_sum_eq_aeval (ℓ ℓ' : ℕ) [NeZero ℓ] [NeZero ℓ'] (h_l : ℓ = ℓ' + κ₀)
    (β : Basis (Fin κ₀ → Fin 2) K₀ L₀) (t : MultilinearPoly K₀ ℓ) (r : Fin ℓ → L₀) :
    (∑ v : Fin κ₀ → Fin 2,
        eqTilde (fun i => (if v i == 1 then (1 : L₀) else 0)) (fun i => r ⟨i.val, by omega⟩)
          * decompose_tensor_algebra_rows (L := L₀) (K := K₀) (β := β)
              (embedded_MLP_eval κ₀ L₀ K₀ (binaryTowerProfile κ₀ K₀ L₀ β) ℓ ℓ' h_l
                (packMLE κ₀ L₀ K₀ ℓ ℓ' h_l β t) r) v)
      = (MvPolynomial.aeval r) t.val := by
  subst h_l
  rw [aeval_eq_sum_eqTilde]
  -- reindex `∑_b` over `Fin (ℓ'+κ₀)` to `∑_{(v,w)}`, then `Fintype.sum_prod_type`
  rw [← Equiv.sum_comp (hypercubeSplitEquiv (κ₀ := κ₀) (ℓ' + κ₀) ℓ' rfl), Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro v _
  -- expand the row component and distribute the prefix `eq̃`
  rw [decompose_rows_packMLE, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro w _
  -- `•` → `algebraMap * `
  rw [Algebra.smul_def]
  -- the `t`-evaluation point on both sides is `split (v, w)` (definitional)
  rw [show (fun i => ((hypercubeSplitEquiv (κ₀ := κ₀) (ℓ' + κ₀) ℓ' rfl (v, w) i : Fin 2) : K₀))
      = (fun i => ((if h : i.val < κ₀ then v ⟨i.val, h⟩ else w ⟨i.val - κ₀, by omega⟩ : Fin 2) : K₀))
      from by funext i; rfl]
  rw [show (getEvaluationPointSuffix κ₀ L₀ (ℓ' + κ₀) ℓ' rfl r)
      = (fun i => r ⟨i.val + κ₀, by omega⟩) from by funext i; rfl]
  -- the two `eq̃` factors fuse along the κ/ℓ' split into `eq̃(split(v,w)_as_L, r)`
  have hfuse :
      eqTilde (fun i => (if v i == 1 then (1 : L₀) else 0)) (fun i => r ⟨i.val, by omega⟩)
        * eqTilde (fun i => (if w i == 1 then (1 : L₀) else 0)) (fun i => r ⟨i.val + κ₀, by omega⟩)
      = eqTilde
          (fun i => (if hypercubeSplitEquiv (κ₀ := κ₀) (ℓ' + κ₀) ℓ' rfl (v, w) i == 1 then
            (1 : L₀) else 0)) r := by
    rw [← eqTilde_concat_split (κ₀ := κ₀) ℓ'
        (fun i => (if v i == 1 then (1 : L₀) else 0))
        (fun i => (if w i == 1 then (1 : L₀) else 0))
        (fun i => r ⟨i.val, by omega⟩)
        (fun i => r ⟨i.val + κ₀, by omega⟩)]
    congr 1
    · funext i
      by_cases h : i.val < κ₀
      · simp only [hypercubeSplitEquiv, Equiv.coe_fn_mk, h, dif_pos]
      · simp only [hypercubeSplitEquiv, Equiv.coe_fn_mk, h, dif_neg, not_false_iff]
    · funext i
      by_cases h : i.val < κ₀
      · rw [dif_pos h]
      · rw [dif_neg h]
        congr 1
        apply Fin.ext
        simp only []
        omega
  rw [← hfuse]
  ring

/-- **DP24 ring-switching capstone (decision form).** The verifier's Step-2 check on the prover's
honest tensor `ŝ = embedded_MLP_eval (packMLE β t) r` accepts exactly when the original claim
equals `t(r) = aeval r t`. This is the soundness/completeness pivot for the batching phase. -/
lemma performCheckOriginalEvaluation_packMLE_iff (ℓ ℓ' : ℕ) [NeZero ℓ] [NeZero ℓ']
    (h_l : ℓ = ℓ' + κ₀) (β : Basis (Fin κ₀ → Fin 2) K₀ L₀) (s : L₀)
    (t : MultilinearPoly K₀ ℓ) (r : Fin ℓ → L₀) :
    performCheckOriginalEvaluation κ₀ L₀ K₀ (binaryTowerProfile κ₀ K₀ L₀ β) ℓ ℓ' h_l s r
        (embedded_MLP_eval κ₀ L₀ K₀ (binaryTowerProfile κ₀ K₀ L₀ β) ℓ ℓ' h_l
          (packMLE κ₀ L₀ K₀ ℓ ℓ' h_l β t) r) = true
      ↔ s = (MvPolynomial.aeval r) t.val := by
  unfold performCheckOriginalEvaluation
  simp only [decide_eq_true_eq]
  rw [check_rows_sum_eq_aeval]

end RingSwitchingAlgebraBinius


/-! ## DP24 Batching-Phase Sumcheck Orientation (gap analysis)

The batching phase's round-2 knowledge-state and its completeness require the **sumcheck
consistency** identity (`sumcheckConsistencyProp`)

  `compute_s0 κ L K β ŝ r'' = ∑ x ∈ (univ.map 𝓑) ^ᶠ ℓ', H.eval x`,

with `H = projectToMidSumcheckPoly t' (A_MLE …) 0 Fin.elim0` (so `H = A_MLE · t'` at round 0).

The left-hand side `compute_s0` is a sum over `{0,1}^κ` of `eqTilde`-weighted **row components**
and is **independent of the evaluation domain `𝓑 : Fin 2 ↪ L`**. The right-hand side is the
sumcheck sum over the 2-element domain `{𝓑 0, 𝓑 1}^{ℓ'}` and is genuinely **`𝓑`-dependent**
(the variable `𝓑` is declared free in `BatchingPhase`/`SumcheckPhase`, with no constraint pinning
it to the Boolean embedding `𝓑 0 = 0, 𝓑 1 = 1`).

The two lemmas below make this concrete: the consistency sum of the linear polynomial `X 0`
equals `𝓑 0 + 𝓑 1`, so no single `𝓑`-free target can satisfy consistency simultaneously for two
domains with different element sums. Consequently the round-2
`batchingKStateProp`/`batchingReduction_perfectCompleteness` sumcheck-consistency obligation is
**not satisfiable for a free `𝓑`**; honestly closing it requires either pinning `𝓑` to the
Boolean embedding or reorienting `compute_s0`/`sumcheckConsistencyProp` — both of which would
alter the existing free declarations. See the module report. -/
section SumcheckOrientation
open Module Finset

variable {L₀ : Type} [Field L₀] [Fintype L₀] [DecidableEq L₀] [CharP L₀ 2]

omit [Fintype L₀] [DecidableEq L₀] [CharP L₀ 2] in
/-- **Sumcheck hypercube sum depends on the evaluation domain `𝓑`.**
The single-variable sumcheck consistency sum of the linear polynomial `X 0` over the
2-element domain `{𝓑 0, 𝓑 1}` equals `𝓑 0 + 𝓑 1`. -/
lemma sumcheckSum_X0_eq (𝓑 : Fin 2 ↪ L₀) :
    (∑ x ∈ (univ.map 𝓑) ^ᶠ (1),
        (MvPolynomial.X (0 : Fin 1) : MvPolynomial (Fin 1) L₀).eval x) = 𝓑 0 + 𝓑 1 := by
  rw [Finset.sum_bij' (t := univ.map 𝓑) (g := fun a => a)
    (fun x _ => x 0) (fun a _ => (fun _ => a))
    (fun a ha => by simp only [Fintype.mem_piFinset] at ha; exact ha 0)
    (fun a ha => by simp only [Fintype.mem_piFinset]; exact fun i => ha)
    (fun a ha => by funext i; rw [Fin.fin_one_eq_zero i])
    (fun a ha => rfl)
    (fun a ha => by simp only [MvPolynomial.eval_X])]
  rw [Finset.sum_map]; simp [Fin.sum_univ_two]

omit [Fintype L₀] [DecidableEq L₀] [CharP L₀ 2] in
/-- **No `𝓑`-free target satisfies sumcheck consistency for all domains `𝓑`.**
If a single value `c` (independent of `𝓑`) equals the sumcheck consistency sum of `X 0`
for two embeddings `𝓑₁`, `𝓑₂`, then `𝓑₁ 0 + 𝓑₁ 1 = 𝓑₂ 0 + 𝓑₂ 1`. Contrapositive: whenever two
domains have different element sums (e.g. `{0,1}` vs `{0,ω}` in `GF(4)`, where `1 ≠ ω`), no
`𝓑`-free target can be consistent with both. Since `compute_s0` does not depend on `𝓑`, this
obstructs `sumcheckConsistencyProp (compute_s0 …) H` for a free `𝓑`. -/
lemma sumcheckTarget_domain_indep (c : L₀) (𝓑₁ 𝓑₂ : Fin 2 ↪ L₀)
    (h₁ : c = ∑ x ∈ (univ.map 𝓑₁) ^ᶠ (1),
        (MvPolynomial.X (0 : Fin 1) : MvPolynomial (Fin 1) L₀).eval x)
    (h₂ : c = ∑ x ∈ (univ.map 𝓑₂) ^ᶠ (1),
        (MvPolynomial.X (0 : Fin 1) : MvPolynomial (Fin 1) L₀).eval x) :
    𝓑₁ 0 + 𝓑₁ 1 = 𝓑₂ 0 + 𝓑₂ 1 := by
  rw [sumcheckSum_X0_eq] at h₁ h₂
  rw [← h₁, ← h₂]

/-! ### Boolean-domain (pinned-`𝓑`) regime of DP24

The two lemmas above show the sumcheck consistency identity is `𝓑`-dependent and hence
unsatisfiable for a *free* `𝓑`. The lemmas below pin `𝓑` to the Boolean embedding
`{𝓑 0 = 0, 𝓑 1 = 1}` (the regime DP24 actually instantiates) and re-express the `𝓑`-domain
hypercube sum `∑ x ∈ (univ.map 𝓑) ^ᶠ k, f x` as the canonical Boolean hypercube sum over
`Fin k → Fin 2`. This is the bridge that turns the `𝓑`-dependent right-hand side of
`sumcheckConsistencyProp` into a `𝓑`-free form matching `compute_s0`, and is the load-bearing
reindexing step for closing `batchingReduction_perfectCompleteness` once `𝓑` is pinned. -/

/-- The Boolean hypercube embedding `(Fin k → Fin 2) ↪ (Fin k → L₀)` induced by a 2-element
domain embedding `𝓑`, sending `b ↦ (j ↦ 𝓑 (b j))`. -/
def boolHypercubeEmb (𝓑 : Fin 2 ↪ L₀) (k : ℕ) : (Fin k → Fin 2) ↪ (Fin k → L₀) where
  toFun b := fun j => 𝓑 (b j)
  inj' := by intro a b hab; funext j; exact 𝓑.injective (congrFun hab j)

omit [Field L₀] [Fintype L₀] [DecidableEq L₀] [CharP L₀ 2] in
/-- **`𝓑`-domain hypercube sum reindexes to the Boolean hypercube.** For any `𝓑 : Fin 2 ↪ L₀`,
summing `f` over the `k`-fold product domain `{𝓑 0, 𝓑 1}^k` equals summing `f ∘ (𝓑 ∘ ·)` over
the Boolean hypercube `Fin k → Fin 2`. (No pinning required — `𝓑` only needs to be an embedding.) -/
lemma boolHypercube_sum_eq (𝓑 : Fin 2 ↪ L₀) {k : ℕ} {M : Type*} [AddCommMonoid M]
    (f : (Fin k → L₀) → M) :
    (∑ x ∈ (univ.map 𝓑) ^ᶠ k, f x) = ∑ b : Fin k → Fin 2, f (fun j => 𝓑 (b j)) := by
  have hset : (univ.map 𝓑) ^ᶠ k
      = (univ : Finset (Fin k → Fin 2)).map (boolHypercubeEmb 𝓑 k) := by
    ext x
    simp only [Fintype.mem_piFinset, Finset.mem_map, Finset.mem_univ, true_and, boolHypercubeEmb,
      Function.Embedding.coeFn_mk]
    constructor
    · intro hx; choose c hc using hx; exact ⟨c, funext hc⟩
    · rintro ⟨b, rfl⟩ j; exact ⟨b j, rfl⟩
  rw [hset, Finset.sum_map]
  rfl

omit [Fintype L₀] [DecidableEq L₀] [CharP L₀ 2] in
/-- **Pinned-`𝓑` Boolean-domain sumcheck sum.** When `𝓑` is pinned to the Boolean embedding
(`𝓑 c = if c = 1 then 1 else 0`, i.e. `𝓑 0 = 0`, `𝓑 1 = 1`), the `𝓑`-domain hypercube sum equals
the canonical sum over `Fin k → Fin 2` with the Boolean-literal evaluation point
`j ↦ (if b j = 1 then 1 else 0)`. This is the `𝓑`-free right-hand side of `sumcheckConsistencyProp`
in the regime DP24 instantiates. -/
lemma boolHypercube_sum_pinned (𝓑 : Fin 2 ↪ L₀)
    (h𝓑 : ∀ c, (𝓑 c : L₀) = if c = 1 then 1 else 0)
    {k : ℕ} {M : Type*} [AddCommMonoid M] (f : (Fin k → L₀) → M) :
    (∑ x ∈ (univ.map 𝓑) ^ᶠ k, f x)
      = ∑ b : Fin k → Fin 2, f (fun j => (if b j == 1 then (1 : L₀) else 0)) := by
  rw [boolHypercube_sum_eq]
  apply Finset.sum_congr rfl
  intro b _
  congr 1
  funext j
  rw [h𝓑 (b j)]
  rcases Fin.exists_fin_two.mp ⟨b j, rfl⟩ with h | h <;> rw [h] <;> simp

end SumcheckOrientation


/-! ## `simOracle2` message-query support

These lemmas reduce `simulateQ (OracleInterface.simOracle2 oSpec t₁ t₂) (…)` applied to a single
query to the *right* (message) oracle family `[T₂]ₒ` of the combined spec
`oSpec + ([T₁]ₒ + [T₂]ₒ)`. They are the load-bearing infrastructure for verifier-side
`toFun_full` proofs whose `OracleVerifier.verify` body *queries a prover message*: under
`simulateQ (simOracle2 …)` the message query (read via the per-message `OracleInterface`) routes,
through `QueryImpl.addLift`/`QueryImpl.add`, to `OracleInterface.answer` of the message value.

These are stated over fully general spec/oracle parameters and are candidates for upstreaming to
`OracleReduction/OracleInterface.lean` (which owns `simOracle2`); they live here for now so that
the analogous message-querying `toFun_full`s in `SumcheckPhase` and `BinaryBasefold/Steps` can
import them. -/
section SimOracle2MessageQuery

open OracleInterface

/-- **`simOracle2` message-query collapse (`OracleComp` form).** Simulating, via
`simOracle2 oSpec t₁ t₂`, the lift into the combined spec `oSpec + ([T₁]ₒ + [T₂]ₒ)` of a single
query `qm` to the *right* (message) oracle family `[T₂]ₒ` collapses to `pure` of that oracle's
`answer`, with all queries routed to `t₂`. -/
lemma simulateQ_simOracle2_messageQuery {ι : Type} {oSpec : OracleSpec ι}
    {ι₁ : Type} {T₁ : ι₁ → Type} [∀ i, OracleInterface (T₁ i)]
    {ι₂ : Type} {T₂ : ι₂ → Type} [∀ i, OracleInterface (T₂ i)]
    (t₁ : ∀ i, T₁ i) (t₂ : ∀ i, T₂ i) (qm : ([T₂]ₒ).Domain) :
    simulateQ (OracleInterface.simOracle2 oSpec t₁ t₂)
      (liftM (([T₂]ₒ).query qm) : OracleComp (oSpec + ([T₁]ₒ + [T₂]ₒ)) _)
      = (pure (OracleInterface.answer (t₂ qm.1) qm.2) : OracleComp oSpec _) := by
  -- `liftM` of the message query into the combined spec is `liftM ((…).query (inr (inr qm)))`.
  change simulateQ (OracleInterface.simOracle2 oSpec t₁ t₂)
      (liftM ((oSpec + ([T₁]ₒ + [T₂]ₒ)).query (Sum.inr (Sum.inr qm)))) = _
  rw [simulateQ_spec_query]
  -- `simOracle2` routes `inr (inr …)` to `(simOracle0 T₂ t₂).liftTarget`, i.e. `answer (t₂ …)`.
  simp only [OracleInterface.simOracle2, QueryImpl.addLift_def, QueryImpl.add_apply_inr,
    QueryImpl.liftTarget_apply]
  change liftM (OracleInterface.simOracle0 T₂ t₂ qm) = _
  simp only [OracleInterface.simOracle0]
  rfl

/-- **`simOracle2` message-query collapse (`OptionT`-`query` form).** The same reduction as
`simulateQ_simOracle2_messageQuery`, phrased for the `query`/`monadLift` form that appears verbatim
in an `OracleVerifier.verify` body (a query in `OptionT (OracleComp (oSpec + ([T₁]ₒ + [T₂]ₒ)))`).
This is the form consumed by the verifier-run collapse in message-querying `toFun_full` proofs. -/
lemma simulateQ_simOracle2_query {ι : Type} {oSpec : OracleSpec ι}
    {ι₁ : Type} {T₁ : ι₁ → Type} [∀ i, OracleInterface (T₁ i)]
    {ι₂ : Type} {T₂ : ι₂ → Type} [∀ i, OracleInterface (T₂ i)]
    (t₁ : ∀ i, T₁ i) (t₂ : ∀ i, T₂ i) (qm : ([T₂]ₒ).Domain) :
    simulateQ (OracleInterface.simOracle2 oSpec t₁ t₂)
      (query (spec := [T₂]ₒ) qm : OptionT (OracleComp (oSpec + ([T₁]ₒ + [T₂]ₒ))) _)
      = (OptionT.lift (pure (OracleInterface.answer (t₂ qm.1) qm.2))
          : OptionT (OracleComp oSpec) _) := by
  -- The OptionT query is `OptionT.lift (liftM (message query))`; `simulateQ` commutes with `lift`.
  rw [show (query (spec := [T₂]ₒ) qm : OptionT (OracleComp (oSpec + ([T₁]ₒ + [T₂]ₒ))) _)
        = OptionT.lift (liftM (([T₂]ₒ).query qm) : OracleComp (oSpec + ([T₁]ₒ + [T₂]ₒ)) _) from rfl]
  rw [simulateQ_optionT_lift, simulateQ_simOracle2_messageQuery]
  rfl

end SimOracle2MessageQuery

end RingSwitching

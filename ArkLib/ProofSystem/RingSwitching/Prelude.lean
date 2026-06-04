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

/-- Step 2 (V): Check 1: s ?= Σ_{v ∈ {0,1}^κ} eqTilde(v, r_{0..κ-1}) ⋅ ŝ_v. -/
def performCheckOriginalEvaluation (s : L) (r : Fin ℓ → L) (s_hat : P.A) : Bool :=
  let r_prefix : Fin κ → L := fun i => r ⟨i.val, by omega⟩
  let check_sum := Finset.sum Finset.univ fun (v : Fin κ → Fin 2) =>
    let v_as_L : Fin κ → L := fun i => if (v i == 1) then 1 else 0
    (eqTilde v_as_L r_prefix) * (P.decomposeColumns s_hat v)
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
  -- Soundness fix (defect #10, dual of the #8 performCheck fix): the final eq-value must read
  -- the COLUMN components of the eq-tensor. Term-by-term derivation (via
  -- `MLE_eval_eq_sum_eqTilde` + `eqTilde_tensor_expand` + the atomic extraction laws):
  -- `decomposeColumns (eqTilde(φ₀∘r_suf, φ₁∘ch)) v = Σ_w β.repr(eqTilde(w,r_suf)) v • eqTilde(w,ch)`,
  -- which matches `A_MLE.eval ch` after eqTilde symmetry; the rows form yields the transposed
  -- bilinear pairing, which is NOT symmetric — the A_MLE identity is false for rows.
  let e_u : (Fin κ → Fin 2) → L := P.decomposeColumns e_tensor
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

open Module
/- The Binius (binary-tower) instantiation of `RingSwitchingProfile`, built from the tensor-algebra
definitions above: `A := L ⊗[K] L`, embeddings `φ₀ = · ⊗ 1` / `φ₁ = 1 ⊗ ·`, and the decompositions
are the `K`-basis coordinates via the left/right `L`-module structures.

The final sumcheck step's completeness needs to evaluate the round polynomial
`H = projectToMidSumcheckPoly t' m (Fin.last ℓ') challenges` (= `fixFirstVariablesOfMQP` of
`m · t'` at *all* `ℓ'` variables) at the 0-variate point and recognise it as `(m · t')(challenges)`.
The two lemmas below provide that bridge generically. -/
section FixVarsEval
open MvPolynomial

/-- **`sumAlgEquiv` evaluation.** Evaluating the curried polynomial `sumAlgEquiv p` by `eval x` on
the outer (`S₁`) variables and `eval challenges` on the inner (`S₂`) coefficient ring equals
evaluating `p` directly at the combined point `Sum.elim x challenges`. Proven by `induction_on`,
using `sumToIter` (`= sumAlgEquiv` by `rfl`) on the generators. -/
theorem sumAlgEquiv_eval₂ {L : Type} [CommRing L] {S₁ S₂ : Type} [Fintype S₁]
    (x : S₁ → L) (challenges : S₂ → L) (p : MvPolynomial (S₁ ⊕ S₂) L) :
    eval₂ (eval challenges) x ((sumAlgEquiv L S₁ S₂) p) = eval (Sum.elim x challenges) p := by
  induction p using MvPolynomial.induction_on with
  | C a =>
    rw [show ((sumAlgEquiv L S₁ S₂) (C a)) = sumToIter L S₁ S₂ (C a) from rfl, sumToIter_C,
      MvPolynomial.eval₂_C, MvPolynomial.eval_C, MvPolynomial.eval_C]
  | add p q hp hq =>
    simp only [map_add, MvPolynomial.eval₂_add, MvPolynomial.eval_add, hp, hq]
  | mul_X p s hp =>
    simp only [map_mul, MvPolynomial.eval₂_mul, MvPolynomial.eval_mul, hp]
    congr 1
    cases s with
    | inl a => rw [show ((sumAlgEquiv L S₁ S₂) (X (Sum.inl a))) = sumToIter L S₁ S₂ (X (Sum.inl a))
        from rfl, sumToIter_Xl, MvPolynomial.eval₂_X, MvPolynomial.eval_X, Sum.elim_inl]
    | inr b => rw [show ((sumAlgEquiv L S₁ S₂) (X (Sum.inr b))) = sumToIter L S₁ S₂ (X (Sum.inr b))
        from rfl, sumToIter_Xr, MvPolynomial.eval₂_C, MvPolynomial.eval_X, MvPolynomial.eval_X,
        Sum.elim_inr]

/-- **`fixFirstVariablesOfMQP` evaluation.** Evaluating the polynomial obtained by fixing the last
`v` variables of `poly` to `challenges` (then `eval x` on the survivors) equals evaluating `poly`
directly at the recombined point (survivors from `x`, fixed coords from `challenges`, via the same
`finCongr`/`finSumFinEquiv` reindexing used in `fixFirstVariablesOfMQP`). -/
theorem fixFirstVariablesOfMQP_eval {L : Type} [CommRing L] (ℓ : ℕ) (v : Fin (ℓ+1))
    (poly : MvPolynomial (Fin ℓ) L) (challenges : Fin v → L) (x : Fin (ℓ - v) → L) :
    eval x (fixFirstVariablesOfMQP ℓ v poly challenges)
      = eval (fun i => Sum.elim x challenges
          (((finCongr (by rw [Nat.add_comm]; exact (Nat.add_sub_of_le v.is_le).symm)).trans
            (finSumFinEquiv (m := ℓ - v) (n := v).symm)) i)) poly := by
  unfold fixFirstVariablesOfMQP
  dsimp only
  rw [MvPolynomial.eval_map, sumAlgEquiv_eval₂, eval_rename]
  rfl

end FixVarsEval

/-! ## Round-transition algebra for the iterated sumcheck

The per-round completeness of `iteratedSumcheckOracleReduction` needs to relate the projected
round polynomial at round `i` to the one at round `i+1` after the verifier's challenge `r'` is
folded in. Because `projectToMidSumcheckPoly ℓ t m i ch = fixFirstVariablesOfMQP ℓ i (m·t) ch`
(`projectToMidSumcheckPoly_eq_fixVars` below), the round transition is a pure statement about
`fixFirstVariablesOfMQP`: fixing the last `i` variables and then one more equals fixing the last
`i+1` variables at once.

CONVENTION / STATEMENT-REPAIR NOTE (counterexample-backed, defect-#8/#10/#11 family).
`fixFirstVariablesOfMQP ℓ v poly ch` fixes the **last** `v` variables of `poly`, with `ch 0`
fixing variable `ℓ-v`, …, `ch (v-1)` fixing variable `ℓ-1` (see its corrected docstring). When we
fix one *more* variable (the new round-`i` challenge `r'`), that fresh variable is the *new last
survivor*, i.e. the variable at position `ℓ-v-1`. In the combined `Fin (v+1)`-indexed challenge
vector for `fixFirstVariablesOfMQP ℓ (v+1)`, position `0` corresponds to variable `ℓ-(v+1) = ℓ-v-1`
(the fresh one) and positions `1..v` to the previously-fixed `ch 0 .. ch (v-1)`. Hence the correct
recombination is `Fin.cons r' ch`, **not** `Fin.snoc ch r'`.

The `Fin.snoc ch r'` form is FALSE. Counterexample (`L = ZMod 7`, `ℓ = 3`, `v = 1`,
`poly = X 0 + 2·X 1 + 4·X 2`, `ch = ![5]`, `r' = 3`): fixing the last var to `5`, then one more to
`3`, fixes `X 2 = 5, X 1 = 3`, giving (at survivor `X 0 = 2`) `2 + 2·3 + 4·5 = 28 = 0`. The
`Fin.snoc ![5] 3 = ![5,3]` form fixes `X 1 = 5, X 2 = 3`, giving `2 + 2·5 + 4·3 = 24 = 3 ≠ 0`. The
`Fin.cons 3 ![5] = ![3,5]` form fixes `X 1 = 3, X 2 = 5`, giving `2 + 2·3 + 4·5 = 0`, matching. So
the round-transition lemma below is stated and proved with `Fin.cons r' challenges`. -/
section RoundTransition
open MvPolynomial Finset Sumcheck.Structured

variable {L : Type} [CommRing L]

/-- Value-form of `finSumFinEquiv.symm`: classify the index by whether its value is `< m`. -/
theorem finSumFinEquiv_symm_dite {m n : ℕ} (x : Fin (m + n)) :
    finSumFinEquiv.symm x
      = if h : (x : ℕ) < m then Sum.inl ⟨x, h⟩
        else Sum.inr ⟨(x : ℕ) - m, by omega⟩ := by
  rw [Equiv.symm_apply_eq]
  by_cases h : (x : ℕ) < m
  · rw [dif_pos h, finSumFinEquiv_apply_left]
    apply Fin.ext; simp
  · rw [dif_neg h, finSumFinEquiv_apply_right]
    apply Fin.ext; simp; omega

/-- Characterization of `fixFirstVariablesOfMQP` as a `bind₁` partial substitution: it sends the
surviving variables (value `< ℓ-v` under the canonical reindex) to themselves and the fixed
variables (value `≥ ℓ-v`) to the corresponding `challenges` constant. -/
theorem fixVars_eq_bind₁ (ℓ : ℕ) (v : Fin (ℓ + 1)) (poly : MvPolynomial (Fin ℓ) L)
    (challenges : Fin v → L) :
    fixFirstVariablesOfMQP ℓ v poly challenges
      = bind₁ (fun i : Fin ℓ =>
          Sum.elim (X : Fin (ℓ - v) → MvPolynomial (Fin (ℓ - v)) L)
            (fun j => C (challenges j))
            (((finCongr (by rw [Nat.add_comm]; exact (Nat.add_sub_of_le v.is_le).symm)).trans
              (finSumFinEquiv (m := ℓ - v) (n := v).symm)) i)) poly := by
  unfold fixFirstVariablesOfMQP
  dsimp only
  have hmap : ∀ q : MvPolynomial (Fin (ℓ - v) ⊕ Fin v) L,
      MvPolynomial.map (eval challenges) ((sumAlgEquiv L (Fin (ℓ - v)) (Fin v)) q)
        = bind₁ (Sum.elim X (fun j => C (challenges j))) q := by
    intro q
    induction q using MvPolynomial.induction_on with
    | C a =>
      rw [show ((sumAlgEquiv L (Fin (ℓ - v)) (Fin v)) (C a))
          = sumToIter L (Fin (ℓ - v)) (Fin v) (C a) from rfl, sumToIter_C]
      simp
    | add p q hp hq => simp only [map_add, map_add, hp, hq]
    | mul_X p s hp =>
      rw [map_mul, map_mul, hp]
      congr 1
      cases s with
      | inl a =>
        rw [show ((sumAlgEquiv L (Fin (ℓ - v)) (Fin v)) (X (Sum.inl a)))
            = sumToIter L (Fin (ℓ - v)) (Fin v) (X (Sum.inl a)) from rfl, sumToIter_Xl]
        simp
      | inr b =>
        rw [show ((sumAlgEquiv L (Fin (ℓ - v)) (Fin v)) (X (Sum.inr b)))
            = sumToIter L (Fin (ℓ - v)) (Fin v) (X (Sum.inr b)) from rfl, sumToIter_Xr]
        simp
  rw [hmap, bind₁_rename]
  rfl

/-- **Round-transition for `fixFirstVariablesOfMQP` (cons form).** Fixing the last `v` variables of
`poly` to `challenges` and then the new last survivor to `r'` equals fixing the last `v+1` variables
at once to `Fin.cons r' challenges` (the fresh challenge `r'` lands at index `0`, the previously
fixed `challenges` shift to indices `1..v`), up to the canonical reindex
`Fin (ℓ-(v+1)) ≃ Fin (ℓ-v-1)`. See the section note for why `Fin.snoc challenges r'` is false. -/
theorem fixVars_step (ℓ : ℕ) (poly : MvPolynomial (Fin ℓ) L) (v : Fin (ℓ + 1))
    (hv : (v : ℕ) < ℓ) (challenges : Fin v → L) (r' : L) :
    fixFirstVariablesOfMQP (ℓ - v) ⟨1, by omega⟩
        (fixFirstVariablesOfMQP ℓ v poly challenges) (fun _ => r')
      = rename (finCongr (show ℓ - ((v : ℕ) + 1) = ℓ - v - 1 by omega))
          (fixFirstVariablesOfMQP ℓ ⟨(v : ℕ) + 1, by omega⟩ poly (Fin.cons r' challenges)) := by
  rw [fixVars_eq_bind₁ (ℓ - v) ⟨1, by omega⟩ _ (fun _ => r')]
  rw [fixVars_eq_bind₁ ℓ v poly challenges]
  rw [fixVars_eq_bind₁ ℓ ⟨(v : ℕ) + 1, by omega⟩ poly (Fin.cons r' challenges)]
  rw [bind₁_bind₁]
  rw [rename_bind₁]
  apply congrArg (fun f => bind₁ f poly)
  funext i
  simp only [Equiv.trans_apply, finCongr_apply, finSumFinEquiv_symm_dite, Fin.val_cast]
  by_cases h1 : (i : ℕ) < ℓ - v - 1
  · have h2 : (i : ℕ) < ℓ - v := by omega
    have h1' : (i : ℕ) < ℓ - ((v : ℕ) + 1) := by omega
    -- survivor on both sides → X.  Inner gives X⟨i⟩; outer keeps it (also a survivor).
    rw [dif_pos h2, Sum.elim_inl, bind₁_X_right, dif_pos h1, Sum.elim_inl]
    rw [dif_pos h1', Sum.elim_inl]
    rw [rename_X, finCongr_apply]
    rfl
  · have h1' : ¬ (i : ℕ) < ℓ - ((v : ℕ) + 1) := by omega
    by_cases h2 : (i : ℕ) < ℓ - v
    · -- fresh coord (i = ℓ-v-1): inner is survivor X⟨i⟩; outer fixes it (its last var) to C r'.
      rw [dif_pos h2, Sum.elim_inl, bind₁_X_right]
      rw [dif_neg h1, Sum.elim_inr]
      rw [dif_neg h1', Sum.elim_inr]
      rw [rename_C]
      congr 1
      -- RHS `Fin.cons r' challenges` index over `Fin (v+1)`: value `i-(ℓ-(v+1)) = 0`, gives `r'`.
      have : (⟨(i : ℕ) - (ℓ - ((v : ℕ) + 1)), by omega⟩ : Fin ((v : ℕ) + 1)) = 0 := by
        apply Fin.ext; simp; omega
      rw [this, Fin.cons_zero]
    · -- previously-fixed coord (i ≥ ℓ-v): `C (challenges ⟨i-(ℓ-v)⟩)` on both sides.
      rw [dif_neg h2, Sum.elim_inr, bind₁_C_right]
      rw [dif_neg h1', Sum.elim_inr, rename_C]
      congr 1
      -- RHS index value `i-(ℓ-(v+1)) = (i-(ℓ-v)) + 1`, i.e. `Fin.succ ⟨i-(ℓ-v)⟩`; cons drops to it.
      have hidx : (⟨(i : ℕ) - (ℓ - ((v : ℕ) + 1)), by omega⟩ : Fin ((v : ℕ) + 1))
          = Fin.succ ⟨(i : ℕ) - (ℓ - v), by omega⟩ := by
        apply Fin.ext; simp only [Fin.val_succ]; omega
      rw [hidx, Fin.cons_succ]

/-- `projectToMidSumcheckPoly` is `fixFirstVariablesOfMQP` applied to the initial round polynomial
`m · t`, at the same number of fixed variables `i`. -/
theorem projectToMidSumcheckPoly_eq_fixVars (ℓ : ℕ) [NeZero ℓ] (t m : MultilinearPoly L ℓ)
    (i : Fin (ℓ + 1)) (challenges : Fin i → L) :
    (projectToMidSumcheckPoly ℓ t m i challenges).val
      = fixFirstVariablesOfMQP ℓ ⟨i, by omega⟩ (m.val * t.val) challenges := by
  unfold projectToMidSumcheckPoly computeInitialSumcheckPoly
  rfl

/-- **Round-transition for the projected sumcheck polynomial (target (a), cons form).**
Fixing the new round-`i` survivor variable to the verifier challenge `r'` advances the projected
round polynomial from round `i.castSucc` to round `i.succ`, with the challenge vector recombined as
`Fin.cons r' challenges` (see the section note: the `Fin.snoc challenges r'` form is false —
counterexample included). The two sides live over `Fin (ℓ - i.succ)` vs `Fin (ℓ - i.castSucc - 1)`;
they are reconciled by the canonical `finCongr`. -/
theorem fixFirstVariablesOfMQP_projectToMid_step (ℓ : ℕ) [NeZero ℓ] (t m : MultilinearPoly L ℓ)
    (i : Fin ℓ) (challenges : Fin i.castSucc → L) (r' : L) :
    fixFirstVariablesOfMQP (ℓ - i.castSucc)
        ⟨1, by have := i.isLt; simp only [Fin.val_castSucc]; omega⟩
        (projectToMidSumcheckPoly ℓ t m i.castSucc challenges).val (fun _ => r')
      = rename (finCongr (show ℓ - (i.succ : ℕ) = ℓ - i.castSucc - 1 by
          have := i.isLt; simp only [Fin.val_succ, Fin.val_castSucc]; omega))
          (projectToMidSumcheckPoly ℓ t m i.succ (Fin.cons r' challenges)).val := by
  rw [projectToMidSumcheckPoly_eq_fixVars, projectToMidSumcheckPoly_eq_fixVars]
  -- `fixVars_step` at `v := i.castSucc`. Its `⟨↑v + 1⟩` matches `⟨↑i.succ⟩` (both `↑i + 1`).
  have hstep := fixVars_step (L := L) ℓ (m.val * t.val) i.castSucc
    (by have := i.isLt; simp only [Fin.val_castSucc]; omega) challenges r'
  rw [hstep]
  -- Both sides are `rename (finCongr …) (fixFirstVariablesOfMQP ℓ ⟨_⟩ (m·t) (Fin.cons r' ch))`;
  -- the only difference is the fixed-variable count index `⟨↑i.castSucc + 1⟩` vs `⟨↑i.succ⟩`,
  -- which are equal `Fin (ℓ+1)` values (`↑i.succ = ↑i + 1 = ↑i.castSucc + 1`), hence defeq.
  rfl

/-- **Round-polynomial marginal identity (core of target (b)).** Evaluating, at `r'`, the sum over a
finite set `S` of the partial evaluations `Polynomial.map (eval (pt x)) (finSuccEquivNth L 0 H)`
equals the sum over `S` of the full evaluations of `H` with variable `0` fixed to `r'` (the rest set
by `pt x`). This is the marginal that `getSumcheckRoundPoly` computes: it keeps variable `0` as the
round indeterminate (`finSuccEquivNth L 0`, i.e. `Fin.insertNth 0 = Fin.cons`). Generic in the index
type/point function so it can absorb the `Fin.append (∅) · ∘ Fin.cast` reindexing of the round code.

CONVENTION NOTE (counterexample-backed, see `getSumcheckRoundPoly_eval_eq_sum_cons` in
`SumcheckPhase.lean`): the surviving variable here is variable `0` (`Fin.cons r' (pt x)`), **not**
the last variable. The naive target (b) form `getSumcheckRoundPoly H r' = ∑ (fixFirstVariablesOfMQP
H {r'})` is FALSE, because `fixFirstVariablesOfMQP` fixes the *last* variable while
`getSumcheckRoundPoly` marginalises variable `0`; for an asymmetric `H` the two marginals differ.
Counterexample (`L = ZMod 7`, `H = X 0 + 3·X 1` over `Fin 2`, `r' = 2`):
`getSumcheckRoundPoly H` (var 0) at `2` is `H(2,0)+H(2,1) = 2+5 = 0`, whereas
`∑ (fix-last H {2})` is `(0+6)+(1+6) = 6 ≠ 0`. Hence (b) holds only for the variable-`0` marginal. -/
theorem roundPoly_eval_eq_sum_cons {k : ℕ} {ι : Type*} (S : Finset ι) (pt : ι → (Fin k → L))
    (H : MvPolynomial (Fin (k + 1)) L) (r' : L) :
    Polynomial.eval r' (∑ x ∈ S, Polynomial.map (eval (pt x)) (finSuccEquivNth L 0 H))
      = ∑ x ∈ S, eval (Fin.cons r' (pt x)) H := by
  rw [Polynomial.eval_finset_sum]
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [← eval_eq_eval_mv_eval_finSuccEquivNth, Fin.insertNth_zero']

end RoundTransition

end RingSwitching

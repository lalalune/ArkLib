/-
Copyright (c) 2024 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

import ArkLib.ProofSystem.ConstraintSystem.R1CS
import ArkLib.Data.MvPolynomial.Multilinear
import ArkLib.ProofSystem.Sumcheck.Spec.General
import ArkLib.ProofSystem.Component.SendWitness
import ArkLib.ProofSystem.Component.RandomQuery
import ArkLib.ProofSystem.Component.SendClaim
import ArkLib.ProofSystem.Component.CheckClaim

/-!
  # The Spartan PIOP (Polynomial Interactive Oracle Proof)

  The protocol is parametrized by the following parameters:

  - `R` is the underlying ring, required to be a finite integral domain.
  - `n := 2 ^ ℓ_n` is the number of variables in the R1CS relation.
  - `m := 2 ^ ℓ_m` is the number of constraints in the R1CS relation.
  - `n_w := 2 ^ ℓ_w` is the number of witness variables, where `ℓ_w < ℓ_n`.

  Note that all dimensions are required to be powers of two.

  (Maybe we shouldn't do this? And do the padding explicitly, so we can handle arbitrary
  dimensions?)

  It is used to prove the correctness of R1CS relations: `(A *ᵥ 𝕫) * (B *ᵥ 𝕫) = (C *ᵥ 𝕫)`, where:
  - `A, B, C : Matrix (Fin m) (Fin n) R` are the R1CS constraint matrices.
  - `𝕩 : Fin (n - n_w) → R` is the public input.
  - `𝕨 : Fin n_w → R` is the private witness.
  - `𝕫 = 𝕩 ‖ 𝕨` is the concatenation of the public input `𝕩` and the private witness `𝕨`.
  - `*ᵥ` denotes the standard matrix-vector product, and `*` denotes the component-wise product.

  The protocol may prove R1CS relations whose dimensions are not powers of two by zero-padding.
  (details in the `R1CS.lean` file)

  The protocol (described as a PIOP, before composing with poly commitments) proceeds as follows:

  **I. Interaction Phase:**

  - **Stage 0:** The oracle verifier may optionally receive oracle access to the multilinear
    extensions `MLE A, MLE B, MLE C : R[X Fin ℓ_n][X Fin ℓ_m]` of the R1CS matrices `A`, `B`, and
    `C`. Otherwise, the oracle verifier may see the matrices `A`, `B`, and `C` directly (as part of
    the input statement).

  - **Stage 1:** The prover sends the multilinear extension `MLE 𝕨 : R[X Fin n_w]` of the witness
    `w` to the verifier. The verifier sends back a challenge `τ : Fin ℓ_m → R`.

  - **Stage 2:** The prover and verifier engage in a sum-check protocol to verify the computation:
      `∑ x ∈ {0, 1}^ℓ_m, eqPoly ⸨τ, x⸩ * (A𝕫 ⸨x⸩ * B𝕫 ⸨x⸩ - C𝕫 ⸨x⸩) = 0`,

    where `A𝕫 ⸨X⸩ = ∑ y ∈ {0, 1}^ℓ_m, (MLE A) ⸨X⸩ ⸨y⸩ * (MLE 𝕫) ⸨y⸩`, and similarly for `B𝕫` and
    `C𝕫`.

    The sum-check protocol terminates with random challenges `r_x : Fin ℓ_m → R`, and the purported
    evaluation `e_x` of `eqPoly ⸨τ, r_x⸩ * (A𝕫 ⸨r_x⸩ * B𝕫 ⸨r_x⸩ - C𝕫 ⸨r_x⸩)`.

  - **Stage 3:** The prover sends further evaluation claims to the verifier:

      `v_A = A𝕫 ⸨r_x⸩`, `v_B = B𝕫 ⸨r_x⸩`, `v_C = C𝕫 ⸨r_x⸩`

    The verifier sends back challenges `r_A, r_B, r_C : R`.

  - **Stage 4:** The prover and verifier engage in another sum-check protocol to verify the
    computation:

      `∑ y ∈ {0, 1}^ℓ_n, r_A * (MLE A) ⸨r_x, y⸩ * (MLE 𝕫) ⸨y⸩ + r_B * (MLE B) ⸨r_x, y⸩ *`
      `(MLE 𝕫) ⸨y⸩ + r_C * (MLE C) ⸨r_x, y⸩ * (MLE 𝕫) ⸨y⸩ = r_A * v_A + r_B * v_B + r_C * v_C`

    The sum-check protocol terminates with random challenges `r_y : Fin ℓ_n → R`, and the purported
    evaluation `e_y` of

      `(r_A * (MLE A) ⸨r_x, r_y⸩ + r_B * (MLE B) ⸨r_x, r_y⸩ + r_C * (MLE C) ⸨r_x, r_y⸩) *`
      `(MLE 𝕫) ⸨r_y⸩`.

  **II. Verification Phase:**

  1. The verifier makes a query to the polynomial oracle `MLE 𝕨` at `r_y [ℓ_n - ℓ_k :] : Fin ℓ_k →
     R`, and obtain an evaluation value `v_𝕨 : R`.

  2. The verifier makes three queries to the polynomial oracles `MLE A, MLE B, MLE C` at `r_y ‖ r_x
     : Fin (ℓ_n + ℓ_m) → R`, and obtain evaluation values `v_1, v_2, v_3 : R`.

  Alternatively, if the verifier does not receive oracle access, then it computes the evaluation
  values directly.

  3. The verifier computes `v_𝕫 := 𝕩 *ᵢₚ (⊗ i, (1, r_y i))[: n - k] + (∏ i < ℓ_k, r_y i) * v_𝕨`,
     where `*ᵢₚ` denotes the inner product, and `⊗` denotes the tensor product.

  4. The verifier accepts if and only if both of the following holds:
    - `e_x = eqPoly ⸨τ, r_x⸩ * (v_A * v_B - v_C)`
    - `e_y = (r_A * v_1 + r_B * v_2 + r_C * v_3) * v_𝕫`.

-/

open MvPolynomial Matrix OracleComp ProtocolSpec

namespace Spartan

-- Note: this is the _padded_ Spartan protocol. The non-padded version will be defined via padding
-- to the nearest power of two

noncomputable section

/-- The public parameters of the (padded) Spartan protocol. Consists of the number of bits of the
  R1CS dimensions, and the number of bits of the witness variables. -/
structure PublicParams where
  ℓ_m : ℕ
  ℓ_n : ℕ
  ℓ_w : ℕ
  ℓ_w_le_ℓ_n : ℓ_w ≤ ℓ_n := by omega

namespace PublicParams

/-- The R1CS dimensions / sizes are the powers of two of the public parameters. -/
def toSizeR1CS (pp : PublicParams) : R1CS.Size := {
  m := 2 ^ pp.ℓ_m
  n := 2 ^ pp.ℓ_n
  n_w := 2 ^ pp.ℓ_w
  n_w_le_n := Nat.pow_le_pow_of_le (by decide) pp.ℓ_w_le_ℓ_n
}

end PublicParams

namespace Spec

variable (R : Type) [CommRing R] [IsDomain R] [Fintype R] (pp : PublicParams)

variable {ι : Type} (oSpec : OracleSpec ι)

section Construction

/- The input types and relation is just the R1CS relation for the given size -/

/-- This unfolds to `𝕩 : Fin (2 ^ ℓ_n - 2 ^ ℓ_w) → R` -/
@[simp]
abbrev Statement := R1CS.Statement R pp.toSizeR1CS

/-- This unfolds to `A, B, C : Matrix (Fin 2 ^ ℓ_m) (Fin 2 ^ ℓ_n) R` -/
@[simp]
abbrev OracleStatement := R1CS.OracleStatement R pp.toSizeR1CS

/-- This unfolds to `𝕨 : Fin 2 ^ ℓ_w → R` -/
@[simp]
abbrev Witness := R1CS.Witness R pp.toSizeR1CS

/-- This unfolds to `(A *ᵥ 𝕫) * (B *ᵥ 𝕫) = (C *ᵥ 𝕫)`, where `𝕫 = 𝕩 ‖ 𝕨` -/
@[simp]
abbrev relation := R1CS.relation R pp.toSizeR1CS

/-- The oracle interface for the input statement is the polynomial evaluation oracle of its
  multilinear extension. -/
-- For the input oracle statement, we define its oracle interface to be the polynomial evaluation
-- oracle of its multilinear extension.

instance : ∀ i, OracleInterface (OracleStatement R pp i) :=
  fun i => {
    Query := (Fin pp.ℓ_m → R) × (Fin pp.ℓ_n → R)
    toOC.spec := fun _ => R
    toOC.impl := fun ⟨x, y⟩ => do return (← read).toMLE ⸨C ∘ x⸩ ⸨y⸩
  }

-- For the input witness, we define its oracle interface to be the polynomial evaluation oracle of
-- its multilinear extension.

-- TODO: define an `OracleInterface.ofEquiv` definition that transfers the oracle interface across
-- an equivalence of types.
instance : OracleInterface (Witness R pp) where
  Query := Fin pp.ℓ_w → R
  toOC.spec := fun _ => R
  toOC.impl := fun evalPoint => do
    return (MLE ((← read) ∘ finFunctionFinEquiv)) ⸨evalPoint⸩

/-!
  ## First message
  We invoke the protocol `SendSingleWitness` to send the witness `𝕨` to the verifier.
-/

/-- Unfolds to `𝕩 : Fin (2 ^ ℓ_n - 2 ^ ℓ_w) → R` -/
@[simp]
abbrev Statement.AfterFirstMessage : Type := Statement R pp

/-- Unfolds to `A, B, C : Matrix (Fin 2 ^ ℓ_m) (Fin 2 ^ ℓ_n) R` and `𝕨 : Fin 2 ^ ℓ_w → R` -/
@[simp]
abbrev OracleStatement.AfterFirstMessage : R1CS.MatrixIdx ⊕ Fin 1 → Type :=
  Sum.rec (OracleStatement R pp) (fun _ => Witness R pp)

/-- Unfolds to `() : Unit` -/
@[simp]
abbrev Witness.AfterFirstMessage : Type := Unit

def oracleReduction.firstMessage :
    OracleReduction oSpec
      (Statement R pp) (OracleStatement R pp) (Witness R pp)
      (Statement.AfterFirstMessage R pp) (OracleStatement.AfterFirstMessage R pp) Unit
      ⟨!v[.P_to_V], !v[Witness R pp]⟩ :=
  SendSingleWitness.oracleReduction oSpec
    (Statement R pp) (OracleStatement R pp) (Witness R pp)

/-!
  ## First challenge
  We invoke the protocol `RandomQuery` on the "virtual" polynomial:
    `𝒢(Z) = ∑_{x} eq ⸨Z, x⸩ * (A𝕫 ⸨x⸩ * B𝕫 ⸨x⸩ - C𝕫 ⸨x⸩)`, which is supposed to be `0`.
-/

def zeroCheckVirtualPolynomial (𝕩 : Statement.AfterFirstMessage R pp)
    -- Recall: `oStmt = (A, B, C, 𝕨)`
    (oStmt : ∀ i, OracleStatement.AfterFirstMessage R pp i) :
      MvPolynomial (Fin pp.ℓ_m) R :=
  letI 𝕫 := R1CS.𝕫 𝕩 (oStmt (.inr 0))
  ∑ x : Fin (2 ^ pp.ℓ_m),
    (eqPolynomial (finFunctionFinEquiv.symm x : Fin pp.ℓ_m → R)) *
      C ((oStmt (.inl .A) *ᵥ 𝕫) x * (oStmt (.inl .B) *ᵥ 𝕫) x - (oStmt (.inl .C) *ᵥ 𝕫) x)

/-- Unfolds to `τ : Fin ℓ_m → R` -/
@[simp]
abbrev FirstChallenge : Type := Fin pp.ℓ_m → R

/-- Unfolds to `(τ, x) : (Fin (2 ^ ℓ_n - 2 ^ ℓ_w) → R) × (Fin (2 ^ ℓ_m) → R)` -/
@[simp]
abbrev Statement.AfterFirstChallenge : Type :=
  FirstChallenge R pp × Statement.AfterFirstMessage R pp

/-- Is equivalent to `((A, B, C), 𝕨) :`
  `(fun _ => (Matrix (Fin 2 ^ ℓ_m) (Fin 2 ^ ℓ_n) R)) × (Fin 2 ^ ℓ_w → R)` -/
@[simp]
abbrev OracleStatement.AfterFirstChallenge : R1CS.MatrixIdx ⊕ Fin 1 → Type :=
  OracleStatement.AfterFirstMessage R pp

@[simp]
abbrev Witness.AfterFirstChallenge : Type := Unit

#check RandomQuery.oracleReduction

/-! ### `firstChallenge` via `RandomQuery` + `OracleLens`

We lift the `RandomQuery` oracle reduction onto the *virtual* zero-check polynomial `𝒢`.
`RandomQuery` tests two oracles `(o₀, o₁)` for equality at a random query; here we instantiate
`o₀ := 𝒢` (the zero-check polynomial built from the R1CS matrix/witness oracles) and `o₁ := 0`,
so the random-query test is exactly "is `𝒢 = 0` at the sampled point `τ`?".

The routing data:
- `projStmt`/`liftStmt`: the inner input statement is `Unit`; the outer output statement is
  `(τ, 𝕩)` (the sampled challenge paired with the unchanged public input).
- `simOStmt`: answers an inner evaluation query to oracle index `j : Fin 2` at point `pt`:
  - `j = 1` (the zero oracle): answer `0` — no outer query needed.
  - `j = 0` (the `𝒢` oracle): answer `𝒢.eval pt` by *reconstructing* it from the outer matrix &
    witness oracles. We read each `(M *ᵥ 𝕫) x` for `x : Fin (2 ^ ℓ_m)` as a `|Fin (2^ℓ_n)|`-fold
    sum of `M(x,y) · 𝕫(y)`, where `M(x,y)` is recovered by a boolean MLE-evaluation query to the
    matrix oracle and `𝕫(y)` is `𝕩` on the public coordinates and a boolean MLE-evaluation query
    to the witness oracle otherwise. This is the faithful virtual-oracle routing (mirroring the
    sum-fold shape of `sumcheckOracleLens.simOStmt`).
- `embedOStmt`/`hEqOStmt`: the output oracle family is the unchanged input family
  (`A, B, C, 𝕨`), so we draw each output oracle from the corresponding input oracle (`.inl`) with
  definitional type coherence. -/

variable [SampleableType R]

/-- The boolean point in `Fin k → R` obtained from the binary digits of `e : Fin (2 ^ k)`. -/
@[reducible]
def boolPoint {k : ℕ} (e : Fin (2 ^ k)) : Fin k → R :=
  fun j => ((finFunctionFinEquiv.symm e j : Fin 2) : R)

/-- The faithful reconstruction of one summand `M(x,y) · 𝕫(y)` of `(M *ᵥ 𝕫) x` from the outer
matrix & witness oracles, as an `OracleComp` over `oSpec + [OuterOStmtIn]ₒ`. We recover the boolean
matrix entry `M(x,y)` via a matrix MLE-evaluation query at the boolean points, and `𝕫 y` either
from the public input `𝕩` (when `y` indexes a public coordinate) or via a witness
MLE-evaluation query. -/
noncomputable def matVecSummandFromOracles
    (𝕩 : Statement.AfterFirstMessage R pp)
    (idx : R1CS.MatrixIdx) (xBits : Fin pp.ℓ_m → R)
    (yEnum : Fin (2 ^ pp.ℓ_n)) :
    OracleComp (oSpec + [OracleStatement.AfterFirstMessage R pp]ₒ) R := do
  let yBits : Fin pp.ℓ_n → R := boolPoint R yEnum
  -- entry `M(x,y)` via boolean MLE query to the matrix oracle
  let mEntry ← (OracleComp.lift <| OracleSpec.query
      (spec := [OracleStatement.AfterFirstMessage R pp]ₒ)
      (show [OracleStatement.AfterFirstMessage R pp]ₒ.Domain from
        ⟨.inl idx, (xBits, yBits)⟩) :
      OracleComp (oSpec + [OracleStatement.AfterFirstMessage R pp]ₒ) R)
  -- value `𝕫 y`: public coordinate from `𝕩`, witness coordinate from the witness oracle
  let zVal : R ←
    if hy : (yEnum : ℕ) < pp.toSizeR1CS.n_x then
      (pure (𝕩 ⟨(yEnum : ℕ), hy⟩) :
        OracleComp (oSpec + [OracleStatement.AfterFirstMessage R pp]ₒ) R)
    else
      (OracleComp.lift <| OracleSpec.query
        (spec := [OracleStatement.AfterFirstMessage R pp]ₒ)
        (show [OracleStatement.AfterFirstMessage R pp]ₒ.Domain from
          ⟨.inr 0,
            boolPoint R
              (⟨(yEnum : ℕ) - pp.toSizeR1CS.n_x,
                by
                  have hlt := yEnum.isLt
                  have hnx : pp.toSizeR1CS.n_x = 2 ^ pp.ℓ_n - 2 ^ pp.ℓ_w := rfl
                  have hle : 2 ^ pp.ℓ_w ≤ 2 ^ pp.ℓ_n :=
                    Nat.pow_le_pow_of_le (by decide) pp.ℓ_w_le_ℓ_n
                  omega⟩ : Fin (2 ^ pp.ℓ_w))⟩) :
        OracleComp (oSpec + [OracleStatement.AfterFirstMessage R pp]ₒ) R)
  pure (mEntry * zVal)

/-- The faithful reconstruction of the zero-check polynomial's evaluation `𝒢.eval pt`, computed
from the outer matrix & witness oracles. Mirrors `zeroCheckVirtualPolynomial` term-by-term:
`∑ x, eqPolynomial (bits x) pt * (A𝕫 x · B𝕫 x − C𝕫 x)`. -/
noncomputable def zeroCheckEvalFromOracles
    (𝕩 : Statement.AfterFirstMessage R pp) (pt : Fin pp.ℓ_m → R) :
    OracleComp (oSpec + [OracleStatement.AfterFirstMessage R pp]ₒ) R :=
  (Finset.univ : Finset (Fin (2 ^ pp.ℓ_m))).toList.foldlM
    (fun (acc : R) (xEnum : Fin (2 ^ pp.ℓ_m)) => do
      let xBits : Fin pp.ℓ_m → R := boolPoint R xEnum
      -- A𝕫 x, B𝕫 x, C𝕫 x as `2^ℓ_n`-fold sums over the boolean `y`
      let rowSum : R1CS.MatrixIdx →
          OracleComp (oSpec + [OracleStatement.AfterFirstMessage R pp]ₒ) R :=
        fun idx => (Finset.univ : Finset (Fin (2 ^ pp.ℓ_n))).toList.foldlM
          (fun (a : R) (yEnum : Fin (2 ^ pp.ℓ_n)) => do
            let term ← matVecSummandFromOracles R pp oSpec 𝕩 idx xBits yEnum
            pure (a + term))
          (0 : R)
      let aVal ← rowSum .A
      let bVal ← rowSum .B
      let cVal ← rowSum .C
      let coeff : R := MvPolynomial.eval pt
        (eqPolynomial (boolPoint R xEnum))
      pure (acc + coeff * (aVal * bVal - cVal)))
    (0 : R)

/-- The value-level oracle-statement lens for `firstChallenge`: projects to the two virtual
RandomQuery oracles `(𝒢, 0)`, and lifts back to `((τ, 𝕩), A, B, C, 𝕨)`. -/
noncomputable def firstChallengeStmtLens :
    OracleStatement.Lens
      (Statement.AfterFirstMessage R pp) (Statement.AfterFirstChallenge R pp)
      (RandomQuery.StmtIn) (RandomQuery.StmtOut (MvPolynomial (Fin pp.ℓ_m) R))
      (OracleStatement.AfterFirstMessage R pp) (OracleStatement.AfterFirstChallenge R pp)
      (RandomQuery.OStmtIn (MvPolynomial (Fin pp.ℓ_m) R))
      (RandomQuery.OStmtOut (MvPolynomial (Fin pp.ℓ_m) R)) :=
  { toFunA := fun ⟨𝕩, oStmt⟩ =>
      ⟨(), fun j => match j with
        | 0 => zeroCheckVirtualPolynomial R pp 𝕩 oStmt
        | 1 => 0⟩
    toFunB := fun ⟨_𝕩, _oStmt⟩ ⟨q, _innerO⟩ => ⟨(q, _𝕩), fun i => (_oStmt i)⟩ }

/-- The oracle-routing lens lifting `RandomQuery` (on the virtual zero-check poly `𝒢`, compared to
the zero polynomial) into Spartan's `firstChallenge` context. -/
noncomputable def firstChallengeOracleLens :
    OracleStatement.OracleLens oSpec
      (Statement.AfterFirstMessage R pp) (Statement.AfterFirstChallenge R pp)
      (RandomQuery.StmtIn) (RandomQuery.StmtOut (MvPolynomial (Fin pp.ℓ_m) R))
      (OracleStatement.AfterFirstMessage R pp) (OracleStatement.AfterFirstChallenge R pp)
      (RandomQuery.OStmtIn (MvPolynomial (Fin pp.ℓ_m) R))
      (RandomQuery.OStmtOut (MvPolynomial (Fin pp.ℓ_m) R))
      (RandomQuery.pSpec (MvPolynomial (Fin pp.ℓ_m) R)) where
  toLens := firstChallengeStmtLens R pp
  projStmt := fun _ => ()
  liftStmt := fun 𝕩 q => (q, 𝕩)
  simOStmt := fun q =>
    match q with
    | ⟨j, pt⟩ => ReaderT.mk fun 𝕩 =>
      match j with
      | 0 => zeroCheckEvalFromOracles R pp oSpec 𝕩 pt
      | 1 => (pure 0 : OracleComp (oSpec + [OracleStatement.AfterFirstMessage R pp]ₒ) R)
  embedOStmt := Function.Embedding.inl
  hEqOStmt := fun _ => rfl

/-- The value-level oracle context lens (drives the prover) corresponding to
`firstChallengeOracleLens`. -/
noncomputable def firstChallengeContextLens :
    OracleContext.Lens
      (Statement.AfterFirstMessage R pp) (Statement.AfterFirstChallenge R pp)
      (RandomQuery.StmtIn) (RandomQuery.StmtOut (MvPolynomial (Fin pp.ℓ_m) R))
      (OracleStatement.AfterFirstMessage R pp) (OracleStatement.AfterFirstChallenge R pp)
      (RandomQuery.OStmtIn (MvPolynomial (Fin pp.ℓ_m) R))
      (RandomQuery.OStmtOut (MvPolynomial (Fin pp.ℓ_m) R))
      (Witness R pp) Unit RandomQuery.WitIn RandomQuery.WitOut where
  stmt := firstChallengeStmtLens R pp
  wit := ⟨fun _ => (), fun _ _ => ()⟩

def oracleReduction.firstChallenge :
    OracleReduction oSpec
      (Statement.AfterFirstMessage R pp) (OracleStatement.AfterFirstMessage R pp) (Witness R pp)
      (Statement.AfterFirstChallenge R pp) (OracleStatement.AfterFirstChallenge R pp) Unit
      ⟨!v[.V_to_P], !v[FirstChallenge R pp]⟩ :=
  (RandomQuery.oracleReduction oSpec (MvPolynomial (Fin pp.ℓ_m) R)).liftContext
    (firstChallengeContextLens R pp)
    (firstChallengeOracleLens R pp oSpec)

/-!
  ## First sum-check
  We invoke the sum-check protocol the "virtual" polynomial:
    `ℱ(X) = eq ⸨τ, X⸩ * (A ⸨X⸩ * B ⸨X⸩ - C ⸨X⸩)`
-/

-- def firstSumCheckVirtualPolynomial (𝕩 : FirstMessageStatement R pp)
--     (oStmt : ∀ i, FirstMessageOracleStatement R pp i) : MvPolynomial (Fin pp.ℓ_n) R :=
--   letI 𝕫 := R1CS.𝕫 𝕩 (oStmt (.inr 0))
--   ∑ x : Fin (2 ^ pp.ℓ_n),
--     (eqPolynomial (finFunctionFinEquiv.symm x : Fin pp.ℓ_n → R)) *
--       C ((oStmt (.inl .A) *ᵥ 𝕫) x * (oStmt (.inl .B) *ᵥ 𝕫) x - (oStmt (.inl .C) *ᵥ 𝕫) x)

/-- Unfolds to `r_x : Fin ℓ_m → R` -/
@[simp]
abbrev FirstSumcheckChallenge : Type := Fin pp.ℓ_m → R

/-- Unfolds to `(r_x, τ, 𝕩) : (Fin ℓ_m → R) × (Fin (2 ^ ℓ_n - 2 ^ ℓ_w) → R) × (Fin ℓ_m → R)` -/
@[simp]
abbrev Statement.AfterFirstSumcheck : Type :=
  FirstSumcheckChallenge R pp × Statement.AfterFirstChallenge R pp

/-- Is equivalent to `((A, B, C), 𝕨) :`
  `(fun _ => (Matrix (Fin 2 ^ ℓ_m) (Fin 2 ^ ℓ_n) R)) × (Fin 2 ^ ℓ_w → R)` -/
@[simp]
abbrev OracleStatement.AfterFirstSumcheck : R1CS.MatrixIdx ⊕ Fin 1 → Type :=
  OracleStatement.AfterFirstChallenge R pp

@[simp]
abbrev Witness.AfterFirstSumcheck : Type := Unit

-- def oracleReduction.firstSumcheck :
--     OracleReduction (Sumcheck.Spec.pSpec R pp.ℓ_m) oSpec
--       (Statement.AfterFirstChallenge R pp) Witness.AfterFirstChallenge
--       (Statement.AfterFirstSumcheck R pp) Witness.AfterFirstSumcheck
--       (OracleStatement.AfterFirstChallenge R pp) (OracleStatement.AfterFirstSumcheck R pp) :=
  -- Sumcheck.Spec.oracleReduction oSpec
  --   (Statement.AfterFirstChallenge R pp) (Witness.AfterFirstChallenge R pp)
  --   (Statement.AfterFirstSumcheck R pp) (Witness.AfterFirstSumcheck R pp)
  --   (OracleStatement.AfterFirstChallenge R pp) (OracleStatement.AfterFirstSumcheck R pp)

/-!
  ## Send evaluation claims

  We send the evaluation claims `v_A, v_B, v_C` to the verifier.

  (i.e. invoking `SendClaim` on these "virtual" values)
-/

@[simp]
abbrev EvalClaim : R1CS.MatrixIdx → Type := fun _ => R

/-- We equip each evaluation claim with the default oracle interface, which returns the claim upon a
  trivial query `() : Unit`. -/
instance : ∀ i, OracleInterface (EvalClaim R i) :=
  fun _ => default

/-- The *bundled* evaluation-claim oracle `(v_A, v_B, v_C)`, modelled as a single oracle of type
  `∀ i, EvalClaim R i`. Its oracle interface is the indexed-product interface `instProdForall`
  (query `(i : R1CS.MatrixIdx) × Unit`, response `R`), which is *definitionally* the interface used
  for the bundled `P_to_V` message `∀ i, EvalClaim R i`. -/
@[simp]
abbrev BundledEvalClaim : Type := ∀ i, EvalClaim R i

/-
STATEMENT REPAIR (2026-06-04): the previous output oracle family was indexed by
`R1CS.MatrixIdx ⊕ R1CS.MatrixIdx ⊕ Fin 1`, putting THREE separate `EvalClaim R i` oracles in the
left summand while the protocol spec `⟨!v[.P_to_V], !v[∀ i, EvalClaim R i]⟩` carries exactly ONE
bundled `P_to_V` message. Since `pSpec.MessageIdx` is `Unique`, the oracle-verifier embedding
`ιₛₒ ↪ ιₛᵢ ⊕ pSpec.MessageIdx` cannot inject three new oracles into one message — so the def was
unrealizable at the signature level (documented inline by the prior agent).

Repair, option (b) from that note: the new eval-claim oracle is the SINGLE *bundled* oracle
`BundledEvalClaim = ∀ i, EvalClaim R i`, drawn directly from the single bundled message. The output
oracle family is therefore indexed by `Fin 1 ⊕ (R1CS.MatrixIdx ⊕ Fin 1)`: the left `Fin 1` is the
bundled claim oracle (sourced from the message), the right summand is the unchanged input family
`A, B, C, 𝕨` (passed through). This keeps the message/output arity matched, so `embedOStmt` is a
genuine injection and the reduction is realizable (built directly below, mirroring `SendClaim`). The
downstream `secondSumCheckVirtualPolynomial` is rethreaded to read the bundled claim and the
matrices through the new index. -/
@[simp]
abbrev Statement.AfterSendEvalClaim : Type := Statement.AfterFirstSumcheck R pp

@[simp]
abbrev OracleStatement.AfterSendEvalClaim : Fin 1 ⊕ (R1CS.MatrixIdx ⊕ Fin 1) → Type :=
  Sum.elim (fun _ => BundledEvalClaim R) (OracleStatement.AfterFirstSumcheck R pp)

/-- Oracle interface for the bundled-eval-claim output family: the leading `Fin 1` index is the
bundled claim oracle `∀ i, EvalClaim R i` (indexed-product interface `instProdForall`, the same
interface used for the bundled `P_to_V` message, so output/message types are coherent); the trailing
`R1CS.MatrixIdx ⊕ Fin 1` indices reuse the matrix/witness interfaces of `AfterFirstSumcheck`. -/
instance : ∀ i, OracleInterface (OracleStatement.AfterSendEvalClaim R pp i) :=
  fun i => match i with
    | .inl _ => OracleInterface.instProdForall (EvalClaim R)
    | .inr j => (inferInstance : ∀ k, OracleInterface (OracleStatement.AfterFirstSumcheck R pp k)) j

@[simp]
abbrev Witness.AfterSendEvalClaim : Type := Unit

/-- The honest *value* of the bundled evaluation claim `(v_A, v_B, v_C)` at the first sum-check
challenge `r_x`, computed in the clear from the matrices `A, B, C`, the witness `𝕨`, and the public
input `𝕩`. Each `v_idx = (M *ᵥ 𝕫) ⸨r_x⸩` is the multilinear extension of the row vector `M *ᵥ 𝕫`
evaluated at `r_x`. (The prover holds all oracle statements in the clear, so this is a plain
function; the verifier only ever queries it as an oracle.) -/
noncomputable def evalClaimValue
    (stmt : Statement.AfterFirstSumcheck R pp)
    (oStmt : ∀ i, OracleStatement.AfterFirstSumcheck R pp i) :
    BundledEvalClaim R :=
  letI r_x : Fin pp.ℓ_m → R := stmt.1
  letI 𝕩 : Statement.AfterFirstMessage R pp := stmt.2.2
  letI 𝕫 := R1CS.𝕫 𝕩 (oStmt (.inr 0))
  fun idx => MvPolynomial.eval r_x (MLE (((oStmt (.inl idx)) *ᵥ 𝕫) ∘ finFunctionFinEquiv))

/-- The oracle prover for `sendEvalClaim`: it forwards the input oracle family `A, B, C, 𝕨`
unchanged and sends the bundled evaluation claim `(v_A, v_B, v_C)` (computed via `evalClaimValue`)
as the single `P_to_V` message. Mirrors `SendClaim.oracleProver`, but the message is reconstructed
from the input oracles rather than being an input oracle itself. -/
noncomputable def sendEvalClaimProver :
    OracleProver oSpec
      (Statement.AfterFirstSumcheck R pp) (OracleStatement.AfterFirstSumcheck R pp) (Witness R pp)
      (Statement.AfterSendEvalClaim R pp) (OracleStatement.AfterSendEvalClaim R pp) Unit
      ⟨!v[.P_to_V], !v[∀ i, EvalClaim R i]⟩ where
  PrvState := fun _ =>
    (Statement.AfterFirstSumcheck R pp × (∀ i, OracleStatement.AfterFirstSumcheck R pp i))
      × BundledEvalClaim R
  input := fun ⟨⟨stmt, oStmt⟩, _wit⟩ => (⟨stmt, oStmt⟩, evalClaimValue R pp stmt oStmt)
  sendMessage | ⟨0, _⟩ => fun st => pure (st.2, st)
  receiveChallenge | ⟨0, h⟩ => nomatch h
  output := fun st => pure
    (⟨st.1.1,
      fun i => match i with
        | .inl _ => st.2
        | .inr j => st.1.2 j⟩,
     ())

/-- The oracle verifier for `sendEvalClaim`: it performs no check (the eval-claim send is a pure
forwarding component; the claims are verified later by the second sum-check / final check), routes
the bundled claim output oracle from the `P_to_V` message, and routes the `A, B, C, 𝕨` output
oracles from the corresponding input oracles. Mirrors `SendClaim.oracleVerifier`. -/
def sendEvalClaimVerifier :
    OracleVerifier oSpec
      (Statement.AfterFirstSumcheck R pp) (OracleStatement.AfterFirstSumcheck R pp)
      (Statement.AfterSendEvalClaim R pp) (OracleStatement.AfterSendEvalClaim R pp)
      ⟨!v[.P_to_V], !v[∀ i, EvalClaim R i]⟩ where
  verify := fun stmt _challenges => pure stmt
  embed := {
    toFun := fun
      | .inl _ => .inr default
      | .inr j => .inl j
    inj' := by
      intro a b h
      match a, b with
      | .inl _, .inl _ => congr 1; exact Subsingleton.elim _ _
      | .inl _, .inr _ => simp at h
      | .inr _, .inl _ => simp at h
      | .inr _, .inr _ => simpa using h
  }
  hEq := fun i => match i with
    | .inl _ => rfl
    | .inr _ => rfl

/-- STATEMENT REPAIR (2026-06-04): `sendEvalClaim` is now realized (no `sorry`) by the bundled
output-oracle interface above. The prover forwards `A, B, C, 𝕨` and sends the bundled claim
`(v_A, v_B, v_C)`; the verifier draws the claim oracle from the message and the rest from the
inputs. -/
noncomputable def oracleReduction.sendEvalClaim :
    OracleReduction oSpec
      (Statement.AfterFirstSumcheck R pp) (OracleStatement.AfterFirstSumcheck R pp) (Witness R pp)
      (Statement.AfterSendEvalClaim R pp) (OracleStatement.AfterSendEvalClaim R pp) Unit
      ⟨!v[.P_to_V], !v[∀ i, EvalClaim R i]⟩ where
  prover := sendEvalClaimProver R pp oSpec
  verifier := sendEvalClaimVerifier R pp oSpec

/-!
  ## Random linear combination challenges

  The verifier sends back random linear combination challenges `r_A, r_B, r_C : R`.
-/

@[simp]
abbrev LinearCombinationChallenge : Type := R1CS.MatrixIdx → R

/-- Unfolds to `((r_A, r_B, r_C), r_x, τ, 𝕩) :`
  `(R1CS.MatrixIdx → R) × (Fin (2 ^ ℓ_m) → R) × (Fin ℓ_m → R) × (Fin (2 ^ ℓ_n - 2 ^ ℓ_w) → R)` -/
@[simp]
abbrev Statement.AfterLinearCombination : Type :=
  LinearCombinationChallenge R × Statement.AfterSendEvalClaim R pp

/-- STATEMENT REPAIR (2026-06-04): the output oracle family now matches the (corrected) bundled
shape of `AfterSendEvalClaim` — the bundled claim oracle `BundledEvalClaim` plus the passthrough
`A, B, C, 𝕨`, indexed `Fin 1 ⊕ (R1CS.MatrixIdx ⊕ Fin 1)`. `linearCombination` is a pure challenge,
so the oracles pass through unchanged. -/
@[simp]
abbrev OracleStatement.AfterLinearCombination : Fin 1 ⊕ (R1CS.MatrixIdx ⊕ Fin 1) → Type :=
  OracleStatement.AfterSendEvalClaim R pp

@[simp]
abbrev Witness.AfterLinearCombination : Type := Unit

/-
STATEMENT REPAIR (2026-06-04): the previous signature stated the INPUT oracle family as
`OracleStatement.AfterFirstSumcheck` (`A, B, C, 𝕨` only), while the OUTPUT family already contained
the eval-claim oracles `v_A, v_B, v_C`, which were absent from that input. Since `linearCombination`
is a pure `V_to_P` challenge, `pSpec.MessageIdx` is `IsEmpty`, so `embed : ιₛₒ ↪ ιₛᵢ ⊕ MessageIdx`
must route every output oracle from an input oracle — impossible for the new claim oracles. The def
was therefore unrealizable at the signature level (documented inline by the prior agent).

Repair (the prior agent's root-cause fix): per the protocol order, `linearCombination` runs AFTER
`sendEvalClaim`, so its INPUT oracle family is `OracleStatement.AfterSendEvalClaim` (the bundled
claim oracle + `A, B, C, 𝕨`), which equals the output family. With the input corrected, this is a
clean identity-oracle challenge round — exactly the shape of `RandomQuery.oracleVerifier`'s
bare-challenge: the prover receives the challenge `r = (r_A, r_B, r_C)`, the verifier returns it and
identity-routes every oracle (`embed = .inl`, `hEq = rfl`). Built directly below. -/
def linearCombinationProver :
    OracleProver oSpec
      (Statement.AfterSendEvalClaim R pp) (OracleStatement.AfterSendEvalClaim R pp) Unit
      (Statement.AfterLinearCombination R pp) (OracleStatement.AfterLinearCombination R pp) Unit
      ⟨!v[.V_to_P], !v[LinearCombinationChallenge R]⟩ where
  PrvState
  | 0 => (Statement.AfterSendEvalClaim R pp × (∀ i, OracleStatement.AfterSendEvalClaim R pp i)) × Unit
  | 1 => (Statement.AfterSendEvalClaim R pp × (∀ i, OracleStatement.AfterSendEvalClaim R pp i))
            × (LinearCombinationChallenge R)
  input := fun x => x
  sendMessage | ⟨0, h⟩ => nomatch h
  receiveChallenge | ⟨0, _⟩ => fun st => pure fun r => (st.1, r)
  output := fun ⟨⟨stmt, oStmt⟩, r⟩ => pure (((r, stmt), oStmt), ())

/-- The oracle verifier for `linearCombination`: returns the linear-combination challenge and
identity-routes every oracle, mirroring `RandomQuery.oracleVerifier`. -/
def linearCombinationVerifier :
    OracleVerifier oSpec
      (Statement.AfterSendEvalClaim R pp) (OracleStatement.AfterSendEvalClaim R pp)
      (Statement.AfterLinearCombination R pp) (OracleStatement.AfterLinearCombination R pp)
      ⟨!v[.V_to_P], !v[LinearCombinationChallenge R]⟩ where
  verify := fun stmt chal => do
    let r : LinearCombinationChallenge R := chal ⟨0, rfl⟩
    pure (r, stmt)
  embed := Function.Embedding.inl
  hEq := fun _ => rfl

/-- STATEMENT REPAIR (2026-06-04): `linearCombination` is now realized (no `sorry`) with the
corrected input oracle family `AfterSendEvalClaim`. It is a clean identity-oracle challenge round. -/
def oracleReduction.linearCombination :
    OracleReduction oSpec
      (Statement.AfterSendEvalClaim R pp) (OracleStatement.AfterSendEvalClaim R pp) Unit
      (Statement.AfterLinearCombination R pp) (OracleStatement.AfterLinearCombination R pp) Unit
      ⟨!v[.V_to_P], !v[LinearCombinationChallenge R]⟩ where
  prover := linearCombinationProver R pp oSpec
  verifier := linearCombinationVerifier R pp oSpec

/-!
  ## Second sum-check
  We invoke the sum-check protocol the "virtual" polynomial:
    `ℳ(Y) = r_A * (MLE A) ⸨r_x, Y⸩ * (MLE 𝕫) ⸨Y⸩ + r_B * (MLE B) ⸨r_x, Y⸩ * (MLE 𝕫) ⸨Y⸩`
      `+ r_C * (MLE C) ⸨r_x, Y⸩ * (MLE 𝕫) ⸨Y⸩`
-/

-- STATEMENT REPAIR (2026-06-04): rethreaded to the bundled output-oracle index
-- `Fin 1 ⊕ (R1CS.MatrixIdx ⊕ Fin 1)`: the witness oracle is now `.inr (.inr 0)` and matrix `idx`
-- is `.inr (.inl idx)` (the leading `.inl 0` is the bundled eval-claim oracle, unused here).
def secondSumCheckVirtualPolynomial
    (stmt : Statement.AfterLinearCombination R pp)
    (oStmt : ∀ i, OracleStatement.AfterLinearCombination R pp i) :
      MvPolynomial (Fin pp.ℓ_n) R :=
  let r := stmt.1
  let r_x := stmt.2.1
  let x := stmt.2.2.2
  let z := R1CS.𝕫 x (oStmt (.inr (.inr 0)))
  let zMLE : MvPolynomial (Fin pp.ℓ_n) R := MLE (z ∘ finFunctionFinEquiv)
  let matrixEval (idx : R1CS.MatrixIdx) : MvPolynomial (Fin pp.ℓ_n) R :=
    (oStmt (.inr (.inl idx))).toMLE
      ⸨(MvPolynomial.C ∘ r_x : Fin pp.ℓ_m → MvPolynomial (Fin pp.ℓ_n) R)⸩
  let scalar (a : R) : MvPolynomial (Fin pp.ℓ_n) R := MvPolynomial.C a
  scalar (r .A) * matrixEval .A * zMLE +
  scalar (r .B) * matrixEval .B * zMLE +
  scalar (r .C) * matrixEval .C * zMLE

@[simp]
abbrev SecondSumcheckChallenge : Type := Fin pp.ℓ_n → R

/-- Unfolds to `(r_y, (r_A, r_B, r_C), r_x, τ, 𝕩) :`
  `(Fin ℓ_n → R) × (R1CS.MatrixIdx → R) × (Fin (2 ^ ℓ_m) → R) × (Fin ℓ_m → R) ×`
  `(Fin (2 ^ ℓ_n - 2 ^ ℓ_w) → R)` -/
@[simp]
abbrev Statement.AfterSecondSumcheck : Type :=
  SecondSumcheckChallenge R pp × Statement.AfterLinearCombination R pp

-- STATEMENT REPAIR (2026-06-04): rethreaded to the bundled output-oracle index
-- `Fin 1 ⊕ (R1CS.MatrixIdx ⊕ Fin 1)`, matching `AfterLinearCombination` (the second sum-check
-- leaves the oracle family unchanged).
@[simp]
abbrev OracleStatement.AfterSecondSumcheck : Fin 1 ⊕ (R1CS.MatrixIdx ⊕ Fin 1) → Type :=
  OracleStatement.AfterLinearCombination R pp

@[simp]
abbrev Witness.AfterSecondSumcheck : Type := Unit

-- def oracleReduction.secondSumcheck :
--     OracleReduction (Sumcheck.Spec.pSpec R pp.ℓ_n) oSpec
--       (Statement.AfterLinearCombination R pp) Witness.AfterLinearCombination
--       (Statement.AfterSecondSumcheck R pp) Witness.AfterSecondSumcheck
--       (OracleStatement.AfterLinearCombination R pp) (OracleStatement.AfterSecondSumcheck R pp) :=
--   placeholder

/-!
  ## Final check

  We invoke the `CheckClaim` protocol to check the two evaluation claims.
-/

-- Definition of the final relation to be checked
-- def finalCheck := placeholder

-- def oracleReduction.finalCheck :
--     OracleReduction ![] oSpec
--       (Statement.AfterSecondSumcheck R pp) Witness.AfterSecondSumcheck
--       Unit Unit
--       (OracleStatement.AfterSecondSumcheck R pp) (fun _ => Unit) :=
--   CheckClaim.oracleReduction oSpec (Statement.AfterSecondSumcheck R pp)
--     (OracleStatement.AfterSecondSumcheck R pp) (placeholder)

end Construction

section Security


end Security

end Spec

end

end Spartan

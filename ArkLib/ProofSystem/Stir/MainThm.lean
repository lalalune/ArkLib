/-
Copyright (c) 2025 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Poulami Das (Least Authority)
-/

import ArkLib.Data.CodingTheory.ListDecodability
import ArkLib.Data.CodingTheory.ReedSolomon
import ArkLib.OracleReduction.VectorIOR
import ArkLib.ProofSystem.Stir.ProximityBound

/-!Section 5 ACFY24stir, Theorem 5.1 and Lemma 5.4

## References

* [Arnon, G., Chiesa, A., Fenzi, G., and Yogev, E., *STIR: Reed-Solomon proximity testing
    with fewer queries*][ACFY24stir]
-/

open BigOperators Finset ListDecodable NNReal ReedSolomon VectorIOP OracleComp LinearCode STIR

namespace StirIOP

variable {F : Type} [Field F] [Fintype F] [DecidableEq F]
         {M : ℕ} (ι : Fin (M + 1) → Type) [∀ i : Fin (M + 1), Fintype (ι i)]

/-- **Per‑round protocol parameters:**
  For a fixed depth `M`, the reduction runs `M + 1` rounds.
  In round `i ∈ {0,…,M}` we fold by a factor `foldingParamᵢ`,
  evaluate on the point set `ιᵢ` through the embedding `φᵢ : ιᵢ ↪ F`,
  and repeat certain proximity checks `repeatParamᵢ` times. -/
structure Params (F : Type*) where
  deg : ℕ -- initial degree
  foldingParam : Fin (M + 1) → ℕ
  φ : (i : Fin (M + 1)) → (ι i) ↪ F
  repeatParam : Fin (M + 1) → ℕ

/-- **Degree after `i` folds:**
  The starting degree is `deg`;
  every fold divides it by `foldingParamⱼ (j<i)` to obtain `degreeᵢ`.
  Note that division rounds down for `ℕ`. -/
def degree (P : Params ι F) : Fin (M + 1) → ℕ :=
  fun i => P.deg / ∏ j < i, (P.foldingParam j)

/-- **Conditions that protocol parameters must satisfy.**
  - `h_deg` : initial degree `deg` is a power of 2
  - `h_foldingParams` : `∑ i : Fin (M + 1), foldingParamᵢ` is a power of 2
  - `h_deg_ge` : `deg ≥ ∏ i foldingParamᵢ`
  - `h_smooth` : each `φᵢ` must embed a smooth evaluation domain
  - `h_smooth_le` : `|ιᵢ| ≤ degreeᵢ`
  - `h_repeatP_le` : `∀ i : Fin (M + 1), repeatParamᵢ + 1 ≤ degreeᵢ` -/
structure ParamConditions (P : Params ι F) where
  h_deg : ∃ k : ℕ, P.deg = 2^k
  h_foldingParams : ∀ i : Fin (M + 1), ∃ k : ℕ, (P.foldingParam i) = 2^k
  h_deg_ge : P.deg ≥ ∏ i : Fin (M + 1), (P.foldingParam i)
  h_smooth : ∀ i : Fin (M + 1), Smooth (P.φ i)
  h_smooth_le : ∀ i : Fin (M + 1), Fintype.card (ι i) ≤ (degree ι P i)
  h_repeatP_le : ∀ i : Fin (M + 1), P.repeatParam i + 1 ≤ (degree ι P i)

/-- Distance and list‑size targets per round. -/
structure Distances (M : ℕ) where
  δ : Fin (M + 1) → ℝ≥0
  l : Fin (M + 1) → ℝ≥0

/-- Family of Reed–Solomon codes expected by the verifier, we have
  `codeᵢ = RS[F, ιᵢ, degreeᵢ]` and for `i ∈ {1,…,M}`
  `hlistDecode: codeᵢ` is `(δᵢ,lᵢ)`-list decodable
-/
structure CodeParams (P : Params ι F) (Dist : Distances M) where
  C : ∀ i : Fin (M + 1), Set ((ι i) → F)
  h_code : ∀ i : Fin (M + 1), C i = code (P.φ i) (degree ι P i)
  h_listDecode : ∀ i : Fin (M + 1), i ≠ 0 → listDecodable (C i) (Dist.δ i) (Dist.l i)

section MainTheorem

/-- `OracleStatement` defines the oracle message type for a multi-indexed setting:
  given base input type `ι`, and field `F`, the output type at each index
  is a function `ι → F` representing an evaluation over `ι`.
-/
@[reducible]
def OracleStatement (ι F : Type) : Unit → Type :=
    fun _ => ι → F

/-- Provides a default OracleInterface instance that leverages
  the oracle statement defined above. The oracle simply applies
  the function `f : ι → F` to the query input `i : ι`,
  producing the response. -/
instance {ι : Type} : OracleInterface (OracleStatement ι F ()) := OracleInterface.instFunction

/-- STIR relation: the oracle's output is δᵣ-close to a Reed-Solomon codeword
  of degree at most `degree` over domain `φ`, within error `err`.
-/
def stirRelation
    {F : Type} [Field F] [Fintype F] [DecidableEq F]
    {ι : Type} [Fintype ι] [Nonempty ι]
    (degree : ℕ) (φ : ι ↪ F) (err : ℝ≥0)
    : Set ((Unit × ∀ i, (OracleStatement ι F i)) × Unit) :=
  fun ⟨⟨_, oracle⟩, _⟩ => δᵣ(oracle (), ReedSolomon.code φ degree) ≤ err

end MainTheorem

section RBRSoundness

open LinearCode

end RBRSoundness

end StirIOP

/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexander Hicks
-/

import ArkLib.Data.CodingTheory.ListDecodability
import ArkLib.Data.CodingTheory.InterleavedCode

/-!
# Extension fields and extension codes (ABF26 §2.6)

Definitions and one external-admit lemma from ABF26 §2.6 (Arnon-Boneh-Fenzi,
*Open Problems in List Decoding and Correlated Agreement*, 2026, page 11):
extension-field presentations, extension codes obtained by base-change, and the
relation `|Λ(C_F, δ)| = |Λ(C_B^e, δ)|` between the list size of an extension code
and the list size of the corresponding interleaved base code.

## Main definitions

- `ExtensionFieldPresentation` (D2.19): tuple `(B, F, e, ψ, φ)` packaging a field
  embedding `ψ : B ↪ F` of dimension `e` together with a `B`-linear isomorphism
  `φ : F ≃ B^e`.
- `CodingTheory.extensionCode` (D2.20): the extension code `C_F : F^k → F^n`
  obtained from a `B`-linear code `C_B : B^k → B^n` via an `ExtensionFieldPresentation`.

## Main statements (external admits)

- `CodingTheory.lambda_extensionCode_eq_lambda_interleaved` (L2.21, [BCFW25 Lem D.3]):
  `|Λ(C_F, δ)| = |Λ(C_B^≡e, δ)|`.

## References

- [ABF26] Arnon-Boneh-Fenzi. *Open Problems in List Decoding and Correlated Agreement*.
  2026.
- [BCFW25] Bordage-Chiesa-Fenzi-Wahby. Lemma D.3.

(The distance equality `δ_min(C_F) = δ_min(C_B)`, referenced in the L2.21 paragraph
context, is from a separate paper not formalised in this file.)
-/

set_option linter.unusedFintypeInType false
set_option linter.unusedDecidableInType false

namespace CodingTheory

open scoped NNReal
open ListDecodable

/-- **ABF26 Definition 2.19.** An *extension field presentation* is a tuple
`(B, F, e, ψ, φ)` where:

- `B` and `F` are fields,
- `ψ : B → F` is an injective field homomorphism,
- `e : ℕ` is the dimension of `F` as a `B`-vector space,
- `φ : F ≃ₗ[B] (Fin e → B)` is a `B`-linear isomorphism.

We package these as a structure rather than a tuple for ergonomic access at use
sites. The "systematic" predicate (paper: `φ(ψ(x)) = (x, 0, …, 0)`) is the
optional `systematic` field. -/
structure ExtensionFieldPresentation (B F : Type) [Field B] [Field F] where
  /-- The dimension `e := dim_B F`. -/
  e : ℕ
  /-- The base-field embedding `ψ : B ↪ F`. -/
  ψ : B →+* F
  /-- Injectivity of `ψ` (`ψ` is a *non-trivial* ring hom between fields). -/
  ψ_injective : Function.Injective ψ
  /-- The `B`-linear isomorphism `φ : F ≃ B^e`. The `B`-module structure on `F`
      comes from `ψ` via `letI := ψ.toAlgebra`. The Lean-side equivalence is
      packaged via a `Module` instance on `F` provided at the use site. -/
  φ : F → Fin e → B
  /-- Mirror map `φ⁻¹`. -/
  φ_inv : (Fin e → B) → F
  /-- Left inverse. -/
  φ_left_inv : Function.LeftInverse φ_inv φ
  /-- Right inverse. -/
  φ_right_inv : Function.RightInverse φ_inv φ

namespace ExtensionFieldPresentation

variable {B F : Type} [Field B] [Field F]

/-- A presentation is *systematic* if `φ(ψ(x)) = (x, 0, …, 0)` for every `x : B`.
This makes the base-field copy of `B` inside `F` align with the first coordinate.
Requires `P.e ≥ 1` for the "first coordinate" to exist; we sidestep the
`Fin P.e` typeclass requirement by indexing on `i.val`. -/
def IsSystematic (P : ExtensionFieldPresentation B F) : Prop :=
  ∀ x : B, P.φ (P.ψ x) = fun i => if i.val = 0 then x else 0

/-- The `i`-th coordinate `φᵢ : F → B` of an extension-field presentation. Applied
componentwise to vectors in the paper. -/
def coord (P : ExtensionFieldPresentation B F) (i : Fin P.e) : F → B :=
  fun x => P.φ x i

end ExtensionFieldPresentation

/-- **ABF26 Definition 2.20.** The *extension code* `C_F : F^k → F^n` associated to a
linear code `C_B : B^k → B^n` via an extension-field presentation. Defined on a
vector `v : ι → F` by

  `v ∈ C_F  ↔  ∃ c_B : ι → Fin e → B, (∀ i, c_B i ∈ projections of v) ∧`
  `              (∀ j : Fin e, (fun i => c_B i j) ∈ C_B)`

i.e. each of the `e` coordinate-projections of `v` lies in `C_B`. We express the
codeword set; the underlying `Submodule F (ι → F)` structure follows by closure of
`C_B` under linear combinations, but we keep the `Set`-level definition for direct
comparison with the paper's encoder shape. -/
def extensionCode {ι : Type} [Fintype ι]
    {B F : Type} [Field B] [Field F]
    (P : ExtensionFieldPresentation B F)
    (C_B : Set (ι → B)) : Set (ι → F) :=
  { v : ι → F | ∀ j : Fin P.e, (fun i => P.coord j (v i)) ∈ C_B }

/-- **ABF26 Lemma 2.21 [BCFW25 Lemma D.3].** List size of an extension code equals the
list size of the corresponding interleaved base code. Let `C_B : B^k → B^n` be a
linear code and `P` be an extension-field presentation. For every `δ ∈ (0, 1)`:

  `|Λ(C_F, δ)| = |Λ(C_B^≡e, δ)|`

where `C_F` is the extension code (D2.20) and `C_B^≡e` is the `e`-fold interleaved
base code (D2.9). Admitted as an external result. -/
theorem lambda_extensionCode_eq_lambda_interleaved
    {ι : Type} [Fintype ι] [Nonempty ι] [DecidableEq ι]
    {B F : Type} [Field B] [Fintype B] [DecidableEq B]
    [Field F] [Fintype F] [DecidableEq F]
    (P : ExtensionFieldPresentation B F)
    (C_B : Set (ι → B)) (δ : ℝ) (_hδ_pos : 0 < δ) (_hδ_lt : δ < 1) :
    Lambda (extensionCode P C_B) δ =
      Lambda (Code.interleavedCodeSet (κ := Fin P.e) C_B)
        δ := by
  sorry -- ABF26-L2.21; external admit [BCFW25 Lem D.3].

end CodingTheory

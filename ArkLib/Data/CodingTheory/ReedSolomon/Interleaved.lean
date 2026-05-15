/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexander Hicks
-/

import ArkLib.Data.CodingTheory.ReedSolomon
import ArkLib.Data.CodingTheory.InterleavedCode

/-!
# Interleaved Reed-Solomon codes (ABF26 §2.4)

ABF26 Definition 2.13: the `s`-interleaved Reed-Solomon code
`IRS[F, L, k, s] := (RS[F, L, k/s])^≡s`. Each codeword is an `s`-tuple of base RS
codewords, arranged column-wise.

## Main definitions

- `ReedSolomon.Interleaved.irsCode` — ABF26 Definition 2.13.

## Main lemmas

- `ReedSolomon.Interleaved.dim_irsCode` — `Module.finrank F (irsCode domain k s) = s · (k/s)`
  (admitted; needs a `LinearEquiv` to `Fin s → (RS code)` + `Module.finrank_pi`).

## References

- [ABF26] Arnon-Boneh-Fenzi. *Open Problems in List Decoding and Correlated Agreement*.
  2026. §2.4 Definition 2.13.
-/

set_option linter.unusedFintypeInType false
set_option linter.unusedDecidableInType false
set_option linter.unusedSectionVars false

namespace ReedSolomon
namespace Interleaved

/-- **ABF26 Definition 2.13.** The `s`-interleaved Reed-Solomon code:

  `IRS[F, L, k, s] := (RS[F, L, k/s])^≡s`

Each codeword is an `s`-tuple of base RS codewords arranged column-wise. The carrier is
`Code.interleavedCodeSet (RS[F, L, k/s])`; closure under addition and scalar
multiplication follows from the same closure of the underlying RS code applied
column-by-column.

**Submodule structure.** Returns `Submodule F (ι → Fin s → F)` (equivalently
`ModuleCode ι F (Fin s → F)`) directly, so downstream theorems (e.g. T4.14) consume
it as an F-linear code without an existential wrap.

**Rounding convention.** The paper writes `k/s` and implicitly assumes `s ∣ k` so that
the message length divides cleanly into `s` blocks of size `k/s`. In Lean `k / s` is
Nat truncated division, which silently rounds when `s ∤ k`. Downstream theorems quoting
the paper directly (e.g. `dim(IRS) = k`) should add an explicit `s ∣ k` hypothesis at
the use site; we keep the definition itself unguarded so degenerate parameter regimes
type-check uniformly. -/
noncomputable def irsCode {ι : Type} [Fintype ι] [DecidableEq ι]
    {F : Type} [Field F] [DecidableEq F]
    (domain : ι ↪ F) (k s : ℕ) : Submodule F (ι → Fin s → F) :=
  (ReedSolomon.code domain (k / s)) ^⋈ (Fin s)

/-- **Dimension of `irsCode`.** Equal to `s · (k / s)` — the interleave multiplies the
underlying RS code's dimension by the interleaving factor.

Requires `k / s ≤ Fintype.card ι` for the underlying RS code to attain its full
dimension `k / s` (the Singleton-tight regime); the bound holds with equality in this
regime. -/
lemma dim_irsCode {ι : Type} [Fintype ι] [Nonempty ι] [DecidableEq ι]
    {F : Type} [Field F] [DecidableEq F]
    (domain : ι ↪ F) (k s : ℕ)
    (_h_rs_full : k / s ≤ Fintype.card ι) :
    Module.finrank F (irsCode domain k s) = s * (k / s) := by
  -- `irsCode domain k s = (RS code) ^⋈ (Fin s)`, an F-submodule of `ι → Fin s → F`.
  -- The carrier is `{V : Matrix ι (Fin s) F | ∀ j, V.transpose j ∈ RS}`. As an
  -- F-module, this is isomorphic to `Fin s → (RS code)` (each column independent).
  -- Hence `finrank = Fintype.card (Fin s) · finrank (RS code) = s · (k/s)`.
  --
  -- The proof needs:
  -- 1. A LinearEquiv `irsCode ≃ₗ[F] (Fin s → RS code)`.
  -- 2. `Module.finrank_pi` + `Fintype.card_fin`.
  -- 3. `LinearCode.dim` of RS = `k/s` (Mathlib/ArkLib has this when `k/s ≤ |ι|`).
  --
  -- Constructing (1) requires picking the right `LinearEquiv` between the
  -- interleavedCodeSet Submodule and the Pi-of-Submodule. This is mechanical
  -- but tedious. Admitted with sketch.
  sorry -- in-tree; LinearEquiv `irsCode ≃ₗ[F] (Fin s → RS code)` + `Module.finrank_pi`.

end Interleaved
end ReedSolomon

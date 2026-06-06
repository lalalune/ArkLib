# Issue #24 FRI/STIR Soundness Residual Audit

Date: 2026-06-06

Scope:

- `ArkLib/ProofSystem/Fri/Spec/Soundness.lean`
- `ArkLib/ProofSystem/Stir/ProximityGap.lean`
- `ArkLib/ProofSystem/Stir/Combine.lean`
- `ArkLib/ProofSystem/Stir/MainThm.lean`

## Current residual surfaces

### FRI soundness accounting

`ArkLib/ProofSystem/Fri/Spec/Soundness.lean` currently contains candidate
accounting definitions:

- `roundError`
- `queryRoundError`
- `queryError`
- `totalError`

The module documentation explicitly marks these as accounting placeholders
pending sequential-composition infrastructure. There is no local proof hole to
discharge in this file; the missing work is a soundness theorem tying the
per-round BCIKS20 proximity-gap and query-consistency quantities to the actual
FRI verifier failure probability.

### STIR proximity gap

`ArkLib/ProofSystem/Stir/ProximityGap.lean` is intentionally inert today. Its
audit comments record two separate blockers:

1. The original unconstrained-generator statement is false. A zero generator
   makes the combined word identically zero, so the probability hypothesis can
   hold for arbitrary inputs without yielding the claimed common agreement set.
   The file therefore includes the `_hGen` repair requiring the monomial /
   Vandermonde generator shape.
2. The repaired monomial statement still depends on the BCIKS20 correlated
   agreement chain in the square-root-rate list-decoding regime. The blocking
   base case is `RS_correlatedAgreement_affineLines` in
   `ArkLib/Data/CodingTheory/ProximityGap/BCIKS20/AffineLines/Main.lean`.

The clean unique-decoding-regime result does not cover the STIR hypothesis
`δ < 1 - Bstar ρ`, so closing this surface requires the list-decoding branch,
not just a local restatement.

### STIR combine theorem

`ArkLib/ProofSystem/Stir/Combine.lean` exposes `combine_theorem`, but the theorem
requires `ProximityGap.StrictCoeffPolysResidual`. That residual is the strict
coefficient-polynomial bridge needed to feed the repaired BCIKS20 proximity gap.
As a result, `combine_theorem` remains downstream of the same affine-lines /
spaces / curves correlated-agreement proof chain.

### STIR main theorem and RBR soundness

`ArkLib/ProofSystem/Stir/MainThm.lean` has two documented residual surfaces:

- `stir_main`, the full STIR IOPP construction theorem.
- `stir_rbr_soundness`, the round-by-round soundness theorem.

Both require constructing an actual `VectorIOP` protocol object and proving the
round-by-round security bounds. The directory currently contains algebraic
building blocks, but not the protocol construction and sequential soundness
assembly needed by these theorem statements. Their proximity-gap inputs also
flow through `Combine.combine_theorem`, so they remain gated on the BCIKS20
list-decoding-regime correlated-agreement work.

## Audit command

```sh
rg -n 'accounting placeholders|sorryAx-tainted|Honest residual|Open proof|residual|placeholder' \
  ArkLib/ProofSystem/Fri ArkLib/ProofSystem/Stir
```

Observed hits on 2026-06-06:

```text
ArkLib/ProofSystem/Fri/Spec/Soundness.lean:19:soundness theorem — they are accounting placeholders pending the sequential
ArkLib/ProofSystem/Stir/MainThm.lean:150:  -- full chain). Honest residual: this is a major protocol-formalisation effort gated on (1) the
ArkLib/ProofSystem/Stir/MainThm.lean:242:  -- construction scaffolding exists yet. Honest residual: gated on AffineLines/Main.lean:40
ArkLib/ProofSystem/Stir/ProximityGap.lean:41:  STATUS (audit 2026-06-04, branch arklib-sorry-fixes). Open proof. Two independent,
ArkLib/ProofSystem/Stir/ProximityGap.lean:68:  Honest residual: close `AffineLines/Main.lean:40` (Thm 5.1, list-decoding regime), which
```

## Remaining proof tracks

1. FRI: add sequential-composition soundness infrastructure, then prove that
   `totalError` bounds the verifier failure probability.
2. BCIKS20/STIR proximity gap: close the affine-lines correlated-agreement
   theorem in the list-decoding regime, then lift through affine spaces and
   curves to the repaired monomial proximity-gap statement.
3. STIR combine: discharge `StrictCoeffPolysResidual` and reconnect
   `combine_theorem` to the repaired proximity gap.
4. STIR main theorem: build the concrete `VectorIOP` object and prove the
   round-by-round security assembly using the closed combine/proximity-gap
   inputs.

This audit does not close the mathematical residuals. It makes the remaining
surfaces explicit and separates the work into dependency tracks so the issue is
not mistaken for a collection of local `sorry` cleanups.

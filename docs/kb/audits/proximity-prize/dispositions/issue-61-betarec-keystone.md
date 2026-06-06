# Issue #61: betaRec-to-hcoeffPoly keystone assembly

This issue owns the final non-vacuous Proximity Prize integration gate:

```text
betaRec + Section 5 extraction data
  -> CurveCoeffPolys
  -> bundled hcoeffPoly
  -> BCIKS20 curve correlated agreement front door
```

## Current in-tree state

The honest assembly route is `ArkLib.ToMathlib.CorrelatedAgreementListDecodingClosed`.

The key non-vacuous step is:

```lean
ArkLib.CorrelatedAgreementListDecodingClosed.curveCoeffPolys_of_section5Data
```

That theorem calls:

```lean
ArkLib.BetaToCurveCoeffPolys.curveCoeffPolys_of_betaRec
```

so the proof route consumes the real `betaRec` machinery, including the matching-set large-root
path through `tail_zero_of_betaRec_embedding_zero` and
`betaRec_embedding_eq_zero_of_matchingSet_large`. It does not assume a packaged conclusion
equivalent to the front-door `hcoeffPoly` witness.

The bundling step is:

```lean
ArkLib.CorrelatedAgreementListDecodingClosed.hcoeffPoly_witness_of_section5Data
```

which turns the derived `CurveCoeffPolys` data into the `∃ B : ℕ -> Polynomial F` shape consumed by
the curve front door.

## Remaining gate

The remaining work is not to prove another wrapper from an `hcoeffPoly`-shaped assumption. The live
gap is to supply `Section5StrictData` from the in-tree Section 5 context:

- matching-point data and matching-set cardinality/weight bounds;
- the valid gamma/substitution representative data, including the F1 recentering issue;
- the degree-X bound and decoded-family specialization bridge;
- the GS-factor divisibility input `Hlift H ∣ R`;
- the L13 betaRec drop-in for the legacy `β_regular` path.

Those are the inputs to `curveCoeffPolys_of_betaRec`; the per-coefficient polynomial conclusion is
derived after those inputs exist.

## Anti-vacuity check

Do not replace the remaining gate with `Section55Output`, `hcoeffPoly`, or any structure that already
contains:

```lean
∀ P, ... -> ∃ B, ...
```

as a field. That reintroduces the F4 trap documented in `GRIND-LEDGER.md`.

The proof-gap index now points to #61 for this apex integration surface so the issue is not hidden
under local residual tickets.

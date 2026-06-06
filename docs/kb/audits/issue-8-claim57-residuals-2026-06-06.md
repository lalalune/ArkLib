# Issue #8: Claim 5.7 residual surface

This note audits the current `Claim57Residuals` surface in
`ArkLib/Data/CodingTheory/ProximityGap/BCIKS20/ListDecoding/Agreement.lean`.

## Current front door

The residual bundle is still:

```lean
class Claim57Residuals (k : ℕ) (δ : ℚ) (x₀ : F)
    (h_gs : IsGSSolution (F := F) (m := m) (n := n) (k := k) Q ωs δ x₀) where
  hx0 : x₀ ∈ (Finset.univ : Finset F)
  hsep : w ∈ₗ ReedSolomonCode F k evalDomain →
    agreementFraction F evalDomain wᵥ w < 1 - δ
  hS_nonempty : pg_Rset F k δ x₀ h_gs ≠ []
  A : Finset F
  hA : A = Finset.univ
  hcount : pg_Rset_common_roots_count F k δ x₀ h_gs A
      = Finset.card A * List.length (pg_Rset F k δ x₀ h_gs)
  hlarge : pg_Rset_common_roots_count F k δ x₀ h_gs A >
      k * List.length (pg_Rset F k δ x₀ h_gs)
  hfactor : ∀ R ∈ pg_Rset F k δ x₀ h_gs,
    R ∈ (irreducible_factorization_of_gs_solution h_gs).choose_spec.choose
```

This means the residual is no longer a monolithic Claim 5.7 placeholder, but it
still packages eight facts. The hardest remaining bridge is `hfactor`: converting
membership in `pg_Rset` into membership in
`(irreducible_factorization_of_gs_solution h_gs).choose_spec.choose`.

## Partial reduction already present

The current source has a useful constructor:

```lean
Claim57Residuals.ofGraphExtractionHypotheses
```

It discharges `hx0`, `hsep`, `hS_nonempty`, `A`, `hA`, `hcount`, and `hlarge`
from `GraphExtractionHypotheses`. It still requires the factor-list bridge:

```lean
∀ R ∈ pg_Rset F k δ x₀ h_gs,
  R ∈ (irreducible_factorization_of_gs_solution h_gs).choose_spec.choose
```

The current source also exposes:

```lean
exists_factors_with_large_common_root_set_of_graphExtraction
```

This is the right front-door theorem for callers that already have
`GraphExtractionHypotheses`, because it avoids requiring an ambient
`[Claim57Residuals]` instance.

## Remaining downstream surface

Most downstream Claim 5.7 and Claim 5.8 lemmas still carry:

```lean
[Claim57Residuals (F := F) k δ x₀ h_gs]
```

The long-term cleanup is to thread `GraphExtractionHypotheses` and the explicit
factor-list bridge deeper through the file, replacing ambient residual-class
dependencies at call sites that do not need the full bundled instance.

In particular, the next useful target is to lift the later
`solution_gamma_graph_*` lemmas onto the graph-extraction front door, or to split
the factor-list bridge into a smaller named theorem that can be proved or
imported independently.

## Verification status

This audit was checked against the current anchors:

- `Claim57Residuals`
- `Claim57Residuals.ofGraphExtractionHypotheses`
- `exists_factors_with_large_common_root_set_of_graphExtraction`
- `GraphExtractionHypotheses`
- `irreducible_factorization_of_gs_solution`

Full focused Lean verification of `Agreement.lean` is currently blocked before
ArkLib targets by the manifest-pinned `CompPoly` dependency failures observed on
the clean `fork/main` checkout.

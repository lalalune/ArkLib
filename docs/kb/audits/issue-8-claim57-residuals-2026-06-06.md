# Issue #8: Claim 5.7 residual surface

This note audits the current `Claim57Residuals` surface in the BCIKS20
list-decoding agreement stack. The legacy bundle lives in
`ArkLib/Data/CodingTheory/ProximityGap/BCIKS20/ListDecoding/Agreement.lean`;
the newer discharge layers live in `ArkLib/ToMathlib/Claim57Supply.lean`,
`ArkLib/ToMathlib/Section5ConcreteJohnson.lean`, and
`ArkLib/Data/CodingTheory/ProximityGap/BCIKS20/ListDecoding/Claim57FieldDischarge.lean`.
The descended-set replacement for the legacy factor surface lives in
`ArkLib/Data/CodingTheory/ProximityGap/BCIKS20/ListDecoding/DescendedRset.lean`.
The mathlib-only discriminant/separability bridge for the good-specialization side condition lives
in `ArkLib/ToMathlib/DiscriminantSeparable.lean`.

## Legacy Front Door

The legacy class still packages eight fields:

```lean
class Claim57Residuals (k : ℕ) (δ : ℚ) (x₀ : F)
    (h_gs : ModifiedGuruswami m n k ωs Q u₀ u₁) where
  hx0 : ∀ R ∈ pg_Rset h_gs, Bivariate.evalX (Polynomial.C x₀) R ≠ 0
  hsep : ∀ R ∈ pg_Rset h_gs, (Bivariate.evalX (Polynomial.C x₀) R).Separable
  hS_nonempty : (coeffs_of_close_proximity k ωs δ u₀ u₁).Nonempty
  A : coeffs_of_close_proximity k ωs δ u₀ u₁ → Finset (Fin n)
  hA : ∀ z i, i ∈ A z → (u₀ + z.1 • u₁) i = (Pz z.2).eval (ωs i)
  hcount : ∀ z, natWeightedDegree (eval_on_Z Q z.1) 1 k < m * (A z).card
  hlarge : #(coeffs_of_close_proximity k ωs δ u₀ u₁) / natDegreeY Q > ...
  hfactor : ∀ R ∈ pg_Rset h_gs,
    R ∈ (irreducible_factorization_of_gs_solution h_gs).choose_spec.choose
```

That class shape is still used by many downstream lemmas in `Agreement.lean`, but it is no longer
the minimal mathematical frontier.

## Discharge Layers

`Agreement.lean` exposes the first API reduction:

```lean
GraphExtractionHypotheses
Claim57Residuals.ofGraphExtractionHypotheses
exists_factors_with_large_common_root_set_of_graphExtraction
```

This moves `hx0`, `hsep`, `hS_nonempty`, `A`, `hA`, `hcount`, and `hlarge` into a proved
graph-extraction side-condition package. The only extra hypothesis at that front door is the
legacy factor-list bridge `hfactor`.

`Claim57Supply.lean` then makes the graph package non-circular by using the canonical
`matching_coords_for_z` agreement set:

```lean
graphExtractionHypotheses_of_johnson
graphExtractionHypotheses_of_natCeil_johnson
claim57Residuals_of_johnson
claim57Residuals_of_natCeil_johnson
```

At this layer, `A`/`hA` are canonical, `hS_nonempty` follows from `hlarge`, and `hcount` is narrowed
to the Johnson matching-coordinate or `⌈δ * n⌉` budget.

`Section5ConcreteJohnson.lean` narrows the Johnson side further:

```lean
hcount_natCeil_of_johnson_budget
claim57Residuals_of_gsInterpolant
```

It proves that `Z`-specialization does not raise the `(1, k)` weighted degree, so the per-`z`
`hcount` follows from one `z`-independent budget:

```lean
Bivariate.natWeightedDegree Q 1 k < m * (n - ⌈δ * (n : ℚ)⌉₊)
```

`Claim57FieldDischarge.lean` is the latest field-level brick:

```lean
claim57_hfactor_irreducible_of_pg_Rset
exists_good_x₀_evalX_discr_y_ne
exists_good_x₀_X_shape_ne
exists_good_x₀_X_shape
Claim57Residuals.ofInTree
Claim57Residuals.ofInTree2
```

It proves the honest irreducibility fragment of legacy `hfactor`, proves both the original
`Z`-shape and repaired `X`-shape avoidance producers for the specialization point, and assembles
the legacy bundle from the minimal current inputs.

`DescendedRset.lean` is now the preferred Claim 5.7 factor-set route:

```lean
pg_RsetDescended
pg_RsetDescended_hfactor
pg_RsetDescended_irreducible
pg_RsetDescended_separable_FF
pg_RsetDescended_natDegree_pos
pg_RsetDescended_discr_y_ne_zero
pg_RsetDescended_comp_dvd_Q
Claim57ResidualsDescended
Claim57ResidualsDescended.ofInTree
Claim57Residuals.ofDescended
exists_factors_with_large_common_root_set_of_descended
R_descended
H_descended
claimA2_hypotheses_descended
```

The descended bundle removes `hfactor` by construction: membership in `pg_RsetDescended` is
membership in the descended primitive-separable factor list. Legacy consumers can still recover
`Claim57Residuals` through `Claim57Residuals.ofDescended`, but only under the explicit coincidence
hypothesis `pg_RsetDescended = pg_Rset`. The new front door and projections then expose the
Claim-5.7 factors and Claim-A.2 hypotheses from that descended bundle.

`DiscriminantSeparable.lean` supplies the mathlib-level payoff bridge for the `hx0` / `hsep`
side condition:

```lean
Polynomial.discr_map_of_natDegree_preserved
Polynomial.separable_of_discr_ne_zero
Polynomial.ne_zero_and_separable_of_specialized_discr_ne_zero
Polynomial.ne_zero_and_separable_of_specialized_base_discr_ne_zero
```

This proves that nonvanishing specialized discriminant data gives both nonzero specialized factors
and separability, provided the specialization preserves `natDegree`. It deliberately stays out of
the `CompPoly` `discr_y` / `evalX` stack while that layer is under repair.

## Current Minimal Surface

After the current discharge layers, the recommended descended-set path has this remaining
Claim 5.7 proof surface:

| Field | Current status |
| --- | --- |
| `hx0` / `hsep` | `hx0` is produced on both the legacy and descended routes by the `X`-shape avoidance lemmas (`exists_good_x₀_X_shape_ne`, `exists_good_x₀_X_shape_ne_descended`). The remaining separability input is the honest per-point residual `hsepPt` used by `Claim57ResidualsDescended.ofInTree`. |
| `hJohnson` | The single Johnson weighted-degree budget feeding `hcount_natCeil_of_johnson_budget`; not a class field, but still an explicit input to `claim57Residuals_of_gsInterpolant` and `Claim57Residuals.ofInTree`. |
| `hlarge` | The close-set largeness / field-size budget input. It also derives `hS_nonempty`. |
| `hfactor` | Removed on the `Claim57ResidualsDescended` path. The legacy `pg_Rset` field remains unprovable in full generality because `pg_Rset` is built from `normalizedFactors Q`, while the Eq. 5.12 list contains descended primitive-separable factors. Use `Claim57Residuals.ofDescended` only under the explicit coincidence hypothesis. |

The fields `A`, `hA`, `hcount`, and `hS_nonempty` are not the active residual surface anymore:
they are discharged through `Claim57Supply.lean` and `Section5ConcreteJohnson.lean` once the
minimal inputs above are provided.

## Remaining Downstream Surface

Most later Claim 5.7 / Claim 5.8 lemmas in `Agreement.lean` still carry the legacy class:

```lean
[Claim57Residuals (F := F) k δ x₀ h_gs]
```

The useful downstream cleanup is to route new consumers through
`Claim57ResidualsDescended.ofInTree` and the descended projections, then use
`Claim57Residuals.ofDescended` only at legacy boundaries that still need the old class under an
explicit coincidence hypothesis.

## Verification Status

This audit was checked against the current anchors:

- `Claim57Residuals`
- `GraphExtractionHypotheses`
- `Claim57Residuals.ofGraphExtractionHypotheses`
- `exists_factors_with_large_common_root_set_of_graphExtraction`
- `graphExtractionHypotheses_of_johnson`
- `claim57Residuals_of_gsInterpolant`
- `hcount_natCeil_of_johnson_budget`
- `claim57_hfactor_irreducible_of_pg_Rset`
- `exists_good_x₀_evalX_discr_y_ne`
- `exists_good_x₀_X_shape_ne`
- `exists_good_x₀_X_shape`
- `Claim57Residuals.ofInTree`
- `Claim57Residuals.ofInTree2`
- `pg_RsetDescended`
- `pg_RsetDescended_hfactor`
- `Claim57ResidualsDescended`
- `Claim57ResidualsDescended.ofInTree`
- `Claim57Residuals.ofDescended`
- `exists_factors_with_large_common_root_set_of_descended`
- `R_descended`
- `H_descended`
- `claimA2_hypotheses_descended`
- `Polynomial.discr_map_of_natDegree_preserved`
- `Polynomial.separable_of_discr_ne_zero`
- `Polynomial.ne_zero_and_separable_of_specialized_discr_ne_zero`
- `Polynomial.ne_zero_and_separable_of_specialized_base_discr_ne_zero`

This refresh was docs-only and anchor-checked against current `fork/main`; no broad Lean build was
run for this audit update.

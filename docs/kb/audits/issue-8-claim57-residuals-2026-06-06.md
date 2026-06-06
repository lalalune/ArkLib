# Issue #8: Claim 5.7 residual surface

This note audits the current `Claim57Residuals` surface in the BCIKS20
list-decoding agreement stack. The legacy bundle lives in
`ArkLib/Data/CodingTheory/ProximityGap/BCIKS20/ListDecoding/Agreement.lean`;
the newer discharge layers live in `ArkLib/ToMathlib/Claim57Supply.lean`,
`ArkLib/ToMathlib/Section5ConcreteJohnson.lean`, and
`ArkLib/Data/CodingTheory/ProximityGap/BCIKS20/ListDecoding/Claim57FieldDischarge.lean`.
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
Claim57Residuals.ofInTree
```

It proves the honest irreducibility fragment of `hfactor`, proves the discriminant-avoidance
substrate for the specialization point, and assembles the legacy bundle from the minimal current
inputs.

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

After the current discharge layers, the remaining Claim 5.7 proof surface is:

| Field | Current status |
| --- | --- |
| `hx0` / `hsep` | Reduced to discriminant-nonvanishing plus the mathlib bridge in `DiscriminantSeparable.lean`. The remaining bridge is the same-variable `CompPoly` wiring: match the `Claim57FieldDischarge` producer to the `evalX (Polynomial.C x₀)` consumer shape, account for the `discr_y = unit * discr` normalization, and supply the explicit `natDegree`-preservation / leading-coefficient-survival side condition. The previous natural-looking `X`/`Z` commutation is documented as false. |
| `hJohnson` | The single Johnson weighted-degree budget feeding `hcount_natCeil_of_johnson_budget`; not a class field, but still an explicit input to `claim57Residuals_of_gsInterpolant` and `Claim57Residuals.ofInTree`. |
| `hlarge` | The close-set largeness / field-size budget input. It also derives `hS_nonempty`. |
| `hfactor` | Not provable as currently stated in full generality: `pg_Rset` is built from `normalizedFactors Q`, while the Eq. 5.12 list contains descended primitive separable factors. The proven fragment is `claim57_hfactor_irreducible_of_pg_Rset`. |

The fields `A`, `hA`, `hcount`, and `hS_nonempty` are not the active residual surface anymore:
they are discharged through `Claim57Supply.lean` and `Section5ConcreteJohnson.lean` once the
minimal inputs above are provided.

## Remaining Downstream Surface

Most later Claim 5.7 / Claim 5.8 lemmas in `Agreement.lean` still carry:

```lean
[Claim57Residuals (F := F) k δ x₀ h_gs]
```

The useful downstream cleanup is to thread `Claim57Residuals.ofInTree` or the explicit
`hx0`/`hsep`/`hJohnson`/`hlarge`/`hfactor` inputs to later front doors, replacing ambient
`[Claim57Residuals]` dependencies where the full legacy instance is only a transport device.

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
- `Claim57Residuals.ofInTree`
- `Polynomial.discr_map_of_natDegree_preserved`
- `Polynomial.separable_of_discr_ne_zero`
- `Polynomial.ne_zero_and_separable_of_specialized_discr_ne_zero`
- `Polynomial.ne_zero_and_separable_of_specialized_base_discr_ne_zero`

Full focused Lean verification of these modules is currently blocked before the BCIKS20 targets by
the live manifest-pinned `CompPoly` dependency failures on `fork/main`.

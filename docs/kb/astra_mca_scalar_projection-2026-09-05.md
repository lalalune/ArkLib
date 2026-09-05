# From residual directions to scalar challenges and polynomial agreements

The four-generator construction now has a formal scalar projection over the
certified production field. `production_scalar_projection` supplies one
partition, one polynomial basis, and two coefficient vectors whose 1073741828
slot ratios are finite and pairwise distinct. The evaluation lemmas identify
these ratios with polynomial agreements and exclude a degree-bounded
explanation on the same enlarged core. The subsequent
[production assembly](astra_mca_production_upper-2026-09-05.md) checks the
actual events, probability, and upper threshold locally and in CI. **The universal
lower bound remains open.**

Sources:

- [Polynomial evaluations and supports](../../scripts/probes/astra_mca_evaluations.lean).
- [Finite-field scalar projection](../../scripts/probes/astra_mca_scalar_projection.lean).
- [Production specialization](../../scripts/probes/astra_mca_production_basis.lean).

## Evaluations and the same support

For a coefficient vector v, the F candidate is

```text
F(v) = v0*F0 + v1*F1 + v2*X*F0 + v3*X*F1.
```

The G candidate has the same form. Each has degree at most D+1. The three
owners are 0, F(v), and G(v); the received value is F(v) on S and zero
elsewhere. The row at each absent-core slot is exactly received minus owner.
Received values respect affine combinations of coefficient vectors.

The three joint cores are A union B union I, A union S, and B union S. Their
sizes are proved from disjointness. On each core the received value agrees
with its owner for every coefficient vector.

Given u0,u1 and a slot row r with r(u1) nonzero, set c=-r(u0)/r(u1).
`slot_cancellation` proves agreement at that slot for the received combination
u0+c*u1 and its owner polynomial. A nonzero denominator also proves that the
slot lies outside its core.

Let U be any subset of that core with |U|>D+1. Any polynomial of degree at most
D+1 agreeing with the second received word on U must equal the second owner
polynomial, by root counting. It therefore cannot agree at the extra slot.
`core_insert_witness` combines the following statements on the same support:

- inserting the slot increases its size from |U| to |U|+1;
- the scalar combination agrees with its owner on every point of this support;
- no polynomial of the required degree explains even the second received word
  on this support, and hence no pair can explain both words there.

## Projection by univariate root avoidance

For a row r=(r0,r1,r2,r3), restrict its functional to the moment curve
(1,t,t^2,t^3). The resulting polynomial has degree at most three and is
nonzero whenever r is nonzero. A product of M such polynomials has degree at
most 3M. If 3M<|F|, root counting supplies a common nonroot, hence a coefficient
vector u1 with every denominator nonzero.

For each ordered pair of distinct rows, form

```text
r_j(u1)*r_i - r_i(u1)*r_j.
```

Projective distinctness makes this row nonzero. A second root-avoidance step
chooses u0 making every cross-evaluation nonzero. Consequently the ratios
-r_i(u0)/r_i(u1) are injective.

This version uses the sufficient field bounds 3M<|F| and 3M^2<|F|. It requires
a larger field than the written hyperplane argument, but the actual
production field satisfies both bounds. The arithmetic is checked in
`production_moment_curve_arithmetic`; no field or domain is enumerated and
no analytic assumption is introduced.

## Verification and limits

Run the [compilation helper](../../scripts/check-mca-production-basis.sh) from
a Lake environment with the matching pinned imports cached:

```sh
bash /absolute/path/to/arklib/scripts/check-mca-production-basis.sh /tmp/mca-proof-lib
```

The helper compiles the certificate, basis, rows, evaluations, projection,
and production wrapper in dependency order. All 69 named axiom reports pass
local Lean 4.30.0-rc2 with only permitted standard axioms and no compiler
warnings: 3 certificate, 31 basis, 9 row, 13 evaluation/support, 6 projection,
and 7 production theorems. The
[auxiliary workflow](../../.github/workflows/proximity-strip-proof.yml)
audits them on both supported toolchains, together with the other auxiliary
proofs, and rejects warnings, errors, and nonstandard axioms.

The preceding residual-row checkpoint `f5f60954060c9f0ec8645e2b7d01f582279b9c7e`
passed both supported pins in
[run 33988862034](https://github.com/lalalune/ArkLib/actions/runs/33988862034).
That run does not cover these new evaluation and projection proofs; their
own revision must pass the same checks.

The [general event bridge](astra_mca_event_bridge-2026-09-05.md) now transports
polynomial supports into the repository's actual indexed RS `mcaEvent`.
The subsequent [production assembly](astra_mca_production_upper-2026-09-05.md)
now chooses those supports, instantiates the bridge, and derives the probability
and threshold consequence in local Lean. This construction proves the upper bound
357913942/2^30, one Hamming step weaker than the previously computed upper
bound. It does not improve that number or prove the matching universal bound.

The complete 69-report chain passed both pins at
`59f6cee640546b7185656fa370353c0c182ea5ae` in
[run 33989276174](https://github.com/lalalune/ArkLib/actions/runs/33989276174).

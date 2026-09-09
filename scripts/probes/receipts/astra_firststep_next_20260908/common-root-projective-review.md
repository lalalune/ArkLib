# Review: common-root inverse and the projective API

2026-09-08. Read-only review of `08-singleton/common-root-inverse.md` and
`ArkLib/Data/CodingTheory/ProximityGap/MCAProjectiveEquivariance.lean`.

## Common-root inverse: approved as a written argument

No gap found in the claim that three distinct parameters with nonzero
decoders sharing k-2 high-core roots force a distinct joint source with
core at least t-1, for s>=6.

After choosing exactly k-2 shared roots, the factor G is nonzero at
every outside point automatically, since its roots were chosen inside
the high core. Each decoder divided by G is linear. Three selected
supports omit at most three outside-point incidences in total; at least
two outside points are common to all three. The scalar-interpolated
third decoder's residual quotient therefore has two roots and vanishes.

A point appearing in at least two supports then gives two independent
scalar equations and hence joint agreement. At most one outside point
can appear fewer than twice, since each such point costs at least two
of the three possible omissions. This proves the stated t-1 core bound.

The final safety consequence uses the near-source theorem's s>=94,
which holds in production. It should not be read as a safety theorem
for every s>=6. The source text explicitly applies that consequence at
production, so no correction is required. The projective-decoder
corollary is valid when direction means scalar-proportional normalized
nonzero decoder polynomials; those share at least k-2 high-core roots.

## Projective sparse proof: API agreement confirmed

The actual `mcaEventProj` definition, lines 76–80, retains exactly the
same witness set S and the same `not pairJointAgreesOn` clause as the
original event. Only the projected word is homogenized. At
`delta=(s+1)/n`, `(1-delta)*n=3s-1=t`, so the real-valued size condition
is precisely the integer support threshold used in the written proof.

`slotCoords` uses `(1,gamma)` for a finite slot and `(0,1)` for infinity;
the zero coefficient pair never occurs. `mcaEventProj_row_mix` requires
nonzero determinant, maps coefficients by row multiplication, and
preserves S unchanged. `mcaEventProj_translate` handles codeword shifts.
`badSlotCount_row_mix` proves projective census invariance, and
`badSlotCount_eq_affine_add_infty` is exactly the finite-count-plus-one-
indicator decomposition used in our bound.

Thus the projective sparse theorem's `L*m+1` count and its support
convention agree with the actual source API. No Lean instantiation or
new kernel check is claimed.

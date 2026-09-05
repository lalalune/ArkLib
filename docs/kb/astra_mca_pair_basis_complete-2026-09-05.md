# Pair-region basis completeness and the two-deletion collision problem

The two-deletion construction already spans every polynomial pair with its
prescribed regions and degree cap. Changing this basis cannot remove any
projective collision. Thirteen statements in the
[Lean module](../../scripts/probes/astra_mca_pair_basis_complete.lean)
pass local Lean 4.30.0-rc2 with only standard axioms and no diagnostics.
Both CI pins are configured to require the same thirteen reports.

This limits a proposed shortcut to the sharper upper bound. It does not
improve either bound, prove the universal lower bound, or solve the prize.
The existing full Lean upper bound remains `357913942/1073741824`; the
[production count](astra_mca_production_count-2026-09-05.md) supports the
sharper `357913941/1073741824` through a computational distinctness count.
The latter distinctness argument is still not Lean-formalized.

## Exact polynomial statement

Let A, B, S be finite subsets of a field. A pair-region basis has columns
`(f0,g0)` and `(f1,g1)`, each polynomial of degree at most D, with f vanishing
on A, g vanishing on B, and f=g on S. Its determinant is exactly

```text
Delta = f0*g1 - f1*g0 = c Z,
Z = product_(x in A union B union S) (X-x), c != 0.
```

Consider any pair `(p,q)` of degree at most T with the same vanishing and
agreement conditions. Its Cramer numerators

```text
N0 = p*g1 - q*f1, N1 = q*f0 - p*g0
```

vanish on the whole union and have degree at most T+D. Divide by cZ to
obtain unique polynomial coefficients u,v satisfying

```text
p = u*f0 + v*f1, q = u*g0 + v*g1,
natDegree(u), natDegree(v) <= T+D-|A union B union S|.
```

The subtraction in the Lean bound is truncated natural subtraction. If
T+D is at most the union cardinality, u and v are constants, including
the zero-polynomial case. The proof uses the exact determinant and root
divisibility; it assumes no unproved independence or cancellation bound.

Any two bases with the same regions and degree cap, when `2D <= |union|`,
differ by an invertible constant matrix. For residual rows r and s, the
wedge after the change of basis is the old wedge times the matrix
determinant. Thus vanishing of the wedge is unchanged. The Lean file
proves the constant change of basis and this wedge equivalence separately;
it does not introduce a new residual-slot API.

## Production degree and core budgets

Write `n=1073741824` and let the code polynomial degree cap be `w=536870911`.
The basis existence construction is in the
[polynomial basis module](../../scripts/probes/astra_mca_polynomial_basis.lean).
The new production specializations take such a basis as input.

| Deleted points | A, B cardinalities | S cardinality | Basis D | Pair cap T | Union cardinality | Coefficient cap |
| --- | --- | --- | --- | --- | --- | --- |
| 2 | 357913940 each | 357913942 | 536870911 | 536870911 | 1073741822 | 0 |
| 4 | 357913939 each | 357913942 | 536870910 | 536870911 | 1073741820 | 1 |

Two deletions therefore leave only the constant span of two columns.
Four deletions allow their X multiples, giving four generators. This
explains the extra degree room in the existing
[production projection](astra_mca_production_basis-2026-09-05.md).
It does not create additional degree room at two deletions.

There is also an exact incidence limit. With region sizes a,b,s, private
size i, and `a+b+s+i=n`, the three core sizes are

```text
a+b+i, a+s, b+s.
```

If all are at least t, summing gives `3t+i <= 2n`. At the sharper radius,
one extra agreement per core requires `t=715827882`, forcing `i <= 2`.
Thus the four-private-coordinate, one-extra-agreement construction cannot
reach that radius just by rearranging its region sizes. Other constructions,
partitions, or strategies using multiple extra agreements remain open.

## Independent exact collision controls

The [finite checker](../../scripts/probes/astra_mca_pair_basis_complete_check.py)
reconstructs the degree-seven polynomial pairs on 16 nodes by dense Lagrange
interpolation and exact division. It checks the degree caps, the exact
degree-fourteen locator determinant, all shared core values, and every
nonzero residual row. It does not obtain its rows from the compact recursive
evaluator. All three cores have ten points and there are eighteen slots.

| Field prime | Distinct projective directions among 18 slots |
| --- | --- |
| 17 | 13 |
| 97 | 17 |
| 113 | 17 |
| 193 | 18 |
| 241 | 17 |
| Production prime | 18 |

For F97, with primitive sixteenth root 8, the absent-owner residual at
exponent 4 is `(67,1)`, while the one at exponent 10 is `(71,72)`.
Both are nonzero and `67*72-71=4753=49*97`, so they collide projectively.
The JSON output includes both full polynomial columns and the two slots.
This refutes injectivity over every field admitting sixteenth roots.

The p-sweep is essential: the collision is absent in the production-field
16-node control. None of these controls proves or disproves injectivity on
the production domain of 2^30 nodes, or a universal prize statement. In
particular, the Lean basis theorem does not itself prove that a collision
exists over the production field; it says that any existing collision is
preserved by a permitted basis change.

## Reproduction

```bash
python3 scripts/probes/astra_mca_pair_basis_complete_check.py
bash scripts/check-mca-production-basis.sh /tmp/proximity-aux-lib
```

Run the second command from a Lake project with the matching pinned
Mathlib dependencies cached, as described in the
[quickstart](../wiki/quickstart.md). The new Lean source SHA-256 is
`581959200e7f5376fb8fcf70c7947fb76ab8db7dc74a89b9b0369f2f71daa2f8`.
The helper compiles this file after its polynomial-basis dependency.
The CI audit requires 154 reports on ArkLib and 132 on the companion pin,
including these thirteen. Required report counts are validation coverage,
not a measure of progress toward a prize solution.

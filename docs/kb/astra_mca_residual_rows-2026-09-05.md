# Residual directions for the four-generator construction

The [residual-row proof](../../scripts/probes/astra_mca_residual_rows.lean)
establishes nonzero, pairwise projectively distinct rows for every absent-core
slot of the [constructed polynomial basis](astra_mca_polynomial_basis-2026-09-05.md).
The [production specialization](astra_mca_production_basis-2026-09-05.md)
uses the same basis over the certified field and gives exactly 1,073,741,828
such rows. **These are residual directions, not yet a Lean proof of distinct
bad challenges, MCA events, their probability, or a threshold bound.**

## Construction and proof

Write A for the region where the F components vanish, B for the region where
the G components vanish, S for their agreement region, and I for the four
deleted points. The slot set consists of

```text
owner 0 at points in S
owner 1 at points in B union I
owner 2 at points in A union I.
```

The corresponding base rows are (F0,F1), (-F0,-F1), and (-G0,-G1), evaluated
at the slot coordinate x. Each base row (b,c) is lifted to (b,c,x*b,x*c).

The determinant identity makes these rows nonzero. Outside A union B union S,
the determinant does not vanish. At a point inside that union, its locator has
a simple root: all four component values vanishing would also force the
derivative to vanish, a contradiction. The basis root and agreement
conditions then exclude a zero base row at each slot.

If two nonzero lifted rows are proportional, comparing the first two
coordinates with their X multiples shows that their evaluation coordinates
are equal. At an ordinary pair-region point there is only one slot. At a
private point there are two, but their base-row determinant is nonzero.
Thus distinct slots cannot give proportional rows.

The slot count is |A|+|B|+|S|+2|I|. At the concrete production parameters this
is 357913939+357913939+357913942+8 = 1073741828. The theorem
`production_residual_rows` constructs a single partition and basis satisfying
the domain, size, nonzero-row, and distinctness conclusions together.

## Verification and remaining work

The module prints axiom reports for nine supporting theorems. The production
wrapper adds the concrete specialization. Run

```sh
bash /absolute/path/to/arklib/scripts/check-mca-production-basis.sh /tmp/mca-proof-lib
```

from a Lake environment with the matching Mathlib imports cached. The helper
compiles the prime certificate, basis, rows, and production wrapper in order.
The [auxiliary workflow](../../.github/workflows/proximity-strip-proof.yml)
checks both supported toolchains and requires every named report to use only
the permitted standard axioms, with no compiler warnings or errors.

The [evaluation and scalar-projection extension](astra_mca_scalar_projection-2026-09-05.md)
now expresses these rows as received-word minus polynomial evaluations,
chooses a projection giving distinct scalar challenges, and proves the
general polynomial support lemmas. The indexed MCA event and probability
statements remain to be assembled.
Even completion of that upper-bound construction would leave the matching
universal lower bound open. The strongest computed upper bound is unchanged.

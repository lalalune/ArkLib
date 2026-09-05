# Factor partitions and the surviving 68.04 counting gap

The 49-source candidate still exceeds the field budget by
`17225531450318380` (6.26%). A stronger bounded partition calculation improves
125,020 intermediate cells but leaves the maximum unchanged. This is a failure
of the specified numerical envelope, not a counterexample to the prize or an
impossibility theorem for other sources or counting arguments.

The parameters and source pool are those in the
[contact-strip note](proximity-astra-contact-strip-2026-09-04.md). The official
companion is pinned to
[`032154395c51fd6f77715a7f42d9a987ab9fb48a`](https://github.com/proximity-prize/proximity-prize/commit/032154395c51fd6f77715a7f42d9a987ab9fb48a).

## The stronger partition rule

The companion's `routeable_exists_strict_helper_split` produces a strict
subfamily and charges the removed factors using a source potential. For a
singleton family its strict subfamily is empty. Consequently a routeable
individual factor can use that source's point charge directly. The atom
allowance is the minimum of the ordinary cost and every available source
charge that routes that individual flag.

[`astra_companion_atom_partition.cpp`](../../scripts/probes/astra_companion_atom_partition.cpp)
uses this allowance inside `r <= 12, v <= 48, z <= 3000`. A family of at least
two factors with positive R degrees has an atom whose R degree is at most half
the total. Removing it leaves strictly smaller R degree. The experiment
maximizes the atom allowance plus the already computed complement allowance
over all such splits, then takes the minimum with the original phase allowance.
The original root and correlated ledger still range over their full domains.

Each atom allowance is piecewise affine in z, including possible downward
jumps. On each interval the max-plus convolution with the complement is
computed using a sliding maximum. There are 48,528 interval convolutions in
the recorded replay. The arithmetic implementation is not a Lean certificate;
its combination with the actual polynomial source splits still needs proof.

The independent audit compares 1,000 random interval convolutions against
direct enumeration, including negative slopes and jumps. Both the optimized
and undefined-behavior-sanitized full replays passed. The four original phase
regressions also passed after adding the compile-time experiment hooks.

## Why this pool still fails

At raw flag `(r,v,z)=(10,37,2317)`, the ordinary singleton allowance is
`283403712362442072`. Six of the 49 sources route this flag; the cheapest costs
`286642894046259837`. Thus the singleton allowance survives the partition
refinement unchanged. The accounting is:

| Term | Count |
|---|---:|
| Singleton allowance | 283403712362442072 |
| Initial complement and correlated chain/residual terms | 8728752287324751 |
| Fixed tails | 73789382345390 |
| Scalar list | 5529601254 |
| Combined allowance | 292206259561713467 |
| Field budget | 274980728111395087 |

The maximum remains at this flag. These are allowances in an abstract flag
domain; no polynomial realizing the flag and saturating the counts is asserted.

A denser local source search at `(10,37,2310)` considers every multiplicity
8000 through 11000 and every integer slope from `floor(.298*m)-2` through
`floor(.320*m)+2`, subject to the existing source gates. It optimizes L within
each shape using the same concavity argument as the coarse search. Of 627,767
tested shapes with positive affine kernel slope, 35,452 pass the strip gate.
The best is `(m,L,S)=(9918,553718,3076)`, with point charge
`349193997186658117`, kernel nullity `69199373378536160871`, and strip margin
`10597174107`. That charge exceeds the ordinary allowance
`282555141211273947` at this point. This remains a bounded grid result.

## Reproduction

```sh
python3 scripts/probes/astra_companion_atom_audit.py
python3 scripts/probes/astra_companion_atom_audit.py --check-partition
python3 scripts/probes/astra_companion_atom_audit.py --sanitize
python3 scripts/probes/astra_companion_atom_audit.py --check-dense-source
```

The dense check passed after rebuilding the search program and verifying the
exact grid metadata and result. It independently recomputed all 20 returned
witnesses in Python, including their preceding failing L values. It takes
several minutes. The source CLI also accepts
`source-limit 10 37 2310 --dense-local`; the original coarse CLI and its
regression checks remain available and passed with the new grid option.

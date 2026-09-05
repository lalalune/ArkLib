# Exact contact-strip projection and the 68.04 budget

The Proximity Prize remains open. The clipped strip improves some numerical
source exits, but the best candidate recorded here still exceeds the field
budget by `18801369262787534` (about 6.84%). No new `ProtocolClaim` is proved.

This follows the [correlated-ledger audit](proximity-astra-joint-ledger-2026-09-04.md)
and the official companion pin
[`032154395c51fd6f77715a7f42d9a987ab9fb48a`](https://github.com/proximity-prize/proximity-prize/commit/032154395c51fd6f77715a7f42d9a987ab9fb48a).
The official lower score at that pin is 68.03. A fresh remote check at
2026-09-05 00:20 UTC found no later companion commit or changes to ArkLib's
`main` (`8e2fc19130e2fea9e175c52b0953b88804b8f333`) and
`research/proximity-prize` (`54007b004040a9cd0964dcb0a2413e86bc60ae8d`).

## The smaller coefficient projection

In a nested coefficient box, nonnegative exponents satisfy

```text
y+r+z <= T,   y+r <= Y,   r <= S,
x+w*y+(w-1)*r < D.
```

To lower the contact bound from `D` to `max(0,D-delta)`, the exact number of
X coefficients in a fixed `(y,r,z)` channel is

```text
min(delta, max(0,D-w*y-(w-1)*r)).
```

This can be strictly smaller than charging `delta` for every channel below
the published thin cut. The exact projection dimension is the sum of this
width times `T+1-y-r`, over the allowed `(y,r)` pairs.

[`astra_companion_band_strip.lean`](../../scripts/probes/astra_companion_band_strip.lean)
proves the interval indexing, width identities, and the two-boundary-row
property using `Std` only. It has been checked with Lean 4.30.0-rc2. Its
theorem axiom reports use only `propext`, `Classical.choice`, and `Quot.sound`.

[`astra_companion_strip_projection.lean`](../../scripts/probes/astra_companion_strip_projection.lean)
adds the Mathlib polynomial projection and rank argument. It constructs a
dependent finite index with exactly this cardinality, shows that vanishing
strip coefficients leave the lower box, and uses rank-nullity to bound the
dimension lost. Its first compilation passed in
[run 33932666190](https://github.com/lalalune/ArkLib/actions/runs/33932666190)
with Lean 4.30.0-rc2 and all four theorem reports containing only `propext`,
`Classical.choice`, and `Quot.sound`. That run emitted two linter warnings,
now corrected, and exposed a missing `rg` command in the output check. The
workflow now uses Python to enforce the complete axiom allowlist, report
presence, and absence of warnings. A subsequent clean run is still pending
for that stricter gate. The job does not build ArkLib or certify a prize claim.

The workflow also checks the same file with the official companion's pinned
dependencies. That project uses Lean 4.32.2 and upstream ArkLib
`e65197892890b8fd9b0dc05b8980273cf1d595cc`; these differ from this research
checkout. Passing with this checkout's 4.30.0-rc2 alone does not establish
compatibility with the companion. The second toolchain check is pending.

The projection-to-selector integration, identity between the fast arithmetic
and the formal sum, concrete source tables, retuned ordinary-factor gates,
and final companion assembly remain separate proof obligations.

## Reproducible numerical checks

[`astra_companion_band_audit.py`](../../scripts/probes/astra_companion_band_audit.py)
compares the fast cumulative-row formula against a direct channel sum in
40,095 small boxes, and against the difference of two independently counted
whole boxes in 160 large cases. All passed. The optimized C++ implementation
also matched 1,542 sampled cases. All three phase replays below passed both
optimized and undefined-behavior-sanitized builds. The four older default
phase regressions also retained their exact outputs.

All rows use the 68.04 error cell 80791 and include the fixed tail count
`73789382345390` and scalar list count `5529601254`. The capacity is
`274980728111395087`.

| Source pool and rule | Phase maximum | Maximizer `(r,v,z)` | Combined count | Excess |
|---|---:|---|---:|---:|
| Six, actual contact with thin cut | 295065697758669524 | (12,37,4371) | 295139492670616168 | 20158764559221081 |
| Six, exact strip | 294944000934875098 | (12,37,4368) | 295017795846821742 | 20037067735426655 |
| Thirty, exact strip | 293708302462235977 | (10,37,2330) | 293782097374182621 | 18801369262787534 |

The thirty-source pool is the earlier 29-source ladder plus
`(multiplicity,limit,slope) = (6800,374000,2097)`. Its global maximum is the
same with the published band rule: the extra source moves the worst child
one Z step, and the strip improvement does not reduce that new maximum.
These are conditional numerical envelopes, not optimality claims or
certificates of the retuned algebraic assumptions.

```sh
python3 scripts/probes/astra_companion_band_audit.py --check-phases
python3 scripts/probes/astra_companion_band_audit.py --sanitize
lean scripts/probes/astra_companion_band_strip.lean
./scripts/lake-locked.sh exe cache get
lake env lean scripts/probes/astra_companion_strip_projection.lean
```

The Python script uses the standard library. C++ checks require a C++17
compiler supporting signed 128-bit integers. The Mathlib proof uses the
repository's pinned Lean toolchain and dependency manifest. Local Mathlib
verification is unavailable on this host because its cache is absent and
there is insufficient disk space for it; the focused public CI job is used
for this file instead.

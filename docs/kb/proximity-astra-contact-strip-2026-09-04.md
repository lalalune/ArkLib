# Exact contact-strip projection and the 68.04 budget

The Proximity Prize remains open. The clipped strip improves some numerical
source exits, but the best candidate recorded here still exceeds the field
budget by `17225531450318380` (about 6.26%). No new `ProtocolClaim` is proved.

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
dimension lost. Both jobs in
[run 33933114315](https://github.com/lalalune/ArkLib/actions/runs/33933114315)
passed with no warnings and all four theorem reports containing only
`propext`, `Classical.choice`, and `Quot.sound`. The workflow uses Python to
enforce the full axiom allowlist, report presence, and absence of warnings;
the Lean process must also exit successfully.

The two jobs use this checkout's pinned dependencies (Lean 4.30.0-rc2) and
the official companion's pin (Lean 4.32.2, upstream ArkLib
`e65197892890b8fd9b0dc05b8980273cf1d595cc`), respectively. Thus the lemma has
been checked in both dependency environments. This is a standalone Mathlib
file check, not a full ArkLib build, an import of the packed companion proof,
or a new protocol certificate.

The projection-to-selector integration, identity between the fast arithmetic
and the formal sum, concrete source tables, retuned polynomial integration,
and final companion assembly remain separate proof obligations.

## Arithmetic gates at 68.04

[`astra_companion_6804_ordinary_gates.lean`](../../scripts/probes/astra_companion_6804_ordinary_gates.lean)
checks the ordinary-factor arithmetic at error cell 80791, with 181353
agreements, gap 50282, and support caps `(T,Y,R)=(6919,136,30)`. It supplies
universal padded and hybrid identity inequalities using nonnegative slack
polynomials, together with the mixed-characteristic, product, coordinate,
and weighted-cap gates. The earlier ordinary certificate covered 80781 and
does not establish these retuned inequalities.

[Run 33934610465](https://github.com/lalalune/ArkLib/actions/runs/33934610465)
passed on both pinned toolchains at commit
`e2f63aa1d22c3b2b39b460ffefb608a89824fe07`. Each job checked the four strip
reports and all eight new arithmetic reports, with no warnings or forbidden
axioms. The arithmetic file imports only Std. These are proofs of the
displayed definitions and inequalities; identifying them with the consumers
in the packed companion and proving the final protocol remain separate work.

## Reproducible numerical checks

[`astra_companion_band_audit.py`](../../scripts/probes/astra_companion_band_audit.py)
compares the fast cumulative-row formula against a direct channel sum in
40,095 small boxes, and against the difference of two independently counted
whole boxes in 160 large cases. All passed. The optimized C++ implementation
also matched 1,542 sampled cases. The first three phase replays below passed both
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
| Thirty-seven, refined limits | 293292868140156029 | (10,38,2271) | 293366663052102673 | 18385934940707586 |
| Forty-nine, six further refinement rounds | 292132464649766823 | (10,37,2317) | 292206259561713467 | 17225531450318380 |

The thirty-source pool is the earlier 29-source ladder plus
`(multiplicity,limit,slope) = (6800,374000,2097)`. Its global maximum is the
same with the published band rule: the extra source moves the worst child
one Z step, and the strip improvement does not reduce that new maximum.
These are conditional numerical envelopes, not optimality claims or
certificates of the retuned algebraic assumptions.

## Refining the source degree limit

[`astra_companion_source_limit.cpp`](../../scripts/probes/astra_companion_source_limit.cpp)
searches a fixed grid of multiplicities and slopes, optimizing the degree
limit L within each shape. Above the support bounds the kernel nullity is
affine in L. Each fixed strip channel contributes its width times
`max(0,L-constant)`, so the strip cost is convex in L. A binary search locates
the maximum slack; a second search finds the first passing L and hence the
least point charge for that sampled shape. Every returned witness is then
checked with direct kernel counts and the actual route predicate.

The convexity argument and its connection to the fast formula are not Lean
certified here. Nor does minimizing the source's point charge optimize the
whole phase envelope. These are bounded research searches.

At `(10,37,2320)`, 4,816 of 8,773 tested shapes passed. The best returned
point charge came from `(m,L,S)=(7900,433893,2451)`:
`219771540758329579`, with kernel nullity `27098820480559716359` and strip
margin `216537635742`. At L one smaller the strip margin is nonpositive.
At `(10,37,2250)` the same shape grid found no passing source. That is a
bounded negative result, not an impossibility theorem.

The thirty-seven-source pool adds eight such search seeds to the 29-source
ladder. Six rounds then target the current maximum and five Z steps below it,
adding two sources each time. The final 49 sources, their exact integer source gates,
and the final count are recorded in
[`astra_companion_limit_audit.py`](../../scripts/probes/astra_companion_limit_audit.py).
The optimized final replay passed in both source orders. The sanitized
replay passed with the same maximum. Both optimized and sanitized source
searches reproduced the two 8,773-shape results above; all 20 returned
witnesses at the passing point were independently checked in Python, along
with the preceding failing L value. Six malformed argument cases were also
rejected.

```sh
python3 scripts/probes/astra_companion_limit_audit.py
python3 scripts/probes/astra_companion_limit_audit.py --check-search --check-phases --reverse
python3 scripts/probes/astra_companion_limit_audit.py --sanitize
```

The audit independently recomputes the reported source margins, nullities,
and charges in Python. The search returns no prize score. This source-refined candidate
still exceeds capacity by 6.26%; integrating the strip theorem cannot by
itself fix this failed numerical inequality.

The [factor-partition follow-up](proximity-astra-factor-partition-2026-09-04.md)
then minimizes each atom over the available source charges and enumerates
factor partitions inside a bounded rectangle. It improves intermediate cells
but leaves the maximum unchanged. A dense local source search also fails to
improve the ordinary singleton allowance at a nearby flag.

The subsequent [T-cutoff audit](astra_t_cutoff-2026-09-04.md) changes the
interpolant and quotient cutoff to `(m,L,S,k)=(166,7159,51,1)`. Its full
combined allowance is **292119564672092577**, still **6.23% above capacity**,
with the same critical flag. Optimized and sanitized replays agree. This is
the best T tuning in the audit's stated bounded class for this fixed
49-source numerical envelope; it is not a globally optimal mathematical bound.
The new dimension arithmetic is separately kernel-checked, with the official
polynomial integration and final protocol proof still outstanding.

The [C2 scalar-budget audit](astra_c2_budget_obstruction-2026-09-04.md)
isolates a removable rounding too small to close this gap, and proves that
the independent scalar caps alone cannot force a six-percent reduction.
On the attack side, the [joint-key audit](astra_attack_joint_key_obstructions-2026-09-04.md)
excludes two simple key-space restrictions at the production prime, while the
[mixed-cycle audit](astra_attack_mixed_cycles-2026-09-04.md) shows that its
conditional-support counting estimate is dominated by the pure-cycle family.
Neither result bounds nonlinear key concentration or proves a new score.

## Reproduction

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

The current `./scripts/validate.sh --docs` run passed the repository
forbidden-token precheck with its nine existing allowlisted residual axioms,
then exited 127 because `lake` is unavailable locally. Documentation integrity
and staged whitespace checks passed separately. The focused CI results above
do not replace that full repository gate. A final remote fetch at
2026-09-05 01:03 UTC found the same main, research, and official companion
heads recorded above.

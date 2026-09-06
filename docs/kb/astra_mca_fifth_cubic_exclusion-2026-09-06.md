# A fifth cubic cannot improve the fixed four-source construction

Keeping the four [order-eight source cubics](astra_mca_four_cubic-2026-09-06.md)
and adjoining a fifth distinct cubic cannot improve their production unsafe
radius by the same joint-core-plus-one-point mechanism. This statement allows
arbitrary common-root placement and received values, with `p_i=B W_i(X^s)`,
`q_i=Xp_i`, `s=2^27`, and nonzero `B` of degree at most `s-2`.
It requires all five exact joint cores to reach the proposed larger size and
at least `n+1` distinct directions supplied by those five sources. It does not
exclude replacing the original family, different degrees or carriers, or
additional decoders whose agreement comes from several outside points.

## Reduction from an arbitrary fifth cubic to forty possibilities

The original four sources have a unique largest equality class in every base
fiber. Their largest class sizes sum to `21`, and every largest class has at
least two members. Let `h` be the number of fibers where the fifth cubic equals
that largest-class value. The sum of largest class sizes for all five sources
is exactly `21+h`: adding one value to a smaller class cannot exceed the old
unique maximum.

At a non-root coordinate, a received pair can jointly match at most the size
of its largest class. At a common root the possible gain over that bound is
at most `5-2=3`. Consequently, the sum of the five core sizes is at most

```text
(21+h)s + 3 deg B <= (24+h)s-6.
```

Improving the current radius requires every core to be at least `11s/2-1`.
If `h<=3`, their total would be at least `55s/2-5`, strictly greater than
`27s-6`. Thus `h>=4` is necessary.

Four specified values at four distinct nodes determine a cubic uniquely.
Interpolating all `binom(8,4)=70` choices of four largest-class values produces
exactly 44 distinct polynomials over the production field. Four are the
existing sources; the remaining forty exhaust the fifth-cubic possibilities
that survive this necessary condition.

## Exact allocation certificates for the forty candidates

For each candidate, make nonnegative allocation variables for every fiber:
one for each covered equality class, one for uncovered points, and one for
joint common roots. Normalize all counts by `s`. Every fiber has mass one;
joint-root mass is at most one; and the count of supplied directions is
relaxed to be at least eight. A covered non-root coordinate supplies at most
one direction, and an uncovered coordinate supplies at most its number of
local classes. Common roots off the zero received pair may be represented
by the uncovered state: this only increases the allowed direction count and
relaxes the root budget, so it preserves an upper bound.

The objective `a` is a common lower bound for all five normalized core sizes.
This is a relaxation of every production allocation: it discards the negative
`2/s` root-budget correction and relaxes `D>=8s+1` to `D/s>=8`.

For every one of the forty resulting systems `M x<=b`, the
[certificate](../../scripts/probes/astra_mca_fifth_cubic_certificate.json)
supplies nonnegative rational weights `y` satisfying

```text
y^T M >= objective,
y^T b <= 43/8.
```

Weak duality gives `a<=43/8`. At the production value of `s`, this is a core
upper bound of `721420288`, below the `738197503` needed to improve the
four-source radius. The checker regenerates all forty cubics and every
constraint row, checks the rational inequalities exactly, and verifies the
production comparison. Floating-point optimization was used only to discover
the certificates; reproduction requires only Python's standard library.

```sh
python3 scripts/probes/astra_mca_fifth_cubic_check.py
```

The [receipt](../../scripts/probes/receipts/astra_four_cubic_20260906/fifth_extension.json)
records forty passing rational dual checks. The
[manifest](../../scripts/probes/receipts/astra_four_cubic_20260906/manifest.json)
binds the checker, certificate, proof note, and receipt. This is a finite exact
certificate plus the written interpolation and allocation argument; it is not
a Lean theorem or a universal MCA safety bound.

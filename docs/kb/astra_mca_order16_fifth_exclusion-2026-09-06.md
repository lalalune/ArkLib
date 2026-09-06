# A fifth degree-seven source cannot improve the fixed order-16 construction

Adjoining one distinct polynomial of degree at most seven to the four sources
in the [order-16 construction](astra_mca_order16-2026-09-06.md) cannot improve
its production unsafe radius by the same joint-core-plus-one-point mechanism.
This statement permits arbitrary common-root placement and received values,
with `p_i=Q(X)W_i(X^s)`, `q_i=Xp_i`, `s=2^26`, and `deg Q<=s-2`. It requires
all five exact joint cores to improve and at least `n+1` directions supplied
by those five sources. It does not exclude replacing the original family,
other degrees or carriers, or additional decoders agreeing at several outside
points. It is not a universal MCA safety bound.

If `Q=0`, all source pairs coincide and each coordinate supplies at most one
scalar, giving at most `n` supplied directions. Thus an improving construction
has `Q!=0`, and its common-root count is at most its polynomial degree.

## A necessary interpolation condition

The largest equality-class sizes of the original four sources sum to 43 over
the sixteen base fibers. Let `h` count fibers where a proposed fifth source
equals a largest-class value. Ties count: fiber 10 has two possible largest
values, and fiber 2 has four. In every fiber, adding the fifth source raises
the largest class size by exactly one if such a match occurs, and by zero
otherwise. Thus the sum of the new largest class sizes is `43+h`.

A non-root point can contribute at most its largest class size to the sum
of all five joint cores. Replacing a point by a common root can increase that
sum by at most four, since the former largest class had at least one member.
Consequently

```text
sum_i C_i <= (43+h)s + 4 deg Q.
```

If `h<=9`, the right side is at most `56s-8`. The current common core is
`760567124`, so improving it requires every core to be at least `760567125`.
Their required sum is `3802835625`, strictly greater than
`56s-8=3758096376`. Therefore an improving fifth source must have `h>=10`.

Eight values at distinct nodes determine a polynomial of degree at most
seven. Enumerating all choices of eight fibers and all largest-class values
on those fibers is therefore exhaustive for candidates with `h>=10`. There
are 47,619 interpolation assignments and 43,503 distinct resulting polynomials
over the production field. Their largest-class match counts are:

| Matches | Polynomials |
|---|---:|
| 8 | 43,254 |
| 9 | 240 |
| 10 | 5 |
| 12 | 4 |

The four polynomials with twelve matches are precisely the original sources.
Exactly five new candidates survive the necessary condition.

## Exact allocation bounds for the five candidates

For each candidate introduce nonnegative variables for the mass of each
covered equality class, uncovered points, and joint common roots in each
fiber. Normalize by `s`. Each fiber has mass one, the common-root mass is at
most one, and the count of supplied directions is relaxed to be at least
sixteen. A covered non-root point supplies at most one direction because
`q_i=Xp_i`; an uncovered point supplies at most the number of distinct local
classes. A common root off the zero received pair can be represented by the
uncovered state, which increases its allowed direction count and relaxes the
root budget. This preserves an upper bound.

The objective is a common lower bound `a` on all five normalized cores.
The [certificate](../../scripts/probes/astra_mca_order16_fifth_certificate.json)
gives five nonnegative rational dual vectors. The
[checker](../../scripts/probes/astra_mca_order16_fifth_check.py) regenerates
every candidate and every constraint `M x<=b`, and verifies exactly

```text
y>=0, y^T M>=objective, y^T b<=45/4.
```

Weak duality therefore gives `a<=45/4` for every surviving candidate. At the
production value of `s`, this bounds a common core by `754974720`, strictly
below the `760567125` needed to improve the existing construction. This large
gap also resolves the finite correction: the LP relaxes `deg Q<=s-2` to root
mass at most one and `D>=16s+1` to normalized direction mass at least sixteen;
even those relaxations cannot reach the next integer core.

## Reproduction and scope

```sh
python3 scripts/probes/astra_mca_order16_fifth_check.py
```

Reproduction uses only Python's standard library. It recomputes all 47,619
interpolations over the actual production prime, identifies the five surviving
new sources, and verifies their rational dual certificates and the production
integer comparisons. The saved certificate contains only those five sources
and dual vectors, rather than the full interpolation census. Floating-point
optimization was used to discover the dual vectors; it is not used by the
checker. This is an exact finite certificate with a written interpolation and
allocation argument, not a Lean theorem or a determination of the optimal MCA
radius.

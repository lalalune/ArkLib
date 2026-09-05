# Counting with a cut that may contain first-tail components

A new equation need not cut every first-tail component separately. It is
enough for it to be nonzero on the irreducible surface being counted, provided
we retain the existing tail-multiplicity and tangent-curve bounds. Components
contained in the new equation can be counted using its degree. Components of
large first-tail multiplicity can still use the original weighted divisor
budget.

At the binding companion flag, this gives a conditional bound below the
required allowance for each of the four
[positive second-Hasse sources](astra_hasse_rank_profile-2026-09-05.md).
**Surface properness is still unproved. There is no improved prize bound or
new score.** The argument below is written, its arithmetic is checked, and
the proposed aggregation has not been integrated into Lean or the complete
phase recurrence. Independent mathematical review remains outstanding.

## The geometric split

Work over an algebraically closed field in three affine variables. Let G be
an irreducible surface equation, of degree at most t. Let T be a proper
first-tail representative, of degree at most a1, and let C range over the
regular curve components of `G=T=0`. Write mu_C>=1 for their first-tail
multiplicities. Use the existing weighted zero budgets w_C(v) and divisor
certificate

```text
sum_C mu_C*w_C(v) <= Mixed(surfaceFlag,firstTailFlag,v).   (1)
```

The relevant companion certificate is
[`RegularComponentWeightedInertiaResultantCertificate`](https://github.com/proximity-prize/proximity-prize/blob/032154395c51fd6f77715a7f42d9a987ab9fb48a/ProximityPrize/SubmissionLower/PackedLegacy.lean#L6813).
Its three unit inequalities imply (1) for **any** nonnegative raw flag v,
not just the current provider's chosen second-tail flag.

Retain these two inputs from the existing counting argument:

* On a nontangent component C, there is a proper later tail with index
  `w+1+d`, where `1<=d<=mu_C`. Every selected point annihilates that tail.
* On a tangent component, the selected count is at most g*deg(C). In the
  current MCA setting one may use g=n-A+1. This is the existing tangent
  bound by g times the Y,Z projection degree, followed by the elementary
  fact that a linear projection degree is at most the curve's total degree.
  For arbitrary abstract inflated budget numbers, this last comparison
  cannot be assumed; it uses the actual geometric projection degrees.

The first input is the local-order dichotomy used in
[`exists_hybridTailMultiplicityProviderGen_of_localDVR`](https://github.com/proximity-prize/proximity-prize/blob/032154395c51fd6f77715a7f42d9a987ab9fb48a/ProximityPrize/SubmissionLower/PackedLocatorTail.lean#L19704).
For raw surface flag `(z,v,r)`, the sharp later-tail flag is

```text
Sharp(j)=j*D+U,   D=(2z,2v-1,2r-1), U=(0,1,0).           (2)
```

Now suppose B is an additional polynomial satisfying

```text
G does not divide B,  deg(B)<=b,
B vanishes at every selected point.                     (3)
```

This is properness on the surface, not on every curve C. All degrees here
ignore the generic X parameter, which is already in the coefficient field.
If the original factor F is irreducible over K(X) and B is over that field,
coprimeness of F and B persists under extension of the coefficient field;
it suffices to prove F does not divide B. Without that irreducibility
hypothesis, (3) must be checked for the actual component G being counted.

Choose an integer cutoff M>=1, and put

```text
c_M=ceil((w+1)/M),
V_M=(1+c_M)*D+U,
L_M=max(g, total_degree_bound(Sharp(w+M))).               (4)
```

Then the selected count is bounded by

```text
Mixed(surfaceFlag,firstTailFlag,V_M) + t*b*(a1+L_M).      (5)
```

### Proof of (5)

First consider the components not contained in B. A proper section of a
curve C by a polynomial of degree b contains at most b*deg(C) distinct
points. The distinct curve degrees of the proper complete intersection
`G=T=0` sum to at most t*a1. Their total selected count is therefore at
most t*a1*b. This remains valid if B contains other components; we apply
the curve section bound only to components on which B is nonzero.

Next consider components contained in B. They are components of the proper
complete intersection `G=B=0`, so their distinct degrees sum to at most t*b.
For a nontangent component with mu_C<M, its proper later tail has index
at most w+M, hence counts at most L_M*deg(C) points. Tangent components,
of any multiplicity, satisfy the same bound by the second input above.
Summing gives at most t*b*L_M for these two groups. This step charges each
contained curve once; it does not substitute its multiplicity in B for its
possibly different multiplicity in T.

The remaining contained components are nontangent and have mu_C>=M.
For the proper tail furnished by the dichotomy, (2)--(4) give

```text
Sharp(w+1+d) <= Sharp(w+1+mu_C) <= mu_C*V_M
```

coordinatewise, since `mu_C*c_M>=w+1` and `mu_C>=1`. Its weighted zero
budget is consequently at most mu_C*w_C(V_M). Summing this group and
then using (1) for all components gives the first term of (5). Adding
the three estimates proves (5). Shared selected points can be assigned to
one component, or overcounted, in either case preserving the upper bound.

Only ordinary projective Bezout degree inequalities are used for the two
terms involving b. No new mixed-degree divisor certificate for B, no
transversality, and no moving-pole budget on the contained components are
required. The original weighted multiplicity certificate is still needed
for the last group. Its use is what keeps that term small enough.

## Companion arithmetic at the binding flag

Fix w=131071 and raw surface flag `(2317,37,10)`, so t=2364. The reduced
first-tail representative used by C2 has

```text
firstTail=(607387648,9699329,2359296),
a1=619446273,
D=(4634,73,19),
M=2048, c_M=64, V_M=(301210,4746,1235).
```

The representative is congruent to the original first tail on G, as in
the existing C2 transport. This preserves its regular components and local
multiplicities; we use that reduced representative's degree, not the
unreduced polynomial's potentially larger degree.

The exact terms in (5) are

```text
Mixed(surfaceFlag,firstTailFlag,V_M)=188834222914524,
L_M=2*(t-1)*(w+M)+1=629120395,
t*(a1+L_M)=2951611603152.
```

Here L_M is larger than g=80792. Thus (5) is the affine function

```text
conditional_cell(b)=188834222914524+2951611603152*b.      (6)
```

For a second-Hasse source with caps S2,T, clearing its H denominators gives
`b<=T+(t-1)*S2`. The four previously verified profiles yield:

| Source (m,S1,S2,T) | Extra-cut degree b | Conditional cell allowance from (6) |
|---|---:|---:|
| (99,30,1,4156) | 6519 | 19430390263862412 |
| (99,30,2,2270) | 6996 | 20838308998565916 |
| (80,24,6,1042) | 15220 | 45112362822887964 |
| (99,30,8,1031) | 19935 | 59029211531749644 |

For scale, the published singleton allowance is 283403712362442072.
Keeping the previously recorded complement 8715852309650505 fixed, the
available singleton allowance would be 266264875801744582. Formula (6)
fits that allowance for every b<=90146, and fails at b=90147. These are
conditional single-cell comparisons. Replacing a cell can expose a different
maximum in the phase recurrence, so adding the fixed complement is not a
verified global MCA estimate.

The checker also compares the 18 power-of-two cutoffs 1,...,131072. The best
among those is M=2048 for the first three rows and M=1024 for the fourth.
There is no global cutoff optimum claim.

## A tested attempt to force surface properness

In second-Hasse local coordinates,

```text
partial_(Y2,original)=partial_(Y2,local)+t^2*partial_v.
```

It lowers contact order by at most one and weighted degree by w-2 when the
derivative is nonzero. Therefore a source with the stricter cutoff

```text
D=m*A-S2*(A-w+2)                                        (7)
```

makes every derivative `partial_Y2^j Q`, j<=S2, annihilate every candidate.
For a nonzero Q, take its actual Y2 degree s. Since s is below the
characteristic, `partial_Y2^s Q` is nonzero and independent of Y2. This
would supply a first-order annihilator of total degree at most T-s. If that
degree were below the actual total degree of an irreducible F, it would
force surface properness. Upper degree caps alone do not justify the latter
strict comparison.

The first four production profiles fail the strict dimension certificate
after imposing (7), for **every T**: their affine-tail slopes are respectively
-4153747737, -10499511676, -222607971, -704205203 when ordered as
(80,24,6), (99,30,8), (99,30,1), (99,30,2). A trimmed (166,51,1) profile
first passes at T=42105, and (240,72,1) at T=11828; neither gives the desired
degree separation at the binding flag. The trimmed (166,51,6) profile also
fails for every T. This is a bounded seven-profile test, not an exclusion
of actual kernels or of all derivative-assisted source designs.

## Reproduction and remaining task

Run `python3 scripts/probes/astra_hasse_component_split_check.py` and add
`--derivative-trim` to reproduce the seven more expensive rank calculations.
The checker verifies the affine flag domination, all displayed integer
budgets, the adjacent cut-degree boundary, the bounded cutoff comparison,
and a finite plane example in which B contains one full curve component
while cutting the others. That plane example checks the ordinary geometric
split; it is not an MCA or differential-tail instance.

The remaining production step is to find, for every relevant surface G,
an available Q whose cleared B_Q satisfies G not dividing B_Q, or to bound
the exceptional surfaces on which all available Q vanish. The
[containment examples](astra_hasse_containment-2026-09-05.md) show why merely
finding a nonzero Q does not prove this. The positive dimension surplus and
the source-to-factor relationship remain possible additional information.
The new split removes the need to prove properness on every first-tail
component, but does not discharge surface properness itself.

The [positive-margin first-order controls](astra_positive_kernel_factor-2026-09-05.md)
show that a positive source margin alone does not exclude a universal
regular factor or force a multiple selected tail intersection. Their
positive second-order source does supply a proper cut, so they do not
refute the proposed production properness statement.

# Finite properness certificates from complete interpolation kernels

The second-Hasse source escapes the old universal regular factor in the
three finite examples whose acceleration degree is six. Thus failure of
the earlier low-acceleration-degree sufficient condition does not force
failure of properness in those examples. An additional 44-direction search
over F_257 finds 39 explicit escapes and five cases with no common factor
of positive R degree in the old kernel.

These are reproducible finite certificates. They do not establish universal
properness, reduce a production MCA allowance, or solve a prize target.
All examples have block length nine and lie inside the Johnson range.
Using the companion characteristic does not change this limitation.

## The two complete source spaces

Set n=9, w=2, A=5, m=3, D=15, and use nodes 0,...,8. The received origin
u0 is zero at the first five nodes and one at the remaining four. For the
direction u1, the old and new full monomial spaces are

```text
X^x Y^i R^j S^k Z^z,
x+2*i+j < 15,
i+j+k+z <= T, j<=S1, k<=S2.
```

| Source | T | S1 | S2 | Columns C | Local rank L | C-9L |
| --- | ---: | ---: | ---: | ---: | ---: | ---: |
| Old, first Hasse | 6 | 1 | 0 | 532 | 59 | 1 |
| New, second Hasse | 5 | 3 | 2 | 1253 | 139 | 2 |

At each node a substitute X=a+t and

```text
old: Y=u0(a)+Z*u1(a)+t*R+v,             weight(v)=2;
new: Y=u0(a)+Z*u1(a)+t*R-t^2*S+v,       weight(v)=3.
```

Every coefficient of contact weight less than three must vanish. These are
the complete contact equations, without choosing a subspace of the source
or imposing a preselected common factor. Substitution of R=f' and S=f''/2
at five agreements gives total root multiplicity at least 15, larger than
the degree bound. Therefore both kernels give differential identities on
every selected polynomial of degree at most two.

The solver separates source monomials by h=i+j+k+z. At nodes with u0=0,
the contact map preserves total degree in (v,R,S,Z), so the kernels of
different h blocks form a direct sum. It then applies every remaining
node equation to this entire direct sum. Exact Gaussian elimination at
both stages computes a basis of the full kernel. No homogeneous block is
discarded except when its kernel is zero.

## Why a nonzero evaluation certifies an escape

When the old kernel is one-dimensional, write its generator as

```text
F(X,Y,R,Z)=A0(X,Y,Z)*R+B0(X,Y,Z).
```

Choose (x,y,z) with A0 nonzero, put r=-B0/A0, and set

```text
s=-(F_X+r*F_Y)/(2*F_R).
```

Then F=0 and F_R is nonzero at the chosen point. If a new kernel basis
element Q has Q(x,y,r,s,z) nonzero, its rational acceleration pullback
cannot vanish identically on the positive-R factor of F. Clearing the
denominator 2F_R preserves that nonvanishing.

Even if F has an R-independent content factor c, A0 nonzero ensures
c nonzero at the chosen point. Writing F=c*F0 gives the same acceleration
ratio on F0=0. The primitive linear polynomial F0 is the unique irreducible
positive-R factor over the polynomial coefficient ring. Thus this test
does not require treating an arbitrary generator as primitive.

When the old kernel has several generators A_i*R+B_i, an exact nonzero
evaluation of A_i*B_j-A_j*B_i proves that this polynomial is nonzero. The
two generators then have no common positive-R divisor over K(X,Y,Z)[R],
and neither does the full kernel. An R-independent common factor is not
excluded by this test. A failed point search would prove neither
containment nor properness; the checker stops rather than asserting either.

## Recorded cases

The fixed direction from the
[acceleration chart examples](astra_acceleration_chart-2026-09-05.md) is

```text
u1=(238,84,40,219,30,215,254,215,247).
```

Over each of F_257, F_65537, and F_2130706433 the complete old kernel has
dimension one and the complete new kernel has dimension 22. The earlier
chart checker establishes irreducibility and acceleration degree six for
the old generator. The new checker constructs its escape directly, without
assuming the relative-degree properness criterion.

Two retained evaluations, in coordinate order (X,Y,R,S,Z), are:

| Characteristic | Point | New basis index | Nonzero value |
| --- | --- | ---: | ---: |
| 65537 | (11,2,47290,59741,3) | 0 | 37872 |
| 2130706433 | (11,2,944668979,175244998,3) | 0 | 1284108367 |

The complete 44-direction search over F_257 consists of:

- u1(x)=(x+a)^(-d), for a=1,2,3 and d=1,...,8;
- u1(x)=(x+a)^d, for a=0,1 and d=3,...,8;
- eight NumPy default_rng directions with seed 20260905, taking values
  uniformly from the integers 1,...,256.

All directions have maximum quadratic agreement less than five, checked
by enumerating all 84 node triples and their unique quadratic interpolants.
Any quadratic with at least three agreements occurs in this enumeration.

Of these cases, 39 have an old kernel of dimension one and a certified
proper pullback from the new kernel. Their new nullities are 22 in 37
cases and 25 in two. The other five have a nonzero old cross determinant:
the three reciprocal directions with d=1 have old nullity 12; the two
power directions with d=3 have old nullity 14. No unresolved point-search
outcome occurs in this fixed set. This is not an exhaustive search over
received directions.

## Exact arithmetic and reproduction

Run with Python and NumPy (checked with NumPy 2.3.5):

```sh
python3 scripts/probes/astra_full_kernel_properness_check.py
```

The script emits a JSON receipt containing every direction, kernel
dimension, cross determinant or escape point, and explicit scope flags.
It reconstructs the witnesses rather than trusting a saved matrix.

At p=2130706433, accumulating ordinary int64 dot products would overflow.
The checker splits each residue into two base-2^15 limbs and reduces four
limb dot products before recombining. It checks the inner-dimension bound
for every call. Each elimination product is less than p^2<2^63, while the
recombined expression is less than (p-1)*(1+2^15+2^30)<2^63. All inputs are
required to be canonical residues.

Eighty matrix/vector controls compare this arithmetic with Python integers
at four characteristics and five inner dimensions, including empty products
and all-(p-1) boundary inputs. For the three fixed-direction characteristics,
the script also compares every local column against the earlier per-monomial
contact implementation, tests every reconstructed kernel vector against
every node equation, and checks that the returned vectors are independent.
There are 48195 such local-column comparisons across the two source spaces.

The absent step is a proof that an appropriate positive source always
contains an equation escaping each required production factor. The finite
examples neither prove nor disprove that statement. Independent review,
Lean formalization, and a valid full production bound remain outstanding.

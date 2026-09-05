# Exact resultant equations for saturated six-pencil configurations

Under the full-cover, six distinct exact-core hypotheses of the
[locator-consistency note](astra_mca_six_locator_consistency-2026-09-04.md),
each pencil has a homogeneous resultant of degree `2b` whose factors record
its absent-coordinate cancellation directions exactly. Saturation is
equivalent to this resultant being a constant times a square of a split,
squarefree degree-b form with no root at infinity. This is a concrete
necessary equation for at least five pencils in an over-budget six-pencil
configuration. It is not a contradiction, a production witness, or a Lean
proof.

Here `n=6b-2`, `k=3b-1`, the component degree bound is `d=3b-2`, each exact
joint core Ai has size `4b-2`, and its absence set Di has size `2b`.
The predecessor agreement target is `4b`.

## The syzygy rows give the actual residual direction

Use the notation of the
[balanced-bundle derivation](astra_mca_six_locator_birationality-2026-09-04.md).
For three independent rows, `M` has determinant `c*V^2`, with `c!=0`, and
`N=adj(M)/V` is polynomial. Denote its rows by A,B,C; their degree bounds
are respectively `4b-2,b,b`. For the constant row vector ci satisfying
`Qi=ci*M`, one has

```text
Wi*(A+fi*B+gi*C) = c*V*ci,       B cross C=c*w.
```

The degree-b homogenizations of B,C are independent at every point of P1.
At each domain coordinate x there is a core owner, so `MN=c*V*I` gives

```text
A(x)+u0(x)*B(x)+u1(x)*C(x)=0.
```

For x in Di, differentiating the first identity and using squarefreeness of
Wi and V gives

```text
Wi'(x)*[(fi(x)-u0(x))*B(x)+(gi(x)-u1(x))*C(x)] = c*V'(x)*ci.
```

Both scalar derivatives are nonzero. Put
`e0(x)=fi(x)-u0(x)`, `e1(x)=gi(x)-u1(x)`; exact absence means this residual
pair is nonzero. Thus

```text
ci is proportional to T*C(x)-S*B(x)
    iff e1(x)*S+e0(x)*T=0.
```

The scalar chart is `gamma=S/T`. The point `T=0` is a genuine uncancellable
slot with `e1=0`; it must not be discarded as a resultant artifact.

## A degree-2b resultant with no extraneous factor

Choose two independent constant linear forms ell,m annihilating ci. Keep
the X-homogeneous degree fixed at b, including when a leading coefficient
vanishes at a special parameter, and define

```text
F(X;S,T)=ell(T*C-S*B),       G(X;S,T)=m(T*C-S*B),
Ri(S,T)=Res_X(F,G).
```

The two-by-two determinant of the projected B,C rows is a nonzero constant
times Wi. Consequently F,G can have a common X-root only at Di. At each
such node the projected matrix has rank exactly one: rank zero would put
the independent B(x),C(x) in the one-dimensional span of ci. There is
therefore exactly one projective parameter for that node. No common root
can occur at X-infinity, because the degree-2b homogenization of monic Wi
is nonzero there.

Here is an elementary multiplicity proof. The Sylvester matrix represents

```text
H^0(O(b-1)) plus H^0(O(b-1)) -> H^0(O(2b-1)),
(a,d) -> a*F+d*G.
```

It is a `2b` by `2b` matrix with entries linear in S,T. Its determinant is
nonzero: over the algebraic closure choose a parameter outside the finite
set contributed by Di, so F,G are relatively prime and this map is
injective. Thus Ri is a nonzero homogeneous form of degree `2b`.

Suppose r different absent nodes contribute the same projective parameter.
Evaluation at those nodes gives r independent functionals on
`H^0(O(2b-1))` annihilating the Sylvester map's image. Independence follows
from interpolation at at most `2b` distinct nodes. The matrix has corank at
least r there, so its determinant vanishes to order at least r: after
constant row operations r rows vanish at the parameter, and each row is
divisible by its local parameter. This argument also applies at `T=0`.

All slot multiplicities sum to `2b`, already the degree of Ri. Every lower
bound is therefore exact and no other factor remains:

```text
Ri(S,T)=ai * product_{x in Di} [e1(x)*S+e0(x)*T],       ai in K*,
```

up to the nonzero normalization chosen for the resultant and ell,m. For
standard resultant product formulas see J. Milne,
[Fields and Galois Theory, Proposition 4.35](https://www.jmilne.org/math/CourseNotes/FT.pdf).
The Sylvester argument above supplies the multiplicity and infinity checks
needed here, without a generic-position assumption on the directions.

## Saturation is an exact square condition

A finite root gamma of Ri with multiplicity r means the pencil codeword
`fi+gamma*gi` agrees at exactly `4b-2+r` coordinates. It supplies an MCA
witness precisely when `r>=2`. To check the no-joint clause, take its full
agreement support: any joint explaining pair must agree with `(fi,gi)` on
Ai, whose size is at least k. Polynomial uniqueness therefore forces that
pair to be `(fi,gi)`, which fails at each added exact-absence coordinate.

There are only `2b` outside slots. Consequently the pencil supplies b
distinct finite bad scalars if and only if

```text
Ri=ai*Fi^2,
degree Fi=b,       Fi splits into b distinct linear factors over K,
Fi(1,0)!=0.
```

The last condition excludes infinity; squarefreeness excludes multiplicity
four or greater. A square identity alone is insufficient. For six pencils
exceeding the length bound, at least five must satisfy this full condition,
and their bad-scalar sets must also have at most one total deficit/overlap
relative to the maximum `6b=n+2`.

At production these are degree-`357913942` resultant equations and
degree-`178956971` square roots. Nothing here proves that five such equations
force a common double cover, nor that they are impossible for odd b.

## Bounded identity checks

Run `python3 scripts/probes/astra_mca_six_resultant_check.py`. It compares
fixed-degree Sylvester determinants against products of the exact direction
factors over F101, using degree bounds b=1,2,3,4. It also checks a saturated
two-pair example, an unsaturated example, a transformed example with genuine
infinity factors, and changes of the annihilator basis. These are checks of
the algebraic identity and its edge cases, not realizations of the six-pencil
production hypotheses.

The subsequent [low-degree rigidity result](astra_mca_low_degree_saturation-2026-09-05.md)
settles this implication only at b=1,2: saturation is impossible at b=1,
and four saturated points force a common degree-two cover at b=2. A sharp
three-point example and a birational b=3 example with one square resultant
show why the hypotheses and degree restriction matter. The five-square
production question remains open.

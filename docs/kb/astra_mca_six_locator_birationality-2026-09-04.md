# Birationality of the concrete one-triple locator model

This is a necessary structural result for the concrete one-triple incidence
pattern in the [six-pencil classification](astra_mca_six_pencil_types-2026-09-04.md).
If that pattern has a polynomial realization at production, its locator map
is birational onto a rational plane curve of degree 357913942. The resulting
genus inequality is compatible with the pattern, so this is not an exclusion
or a proof of the universal predecessor bound. The argument is not
Lean-formalized.

Assume all hypotheses of the
[locator-consistency note](astra_mca_six_locator_consistency-2026-09-04.md).
Put `n=6b-2`, `d=3b-2`; each absence locator Wi is monic of degree 2b.
Geometric arguments below can be made over the algebraic closure of the
production field; the polynomial degrees and splitting of the locators on
the domain are unchanged.

## A balanced syzygy bundle follows from the actual pair realization

Choose three noncollinear polynomial pairs, with indices p,q,r, and form the
matrix M with rows `Qi=Wi*(1,fi,gi)` for those indices. Write
`w=(Wp,Wq,Wr)^T` for its first column. These are three independent locators;
the labels need not be 1,2,3, which denote the collinear triple in the concrete
model. All other Wi are constant linear forms in w. The earlier identities
give

```text
det M=c*V^2,  c!=0,       V=product_{x in Omega}(X-x),
column degree bounds of M: (2b,5b-2,5b-2).
```

At a domain node, every absent Q row is zero and all present rows are
proportional to `(1,u0(x),u1(x))`. Thus every two-by-two minor vanishes at
every domain node and is divisible by the squarefree polynomial V. Hence

```text
N=adj(M)/V is polynomial,       NM=MN=c*V*I.
```

Its first row has degree at most `4b-2`; each of its other two rows has degree
at most b. Call those rows s and t. The identity `adj(N)=c*M` shows

```text
s dot w=t dot w=0,       s cross t=c*w.
```

The degree-2b homogenizations of the three entries of w have no common zero.
A finite common zero would be a domain node at which all six Wi vanish,
contradicting the full cover. At infinity their monic leading coefficients
give `(1,1,1)`. They therefore define a morphism
`phi:P1 -> P2` with `phi^*O(1)=O(2b)`.

Homogenize s and t to degree b. Their cross product is the nonvanishing
section vector c*w, so they are independent in every fiber and give the full
rank-two kernel of the evaluation map. In particular,

```text
0 -> O(-b) plus O(-b) -> O^3 -> O(2b) -> 0.
```

This proves the balanced splitting from the pair realization; it is not an
extra assumption about arbitrary root polynomials.

## The covering degree divides b and every nontrivial flat weight

Let C be the image curve. By Lüroth's theorem its normalization is P1; factor
`phi=eta after rho`, where eta is the normalization map and rho is a finite
map of degree nu. A direct general-field proof of the field-theoretic input
is given in [Mondal's proof of Lüroth's theorem](https://pinakimondal.org/luroths-theorem-a-constructive-proof/).

Write `eta^*O(1)=O(e)`. The kernel of its three-section evaluation map splits
as `O(-a) plus O(-c')`, with `a+c'=e`. This uses Grothendieck splitting and
uniqueness of its degrees, valid over an arbitrary field; see Theorem 2.1 and
Section 2.5 of [Schoemann and Wiedmann](https://arxiv.org/pdf/1712.03056).
Pulling back the evaluation sequence along rho is exact because its quotient
is a line bundle. Since pullback multiplies line-bundle degree by nu,

```text
O(-b) plus O(-b) = O(-nu*a) plus O(-nu*c'),
nu*a=nu*c'=b,       hence nu divides b.
```

The degree rule is [Stacks Project, Lemma 33.44.11](https://stacks.math.columbia.edu/tag/0AYQ).

Now take a nontrivial complete absence flat, with weight t_F. Its two
independent locator linear forms cut out a single point z in the plane. The
entire preimage `phi^{-1}(z)` is exactly the common zero set of those two
locators. It consists of t_F domain nodes, since the locators split on Omega;
there are no other finite preimages and no preimage at infinity.

For a point y of the normalization above z and a point x above y under rho,
the local vanishing order of either of these locator sections satisfies

```text
1 = ord_x(Wi) = ramification_index_x(rho) * ord_y(eta^*ell_i).
```

The first equality uses the squarefree domain locator. Both factors on the
right are positive integers, so both equal one. Thus rho is unramified on
these fibers, each branch meets the chosen line simply, and each y has
exactly nu distinct preimages. The last assertion also follows by pulling
back the point divisor of degree one. Therefore

```text
t_F = nu * (number of normalization branches above z),
nu divides every nontrivial flat weight.
```

For the concrete production one-triple model, some flat weights are 2 and
`b=178956971` is odd. Consequently `nu` divides both 2 and b, giving `nu=1`.
The locator map is birational, and the image degree is `e=2b=357913942`.

## The actual genus constraint still leaves positive slack

Birationality identifies the domain preimages of each flat point with
distinct branches of C. Each such branch is smooth, since a linear form has
vanishing order one on it. A plane point with t smooth branches contributes
at least `t(t-1)/2` to the delta invariant: each pair of distinct branches has
intersection multiplicity at least one. The branch-additivity formula holds
in arbitrary characteristic; see the proof of Theorem 2.11, Step 2, in
[Nguyen Hong Duc](https://arxiv.org/pdf/1412.5007).

The normalization exact sequence gives `sum delta=p_a(C)` because the
normalization is P1. For a degree-2b plane curve,
`p_a(C)=(2b-1)(2b-2)/2=2b^2-3b+1`; see
[Stacks Project, Lemma 53.9.3](https://stacks.math.columbia.edu/tag/0BYA).

The one-triple model has nine cross-pair flat points of weight
`a=(2b-4)/3`, three of weight 2, and one of weight 4. These are different
plane points because their complete flats are different. They require

```text
sum delta >= 9*binomial(a,2)+3*binomial(2,2)+binomial(4,2)
          = 2b^2-11b+23.
```

The difference between the arithmetic genus and this lower estimate is

```text
8b-22 = 1431655746 at production.
```

It is positive. Additional tangencies, singularities, or other information
would be needed to turn this into a contradiction. The proof above supplies
birationality and a valid necessary genus inequality; it does not establish
that a curve, the required root polynomials, or the saturated MCA events
actually exist.

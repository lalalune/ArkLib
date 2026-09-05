# Ordinary MDS weights and a rank-two quotient do not bound rich MCA vertices

There exists a length-64, dimension-32 **MDS code** over the production field
with a received pair of quotient rank two and at least **84 distinct finite
MCA-bad scalars at agreement threshold 44**. Each constructed decoding has
exactly 44 agreements and is an isolated point of the threshold-agreement
locus. Thus ordinary MDS generalized Hamming weights and quotient rank two
alone cannot prove the proposed cap of 64.

This is a generic-matrix existence proof, with an explicit finite-field
specialization bound. The accompanying probe checks the finite support and
degree calculations; it does not exhibit a numerical matrix. The code is
**not asserted to be Reed--Solomon**. This is neither a counterexample at
production length nor a refutation of the smooth-domain predecessor bound.
The argument is not Lean-formalized.

## The actual event in a two-dimensional quotient

Let C be a linear code of dimension k and let
`D=C+span(u0,u1)` have dimension k+2. For a coordinate set E write

```text
D(E)={v in D : support(v) is contained in E}.
```

Suppose `r=u0+gamma*u1-w`, with w in C, has full support E and its complement
A has at least k coordinates. If C is MDS, no nonzero codeword is supported
on E when `|E|<=n-k`. Thus projection `D(E) -> D/C` is injective, so its
dimension is at most two. It contains the nonzero vector r.

There is a joint pair of codewords agreeing with `(u0,u1)` on A exactly when
`dim D(E)=2`: in that case the projection is surjective, so subtracting the
two supported lifts from u0 and u1 gives the joint pair. Conversely a joint
pair gives two independent supported lifts. Consequently

```text
no joint pair on the full agreement set A  iff  dim D(E)=1.
```

This is the same-support no-joint condition in
[Errors.lean](../../ArkLib/Data/CodingTheory/ProximityGap/Errors.lean), not
merely an ordinary list-decoding condition. It is also the rank criterion in
the [decoding-curve incidence note](astra_mca_decoding_curve_incidence-2026-09-04.md).
The common-witness uniqueness theorem in
[MCAWitnessSpread.lean](../../ArkLib/Data/CodingTheory/ProximityGap/MCAWitnessSpread.lean)
remains valid; our 84 agreement sets are distinct.

## A sparse generic ambient code

Use coordinates `0,...,63`, and let

```text
F_i={16*i,...,16*i+20} modulo 64,  i=0,1,2,3.
```

Each F_i has size 21. The minimum union sizes for one, two, three and four
distinct blocks are respectively `21,37,53,64`.

Let G be a 64-by-34 matrix. For each i its columns `2*i,2*i+1` are supported
on F_i, with an independent indeterminate in every allowed entry. Its other
26 columns have independent indeterminates in every row. Let L be a 2-by-34
matrix with further independent entries. All generic assertions below mean
nonvanishing of explicitly specified polynomials in these entries.

We use the elementary matching criterion for a matrix with independent
entry variables: a matching of size r in its allowed-entry bipartite graph
gives a nonzero r-by-r minor. The determinant has a matching monomial with
coefficient 1 or -1, and different permutations use different variables.
Thus it is nonzero over **every** prime field. Hall's theorem, with d dummy
rows attached to all columns, says that neighbor bounds
`|N(J)|>=|J|-d` give a matching leaving at most d columns unmatched.

First, G has a nonzero 34-by-34 minor. A set of columns including a dense
column sees all 64 rows. A sparse-only set meeting h blocks has at most 2h
columns and at least 21 rows, so Hall's condition holds.

Second, for every set S of 32 rows, the determinant

```text
Delta_S=det([G_S; L])
```

is a nonzero polynomial. For a sparse-only column set meeting h blocks, its
neighbors among S number at least `max(0,|union F_i|-32)`, and the two L
rows are additional neighbors. For h=1,2,3,4 these lower bounds including
the L rows are `2,7,23,34`, respectively, at least 2h. A column set containing
a dense column sees all 34 rows. This proves Hall's condition for every S,
without enumerating the `binomial(64,32)` sets.

## Eighty-four weight-20 rays

For each i and x in F_i, define the coefficient vector v_ix in K^34 by its
two possibly nonzero entries

```text
(v_ix)_(2i)=G_(x,2i+1),  (v_ix)_(2i+1)=-G_(x,2i).
```

Require every 2-by-2 minor formed by two rows of each block's two columns to
be nonzero. Then `G*v_ix` has **exact** support `E_ix=F_i\{x}`, of size 20.
There are 84 distinct coefficient rays: within one block this follows from
its row minors, and different blocks use disjoint pairs of coefficient
positions.

For each E_ix, put A=E_ix^c, of size 44. The restriction G_A has a nonzero
33-by-33 minor. To see this, a sparse-only column subset meeting one block
has at least one neighbor in A, sufficient for deficiency at most one. A
subset meeting h>=2 blocks has at least `|union F_i|-20>=17` neighbors,
at least `2h-1`. Any subset containing a dense column sees all 44 rows.
Hall's criterion with one dummy row gives a matching of size at least 33.
On the other hand, the columns of block i restricted to A are supported on
the single row x, so their explicit relation v_ix makes the rank at most
33. Requiring one such minor for each of the 84 supports therefore gives

```text
ker G_A=K*v_ix.
```

Require also that the first coordinate of every `L*v_ix` be nonzero and
that every pair of these 84 images have nonzero 2-by-2 determinant. These
are nonzero polynomials: two distinct coefficient rays are independent,
and a linear map to K^2 can separate any prescribed independent pair.
Within a single block this determinant factors as its L-column determinant
times its G-row determinant; for different blocks its independent L
variables likewise prevent identically zero cancellation. This argument
works over every prime field.

## The MDS subcode and its actual MCA vertices

At a simultaneous nonzero specialization set `D=image(G)` and
`C=G(ker L)`. The full minor of G gives `dim D=34`. The augmented minors
imply that L is surjective and that no nonzero vector of C vanishes on any
32 coordinates: if `G_S a=0` and `La=0`, then `Delta_S!=0` forces a=0.
Hence C is an `[64,32]` MDS code. In particular it has all the usual MDS
generalized Hamming weights `d_j(C)=32+j`.

Choose coefficient vectors a0,a1 with `La0=(1,0)` and `La1=(0,1)`, and put
`u0=Ga0`, `u1=Ga1`. This gives the required global rank 34. Write
`L*v_ix=(alpha,beta)`, with alpha nonzero. Then

```text
gamma=beta/alpha,
w=u0+gamma*u1-(G*v_ix)/alpha in C.
```

The 84 scalars are distinct. Each w agrees with the received line on exactly
44 coordinates. Moreover `D(E_ix)=K*(G*v_ix)`, so the quotient criterion
above proves the no-joint clause on that same 44-coordinate set.

These are genuinely isolated points of the threshold-44 arrangement locus,
not uncounted line components. Each point is incident with exactly its 44
agreement hyperplanes, whose total intersection is a point. Any line of
threshold-44 decodings through it would have to be contained in all those
same hyperplanes, which is impossible. The four underlying pencils have
joint cores of size 43, below the threshold. They need no low-degree carrier
assumption and do not contradict a fixed-polynomial-pencil theorem for RS.

## A large-field specialization bound

Multiply the following nonzero polynomials:

| Conditions | Number | Degree each |
| --- | ---: | ---: |
| All augmented minors Delta_S | binomial(64,32) | 34 |
| One full G minor | 1 | 34 |
| One rank-33 minor for each E_ix | 84 | 33 |
| Two-row minors within the four blocks | 840 | 2 |
| First coordinate of L*v_ix | 84 | 2 |
| Pair determinants of L*v_ix | binomial(84,2) | 4 |

Their product is nonzero over every prime field. Its total degree is at
most

```text
B=34*binomial(64,32)+34+84*33+840*2+84*2+4*binomial(84,2)
 =62,309,220,792,048,096,754.
```

A nonzero polynomial of total degree B over F_q cannot vanish at all points
of F_q^N when q>B: induction on the number of variables, or the elementary
polynomial zero bound, gives at most B*q^(N-1) zeros. The production prime

```text
P=365375409332725729550921208179070755120141565953
```

is larger than B. Therefore a simultaneous specialization exists over this
very field. Its primality is the existing `prime_P` theorem in
[_PrizeShapePrimeP30.lean](../../ArkLib/Data/CodingTheory/ProximityGap/Frontier/_PrizeShapePrimeP30.lean);
this note does not rebuild that theorem. No small-characteristic inference
or probabilistic success claim is used.

Run `python3 scripts/probes/astra_mca_mds_rank_obstruction.py` for the exact
finite support, matching, and degree audit. A PASS is evidence for those
calculations; the existence and MCA implications are the written proof.
No numerical matrix, RS realization, production-length counterexample,
universal predecessor result, or Lean closure is claimed.

## Weighted self-duality adds a rank-four constraint

The production half-rate RS code has additional structure absent from the
generic construction above. On its subgroup domain, the nondegenerate form

```text
B(v,w)=sum_{x in Omega} x*v(x)*w(x)
```

vanishes on C times C: every monomial in `X*f*g` has degree between one and
`2k-1=n-1`, and its sum on the subgroup is zero. Since `dim C=n/2`, this
gives `C=C^perp` for B.

For any weighted self-dual C and quotient-rank-two D as above,
`D^perp=C intersect u0^perp intersect u1^perp` has dimension `k-2` and lies
in D. The two conditions on C are independent: a dependent combination
would put a nonzero quotient combination of u0,u1 in `C^perp=C`.
Consequently `D/D^perp` is a nondegenerate four-dimensional space. The
Gram matrix of any collection of error vectors in D therefore has rank
at most four.

Explicitly, for `r_gamma=u0+gamma*u1-w_gamma`, with `w_gamma in C`, put
`q_gamma=(1,gamma)^T`, `h_gamma=(B(w_gamma,u0),B(w_gamma,u1))^T`, and
`S=(B(ui,uj))`. Then

```text
B(r_gamma,r_eta)
 =q_gamma^T*S*q_eta-q_gamma^T*h_eta-h_gamma^T*q_eta.
```

This is a genuine necessary condition, but no scalar-count bound or
weighted-self-dual version of the generic counterexample is proved here.
In particular, a rank-four Gram matrix alone does not limit the number of
vectors with different quotient directions.

The RS determinant argument also retains polynomial root multiplicities.
For a fully covered triple with total joint-core incidence `2n-2`, let Ej
count coordinates owned by exactly j members. Then `E1=E3+2`. The triple
determinant can be nonzero at all E1 single-owner coordinates; a single
Schur-product parity equation cannot count the triple-owner roots twice.
The polynomial divisor argument does count those double roots before
reduction modulo the domain locator. Weighted self-duality alone has not
recovered that information.

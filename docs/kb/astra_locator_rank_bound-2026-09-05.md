# A list bound from the rank of exact error locators

For the punctured rate-one-half parameter shape, a decoded family whose
exact error locators span a vector space of dimension r has at most
`4^(r-1)` members. The argument allows different numbers of errors; it
does not pad locators or assume they belong to one pencil.

At the production parameters, a uniform rank bound of 16 would therefore
give the desired scalar list budget `2^30`. **No such uniform rank bound is
proved here.** This is a written theorem with exact algebra and finite
controls, not a new Lean verification or a prize solution. The three
research agents reached their usage limit before independently reviewing
this generalized argument.

## Statement and pair constraint

Let b>=3 be an integer and let D consist of N=6b-3 distinct nodes over any
field K. Put

```text
k=3b-1, A=4b-1, e=N-A=2b-2, C=N-k+1=3b-1.
```

Fix a received word v on D. For distinct polynomials f_i of degree less
than k agreeing with v at at least A nodes, let E_i be their exact error
sets, d_i=|E_i|<=e, and

```text
Lambda_i(X)=product_(x in E_i) (X-x).
```

All locators are monic and lie in K[X] of degree at most e. Let r be the
dimension over K of their linear span. For a nonempty family,

```text
number of distinct f_i <= 4^(r-1).                     (1)
```

The family is finite even if K is infinite: any candidate is determined
by its values on any k of its agreement nodes. For distinct f_i,f_j the
root bound on their difference gives

```text
|E_i union E_j| >= C,
|E_i intersection E_j| <= d_i+d_j-C.                   (2)
```

The locator determines its exact error set, and that set determines at
most one decoded polynomial because A>=k. Thus the locators are distinct.
In particular rank one permits at most one: proportional monic polynomials
are equal, including when some candidate has no errors.

## Incidence lemma

Suppose a decoded family has the property that every node outside its
common error set belongs to at most L of its exact error sets, where L>=1
is an integer. Then its size is at most 4L.

It suffices to exclude a subfamily of M=4L+1 members. A subset preserves the
incidence cap outside its own common error set: outside that common set
some retained locator is nonzero, so the node was also outside the original
common set. Let g be the number of common errors in this subfamily. By (2),

```text
0 <= g <= 2e-C=b-3.
u=b-3-g,                 0<=u<=b-3,
n'=N-g=5b+u,
a=e-g=b+1+u,
c'=C-g=2b+2+u.
```

Remove those common errors from each E_i and put s_i=d_i-g and S=sum_i s_i.
At each remaining node let r_x be the incidence count. Then

```text
S=sum_x r_x <= L*n',
S=sum_i s_i <= M*a.
```

The total pair intersection J satisfies, by (2),

```text
J=sum_x binomial(r_x,2)
 <= (M-1)*S - M*(M-1)*c'/2.
```

Cauchy--Schwarz gives `2J>=S^2/n'-S`, so necessarily

```text
F(S):=S^2/n'-(2M-1)*S+M*(M-1)*c' <= 0.               (3)
```

The quadratic F is decreasing between zero and either upper bound L*n'
or M*a. Indeed `L<M-1/2`, and `a<n'/2` follows from u<=b-3;
also M>1. Alternatively, for S<=B and B equal to either upper bound,

```text
F(S)-F(B)=(B-S)*((2M-1)-(B+S)/n') >= 0.
```

Consequently both endpoint values must be nonpositive. Their exact
expansions at M=4L+1 are

```text
F(L*n') = L*(3*(1-L)*b+32*L+8+3*(3*L+1)*u),

F(M*a) = M/n' * (
  (b+1)*((4*L-4)*b+4*L+1)
  - ((12*L+4)*b-8*L-1)*u).
```

The first forces an upper bound on u and the second a lower bound:

```text
u <= Ulo=(3*(L-1)*b-32*L-8)/(3*(3*L+1)),
u >= Uhi=(b+1)*((4*L-4)*b+4*L+1)/((12*L+4)*b-8*L-1).
```

Both denominators are positive for b>=3,L>=1. But Uhi>Ulo, since the
cross-multiplied difference is exactly

```text
3*(3*L+1)*(b+1)*((4*L-4)*b+4*L+1)
 - (3*(L-1)*b-32*L-8)*((12*L+4)*b-8*L-1)
 = 5*(4*L+1)*((24*L+4)*b-11*L-1) > 0.               (4)
```

For positivity, the last parenthesis is at least 61L+11. This contradiction
proves the incidence lemma. No equal-degree assumption was used.

## Induction on locator rank

The rank-one case was proved above. Suppose (1) holds through rank r-1,
where r>=2, and choose a hypothetical subfamily of size

```text
M=4^(r-1)+1=4L+1,       L=4^(r-2).
```

Let W be its locator span, of dimension at most r. Outside its common error
set, evaluation at a node x is a nonzero linear functional on W. The
locators vanishing there therefore span a space of dimension at most r-1.
They are still exact locators of an actual decoded subfamily around the
same received word, so induction bounds their number by L. The incidence
lemma contradicts the chosen size M. This proves (1).

This also bounds the number of distinct extrapolated values if one first
selects one decoded polynomial per value and bounds the rank of that
selected family. A rank bound for a value-selected family alone is not a
rank bound for the entire decoded list.

## Production consequence and remaining gap

For b=178956971, the unpunctured domain has n=6b-2=2^30 nodes, k=n/2,
and the predecessor error radius is e/n with e=357913940. Any polynomial
with at least 4b agreements on that domain has at least A=4b-1 agreements
after one node is removed. Therefore a universal bound r<=16 for every
such punctured scalar list would imply

```text
full-domain scalar list size <= 4^15=1073741824=n.
```

The production field also passes the exact
[interleaving transfer gate](astra_interleaved_projection-2026-09-05.md),
so a uniform scalar list cap would transfer to every positive interleaving
arity. No scalar rank cap is supplied by that transfer. Rank 17 already
allows `4^16=4294967296` in (1), above the budget.

The available linear key-equation relaxation has much larger dimension;
replacing it with a rank bound for its actual split exact-error solutions
is an additional theorem, not an automatic consequence. This note neither
proves the universal MCA predecessor bound nor identifies the full sharp
list-decoding threshold, and it does not handle the other prize rates.

## Reproduction and controls

Run from the repository root:

```sh
python3 scripts/probes/astra_locator_rank_check.py
```

The checker verifies the two endpoint expansions and identity (4) as
integer polynomial identities, not merely at sampled parameters. It also
checks rational endpoint inequalities across a bounded grid and reconstructs
actual decoded families on 21 nodes over F101, with b=4:

* Four degree-six exact locators of rank two attain the bound of four.
  These are the sharp generic-domain pencil construction from the
  [locator-pencil note](astra_mca_locator_pencils-2026-09-05.md).
* Changing the received value at their shared error node to match one
  candidate gives heterogeneous exact error degrees 5,6,6,6 and locator
  rank three. Pair-union and evaluation-kernel constraints are rechecked.
* A received codeword supplies the rank-one, empty-error endpoint.

The finite fixtures check the implementation and the exact-error setup;
they do not enumerate all decoded polynomials over F101 or establish the
missing production rank bound. No independent review of this generalized
proof or new Lean kernel check is claimed.

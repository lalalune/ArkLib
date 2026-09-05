# Full quadratic contact has zero source space for three decoded candidates

The [Riccati obstruction](astra_riccati_contact_obstruction-2026-09-05.md)
extends to every source of total degree at most two in the value Y and
derivative R, including YR and R^2. At the production profile, if a received
word has three distinct decoded candidates, every source with the specified
contact conditions and weighted degree cap is zero, at every positive
contact order. Fifteen statements, including the complete implication from
actual agreements, pass local Lean 4.30.0-rc2 with only standard axioms.

This excludes a particular interpolation construction. It does not exclude
higher-degree sources, other contact conditions, or equations obtained by
another argument. It supplies no new list bound and does not solve the prize.

## Exact scope and coefficient conditions

Work over a field K on a finite set S of distinct nodes. Put

```text
N = 1073741823, w = 536870911, A = 715827883, |S| = N.
Q(X,Y,R) = a(X)+b(X)Y+c(X)Y^2+d(X)R+e(X)YR+f(X)R^2.
weighted_degree_(1,w,w-1)(Q) < m A, m > 0.
```

At x with received value v(x), substitute X=x+t and Y=v(x)+tR+z,
and demand that every term of weight less than m vanish, with weights
wt(t)=1, wt(z)=2, wt(R)=0. Collecting the six coefficients gives the
following necessary and sufficient local conditions. Write T=X-x; all
polynomials on the right are in K[X].

| Coefficient | Polynomial divisible by the stated power of T | Power |
| --- | --- | --- |
| constant | a+v b+v^2 c | m |
| R | d+v e+T(b+2v c) | m |
| R^2 | f+T e+T^2 c | m |
| z | b+2v c | max(m-2,0) |
| Rz | e+2T c | max(m-2,0) |
| z^2 | c | max(m-4,0) |

The [Lean source](../../scripts/probes/astra_quadratic_contact_obstruction.lean)
proves the expansion as a ring identity and takes these explicit polynomial
divisibilities as its contact definition. It does not invoke a separate
multivariate-polynomial contact API. Its `FullProductionContact` structure
also records all six weighted degree caps, guarded by nonzero coefficients.
The guards matter when a monomial's weight already exceeds mA.

The main theorem `production_quadratic_contact_zero` takes three distinct
polynomials of degree at most w, and three subsets of S of size at least A
where they actually equal the same received word. It concludes that all
six source coefficients vanish. Candidate solution identities are proved
inside the theorem; they are not additional hypotheses of this final result.

## Eliminate the square derivative term

Subtract T times the Rz coefficient from the R^2 coefficient and add T^2
times the z^2 coefficient. The result is f. Hence

```text
T^qF divides f,
qF = min(m, 1+max(m-2,0), 2+max(m-4,0)).
```

The values are qF=1 for m=1,2, qF=2 for m=3, and qF=m-2 for m>=4.
The distinct node powers are pairwise coprime, so a nonzero f has degree
at least N qF. But its cap is deg f+2(w-1)<mA, and

```text
N qF + 2(w-1) >= m A
```

for every positive m at production. Thus f=0. This conclusion needs no
decoded candidates and is independent of the received word.

## Eliminate the mixed term, including the exceptional contact order

With f=0, cancelling T in the R^2 condition gives
T^(m-1) dividing e+T c. Combining this with the Rz condition forces
T^qE to divide e, where qE=1 at m=2 and qE=max(m-2,0) otherwise.
The degree cap deg e+2w-1<mA forces e=0 for every m except three.

At m=3, the remaining conditions give, for every x in S,

```text
T divides e,
T^2 divides d+v(x)e,
deg e <= 1073741827,
deg d <= 1610612738.
```

For a candidate g, the polynomial W=d+g e has a simple root at every node.
At every agreement node, T divides g-v(x), so T^2 divides
(g-v(x))e. Together with the second displayed condition, this makes the
root of W double at each agreement node. Consequently, if W is nonzero,

```text
deg W >= N+A = 1789569706,
deg W <= max(deg d, deg e+deg g) <= 1610612738.
```

This is impossible. Hence d+g e=0 for every decoded candidate. Two distinct
candidates give (g0-g1)e=0, then e=d=0. At other contact orders the earlier
Riccati result eliminates d once e=f=0.

The distinction at m=3 is necessary: for the zero received word on a domain
with locator Z, the source `-Z'(X)Y^2+Z(X)YR` satisfies contact order three
and the cap at the profiles considered here. Its YR coefficient is nonzero.
Thus the multiple-candidate hypothesis cannot simply be dropped.

## Extract the algebraic identities and finish

Once d=e=f=0, the constant, R and R^2 conditions say that T^m divides

```text
a+v b+v^2 c,   T(b+2v c),   T^2 c.
```

At an agreement node write g-v=T h. The identity

```text
a+b g+c g^2 = (a+v b+v^2 c) + h*T(b+2v c) + h^2*T^2*c
```

preserves multiplicity m. The product of node powers on the agreement set
has degree at least mA, while the source caps imply deg(a+b g+c g^2)<mA
unless the polynomial is zero. It must therefore be zero. Three distinct
polynomials cannot be roots of a nonzero quadratic over K(X), so a=b=c=0.
Lean checks this last statement directly over K[X]. No characteristic-zero
differential equation theorem is imported.

## Verification and finite controls

All fifteen named reports in the new module passed local Lean 4.30.0-rc2
without diagnostics, using only propext, Classical.choice and Quot.sound.
The production build helper and the
[two-pin CI audit](../../.github/workflows/proximity-strip-proof.yml) include
the module and require every report. The new CI run is pending at this revision.

Run:

```sh
python3 scripts/probes/astra_quadratic_contact_check.py
```

The exact checker verifies three-candidate words on two smaller domains:

| Field and domain | N,w,A | Actual agreements per candidate | Full source ranks at m=1,2,3,4 |
| --- | --- | --- | --- |
| F101, mu20 plus zero | 21,10,15 | 15,15,15 | 26,104,194,284 |
| Actual production prime P, mu32 plus zero | 33,16,23 | 24,24,24 | 38,152,290,428 |

Every displayed rank equals the complete number of source columns, so each
of these eight maps has zero kernel. The generator order is checked exactly,
including the odd factors in order 20. These are small domains; using the
production prime does not make the second test production-sized.

The checker separately constructs the nonzero order-three source for the
zero word over F101: degree 40 below cap 45, with all 231 collected contact
conditions verified using Hasse coefficients independently of matrix
elimination. It also checks 504 integer profiles. These finite checks support
the implementation; the all-multiplicity production assertion is the Lean
theorem, not an extrapolation from them.

The earlier upper-bound construction and the universal lower-bound problem
retain their separate status. This obstruction gives no bound on the number
of outside-factor fibres in an arbitrary production list.

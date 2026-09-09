# Independent audit of the new three-source first-step closure

2026-09-08. Reviewed `../08-exceptions/three-source-closure.md` and its stated
preliminary lemmas in `../08-exceptions/REPORT.md`. No code or proof text was
imported into the independent checker. All changes remain in this review lane.

**Verdict: mathematically sound as a written theorem for s>=20.** I found no
gap in its cardinality-three branch closure after checking the cases below.
It is not Lean-formalized. Combined with the independently reviewed
cardinality-four argument, the remaining universal first-step obligation is
confined to full high-core joint lists of cardinality at most two.

Use n=4s, k=2s, t=3s-1; J denotes the complete list of joint RS pairs with
exact cores at least t. The claim is `|B|<=n` under the hypothesis `|J|=3`.

## Points checked adversarially

1. **The four sets are legitimate.** At an exceptional scalar, the three
   projected source polynomials are distinct, and the chosen witness decoder
   differs from all three. Consequently their three exact joint cores plus
   the chosen witness support are four sets of size at least t with pairwise
   intersections at most k-1. Using joint cores, rather than maximal scalar
   agreement sets, does not invalidate either the incidence or defect bound.

2. **Defect and outside points.** The identity
   `binom(r,2)-3r+6=(6,3,1,0,0)` for r=0,...,4, the pair budget, and the
   membership lower bound give `6N0+3N1+N2<=6`. The independently proved
   puncture inequality gives N0=0. Therefore every point outside the three
   original cores belongs to the exceptional witness and uses three defect
   units, proving |O|<=2. Points in at most one original core use at least
   one unit, proving |L|<=6.

3. **Enough common roots.** With primitive carrier degree d<=1, each pair
   of original cores intersects at most k-1-d times. Thus
   `3|Z|+|M|<=3(k-1-d)` and `|Z|+|M|+|L|=4s` imply
   `|Z|<=s+1`, `|M|>=3s-7`. Each witness can omit at most six M points.
   Two witnesses therefore share at least `3s-19` M points. At s=20 this
   is 41 roots for a polynomial of degree at most k=40; the surplus grows
   as s increases. At shared points the two projected residuals are
   scalar multiples of their respective carrier projections, proving the
   polynomial identity `T_delta F_gamma = T_gamma F_delta`.

4. **The common polynomial H is valid, including constant projections.**
   For d=0, T_gamma is a nonzero constant outside the covered set: a zero
   projection would collide the original source projections. Division is
   valid and gives H of degree at most k-1. For d=1, primitive A,B cannot be
   proportional. Two distinct T polynomials are coprime and at least one
   is linear, although one may be a nonzero constant. Coprimality implies
   divisibility of each F by its T; the linear member bounds H by k-2.
   Applying the identity against a fixed exceptional scalar propagates the
   same H to every chosen exceptional witness. Thus z_* is an actual joint
   RS pair, and cannot equal any member of J because that would make the
   corresponding exceptional scalar covered.

5. **Constant-carrier exceptions use O.** At a point in the union of the
   original cores, both received and z_* lie on the same carrier line.
   A nonzero residual cannot have zero scalar projection when T_gamma is
   a nonzero constant. Every original MCA witness projected from z_* must
   nevertheless have a nonzero residual somewhere on its support, so that
   point lies in O. A fixed nonzero residual admits at most one scalar.
   Consequently there are at most two exceptional scalars. The cases of
   fewer than two exceptions need no common-source construction.

6. **Linear-carrier choice of a witness.** Once there are at least three
   exceptional scalars, construct common z_* first. At most two scalars can
   cancel its nonzero residuals at the at most two O points. Select an
   exception outside that set. Every failure of joint agreement on its
   support then lies in the original core union and at a root of its
   nonzero degree-at-most-one carrier projection. Thus z_* has core at
   least t-1. This argument excludes only nonzero residual cancellations;
   points with zero residual cause no problem and are not charged.

7. **Mixed-core coverage.** All four sources have the same primitive
   degree-one carrier and distinct scalar polynomials of degree at most
   k-2. Their exact joint cores consequently intersect at most k-2 times.
   If some coordinate were uncovered, their total membership R on n-1
   points would satisfy R>=12s-5 and
   `R^2-(n-1)R <= (n-1)12(k-2)`.
   The left side is increasing in this range. Substituting the lower bound
   gives a contradiction with the exact positive gap `32s-4`. This step
   permits the fourth core to be t-1 rather than t; no assumption that
   z_* belongs to J is made.

8. **Counting all bad scalars.** Choose one actual witness per exceptional
   scalar. The common-H identity represents those witnesses by z_*. Every
   covered bad scalar has some witness represented by the original three
   sources. After mixed-core coverage, the received pair is on their common
   carrier line at every coordinate. The original same-support MCA
   obstruction forces a nonzero residual cancellation for the represented
   source at some point. Coprimality prevents A(x)=B(x)=0, so each point
   permits at most one scalar. This proves |B|<=n without claiming that
   every possible decoder at a scalar must have the selected representation.

## Arithmetic evidence and limitations

`three_source_arithmetic.py` checks the incidence and mixed-core gap identities
as polynomial identities in Z[s], exhausts the finite d,L correction cases,
and checks the s=20,21,2^28 parameter boundaries. The overlap surplus is
exactly s-19 and the small-exception budget slack is s-5, which prove the
stated numerical inequalities for all s>=20. No small-field safety verdict,
production-domain enumeration, or Lean closure is inferred from these checks.

For publication, explicitly say "choose one witness decoder for each
exceptional scalar" in the common-H section. The proof already has that
meaning, and it is sufficient; no uniform classification of all possible
decoder choices is needed. No substantive correction to the theorem is
required by this review.

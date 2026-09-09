# Independent review of the two-near-source theorem

2026-09-08. Reviewed read-only:

* `08-singleton/two-near-source.md`
* `08-singleton/check_near_source.py`

**Verdict: approve the written theorem as stated; no mathematical gap found.**
The scope is n=4s, k=2s, t=3s-1, s>=94, with two distinct joint codeword
pairs whose cores have sizes at least t and t-1. This does not establish
the existence of the second pair in a general singleton instance. It is
not Lean verification.

## Primitive-carrier and profile setup

The factorization of the polynomial pair difference as H(A,B), with A,B
coprime, is valid over any field. A common core point forces H to vanish
because coprime A,B cannot both vanish there. The k-3 intersection bound
therefore gives d<=2. The improved union bound uses deg H<=k-1-d, not the
weaker k-1 bound, and correctly gives h<=2-d.

For d>=1, A and B are linearly independent over the field. Otherwise a
nonconstant component would be a common polynomial factor; a zero
component also forces the other to be constant by coprimality. Thus no
T_gamma is the zero polynomial. Excluding its at most d roots from an
actual witness costs at most d points. Together with the h holes, this
leaves at least t-2 fixed-word agreements.

The rational list bound correctly counts distinct rational functions,
not syntactic numerator/denominator presentations. Cross multiplication
for distinct functions gives a nonzero polynomial of degree at most
(k-1)+2=k+1. Poles have already been excluded from agreement sets.
The two known profiles 0,H satisfy the same degree and agreement bounds,
and are distinct because the chosen codeword pairs are distinct.

## Nonliftable multiplicity, including d=2

For distinct gamma,delta, every common factor of T_gamma,T_delta divides
their difference (gamma-delta)B and then A. Hence they are coprime.
If the same rational profile occurs at both parameters, its reduced
denominator divides both polynomials, so it is a polynomial.

At most one finite gamma can cancel the top degree-d coefficient of
A+gamma B. If deg B<d, none can. Thus at least one of two distinct
parameters has deg T=d. Its numerator degree bound forces
deg R<=k-1-d. This establishes the claimed at-most-one occurrence of a
nonliftable profile, including the exceptional parameter where T has
smaller degree. No regular parameter dependence of the chosen decoders
is assumed.

When d=2, the geometry forces h=0. If any nonliftable profile occurs,
there are at most three liftable profiles, including the selected two.
The bound 3s+8 deliberately overcounts by allowing an extra source and
two nonliftable profiles simultaneously; this is harmless. If all
profiles lift, every coordinate of the received pair is on the common
carrier line, so the same-support obstruction injects bad scalars into
coordinate directions. Degree two does not introduce a factor of two:
at each fixed x, the equation A(x)+gamma B(x)=0 has at most one gamma.

## d=1, h=1: weak profiles

For a weak source, actual joint core size <=t-2 implies every t-point
witness has at least two points with nonzero source residual. Inside U,
a nonzero residual is a scalar multiple of the primitive carrier, so
projection cancellation forces a root of the nonzero degree-at-most-one
polynomial T_gamma. At most one witness residual can be cancelled this
way inside U. The unique hole o must therefore be in the witness with
nonzero residual cancellation. For that fixed source, the residual at
o is fixed, and its affine equation has at most one gamma. This correctly
bounds each weak profile by one scalar even if it has many decoders or
witness supports at that scalar.

If there are at most three strong profiles, the selected cores contribute
at most s+1 and s+2, an additional strong profile at most s+2, and all
other profiles together at most two. Again the count is conservative
when there are three strong profiles, since then at most one other
profile remains. Thus 3s+7 is a valid bound.

## d=1, h=1: four strong profiles

Four strong profiles exhaust the list and all lift. Distinct scalar
polynomials have degree at most k-2, so their joint-core intersections
have size at most k-2. If the hole were outside every core, their total
membership R on N=n-1 points would satisfy

    R>=12s-7,
    sum binom(r_x,2)<=12s-12.

The pointwise integer inequality binom(r,2)>=2r-3 for r=0,...,4 yields
the lower bound 2R-3N>=12s-11, a contradiction. The sign and one-unit
slack are correct. The first two sources already cover U, so placing
the hole in any of the four cores proves that the four cores cover D.
The final common-carrier direction count applies to every chosen actual
bad witness because the profile list was formed from those witnesses.

## Arithmetic script check

Executed the exact arithmetic prefix of `check_near_source.py` read-only,
stopping before its output-file writes. All assertions passed for
s=94,95,128,256,2^28. In particular the production five-profile gap is
`72057568804995117`, the non-saturating count is `805306376<n`, and the
four-strong integer contradiction has gap one. No files in the reviewed
agent's directory were modified.

The arithmetic script checks numerical identities, not the polynomial
lemmas. The latter were checked by the independent written reasoning
above. No additional hypothesis or repair is requested.

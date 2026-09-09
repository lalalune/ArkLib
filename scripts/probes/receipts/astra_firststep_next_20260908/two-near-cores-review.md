# Independent review: two short cores and the final realization obstruction

2026-09-08. Reviewed read-only:

* `08-singleton/two-short-cores-final-pattern.md`
* `08-singleton/check_final_pattern.py`

**Verdict: approve the written reductions, incidence census, Pluecker
degree bounds, and conditional construction. No substantive gap found.**
The theorem concerns n=4s, k=2s, t=3s-1 and s>=136. It does not assert a
production realization of the polynomial configuration. In particular,
this is neither a universal two-short-core safety theorem nor an actual
first-step disproof. No Lean verification is claimed.

## 1. Reduction and resolved branches

The two selected cores have intersection at least k-4. Primitive
factorization gives d<=3 and h<=3-d. Every normalized actual witness
loses at most h outside points and d denominator roots; it therefore
agrees with the fixed scalar word at least t-3 times. Cross multiplication
of distinct profiles gives a nonzero polynomial of degree at most k+2.
The five-list gap s^2-136s+80 is positive throughout the stated range.

For d=0, normalization must exclude the possible zero T_gamma. The
degree-zero branch explicitly makes this exclusion and charges the
parameter separately. For d>=1, no T_gamma is the zero polynomial.

The nonliftable multiplicity proof survives d=3: two different T_gamma
are coprime, their common profile is polynomial, and at least one has
the full degree d. Thus its degree is at most k-1-d. No regularity in
the chosen decoder family is assumed.

The source counts in all resolved branches are valid conservative sums.
For d=2,h=1, a source core at most t-3 forces three nonjoint witness
points, of which at most two can be carrier roots in U, leaving a hole
cancellation and at most one parameter. Four strong cores cannot miss
that hole: their integer incidence lower bound exceeds the pair budget
by one.

For d=1,h<=2, a weak core at most t-2 forces a hole cancellation, giving
at most two parameters per weak profile. With four strong profiles, the
integer incidence bound excludes two uncovered coordinates. If the
four cores cover D, the one-direction-per-coordinate count is valid.
The remaining one-hole configuration is explicitly retained rather
than incorrectly declared safe.

## 2. Three-pattern and edge census

On N=n-1 covered coordinates, R>=12s-8 and pair incidence <=12s-12.
The integer inequality binom(r,2)>=2r-3 implies R<=12s-8, so each of
the four cores is exactly t-1. The residual identities are

    N1+N4<=1,
    2N1+N2-N4=5.

These yield exactly A=(0,5,0), B=(1,3,0), C=(0,6,1) for (N1,N2,N4).
I independently recovered these identities before reading the final
file. The edge census also checks out: source-core equality determines
the four omitted-source triple block sizes from the six double-edge
counts, and the script enumerates every nonnegative composition of
the prescribed double-node total. All triple block sizes are positive
for s>=136. The six individual root bounds produce six labeled A
patterns, one B pattern with fixed singleton owner, and one C pattern.

These are necessary incidence patterns. Additional unrecorded pair
coincidences can only consume more root budget; no polynomial existence
is inferred from the incidence enumeration.

## 3. Pluecker degree reduction

Distinct scalar profiles make all three displayed products nonzero.
Each has degree at most n-4. A triple ownership point supplies a linear
factor to all products, and a quadruple point supplies its square.
Thus their gcd has degree at least N3+2N4, leaving quotient degrees at
most 2,1,2 for A,B,C. The identity V1-V2+V3=0 has the correct signs.
This uses polynomial divisibility, not derivatives, and is valid in
every characteristic. It gives no realization or exclusion by itself.

## 4. Conditional field construction and actual MCA witnesses

Assuming scalar polynomials of degree at most k-2 realize one of the
patterns on the actual D minus one point o, the canonical source pairs
(X*f_i,f_i) belong to the full RS code. The received values on the
covered coordinates preserve the exact t-1 cores.

The ordinary parameters -x are distinct and finite. At any nonquadruple
coordinate, a source nonowner supplies a nonzero residual cancellation.
Its core plus that coordinate has size t. A competing joint pair would
agree with that source on t-1>=k points, forcing both polynomials equal
and contradicting the nonowner point. The same argument applies to
every hole cancellation. These are original same-support MCA witnesses
against all codeword pairs, not merely the selected four.

The six pair-degree budgets total 3n-12. Owned pair incidences use
3n-13 in A and 3n-12 in B/C. Consequently at most one pair can collide
at o in A, so at least three local values are distinct; in B/C all four
are distinct. This root-budget argument is sufficient even if some
pair differences have smaller degree or additional roots elsewhere.

The forbidden-hole conditions are genuinely affine lines in F_P^2:
one carrier line, at most four denominator lines, and at most
4(n-1) ordinary-collision lines. Each has P points. Since
P>4n+1, their union has fewer than P^2 points. The chosen hole is
off the carrier, its ratios are finite, pairwise distinct for distinct
local values, and disjoint from every ordinary parameter. No random
choice, assumed genericity, or uncounted field exception is used.

The resulting counts would therefore be at least n+2,n+3,n+2. These
strictly exceed the production 2^-128 budget. The hypotheses include
the unconstructed production polynomials; the conclusion remains
conditional until they are found and checked.

## 5. Empty high-core joint list

The first proof is valid: a new core of size at least t would add a
fifth distinct joint pair to four exact t-1 pairs. The generic joint
pair root cap k-1 and the positive gap s^2-36s+20 exclude this.

The carrier proof is valid independently. The determinant involving
the hypothetical source and two selected sources has more forced
root multiplicity than its n-2 degree bound. Its vanishing implies
p=Xq, with deg q<=k-2. The off-carrier hole cannot be in its core.
The fifth scalar-profile contradiction on n-1 points has the stated
positive gap s^2-9s+10. Neither argument supplies the four starting
polynomials.

The proposed simpler replacement for the determinant proof is also
approved: a hypothetical source (p,q) with core at least t agrees with
the carrier relation p=Xq at at least t-1 points in U. The polynomial
p-Xq has degree at most k, while t-1>k, so it vanishes identically.
The rest of the scalar-profile argument is unchanged.

## 6. Publication wording and conditional exact threshold

The covering condition must be stated pointwise: **for every x in U,
there is an i with f_i(x)=w(x)**. This is the meaning used throughout
the incidence and witness arguments. The earlier wording could be
misread as one fixed polynomial agreeing on all U; that reading is
neither intended nor needed.

The proposed conditional threshold conclusion is correct. A production
realization of any of A/B/C would be unsafe at
delta_1=268435457/2^30. Monotonicity then gives deltaStar<=delta_1,
while the established UDR theorem and its half-open Hamming plateau
already give deltaStar>=delta_1. Therefore that realization would prove
the exact **supremum** deltaStar=268435457/2^30 for this prime-field,
rate-half code. Safety would fail at the supremum itself. This is
conditional on the polynomial realization and does not solve the
other rates, fields, or full grand challenge.

## Checks and limits

Executed the arithmetic/census prefix of check_final_pattern.py
read-only, stopping before its output-file writes. The census counts
6,1,1 and all assertions at s=136,137,256,2^28 passed. Independently
checked that each conditional production numerator times 2^128
strictly exceeds P. No files in the reviewed directory were modified.

The core result to preserve is an explicit finite polynomial-realization
obstruction, with a verified conditional route from any realization to
an empty-high-core, over-budget original-MCA instance. The existence
problem on the certified subgroup remains open.

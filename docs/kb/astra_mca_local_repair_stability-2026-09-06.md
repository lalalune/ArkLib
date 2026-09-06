# Exact stability and scalar trade for one/two-coordinate repairs

This is a restriction on locally repairing the existing production three-pencil
witness, not a universal predecessor bound. Arbitrary new decoding polynomials
are excluded only when they retain the stated number of old agreements.

## Setup and general fixed-pair bound

Let n=6h+4, k=3h+2, t=4h+2 and S=t+2, with h>=1. Put
m=n-t=2h+2. The three degree-<k pairs P_A,P_B,P_C have exact cores of
size t in the old received pair u. Each ordinary coordinate belongs to exactly
two cores, and the two private coordinates belong only to A. Require the three local pair
values at each private point to be pairwise distinct; the actual construction
has this property by its nonzero determinant there. The old residuals
are nonzero in all 3m=n+2 absent-core slots. Suppose those slots have at least
3m-1 distinct projective directions. Thus at most one direction is repeated,
with exactly two occurrences if a repeat exists.

For any received pair whatsoever, a fixed pair with exact core c contributes
at most

    floor((n-c)/max(1,S-c)) <= n-S+1 = m-1

actual MCA-bad projective scalars. A bad event must have at least S-c outside
agreements, and the same-support no-joint clause requires at least one even if
c>=S. Each nonzero residual cancels in exactly one projective direction.
Consequently **these three fixed pencils supply at most 3(m-1)=n-1**, after
arbitrary received-value changes and with all their possible supports allowed.
This elementary fixed-pencil observation complements, rather than extends, the
existing fixed-pencil predecessor note.

## Escape from the old pencils requires macroscopic core changes

Change the received pair only on E, |E|<=r. If a new scalar decoder p of degree
<k at direction [a:b] agrees on a support T and

    |T intersect (S_i minus E)| >= k,

then p=a f_i+b g_i by the polynomial root bound. Hence every decoder outside
all three old scalar specializations must satisfy, for each i,

    |S_i minus T| >= t-r-(k-1) = h+1-r.                 (1)

The same statement holds for a new jointly explaining polynomial pair outside
the old three pairs, by applying uniqueness to both components. The supports
and polynomial choices may depend arbitrarily on gamma: retaining k unedited
old-core points already forces the old specialization at that gamma.

At production h=178956970. With one edit an escaping decoder must omit at
least 178956970 points of EACH old core; with two edits, at least 178956969.
Thus this is a stability statement for locally retained cores, not an
exclusion of arbitrary gamma-dependent supports.

## Exact edit identity

For pencil i, define its old residual R_i(x)=u(x)-P_i(x). For a direction
[a:b], write l(v)=a v_0+b v_1. If u' differs on E, its exact scalar agreement
count is

    N'_i([a:b]) = t + m_i([a:b])
                 + sum_(x in E) (1[l(u'(x)-P_i(x))=0]
                                 -1[l(R_i(x))=0]),    (2)

where m_i counts old nonzero residual slots with that cancellation direction.
The identity counts all joint and scalar-only agreements, including infinity.
It shows directly that a changed absent-core coordinate can add at most one
agreement for an old direction. Making that coordinate jointly equal to P_i
adds an agreement for every direction which did not already cancel there;
a nonzero replacement residual can add an agreement at only one direction.

For quantitative bounds, take E to be the set of genuinely changed values,
put r=|E|, and set

    a_i = |E intersect S_i|,
    b_i = #{x in E : u'(x)=P_i(x)},
    delta_i=b_i-a_i, q_i=r-b_i.

The new exact core size is t+delta_i; q_i is the number of new nonzero residuals
at edited coordinates. Call a core lifted if delta_i>0. A lifted pencil
contributes at most m-delta_i bad directions (using the no-joint condition if
its core already has size S).

Outside the possible one globally repeated OLD direction, an old unchanged
residual direction occurs at most once. For delta_i<=0, reaching S therefore
requires at least 1-delta_i edited nonzero residuals of the same direction.
The number of such directions for this pencil is at most

    floor(q_i/(1-delta_i)).                            (3)

The single exceptional old direction can add at most one to the UNION, not
one per pencil. Therefore, with L lifted pencils, the upper bound is

    L*m - sum_(delta_i>0) delta_i
        + sum_(delta_i<=0) floor(q_i/(1-delta_i)) + 1.  (4)

If all old slot directions are distinct, the final +1 is absent.

## One and two edits

At an ordinary coordinate missing owner j, a genuine change can create a new
joint value only for j; otherwise it creates no joint value. At a private
coordinate, it can create a new joint value only for B or C, otherwise none.
The three private values are distinct (indeed noncollinear) by the old
nonvanishing determinant. Thus there are exactly nine possible membership
transition types: ordinary j to j/none for j=A,B,C, and private A to B/C/none.
Their one- and two-step sums give the following maxima in (4):

| Edited coordinates | Lifted cores | Bound |
| --- | --- | --- |
| 1 | 0 | 3 |
| 1 | 1 | m+1 |
| 2 | 0 | 5 |
| 2 | 1 | m+2 |
| 2 | 2 | 2m-1, improved below to 2m-2 |

The nine-state tabulation is certified exactly by `python3 scripts/probes/astra_mca_local_repair_trade_check.py`.
The upper bounds use necessary event conditions and remain valid when h=1;
the later sufficient no-joint statement requires h>=2.
For two lifted cores, both edits must be at the two private points and assign
one to B and one to C. The core changes are (-2,1,1). A has lost two joint
agreements and cannot reach S using a direction with at most one old residual
occurrence. If it used the exceptional old double direction, BOTH edited
coordinates would have to cancel it. But cancellation of new B-A at the
first point is the direction of the old absent-B residual there. That is a
third old occurrence, in addition to A's two: impossible. Thus A contributes
nothing and B,C each contribute at most m-1. This removes the exceptional +1
in this case. The same reasoning works over every field satisfying the setup.

Since m>=4, the final bounds are

    at most one edit:  m+1,
    at most two edits: 2m-2.                           (5)

For completely distinct old slot directions, the one-edit bound improves to
m. These bounds permit arbitrary replacement vectors, not just changes to
one of the three local pair values. When h>=2 and r<=2, every new core has size at least
t-2>=k. Hence any counted direction that attains S and has a nonzero residual
has the actual same-support no-joint property by uniqueness on its new core.

At production the archived n+1 distinct fingerprints imply the required
at-most-one-repeat assumption without resolving its repeated fingerprint.
The resulting projective upper bounds for the OLD THREE PENCILS are
357913943 after at most one edit and 715827882 after at most two edits. These
are also upper bounds on their finite bad scalars. No production scan was run.

## Exact production-field length-16 control

`python3 scripts/probes/astra_mca_local_repair_check.py` independently reconstructs the actual degree-seven
three-pair witness on mu16 over the production prime, using dense polynomial
interpolation and exact division. Its 18 old residual directions are distinct.
It tests every change to another local pair value: 18 one-coordinate choices,
151 choices at two distinct coordinates, and the unchanged word.

For each of these 170 words, it checks all C(16,12)=1820 supports by exact
Vandermonde quotient arithmetic. The four quotient rows annihilate all
monomials of degrees 0 through 7. If the two received quotient vectors have
rank zero, the support is jointly explained and is rejected. If rank one,
its unique projective kernel direction is counted; rank two contributes none.
This is the original RS same-support no-joint test, and does not restrict the
decoding polynomial to the three old pencils.

Testing exactly size-12 supports suffices for all larger supports too. Given
a non-joint larger agreement support, choose eight anchors. They determine
a putative pair; a ninth point violates at least one component. Extend these
nine points to twelve within the agreement support. The same decoder works
and no joint pair can explain that twelve-point support.

The complete projective bad-set maxima are 0,5,10 for zero, one, two edits.
All qualifying decoding polynomials in all tested size-12 supports are old
pencil specializations; this is checked on eight anchors, not inferred from
agreement of scalar counts. The best two-edit control transfers the two
private coordinates from A to B and C, giving cores (8,11,11), five directions
from B and five disjoint directions from C. It attains the two-edit bound 10.
This control is length 16 only; it is not a production witness or an exhaustive
search over arbitrary replacement values. No claim that every production
candidate decoder remains in the old pencils is made.

Run both commands above from the repository root. The field and full-size
count are documented in the [production certificate](astra_mca_production_count-2026-09-05.md).
The census probe prints a summary by default; add `--verbose` for all 170 cases.
Independent agent review checked the general trade bound, exceptional-direction
case, and agreement-uniqueness argument. These results are written proofs and
exact finite computations, not Lean formalization or a universal MCA bound.

# Four points on a locator line remain possible: a cyclotomic inversion family

The later [reciprocal-balance obstruction](astra_mca_reciprocal_balance-2026-09-05.md)
proves that this particular symmetry type cannot extend to a dyadic
n=6b-2. The allowed reciprocal symmetry type remains open.

This is a general-field written sharpness construction for the abstract six-locator assumptions. It disproves a uniform strengthening from “no five locators lie on one line” to “no four lie on one line,” even after imposing actual cyclotomic divisibility, full cover, pairwise gcd degree at most b, balanced syzygies, and a birational locator map. It is a **non-dyadic length-10 example with b=2**, not an example at the production parameters, and supplies no MCA budget violation. The production prime is 3 modulo 5, so it does not even contain mu_10.

This uses only the structural pairwise gcd bound at most b. The existing [incidence-feasibility](astra_mca_incidence_feasibility-2026-09-05.md) four-point-line lower threshold b>=8 additionally assumes the saturation-strengthened bound at most b-2. Our common first-four gcd has degree b=2 and fails that stronger assumption, so there is no contradiction. The calculation below confirms that the example is not saturated or over budget.

## Construction over every field containing ten distinct roots of unity

Let K contain all ten distinct roots of X^10-1, so char K is neither 2 nor 5. Set b=2, n=10 and Omega=mu_10. Apart from 1 and -1, Omega has four inverse pairs {r,r^-1}. Choose one element from each pair, giving a transversal S of size four. There are 16 choices. Write

    G=X^2-1, U=X^4-1, J=X^3-X,
    H=product_(s in S)(X-s)=X^4+h3 X^3+h2 X^2+h1 X+c,
    Hr=product_(s in S)(X-s^-1)=c^-1 X^4 H(1/X),  c!=0.

For the four inverse pairs define

    W_r=G*(X-r)*(X-r^-1)=U-(r+r^-1)J.

The last two locators are H and Hr. Every locator is monic of degree four and divides X^10-1.

The four traces r+r^-1 are distinct: equality would make the two unordered pairs roots of the same quadratic. Therefore the first four locators are distinct points on the affine line U-aJ. Their common gcd is G, of degree two. Each of H and Hr intersects each first-four root set in exactly one node, and H,Hr are coprime. Hence all six are distinct, their overall gcd is one, and all pairwise gcd degrees are at most b=2. The root incidence type has exactly one four-point line: its common flat has weight two, the eight cross pairs to H,Hr have weight one, and no other absence flats occur.

The reciprocal identity is

    c Hr-H=(c-1)U+(h1-h3)J.

Thus all six span the space with basis w=(U,J,H)^T. Its dimension is exactly three, because every element of span(U,J) vanishes at 1 and -1, whereas H vanishes at neither. The first four account for the unique four-point line. No triple containing H,Hr and a first-four locator is dependent: their line intersects span(U,J) in cHr-H. If this were proportional to W_r, evaluate at the element of S in its inverse pair; Hr is nonzero there but H and W_r are zero, a contradiction.

## Explicit balanced certificate, valid for all 16 transversals

Put

    B=(-X, X^2+1, 0),
    C=(-X^2-c, -h3 X^2+(c+1-h2)X-h1, X^2-1).

Direct multiplication gives

    B cross C=(U,J,H)=w.

Both rows have degree at most two, with independent leading vectors (0,1,0) and (-1,-h3,1). Thus every transversal satisfies the balanced-syzygy condition. No exceptional transversal or determinant assumption is needed. In particular the 6-by-6 coefficient map at degree at most one is invertible by the independently audited balanced-certificate equivalence.

## The full locator map has no nontrivial common cover

The coordinate ratio U/J is t=X+1/X. The extension K(X)/K(t) has degree two and its nontrivial automorphism is sigma(X)=1/X. If q=H/J, then

    sigma(q)=-c Hr/J.

This differs from q because H and Hr have disjoint nonempty root sets. Therefore K(t,q)=K(X). The full locator map is birational, despite the inversion structure of the first-four pencil. In particular the full space cannot be obtained by composing a smaller map with any rational right factor of degree greater than one, including a nontrivial power map.

## The reconstructed pencils contribute exactly one projective MCA direction

Use the [balanced-locator reconstruction](astra_mca_locator_reconstruction-2026-09-05.md) with degree cap d=4, exact joint cores of size six, and target agreement eight. Its residual direction identity says that for a locator coefficient row ci, one has ci proportional to e0 B(x)+e1 C(x).

For a first-four row ci=(1,-a,0), at its two private roots outside {1,-1}, the third coordinate forces e1=0. These two slots therefore have the same direction infinity, common to all four pencils.

At x=epsilon in {1,-1}, the finite direction gamma=-e0/e1 satisfies

    gamma*(a*epsilon-2)
      =a*(1+c)+(h1+h3)-epsilon*(1+c-h2).

Its denominator is nonzero because a=r+r^-1 and r is not epsilon. The directions at 1 and -1 are distinct. Indeed their equality is equivalent, in characteristic not two, to

    (1+c)*a^2+(h1+h3)*a-2*(1+c-h2)=0.

For the member r of S in this inverse pair, that expression equals

    (H(r)+r^4 H(1/r))/r^2.

It is nonzero: H(r)=0 and Hr(r)!=0. Thus every first-four pencil has slot multiplicities (2,1,1), with infinity its only doubled direction.

For H, the direction at x in S is gamma=x+c/x. It is injective on S: two distinct roots x,y give equal values only if xy=c, which would force the other two roots of S to have product one, contrary to S containing one element per inverse pair. For Hr, at x in S^-1 the direction is gamma=c*x+1/x, giving exactly the same four distinct values under x=1/s. Hence neither last pencil has a doubled direction.

Consequently these six pencils supply exactly one projective bad direction at the target agreement, independent of the transversal. In the displayed chart it is infinity. Whenever a common chart avoids all residual poles, it becomes one finite bad scalar, with four local-pencil witnesses. There are at most 24 slot directions, so a pole-free chart exists over the large verification field below. None of this censuses other decoding polynomials of the received line.

## Exact controls

Run `python3 scripts/probes/astra_mca_inversion_locator_sharpness_check.py`. It checks all 16 transversals over

    p=2013265921, primitive tenth root=1403701133.

The prime is independently certified by exhaustive trial division through floor(sqrt(p))=44869. The general construction and conclusions are proved algebraically for every field containing ten distinct roots of unity.

For every transversal the check:

- verifies all six actual divisor identities, degree-four polynomials, gcd incidences and exact rank-three span;
- checks the explicit balanced cross product and a nonzero 6-by-6 determinant;
- solves the bounded Bezout system (rank eleven), verifies both adjugate identities, and reconstructs all six degree-at-most-four pairs;
- verifies all six exact joint cores on every domain node and chooses a common pole-free chart;
- computes all per-pencil residual fibers and their union;
- checks the original no-joint condition by augmented Vandermonde ranks on both the exact eight-node witness and its full agreement support.

Output: 96 reconstructed polynomial pairs; 128 exact/full-support no-joint rank checks; per-pencil bad counts (1,1,1,1,0,0) and union count one for all 16 transversals. The determinant for the transversal exponents {1,2,3,4} is 5 modulo p; all other determinant values are recorded.

The checker is standalone and uses only the Python standard library, with its polynomial and modular linear-algebra routines included. It imports no repository, other-agent, or scratch-path code. It explicitly asserts all per-pencil slot multiplicities, the bad-count vector, the singleton union, and the displayed finite direction formulas for all 16 transversals. The result is a sharpness control for a universal incidence claim, not an unrestricted production six-locator realization, an unsafe radius, or a prize closure.


## Independent review

The independent `new_lower_bound_route` agent reviewed the general-field construction, all-16 balance claim, reciprocal identity, birationality sign, and direction collision/injectivity arguments, and reran the standalone checker successfully. Its review identified an incorrect optional root-multiplicity justification in the draft; that sentence has been deleted. The correct direct-evaluation proof above is retained. This is independent agent review, not external human peer review or Lean formalization.

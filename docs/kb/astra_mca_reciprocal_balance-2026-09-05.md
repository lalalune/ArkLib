# Odd balanced degree forces the reciprocal symmetry type

This is a written algebraic obstruction to a reciprocal-symmetry extension of the [length-10 inversion family](astra_mca_inversion_locator_sharpness-2026-09-05.md). It excludes that architecture at every dyadic length n=6b-2, including production, without enumerating domain divisors. It does not exclude every reciprocal-invariant three-dimensional space, arbitrary rational composition, or unrestricted six-locator configurations. It is not Lean-formalized.

## General coefficient-map theorem

Let K be a field of characteristic different from two, let b be a positive odd integer, and let L be a three-dimensional subspace of K[X]_(<=2b). Write

    R_m f(X)=X^m*f(1/X).

Assume R_(2b)(L)=L and that the multiplication map

    T: K[X]_(<=b-1) tensor L -> K[X]_(<=3b-1), a tensor w -> a*w

is an isomorphism. For primitive locator spaces of maximum degree 2b, this is exactly the independently audited balanced-syzygy certificate. Then

    dim L^+=2,     dim L^-=1,
    L^+={w:R_(2b)w=w}, L^-={w:R_(2b)w=-w}.

In particular, L cannot contain two linearly independent antireciprocal polynomials.

### Elementary proof

Each R_m is a linear involution. Since char K is not two, its plus and minus eigenspaces form a direct sum. For even m, coefficient reversal has eigenspace dimensions m/2+1 and m/2: pair the coefficients indexed j and m-j, with the unique central coefficient contributing one extra plus eigenvector.

Put b=2t+1 and a=dim L^+. Then K[X]_(<=b-1) has dimensions (t+1,t) and L has dimensions (a,3-a). Their tensor product has plus dimension

    (t+1)*a+t*(3-a)=3t+a,

and minus dimension 3t+3-a. The target, whose degree bound is 3b-1=6t+2, has dimensions (3t+2,3t+1).

The identity

    R_(3b-1)(f*w)=R_(b-1)(f)*R_(2b)(w)

makes T equivariant. An equivariant isomorphism identifies the respective eigenspaces, so 3t+a=3t+2 and a=2. More generally, without invertibility,

    nullity T >= |a-2|.

This proof uses exact eigenspace dimensions, not field-valued trace comparisons, and remains valid in small odd characteristic.

## All-dyadic consequence for the inversion architecture

Whenever n=2^m=6b-2 with integer b, m is even, say m=2j, and

    b=(4^j+2)/6

is odd for every j>=1. In particular b=3 at n=16, b=11 at n=64, and b=178956971 at production n=2^30.

Suppose six monic degree-2b domain-divisor locators have primitive three-dimensional span L, balanced degree-b syzygies, and their collection is closed under root inversion. Normalized reciprocity sends each locator to another locator in the collection, so L is R_(2b)-stable. The theorem forces the symmetry type (two reciprocal, one antireciprocal dimensions).

Thus there is at most one configured antireciprocal locator: the minus eigenspace is a line and monic locators on it coincide. In particular the length-10 architecture cannot extend to such a dyadic domain. That architecture has four distinct antireciprocal locators spanning a line, plus a locator and its normalized reciprocal, and hence its whole span is stable with dimensions (1,2), precisely the forbidden type.

The conclusion applies already if a three-dimensional span contains two independent antireciprocal locators and is closed under reciprocity; closure of the six individual locators as a set is merely a convenient sufficient hypothesis. Actual cyclotomic divisibility, the pairwise gcd bounds, and scalar saturation are not needed for this obstruction.

## Twisted inversion has the same obstruction

For any c in K^*, on polynomials of even degree bound 2r define

    R_(2r,c) f=c^(-r)*X^(2r)*f(c/X).

This is an involution. Each noncentral coefficient pair contributes one plus and one minus eigenvector, while the central monomial X^r is fixed, so the same eigenspace dimensions hold even if c is not a square in K. Since b-1, 2b and 3b-1 are all even and their exponents add correctly, multiplication is again equivariant. A balanced L invariant under normalized x -> c/x therefore also has dimensions (2,1). This closes a simple change of inversion center as an escape from the same architecture; it does not handle an arbitrary rational right factor.

## Scope of the surviving reciprocal type

The theorem does not rule out the symmetry type (2,1). It is algebraically compatible with balance: L=span(1,X^b,X^(2b)) has exactly this type and a bijective coefficient map, for every b. This example is only a polynomial-space control; it does not supply six required divisors of the dyadic domain.

Nor does the theorem imply reciprocal closure for an arbitrary six-locator span. Root inversion preserves the full pool of domain divisors but need not preserve a selected six-element collection or its span. No such closure is assumed without evidence.

## A stronger four-point threshold inside the reciprocal subspace

Suppose four distinct monic reciprocal degree-2b divisors of X^n-1 lie
in a two-dimensional pencil, with n=6b-2 and b odd. A squarefree reciprocal
polynomial of even degree cannot vanish at 1 or -1: differentiation of
W(X)=X^(2b)W(1/X) at either root would give W'=-W', contradicting a
simple root in odd characteristic.

All roots therefore occur in distinct inverse pairs. Each locator uniquely
has the form X^b F_i(X+X^-1), where F_i is monic of degree b and divides
the polynomial of the 3b-2 inverse-pair traces of the domain. This linear
substitution is injective, so the four F_i lie in a pencil. If their common
pairwise gcd has degree g, their lcm has degree 4b-3g, and hence

    4b-3g<=3b-2, or g>=ceil((b+2)/3).

The corresponding W gcd has degree 2g. The structural bound 2g<=b gives
g<=(b-1)/2 and therefore b>=7. The saturation-strengthened bound 2g<=b-2
gives g<=(b-3)/2 and therefore b>=13. These are necessary thresholds,
not constructions at their endpoints. They exclude a reciprocal four-point
pencil structurally at n=16,b=3, and under the saturated condition at
n=64,b=11. Production b is much larger, so this threshold alone does not
exclude that case. It strengthens the general saturated b>=8 threshold
only for the stated reciprocal class.

The trace descent, doubled gcd degree, and the two inequalities were also
independently checked by an agent. No small-field count is being extrapolated.

## Exact symmetry controls

Run `python3 scripts/probes/astra_mca_reciprocal_balance_check.py`. The standalone standard-library checker verifies every basis column of the ordinary and twisted reciprocal multiplication identities in 48 matrix cases at b=3 and b=11 over F3,F5,F7 and the certified production field. It checks the forced nullity bound for forbidden types (1,2) and (3,0), and invertibility for an explicit allowed-type (2,1) control. It also verifies a balanced type-(1,2) example at even b=2, demonstrating that oddness is essential, and all fifteen dyadic degree identities through n=2^30. These tests accompany the general eigenspace proof; they do not enumerate a production domain or establish existence of six admissible locators.

## Independent review

The sibling `new_lower_bound_route` agent independently audited the general reciprocal theorem, exact eigenspace and nullity counts, all-dyadic parity application, the length-10 forbidden symmetry type, and the normalized twisted-inversion extension. It found no algebraic or scope defect. This is independent agent review, not external human peer review or Lean formalization.

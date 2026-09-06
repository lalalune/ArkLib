# An order-eight symmetry cannot preserve a balanced locator space

There is no balanced, primitive three-dimensional locator space spanning
degree-2b divisors of X^n-1, where n=6b-2 and 8 divides n, that is invariant
under X -> zeta X for a primitive eighth root zeta. This applies at the
production parameters. It does not require the individual power-factor
assumptions of the [common-composition exclusion](astra_mca_near_power_locator_exclusion-2026-09-05.md).
It does require symmetry of the entire space; no such symmetry has been
proved for arbitrary received pairs or locators. This is a written proof,
not a Lean proof or the universal MCA bound.

## Hypotheses and the exact representation forced by balance

Work over a field K in which X^n-1 splits with distinct roots. Assume

    n=6b-2, 8 divides n, Omega=mu_n,
    L subset K[X]_(<=2b), dim L=3, gcd(L)=1,
    L is invariant under f(X) -> f(zeta X), order(zeta)=8.

Balance means that multiplication is an isomorphism

    K[X]_(<=b-1) tensor L -> K[X]_(<=3b-1).

This is precisely the invertible coefficient map in the
[reconstruction theorem](astra_mca_locator_reconstruction-2026-09-05.md),
equivalently the existence of degree-at-most-b syzygy rows B,C with
B cross C equal to a basis of L. The domain-divisor condition is imposed
on the locators in L below, not on an arbitrary basis vector.

Here b is odd. The action is diagonalizable because char K does not divide
eight. Label its eigenvalues by powers of zeta, and record the integer
multiplicities as polynomials modulo t^8-1. Put S_b=1+t+...+t^(b-1).
Equivariance of the multiplication isomorphism gives

    chi_L * S_b = S_(3b) = S_b*(1+t^b+t^(2b)) mod (t^8-1).

These are equalities of integer eigenspace dimensions, not merely equality
of traces in K. Since gcd(b,8)=1, S_b and t^8-1 are coprime over Q: an
eighth root other than one cannot also be a nontrivial bth root, and
S_b(1)=b is nonzero over Q. Cancellation therefore gives

    chi_L = 1+t^b+t^(2b) mod (t^8-1).

This cancellation over Q remains legitimate if char K divides b, since
the multiplicities being compared are integers. The three residues are
distinct. Choose an eigenbasis A_0,A_1,A_2 with

    A_j(zeta X)=zeta^(jb) A_j(X), j=0,1,2.

## Balance bounds the gcd of any two independent coordinates

In any polynomial basis A_0,A_1,A_2 of a primitive balanced L, the gcd G
of two basis entries has degree at most b. For example take G=gcd(A_0,A_1).
Primitivity gives gcd(G,A_2)=1. The two syzygy identities then imply

    G divides B_2 and G divides C_2.

At least one of B_2,C_2 is nonzero: otherwise the first two entries of
B cross C would vanish identically, contrary to a basis of L. Their
degree bound gives deg G<=b. A constant change of basis preserves the
balanced certificate, so this applies to every two independent linear
forms in L. It does not assume they are themselves domain divisors.

## Count roots on actual eight-element domain orbits

Consider a monic degree-2b divisor W of X^n-1 lying in L, and write

    W=c_0 A_0+c_1 A_1+c_2 A_2.

Every orbit of x in Omega under multiplication by zeta has eight elements.
On that orbit put y=zeta^(bj). Since b is odd, y runs through mu_8, and

    W(zeta^j x)=c_0 A_0(x)+c_1 A_1(x)*y+c_2 A_2(x)*y^2.

If all three c_i are nonzero, this quadratic is not identically zero on
any orbit: otherwise all three A_i(x) would be zero, contradicting
primitivity. Thus W has at most two roots per orbit, or at most
n/4=(3b-1)/2<2b roots altogether. This contradicts W being a squarefree
degree-2b domain divisor.

If exactly two adjacent coefficients are nonzero, with indices {0,1} or
{1,2}, let z be the number of common domain roots of the corresponding
A_i,A_j. These common roots form whole eight-element orbits and z<=b by
the gcd bound. Outside those orbits the expression, after dividing by a
nonzero power of y, is a nonzero linear polynomial in y. Therefore

    number of roots of W <= z+(n-z)/8
                          <= b+(n-b)/8
                           = (13b-2)/8 < 2b.

This is again impossible. If just one coefficient is nonzero, W is an
eigenvector. Its domain roots form complete eight-element orbits, forcing
8 to divide 2b, which is impossible for odd b.

The only remaining possible coefficient support is {0,2}. Consequently
every degree-2b domain divisor in L lies in span(A_0,A_2), a space of
dimension two. Such divisors cannot span L. In particular a six-locator
certificate with span three is impossible under this symmetry.

At production n=1073741824 and b=178956971, the all-three bound is
268435456<357913942. The adjacent-two bound is the rational number
2326440621/8<357913942. No enumeration of production polynomials or roots
is used in either strict inequality.

## Boundary and reproducible controls

The assumption 8 divides n is essential. At n=4,b=1 over F17, the space
span(1,X,X^2) is primitive, balanced and invariant under a primitive
eighth-root scaling. Its six quadratic divisors of X^4-1 span that space.
The four-node domain has no eight-element orbits, so it is outside the
theorem. The proof must not be applied just because K contains mu_8.

Run `python3 scripts/probes/astra_mca_cyclic_locator_symmetry_check.py`.
It checks the exact integer character convolution and its nonsingular
circulant matrix, including production; constructs primitive balanced
invariant polynomial spaces at lengths 16 and 64; checks their coefficient
maps and all normalized degree-2b combinations over F257; and verifies the
length-four boundary example. These finite controls test the proof's
ingredients and scope. They do not replace the general argument or imply
a production count from small-field evidence.

An independent agent reviewed the integer-character cancellation, the
pair-gcd argument, and each orbit-count case, and identified the necessary
8-divides-n boundary made explicit above. This is agent review of a written
proof, not external human peer review or Lean verification. Arbitrary
locator spaces need not have this symmetry.

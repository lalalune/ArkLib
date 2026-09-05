# Large quotient contact spaces persist for an actual far word

The zero-word obstruction in the [colon audit](astra_colon_2026-09-04.md)
can be strengthened to a far received word, along a line whose defining
words are independent modulo the Reed--Solomon code. At the same production
quotient box, an explicit contact subspace has dimension 10121888390 at
retained order 166, or 30981249640 at order 132.
Both exceed the available source nullity lower bound 228451639. Therefore
far-word, contact, and support information alone cannot give a universally
small enough quotient-kernel upper bound for that comparison.

The construction has no selected high-agreement family and supplies no
universal source divisor. Those remain essential additional hypotheses. This
is an obstruction to a proposed proof route, not a counterexample to the
companion target or a factor-count improvement. The mathematical proofs below
are elementary, with exact finite transcription checks; they are not
Lean-formalized.

## Production construction, contact, and distance

Use the [T-source pin](astra_t_cutoff-2026-09-04.md) and quotient box from
the [channel Hermite note](astra_kernel_channel_hermite-2026-09-05.md):

    p=2130706433, n=262144, w=131071,
    (D,T,Ycap,S)=(23944271,4795,182,41).

Take K=F_(p^6), as in the companion field; the construction also works over
any extension of F_p. Here n divides p-1, with quotient 8128. Let Omega be
the n roots of unity in F_p, viewed inside K. Choose received words
u0(x)=1/x and u1(x)=1/x^2 on Omega, and put

    Phi(X,Y,Z)=X^2*Y-X-Z.

For every z in K, the word u0+z*u1 has distance at least n-w-2=131071
even from polynomials over K of degree at most w. This is the degree
convention for selected polynomials in the
[family-incidence note](astra_family_incidence_secants-2026-09-04.md).
An agreement with f is a root of X^2*f-X-z, a nonzero polynomial of degree
at most w+2: its X coefficient is -1. Thus every
line member is farther than the target error cell 80791, and has at most
131073 agreements, fewer than the required 181353.

Moreover u0 and u1 are independent over K modulo the Reed--Solomon code. If
alpha*u0+beta*u1 agrees everywhere with some f of degree at most w, then
X^2*f-alpha*X-beta has n roots and degree at most w+2<n. It must vanish
identically, and its constant and X coefficients force beta=alpha=0.

At a node xi, write X=xi+t and Y=1/xi+Z/xi^2+Rt+v. Then

    Phi=(1+2*Z/xi+xi^2*R)*t
        +(1/xi+Z/xi^2+2*xi*R)*t^2+R*t^3+(xi+t)^2*v.

For the local weights (t,v,R,Z)=(1,2,0,0), this has exact contact order
one. Its first-order term has nonzero R coefficient xi^2. Hence
Phi^m has exact contact order m in every characteristic; its lowest-weight
part is the nonzero m-th power of that first-order term.

The coefficient box is

    Xexp+w*Yexp+(w-1)*Rexp < D,
    Yexp+Rexp+Zexp <= T, Yexp+Rexp <= Ycap, Rexp <= S.

Phi has weighted degree w+2, joint Y+R+Z degree one, Y+R degree one,
and R degree zero. Therefore all polynomials

    Phi^m * X^x * Z^z,
    0 <= x < D-m*(w+2), 0 <= z <= T-m,                    (1)

fit the box and retain order m at every node, provided m<=Ycap and the
displayed widths are positive. Multiplication by the nonzero polynomial
Phi^m is injective in K[X,Y,R,Z], so (1) is independent over K. These
are formal polynomial identities; no generic-Z specialization or extension
field enumeration is needed. All constructed coefficients already lie in F_p.

| Retained order m | X width | Z width | Subspace dimension | Dimension minus source lower bound |
|---:|---:|---:|---:|---:|
| 166 | 2186153 | 4630 | 10121888390 | 9893436751 |
| 132 | 6642635 | 4664 | 30981249640 | 30752798001 |

Taking u1=0 and Phi=XY-1 gives exact distance n-w-1=131072 from the
degree-at-most-w code and slightly larger subspaces, but loses independence
modulo the code.
The primary construction above avoids that degeneracy. It still has no
high-agreement line member at all, so it does not satisfy the selected-family
hypotheses of the factor argument.

## Exact kernel and Hermite ranks in a smaller block

There is also a complete bounded calculation for a rational received word.
Let x_1,...,x_n be arbitrary distinct field elements, V=product_i(X-x_i),
L=X-a with V(a) nonzero, and 1<=w<=n-3. Impose contact order two with
u0_i=1/L(x_i), u1_i=0, in the box

    (D,T,Ycap,S)=(n+w+1,1,1,1).

This separate small-block control has exact distance n-w from polynomials
of degree <w: L*f-1 has at most w roots, and interpolation at w nodes
attains that number. Its stated degree-<w convention is separate from the
degree-at-most-w production convention above.

The full contact kernel is exactly one-dimensional, spanned by

    P_*=(V-L*V')*Y+L*V*R+V'.                              (2)

For existence, put F=L*Y-1. Then P_*=V*(Y+L*R)-V'*F; its two
order-one terms cancel at each node. Its support fits the displayed box.

For uniqueness write P=A*Y+B*R+C+Z*C_1. The caps give deg A<=n,
deg B<=n+1, and deg C,deg C_1<=n+w. The Z coefficient must be divisible
by V^2, hence C_1=0. The remaining contact equations are

    B=0 mod V, A+B'=0 mod V,
    C=-A/L mod V, C'=-A'/L mod V.                        (3)

Write B=V*b, deg b<=1. Then A=-V'*b mod V. Write L*C+A=V*Q;
the C cap gives deg Q<=w+1. Differentiation and (3) give C=V'*Q mod V,
and therefore b=L*Q mod V. The distinct-node condition makes V' invertible
modulo V. Since deg(L*Q)<=w+2<n, b=L*Q exactly. Hence Q=kappa constant
and b=kappa*L. Now C=kappa*V'+V*E and

    A=kappa*(V-L*V')-L*V*E.

The A cap forces E=0, proving (2). This argument is characteristic free
for distinct nodes. For V=X^n-1, distinctness requires char(K) not dividing n.

Let U, of degree <n, interpolate 1/L. The unique C remainder modulo V^2
with the prescribed values and derivatives is

    H_u(A)=rem_(V^2)(-A*U+V*rem_V(A*U'*(V')^(-1))).      (4)

The inverse is taken modulo V. Its coefficients in X degrees D,...,2n-1
form a linear tail map. Their vanishing is exactly the C degree constraint.
On all A of degree <=n this map has maximal rank n-w-1, with kernel
dimension w+2. To see this, choose any Q of degree <=w+1 and divide

    (V-L*V')*Q=L*V*E+A, deg A<=n,
    C=V'*Q+V*E.

Then deg E<=w, deg C<=n+w, and (3)'s last two equations hold. This
parameterization is injective: if A=0, then V|C; from L*C=V*Q and the
derivative condition one gets V|Q, hence Q=0 because deg Q<n. Conversely
every admissible pair (A,C) gives this division and this Q.

Before the R^0 constraints, the first two equations of (3) restrict A to
the three-dimensional space

    A=-rem_V(V'*b)+lambda*V, deg b<=1.

The exact kernel result shows the tail map has rank two on this space,
leaving the one-dimensional kernel spanned by V-L*V'. Thus the rational
word does not give anomalously low rank on unrestricted A: that tail map
is already surjective. A nonzero kernel nevertheless survives all equations.

On V=X^n-1, (4) simplifies to

    H_u(A)=rem_(V^2)(-A/L-(V/n)*rem_V(X*A/L^2)),          (5)

where 1/L is taken modulo V^2 in the first term and modulo V in the
second. Its value is -A/L at nodes, and its derivative is -A'/L because
the second term cancels the extra derivative A/L^2 of -A/L.

## Reproduction and scope

Run

    python3 scripts/probes/astra_far_word_kernel_check.py

The [checker](../../scripts/probes/astra_far_word_kernel_check.py) verifies
the fixed production field and arithmetic, and every monomial in both
displayed powers of Phi against the box at the extreme shifts. Three fixed
examples over F17 independently verify the full order-two contact-matrix
nullity, Hermite value/derivative identities, both tail ranks, the spanning
polynomial, and an interpolant attaining exactly w agreements for the
separate 1/x control. It also checks independence of 1/x and 1/x^2 modulo
the small Reed--Solomon spaces, and directly expands small powers of both
locator polynomials to check their exact contact orders. No production
matrix, parameter grid, or full kernel basis is computed.

The production obstruction follows from the polynomial proof, not an
extrapolation from the small-field matrices. It strengthens the previous
zero-word limitation to an actual far word. A successful quotient bound must
still exploit universal-divisor/source provenance or the selected-family
conditions; those are absent from this construction. No claim about the
current global moving budget, ProtocolClaim, or prize closure follows.

The [contact-variation follow-up](astra_contact_variation-2026-09-05.md)
adapts the exact order-two block to a rank-two line with an actual bad MCA
seed. Its full kernel is one-dimensional and the extracted regular factor's
first two tails meet simply. This supplies a different limitation, at R
degree one; it does not realize the binding C2 flag or a large selected family.

# Actual-domain Cartier constraints and the quartic-defect cutoff

This is a necessary-condition calculation, not a production exclusion.
It complements the [private cubic normal form](astra_mca_private_cubic_surface-2026-09-05.md)
and the [bounded one-node-defect exclusion](astra_mca_defect_one-2026-09-05.md).
The proofs below are elementary and are not Lean-formalized.

Let P be the certified production prime, n=2^30, L=(P-1)/n,
m=(n-4)/3=357913940, and k=(P-2)/3. Thus P=nL+1,
P=2 mod 3, n=3m+4, and k<P. For A+B=C with pairwise coprime
nonzero degree-m polynomials put H=ABC and W=A'B-AB'.
Then deg W<=2m-2 because the leading terms cancel.

## Elementary primitive for the necessary Cartier condition

Define over F_P

    G(T) = sum_{j=0}^k binom(k,j)*T^(k+j+1)/(k+j+1).

Every denominator lies strictly between 0 and P. Therefore
G'(T)=T^k*(1+T)^k. The rational expression

    S = B^P * G(A/B)

is a polynomial: every term has nonnegative B exponent, in fact at
least k+1. Since (B^P)'=0 in characteristic P,

    S' = W*H^k.

Consequently the coefficient of X^(P*ell+P-1) in W*H^k vanishes for
every ell>=0. This is the Cartier-zero condition, proved directly
without importing the supersingularity/pullback theorem. It agrees with
the differential formulation for the map Y^3=H -> z^3=t*(1+t).

For deg H=3m, deg(W H^k)<=mP-2. Hence the possibly nonzero Cartier
output coefficients have ell=0,...,m-2. This is a linear map on W
with at most m-1 rows and 2m-1 columns, so its kernel has dimension
at least m. Dependence of H on the unknown A,B remains nonlinear.

## Exact diagonal formula for the undeleted binomial

For comparison only, replace H by V=X^n-1 while retaining deg W<=2m-2.
Write W=sum_j w_j X^j. A contribution to the ell-th Cartier coefficient
satisfies

    j+n*a=P*(ell+1)-1.

The output degree is at most m<n, and deg W<n. Reducing modulo n
therefore gives j=ell, and then a=L*(j+1). Exactly j=0,...,m satisfy
0<=a<=k. Thus

    Cartier(W V^k dX)
      = sum_{j=0}^m (-1)^(k-L*(j+1))
        * binom(k,L*(j+1))*w_j*X^j dX.

All these diagonal scalars are nonzero because their binomial arguments
lie between 0 and k<P. Its kernel forces ord_0 W>=m+1=(n-1)/3.
It does NOT force ord_0 W near n/2.

If A(0)B(0)!=0 and deg A,deg B<=m<P, ord_0 W>=m would already force
A/B constant: the numerator A-(A(0)/B(0))*B has degree<=m, whereas
its first possible nonzero term would have order at least m+1.

For the actual quartic defect, however, the kernel dimension >=m is
larger than the dimension m-1 of polynomials of degree<=2m-2 with
ord_0 W>=m. Therefore the actual Cartier condition ALONE cannot imply
that origin cutoff for all W. This does not exclude an additional
constraint on W arising from the same A,B that define H.

## An actual-prime quartic-defect control attains order m-1

Work in the production prime field, at the bounded length n0=16,m0=4.
Choose i of order four and put

    D=X^4-1,
    A=X^4-i,
    B=(i-1)*(X^4+1),
    C=i*(X^4+i).

Then, exactly,

    A+B=C,
    ABC=-(1+i)*(X^16-1)/(X^4-1),
    W=A'B-AB'=-8*X^3.

All private factors and D are squarefree and split on the actual
field's sixteenth roots. Thus ord_0 W=3=m0-1. H is a polynomial in
X^4, so W H^k has exponents congruent to 3 modulo 4. Since P=1 mod4,
its ell-th Cartier coefficient could be nonzero only if ell=3 mod4.
But the output range is ell=0,1,2; the condition therefore vanishes
identically, without evaluating any huge binomial coefficient.

This example concerns one triple and length16, not the full production
configuration. It shows that a uniform defect-four origin cutoff cannot
be imported from the undeleted binomial. It is itself an X^4 lift, so
it does not refute a possible classification forcing that lift.

## Direct sparse derivative identity

If the scalars are normalized so D*ABC=X^n-1, write
EA=X*A'-m*A, EB=X*B'-m*B, and ED=X*D'-4D. Then

    D*[B*(2A+B)*EA+A*(A+2B)*EB]+ED*ABC=n.

Here deg EA,deg EB<=m-1 and deg ED<=3. This is exactly
X*(DABC)'-n*DABC=n after expanding the Euler derivative of ABC.
It exposes the binomial sparsity but supplies no contradiction by its
present degree bounds.

No bounded-loss or transformed-jet formula for arbitrary quartic D has
been proved. The surviving task is to use the special split binomial
product together with the nonlinear A,B/W compatibility, or additional
two-triple conditions, beyond the linear Cartier kernel.


## Reproduction

Run `python3 scripts/probes/astra_mca_cartier_check.py`. It expands the
polynomial-primitive identity over F5, F11, and F17; checks the length-16
control in the certified production field; and verifies the production
index bounds without expanding a polynomial of degree comparable to P.
The general identity and its scope are supplied by the written argument,
not by the finite controls. No production exclusion follows.

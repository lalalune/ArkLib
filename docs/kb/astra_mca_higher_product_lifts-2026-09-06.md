# Higher product lifts collapse to the cubic condition

This is an elementary written theorem and an exact finite/sparse arithmetic
probe. It concerns a two-column witness image over the actual evaluation
domain. It does not construct actual MCA witnesses or prove the universal
production scalar bound. It strengthens the no-go result in
the [Cauchy normal-form theorem](astra_mca_cauchy_normal_form-2026-09-05.md): adding separately
factorized products of every degree still does not recover the original RS
code. Cross-order multiplication is substantive.

## 1. Precise admissibility condition

Let K be any field, let Omega consist of n=2k distinct K-rational nodes, and
let V(T)=product_{x in Omega}(T-x). Let E have rows e_x=(u_x,v_x) and column
rank two. Assume its quadratic Lagrange numerator is an exact rank-one
polynomial matrix of degree at most 2k-2. The previously proved UFD normal
form gives

    N_2 = D*(F^2,F*G,G^2),  gcd(F,G)=1,
    e_x=t_x*(F(x),G(x)),  t_x^2=D(x),
    m=max(deg F,deg G)>=1,
    ell=k-1-m>=0,  deg D<=2*ell.                    (1)

The stronger quadratic cap 2k-2, rather than merely <n, is automatic for
actual RS_k columns. The scalar t_x is well-defined even at a zero row:
coprimality prevents simultaneous vanishing of F,G, and t_x=0 there.

For q>=2, a *coherent admissible q-product lift* means polynomials C_{q,j},
0<=j<=q, satisfying all of the following:

    deg C_{q,j}<=q(k-1),
    C_{q,j}(x)=u_x^(q-j)*v_x^j for every x,
    G*C_{q,j}=F*C_{q,j+1} as exact polynomial identities. (2)

Thus the lift retains the primitive row direction already determined by
N_2. It is more restrictive than asking only for within-order tensor minors
to vanish. For actual RS columns all these conditions hold. For q>=3 one
must allow lifts above degree n: the canonical degree-<n row interpolants
need not satisfy the exact identities even for true RS columns.

Condition (2) is equivalent to

    C_{q,j}=L_q*F^(q-j)*G^j,
    L_q in K[T], deg L_q<=q*ell,
    L_q(x)=t_x^q at every x.                         (3)

Indeed the rational recurrences give the displayed formula with a rational
scalar. At any irreducible polynomial, at least one of F,G is a unit, so
the corresponding endpoint C_{q,0} or C_{q,q} rules out a pole. The maximum
degree of the two endpoints is deg L_q+qm. Evaluation in a nonzero
component of (F(x),G(x)) proves the last equality, including zero rows.

Consequently cubic admissibility is exactly

    deg(interp_Omega(t_x^3))<=3*ell.                  (4)

Here interpolation means the canonical remainder of degree <n; it has the
minimum degree among all polynomials with those values. This is an exact
scalar interpolation criterion, not an assumption that the canonical
cubic tensor numerator itself has rank one.

## 2. No additional information from separately lifted higher orders

The following are equivalent:

* a coherent admissible cubic lift exists;
* coherent admissible q-product lifts exist for every q>=2;
* such a family exists that also satisfies every even-order multiplication
  law L_{2a}L_q=L_{2a+q}, for a>=1 and q>=2.

Proof: the reverse implications include q=3. In the forward direction,
write J=L_3. Set, for s>=1 or s>=0 as appropriate,

    L_{2s}=D^s,
    L_{2s+3}=J*D^s.                                 (5)

Their evaluations are t_x^q. Since deg D<=2ell and deg J<=3ell, their
degrees are <=q ell, which proves (3). Formula (5) proves all the claimed
even-order multiplication laws and, in particular,

    L_{q+2}=D*L_q  for every q>=2.

Every odd-times-odd defect in this family is a multiple of one polynomial:

    L_{2a+3}L_{2b+3}-L_{2a+2b+6}
       =D^(a+b)*(J^2-D^3).                          (6)

Thus adding arbitrarily many independently admissible products, with
common primitive direction and even these exact cross-order recurrences,
adds nothing beyond the cubic condition. This statement includes arbitrary
zero rows and arbitrary characteristic.

There is also a broad automatic range: if 3ell>=n-1, interpolate t_x^3 by
a polynomial J of degree <n, and (5) supplies the entire family. In this
range the extra conditions impose no restriction on a quadratic-admissible
image whatsoever.

## 3. The first missing odd-times-odd relation repairs the original code

For any admissible cubic J, the node evaluations imply

    V divides J^2-D^3.                              (7)

The exact identity J^2=D^3 holds if and only if there is a polynomial H
such that D=H^2 and J=H^3. To prove the nontrivial direction, put H=J/D in
K(T). Its square is D, so the valuation at every irreducible polynomial
is nonnegative; therefore H is a polynomial. Directly H^2=D and H^3=J.
No algebraic closure or extraction of a scalar square root is required.

In that case t_x^2=H(x)^2 and t_x^3=H(x)^3 imply t_x=H(x). At a zero
both vanish; otherwise take the quotient of cube by square. Also
deg H<=ell. Hence the actual original columns are evaluations of HF,HG,
both of degree <=k-1. This removes the independent row-sign ambiguity as
well as the nonsquare scalar factor and handles zero rows without deletion.

Conversely actual RS columns give such H and allow the choice J=H^3.
Therefore original RS membership is equivalent to the *existence* of an
admissible cubic J satisfying J^2=D^3. In its family (5), already the single
relation L_3^2=L_6 is exactly this repair. An arbitrary chosen lift of actual
RS columns can fail the relation: for E=(1,T), D=1, n=16,k=8, both J=1 and
J=1+V are admissible since deg(1+V)=16<=3(k-2)=18, but only the former
satisfies J^2=D^3. The per-order minor identities do not make the choice.

There is a useful sufficient degree range. If

    6ell<n,                                         (8)

then (7) and deg(J^2-D^3)<=6ell force exact equality, hence original RS
membership. If z is the number of zero rows, the slightly stronger test
6ell<n+z suffices: at each of those nodes D and J both vanish, so the
defect has multiplicity at least two. Since V is squarefree, V times the
zero-row locator divides the defect.

At production write n=6b-2, k=3b-1, b=178956971. The two unconditional
degree ranges are:

    1<=m<=b-1=178956970: every higher-product lift is automatic;
    m>=2b-1=357913941: one admissible cubic forces true RS membership.

The intermediate degrees b<=m<=2b-2 are not settled by these degree
arguments. This partition alone gives no scalar count for actual witnesses.

## 4. A sparse production false positive for the entire hierarchy

Take Omega=mu_n, n=2k a power of two with n>=16. Let c be nonzero and put

    t(T)=T^(k-2)*(1+c*T^4),  e_x=t(x)*(1,x),
    D(T)=T^(n-4)+2c+c^2*T^4,
    J(T)=T^(k-6)*(1+c*T^4)^3.                        (9)

Modulo V=T^n-1 these are t^2 and t^3, respectively. Thus (1) holds with
F=1,G=T,m=1 and the quadratic numerator D*(1,T,T^2), whose largest degree
is n-2. The cubic tensor J*(1,T,T^2,T^3) is an admissible lift because

    deg J+3=k+9<=3k-3.

Formula (5) supplies every higher lift. Its largest coordinate degree is
exactly q(k-1) for even q. For odd q>=3 it is q(k-1)-(n-12). All tensor
minor/common-direction identities and all even-order multiplication laws
hold as exact polynomial identities, not only modulo V.

Nevertheless the remaining cross-order defect is explicitly nonzero.
Writing z=T^4 and M=n/4 gives

    J^2-D^3 = (z^M-1) * Q(z),
    Q(z)=c^3*(2+c*z)^3
         -z^(M-3)*(1+6*c*z+3*c^2*z^2)
         -z^(2*M-3).                                (10)

Since M>=4, the leading term of Q is -z^(2M-3), distinct from every
other term. Thus the defect is nonzero in every characteristic, including
when some displayed integer coefficients vanish. Its degree is 3n-12.

At the actual production prime

    p=365375409332725729550921208179070755120141565953,
    n=1073741824, k=536870912, c=2,

the existing squarefreeness/nonvanishing criterion is checked again by
the standalone probe. The multiplier t is nowhere zero, D is nonconstant
and squarefree, and E has rank two. The two canonical interpolation
polynomials t,Tt have degrees k+2,k+3, outside RS_k. Therefore this is a
full-support actual-production-domain false positive for the infinite
per-order product hierarchy, including its exact even-order recurrence.
It is not a received-pair/MCA construction.

## Verification and residual

Run `python3 scripts/probes/astra_mca_higher_product_check.py` from the repository root. The script
uses standalone finite-field polynomial arithmetic and no external package.
Dense controls at n=16,64 over F257 and the production prime verify row
products, exact polynomial identities, degree caps, orders 2 through 11,
quadratic and cubic interpolation, nonzero defect, and nonmembership. It
also checks true-RS controls and a zero-row automatic-range control. Sparse
production controls verify (9)-(10), all-order degree arithmetic, full
support and squarefreeness without expanding billion-degree polynomials.

This gives a bounded rigorous obstruction to an entire higher-product
relaxation, plus an exact positive converse and degree ranges. To turn
products into a universal MCA count one must use actual cross-order
multiplication or other structure from the witness equations, and then
derive a count. Neither an eliminant of degree <=n nor the universal
production bound is proved here. Independent agent review checked the written
argument, including its existential choice of cubic lift. A separate sparse
arithmetic implementation checked twelve field/length/parameter controls,
including production, at orders two through thirteen. These are mathematical
and computational audits, not Lean formalization or external human peer review.

The root agent independently checked the algebra and ran a separate sparse
checker on twelve small/production parameter cases. A second agent audited
the all-order construction, the existential converse, support-zero handling,
degree ranges, and the exact defect factorization. The root caught and this
note corrects a quantifier ambiguity: arbitrary alternative cubic lifts of
an actual RS image need not satisfy the exact odd-times-odd relation.
The standalone checker now includes that guard. This is agent review of
written arguments and arithmetic controls, not Lean formalization.

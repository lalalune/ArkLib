# The first shifted Gram form recovers RS structure

This note contains written elementary proofs and exact finite controls. It is
not a Lean proof, a scalar-count bound, a production-length counterexample,
or a solution of the Proximity Prize.

The relevant predecessor remains: at n=2^30, k=n/2, t=715827884,
bound the distinct actual same-support MCA-bad scalars by n for every
received pair. Neither result below proves that assertion.

## 1. An RS-specific hierarchy, retaining the common quotient kernel

Let K contain n distinct nth roots of unity, assume char(K) does not divide
n, and write n=2k. Let C be the degree-<k RS evaluation code on Omega=mu_n.
For 0<=s<=k define

    B_s(v,w) = sum_{x in Omega} x^(s+1) v(x) w(x).

For f,g of degree <k, the elementary subgroup sum gives exactly

    B_s(f,g) = n * coeff_(n-s-1)(f*g).                 (1)

Indeed all exponents in X^(s+1)fg are positive and less than 2n; only the
exponent n has a nonzero subgroup sum. In the monomial basis of C the
matrix has entry n when i+j=n-s-1 and zero otherwise. It has a nonsingular
s-by-s reverse-diagonal block on the last s coefficients and is zero
elsewhere. Thus

    rank(B_s restricted to C) = s,  0<=s<=k.           (2)

In particular B_0 vanishes, but B_1 has rank ONE. The latter is additional
information beyond weighted self-duality.

For selected MCA witnesses, let r_i=u0+gamma_i*u1-f_i be the actual error
columns, let R be their coordinate-by-witness matrix, and let Q have columns
(1,gamma_i). For ANY matrix Z with QZ=0, put E=RZ. Its columns are codewords,
with polynomial vector h(X)=-sum_i f_i(X) Z_i. If a_j is the row vector of
degree-j coefficients of h, then

    E^T diag(x) E = 0,
    E^T diag(x^2) E = n*a_(k-1)^T*a_(k-1),
    E^T diag(x^(s+1)) E
      = n*sum_{u+v=s-1} a_(k-1-u)^T*a_(k-1-v)          (3)

for 1<=s<=k. Consequently these restricted matrices have rank at most s.
The SAME matrix Z must be used throughout; forgetting that common kernel
loses part of the assertion. No assumption about errors being disjoint,
or about witness uniqueness, is involved. These hold for actual witnesses
on arbitrary supports and preserve the original quotient directions.

There is also one exact rational identity containing all the moments.
For an arbitrary n-point domain Omega, let

    P_Omega(T)=product_x(T-x), lambda_x=1/P_Omega'(x).

Lagrange partial fractions, applied to the polynomial h_a*h_b of degree
at most n-2, give the matrix identity

    E^T diag(lambda_x/(T-x)) E = h(T)^T*h(T)/P_Omega(T). (4)

Thus the rational matrix on the left has rank at most one over K(T), and
ALL its 2-by-2 minors vanish identically before reduction modulo the domain
polynomial. To prove (4), multiply by P_Omega: the two sides agree at every
x in Omega and have degree at most n-1; the root bound gives equality.
For subgroup coordinates lambda_x=x/n. In the reciprocal variable z,
if A(z)=z^(k-1)h(1/z), the equivalent form is

    E^T diag(x^2/(1-x*z)) E
       = n*A(z)^T*A(z)/(1-z^n).                       (5)

These are exact polynomial/residue constraints missing from the single
rank-four Gram statement. They do not by themselves bound the number of
scalars. In particular, cancellation in the finite field prevents treating
the squared minors in a Cauchy-Binet expansion as nonnegative quantities.

For four witnesses with distinct scalars, take Z to be any basis of the
two-dimensional kernel of Q. With E=RZ and e_x its two-entry row, (4) gives
the following explicit FOUR-WITNESS residue equations, containing no
unknown decoding-polynomial coefficients:

    sum_{y != x} lambda_y * det(e_x,e_y)^2/(x-y) = 0
       for every x in Omega.                         (6)

Proof: Cauchy-Binet expands the zero determinant from (4) as

    sum_{x<y} lambda_x*lambda_y*det(e_x,e_y)^2
                         /((T-x)*(T-y)) = 0.

Its residue at T=x is lambda_x times the left side of (6).
Equivalently, if K_R(T)=R^T diag(lambda_x/(T-x))R, then the bordered
6-by-6 matrix

    [ K_R(T)  Q^T ]
    [ Q        0  ]

has determinant zero. More generally its rank is at most five for any
number of witnesses. To see the rank claim, choose a witness-coordinate
basis with Q=(I_2,0); elementary row and column elimination gives rank
4+rank(K_R restricted to ker Q), hence at most five by (4).
This common-kernel condition is stronger than the unbordered rank bound.
Equation (6) is a concrete necessary condition to test for a proposed
four-witness realization; a uniform scalar-count consequence is still open.

## 2. The first shifted rank already characterizes half-rate GRS

Let Omega={x_1,...,x_n} consist of distinct NONZERO elements of K, n=2k.
Let C be an [n,k] MDS code, self-dual for the nondegenerate diagonal form

    B(v,w)=sum_i beta_i*v_i*w_i,

with fixed diagonal coefficients beta_i != 0. Let T=diag(x_i). Assume

    rank((v,w) |-> B(Tv,w), restricted to C) = 1.     (7)

Then there is a nowhere-zero vector v such that

    C=span(v,Tv,...,T^(k-1)v)=diag(v)*RS_k(Omega).     (8)

Proof: the map C -> C^* sending c to B(Tc,-) has kernel
{c in C:Tc in C^perp}=C intersect T^(-1)C. Equation (7) therefore says
dim(C+TC)=k+1. Put H=C+TC and

    V_r={v in C:T^j v in C for 0<=j<=r}.

For r>=1, the map V_(r-1) -> H/C sending v to T^r v mod C is defined:
T^(r-1)v lies in C. Its kernel is V_r and its target has dimension one.
Thus dim V_r>=k-r. Choose 0!=v in V_(k-1).

MDS gives |support(v)|>=n-k+1=k+1. If a linear combination of
v,Tv,...,T^(k-1)v vanished, a polynomial of degree <k would vanish at all
these distinct support coordinates, forcing that combination to be zero.
The k vectors are therefore independent and span C. If any coordinate of
v were zero, every codeword of C would be zero there, contradicting MDS.
This proves (8).

In subgroup coordinates with beta_i=x_i, self-duality further gives

    sum_i x_i*v_i^2*x_i^d=0,  0<=d<=n-2.

The nullspace of these n-1 Vandermonde moment equations is one-dimensional,
spanned by the Lagrange weights x_i/n. Hence x_i*v_i^2 is proportional to
x_i/n, so all v_i^2 are equal and nonzero. In odd characteristic each
v_i/v_1 is +1 or -1. Thus C is the target subgroup RS code up to coordinate
signs (and a common irrelevant scalar). Coordinate signs preserve Hamming
agreement and the same-support MCA event when applied to all words.

This is a characterization theorem, not an extra hypothesis we know how
to turn into the production census. At witness level E=RZ need not span C;
an over-budget set can still have small polynomial span. Therefore one
cannot silently invoke the MDS characterization on image(E).

## 3. Self-duality alone still admits an over-budget MCA construction

There is a weighted-self-dual [128,64] MDS code over the ACTUAL production
prime P with quotient rank two and at least 147 distinct actual MCA-bad
scalars, each with exactly 88 agreements. It can be labeled by mu_128 and
made self-dual for the exact subgroup form sum_x x*v(x)*w(x).
The code is not asserted to be RS. Length 128 is not production length.

### Seven blocks in the existing generic MDS construction

The accompanying checker supplies seven explicit subsets F_i of {0,...,63},
each of size 21. Their minimum union sizes at h=1,...,7 are

    21,34,43,49,53,57,61.

Use the same construction as the [ordinary-MDS obstruction](astra_mca_mds_rank_obstruction-2026-09-05.md):
a 64-by-34 generic matrix G has two independent-variable columns supported
on each F_i and 20 further dense columns; L is generic 2-by-34.
For every 32-row set S, a sparse column subset meeting h blocks sees at
least max(0,|union F_i|-32)+2 >=2h rows of [G_S;L]. Any subset containing a
dense column sees all 34 rows. Hall's criterion gives a nonzero augmented
determinant for every S, hence C0=G(ker L) is [64,32] MDS at a common
nonzero specialization.

For i and x in F_i, the two sparse columns have a nonzero combination v_ix
canceling row x. Nonzero two-row minors ensure Gv_ix has exact support
F_i minus {x}, of size 20. The checker gives a rank-33 matching for its
44-row complement; rank at most 33 follows from v_ix. Require one such
minor and separate all projective images Lv_ix, with first coordinates
nonzero. This gives 7*21=147 distinct finite scalars, each an actual
same-support MCA vertex, by the existing quotient criterion

    dim D0(E)=1 iff the full agreement set has no joint pair.

Every required polynomial is nonzero over every prime field by the same
independent-variable matching/quotient-separation argument. The product's
degree is at most

    34*binom(64,32)+34+147*33+7*binom(21,2)*2
       +147*2+4*binom(147,2)
      =62309220792048129199 < P.

So a common specialization exists over P. This is an existence proof,
not a numerical 64-by-34 matrix certificate.

### Doubling to weighted self-duality, with MDS proved

Let C0^perp use the ordinary dot product. For nonzero parameters theta_i set

    T_theta(c,d)=(c+theta*d, c-theta*d),
    C=T_theta(C0 x C0^perp).

It has dimension 64 and is isotropic, hence self-dual, for the diagonal
weights (+1/theta_i,-1/theta_i), because the pairing becomes
2*(c dot d' + d dot c').

For each set of 64 output coordinates, let m original indices have both
outputs selected. There are also m omitted indices and 64-2m single-output
indices. Vanishing on the doubled indices forces both c,d to vanish there.
Each shortened constituent is an MDS space of dimension 32-m. On the
single-output indices the remaining equations have coefficient rows
c_i +/- theta_i*d_i. In their determinant the coefficient of any monomial
using a specified 32-m of those theta_i is, up to sign, the product of
two nonzero shortened-MDS minors. Different subsets give different
monomials. Thus every output minor is a nonzero polynomial.

Each original output determinant has total theta-degree 32 (one factor
from each d-column). Multiplying all binom(128,64) minors and all theta_i
has degree at most

    32*binom(128,64)+64
      =766436673341698651716338808844177656064 < P.

Therefore some theta makes C MDS. The received words T_theta(u0,0),
T_theta(u1,0) and decodings T_theta(f,0) duplicate the original error
support. They have exactly 128-2*20=88 agreements. A joint explanation on
the duplicated support would, by inverting the two coordinates at each
agreement index, give a joint C0 explanation there, impossible. The 147
scalars and quotient rank two are preserved.

To obtain the exact subgroup weights, restrict theta_i=z_i^2. Substitution
is injective on the polynomial ring, so the determinant product remains
nonzero and its degree merely doubles to

    1532873346683397303432677617688355312128 < P.

Here -1 and every x in mu_128 are squares in F_P. Thus all weights
beta_i=(+/-1/theta_i) can be converted to prescribed weights x_i by
nonzero coordinate scalings s_i with x_i*s_i^2=beta_i. Scaling code,
received pair, and decodings preserves every agreement support and MCA
condition. This still does not impose the first shifted rank-one condition.

## 4. Exact finite controls and the remaining obstacle

Run `python3 scripts/probes/astra_mca_shifted_gram_check.py`.
It checks all seven-block union bounds, all 147 rank-33 support matchings,
the exact field-size inequalities, and the RS basis Gram identity on
mu_8,mu_16,mu_64 over F257 and mu_16 over P.
It reconstructs the full Krylov basis from a scrambled basis with coordinate
signs at each of those sizes, verifies the equality of the recovered and
original spaces, and checks every squared-minor residue in (6) for two
independent codeword columns. It also checks (4) directly at three
non-domain values in each control. These finite checks do not replace the
general written proof of (4).

An explicit [8,4] MDS control over F257, labeled by mu_8, has weighted Gram
rank zero but FIRST SHIFTED Gram rank FOUR. All 70 MDS minors are checked.
This directly separates self-duality from the RS-specific identity;
it is not an over-budget MCA example. The checker prints its exact matrix.

The open counting question can now be stated with more retained structure:
selected sparse errors with distinct quotient directions must satisfy
(3), or equivalently the Cauchy rank-one identities (4), after restricting
to the common quotient kernel. A bound that uses only weighted self-duality
is refuted by section 3. A bound using all these RS identities is still
unproved; no plane extraction, carrier-degree budget, or bound on the
number of distinct extrapolated single-hole values follows here.

An independent agent audit verified the characterization in section 2, including its full-support argument and the k=1 case. Exhaustive length-four controls over F5, F7, and F13 recovered the stated form for every qualifying rank-one code. In the F13 control, exactly eight of 24 weighted-self-dual MDS codes had shifted rank one. The characterization remains a written theorem, not a Lean proof or a scalar-count bound.

A separate agent audit verified the Cauchy and residue identities in section 1
and the finite-specialization, MDS, self-duality, and same-support arguments
in section 3. These are independent agent reviews, not external human peer
review or Lean verification. No assertion is made that the length-128
existence construction violates every RS-specific identity; the explicit
length-eight control separates self-duality from the first shifted identity.

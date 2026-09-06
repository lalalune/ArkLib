# What the common-kernel Cauchy rank-one identity actually forces

This is a written elementary converse with exact finite and sparse
production-arithmetic controls. It is not Lean-formalized. It concerns a
two-column witness image, not a full half-rate MDS code, and does not prove
the universal MCA bound or construct actual over-budget MCA witnesses.
It audits relaxations of the [shifted-Gram and Cauchy identities](astra_mca_shifted_gram-2026-09-05.md).

## 1. Polynomial normal form

Let K be a field, Omega={x_1,...,x_n} distinct K-rational nodes, n=2k,
P(T)=product_x(T-x), and lambda_x=1/P'(x). Let E have n rows e_x=(u_x,v_x)
and column rank two. Define

    K_E(T)=sum_x lambda_x*e_x^T*e_x/(T-x),
    N(T)=P(T)*K_E(T)=[A(T),B(T);B(T),C(T)].

Each entry of N has degree <n and interpolates its row product, because
lambda_x*P(T)/(T-x) is the Lagrange basis polynomial. Assume det K_E=0,
equivalently A*C=B^2 as an exact polynomial identity.

Then there are nonzero D in K[T] and coprime F,G in K[T] such that

    N=D*[F^2,F*G;F*G,G^2],
    d+2m<n,  d=deg D, m=max(deg F,deg G).             (1)

The two-column rank assumption makes F/G nonconstant, so m>=1. In
particular m<=k-1. The primitive pair F,G is unique up to a common
nonzero scalar; D changes by its inverse square.

Proof: A is nonzero because some u_x is nonzero. Put a=gcd(A,B),
F=A/a and G=B/a, so gcd(F,G)=1. From A*C=B^2 one obtains F*C=a*G^2.
Hence F divides a; writing a=D*F gives the formula. The degree bound
follows from max(deg A,deg C)=d+2m<n. Uniqueness follows from the
primitive rational ratio B/A=G/F.

For every domain node there is a scalar t_x with

    e_x=t_x*(F(x),G(x)),  t_x^2=D(x).                 (2)

Here e_x=0 exactly when D(x)=0. To prove this, F(x),G(x) cannot both
vanish by coprimality. Divide the corresponding nonzero component to
define t_x and use the three row-product equations. If D(x)=0 both
components of e_x are zero. Thus (2) includes zero rows without deleting
them. For nonzero rows, D(x) must be a square in K.

Conversely, any D,F,G satisfying (1), together with choices t_x satisfying
(2), gives the Cauchy rank-one identity. The entries on the right of (1)
have degree <n and interpolate the row products, so they equal N.

Thus full-support E is always an invertible diagonal rescaling of a
degree-<k polynomial pair. Rank-one residues alone do not identify the
original RS code: they permit the extra scalar polynomial D and the
coordinate-wise square-root choices t_x.

## 2. Exact condition for an invertible coordinate rescaling, including zeros

Let z be the number of zero rows, equivalently domain roots of D, and let
Z(T)=product_{x:e_x=0}(T-x). Then

    E is an invertible coordinate rescaling of an RS_k pair
       if and only if z+m<k.                         (3)

Sufficiency: use the code polynomials ZF,ZG, of degree z+m<k. Off the
zero rows, set the diagonal multiplier to t_x/Z(x), which is nonzero.
At the zero rows choose any nonzero multiplier; both code polynomials
vanish there.

Necessity: suppose p,q of degree <k have the same row directions and
zero rows as E up to invertible coordinate multiplication. If z>=k they
are both zero, impossible. Otherwise p=Z*p0 and q=Z*q0 with
deg p0,deg q0<=k-1-z. The cross polynomial p0*G-q0*F vanishes at all
n-z active nodes. Its degree is at most k-1-z+m<n-z, so it is zero.
Coprimality forces p0=L*F and q0=L*G for a nonzero polynomial L. Hence
m<=k-1-z, proving (3).

The rank-one degree budget d+2m<2k gives only z+2m<2k. It can therefore
charge common zero rows less than the degree cost required in (3).

## 3. Exact condition for membership in the original RS code

There are polynomials h_1,h_2 of degree <k whose evaluations equal E
exactly if and only if there exists H in K[T] such that

    D=H^2 and e_x=H(x)*(F(x),G(x)) for all x.         (4)

Proof: products of actual RS polynomials have degree <=n-2, so uniqueness
of interpolation gives N=(h_1,h_2)^T(h_1,h_2). The primitive rational
ratio implies h_1=HF,h_2=HG, and then D=H^2. Conversely (1) and D=H^2
give deg H+m<k, so (4) supplies the required code polynomials.

In odd characteristic, if D is a polynomial square, the row values may
still differ from this polynomial pair by independent signs. Those signs
are invisible to every quadratic Gram identity. Applying one such sign
vector globally to all words preserves supports and the MCA event under
the corresponding transformed code; it must not be confused with proving
membership in the original fixed code.

It is enough that D=c*H0^2 have even irreducible valuations: an active
node exists, and its nonzero square value D(x)=t_x^2 forces c to be a
square in K. The scalar-square condition is then automatic. Zero rows
cause no obstruction once D is a square, since z<=deg H and (1) imply
z+m<k.

## 4. A full-support production false positive with first shifted rank ONE

Let Omega=mu_n, n=2k a power of two with n>=8. For a nonzero field scalar c
put

    t(x)=x^(k-2)+c*x^(k+2),  e_x=t(x)*(1,x),
    D(T)=T^(n-4)+c^2*T^4+2c.

Modulo T^n-1, t(T)^2 is exactly D(T). Consequently

    N(T)=D(T)*[1,T;T,T^2],                           (5)

whose degree is n-2 (at n=8 combine the two T^4 terms and require
1+c^2 !=0). All rational 2-by-2 minors therefore vanish.

For B_s(E)=sum_x x^(s+1)e_x^T e_x, the subgroup sum gives

    B_0(E)=0,
    B_1(E)=n*[0,0;0,1]  when n>8.

At n=8 the second expression is multiplied by 1+c^2. Thus the first
shifted form has rank exactly one. Every higher inequality rank B_s<=s
for s>=2 holds because these matrices have two rows and columns. In fact
the ranks for s=1,...,k are (1,2,1,0,...,0) in the checked profiles.
This is a false positive for both the Cauchy-minor and shifted-rank
relaxations, including the first shifted rank being exactly one.

Take the actual production field

    p=365375409332725729550921208179070755120141565953,
    n=1073741824, k=536870912, c=2, M=n/4=268435456.

The row multiplier is nowhere zero exactly when (-1/c)^M !=1. The
checker verifies this inequality by exact modular exponentiation.
Consequently E is itself an [n,2] MDS space: any two rows have determinant
t_x*t_y*(y-x) !=0. It is not the half-rate code assumed in the earlier
full-code characterization.

D is not a polynomial square. Write

    R(Y)=Y^(M-1)+c^2*Y+2c, D(T)=R(T^4).

Since c and the characteristic are nonzero and p does not divide 4,
D has no repeated root if R has none. A common root of R and R' must be

    y=-2*(M-1)/(c*(M-2)).

This follows by subtracting (M-1)R from YR'. At c=2 and the exact
production M, direct modular exponentiation gives

    R(y)=179052947728843771035873342159914811345174123349 !=0.

Also R(0)=4 !=0, so composition with T^4 adds no repeated root.
Thus D is nonconstant and squarefree, hence not a square even over an
algebraic closure. This excludes (4). Directly, the two canonical
interpolation polynomials t(T),T*t(T) have degrees k+2 and k+3, both
strictly above the RS degree cap and below n.

No billion-node field scan or expanded billion-degree polynomial is used.
These are sparse polynomial identities and logarithmic modular powers.

## 5. A zero-row false positive that fails even invertible rescaling

On the same subgroup put

    t(x)=(1-x^k)/2, e_x=t(x)*(1,x),
    D(T)=(1-T^k)/2.

Here t is the indicator of the coset with x^k=-1, so t^2=t at every
node. The normal form is again N=D*[1,T;T,T^2], with degree k+2<n
for k>=4. All rational minors vanish. There are exactly z=k zero rows
and m=1, violating (3). Indeed every nonzero RS_k word has support at
least k+1, whereas both columns are supported on exactly k coordinates.
This example also satisfies B_0=0 and all rank B_s<=s in the checked
range; at n=8 the first shifted rank is one and at larger sizes it is zero.

## 6. The remaining sign ambiguity is separate

For completeness, e_x=x^k*(1,x) has full support and gives D=1 and
N=[1,T;T,T^2], identical to the true polynomial pair (1,T). Its two
interpolation polynomials are T^k,T^(k+1), so it is not in the original
RS_k code. It differs by the single global coordinate-sign vector x^k.
This example isolates the sign ambiguity; it does not refute equivalence
under invertible coordinate scaling.

## Verification and scope

Run `python3 scripts/probes/astra_mca_cauchy_normal_form_check.py`. Dense controls on orders 8,16,64
over F257 and the production prime independently interpolate the row
products, check the exact polynomial determinants, recover the primitive
normal form, and verify the shifted Gram ranks. Sparse production checks
verify (5), squarefreeness, full support, and all degree arithmetic at the
actual n and p. No actual production MCA witnesses are constructed.

The original witness equation E=RZ, QZ=0 supplies true codeword columns
before relaxation. The results here identify precisely what is lost when
that membership is replaced only by Cauchy minors or moment-rank bounds:
an uncontrolled polynomial scalar factor, common-zero degree costs, and
coordinate square-root signs. These examples do not satisfy an asserted
exact polynomial square-root identity; that missing condition is substantive.

The root agent independently reviewed the normal form, both converse criteria, the sign distinction, and the sparse production false positive. The polynomial identities and finite-field nonvanishing checks passed review. This is agent review of written arguments, not external human peer review or Lean verification.

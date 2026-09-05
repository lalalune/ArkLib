# Three candidates for received polynomials of bounded interpolation degree

On the actual production domain, the punctured scalar list has at most
**three polynomials** whenever the received word's interpolation polynomial
has degree at most 715827883. An explicit word in this class attains three,
with three distinct values at the omitted point. This proves a restricted
case of the [single-hole value problem](astra_mca_single_hole_reduction-2026-09-05.md).

This is a written proof with exact finite controls and production arithmetic,
not a Lean-verified or independently reviewed result. It does not cover
arbitrary received words: interpolation degrees 715827884 through 1073741822
remain outside this entire-list argument. The subsequent
[root-multiplicity extension](astra_mca_split_root_rigidity-2026-09-05.md)
bounds the fully split sublist at every received degree and, more generally,
each fibre with a fixed outside-domain factor. The number of different
outside factors is still uncontrolled. Neither argument supplies a universal
MCA lower bound or grand-prize solution.

## Parameters and statement

Use the existing [prime and generator certificate](../../ArkLib/Data/CodingTheory/ProximityGap/Frontier/_PrizeShapePrimeP30.lean):

```text
n=2^30=1073741824,
P=365375409332725729550921208179070755120141565953,
g=303645430271030343624574566109998498685964493478 in F_P,
order(g)=n,
k=n/2=536870912,
b=(n+2)/6=178956971,
A=k+b=715827883.
```

Let Omega=mu_n and remove any a in Omega. Write V for the unique polynomial
of degree at most n-2 representing a received word on D=Omega\{a}. If
degree V<=A, then

```text
#{f : degree f<k, #{x in D : f(x)=V(x)}>=A} <= 3.       (1)
```

The associated single-hole MCA event has agreement threshold A+1 and radius
357913940/n. The [exact Lean reduction](../../scripts/probes/astra_mca_single_hole.lean)
identifies its bad scalars with the values f(a), so (1) would supply at most
three such scalars for this received-word class once the present written
argument is formalized. The reduction alone does not prove (1).

Rescaling x by a reduces the proof to a=1 without changing polynomial degrees
or agreement counts. We use that normalization below.

## An integer determinant lemma

Let m>=8 be a power of two, let z in F_p have exact order m, and let
v_0,...,v_(m-1) belong to {-1,0,1}. Suppose

```text
sum_i v_i*z^(ij)=0 in F_p,       1<=j<=h<m.
```

Put d=m/2, r=ceil(h/2), c_i=v_i-v_(i+d), and
C(T)=sum_(i<d) c_i*T^i in Z[T]. If

```text
p^(2r) > (2m)^d,                                      (2)
```

then c_i=0 for every i; equivalently v_(i+d)=v_i as integers.

Consider the integer d-by-d matrix M of multiplication by C in
Z[T]/(T^d+1). Each row is a signed permutation of the coefficients c_i.
Therefore Hadamard's determinant inequality gives

```text
det(M)^2 <= (sum_i c_i^2)^d <= (4d)^d=(2m)^d.           (3)
```

Modulo p, T^d+1 splits into the d distinct roots z^j with j odd. Evaluation
at those roots diagonalizes multiplication by C. For odd j, z^(jd)=-1,
so C(z^j)=sum_i v_i*z^(ij). The stated equations provide r distinct zero
eigenvalues. Thus M modulo p has nullity at least r and

```text
p^r divides det(M).                                    (4)
```

For completeness, the integer matrix divisibility fact in (4) follows by
Gaussian row elimination modulo p, lifting each row operation to integers.
The resulting last r rows are divisible by p. The determinant multiplier
from the lifted operations is prime to p, so divisibility by p^r passes back
to det(M). No assertion about extra p-adic precision at one root is used.

If C is nonzero, its multiplication matrix is invertible over Q: T^d+1 is
the irreducible cyclotomic polynomial Phi_m and degree C<d. Consequently
det(M) is a nonzero integer. Equation (4) then gives det(M)^2>=p^(2r),
contradicting (2) and (3). Hence C=0, proving the lemma.

The distinction from a single-evaluation norm argument is essential.
Here r different primitive roots give r divisibility factors. The
repository's [height/norm ceiling](../../ArkLib/Data/CodingTheory/ProximityGap/Frontier/_OCPieceBHeightNormCeiling.lean)
and [single-evaluation height obstruction](../../ArkLib/Data/CodingTheory/ProximityGap/Frontier/_OcNegacyclicHeightNoGo.lean)
do not supply these vanishing evaluations for general relations. In the
application below they come from actual matching polynomial coefficients.

## Matching initial moments force period four

Let S and S' be subsets of Omega\{1} of size A. Suppose their monic root
polynomials H_S and H_S' have the same coefficients in degrees k through
A-1. Newton's identities then give equality of the power sums of their roots
for every exponent 1<=j<=A-k=b. Thus the integer indicator difference

```text
v_i=1_(g^i in S)-1_(g^i in S')
```

satisfies the preceding moment equations. In addition, v_0=0 and sum_i v_i=0
as integers. Newton's implication only uses the equality of the initial
elementary symmetric functions; it makes no bounded-height assumption about
the arbitrary received-word coefficients.

Apply the determinant lemma first with m=n and h=b. After obtaining
v_(i+m/2)=v_i, the even-indexed moment equations become

```text
2*sum_(i<m/2) v_i*(z^2)^(ij)=0,       1<=j<=floor(h/2).
```

Since p is odd, these are the same equations for the shortened vector,
root z^2, order m/2, and moment cap floor(h/2). Iteration down to order
eight proves that the original indicator difference has period four.

All 28 determinant steps meet (2) at the production prime without computing
the enormous powers in that inequality. The exact arithmetic certificate is

```text
P > (2n)^4 = 2^124,
16*ceil(floor(b/2^j)/2) >= n/2^j,
                         j=0,...,27.
```

For each step, put m=n/2^j and r=ceil(floor(b/2^j)/2). These facts imply

```text
P^(2r) > (2n)^(8r) >= (2m)^(m/2).
```

The checker verifies all 28 integer inequalities. After the order-eight
step the remaining order is four and the remaining moment cap is zero.
This is a finite arithmetic check of the production constants, not a
billion-node enumeration or an extrapolation from small fields.

## Counting the coefficient fibre

Partition Omega into the four cosets C_0,...,C_3 of mu_(n/4), with 1 in C_0.
Period four of the exponent indicator difference says that S and S' differ
by a constant on each coset.

Fix one S in a coefficient fibre. On any coset where S is partially filled,
that constant must be zero: adding 1 or -1 would take some indicator outside
{0,1}. An empty or full coset can only remain such or switch to full or
empty. On C_0, the omitted point forces the difference to be zero regardless
of its other memberships.

There are therefore at most three cosets whose empty/full status can vary.
The cardinality A fixes how many are full, since they have equal size.
Among t<=3 such cosets there are at most binomial(t,s)<=3 choices for any
fixed s. Every coefficient fibre contains at most three root sets.

If degree V=A, every list candidate f gives a monic polynomial
H_f=(V-f)/lc(V) of degree A with at least A roots in D. It has exactly those
A roots and hence is their root polynomial. Its coefficients in degrees
k through A-1 are independent of f. Distinct f give distinct H_f, so the
coefficient-fibre bound proves (1).

If k<=degree V<A, no candidate is possible by the root bound on V-f.
If degree V<k, only f=V is possible. This includes V=0 and completes the
degree-at-most-A statement.

## An exact three-member production list

Put ell=n/4 and i=g^ell, so i^2=-1. Choose any b nodes from C_0\{1}, and
let R be their monic locator. This is possible since b<=ell-1. Define

```text
U_j=X^ell-i^j,     j=1,2,3,
H_0=R*U_1*U_2, H_1=R*U_1*U_3, H_2=R*U_2*U_3,
V=H_0,             f_j=V-H_j.
```

Each H_j has exactly A=b+2ell distinct roots in D. The polynomials f_j
have degree at most A-ell=b+ell<k, since the leading private product terms
cancel. They consequently give three decoded candidates. Their values at
the omitted point are

```text
0, -2i*R(1), -4i*R(1),
```

which are distinct. The upper bound proves that these are the complete
list, not just three members of a possibly larger one. This sharpens the
status of a particular choice in the earlier
[three-coset construction](astra_mca_locator_pencils-2026-09-05.md); that
construction allowed arbitrary received values on the shared error region
and did not classify the full production list.

## Controls and remaining gap

Run `python3 scripts/probes/astra_mca_moment_rigidity_check.py`.

The checker covers every signed indicator difference with v_0=0 at orders
eight and sixteen by joining two exhaustive half-vector tables. It checks
equal cardinality and all required moments, not random samples. In the
fields passing the determinant gates, exactly seven such differences remain,
all periodic with period four. At order sixteen this represents 3^15
possible signed vectors per field.

The characteristic gate matters. Over F17 there are 23 moment solutions at
order eight, including 16 nonperiodic ones, and 351 at order sixteen,
including 344 nonperiodic ones. Explicit examples give nonzero negacyclic
determinants 34 and 2312; the latter is divisible by 17^2. The same checker
verifies the matrix rank, divisibility, and Hadamard bound for these examples.

An exhaustive census of all 1365 degree-eleven divisors on mu_16\{1} over
the production prime finds 1362 singleton coefficient fibres and one fibre
of size three. Over F17 the largest fibre is also three, but 56 differences
from fibre representatives fail period four. Thus the small-field list
maximum alone would not validate the rigidity argument.

The explicit three-member construction is checked at orders sixteen and
sixty-four over the actual prime, including the independent same-support
no-joint rank condition. At production the checker verifies the full
28-step numerical certificate and construction degree margins; the list
classification uses the written determinant and counting proof above.

The unrestricted received polynomial can have degree as large as n-2.
For degree greater than A, V-f may have additional roots outside its chosen
agreement set or a nonconstant residual factor. Its top coefficients then
no longer give equality of the root sums of those agreement sets alone.
The [subsequent extension](astra_mca_split_root_rigidity-2026-09-05.md)
handles every higher degree when all roots remain in the domain, allowing
arbitrary multiplicities, and bounds each fixed outside-factor fibre. It
does not bound variation between different outside factors. The entire-list
extension, independent mathematical review, and Lean formalization remain open.

# A third-Hasse interpolation source and its remaining properness gap

Adding the third divided derivative gives a positive uniform source at the
companion parameters with residual total degree **915**, below the 1031 cap
of the previously recorded second-Hasse source. Its exact dimension surplus
is 1033048571. This is a new interpolation certificate, **not** a proof that
the resulting equation cuts the selected MCA surface.

After clearing derivative denominators, the new total-degree bound is larger
than the earlier second-Hasse cut bound. Also, the earlier acceleration-field
properness criterion cannot be applied unchanged when two extra derivative
variables are present. No improved MCA allowance or prize score follows.

## Source and local contact equations

Let w>3 and work in characteristic p>3. Introduce the divided-derivative
variables R1,R2,R3, corresponding to f', f''/2, and f'''/6. Use the full space
of monomials

```text
X^a Y^i R1^j R2^k R3^l Z^z,
a+w*i+(w-1)*j+(w-2)*k+(w-3)*l < D,
i+j+k+l+z <= T,
j<=S1, k<=S2, l<=S3.
```

At a node x_s with received affine value u0_s+Z*u1_s, substitute

```text
X=x_s+t,
Y=u0_s+Z*u1_s+t*R1-t^2*R2+t^3*R3+v,
weight(t,v,R1,R2,R3,Z)=(1,4,0,0,0,0).
```

Require all terms of weight <m to vanish. Translations in X and in Y by
u0_s+Z*u1_s preserve the full source space, in both directions. Consequently
the local rank is independent of the node and received values.

For a selected polynomial f, the substituted value of v is

```text
f(x_s+t)-f(x_s)-t*f'(x_s+t)
  +t^2*f''(x_s+t)/2-t^3*f'''(x_s+t)/6,
```

which is divisible by t^4. Thus every agreement gives a root of multiplicity
at least m after substituting the actual derivatives. If D<=m*A, a polynomial
with at least A agreements satisfies the resulting global differential
identity. This step does not assume a common factor or a proper cut.

## Exact local rank profiles

Fix h=i+j+k+l and temporarily omit Z. Set

```text
r=a+3*h-j-2*k-3*l,
d=3*h-j-2*k-3*l.
```

The global weighted cutoff is r<D-(w-3)h, and a>=0 is r>=d.
Use the homogeneous coefficient columns

```text
(U+V-W0+T0)^i V^j W0^k T0^l.
```

A row U^e V^b W0^c T0^(h-e-b-c) has output weight v_row=2b+c-e.
In the original substitution its t exponent is r-3e-2b-c, and its contact
weight is r-v_row. The nonzero column entries automatically have nonnegative
t exponents, since they arose from original monomials with a>=0.

Sort columns by increasing d and rows by decreasing v_row. Gaussian
elimination with the leftmost nonzero column as pivot produces pairs
(d_pivot,v_row). They simultaneously encode every needed prefix rank:

```text
rank(h,r,m) = #{(d,v) in the profile : d<=r<m+v}.        (1)
```

Processing rows in the stated order gives the row prefix; leftmost pivots
also give every column prefix. Columns or rows with equal weights are
included together in (1). The homogeneous substitution is invertible, so
processing all rows eventually yields one pivot per column.

For h>S1+S2+S3, every column has a common power Y^(h-b), where
b=S1+S2+S3. The profile can be obtained at degree b and shifted by

```text
(d,v) |-> (d+3*(h-b), v+2*(h-b)).                      (2)
```

Indeed the common factor (U+V-W0+T0)^(h-b) has unique highest-weight term
V^(h-b), of coefficient one. Multiplication therefore shifts the output
filtration by exactly 2(h-b), in every characteristic; the input shift is
3(h-b). No assumption about invertibility of high factorials is used.

For cap_h=D-(w-3)h, the layer counts are

```text
C_h=sum_(d,v) max(0,cap_h-d),
L_h=sum_(d,v) max(0,min(cap_h,m+v)-d).
```

Restoring Z multiplies each h layer by T+1-h, for h<=T. Hence

```text
C(T)=sum_(h<=T) (T+1-h)*C_h,
L(T)=sum_(h<=T) (T+1-h)*L_h.
```

The combined n-node rank is at most n*L(T). Thus C(T)>n*L(T) supplies a
nonzero Q uniformly for every received affine line. We do not assume that
the node maps are independent.

Above H=floor((D-1)/(w-3)), put slope=sum(C_h-nL_h) and
moment=sum h(C_h-nL_h). Then C(T)-nL(T)=(T+1)*slope-moment. The checker also
examines every smaller T before using this affine formula.

## Companion certificates

All rows use n=262144, w=131071, A=181353, D=m*A, and p=2130706433.

| m,S1,S2,S3 | First positive T | Source C | Local rank L | C-nL |
|---|---:|---:|---:|---:|
| 80,24,6,0 | 1042 | 106458223810750 | 406103404 | 653072574 |
| 80,24,6,1 | 925 | 185934664372800 | 709277398 | 1850151488 |
| 99,30,8,1 | 915 | 439776945574395 | 1677611971 | 1033048571 |
| 80,24,6,2 | 992 | 296942308628000 | 1132736412 | 2254640672 |

The zero-R3 row exactly reproduces the separate second-Hasse implementation.
This is expected: when Q is independent of R3, replacing the old contact
deviation by t^3*R3+v preserves its order-three filtration and all its ranks.
The displayed T values are minimal for their specified m and derivative caps,
not globally optimal among third-Hasse sources.

## Substitution on the old MCA surface

On a regular irreducible surface F(X,Y,R,Z)=0 write

```text
H=F_R, G=-F_X-RF_Y,
delta(X)=1, delta(Y)=R, delta(R)=G/H, delta(Z)=0.
```

The source substitutions are

```text
R1=R, R2=G/(2H), R3=N3/(6H^3),
N3=H^2*(G_X+R*G_Y)+H*G*G_R
     -G*(H*(H_X+R*H_Y)+G*H_R).
```

If the total Y,R,Z degree of F is t, then deg H<=t-1, deg G<=t, and
deg N3<=3t-2. Clearing H^(S2+3*S3) gives a polynomial B_Q with

```text
degree(B_Q) <= T+(t-1)*(S2+3*S3).                      (3)
```

At the binding degree t=2364, the new caps in (3) are respectively 22192,
26908, and 29348 for the three positive-R3 rows. They exceed the earlier
second-Hasse bounds 15220 and 19935. A smaller original T therefore does not
mean a smaller cleared cut.

If B_Q is proper on F, these bounds can still be used in the
[component split](astra_hasse_component_split-2026-09-05.md), whose conditional
cell allowance at cutoff M=2048 is

```text
188834222914524 + 2951611603152*degree(B_Q).
```

Each of the three degree caps is below its sufficient boundary 90146.
That is a conditional single-cell comparison; neither properness nor the
complete phase maximum is supplied by this calculation.

## Why the previous field-degree criterion needs another argument

For one extra derivative variable S, the earlier
[acceleration-extension criterion](astra_acceleration_extension-2026-09-05.md)
uses a principal ideal: polynomials in K(X,Y,R)[S] vanishing at acceleration
are multiples of its minimal polynomial. This common factor, independent of
Z, allows the full-kernel descent argument.

With both R2 and R3, coefficient polynomials vanishing at their algebraic
values lie in an ideal in two variables. That ideal need not be principal.
Even when both values are zero, the polynomials R2 and R3 vanish together
but have no nonconstant common factor. Thus independence of low powers of Z
does not, by itself, produce the common divisor needed for the old descent.
This is an obstruction to that inference, not a full interpolation-kernel
counterexample. Proving properness needs additional information about the
two-variable relation ideal or about the actual contact kernel.

The [scalar tail split](astra_scalar_tail_split-2026-09-05.md) also supplies
no direct saving for the existing tangent MCA components. The pinned companion
already proves their polynomiality in
[`RCN312.tangent_truncatedPolynomial_solution`](https://github.com/proximity-prize/proximity-prize/blob/032154395c51fd6f77715a7f42d9a987ab9fb48a/ProximityPrize/SubmissionLower/PackedLegacy.lean#L12808)
and bounds coefficient poles by the Y,Z projection budget in
[`coefficientPoleProfile_of_tangent_firstTail`](https://github.com/proximity-prize/proximity-prize/blob/032154395c51fd6f77715a7f42d9a987ab9fb48a/ProximityPrize/SubmissionLower/PackedLegacy.lean#L12846).
Those components already
have the relevant constant-field curve argument. The main open contribution
is the nontangent moving estimate or a new proper equation cutting it.

## Reproduction and proof status

Run `python3 scripts/probes/astra_third_hasse_check.py --sanitize`.
It compiles the bounded C++ profiler with undefined-behavior checks, compares
profiles against literal substituted matrices over four characteristics,
checks the common-Y shift, independently sums the production monomials,
reproduces the existing second-Hasse row, and checks all displayed margins.
The retained run passes 7000 direct block comparisons and 64 shifted profiles.

The full production matrix is not constructed. These exact rank calculations
and the written profile argument are not a Lean formalization or independent
mathematical review. The polynomial pullback may vanish identically on F;
positivity of its source kernel does not rule that out. The prize remains open.

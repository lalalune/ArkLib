# Colon ideals and a graded Hermite bound for quotient kernels

The proposed contact-colon identity is already proved in the official source.
Combining it with a filtration by global Y degree gives a useful mathematical
upper bound on the quotient kernel. At the current binding degree flag, however,
that bound is far larger than the available source-kernel dimension lower bound,
even under the favorable extra assumption that the divisor has contact order
zero at every node. This gives no improved protocol bound or leaderboard score.

The source pin is
[`032154395c51fd6f77715a7f42d9a987ab9fb48a`](https://github.com/proximity-prize/proximity-prize/commit/032154395c51fd6f77715a7f42d9a987ab9fb48a).
This follows the [T-cutoff investigation](astra_t_cutoff-2026-09-04.md), at error
cell 80791 targeting 68.04. The graded Hermite lemma below has a mathematical
proof and independent finite-matrix transcription checks; it has not been
formalized or linked to `ProtocolClaim` in Lean.

## The exact existing colon identity

At node i, localize by

```text
X = x_i + t,
Y = u0_i + Z*u1_i + R*t + v,
```

with weights `(t,v,R,Z)=(1,2,0,0)`. Over the coefficient domain `K[R,Z]`, let
`J_m` be the ideal spanned by `t^a v^b` with `a+2b >= m`. For nonzero F, let
`nu_i(F)` denote its minimum local weight. Additivity of minimum weight gives

```text
(J_m : localize_i(F)) = J_max(0,m-nu_i(F)).
```

These are the existing `ContactOrderBridge.contactOrder_mul` and
`ContactOrderBridge.contact_colon_iff` in
[`PackedLegacyCore2.lean`](https://github.com/proximity-prize/proximity-prize/blob/032154395c51fd6f77715a7f42d9a987ab9fb48a/ProximityPrize/SubmissionLower/PackedLegacyCore2.lean#L1526).
The connection with the actual interpolation kernel is the equivalence
`LocatorContact.mem_kernel_iff_contactAtLeast` in
[`PackedLocatorTail.lean`](https://github.com/proximity-prize/proximity-prize/blob/032154395c51fd6f77715a7f42d9a987ab9fb48a/ProximityPrize/SubmissionLower/PackedLocatorTail.lean#L536).

The condition `nu_i(F)=0` means that
`F(x_i,u0_i+Z*u1_i,R,Z)` is a nonzero polynomial in the **free** variables R,Z.
It need not be a unit: its nonzero initial form suffices because the associated
graded ring is a domain. Multiplication by F is then injective on the contact
jet quotient. If its order is positive, the retained order drops exactly as
above; for example, `t*t^(m-1)` has order m while `t^(m-1)` does not.

The audited lower-source closure contains no invocation of `contact_colon_iff`
outside its definition. Existing quotient/source arguments use support boxes
and contact-strip projections; those do not by themselves supply an upper bound
on this kernel with retained nodewise contacts. An interpolation **rank upper
bound** supplies a kernel **lower bound**, which has the wrong direction here.

## Graded Hermite kernel upper bound

Let the nodes x_i be distinct, and impose contact orders m_i, possibly different
at each node. Let V be the vector space of polynomials supported in the box

```text
Yexp + Rexp + Zexp <= T,
Yexp + Rexp <= YS,
Rexp <= S,
Xexp + w*Yexp + (w-1)*Rexp < D,
```

that satisfy every prescribed contact condition. Define

```text
H_h = sum_i max(0,m_i-2*h).
U(D,T,YS,S;m_i) =
  sum_{h=0..min(T,YS)}
  sum_{j=0..min(S,YS-h,T-h)}
    (T+1-h-j) * max(0,D-w*h-(w-1)*j-H_h).
```

Then `dim_K(V) <= U(D,T,YS,S;m_i)`.

To prove it, filter V by global Y degree: `V_h = V intersect {deg_Y <= h}`.
For `P = sum_{b<=h} C_b(X,R,Z) Y^b`, the coefficient of local `v^h` is exactly
`C_h(x_i+t,R,Z)`. Terms with lower global Y degree cannot contribute to it.
The contact condition forces this coefficient to be divisible by
`t^max(0,m_i-2*h)`. Consequently each X-polynomial coefficient of `R^j Z^z`
in C_h is divisible by

```text
product_i (X-x_i)^max(0,m_i-2*h),
```

which has degree H_h. Distinct nodes make these factors relatively prime.
This assertion uses polynomial translation, or equivalently Hasse derivatives,
and is valid in arbitrary characteristic. It requires no division by factorials.

The leading-Y-coefficient map on V_h has kernel V_(h-1). Its image therefore
has dimension at most the h-slice in U: each X channel has its width reduced
by H_h, and the allowed number of Z exponents is `T+1-h-j`. Summing the
successive dimension increments proves the bound. This is a rank lower bound,
so it has the direction needed for a divisor obstruction.

If a fixed nonzero F divides every source-kernel polynomial, unique division
gives an injective linear map into its quotient support box. The colon identity
adds contact orders `m_i=max(0,m-nu_i(F))`. Hence a sufficient contradiction is

```text
source_kernel_dimension_lower_bound > U(quotient_box; m_i).
```

For an arbitrary universal factor, the order profile must still be established.
The factor's degree flag alone does not establish order zero at every node.

## Exact failure at the present binding flag

Use `n=262144`, `w=131071`, agreements `a=181353`, and the binding factor flag

```text
(total degree, joint YR degree, R degree) = (2364,47,10).
```

These are the exact degree labels of the binding raw flag, not merely support
upper bounds. The lower bound below requires joint YR degree at least 47 and
R degree at most 10; upper bounds on all three degrees would not suffice.

For the optimized T source `(m,L,S)=(166,7159,51)`, its weighted parameter is
`D=30104598` and joint YR cap is 229. Using only the factor contact-degree
lower bound `c(F)>=w*47-10=6160327`, its quotient lies in the box

```text
(D',T',YS',S') = (23944271,4795,182,41).
```

Even assuming `nu_i(F)=0` at **every** node, the exact numbers are:

| Quantity | Value |
|---|---:|
| Available source-kernel nullity lower bound | 228451639 |
| Graded Hermite quotient-kernel upper bound | 110165530464248 |
| Upper bound minus nullity lower bound | 110165302012609 |

The inequality needed for the contradiction fails. The same test fails for all
52 prescribed A/T/C and helper sources checked by the probe. This is a scoped
failure of this numerical test using the stated worst-case degree information;
a larger actual `c(F)` or stronger knowledge of the actual source-kernel
dimension can change the comparison. It is not a no-go theorem for all colon
arguments, interpolation spaces, or source choices. Allowing positive factor
orders only weakens this particular retained-contact upper bound.

There is also an actual large quotient-contact space when both received words
are zero. Then `Y=R*t+v` has local order one, so all monomials

```text
Y^166 * X^x * Z^z,
0 <= x <= 2186484,
0 <= z <= 4629,
```

fit that quotient box and retain order 166 at every node. They span a space of
dimension **10123425550**, already larger than 228451639. This is an exact
obstruction to replacing U by a uniformly tiny upper bound using contact and
support constraints alone. The zero words do not satisfy the far-word condition;
this construction claims neither a universal divisor nor a large regular family.
Those additional hypotheses are precisely information a stronger argument could
use. In contrast, the total-degree-one quotient box of the T-cutoff argument has
Hermite upper bound zero **if** all 166 contact orders are retained.

## Replay and remaining obligation

Run from the repository root:

```sh
python3 scripts/probes/astra_colon_audit.py
```

The probe uses exact Python integers, asserts the displayed T values and the
explicit zero-word subspace dimension, and evaluates the 52 prescribed source
rows. It also constructs 24 small contact matrices directly by multinomial
substitution over F2, F5, and F7, computes Gaussian ranks, and checks that actual
nullities do not exceed U. These are transcription checks, not a finite-field
substitute for the general proof. An independent root review also checked the
proof and a separate 27-case direct-matrix calculation over F101.

The useful remaining target is a comparison between the **actual source-kernel
dimension** and its subspace divisible by F, exploiting universal-factor
provenance and the far-word/large-family hypotheses. The tiny uniform nullity
lower bound and the support/contact constraints above do not deliver that
comparison at this flag. Formalizing the new filtration bound would establish
a reusable lemma, but would not by itself close the numerical gap.

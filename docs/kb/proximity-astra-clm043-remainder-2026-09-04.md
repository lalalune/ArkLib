# CLM-043 remainder: improve the uniform constant from 87 to 24

Date: 2026-09-04. This is a proof using the classical Hasse theorem and an
independent exact diagnostic package. It is not a Lean-checked theorem.

The remainder in the CLM-043 identity satisfies the stronger bound

```text
D_6 = 36 U + R,             |R| < 24 q n^3
```

whenever `n>=3`, `q>=n^4`, and the field has odd cardinality `q`. The proof
works for **any set of n distinct nonzero evaluation points**, hence applies
in particular to the multiplicative subgroups in the original prime-field
statement. It improves that statement's remainder coefficient `87` to `24`.

This does not bound the nonnegative main term `U` and does not close a
Proximity Prize target. No optimality or novelty beyond this comparison
with the inspected CLM-043 bound is claimed.

## Definitions and source

Let `K` be a finite field of odd cardinality `q`, let `G` be a set of `n`
distinct nonzero elements of `K`, and let `chi` be its quadratic character,
extended by `chi(0)=0`. For nonzero `t`, write

```text
x_a(t) = chi(1-at),
e_j(t) = sum_(A subset G, |A|=j) product_(a in A) x_a(t),
U = sum_(t != 0) e_3(t)^2,
D_6 = 720 sum_(t != 0) e_6(t),
R = D_6 - 36 U.
```

These agree with the definitions in the
[CLM-043 note at commit 63cfd25644ad3f98c134212f647bc10e7ee48d5a](https://github.com/geofflava/ArkLib/blob/63cfd25644ad3f98c134212f647bc10e7ee48d5a/docs/kb/deltastar-466-clm043-cyclotomic-row-transfer-2026-08-25.md).
Every field sum here excludes `t=0` unless explicitly marked complete.

## Exact ordered-overlap decomposition

For `j=0,1,2,3`, define

```text
I_j = sum_(ordered triples A,B subset G, |A intersect B|=j)
      sum_(t != 0) product_(a in A) x_a(t) product_(b in B) x_b(t).
```

Expanding the square gives `U=I_0+I_1+I_2+I_3`. Every six-element set admits
`C(6,3)=20` ordered disjoint triple pairs, so `36 I_0=D_6`. Therefore

```text
R = -36 (I_1+I_2+I_3).                                  (1)
```

The numbers of ordered pairs in the three relevant sectors are exactly

```text
N_3 = C(n,3),
N_2 = 3(n-3) C(n,3),
N_1 = 3 C(n-3,2) C(n,3),
```

where `C(n-3,2)=0` for `n=3,4`. These count intersection choices inside
the first triple and the remaining choices outside it.

## The diagonal sector is exact

When `A=B`, the summand is one except at the three distinct inverse roots
`t=a^(-1)`, where it is zero. Excluding `t=0` therefore gives

```text
I_3 = N_3 (q-4).                                         (2)
```

This keeps both the puncture and every inverse-root zero.

## Two shared points: an exact quadratic character sum

If `|A intersect B|=2`, let `a,b` be the two elements in the symmetric
difference and let `c,d` be the common elements. After removing squared
factors, the complete quadratic sum is

```text
sum_(t in K) chi((1-at)(1-bt)) = -chi(ab).                 (3)
```

For completeness, translate and scale the two distinct roots. The identity
reduces to `sum_z chi(z^2-1)=-1`: counting `y^2=z^2-1` is equivalent to
choosing a nonzero value of `z-y`, since `(z-y)(z+y)=1` and two is
invertible. There are `q-1` such pairs, while the character count is
`q+sum_z chi(z^2-1)`.

The desired sum deletes `t=0` and the two common inverse roots. Its exact
value is

```text
-chi(ab) - 1
-chi((1-a/c)(1-b/c)) - chi((1-a/d)(1-b/d)).               (4)
```

Each character has absolute value at most one, so

```text
|I_2| <= 4 N_2.                                          (5)
```

No square-subgroup assumption occurs in (3) or (4).

## One shared point: use the elliptic bound, retaining infinity

If `|A intersect B|=1`, the symmetric difference consists of four distinct
elements `a_1,...,a_4`; let `c` be the common element. Put

```text
f(t) = product_(i=1..4) (1-a_i t),
L = product_(i=1..4) a_i,
J = sum_(t in K) chi(f(t)).
```

The smooth projective model of `y^2=f(t)` has genus one: the double cover
of the projective line branches at its four distinct finite roots. It has
the rational point `(0,1)`, so it is an elliptic curve after choosing that
point as origin. Its affine point count is `q+J`; the number of rational
points at infinity is `1+chi(L)`. Hasse's theorem consequently gives

```text
|J+chi(L)| <= 2 sqrt(q),
|J| <= 2 sqrt(q)+1.                                      (6)
```

The classical input is verified in J. S. Milne,
[*Elliptic Curves*, second edition, Chapter IV, Theorem 9.4, printed page 150](https://www.jmilne.org/math/Books/EC2.pdf#page=155).
The paragraph following its proof extends the statement from `p` to `q`.
We use this established theorem; the diagnostic checks below are not a
replacement proof of Hasse's theorem.

The desired correlation is `J-1-chi(f(c^(-1)))`: delete `t=0` and the
common inverse-root term. Thus

```text
|I_1| <= (2 sqrt(q)+3) N_1.                              (7)
```

This is where treating the squarefree quartic as genus one improves on a
generic degree-based `3 sqrt(q)` estimate.

## Explicit bound and the uniform coefficient 24

Combining (1), (2), (5), and (7) yields the useful finite-size bound

```text
|R| <= B(q,n)
     := 36 [N_3(q-4)+4N_2+(2 sqrt(q)+3)N_1].             (8)
```

Equivalently,

```text
B(q,n) = n(n-1)(n-2)
         [6q + 18(n-3)(n-4)sqrt(q) + 27n^2-117n+84].
```

For `n=3`, there is one triple and no six-element set, so
`R=-36(q-4)` directly, which is strictly smaller in absolute value than
`24 q n^3`.

For `n>=4`, set `A=3N_1+4N_2-4N_3`. This is nonnegative because
`4N_2-4N_3=4N_3(3n-10)>0`. From `sqrt(q)>=n^2`,

```text
B(q,n)/(36q) = N_3 + 2N_1/sqrt(q) + A/q
             <= N_3 + 2N_1/n^2 + A/n^4
              = B(n^4,n)/(36n^4).
```

The endpoint margin has the exact expansion

```text
24 n^7 - B(n^4,n)
 = n [198n^5 - 669n^4 + 1098n^3 - 921n^2 + 486n - 168]
 = n [n^4(198n-669) + n^2(1098n-921) + (486n-168)] > 0.
```

Each parenthesis in the last line is positive for `n>=4`. Therefore

```text
|R| <= B(q,n) < 24 q n^3.                               (9)
```

This proves the universal result, including all odd prime powers and all
distinct nonzero evaluation sets. The subgroup and `q`-prime restrictions
are unnecessary for the remainder argument.

## Exact diagnostics

Run:

```sh
python3 scripts/probes/astra_clm043_remainder.py
```

The first implementation computes elementary symmetric functions row by
row, including the exact pointwise identity

```text
e_3^2 = 20e_6 + 6(r-4)e_4 + (r-2)(r-3)e_2 + C(r,3),
r = #{a : x_a != 0}.
```

The second implementation directly sums ordered triple pairs by their
intersection cardinality. It checks (2) and (4) for each applicable pair,
and checks the exact centered quartic inequality
`(J+chi(L))^2 <= 4p` for every one-shared-point pair. All comparisons use
integers and squared inequalities, with no floating-point square roots.

The original six frozen cells reproduce:

| (p,n) | I_1 | I_2 | I_3 | R |
|---|---:|---:|---:|---:|
| (97,3) | 0 | 0 | 93 | -3348 |
| (257,4) | 0 | -48 | 1012 | -34704 |
| (641,5) | 90 | -80 | 6370 | -229680 |
| (1297,6) | -1476 | -720 | 25860 | -851904 |
| (1459,6) | -1116 | -216 | 29100 | -999648 |
| (2521,7) | 26082 | -1680 | 88095 | -4049892 |

The probe also checks four non-subgroup evaluation sets and all 581
admissible prime-subgroup cells with `p<=3000`, `3<=n<=7`, and `p>=n^4`.
The endpoint arithmetic is checked through `n=256` and at `n=2^30`.
It passed on 2026-09-04 in about two seconds on the working host.

The finite diagnostics check the implementation and zero corrections.
The proof of (9), using Hasse, supplies uniform coverage. There is no new
estimate on `U`, no Lean axiom audit, and no production-prize closure.

# A cyclotomic root-product operator does not determine punctured values

The reduced [exact-error algebra](astra_mca_exact_error_eliminant-2026-09-05.md)
has a natural operator T satisfying `T^n=1`: on each decoded polynomial it
records the product of its exact error roots. If value multiplication M
were a polynomial in T, a degree-n resultant would annihilate M.

That additional assumption is false on the actual production subgroup.
An explicit received word has two distinct values with the same exact
error-root product. A small F17 control has three distinct values while T
is scalar on its entire decoding algebra. These are obstructions to this
particular operator route, not counterexamples to the desired value cap.
No production scalar-count bound is proved here.

## The valid cyclotomic identity and the missing hypothesis

Use `D=mu_n\{1}` over K, with the characteristic not dividing n. Let B_v
be the reduced algebra whose points are the degree-less-than-k decoded
polynomials f agreeing with v on at least A punctured nodes. Each point
has its exact error set E_f. The root-selector idempotents from the
factorization `Lambda*H=P_D` are

```text
u_x=Lambda'(x)*H(x)/P_D'(x),
u_x(f)=1 if x is in E_f, and 0 otherwise.
```

They are defined on every exact-degree factor of B_v. Define the algebra
element, and its multiplication operator, by

```text
T=product_{x in D} ((1-u_x)+x*u_x).
```

On the point f it has value

```text
tau_f=product_{x in E_f} x = (-1)^degree(Lambda)*Lambda(0).
```

Since every x has order dividing n and the idempotents commute, `T^n=1`.
The minimal polynomial of T therefore divides `Z^n-1`.

Let M denote multiplication by f(1). The following conditions are
equivalent:

1. `M=p(T)` for some polynomial p over K.
2. Whenever two decoded polynomials have equal tau_f, they have equal f(1).

The forward direction is immediate. For the converse, interpolate the
common value on the distinct tau_f in K. There are at most n such points,
so p can be chosen with degree less than n. Under this additional
hypothesis the concrete monic degree-n polynomial

```text
Res_Z(Z^n-1,Y-p(Z)) = product_{zeta in mu_n}(Y-p(zeta))
```

annihilates M. This derivation explains exactly which extra assumption is
needed to transfer the cyclotomic relation from T to the value operator.

Using several multiplicative characters does not distinguish more points.
Every character `chi:mu_n -> K*` has the form `chi(x)=x^j`, and the
corresponding error-root product is `tau_f^j`. The counterexample below
also has equal exact error counts and equal complementary root products.

## Failure on the actual production domain

More generally, suppose n is even, e is positive and even,

```text
e <= (n-2)/2,       N-2e<k,       k<=A=N-e,
```

where N=n-1. Choose e representatives from distinct antipodal pairs
`{x,-x}` other than `{1,-1}`. Call this set E0, put `E1=-E0`, and set

```text
Z=D\(E0 union E1),       h(X)=product_{z in Z}(X-z).
```

The sets E0 and E1 are disjoint, lie in D, and have the same root product
because e is even. Define the received word to be h on E0 and zero at
every other punctured node. Then

```text
f0=0 has exact error set E0,
f1=h has exact error set E1.
```

Both have exactly A agreements. The degree of h is `N-2e<k`, and h(1)
is nonzero. Thus `tau_f0=tau_f1`, whereas `f0(1)!=f1(1)`. These are actual
exact-error points of the reduced algebra. No padded locator or relaxation
is used.

At production, `n=6b-2=2^30`, `e=2b-2`, and `k=3b-1` with
`b=178956971`. All the displayed conditions hold and
`degree h=2b+1=357913943<536870912=k`. A deterministic choice is to take
root exponents `1,...,e` in E0 and add n/2 to obtain E1. This proves
`M not in K[T]` for an explicit family of words on the production domain,
without enumerating that domain or asserting anything about the rest of
the list.

Affine changes make the failure independent of the chosen two values.
For `c!=0` and a polynomial g of degree less than k,

```text
v -> c*v+g,       f -> c*f+g
```

preserve all exact error sets. Under the resulting algebra isomorphism T
is unchanged, while `M -> c*M+g(1)`. Taking g constant and choosing c
allows the two colliding T-points above to have any prescribed distinct
values in K.

## What the domain symmetries actually preserve

Multiplication by a nonidentity root of unity does not permute the fixed
punctured domain: `zeta*D=mu_n\{zeta}`. It moves the omitted point.
Consequently the unpunctured cyclic action is not an action on this fixed
factor algebra in the first place.

Inversion does preserve D and has an exact covariance. Define

```text
(Jf)(X)=X^(k-1)*f(1/X),
(Jv)(x)=x^(k-1)*v(x^(-1)).
```

Then J is an involution on the polynomial code, sends exact error sets to
their inverses, and preserves the value at 1. It identifies `B_v` with
`B_(Jv)`, carrying T to its inverse and intertwining the value operators.
It is an internal action on the same received-word problem if `Jv=v`.
A slightly weaker sufficient condition is `Jv-v=g|D` for some code
polynomial g: then `f -> Jf-g` is internal. Applying J twice shows
`Jg+g=0`; in the even-order setting here the characteristic is odd, so
g(1)=0 and values are again preserved. An arbitrary v need not satisfy
even this condition.

In the existing F17 fixture, the interpolation polynomial of `Jv-v` is

```text
15*X^2+15*X^3+15*X^4+15*X^5,
```

which has degree five, exceeding the code bound `degree<4`. Reciprocity
therefore relates two different decoding algebras; the natural code
translation does not turn it into a symmetry of that fixed word. This
does not exclude accidental symmetries of particular decoded lists.

Finally, an annihilator with coefficients independent of v cannot supply
the desired cap. For every c in K, the constant word c has exactly the
one decoded polynomial c when `A>=k`. A polynomial annihilating M for all
words must therefore vanish at every c. Over a finite field of size q it
has degree at least q unless it is zero; `Y^q-Y` attains that degree.
At production q>n. A successful degree-n identity must depend on the
received word and use more information than the root-product operator.

## Exact checks and their limits

Run `python3 scripts/probes/astra_mca_value_operator_check.py`. It enumerates
all `17^4` degree-less-than-four polynomials once and tests four fixed words
on `mu_8\{1}` at agreement A=5: the existing fixture, its reciprocal, its
translate by 3, and the antipodal construction.

For the antipodal word, `v(2)=7`, `v(4)=15`, and other values zero. Its
entire list is

```text
0,       4+4X+X^2+X^3,       5+X+6X^2+14X^3.
```

Their values at 1 are `0,10,9`; every exact error-root product is 8.
Thus T is scalar, while M has minimal polynomial `Y*(Y-10)*(Y-9)`.
The checker also verifies the valid conditional resultant on the existing
fixture, exact error-set covariance, the failed fixed-word reciprocity
condition, and the production construction's degree arithmetic.
No field-independent value identity or production value bound is inferred.

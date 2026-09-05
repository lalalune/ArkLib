# Contact vanishing does not force higher local tail multiplicity

At the exact binding flag `(r,v,z)=(10,37,2317)`, there is an irreducible
regular factor with a polynomial solution where the first two relevant
tails meet transversely. Its first-tail component has multiplicity one and
the next tail has a simple zero on that component. Every higher tail still
vanishes at the selected solution.

This rules out a uniform improvement obtained by claiming that polynomial
solutions or contact vanishing force local multiplicity at least two. It
does **not** show simultaneous saturation of the rational and moving degree
budgets, construct a large selected family, or supply a factor of the actual
universal interpolation kernels. A correlation that uses those stronger
hypotheses remains open.

The source audit uses official companion commit
[`032154395c51fd6f77715a7f42d9a987ab9fb48a`](https://github.com/proximity-prize/proximity-prize/commit/032154395c51fd6f77715a7f42d9a987ab9fb48a).
The polynomial and finite recurrence calculations are independently
reproducible with
[`astra_c2_geometry_flag_witness.py`](../../scripts/probes/astra_c2_geometry_flag_witness.py).
The general local-algebra argument below is a mathematical proof note, not a
compiled Lean formalization. An independent agent reviewed the irreducibility,
derivation, and tail-normalization arguments against the source.

## The factor and its regular solution

Work in characteristic `p=2130706433`, set `w=131071`, and write

```
A = Y-X,                 B = R-1,
F = B-X*A-Z+A^47+B^10+Z^2364.
```

For `gamma=0` and `f(X)=X`, the specialization `Y=f(X), R=f'(X), Z=gamma`
makes `A=B=Z=0`. Thus `F` specializes to zero and

```
H = partial_R F = 1+10*B^9
```

specializes to one. This is a `RegularSolution`, not a singular solution.
The support weights are exactly

```
R weight = 10,  Y+R weight = 47,  Y+R+Z weight = 2364,
contact weight for (1,w,w-1,0) = 47*w = 6160337.
```

Consequently the raw flag is exactly `(10,37,2317)`. The factor belongs to
the source's global coefficient box for every `D>6160337`, `L>=2364`, and
`s>=10`, including the published ordinary-factor caps.

The change from `(X,Y,R,Z)` to `(X,A,B,Z)` is a polynomial-ring automorphism.
In the new coordinates `F` is primitive linear in `X`: its coefficient is
`-A`, and its constant coefficient is not divisible by `A`. Gauss's lemma
therefore proves irreducibility over `K[X,Y,R,Z]`.

There is also geometric irreducibility after passing to
`Omega=algebraicClosure(K(X))`, which is needed for the actual surface stage.
In `Omega(Z)[A,B]`, give `A` weight 10 and `B` weight 47. The highest weighted
part is `A^47+B^10`; every other term has smaller weight. This binomial is
irreducible because `gcd(47,10)=1`. For an explicit argument, choose
`c in Omega` with `c^10=-1` and substitute `A=t^10, B=c*t^47`.
Division by the monic polynomial `A^47+B^10` leaves a remainder with
`A` degree below 47. Its distinct monomials have distinct powers of `t`, so
the substitution kernel is exactly the binomial ideal, which is prime.
A factorization of `F` would factor this highest weighted part; one factor
would consequently be a unit in `Omega(Z)[A,B]`. Primitivity, from the monic
coefficient of `A^47`, then gives irreducibility in `Omega[A,B,Z]`.

For the singleton selected family `Gamma={0}`, choose received values
`u0(i)=x_i` at the distinct production nodes and, for example, `u1(i)=0`.
The selected solution agrees at every node. The exact source definition of
`NoLargeSelectedPencil` bounds the size of each filtered subfamily by `e+1`;
every such filtered singleton has size at most one. Thus this hypothesis is
satisfied for either the published or candidate error cap. This choice does
not assert any global farness or universal-kernel provenance from the full
prize argument.

The subsequent [contact-variation example](astra_contact_variation-2026-09-05.md)
has a one-dimensional full source kernel and a genuine MCA-bad seed while
retaining transverse tails. That different example has R degree one. It
cannot be combined with this example to claim a witness satisfying both
full-kernel provenance and the binding C2 flag.

## Linearizing the actual contact derivation

First work over `K(X)`, where differentiation with respect to `X` is defined.
Do not extend this derivation to the algebraic closure: in positive
characteristic it need not extend through purely inseparable extensions.
Only the resulting local equations and gradients are later base-changed
to `Omega`.

Since `H=1` at the solution, the surface is smooth there and its completed
local ring is `K(X)[[A,Z]]`. The implicit equation gives

```
B = X*A+Z mod (A,Z)^2.
```

The source contact derivation satisfies `D(X)=1`, `D(Y)=R`, `D(Z)=0`, and
`D(R)=polyG/H`. Hence

```
D(A)=B,
D(B)=(A+X*B-47*A^46*B)/H.
```

Both right-hand sides belong to `I=(A,Z)`. Therefore `D` preserves `I` and
`I^2`; high-order terms cannot return to linear order after repeated
differentiation. Modulo `I^2` the induced derivation is exactly

```
D(A)=X*A+Z,  D(Z)=0,  D(X)=1.
```

Write `D^n(A)=a_n(X)*A+b_n(X)*Z mod I^2`. The initial conditions are

```
a_0=1, b_0=0, a_1=X, b_1=1.
```

Applying `D^n` to `D(A)=X*A+Z` and using Leibniz's rule, `D^2(X)=0`, and
`D(Z)=0` yields, for `n>=1`,

```
a_(n+1)=X*a_n+n*a_(n-1),
b_(n+1)=X*b_n+n*b_(n-1).
```

This proof uses no factorial denominators. Set
`Delta_n=a_n*b_(n+1)-a_(n+1)*b_n`. The recurrence gives

```
Delta_0=1,   Delta_n=-n*Delta_(n-1),
Delta_n=(-1)^n*n!.
```

At `n=w+1=131072`, all factors in `n!` are nonzero in characteristic `p`,
so `Delta_n` is nonzero. In particular the linear forms for `D^n(Y)` and
`D^(n+1)(Y)` are independent: for `n>=2`, `Y=X+A` gives
`D^n(Y)=D^n(A)`.

## Bridge to the source's first and second tails

The exact definitions are `RCN086.globalTailCut_eq` in
`PackedLegacyCore2.lean:18631` and `iterate_Y_eq_numerator` in
`PackedLegacyCore1.lean:318`. Together they give, on the regular surface,

```
globalTailCut(d) = (-X)^d * numerator_d
                = (-X)^d * H^(2d) * D^d(Y).
```

The coefficient embedding makes `X` transcendental and nonzero, and `H`
has value one at the selected point. The displayed multiplier is therefore
a local unit. Since `D^d(Y)` vanishes at the point for every `d>=2`,
multiplication by this unit merely rescales its linear term.

Thus `globalTailCut(w+1)` has a nonzero linear term on the smooth surface,
and `globalTailCut(w+2)` has an independent linear term. The first tail
defines a smooth reduced curve at the point. Its unique local component
has divisor multiplicity one; the second tail restricts to a uniformizer,
with order exactly one. In particular the first tail is proper on the
surface and the second tail is proper on that component: this realizes
the low-multiplicity, delay-one branch, not the tangent/all-tails component
branch. Nevertheless every tail vanishes at the selected point, because
the selected polynomial is `f(X)=X`.

## What a substantial improvement still needs

`ResidualStage` retains support, regular polynomial solutions, an irreducible
surface component, and `NoLargeSelectedPencil`. It does not retain the
interpolation-ideal multiplicity of a kernel element. In
`LocatorHybridRealizeC2.realizationC2`, the node/agreement/coefficient-box
arguments enter the proper-first-tail provider through `htangent`.
The non-tangent moving count does not consume the large agreement count.
The witness above demonstrates that those discarded global conditions
cannot be replaced by a blanket local transversality failure.

The pole terms also do not count a union of sets. The local estimate for a
delayed tail has the form

```
pole(tail/H^k) <= pole(C)+k*pole(N)+k*movingPoleTarget.
```

Orders add under multiplication, even when the poles occur at the same
places. Merely noting that the rational and moving terms share a pole does
not permit a subtraction. A useful subtraction must prove forced
cancellation, extra zeros outside the selected set, an averaged
multiplicity gain, or a relation supplied by the original interpolation
kernels and large agreement family.

With the other terms frozen at the improved
[m166 T replay](astra_t_cutoff-2026-09-04.md), the binding singleton
must fall to `266264875801744582`. If the rational contribution stays fixed,
a sufficient moving-budget target is

```
sum movingCost <= 670371338283
```

instead of `801126293887`: a decrease of `130754955604`, or **16.3214%**.
No such inequality, nor simultaneous saturation of both existing budgets
by a large actual selected family, is established here. The precise open
step is a global deficit of this size for the admissible large family;
the current local multiplicity argument cannot provide it uniformly.

The [colon and Hermite follow-up](astra_colon_2026-09-04.md) begins to retain
the interpolation constraints on a quotient by the common factor. It proves
a graded kernel upper bound, but that estimate still exceeds the available
nullity lower bound by several orders of magnitude at this flag. The remaining
comparison must use more information about the actual source kernel or the
admissible large family.

## Reproduction

```sh
python3 scripts/probes/astra_c2_geometry_flag_witness.py
```

The probe passed in the actual characteristic. It verifies the polynomial
specialization, regular derivative, triangular coordinate change, exact
support and contact weights, and both recurrence descriptions through
`n=19`. It evaluates the second-order recurrence at `X=0` through the
production index `131072`, independently compares the determinant with the
factorial product, and obtains the nonzero residue **1690593**.

Evaluating the determinant polynomial at `X=0` is only a finite arithmetic
check. The source tails are kept over `K(X)`, where their factor `(-X)^d`
is a unit; the probe does not specialize those tails at zero. The general
irreducibility and local-transversality argument has not been formalized in
Lean, and the probe is not a certificate of a new prize score.

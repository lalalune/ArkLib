# The four-cubic coincidence pattern forces a common direction at covered points

Allowing four new, independently chosen pairs of code polynomials does not
create several ordinary cancellation directions at one covered coordinate
while retaining the current construction's common roots and five full triple
fibers. The coincidence constraints force all four local pairs onto one affine
line. This is an obstruction to that proposed improvement, not a bound for
arbitrary received lines or different support patterns.

Use the production parameters and four normalized cubics `W_0=0,W_1,W_2,W_3`
from the [construction](astra_mca_four_cubic-2026-09-06.md), with `n=8s`,
`k=4s`, and `s=2^27`. Take two tuples of polynomials `p_i,q_i` of degree less
than `k`. Subtract `p_0,q_0` from every tuple so that index zero is zero; this
preserves all pairwise equality constraints. Suppose:

- Both tuples vanish on the same `r` chosen domain points, all outside fibers
  `0,1,3,6,7`, where `r<=s-1`.
- On every point of those five fibers, the tuples satisfy respectively the
  triple equalities `{0,1,2}`, `{0,1,3}`, `{0,2,3}`, `{1,2,3}`, `{1,2,3}`.
- On a set of `c>s-r-1` further non-root points in fibers `2,4,5`, respectively,
  they satisfy the pair equalities `{0,3}`, `{0,2}`, `{0,1}`.

Let `B` be the monic product over the chosen roots. Then there are polynomials
`a,b` of degree at most `s-r-1` such that

```text
p_i-p_0 = B(X) a(X) W_i(X^s),
q_i-q_0 = B(X) b(X) W_i(X^s).
```

For the current allocation, `r=s-2`, `c=3s/2`, so `a,b` are linear or constant.
At any coordinate `x`, the four pairs consequently have the form

```text
(p_0(x),q_0(x)) + B(x) W_i(x^s) (a(x),b(x)).
```

If the received pair equals one of them, every nonzero residual is proportional
to `(a(x),b(x))`. There is at most one finite ordinary cancellation scalar at
that coordinate. Counting different nonowners as independent directions would
therefore be incorrect for this support geometry.

## Exact coefficient-space certificate

For three degree-at-most-three polynomials, the five triple fibers impose ten
linear equations on their twelve coefficients. The
[checker](../../scripts/probes/astra_mca_four_cubic_module_check.py) verifies
rank ten over the production field and gives a basis `W,V` for the kernel.
The analogous matrix for degree at most two has rank nine on nine coefficients,
so that kernel is zero. It also checks

```text
W_3(eta^2)=W_2(eta^4)=W_1(eta^5)=0,
V_3(eta^2),V_2(eta^4),V_1(eta^5) are all nonzero.
```

Thus these computations concern the actual eight-point domain, rather than
abstract partitions with unknown polynomial realizability.

## Lifting the coefficient calculation

Consider either divided tuple `R_i=(p_i-p_0)/B`. Each component has degree at
most `4s-r-1`. Decompose each polynomial uniquely by exponents modulo `s`:

```text
R_i(X) = sum_(0<=t<s) X^t R_(i,t)(X^s).
```

Each `R_(i,t)` has degree at most three. For `t>s-r-1`, it has degree at most
two. On a full fiber `X^s=eta^j`, a required relation among the `R_i` vanishes
at all `s` distinct points. Its remainder modulo `X^s-eta^j` has degree below
`s`, so that remainder is zero. This gives the same ten base equations for
every residue `t`.

The coefficient-space certificate implies that each residue tuple is a
linear combination of `W,V`; the higher residues are zero by the degree-two
rank certificate. Collecting coefficients gives

```text
R(X) = a(X) W(X^s) + d(X) V(X^s),
deg a, deg d <= s-r-1.
```

At each of the `c` covered pair points, the required component of `W` is zero
and that of `V` is nonzero. Hence `d` has all these points as roots. Since
`c>deg d`, it is the zero polynomial. Apply the identical argument to the
second tuple to obtain the displayed representation with multiplier `b`.

```sh
python3 scripts/probes/astra_mca_four_cubic_module_check.py
```

The [receipt](../../scripts/probes/receipts/astra_four_cubic_20260906/module.json)
contains both basis vectors, all ranks and pivot columns, the three nonzero
pair residuals, and the production degree comparison. The general lifting and
root-bound steps above are written mathematics, not a completed Lean proof.

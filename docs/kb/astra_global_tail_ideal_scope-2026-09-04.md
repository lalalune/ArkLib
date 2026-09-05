# Exact all-tail ideal equality: scope check

Status: a written algebraic proof with a reproducible finite arithmetic check;
not a Lean theorem and not a bound for the binding C2 flag `(10,37,2317)`.
The example below lies outside C2 and fails the required large agreement.

## The exact equality

Let `K` have characteristic `p`, let `P,Q ∈ K[Z]`, and put

```
F = R - X(Y-P(Z)) - Q(Z),       A = Y-P(Z).
```

The regular contact surface has coordinate ring `K(X)[A,Z]`, with `H=∂RF=1`
and derivation `DX=1`, `DZ=0`, `DA=XA+Q`. Work over `K(X)`; extending this
derivation to its entire algebraic closure is unnecessary and generally invalid
in positive characteristic.

For `n≥1`, write `DⁿY=aₙA+bₙQ`. The coefficient sequences have initial values
`(a₀,b₀)=(1,0)`, `(a₁,b₁)=(X,1)` and satisfy

```
qₙ₊₁ = X qₙ + n qₙ₋₁,
aₙ bₙ₊₁ - aₙ₊₁ bₙ = (-1)ⁿ n!.
```

The recurrence follows by applying `Dⁿ` to `DA=XA+Q`; for `n≥1`,
`DⁿA=DⁿY`. The determinant identity follows by substitution and induction.
Consequently, for every `1≤n<p`, the two adjacent derivatives generate exactly
`(A,Q)`. This ideal is `D`-stable, since `DA=XA+Q` and `DQ=0`. Thus

```
(DⁿY,Dⁿ⁺¹Y) = (DʲY : j≥n) = (A,Q).
```

The official normalization gives `tail_j=(-X)^j H^(2j) DʲY`; here `H=1`
and `X` is a unit in `K(X)`. The same equality therefore holds for the tail
ideals. If `Q` is squarefree of degree `N` and splits over `K`, their common
zero scheme consists of precisely `N` reduced points. Requiring every later
tail removes no points from the actual first-two-tail intersection.

For the finite check, take `p=2130706433`, `n=w+1=131072`, `P=Z²`, and
`Q=∏_{γ=0}^{2363}(Z-γ)`. The script independently constructs `Q`, checks all
2364 roots and their nonzero derivatives, and checks the adjacent determinant
at four values of `X`. The determinant is `1690593` modulo `p`. These checks
support the displayed formulas; the universal ideal equality follows from the
written recurrence proof, not from testing four values.

## Why this does not settle the C2 question

This factor has raw flag `(r,v,z)=(1,0,2363)`, outside the C2 branch
`r≥3, v≥2`. Its selected solutions are the constants `fγ=γ²`. They obey the
no-large-pencil condition with cap 2: an affine polynomial pencil can equal
`γ²` for at most two distinct values of `γ`. But at each evaluation node the
received affine line also agrees with at most two selected solutions. Hence
the full agreement premise requires `N a≤2n_nodes`; it fails at
`N=2364, a=181353, n_nodes=262144`.

The equality only shows that later tails and `D`-stability alone do not force a
strict decrease from the *actual first-two-tail intersection length* in every
regular factor. It says nothing against an improvement using the C2 flag,
large agreement, or universal interpolation-kernel provenance. It also does
not show saturation of the published mixed-volume allowance.

## The remaining global input

The official `RCN139.global_polynomiality_of_all_tails` already reconstructs
a polynomial of degree at most `w` from the finite tail range `w<j≤D`, under
the coefficient-box hypothesis and `D<p`. Repeating that reconstruction is
not a new point-count estimate. Source: the companion's unchanged
`PackedLegacyCore1.lean:2813` at snapshot
`032154395c51fd6f77715a7f42d9a987ab9fb48a`.

Selected polynomial graphs have codimension two in the three-dimensional
contact surface over `K`, and become points on its generic surface over
`K(X)`. Classical invariant-hypersurface statements address codimension one.
Moreover `Z` is already a first integral, while every `p`th power is a
derivation constant. Bonnet's positive-characteristic theorem controls a
quotient of algebraic solutions by rational first integrals, rather than the
number of these selected points. [Primary source](https://arxiv.org/abs/math/0602338).
A useful application here still needs a new bound for the codimension-two
selected locus using the C2 support and interpolation provenance, or a
transverse relation independent of these existing first integrals.

Reproduce: `python3 scripts/probes/astra_global_tail_ideal_check.py`.

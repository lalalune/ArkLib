# Four deletions give an analytic MCA upper bound

**Status:** written proof with exact finite controls; independent review and
Lean formalization remain open. This gives the production upper bound
`mcaDeltaStar <= 357913942/2^30` without a production collision scan. It is
one Hamming step **weaker** than the existing
[computational upper bound](astra_mca_production_count-2026-09-05.md)
`357913941/2^30`. It does not improve the strongest numerical bound,
prove a matching lower bound, or solve a grand prize challenge.

Thirty-one [supporting Lean theorems](astra_mca_polynomial_basis-2026-09-05.md)
now construct the complete polynomial basis from root-domain data at the
production dimensions: the balanced partition, interpolation, determinant
and both deletion pairs. The code-domain instantiation, actual MCA witnesses
and full threshold consequence below are not yet assembled in Lean.

The useful change is structural: two further deletions permit multiplication
of each generator by X. Evaluation at different coordinates then gives
different projective linear functionals automatically. A polynomial root
bound chooses two combinations preserving all their distinctions.

## Statement

Let K be a finite field containing an element omega of order `n=4^r`,
where `r>=2`. Let `Omega={omega^e : 0<=e<n}`, `k=n/2`, and
`C=RS[K,Omega,k]`, with polynomial degrees strictly less than k. Put

```text
a=(n-1)/3,  s=2a,  M=n+4,  delta_plus=(a+1)/n=(n+2)/(3n).
```

If `|K| > 3*binomial(M,2)`, there exists a received pair with at least M
distinct finite scalars satisfying the actual MCA event at agreement s.
Consequently `epsMCA(C,delta_plus) >= M/|K|`.

The construction and its no-joint-explanation argument are given below.
Existence of a primitive n-th root implies odd characteristic. Every
division by 2 or `1-i` in the proof is therefore legitimate.

## 1. An explicit initial determinant

Set `m=n/4`, `i=omega^m`, and `T=X^m`. Thus `i^2=-1`. Assign the whole
quarters `T=1,i,-1` to the pair regions AB, AC, BC, respectively. Split
the fourth quarter `T=-i` arbitrarily into pieces of sizes

```text
(m-1)/3, (m-1)/3, (m+2)/3,
```

assigned to AB, AC, BC. These are integers because `m=1 mod 3`. The
resulting region sizes are `a,a,a+1`.

Let H have degree less than m and take values `i,i/2,0` on these three
pieces of the fourth quarter. Interpolation at its m distinct points
gives H. Define

```text
J=T+i,  e_A=1+i,  e_B=-2,
P_0=(T-i)/(1-i),  Q_0=(1-T)/(1-i),

lambda = (0, (T-1)*(P_0+e_A*H), -(T-i)*(Q_0+e_B*H)),
kappa  = (0, (T-1)*e_A*J,       -(T-i)*e_B*J).
```

Both triples have degree at most `2m=k`. In each pair region the
designated components agree in both triples. For the fourth quarter,
kappa is zero, while the two nonzero-index lambda components are
`-2-2iH` and `-2-4iH`; the three chosen values of H give exactly the
required equalities. The first three quarters follow by substitution.

Most importantly, there is the polynomial identity

```text
lambda_B*kappa_C - kappa_B*lambda_C
  = (T-1)*(T-i)*(T+i)*(e_A*Q_0-e_B*P_0)
  = (T-1)*(T-i)*(T+i)*(T+1)
  = X^n-1.
```

This is a nonzero polynomial with a simple root at every domain point.
No counting of residual directions enters this identity. The same
initial formulas appear in the
[compact evaluator](astra_mca_twogen_lift_eval-2026-09-04.md).

## 2. Apply the two-point deletion argument twice

We use the following form of the
[deletion lemma](astra_mca_two_generator_bridge-2026-09-04.md), which
requires only degree and determinant identities, not a module-basis theorem.

Suppose two triples `(0,F_1,G_1),(0,F_2,G_2)` have degree at most D,
obey the pair-region equalities, and satisfy

```text
F_1*G_2-F_2*G_1 = c*A*B*C,  c!=0,
deg A+deg B+deg C=2D,  deg A+deg B>D,
```

where A, B, C are the monic locators of nonempty disjoint simple pair
regions AB, AC, BC. Write `W_j=(F_j-G_j)/C`.

At any A or B root, the row `(W_1,W_2)` is nonzero. Otherwise all four
F/G values would vanish there, giving the determinant a double root.
Some A root xi and B root eta have nonproportional W rows: if every
cross-pair had the same direction, one nonzero constant combination W
would vanish on all `deg A+deg B` roots. But

```text
deg W <= D-deg C < deg A+deg B,
```

so W would be identically zero. The same combination satisfies `F=G`,
and AB divides F. Since `deg A+deg B>D`, both F and G would vanish
identically, contradicting the nonzero determinant of the original pair.

Choose one constant combination killing the row at xi and another
killing it at eta. The combinations are independent, and both F and G
of each combination vanish at its chosen point. Divide the respective
triples by `X-xi` and `X-eta`. Their degree is at most `D-1`, their
new determinant is a nonzero constant times

```text
(A/(X-xi))*(B/(X-eta))*C,
```

and all remaining pair equalities persist. Move xi and eta to a
private-A region, where the received value will be zero.

For the initial triples, `D=k` and the degrees are `a,a,a+1`.
Here `2a>k`. After one deletion pair, they are `a-1,a-1,a+1`,
with `D=k-1`. Since `a>=5`,

```text
2a-2 > k-1.
```

Thus the argument applies a second time. It produces triples U,V of
degree at most `k-2`, four private-A points I, and pair regions of sizes
`a-2,a-2,a+1`. Their determinant is a nonzero constant times the monic
locator of the remaining `n-4` points.

This uses existentially chosen deletion points. The finite checker uses
the specific exponent pairs `(0,1)` and `(3,7)` and checks both required
row determinants directly; those fixed choices are not needed by the
general proof.

## 3. Four generators separate every absent-core slot

Take the four triples `U,V,XU,XV`. Every component has degree less
than k. They are linearly independent over K: an identity between them
would give a rational-function dependence of U and V, whose determinant
is nonzero.

Use the designated common component as the received value at each pair
point, and component A, which is zero, at each private point. This rule
defines received values for every linear combination of the four triples.
The joint-agreement cores are

```text
S_A=AB union AC union I,  size 2a,
S_B=AB union BC,          size 2a-1,
S_C=AC union BC,          size 2a-1.
```

An absent-core slot is `(j,x)` with `x` outside `S_j`. There are
`(n-4)+2*4=n+4=M` such slots. Each gives a linear functional ell on
the four coefficients by subtracting component j from the received
value. Its coefficient vector has the form

```text
(b,c,x*b,x*c).
```

Here `(b,c)` is nonzero. At an ordinary point, a zero row would make
all F/G values of U,V vanish, contradicting the simple root of their
determinant. At a private point the determinant is nonzero, so its two
absent-slot rows are both nonzero and nonproportional.

Two slots at different coordinates x,y cannot have proportional
four-coordinate vectors: proportionality in the first two coordinates,
followed by the last two, forces `x=y`. At a common private coordinate,
nonproportionality already holds in the first two coordinates. Thus all
M functionals are pairwise nonproportional.

## 4. A finite-field projection preserves all M directions

For each slot i, let

```text
G_i(Z)=ell_i(1,Z,Z^2,Z^3).
```

These are nonzero polynomials of degree at most three. Their product
has degree at most `3M`, so choose `t in K` with all `G_i(t)!=0`.
This is possible because `|K|>3*binomial(M,2)>=3M` for the present M.

For every pair `i<j`, the polynomial

```text
H_ij(Z)=G_j(t)*G_i(Z)-G_i(t)*G_j(Z)
```

is nonzero and has degree at most three. Otherwise the coefficient
vectors of the two functionals would be proportional. The product of
these polynomials has degree at most `3*binomial(M,2)`. Choose `s_0`
outside its root set.

Let f be the combination of `U,V,XU,XV` with coefficients
`(1,s_0,s_0^2,s_0^3)`, and let g use `(1,t,t^2,t^3)`. All residual
g values are nonzero, and the M scalars

```text
gamma_i = -ell_i(f)/ell_i(g) = -G_i(s_0)/G_i(t)
```

are finite and pairwise distinct. The proof selects parameters by
existence; it does not compute them at production length.

## 5. Each scalar satisfies the full MCA event

Let `(u0,u1)` be the received pair obtained from f,g by the owner rule.
For the slot `(j,x)`, the codeword `f_j+gamma*g_j` agrees with
`u0+gamma*u1` on `S_j` and at x. Choose an exact support consisting
of any `s-1=2a-1` points of `S_j` and x. Since `n>=16`,

```text
2a-1 >= k.
```

If some codeword pair jointly explained `(u0,u1)` on this support,
its two polynomials would equal `f_j,g_j` by polynomial uniqueness on
the at least k core points. At x, the g residual is nonzero, a
contradiction. This is the same-support no-joint clause in
[`mcaEvent`](../../ArkLib/Data/CodingTheory/ProximityGap/Errors.lean),
not only closeness of the scalar combination. All M distinct scalars
are therefore counted in the event, proving the statement.

## Production consequence and precise limitation

For the production field and `n=2^30`,

```text
P=365375409332725729550921208179070755120141565953,
P=n*(2^128+192)+1,
M=1073741828,
3*binomial(M,2)=1729382268184559634 < P,
M*2^128-P=1361129467683753853853498429520914415615 > 0.
```

The certified field/root data are recorded in
[`_PrizeShapePrimeP30.lean`](../../ArkLib/Data/CodingTheory/ProximityGap/Frontier/_PrizeShapePrimeP30.lean).
Therefore `epsMCA(C,357913942/2^30)>2^-128`. Monotonicity and the
supremum definition, as exposed by
[`mcaDeltaStar_le_of_bad`](../../ArkLib/Data/CodingTheory/ProximityGap/MCAThresholdLedger.lean),
give the stated weak upper bound, not a strict inequality for the supremum.

The stronger previously computed bound is `357913941/2^30`. Four
private points leave only `2n-4` core memberships, fewer than the `2n-2`
needed for three cores of size `2a`. This explains the lost agreement
point in this construction; it is not an optimality theorem for all MCA
constructions. The universal predecessor estimate and all broader prize
obligations remain open.

## Reproduction

Run from the repository root:

```sh
python3 scripts/probes/astra_mca_four_delete_check.py
```

The checker reconstructs dense polynomials over the actual production
prime at `n=16,64,256`. It checks the initial determinant, both deletion
determinants, degrees, core equalities, every pair of projective residual
rows, and explicit projection parameters. It obtains respectively
`20,68,260` distinct finite scalars with agreement targets `10,42,170`.
All 348 supports pass a separate Vandermonde parity check showing that
u1 alone has no degree-less-than-k explanation on k core points plus
the absent point. The production cell checks constant-size arithmetic
only. Small controls do not replace the written all-size argument.

No new Lean theorem, full production polynomial enumeration, production
projection parameters, independent proof review, or prize solution is
claimed by this receipt.

Documentation integrity, strict KB lint, Python syntax, and staged whitespace
checks pass. The broader KB generated-file check reports existing stale
`declarations.json` and `dedup-report.md`; its Lean inputs, generator scripts,
and generated files are unchanged from the parent commit. No full Lean build
was run for this documentation/probe change.

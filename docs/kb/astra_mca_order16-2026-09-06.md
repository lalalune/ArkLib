# Order-sixteen degree-seven sources lower the production unsafe radius

For the certified production field, domain size `n=2^30`, and Reed–Solomon
dimension `k=n/2`, the construction below has at least `n+4` distinct original
MCA-bad scalars at radius

```text
delta = 313174699/1073741824 = 7/24 + 1/(3n).
epsMCA(C,delta) >= (n+4)/P > 2^-128.
```

This improves the [four-cubic construction](astra_mca_four_cubic-2026-09-06.md)
from approximately 31.25% to 29.1666667%. It is a written proof with exact
production-field certificates and two independently implemented dense
controls. It is not a Lean-checked numerical production theorem, a complete
bad-scalar census, an exact threshold, or a solution to either grand challenge.
The [official MCA challenge](https://proximityprize.org/) asks for the optimal
threshold, including other specified constant rates and smooth domains.

Related work: [Gao, Yang, Xu, and Kan (2026)](https://arxiv.org/html/2607.10572v1)
construct MCA lower bounds from list-decoding counterexamples using a common
agreement set and an additional coordinate. Their Reed–Solomon construction
permits changing one evaluation point. The present certificate checks a union
of ordinary and fresh directions on the fixed certified subgroup. The shared
core-plus-one mechanism has this literature precedent; novelty of the precise
bound or construction has not been established by a complete literature review.

## Explicit production-field seed

Use the [certified field and generator](../../ArkLib/Data/CodingTheory/ProximityGap/Frontier/_PrizeShapePrimeP30.lean):

```text
P = 365375409332725729550921208179070755120141565953
g = 303645430271030343624574566109998498685964493478
n = 2^30, k = n/2, s = n/16 = 67108864
eta = g^s, t = (s-4)/6 = 11184810
```

Here `g` has order `n`, and `eta` has order sixteen. For a set of exponents
`E`, write `R_E(Y)=product_(j in E)(Y-eta^j)`. Set

```text
A = {0,5,13}, B = {1,8,9}, C = {3,11,12}, D = {4,7,15}
W0 = 0
W1 = R_(A union B union {6})
H  = R_(A union C)
K  = R_(B union C union {10})
```

Let `L` be the explicit linear polynomial whose values at `eta^4` and `eta^7`
are respectively `W1(eta^4)/H(eta^4)` and `W1(eta^7)/H(eta^7)`. More precisely,
for these two distinct arguments `a,b` and target values `v_a,v_b`, use
`L(Y)=v_a+(v_b-v_a)(Y-a)/(b-a)`. Define

```text
W2 = H L
W3 = [W1(eta^4)/K(eta^4)] K.
```

All denominators are nonzero. The primary checker expands these definitions
over the actual production field and verifies the full partition table:

| Fiber exponents | Equality classes of the four values |
|---|---|
| 0, 5, 13 | {0,1,2}, {3} |
| 1, 8, 9 | {0,1,3}, {2} |
| 3, 11, 12 | {0,2,3}, {1} |
| 4, 7, 15 | {0}, {1,2,3} |
| 2 | {0}, {1}, {2}, {3} |
| 6 | {0,1}, {2}, {3} |
| 10 | {0,3}, {1,2} |
| 14 | {0}, {1}, {2,3} |

The three nonzero sources and all six differences have degree seven, and
`gcd(W1,W2,W3)=1`. In contrast to the earlier cubic example, two differences
have only six roots in this sixteen-point subgroup; the proof does not require
all difference roots to lie in the domain.

The independent checker reconstructs the same normalized seed from scratch
by solving the 24 homogeneous coefficient equations imposed by the twelve
triple fibers. That system has rank 23 over the production field. Normalizing
the leading coefficient of `W1` to one recovers exactly the displayed seed.
This independent reconstruction uses no primary-checker arithmetic helpers.

## Common roots, code polynomials, and received word

Fiber `j` contains the `s` distinct points `x=g^(j+16a)`, `0<=a<s`, so
`x^s=eta^j`. Choose the first `4t+2` points of fiber 2, and the first `t`
points of each of fibers 6 and 14, as the common-root set `Z`. These disjoint
prefixes have size `6t+2=s-2`. Define actual polynomials

```text
Q(X) = product_(z in Z)(X-z)
p_i(X) = Q(X) W_i(X^s)
q_i(X) = X p_i(X).
```

Their degrees are at most `(s-2)+7s=k-2` and `k-1`, respectively. Thus all
source pairs belong to the full production Reed–Solomon code.

At common roots, set the received pair to `(0,0)`. At covered non-root nodes,
set it to the common value `(p_i(x),q_i(x))` of the indicated owners:

| Fibers | Common-root prefix | Covered remaining nodes | Uncovered nodes |
|---|---|---|---|
| Twelve triple fibers | none | whole fiber, owners in its triple | none |
| 2 | `4t+2` | none | `s-(4t+2)=2t+2` |
| 6 | `t` | all `s-t`, owners {0,1} | none |
| 10 | none | first half owners {0,3}, second half {1,2} | none |
| 14 | `t` | all `s-t`, owners {2,3} | none |

Each source owns nine full triple fibers, one of the remaining pair blocks
of size `s-t`, and half of fiber 10. Including the common roots, each exact
joint core therefore has size

```text
Acore = 9s + (s-t) + s/2 + (s-2)
      = 68t+44 = 760567124 >= k.
```

The uncovered values will be chosen off every source pair, so they do not
enlarge these joint cores.

## An over-budget union of finite bad scalars

Every covered non-root point has at least one nonowner. Since `q_i(x)=x p_i(x)`,
its nonzero residual cancels at `gamma=-1/x`. Nonzero domain points give
distinct such scalars. The ordinary count is

```text
12s + 2(s-t) + s = 15s-2t = 984263340.
```

At an uncovered point in fiber 2, the four local values `z_i=p_i(x)` are
distinct. Maintain a set `Gamma` containing all ordinary scalars and all fresh
scalars chosen so far. Choose `a` outside these four local values and choose
`b` avoiding:

* the four values `xz_i`, to keep denominators nonzero;
* `xa`, to make the four new ratios mutually distinct;
* `xz_i+(z_i-a)/gamma` for each nonzero `gamma` in `Gamma` and each `i`.

At most `4(|Gamma|+1)+1` field elements are forbidden. Throughout the
construction `|Gamma|<=n+4`, and `P>4(n+5)+1`; also `P>4` permits the initial
choice of `a`. Therefore a permissible pair exists at every point. Set the
received pair to `(a,b)`. The four scalars

```text
gamma_i = (z_i-a)/(b-xz_i)
```

are finite, nonzero, mutually distinct, and outside `Gamma`. The equation
`a+gamma_i b=z_i+gamma_i xz_i` gives the required cancellation. Off-diagonal
ratio equality would imply `(z_i-z_j)(b-xa)=0`, which was excluded. These
`2t+2` uncovered nodes supply `8t+8=89478488` fresh scalars. In total,

```text
Dcount = (15s-2t) + 4(2t+2) = 16s+4 = n+4 = 1073741828.
```

This finite avoidance argument proves production-sized existence without
expanding a billion-coordinate received word or assuming random choices work.

## Original same-support MCA event and numerical bound

For each counted scalar, take its source `i` and origin `x`. Its core is an
`Acore`-point set on which both received components equal `p_i,q_i`. The scalar
projection also agrees at `x`, so the codeword `p_i+gamma q_i` agrees on the
same support consisting of that core and `x`, with size `Acore+1=760567125`.

A joint pair of degree less than `k` explaining this same support would agree
with `p_i,q_i` at `Acore>=k` distinct core points. The polynomial root bound
forces equality of both polynomials. Their nonzero residual at `x` contradicts
joint agreement there. This excludes all competing code pairs in the full
code, not merely the four selected source pairs.

The support radius and strict security margin are

```text
delta = (n-Acore-1)/n = 313174699/n = 7/24+1/(3n)
(n+4)2^128-P = 1361129467683753853853498429520914415615 > 0.
```

Hence this one received line has MCA event probability at least `(n+4)/P`,
strictly exceeding `2^-128`. Monotonicity in radius implies, for the repository's
supremum convention,

```text
268435457/n <= mcaDeltaStar(C,2^-128) <= 313174699/n.
```

The lower side is the existing full-UDR theorem and Hamming staircase argument
described in the [earlier bracket](astra_mca_four_cubic-2026-09-06.md#current-bracket-and-the-remaining-gap).
It is a supremum bound and does not assert safety at that endpoint. The new
interval width is `44739242/n = 1/24-2/(3n)`, approximately 4.167 percentage
points. A matching universal bound is still missing.

## Restricted optimality and verification scope

Within these fixed four sources with a common factor of degree at most `s-2`
and carrier `q_i=Xp_i`, assign source weights `(3,0,3,0)` and fiber weights

```text
beta=(7,4,4,7,4,7,4,4,4,4,4,7,7,7,4,4), sum beta=82.
```

For every allowed local ownership or uncovered state, direction credit plus
weighted core credit is at most the fiber weight. At a common root the extra
credit is at most two. Summing yields

```text
Dcount + 3(C0+C2) <= 82s + 2 deg Q.
```

If all four cores are at least `A` and `Dcount>=n+1`, then
`A<=floor((68s-5)/6)=68t+44`. The construction attains this integer core bound.
This dual restricts only the selected sources' core-plus-one witnesses; it
does not bound additional decoders or the full MCA-bad set.

Reproduce both independent standard-library checks:

```sh
python3 scripts/probes/astra_mca_order16_check.py
python3 scripts/probes/astra_mca_order16_independent_check.py
```

The [primary certificate](../../scripts/probes/astra_mca_order16_certificate.json)
records all production-field seed identities, allocations, degree bounds,
security arithmetic, and the restricted dual. The
[independent receipt](../../scripts/probes/receipts/astra_order16_20260906/independent.json)
records the coefficient-system reconstruction and dense controls at `n=64`
and `n=256`. Each implementation expands the actual polynomials and received
words at those sizes and checks every counted scalar's exact core-plus-one
agreement set, together with the full-code root-bound obstruction to a joint
pair. These controls use the actual production prime, not a small substitute
field. They do not exhaust the production bad set.

The [manifest](../../scripts/probes/receipts/astra_order16_20260906/manifest.json)
binds the note, checkers, certificate, and receipts. The existing
[Lean event bridges](../../scripts/probes/astra_mca_root_relocation.lean)
verify generic finite-choice, same-support MCA, and probability steps. The
order-sixteen seed, lifted allocation, and final numerical production
instantiation remain to be formalized.

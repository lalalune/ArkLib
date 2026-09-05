# Companion attack: mixed cyclic-orbit counting audit

Date: 2026-09-04. This is an exact counting argument at the production
parameters `n=262144`, `p=2130706433`, and challenge field size `p^6`.
It does not improve the current companion upper score.

The question was whether selecting mostly complete cycles of fibre labels,
with a few partially selected cycles, could save enough prescribed
coefficients to improve the official rational-pencil construction. Fixing
the partial pattern is dominated by using coarser fibres. Allowing that
pattern to vary, then bounding key support by a union of its conditional
supports, also cannot improve the current certificate. This last statement
concerns that particular support estimate. It does not bound the actual
largest joint fibre or exclude beneficial overlap between conditional images.

The reference construction is the official
[OrbitPencil.lean at 032154395](https://github.com/proximity-prize/proximity-prize/blob/032154395c51fd6f77715a7f42d9a987ab9fb48a/ProximityPrize/SubmissionUpper/OrbitPencil.lean).
Its upper-submission sources are unchanged from inspected commit
`b34c0131cfa36b51111521541d7d3e35c8791082`.
It obtains `139775` agreeing positions from `272` of `512` fibres,
a `511`-point common core, and fourteen prescribed top coefficients.
An improvement requires at least

```text
A_target = 139776,
B = floor(p^6 / 2^128) = 274980728111395087
```

agreeing positions and strictly more than `B` distinct bad scalars.
The comparisons below concern the candidate-family pigeonhole requirement;
they cannot establish the remaining pencil conditions by themselves.

## Fixed partial patterns reduce to a coarser family

Write the number of fine fibres as `F=dH`, with fibre size `m=n/F`.
All quantities are powers of two where appropriate; `d>=2` and `H>=2`.
The `F` labels are the roots of unity of order `F`. Multiplication by
the subgroup of order `d` partitions them into `H` cycles of length `d`.
The distinguished label `1` is excluded, as in the official construction;
its fine fibre supplies an `(m-1)`-point common core.

Fix a partial pattern `W`: it occupies `h` cycles, selecting between one
and `d-1` labels from each. Write `ell=|W|`. Let `delta=1` if the cycle
containing `1` is empty in `W`, and `delta=0` if that cycle is partial.
There are

```text
L = H-h-delta
```

cycles available to be selected completely. Selecting `a` of them gives
`C(L,a)` candidates with `R=ad+ell` selected fine labels. Their root
polynomials have the form `W(Y) T(Y^d)`, where `T` is monic of degree `a`.
The polynomial denoted by `W(Y)` is fixed throughout this family.

Absorb these fixed roots into the common-core polynomial. Its degree is
`(ell+1)m-1`. After fixing `t` top coefficients of `T` and its product,
the usual two divisibility roots leave a quotient of degree at most
`a-t-3` in the coarser variable. The row-degree requirement is therefore

```text
(ell+1)m-1 + dm(a-t-3) <= n/2-1.
```

Thus the sufficient coefficient count is

```text
t = max(0, a-H/2-3+ceil((ell+1)/d))
  = max(0, r'-H/2-2),          r' = a+floor(ell/d) = floor(R/d).
```

Now use the pure family with `H` coarse fibres, each of size `dm`,
selecting `r'` full coarse fibres. It has the same coefficient exponent,
product-key support at most `H`, and agreement

```text
(r'+1)dm-1 >= (R+1)m-1.
```

It also has at least as many candidates. Indeed, if `h>0`, then
`ell<=h(d-1)`, so `floor(ell/d)<=h-1<=h+delta-1`.
If `h=0`, then `ell=0`, `delta=1`, and the same needed inequality holds.
An `a`-subset of the `L` available cycles can consequently be extended
injectively by a fixed set of `floor(ell/d)` new symbols to an `r'`-subset
of an `(H-1)`-element set. Hence

```text
C(L,a) <= C(H-1,r').
```

This proves domination of the usual product/top-coefficient pigeonhole
certificate for every fixed partial pattern. Degenerate cases with at most
one candidate cannot exceed `B`; they do not create an exception.

## Varying partial patterns: a precise support-bound limitation

Now allow any collection of partial patterns, always with the same total
number `R` of selected fine labels. Use the original fine-variable pencil,
whose prescribed top-coefficient count is

```text
T = max(0, R-F/2-2).
```

Conditional on a particular pattern `W`, the top `T` coefficients of
`W(Y)T_full(Y^d)` depend on at most

```text
k = floor(T/d)
```

coefficients of the monic polynomial `T_full`. This follows directly by
expanding the product: a coefficient at depth `j` can use only full-cycle
coefficients at depths `i` with `di<=j`. There is no independence assumption.
The constant product ranges over a fixed coset of the order-`H` group.
A valid conditional key-support upper bound is therefore

```text
K_W = H * p^min(k,a_W),
```

where `a_W=(R-|W|)/d`. The union bound gives support at most `sum_W K_W`,
and its guaranteed family ratio is

```text
(sum_W C(L_W,a_W)) / (sum_W K_W)
 <= max_W C(L_W,a_W)/K_W.
```

Set `r'=floor(R/d)` and `t'=max(0,r'-H/2-2)`. We have `k>=t'`.
For `a_W>=k`, the injection above consequently shows

```text
C(L_W,a_W)/K_W <= C(H-1,r')/(H*p^t').
```

For `a_W<k`, use `C(L_W,a_W)<=H^a_W<=p^a_W`, since `H<p`;
that component's ratio is at most `1/H` and cannot be useful.
The pure coarse family has at least the mixed family's agreement, as above.
Thus the union of these conditional support estimates, including the
coefficient-count cap by `a_W`, cannot beat the available pure-family
certificate. This argument allows different numbers of partial cycles
and different partial-cycle sizes. The case `H=1` has no selectable full
cycle and at most one candidate for each fixed pattern, so it is likewise
ineffective under this conditional-support estimate.

The inequality does **not** say that actual conditional images are
disjoint, fill these upper bounds, or have uniformly sized fibres. A better
bound on their union, or direct concentration of the joint map, is still a
possible route to an improved attack.

## Exact antipodal scan, with every multiplicity included

The probe also checks a concrete variable-pattern family independently.
For `d=2`, write `F=2H`; select `a` complete pairs and `s` singleton pairs,
so `R=2a+s`. Of the distinguished pair `{1,-1}`, only `-1` is available.
The numbers of singleton patterns that exclude or include this pair are

```text
W0 = C(H-1,s) * 2^s,
W1 = C(H-1,s-1) * 2^(s-1),    with W1=0 when s=0.
```

The total candidate count and the conditional-union support estimate are

```text
C_mixed = W0*C(H-1-s,a) + W1*C(H-s,a),
K_mixed = (W0+W1)*H*p^floor(max(0,R-H-2)/2).
```

The multiplicities include every orientation of every singleton and handle
the reserved pair separately. At the agreement-improving values scanned,
the displayed coefficient exponent is no larger than `a`.

The exact scan covers fine-fibre counts `64,128,256,512,1024,2048,4096`.
For each it checks the first `R` of each parity giving at least `139776`
agreements, and every feasible `s`. These suffice for this estimate:
for fixed `s`, increasing `R` by two increases `a` beyond the binomial
midpoint and increases the denominator exponent. Later feasible singleton
classes are already present at the first value of their parity.

| Fine fibres | Best `(R,s,a,k)` | Ceiling of guaranteed ratio |
|---:|---:|---:|
| 64 | `(34,0,17,0)` | 8,286,954 |
| 128 | `(68,0,34,1)` | 5,569,676 |
| 256 | `(136,0,68,3)` | 7,074,371 |
| 512 | `(273,1,136,7)` | 15,053,820 |
| 1024 | `(546,0,273,16)` | 1 |
| 2048 | `(1092,0,546,33)` | 1 |
| 4096 | `(2184,0,1092,67)` | 1 |

All `3802` class comparisons use integers or rational numbers. The best
ceiling `15053820` remains far below the strict threshold `B`.
For each `F` in `8,16,32,64` and every `R`, the probe independently checks
that summing these symmetry-class candidate counts gives `C(F-1,R)`.

## All production pure-coarse scales and reproduction

To close the domination comparison, the probe checks the pure-family
pigeonhole arithmetic at every coarse scale `H=2,4,...,4096` at its first
agreement-improving `r`. Larger `r` reduce the ratio, since they are beyond
the binomial midpoint and increase the exponent.
For `H=8192,...,262144`, a single integer inequality suffices. Since
`139776=273n/512`, the required `r` obeys `r>=273H/512`, so
`t>=17H/512-2`. Also `p^2>2^61`, and

```text
61*(17H/512-2) - 2*(H-1) = 13H/512-120 > 0.
```

Consequently `C(H-1,r)<=2^(H-1)<p^t`. No pure-family arithmetic
certificate at those scales can reach `B`. Together with the preceding
domination proof this addresses the conditional-union estimate for all
power-of-two cycle lengths and fibre scales dividing the production `n`.

Run:

```sh
python3 scripts/probes/astra_attack_mixed_cycles.py
```

The run passed on 2026-09-04. No official submission file was changed and
no Lean formalization is claimed. The open issue is stronger information
about the actual joint coefficient/product keys, or a different pencil
construction; this count supplies neither a new companion score nor a
Proximity Prize solution.

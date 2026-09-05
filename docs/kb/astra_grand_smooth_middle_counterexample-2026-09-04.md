# A field-uniform smooth-domain counterexample to RegionMiddleExclusion

Date: 2026-09-04. Source interface checked at research HEAD `70f0dd37b`.
Status: mathematical proof plus an exact stdlib probe; not a Lean theorem.

The sufficient-side conjecture `F1RegionSyzygy.RegionMiddleExclusion` is false
over every field containing an element of order 64. More generally, an explicit
family on `mu_(16m)` has reduced degrees `(3m,3m,3m)`, triple-region size `4m-1`,
code dimension `8m`, and minimal syzygy **product degree exactly `4m`**, for
every integer `m >= 4` for which the field contains an element of order `16m`.
Taking `m` to be a power of two gives smooth dyadic domains, including `n=2^30`.
The imbalance is `floor(m/2)`, so it grows with the domain size.

This refutes an actual named polynomial/region conjecture, beyond the earlier
numeric countermodel with an unconstrained syzygy-degree parameter. It does
not refute the genuine over-budget stack statement or determine either grand
prize threshold. A three-codeword list realization is given below, with its
precise limitation.

## Exact target and relation to prior work

The source is
[`_F1RegionSyzygyInterface.lean`](../../ArkLib/Data/CodingTheory/ProximityGap/Frontier/_F1RegionSyzygyInterface.lean):

- `VennRegions` requires a domain of exactly `2k` distinct `2k`-th roots of
  unity, four pairwise-disjoint subsets of sizes `(a,b,c,t)`, and containment.
- `BandStack` requires `a,b,c >= 1`, `max(a,b,c)+1+t <= k`, and
  `2k+1 <= a+b+c+2t`.
- `RegionSyzygyRealizable` additionally binds `delta_1` to the **actual minimal
  product degree** of the three region vanishing polynomials.
- `RegionMiddleExclusion` says all such configurations avoid
  `max(a,b,c) < delta_1 <= floor((a+b+c)/2)-2`.

The source explicitly distinguishes this interface from a genuine
over-budget witness stack. That distinction remains necessary here.
[`_F1PolytopeMiddleCountermodel.lean`](../../ArkLib/Data/CodingTheory/ProximityGap/Frontier/_F1PolytopeMiddleCountermodel.lean)
already refuted a weaker, purely numeric implication. The present construction
supplies disjoint smooth-domain roots and proves the minimal degree, rather
than treating that degree as free numeric data.

Power-map lifting itself is established practice in this repository: for
example `probe_rate_quarter_smooth_split_locators.py` and
`probe_rate_quarter_locator_doubling_extension.py` study **constant** relations
of cubic locators on `mu_16`. Those use a different seed. Here the cubic seed
has **no constant relation**, and lifting its first nonconstant relation
puts it strictly inside the middle band. No claim of a new lifting technique
or an exhaustive literature novelty check is made.

## 1. A characteristic-uniform cubic seed

Let `K` be a field with an element `zeta` of order 16. Put

```
i = zeta^4,       s = 1 + zeta + zeta^2,
S_j = i^j {1, zeta, zeta^2}       (j = 0,1,2).
```

The exponent sets are `{0,1,2}`, `{4,5,6}`, and `{8,9,10}` modulo 16,
so they are disjoint. Their monic vanishing cubics are

```
p_j(Y) = Y^3 - s i^j Y^2 + zeta s i^(2j) Y - zeta^3 i^(3j).
```

The scalar `s` is nonzero: `(zeta-1)s=zeta^3-1`, and neither `zeta=1`
nor `zeta^3=1` is possible. The three coefficient columns on degrees `3,2,1`
are the Vandermonde columns at `1,i,-1`, with row factors `1,-s,zeta s`.
All three arguments are distinct, and both nontrivial row factors are
nonzero. The minor is therefore invertible. In particular,

```
c_0 p_0 + c_1 p_1 + c_2 p_2 = 0,     c_j in K
```

forces `c_0=c_1=c_2=0`.

On the other hand, the linear map

```
(K[Y]_{<=1})^3  ->  K[Y]_{<=4},     (q_j) |-> sum_j p_j q_j
```

has a six-dimensional source and a five-dimensional target, so it has a
nonzero kernel. Thus a nonzero syzygy with product degree at most 4 exists.
The invertible coefficient minor excludes product degree at most 3. The
minimal product degree is exactly 4.

This proof works in every such field, including positive characteristic.
Existence of order 16 already excludes characteristic 2. No exceptional-prime
norm list or empirical large-prime extrapolation is needed.

## 2. Power-map lift, with exact minimality

Let `omega` have order `n=16m`, set `zeta=omega^m`, and take the domain
`Omega={omega^e: 0<=e<16m}`. Define

```
R_j = {omega^e : e modulo 16 belongs to {4j,4j+1,4j+2}},
W_j(X) = p_j(X^m).
```

Each `R_j` has `3m` elements. The sets are disjoint. The monic polynomial
`W_j` has degree `3m` and has all `3m` elements of `R_j` as roots, hence it
is exactly the region vanishing polynomial. This also proves squarefreeness
and pairwise coprimality.

Lift a nonzero linear-cofactor seed syzygy by substituting `Y=X^m`. It gives
cofactors of degree at most `m`, and all slot products have degree at most
`4m`. The lifted syzygy is nonzero because substitution is injective.

For the reverse inequality, suppose

```
sum_j W_j r_j = 0
```

has every slot product of degree less than `4m`. Since `deg W_j=3m`, each
nonzero `r_j` has degree less than `m`. Write
`r_j=sum_(h=0)^(m-1) c_(j,h) X^h`. Terms with different residues modulo
`m` cannot cancel. At each residue `h` the asserted relation is exactly

```
sum_j c_(j,h) p_j(Y) = 0.
```

The seed minor forces every `c_(j,h)` to vanish. This contradicts a
nonzero syzygy and proves **minimal product degree `delta_1=4m`**.
No Hilbert--Burch degree-sum formula or claim about the second generator is
needed for this counterexample.

## 3. Every interface face holds

Set

```
a=b=c=3m,     t=4m-1,     k=8m,     n=16m,     delta_1=4m.
```

The three pair regions use `9m` domain points. Choose any `4m-1` points of
the complement for `T`; the complement has `7m` points. The interface checks
reduce to

```
a+b+c+t = 13m-1 <= 16m,
max(a,b,c)+1+t = 7m <= 8m,
2k+1 = 16m+1 <= 17m-2 = a+b+c+2t,
3m < 4m <= floor(9m/2)-2.
```

The last two hold for `m>=4`. All positivity and disjointness conditions
also hold. Consequently the exact `RegionSyzygyRealizable` predicate holds,
and its `middleBand` conclusion is true, contradicting
`RegionMiddleExclusion K`.

| `n` | `k` | `a=b=c` | `t` | `delta_1` | imbalance |
|---:|---:|---:|---:|---:|---:|
| 64 | 32 | 12 | 15 | 16 | 2 |
| 128 | 64 | 24 | 31 | 32 | 4 |
| 256 | 128 | 48 | 63 | 64 | 8 |
| 1,073,741,824 | 536,870,912 | 201,326,592 | 268,435,455 | 268,435,456 | 33,554,432 |

The same example also refutes the unrestricted
`SYZ40.UniformSylvesterInjective K (16m) (8m)` as actually defined in
[`_SYZ40FinalAssembly.lean`](../../ArkLib/Data/CodingTheory/ProximityGap/Frontier/_SYZ40FinalAssembly.lean).
Use `m_AB=m_AC=m_BC=7m-1`, so all cofactor budgets equal `m` and
`k-1=8m-1 < 10m-1 = m_AB+m_AC-t`. From
`W_AB r_AB+W_AC r_AC+W_BC r_BC=0`, use `(r_AC,-r_BC)` in the
generalized Sylvester divisibility predicate. Each cofactor is nonzero:
if one vanished, pairwise coprimality would force a polynomial of degree
`3m` to divide a nonzero cofactor of degree at most `m`, impossible.
This refutation even supplies the root and coprimality conditions which
that unrestricted definition does not explicitly carry.

## 4. A real three-codeword list, with a remaining stack limitation

Label `W_0,W_1,W_2` as `W_AB,W_AC,W_BC`, and choose a lifted nonzero
syzygy with the plus signs above. Let `V_T` be the vanishing polynomial of
the triple region. Define

```
f_A = 0,
f_B = V_T W_AB r_AB,
f_C = -V_T W_AC r_AC.
```

Then `f_B-f_C=-V_T W_BC r_BC`. The three polynomials are distinct by the
nonzero-cofactor argument. Each has degree at most
`t+4m=8m-1=k-1`, so they define actual codewords of `RS[K,Omega,k]`.
They agree on the prescribed pair regions and on `T`.

After these regions there are `3m+1` unused points. Give each codeword a
disjoint private set of

```
q = floor(2m/3)+2
```

points. These three sets fit because `3q<=3m+1` for `m>=4` (check `m=4`
directly; for `m>=5`, `3q<=2m+6<=3m+1`). A received word can equal each
polynomial on its private region, their common value on each pair region,
and zero on `T`; fill any unused positions arbitrarily. Every assigned
agreement set then has size

```
t+6m+q = floor(2n/3)+1 > 2n/3.
```

This is an actual three-element list. It need not have exactly those full
agreement regions, because additional accidental agreements may occur.
It establishes neither a four-or-more spread stack nor an over-budget MCA
family. It provides no bound on the number of bad scalars and no conclusion
about the largest prize radius.

The [genuine-stack follow-up](astra_grand_stack_scope-2026-09-04.md) proves
that no additional codeword in these three codewords' affine span reaches
the required agreement. It also identifies the missing MCA witness data and
the zero-family obstruction in the current SYZ43 rank premise. Codewords
outside that span remain unresolved.

## 5. Reproduction and large-field discipline

Run:

```sh
python3 scripts/probes/astra_grand_smooth_middle_counterexample.py
```

The probe checks all eight primitive order-16 generators over each of
`F_193`, `F_257`, `F_65537`, and the certified Proth field

```
P = 111*2^128+1 = 37771342728224169444434581424926271471617.
```

The existing repository Proth certificate is reproduced exactly:
`5^((P-1)/2)=-1 mod P`, with odd `111<2^128`. It then performs **40 full
domain checks**: `m=4` over `F_193` and `m=4,8,16` over the other three
fields, using four primitive domain generators in each cell. Twelve of
these checks have `P>n^4`.

The checks directly multiply all root factors, compare to the composed
cubics, compute coefficient-matrix ranks both below and at the claimed
minimal degree, verify the polynomial syzygy, instantiate every region
face, and build/evaluate the actual three codewords and received word.
At `m=4` the two ranks are `12/12` and `14/15`, giving kernel dimensions
zero and one. The first `F_193` received word has agreement counts
`[45,43,44]`, each at least the assigned count 43.

For `n=2^30`, the probe checks the numeric faces and an actual primitive
domain root and seed in the same Proth field, where `P>n^4`. It does
**not** materialize the billion-point domain or its full matrices. The
production-size assertion follows from the field-uniform proof above.
Independent review separately checked the `m=4` root products and ranks
over `F_257`, `F_65537`, and `F_2130706433`.

## 6. Original-prize and current-literature scope

The [official original challenge](https://proximityprize.org/) asks for the
largest radius at a prescribed MCA or constant-interleaving list budget
for fixed smooth plain Reed--Solomon codes, at rates `1/2,1/4,1/8,1/16`.
The [Arnon--Boneh--Fenzi paper](https://eprint.iacr.org/2026/680), last revised
2026-07-06 when checked, includes updated attacks and an MCA lower bound.
This note repairs one attempted sufficient input; it does not determine
those largest radii.

The refreshed [Shortening Bounds for Reed--Solomon MCA](https://eprint.iacr.org/2026/1463)
gives exponential-budget beyond-Johnson bounds and explicitly leaves the
unrestricted subexponential-budget smooth frontier open. Its source was
read at author-repository commit
[`93fba1be3f3299b0ba4708d88715377bbb656e45`](https://github.com/przchojecki/rs-mca/blob/93fba1be3f3299b0ba4708d88715377bbb656e45/RS_MCA_Paving_v9.2.tex).
The [Yuan--Zhu revision of 2026-07-10](https://arxiv.org/abs/2605.07595v2)
treats random Reed--Solomon codes; that theorem does not establish the
fixed smooth-domain prize statement. These distinctions were checked
before selecting the exact region-syzygy residual for this attempt.

The remaining meaningful F1 target must retain additional genuine
large-stack information. A statement about smooth roots, band-region
cardinalities, and minimal syzygy degree alone cannot supply the proposed
middle exclusion, even at arbitrarily large dyadic domain orders and in
large characteristic.

# An obstruction to the direct antipodal recursion after degree seven

The following written argument rules out a specific symmetric extension of the
[four-source order-16 construction](astra_mca_order16-2026-09-06.md). It does not
rule out arbitrary order-32 sources, a different degree allocation, or a stronger
MCA attack. The proof is elementary algebra and has not been formalized in Lean.

## Precise statement

Work over a field `F` of characteristic different from two. Let `A,B,C,D` be
monic degree-`h` polynomials, each split into `h` distinct roots in `F`, with their
four root sets pairwise disjoint. Suppose

```text
A(Y) = (Y-a) F_A(Y²),
B(Y) = (Y-b) F_B(Y²),
C(Y) = (Y-c) F_C(Y²),
```

where `a,b,c` are distinct nonzero field elements. Suppose the roots of `D`
contain `{r,-r,t,-t}`, with `r,t` nonzero and `r² ≠ t²`.

There are no four pairwise distinct polynomials `W0=0,W1,W2,W3`, all of degree
at most `2h+1`, with these triple coincidences:

| Root set | Sources required to agree |
|---|---|
| roots of A | 0, 1, 2 |
| roots of B | 0, 1, 3 |
| roots of C | 0, 2, 3 |
| roots of D | 1, 2, 3 |

Only these coincidences are required. Extra coincidences are permitted by the
hypotheses and cannot evade the obstruction.

## The quadratic coefficient identity

For `N=n0+n1 Y+n2 Y²` and `Q=q0+q1 Y+q2 Y²`, direct expansion gives

```text
N(Y)Q(-Y) - N(-Y)Q(Y)
  = 2Y [(n1 q0 - n0 q1) + (n1 q2 - n2 q1)Y²].
```

If this polynomial vanishes at both `r` and `t`, the assumptions on the
characteristic and those two points imply

```text
n1 q0 = n0 q1,    n1 q2 = n2 q1.
```

Indeed, after dividing by `2r` and `2t`, subtract the two equations and use
`r²-t² ≠ 0`. Thus the cross-difference vanishes identically: `N/Q` is an even
rational function.

If `N,Q` are nonzero, the same two coefficient equations give a useful
classification without any coprimality assumption. Either `n1=q1=0`, so both
polynomials are even, or both odd coefficients are nonzero and
`N=(n1/q1)Q`. To check the latter alternative, if precisely one odd coefficient
were zero, the equations would force the other polynomial to be zero.

When `N=(Y-b)l1` and `Q=(Y-c)l2`, with nonzero polynomials `l1,l2` of degree at
most one and distinct nonzero `b,c`, this says that either `N,Q` are
proportional or they are both even quadratics. A nonzero even polynomial of
degree at most two with a nonzero root cannot be a constant.

## Applying the identity to the source factors

The disjoint zero constraints and degree budget force

```text
W1 = A B l1,    W2 = A C l2,    W3 = B C l3,
```

where `l1,l2,l3` are nonzero and have degree at most one. The quotients exist
because the factors split into distinct roots; they are nonzero because each
`Wi` differs from `W0=0`.

At every root of `D`, the other three factors are nonzero. Cancel them from
the triple equalities to obtain

```text
B l1 = C l2,    A l2 = B l3.
```

At each paired point `u,-u` in `D`, the even factors `F_A,F_B,F_C` have the
same values at both points, and these values are nonzero by disjointness.
Cross-multiplication therefore makes the following quadratic cross-differences
vanish at `r` and `t`:

```text
N1=(Y-b)l1, Q1=(Y-c)l2;
N2=(Y-a)l2, Q2=(Y-b)l3.
```

This step does not divide by any `li` value: those values may vanish. The
coefficient identity shows that both ratios are even identically.

If `N1,Q1` are proportional, evaluation at their specified roots gives

```text
l1 proportional to Y-c,    l2 proportional to Y-b.
```

For the second ratio, proportionality gives `l3` proportional to `Y-a`.
If instead both second quadratics are even, `N2` forces `b=-a`, while `Q2`
forces `l3` proportional to `Y+b=Y-a`. The same conclusion follows.

If instead both `N1,Q1` are even, then `l1` is proportional to `Y+b` and
`l2` to `Y+c`. The second numerator is proportional to `(Y-a)(Y+c)`.
It cannot be even, since that would imply `a=c`. Thus the second quadratics
are proportional. Their specified root `b` gives
`(b-a)(b+c)=0`, hence `b=-c`. This reduces to the preceding case. Every case
therefore forces

```text
l1 proportional to Y-c,
l2 proportional to Y-b,
l3 proportional to Y-a.
```

Now `W1-W2` vanishes at all `h` roots of `A`, all `h` roots of `D`, and at
both `b` and `c`. These are `2h+2` distinct points, by the disjoint-root and
anchor hypotheses. Its degree is at most `2h+1`, so it is the zero polynomial.
This contradicts the required distinction of `W1` and `W2` and proves the claim.

The order-16 degree-seven construction has `h=3`, with only one antipodal pair
in its corresponding `D` set. One pair alone need not annihilate the linear
polynomial in `Y²` in the coefficient identity. Thus that construction escapes
this obstruction. A direct degree-15 recursion with four seven-point sets,
each one nonzero anchor plus three antipodal pairs, does not.

## Exact finite controls and the 576-pattern production check

Run the standalone standard-library checker:

```sh
python3 scripts/probes/astra_mca_antipodal_recursion_check.py
```

It prints a deterministic JSON receipt and writes no files. The observed status
is `PASS_EXACT_ANTIPODAL_ALGEBRA_AND_576_RESTRICTED_PATTERNS`. The controls are:

- Every pair of nonzero degree-at-most-two coefficient vectors over `F3`, `F5`,
  and `F7`: the displayed coefficient identity, the two-pair implication when
  such pairs exist, and the proportional-or-even classification.
- All distinct nonzero anchors and all nonzero linear-or-constant factors up to
  scalar over `F5`, `F7`, `F11`, and `F17`: the two even-ratio conditions force
  exactly the three asserted extra roots.
- All 576 assignments in the following specific order-32 family over the
  [repository-certified production field](../../ArkLib/Data/CodingTheory/ProximityGap/Frontier/_PrizeShapePrimeP30.lean).

For the last control, set `eta=g^(2^25)` using the certified production `P,g`.
The checker verifies `eta^16=-1`, `eta^32=1`, and 32 distinct powers. Fix the
anchor exponents `(0,16,24,8)`. Independently permute `alpha` and `beta` through
`(1,3,5,7)` and form the four degree-seven factors

```text
(Y-eta^anchor_i)(Y²-eta^(4 alpha_i))(Y⁴-eta^(4 beta_i)).
```

The checker independently expands their seven roots, verifies disjointness of
all 28 roots and the three antipodal pairs in each factor, then imposes the
`D` equations on the six coefficients of `l1,l2,l3`. With each linear factor
written constant first, the two matrix rows at a `D` root `x` are

```text
[B(x), xB(x), -C(x), -xC(x), 0, 0],
[0, 0, A(x), xA(x), -B(x), -xB(x)].
```

Exact modular Gaussian elimination gives rank six for all 576 resulting
`14 × 6` matrices. Thus this specified finite family has no nonzero tuple of
such linear quotients, a stronger conclusion for these patterns than merely
excluding four distinct sources. Fixing the anchor labels is harmless within
this family: permute the four source labels, then subtract the newly chosen
reference source to restore `W0=0`. This permutes the four triple types and
preserves the degree bound.

The finite checks are algebra controls, not substitutes for the characteristic-
independent written proof. The script uses the existing production primality
certificate rather than reproving it, and neither its census nor this restricted
obstruction establishes universal MCA safety or an optimal radius.

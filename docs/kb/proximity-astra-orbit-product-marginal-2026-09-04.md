# Exact product marginal for the 256-fibre companion candidate

Date: 2026-09-04. This is a finite exact obstruction to one proposed
pigeonhole refinement. It is not an upper bound on the largest joint
coefficient/product fibre and does not improve a companion score.

The tempting `F=256,r=136,t=6` OrbitPencil variant misses its guaranteed
family-size target by slightly more than a factor four. Optimizing the
product-label marginal cannot repair this: its maximum differs from its
uniform mean by a relative amount strictly between `2^-128` and `2^-127`.
The six top-coefficient labels could still have exploitable concentration;
this calculation does not resolve that separate question.

## Exact census

Use the candidate's 255 allowed fibre labels `1,...,255`, with label zero
reserved for its common core. Let `N_r(s)` count the `r`-subsets whose label
sum is `s mod256`. For `r=136`, this is also the constant-product label of
the monic root polynomial, since `136` is even.

The probe computes every count exactly and obtains:

```text
T = C(255,136)
  = 1642763237966455131089379983394824266573028270959430944304016753768099919875

M = max_s N_136(s)
  = 6417043898306465355817890560136032291335107637534903232761973368781765385

256M - T
  = 8759284249504283283048428640032018685.
```

The maximum occurs exactly for `s=4 mod8`. Integer multiplication verifies

```text
(256M-T)*2^127 < T < (256M-T)*2^128.
```

Thus `(M/(T/256))-1` lies strictly between `2^-128` and `2^-127`.

## Two independent methods and two consistency identities

The first method is the ordinary subset-sum dynamic program. Start with
`D_0(0,0)=1`; while processing label `b`, update

```text
D_b(k,s) = D_(b-1)(k,s) + D_(b-1)(k-1,s-b mod256).
```

The second method uses a root-of-unity filter and evaluates its formula
entirely in integers. For general `F=2^h`, let `d` divide `F`. A character
of exact order `d` gives

```text
product_(b=0..F-1) (1+X*zeta^b) = (1-(-X)^d)^(F/d),
```

where `zeta` now has order `d`. Removing the label-zero factor `1+X`
shows that the degree-`r` coefficient, for `r<F`, is

```text
H_d(r) = (-1)^(r+floor(r/d)) C(F/d-1,floor(r/d)).
```

This follows by expanding the numerator and summing the alternating
binomial prefix. Grouping characters by their exact order yields

```text
F*N_r(s) = sum_(d divides F) H_d(r)*c_d(s),
```

with the power-of-two Ramanujan sums

```text
c_1(s)=1;
c_d(s)= d/2  if d divides s,
       -d/2  if d/2 divides s but d does not,
        0    otherwise.        (d>=2)
```

These formulas reproduce every dynamic-program entry for both sizes 136
and 119. Independently, the total is checked against `C(255,136)`, and
complementation in `{1,...,255}` gives

```text
N_136(s) = N_119(128-s mod256),
```

because the sum of all labels is `128 mod256`.

## Exact companion threshold comparison

The profile uses

```text
p = 2130706433,
budget = floor(p^6/2^128) = 274980728111395087.
```

Retaining only the bound of `p^6` possible six-coefficient vectors,
the strongest product-first pigeonhole guarantee is

```text
ceil(M/p^6) = 68579341025511059.
```

It is below the required strict budget. More precisely, the probe proves
without logarithms or floating point that

```text
4M < budget*p^6 < 5M.
```

Consequently, replacing the uniform product average by the **exact largest
product marginal** still leaves this certificate more than a factor four
short. A successful refinement must control the distribution of the six
top coefficients inside a product fibre, change the construction, or find
some other source of a larger winning family.

This does not prove that the joint map has no sufficiently large fibre.
Its actual maximum may exceed the pigeonhole guarantee; it was not
enumerated or upper-bounded here.

## Reproduction

Run:

```sh
python3 scripts/probes/astra_orbit_product_marginal.py
```

The standard-library probe compares the two formulas entry by entry,
checks the total and complement identities, and verifies every displayed
threshold inequality using integers. It passed on 2026-09-04 in about
0.2 seconds. The official construction was inspected read-only at commit
`b34c0131cfa36b51111521541d7d3e35c8791082`; no official files were changed,
and no Lean verification, score improvement, or prize closure is claimed.

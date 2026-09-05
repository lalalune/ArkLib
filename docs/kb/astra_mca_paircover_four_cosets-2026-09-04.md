# Four-coset pair covers require product degree n/2

Status: a characteristic-independent algebraic proof, independently reviewed,
with exact finite checks in the production prime field. Not Lean-formalized.
It excludes the four-coset architecture below, including a recursively balanced
production partition. **It does not exclude arbitrary pair-region partitions.**

## The architecture and exact minimum

Let `n=4m` with `m≥1`, and suppose K contains all n distinct n-th roots of unity. Split
the domain into the four fibers of `T=X^m` over the fourth roots of unity
α,β,γ,δ. Put the entire α fiber into AB, the entire β fiber into AC, and the
entire γ fiber into BC. Partition the remaining δ fiber arbitrarily among
the three regions.

Let a,b,c be the monic vanishing polynomials of those three residual pieces.
They are pairwise coprime, may have degree zero, and satisfy

```
a b c = X^m-δ,           degree(a)+degree(b)+degree(c)=m.
```

The full region vanishing polynomials are

```
A=(X^m-α)a,    B=(X^m-β)b,    C=(X^m-γ)c.
```

The minimum product degree of a nonzero syzygy `Au+Bv+Cw=0` is **exactly 2m**.
This holds for every split of the fourth fiber, not merely a recursive split.

For the lower bound, suppose every slot product has degree less than 2m.
Put `P=au`, `Q=bv`, `R=cw`; every nonzero one has degree less than m. Then

```
X^m(P+Q+R)=αP+βQ+γR.
```

If `P+Q+R` were nonzero, the left side would have degree at least m while the
right side has degree less than m. Hence both sides vanish. Since α,β,γ are
distinct, the kernel of their two constant coefficient equations is spanned by

```
(β-γ, γ-α, α-β).
```

Thus `(P,Q,R)=h(X)(β-γ,γ-α,α-β)` for a polynomial h of degree less than m,
unless h=0. All three displayed constants are nonzero. Consequently a,b,c
each divide h, and pairwise coprimality gives `abc | h`. As `degree(abc)=m`,
h must be zero, forcing u=v=w=0. This proves the lower bound.

For the upper bound, each of A,B,C has degree at most 2m. The cofactor space
for slot product degree at most 2m has dimension

```
Σ_{F=A,B,C} (2m-degree(F)+1) = 6m-4m+3 = 2m+3.
```

Its sum maps linearly into the `(2m+1)`-dimensional space of polynomials of
degree at most 2m. Rank-nullity gives a nonzero syzygy. This proves the exact
minimum. Existence at 2m alone does not certify absence of extra roots or the
exactly-two-agree condition.

No characteristic-zero argument or prime-size approximation enters the proof.
In particular, a special finite-characteristic identity cannot evade this
degree obstruction while retaining the same four-coset architecture.

## Balanced recursive production partitions are covered

For `n=4^j`, assign three quarter-domain cosets to the three regions and repeat
the construction inside the remaining coset. At the final singleton, assign
the point to BC. Starting with `(a_1,b_1,c_1)=(0,0,1)`, the cardinalities obey

```
(a_(4m),b_(4m),c_(4m))=(m+a_m,m+b_m,m+c_m),
```

so they are exactly `((n-1)/3,(n-1)/3,(n+2)/3)`. This avoids the unequal
proportions retained by a simple power-map lift, but the degree obstruction
still applies already at the top-level split.

At `n=2^30` these sizes are `(357913941,357913941,357913942)`. The minimum
syzygy product degree is 536870912, exceeding the
[pair-cover attack's cap](astra_mca_paircover_target-2026-09-04.md) 536870910.
Indeed, the architecture cannot arise from three degree-less-than-`n/2`
codewords at all: subtract one codeword and factor the three pairwise
differences by A,B,C to obtain the prohibited syzygy.

## Reproduction and limits

Run `python3 scripts/probes/astra_mca_paircover_four_cosets.py`. It uses
the repository's certified production prime
`365375409332725729550921208179070755120141565953`, from
`_PrizeShapePrimeP30.lean`, and checks actual root-product polynomials and
syzygy matrix ranks for the single recursive partition at n=4,16,64,256.
At each size the nullities at degrees `n/2-2,n/2-1,n/2` are respectively
`0,0,2`. It also checks the production cardinality recurrence.

The production-scale exclusion follows from the general proof, not from
extrapolating the small-domain matrices. The script does not construct or
enumerate a production-size matrix. The unrestricted balanced pair-cover
existence problem remains unresolved, and no MCA over-budget witness or
new safe/unsafe radius is asserted.

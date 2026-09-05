# Classical Paley conjectures and the prize's subgroup-sum route

Paley graphs are deterministic graphs built from quadratic residues.
They are believed to resemble random graphs even on fairly small vertex
sets. Our prize route studies a much thinner subgroup and its additive
Fourier coefficients. These problems share character-sum techniques,
but their named conjectures and required estimates are different.

## Three statements to keep separate

For a prime p congruent to one modulo four, the classical Paley graph
joins x,y when x-y is a nonzero square. One familiar conjecture asks
for its clique number to be bounded by a polynomial in log p. This is
distinct from its already-known global eigenvalues
`(p-1)/2, (-1+sqrt(p))/2, (-1-sqrt(p))/2`. Both the graph and the
polylogarithmic clique conjecture are stated in
[Kunisky, introduction and Conjecture 1.1](https://arxiv.org/html/2303.16475v1#S1).

The **double-character-sum Paley conjecture**, in a formulation allowing
all nontrivial multiplicative characters, says: for every epsilon>0
there are delta(epsilon)>0 and p0(epsilon), such that for primes p>p0,
sets A,B with both sizes greater than p^epsilon, and nontrivial chi,

```text
abs(sum_{a in A,b in B} chi(a+b)) <= p^(-delta)*|A|*|B|.
```

It remains open. Its exact quantifiers and status are recorded in
[Kim--Yip--Yoo, Conjecture 2.12 and Section 2.4](https://arxiv.org/html/2309.09124v4#S2.SS4).
The quadratic-character version concerns the discrepancy of Paley edges
between sets. This is not an additive exponential-sum theorem.

The **BGK theorem**, by contrast, gives power saving for

```text
eta_H(b) = sum_{h in H} exp(2*pi*i*b*h/p), b != 0,
```

when H is a multiplicative subgroup of size at least p^gamma for a
fixed gamma>0. The exponent and constant depend on gamma. See the
[primary BGK paper](https://doi.org/10.1112/S0024610706022721) and
[Kowalski's proof account, Theorem 1.1](https://arxiv.org/html/2401.04756#S1).
This theorem does not prove the classical Paley conjecture for arbitrary
A,B. In particular, the two uses of the word "character" do not make
these sums interchangeable.

The graph with eigenvalues eta_H(b) is the additive Cayley graph with
connection set H. Its degree is |H|. It is the classical Paley graph
only when H is the full subgroup of nonzero squares. An arbitrary
bound `C*sqrt(|H|)` also should not be identified with the precise
Ramanujan bound `2*sqrt(|H|-1)`.

## A valid subgroup specialization of the double-sum conjecture

There is an exact positive bridge for a shifted **multiplicative** sum.
Extend a nontrivial multiplicative character chi by chi(0)=0. For any
multiplicative subgroup H and nonzero lambda,

```text
sum_{a,b in H} chi(a+lambda*b)
  = (sum_{a in H} chi(a)) * (sum_{h in H} chi(1+lambda*h)).
```

Proof: for each nonzero a, substitute b=a*h and factor chi(a).
Consequently, if chi is trivial on H, the left side is n times the
shifted sum, where n=|H|. Applying the double-sum conjecture to
`A=H, B=lambda*H` gives

```text
abs(sum_{h in H} chi(1+lambda*h)) <= n*p^(-delta),
```

provided `n>p^epsilon` and `p>p0(epsilon)`. Both input sets are large;
no singleton substitution is used. If chi is nontrivial on H, the
double sum instead vanishes identically and this specialization gives
no bound on the shifted sum.

This refines the scope of the earlier
[singleton-input warning](deltastar-464-paley-double-sum-singleton-gate-2026-06-25.md):
subgroup multiplicative symmetry does remove that particular obstacle
for these shifted sums and characters trivial on H. It does not turn
the result into a bound for eta_H(b).

Even Fourier duality retains a nontrivial summation. With
`tau(bar chi)=sum_t bar chi(t)*exp(2*pi*i*t/p)`, one has

```text
sum_{h in H} chi(1+lambda*h)
 = 1/tau(bar chi) * sum_{t != 0}
     bar chi(t)*exp(2*pi*i*t/p)*eta_H(lambda*t).
```

This follows from the defining Gauss sum after t is rescaled.
The right side mixes all nonzero additive frequencies; it is not a
pointwise equality between a shifted character sum and one Gauss period.
No inverse estimate at the prize scale is proved here.

## Literal production parameters and the quantitative gap

The production instance certified in
[`_PrizeShapePrimeP30.lean`](../../ArkLib/Data/CodingTheory/ProximityGap/Frontier/_PrizeShapePrimeP30.lean)
has

```text
n=2^30,
P=n*(2^128+192)+1,
[F_P^*:H]=2^128+192.
```

The index is even, so the quadratic character is trivial on H.
Exact integer comparisons give `n^5<P<n^6`, `n^4<P`, and
`n^50>P^9`. Thus n>P^(9/50), while n is substantially below P^(1/4).
The approximate exponent log_P(n) is 0.1898734. Estimates requiring
`|H|>P^(1/4)` do not apply to this instance.

The subgroup specialization is eligible at epsilon=9/50 as far as
set size is concerned. The conjecture's unknown p0 and delta do not
give a numeric certificate at this fixed prime. Moreover, even for
the shifted sum, matching a proposed target
`C*sqrt(n*log(P/n))` through `n*P^(-delta)` would require

```text
delta >= log(n/(C^2*log(P/n))) / (2*log(P)).
```

At C=1 the right side is approximately 0.0744581 and the target is
approximately 308651. An assertion that some positive delta exists
does not provide that inequality. C must also be fixed by the actual
consumer; it cannot be enlarged without checking its budget.

The additive analytic route similarly seeks a specific bound on the
maximum eta_H(b), with constants suitable for downstream use. The
literal proof of
[`prizeFloor_of_BGK_and_incidence`](../../ArkLib/Data/CodingTheory/ProximityGap/Frontier/_PrizeFloorOfBGK.lean)
requires a separate `WorstCaseIncidenceBounded` hypothesis and consumes
that hypothesis to bound MCA error. The additive-period estimate alone
is not proved to supply it by this theorem. A claim that the full prize
is equivalent to the named Paley conjecture is therefore unsupported.

## Reproducible check and bounded next target

Run `python3 scripts/probes/astra_paley_transfer.py`. It verifies the
subgroup double-sum identity for every nonzero shift in four cells:
`(p,n)=(17,4),(97,8),(257,16),(17,16)`. The first three have chi trivial
on H. In the last cell H is all nonzero elements, so the double sum
is zero although the shifted single sum is -1. This exactly refutes
omitting the character-triviality condition, not the Paley conjecture.
The production size gates use exact integers; displayed logarithms
are numerical approximations.

The focused analytic target worth retaining is a bound for the Paley
cut between H and lambda*H, uniform in lambda, with an explicit saving
large enough for the desired shifted-sum moment. The subgroup identity
gives its consumer without a singleton loss. This remains a genuine
character-sum problem; generic graph expansion or existing BGK power
saving does not discharge it. The concrete MCA construction remains
the primary prize attack.

The misleading "PGC already proven" comments in
[`_wf9B7_PrizeBGKReductionDirections.lean`](../../ArkLib/Data/CodingTheory/ProximityGap/Frontier/_wf9B7_PrizeBGKReductionDirections.lean)
were corrected. Its entire noncomment Lean token sequence was checked
unchanged. This note and the finite identities do not constitute a new
Paley theorem or a prize solution.

# Independent finite-parameter audit, 2026-09-05

The explicit parameter construction in BCPZZ revision 1 cannot be instantiated
at the production field or length. This is a limitation of the published
constants and of the available quantitative certificate, not a disproof of
their capacity result. The paper is external work by Joshua Brakensiek, Yeyuan
Chen, Aaron (Louie) Putterman, Zihan Zhang, and Kai Zhe Zheng.

Source: [revision 1, September 5](https://eccc.weizmann.ac.il/report/2026/164/revision/1/download),
visually checked printed pages 20 and 22; Theorem 2.1 checked in extracted text
on printed page 7. The formal corollary treats scalar Reed--Solomon codes at arbitrary
distinct evaluation points over prime fields, for constant rate and slack;
its quantitative list bound is q^{O_{R,delta}(1)}. Theorem 2.1 supplies the
explicit root-finding bound q^{4d+6}.

## Uniform parameter obstruction (our arithmetic)

Theorem 4.1, equation (26), requires

    0 < theta, eta < 1,
    eta < [theta^3(1-theta)/768]^[(5+theta)/(1-theta)],
    k' > d = ceil(eta^(-3/theta)),
    q >= N >= k'.

For every 0<theta<1,

    27 - 256 theta^3(1-theta)
      = (4theta-3)^2(16theta^2+8theta+3) >= 0.

Thus theta^3(1-theta)/768 <= 9/65536 < 2^-12. Because the
outer exponent is greater than 5 and the base is below 1, eta < 2^-60.
Since 3/theta>3, d>2^180. Hence any such application needs q>2^180.
But the production prime is

    P = 365375409332725729550921208179070755120141565953
      = 2^30(2^128+192)+1,
    2^158 < P < 2^159.

No theta works, even before imposing a production rate or choosing padding.
This proof uses an exact polynomial identity and rational/integer comparisons,
not a numerical optimization over theta.

## Separate length and agreement obstruction (our arithmetic)

The padding in Corollary 5.1 sets

    k' = max(k, ceil(eta^(-3/theta))+1),
    N = max(n, ceil(k'/((1-theta)eta))).

It needs eta*N <= A, where A is the guaranteed original agreement. These
formulas instead imply

    eta*N >= k'/(1-theta) > 2^180,
    N > 2^240.

The production instance has n=2^30 and A<=n. Therefore this padding argument
cannot preserve the desired agreement even if a larger field were substituted.
The proof on printed page 22 explicitly uses sufficiently large original n
for this preservation step. The formal corollary omits that qualifier; bounded
small n can in principle be handled by exhaustive enumeration absorbed into
the constants, but that existential repair supplies no useful production
list-size bound. This audit does not allege a false asymptotic theorem.

## List bound and scope

The required integer list cap in the question is floor(P/2^128)=2^30.
The available explicit upper bound P^{4d+6} is already greater than P, so it
cannot establish that cap, even if parameter applicability were ignored.
An upper bound larger than the cap is not a lower bound on the true list.
Likewise, an unspecified polynomial exponent or constant cannot be replaced
by 1 to obtain a numerical certificate. The informal n-polynomial wording
does not supply the missing explicit constant at this fixed q/n.

The checked theorem does not cover nonprime fields or supply an interleaved
proximity-gap theorem. Any transfer to extension fields, vector-valued words,
or the prize's bad-scalar event needs its own valid reduction and numerical
bound. No such transfer is proved here. This audit establishes no prize
closure and makes no claim of authorship of the external decoding method.

## Reproduction and source pin

```sh
python3 scripts/probes/astra_capacity_finite_gates_check.py
```

The source PDF downloaded during the audit has SHA-256
`560e7134e49abc065718bf97a50c20b1cce7eba9d7b465b98a64be90dd88d903`.
The optional `--source-pdf PATH` argument verifies a locally supplied copy
against that digest. The default arithmetic check does not download the paper
or certify its proof. Both reviewers independently obtained the same digest.

The current [research receipt](../wiki/proximity-astra-2026-09-04.md) keeps
these finite requirements separate from asymptotic guarantees. The source's
higher-derivative interpolation method remains a possible direction for new
finite estimates; no such improved estimate is asserted here.

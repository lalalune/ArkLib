# The same mu16 pair-cover matrices in the concrete prize field

The prescribed degree-six, 5:5:6 pair-cover seed is also absent on **mu16 in the
concrete prize field**. The exhaustive check evaluates 378378 normalized
partitions and finds zero syzygies. This closes the field-specific gap left by
[the F65537 and characteristic-zero check](astra_mca_paircover_search-2026-09-04.md)
for this small seed. It does not enumerate the production domain of size 2^30.

## Exact field and domain

The field modulus and smooth subgroup generator are read and checked against
[`_PrizeShapePrimeP30.lean`](../../ArkLib/Data/CodingTheory/ProximityGap/Frontier/_PrizeShapePrimeP30.lean):

```text
P = 365375409332725729550921208179070755120141565953
  = 2^30*(2^128+192)+1,
G = 303645430271030343624574566109998498685964493478.
```

The cited source contains the primality and order certificates. This probe
does not rebuild those Lean proofs. It checks the numeric source constants,
the shape of P, and the generator power identities directly. Its actual
sixteenth-root generator is

```text
g16 = G^(2^26) mod P
    = 357111556877444407914257742635116754287240874648.
```

It checks `g16^16=1` and `g16^8=-1`, and uses exactly the sixteen points
`g16^i`, for i=0,...,15.

## Exhaustive algebraic check

The partition normalization, lambda normalization, and reduction to two
unknowns are identical to the previous proof: `1 in BC`, `AB<AC`, sizes 5,5,6,
and

```text
(aX+b)W_AB + (cX+d)W_AC + W_BC = 0.
```

The two reduced columns are independent by coprimality of the two degree-five
root polynomials. The main loop solves a nonzero two-by-two minor using its
adjugate, then checks every remaining coefficient equation by multiplying
through by the determinant. It uses exact Python integers with reduction
modulo P. It does not run Gaussian elimination or compute modular inverses for
each partition.

| Result | Count |
|---|---:|
| Normalized partitions exhaustively checked | 378378 |
| Nonzero syzygies | 0 |
| Exactly-two pair-cover seeds | 0 |
| Degree-five/six root polynomials checked at all sixteen nodes | 12376 |
| Independent original 7-by-5 Gaussian rank checks | 411 |

The independent rank checks cover the first 32 partitions and every 997th
partition. They are a deterministic sample; the reduced-equation enumeration
itself covers every partition. Every sampled original matrix has rank five.

Reproduce from the repository root:

```sh
python3 scripts/probes/astra_mca_paircover_production.py
```

The JSON receipt includes the complete domain, source field constants, counts,
and any witnesses. The successful result is a finite computation, not a Lean
certificate or an executable prize submission.

## The circle-real observation and its current limit

There is a valid necessary observation in characteristic zero. Suppose
`h=P/Q` has degree at most d and takes values in `{0,1,infinity}` at every
n-th root of unity, with `n>2d`. Cancel common factors first, and define
degree-d reciprocal conjugates

```text
P*(z)=z^d conjugate(P(1/conjugate(z))),
Q*(z)=z^d conjugate(Q(1/conjugate(z))).
```

The polynomial `P Q*-P* Q` has degree at most 2d. It vanishes at every n-th
root: the values 0 and infinity are covered by the corresponding zero
numerator or denominator, and value 1 gives P=Q and P*=Q*. Therefore this
polynomial is identically zero, so h is real-valued on the entire unit circle
where finite, with its poles interpreted in the real projective line.

That observation alone is not a lower-degree obstruction: many low-degree
rational functions are real on the circle. This round establishes neither a
general degree lower bound `d>=n/2-1` for power-of-two domains nor a counterexample
to such a bound. A further theorem using the cyclotomic spacing would be needed.
The finite computations above must not be presented as proving that theorem.

The new exclusion concerns n=16 in this one characteristic. It does not exclude
other positive characteristics, larger domains in the same field, other fiber
sizes or degree budgets, or the new constructions discussed in the separate
pair-cover target. No fresh-hole attack or MCA over-budget count is produced
by this empty search.

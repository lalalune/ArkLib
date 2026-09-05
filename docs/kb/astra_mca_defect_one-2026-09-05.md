# A length-sixteen exclusion for three private factors with one missing node

There is no partition of the fifteen nonidentity sixteenth roots in the
certified production field into three degree-five root polynomials having
a nontrivial constant linear relation. An exhaustive exact census checks
all 126,126 unordered partitions. A cyclotomic norm argument extends this
bounded exclusion to characteristic zero and every prime
`p > 400^8 = 655360000000000000000` with `p=1 mod16`.

This is a length-sixteen result, not an exclusion at length `2^30`. The
[two-private-triple problem](astra_mca_incidence_feasibility-2026-09-05.md)
has four missing nodes. A descent to the present one-missing-node case
has not been proved. The argument is written and independently reviewed;
the finite arithmetic is checked by Python, not Lean.

## The precise finite problem

Use the field and generator certified in the
[production-count receipt](astra_mca_production_count-2026-09-05.md):

```text
P = 365375409332725729550921208179070755120141565953
G = 303645430271030343624574566109998498685964493478
g = G^(2^30/16), of exact order 16.
```

Partition `mu_16 \ {1}` into three sets of five roots and let A,B,C be
their monic root polynomials. Any nonzero constant relation among them
has all three coefficients nonzero: two different monic root polynomials
cannot be scalar multiples. Their common leading coefficient then puts
the relation in the form

```text
C = (1-alpha)*A + alpha*B,       alpha not in {0,1}.
```

Thus the coefficient vectors `B-A` and `C-A` must be proportional.
For each unordered partition the checker finds the highest nonzero
coefficient of `B-A` and tests all two-by-two minors against that pivot.
It uses modular integers throughout.

To enumerate each partition once, choose A to contain the first node,
then choose B to contain the first remaining node; C is the complement.
The number of choices is

```text
binomial(14,4)*binomial(9,4) = 126126.
```

Every pivot is in degree four and every partition has a nonzero minor.
The same procedure at length four, degree one, finds the expected single
partition and a nontrivial relation. This positive control guards against
an implementation that simply rejects every relation.

## Cyclotomic norm extension

Let zeta be a primitive complex sixteenth root and work in
`O=Z[zeta]`, whose field has degree eight over Q. Lift each root-label
partition to monic polynomials in O[X]. Specializing zeta to g gives the
finite-field polynomials in the census. Since one minor of each partition
is nonzero after specialization, that algebraic-integer minor is nonzero
in O. Consequently the three polynomials are linearly independent even
over an algebraic closure of Q.

The pivot also has an independent explanation. If the sums of the roots
of disjoint five-element sets A and B were equal, independence of
`1,zeta,...,zeta^7` would force the signed root-membership coefficients
`c_j=c_(j+8)`. Since the sets are disjoint, each set would consist of
antipodal pairs. That is impossible for a set of odd size five.
Each conjugate of the nonzero sum difference has absolute value at most
ten, so its nonzero norm has absolute value at most `10^8 < P`.
It therefore remains a valid degree-four pivot at the production prime.

For a monic polynomial with five roots on the unit circle, its degree-j
coefficient has absolute value at most `binomial(5,j)` at every complex
embedding. A degree-four coefficient difference is at most ten, and any
other coefficient difference is at most twenty. Hence each conjugate of
the selected nonzero two-by-two minor has absolute value at most

```text
10*20 + 10*20 = 400.
```

Its nonzero integer norm has absolute value at most `400^8`. If the minor
vanished under a specialization `O -> F_p`, the corresponding prime
ideal would divide it and p would divide its norm. This is impossible for
`p>400^8`. Thus every partition stays independent in those fields, for
every primitive choice of root. The conclusion also holds after field
extension, since a nonzero minor remains nonzero. No claim is made about
the smaller exceptional primes. Rotation gives the same exclusion when
any other single root is omitted instead of 1.

## Relation to the open production problem

The actual two-triple configuration would give private polynomials of
degree `(2^30-4)/3`, with product `(X^(2^30)-1)/D` up to a nonzero scalar,
where D has degree four. If all four factors descend through `X^4`, the
resulting length is `2^28`, with one missing node. That length remains
uncontrolled by this census. At length 64 the same hypothesized descent
would reach the excluded length-16 case, but it is not valid to assume
that descent even at length 64.

This is also distinct from the earlier degree `(5,5,6)` pair-cover census:
here all three degrees are five, one node is missing, and the relation
has constant coefficients. Neither bounded computation solves the
universal predecessor bound or supplies a prize submission.

## Reproduction

```sh
python3 scripts/probes/astra_mca_defect_one_check.py
```

The deterministic output is archived in
`scripts/probes/receipts/astra_defect_one_20260905.json`.
The checker verifies root orders, partition cardinalities, the positive
control, every rank test, and the displayed integer norm bound. Primality
of P is supplied by the existing exact field certificate linked above;
the norm argument is a separate mathematical proof.

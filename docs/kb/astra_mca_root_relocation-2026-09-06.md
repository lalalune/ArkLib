# A production MCA construction with n+8 bad scalars

The exact six-seed construction below supplies at least

    1073741832 = 2^30+8

distinct MCA-bad scalars at the production field, domain, and code dimension, with exact agreement support size 718064844. Its radius is

    delta = 355676980/1073741824
          = 53/160 + 1/(20*67108864).

The scalar count divided by the production prime is strictly greater than 2^-128. This is a written unsafe-radius construction supported by exact seed arithmetic and independently checked dense controls. It is not Lean-formalized, and does not determine the exact optimal radius. This construction is a general MCA received line; it is not an over-budget instance of the separate single-hole value family.

For the repository's supremum convention, the conclusion is

```text
epsMCA(C,355676980/1073741824) >= 1073741832/P > 2^-128,
mcaDeltaStar(C,2^-128) <= 355676980/1073741824.
```

## Exact source data

Let

    P=365375409332725729550921208179070755120141565953,
    g=303645430271030343624574566109998498685964493478,
    n=2^30, s=n/16=67108864, k=n/2=8s, eta=g^s.

The six degree-at-most-seven polynomials f_i are supplied explicitly in [the exact seed certificate](../../scripts/probes/astra_mca_root_relocation_seed.json). The exact checker verifies the order of g, every equality partition below in the actual field, all six distinct values at 1, and

    gcd(f_i-f_0 : i=1,...,5)=1.

The [existing production certificate](../../ArkLib/Data/CodingTheory/ProximityGap/Frontier/_PrizeShapePrimeP30.lean)
supplies primality and the domain generator order. Set W_i=f_i-f_0. Here
W_0=0 and the other five W_i have degree seven. The coefficient data and
their finite-field checks are the input certificate; no unproved existence
of suitable seeds is assumed.

## A parameterized domain allocation

Take an integer a such that the following counts are nonnegative, and write

    z0=3a-2, z12=s-3a, U=s-4a+2.

Partition the domain into its sixteen actual fibers X^s=eta^j, each of size s. Within each fiber use the order x=g^(j+16t), 0<=t<s, so the allocations below specify particular field points.

Choose a set Z of common roots by taking the first z0 points in fiber 0 and the first z12 points in fiber 12. Its size is

    |Z|=z0+z12=s-2.

Define the actual split polynomial

    B(X)=product_(z in Z)(X-z),
    p_i(X)=B(X)*W_i(X^s), q_i(X)=X*p_i(X).

These are code polynomials: deg p_i<=s-2+7s=8s-2=k-2 and deg q_i<=k-1. At every common root all six pairs equal (0,0).

At the remaining nodes allocate joint ownership as follows. An owner group means all indicated pairs have the same value there; the checker verifies that it is exactly a full equality class of the six seed values.

| Fiber | Non-root ownership and uncovered nodes |
|---|---|
| 0 | owner {5} on a points; U points uncovered |
| 1 | {0,1,2,4} on all s points |
| 2 | {0,1,2,3,5} on all s points |
| 3 | {2,3,4} on all s points |
| 4 | {1,3,4} on all s points |
| 5 | {0,5} on all s points |
| 6 | {0,2,3,4,5} on all s points |
| 7 | {0,1,3,4,5} on all s points |
| 8 | {0,1,2,3,5} on all s points |
| 9 | {0,1,2,4,5} on all s points |
| 10 | {0,1,2,3,4} on all s points |
| 11 | {2,3,4,5} on all s points |
| 12 | {0}, {1,3}, {2,4}, each on a points |
| 13 | {1,2,5} on all s points |
| 14 | {0,2,3} and {1,4,5}, each on s/2 points |
| 15 | {0,1,3,4,5} on all s points |

At a common root set the received pair to (0,0). At a covered non-root node set it to the value of an indicated owner. On each of the U uncovered nodes choose a received pair by the fresh-direction construction below. Consecutive blocks in the stated fiber order determine the owner sets uniquely if a fully deterministic word is desired.

Each pencil receives 9s core points from the thirteen unsplit nonexceptional fibers, s-2 common roots, s/2 points from fiber 14, and a points from fiber 0 or 12. All six exact joint cores therefore have size

    A = 21s/2-2+a.

The cores are exact: away from B's roots the owner groups are the exact seed equality classes, and each uncovered received value is chosen off every local pair.

## Ordinary and fresh cancellation directions

At a covered non-root node x the local pairs have the form (z,xz). There are at least two distinct z values at every fiber, as verified by the exact equality partitions. A nonowner residual is nonzero and proportional to (1,x), so it cancels at gamma_x=-1/x. The domain nodes are nonzero and these scalars are distinct. The ordinary count is

    n-(s-2)-U = 15s+2-U.

At every uncovered node, which lies in fiber 0, all six local values z are distinct. To obtain six fresh directions, let Gamma contain all ordinary directions and
all previously selected fresh directions. Choose a field element v different
from the six values x*z. Then choose u outside the forbidden set

    {v/x} union {(1+gamma*x)*z-gamma*v : gamma in Gamma, z local}.

There are at most 6*|Gamma|+1 forbidden values. At the actual production
parameters P>6*D+1, so this choice exists throughout the finite induction.
The received pair (u,v) is off the local line because v!=x*u. Its six finite
cancellation scalars are

    gamma_z=(z-u)/(v-x*z).

The denominators are nonzero by the choice of v. Two distinct z values
would give equal scalars only if v=x*u, which was excluded. Membership in
Gamma is excluded by the definition of the forbidden set. This proves
six new distinct finite scalars at each uncovered point.

This is an unconditional finite choice. Choosing the least allowed canonical
field representative at each step makes the received word completely
specified. The primary checker uses an equivalent choice that avoids the
entire reciprocal image of the domain; the independent checker uses the
forbidden set above. Neither proof assumes random success or a production
field scan.

The total number of distinct certified scalars is consequently

    D = 15s+2-U+6U = 20s+12-20a.

For every counted scalar choose a corresponding local pencil and append its cancelling non-core node to the full A-point exact core. This gives exactly A+1 agreements. A joint pair of degree less than k on the same support would equal the local pair on its A>=k core nodes, by the polynomial root bound. It would then fail at the displayed nonzero residual. Thus every scalar is an event in the original same-support/no-joint MCA definition, against the full code.

## Production choice and improved unsafe radius

At

    a=floor((4s+11)/20)=13421773,

the integer allocation is

    z0=40265317, z12=26843545, U=13421774.

It gives

    A=718064843, A+1=718064844,
    ordinary directions=993211188,
    fresh directions=80530644,
    D=1073741832=n+8.

The prime satisfies P=n*(2^128+192)+1. Hence

    (n+8)*2^128-P = 8*2^128-192n-1 > 0.

The constructed received line therefore has MCA error strictly greater than 2^-128 at radius (n-A-1)/n=355676980/1073741824. It supplies an unsafe-radius upper bound in the written mathematics; the exact threshold remains undetermined.

For comparison, the predecessor core A=715827883 corresponds to a=11184813 and gives D=1118481032, exceeding n by 44739208. Increasing the core by 2236960 consumes this excess while still leaving eight additional scalars.

## Exact optimality of this core parameter within the fixed source family

There is a short dual certificate showing that arbitrary different owner assignments or common-root placements with these same six source polynomials and deg B=s-2 cannot improve the core threshold while keeping more than n scalars from these six pencils.

Let I={0,1,2,5} and assign fiber weights

    beta=(6,16,21,6,6,11,16,16,21,21,16,11,6,16,11,16).

Their sum is 216. Exact enumeration of the sixteen seed partitions verifies three inequalities in every fiber j:

* beta_j is at least the number of distinct local values;
* beta_j>=6;
* beta_j>=1+5*|S intersection I| for each possible owner group S.

At a non-root uncovered node the number of distinct local cancellation directions is at most its number of local values. At a covered node it is at most one and the selected core credits are exactly |S intersection I|. At a common root, either all six pairs jointly agree, giving selected credit four and no nonzero residual, or none does and at most one scalar occurs. These inequalities therefore give, point by point and then after summation,

    D + 5(C0+C1+C2+C5) <= 216s + 14 deg B.

Here D is any union of scalars supplied by the six selected pencils, bounded by the sum of their node-wise cancellation counts, and C_i are their exact joint-core sizes. If all C_i>=A and deg B=s-2, then

    D <= 230s-28-20A.

The displayed construction attains equality. Requiring D>=n+1 gives

    A <= floor((214s-29)/20)=718064843.

Increasing A by one would give the upper bound D<=n-12. This is optimality within the fixed six-source, common-factor family with all six cores at least A. It does not bound other sources, other degree allocations, additional decoding pencils, or the true optimal MCA radius.

## Exact controls and verification status

Run from the repository root:

```bash
python3 scripts/probes/astra_mca_root_relocation_check.py
python3 scripts/probes/astra_mca_root_relocation_independent_check.py
```

The [primary checker](../../scripts/probes/astra_mca_root_relocation_check.py)
uses the exact seed fixture and has no LP dependency. It verifies the source
partitions, common gcd, degree bounds, every integer allocation and core
count, strict security inequality, and every local inequality in the dual
certificate. Its dense controls build the actual product B and all six
polynomial pairs at lengths 1024 and 4096 over P, construct the complete
received words, and check every coordinate of every claimed scalar support.
The counts are 1032 and 4112 distinct finite bad scalars respectively.

The [independent checker](../../scripts/probes/astra_mca_root_relocation_independent_check.py)
embeds its polynomial fixture separately and imports no repository probes or
LP routines. It independently expands B, verifies its exact domain roots,
expands all source polynomials, constructs the full received pairs using
finite avoidance, and checks every outside cancellation and exact joint
core at both control lengths. It also checks both production parameter
choices and their strict security margins using integers.

Independent agent review found no gap in the construction, finite-field
choices, degree argument or same-support MCA bridge. This is not external
human review or Lean formalization. Production validity follows from the
written algebra and exact fixed-degree certificate; the production domain
and received word have not been fully expanded. The displayed D need not
be the complete bad-scalar set of the constructed line.

The [primary receipt](../../scripts/probes/receipts/astra_root_relocation_20260906/primary.json),
[independent receipt](../../scripts/probes/receipts/astra_root_relocation_20260906/independent.json)
and [SHA256 manifest](../../scripts/probes/receipts/astra_root_relocation_20260906/manifest.json)
are retained with the proof and source data.

This improves the earlier [computational unsafe radius](astra_mca_production_count-2026-09-05.md)
by 2236961 integer error steps. The previous
[Lean upper-bound theorem](astra_mca_production_upper-2026-09-05.md) remains
at its earlier, weaker radius. A Lean formalization of this new construction,
a matching universal lower bound, and the grand prize problems remain open.

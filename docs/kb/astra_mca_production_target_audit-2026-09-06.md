# Audit of the former production target — 6 September 2026

This records an audit performed before the
[common-root relocation construction](astra_mca_root_relocation-2026-09-06.md).
That subsequent construction refutes the predecessor safety statement
discussed below and improves the unsafe radius to `355676980/1073741824`.
The archived count review and arithmetic bounds below remain valid; the
old predecessor is no longer a candidate for a universal safe bound.

No defect was found in the stated computational upper bound. The missing
predecessor cap would pin the repository's supremum exactly, but would not
make the boundary radius safe. No applicable published lower bound was found
in the primary sources checked below. Two exact arithmetic gates show that
the recent MDS envelope and agreement-shortening bounds are trivial at this
particular production target; this does not exclude other uses of their ideas.

## Count, bridge, and provenance

Current checkout inspected at b894e46195f0f206e5d481dd6339db37fedbd7af.
The production computation is pinned separately to source commit
5ec32fa23607ec7a205dc3a17cd0f8cd1c71a402, native SHA256
6b2069e47e698fa96100881eb81175e6acdd8d60d5e0b24a19682817ffa117a5,
and hosted run 33941607360. I inspected the source at that revision, including
canonical field normalization, fingerprinting, slot indexing, parallel block
coverage, and the successful legacy `--scan` count path. I also reran the
lightweight archive/field checker successfully; the billion-slot scan was
not replayed. The binary and billion-slot array are not retained, so this
remains a reviewed finite execution plus proof, not a Lean certificate.

The fixed coordinate change is (u0,u1) -> (u0,u0+u1), of determinant one.
It preserves polynomial degree and all joint cores. Each nonzero residual
(a,b) then cancels at gamma=-a/(a+b), provided a+b!=0. The recorded zero pole
count makes every recorded slot finite in this one common chart.

The hash is one deterministic function of the full canonical field value.
Thus equal scalars necessarily hash equally. Distinct hashes give a lower
bound on distinct scalars, with no probabilistic collision assumption.
The receipt has n+1 distinct hashes among n+2 finite slots: the actual scalar
count is n+1 or n+2. Resolving the one tied hash could improve this count,
but cannot improve the radius because the supports have the same size.

Write n=1073741824, k=536870912, a=(n-1)/3=357913941,
s=n-a=715827883, and P=n(2^128+192)+1. Each local pair has an exact joint
core of size s-1=715827882>=k. Its residual scalar adds an outside node,
producing a support of size s. A jointly explaining pair on that SAME support
would equal the local pair by uniqueness on the core, contradicting its
nonzero residual at the added point. This matches `mcaEvent` in Errors.lean;
plain scalar proximity alone would not suffice.

The exact security budget is floor(P/2^128)=n, and

    (n+1)2^128-P = 340282366920938463463374607225609781247 > 0.

Hence epsMCA(C,a/n)>2^-128 and mcaDeltaStar<=a/n. There is no missing union
bound: all directions use one fixed received pair, and epsMCA takes the
worst case over received pairs.

## Supremum versus largest safe lattice radius

At radius delta, the integer error allowance is floor(n delta). Suppose the
universal predecessor statement is proved:

    every received pair has at most n bad finite scalars
    at S=715827884 agreements, i.e. delta_prev=(a-1)/n.

Then every real delta<a/n is safe, by monotonicity and the constant event on
each Hamming interval. Every delta>=a/n is unsafe by the already constructed
witness. The exact safe set would therefore be [0,a/n), giving

    repository supremum:              a/n;
    largest safe Hamming-lattice point: (a-1)/n;
    safety at the supremum itself:      false.

This is exactly the role of
`latticeBoundary_le_mcaDeltaStar_of_predecessor_good` in the repository.
A cap n-1 is stronger than needed; n is the correct target.

The [official challenge](https://proximityprize.org/) uses the phrase
"largest" over real radii with a closed-distance security condition. That
literal wording needs a supremum or lattice convention when the safe set is
half-open. The repository has already chosen the supremum convention. A future
result should report the safe set and the two numbers above, avoiding an
assertion that its unsafe endpoint satisfies the security inequality.

## Primary literature checked and exact hypothesis mismatches

The following is an applicability audit, not a full proof review of these
external papers, nor a claim that the literature search is exhaustive.

1. [Bordage–Chiesa–Guan–Manzur, CCC 2026](https://drops.dagstuhl.de/storage/00lipics/lipics-vol383-ccc2026/LIPIcs.CCC.2026.24/LIPIcs.CCC.2026.24.pdf),
   Theorem 5: arbitrary evaluation sets and the correct MCA event, but its
   radius is at most 1-(1+1/(2m))sqrt(rho), m>=3. The production predecessor
   is strictly beyond even the exact degree-cap Johnson boundary. The paper
   also discusses a general list-to-MCA transfer with output radius below
   1-sqrt(1-delta_list); even hypothetical list decoding to half-rate capacity
   only reaches Johnson through that transfer. Our target would require
   delta_list>2 delta_prev-delta_prev^2>1/2. This does not exclude a new
   stronger transfer exploiting the RS witness equations.

2. [Goyal–Guruswami–Sun–Wootters, July 2026](https://arxiv.org/html/2607.08516v1#S5.SS2),
   Theorem 5.6: random evaluation points, not the prescribed multiplicative
   subgroup. Its displayed MCA numerator is
   ell*n*ceil((1-R)/eta)+O(ell^2/eta^3), with R<=1-delta-2eta.
   At ell=1 and our target, even the smallest displayed integer multiplier
   is six, above the required numerator n. This theorem supplies neither
   the deterministic code hypothesis nor the required finite constant.

3. [Jo, August 2026 revision](https://eprint.iacr.org/2026/1432): arbitrary
   prescribed domains, but the stated polynomial result concerns a fixed
   number h of integer steps beyond Johnson, with O_(r,h)(K^6) numerator
   for sufficiently large K. Here the predecessor is 43,422,241 steps beyond
   floor(n-sqrt(n(k-1))). The explicit shortening transfer underlying that
   result is separately excluded as a useful bound below; one cannot insert
   this huge h into an unspecified asymptotic constant.

4. [Chojecki, Shortening Bounds](https://eprint.iacr.org/2026/1463), checked
   against the [author's full source](https://github.com/przchojecki/rs-mca/blob/main/RS_MCA_Paving_v9.2.tex):
   the exact linear-budget theorem assumes B*-1 <= ((1-rho)/2-eta)n for
   positive eta; B*=n fails that hypothesis at rho=1/2. The positive-radius
   shortening theorem pays a positive exponential factor. At rho=1/2,
   delta=1/3 its exponent is H2(1/3)-2/3, about 0.251629 per coordinate,
   whereas the usable production budget has only 30 bits total. The two
   exact finite bounds in this source are audited immediately below.

5. [Brakensiek–Chen–Putterman–Zhang–Zheng, 5 September 2026 revision](https://eccc.weizmann.ac.il/report/2026/164/revision/1/download),
   Theorem 4.1 and Corollary 5.1: scalar RS over prime fields and arbitrary
   prescribed domains, but not a concrete MCA numerator bound. I checked
   the stored primary PDF (SHA256
   560e7134e49abc065718bf97a50c20b1cce7eba9d7b465b98a64be90dd88d903).
   Its explicit construction requires eta<2^-60 and derivative order
   d>2^180, hence padded dimension and field >2^180; P<2^159.
   The padding agreement requirement fails as well at n=2^30. This matches
   the repository's earlier finite-parameter audit. An existential polynomial
   list bound does not supply an n-sized value image or the same-support MCA
   bound. This is a quantitative limitation, not a refutation of the paper's
   asymptotic result.

## Exact finite obstruction to the published direct envelopes

Put A=715827884 and E=n-A=357913940.

### All-test-size MDS envelope

The published bound is

    min(P, min_(k+1<=b<=A) floor(C(n,b)/C(A-1,b-1))).

For U_b=C(n,b)/C(A-1,b-1),

    U_(b+1)/U_b = b(n-b)/((b+1)(A-b)),

which exceeds one whenever b(n-A+1)>A. This holds already at b=k+1,
so the inner minimum is U_(k+1). Moreover

    U_(k+1)=n/(k+1) * product_(j=0)^(k-1) (n-1-j)/(A-1-j).

Each factor exceeds 7/5. There are more than 400 factors, and the exact
integer comparison 7^400>P*5^400 proves U_(k+1)>P. Thus the complete
all-test-size envelope reduces exactly to the trivial field cap P here.
This conclusion bounds the certificate's output, not the actual bad set.

### Agreement-set shortening to a Johnson-safe code

The transfer gives

    B_C(A) <= C(n,t)/C(A,t) * max_(|T|=t) B_(C_T)(A-t),
    0<=t<k.

The shortened code is Johnson-safe only if

    (A-t)^2 > (n-t)(k-t-1).

Expanding, the difference equals

    A^2-n(k-1)+t(n+k-1-2A).

Its least positive integer solution is exactly t=357913932. For every such
t, the binomial ratio has at least 400 factors, each at least n/A>7/5;
therefore its value exceeds P. Any universal shortened-code bad-numerator
bound is at least one: a proper linear code always has a one-scalar bad line
by taking (u0,u1)=(-gamma0*r,r) for r outside the code, and using the whole
domain. Hence even a hypothetically optimal universal bound of one inside
this displayed transfer cannot beat the field cap P. A direct application
of the published transfer cannot certify the target n.

No large binomial or domain enumeration is needed. The standalone
[`production target checker`](../../scripts/probes/astra_mca_production_target_check.py) certifies the strict security margin, exact Johnson
floor, minimum shortening, both 400-factor comparisons, random-code
multiplier, generic list-to-MCA radius mismatch, and capacity-parameter
inequalities using integers and rational arithmetic. Run it with `python3 scripts/probes/astra_mca_production_target_check.py`;
it prints its exact receipt as JSON.

## Consequence at the time of this audit

The unsafe construction already has enough scalars at its agreement level.
Resolving a hash tie or adding further scalars on those same supports does not
sharpen the radius. To improve the upper bound, a new construction must reach
at least 715827884 agreements for at least n+1 finite scalars. The independent
local-repair result restricts the old three pencils, but does not exclude new
pencils or decoders abandoning many old core points.

To prove equality of the repository's threshold, the precise remaining target
is the universal cap n at that same agreement level. None of the inspected
literature gives it directly, and the explicit direct bounds tested above
cannot do so. The production upper bound and its source/provenance limitations
were correctly stated at the inspected commit. The later relocation result
supplies the new construction at a strictly stronger agreement level, so
proving the former predecessor target is no longer possible.

# Proximity Prize research receipt — 4 September 2026

**The grand prize problems remain unsolved in this work.** This session produced
exact finite-instance certificates, a sharper character-sum remainder bound,
a companion parameter search with open proof obligations, and a repair to a
verification wrapper that could falsely report success. Nothing was submitted
to a prize organizer. Verification status is recorded separately below.

**5 September update:** the full billion-slot
[production count](../kb/astra_mca_production_count-2026-09-05.md) completed,
giving at least 1,073,741,825 finite MCA witnesses for the explicit rate-one-half
construction. Together with the written bridge this sharpens its threshold
upper bound to `357913941/2^30`. The matching universal lower bound is open;
this is a computational result, not a newly Lean-verified threshold theorem.

The [single-hole reduction](../kb/astra_mca_single_hole_reduction-2026-09-05.md)
also identifies a necessary subproblem for the universal bound: controlling
the distinct extrapolated values of a punctured RS list. Rational collinearity
of its joint cores and a rank-three error Gram matrix do not supply that cap.
An independently checked [six-square countermodel](../kb/astra_mca_six_square_countermodel-2026-09-05.md)
rules out extending the degree-two cover argument using square-resultant
conditions alone. Its common-domain requirement fails, so the actual
six-pencil MCA question remains open.
The [incidence feasibility result](../kb/astra_mca_incidence_feasibility-2026-09-05.md)
supplies common-domain absence set systems at the production parameters;
their polynomial realization still requires two compatible private-locator
identities. Counting those set memberships alone cannot finish the exclusion.

The [locator-pencil bound](../kb/astra_mca_locator_pencils-2026-09-05.md)
now caps each two-dimensional valid locator family at four distinct values,
with an exact realization converse and a sharp three-value coset construction
on the production domain. The full family need not lie in one pencil.
Two bounded cyclotomic censuses exclude a cubic four-member pencil and a
[degree-five private triple](../kb/astra_mca_defect_one-2026-09-05.md) on
sixteenth roots. Their large-characteristic extensions use explicit norm
bounds; neither excludes arbitrary production configurations.
An [elementary Cartier identity](../kb/astra_mca_cartier-2026-09-05.md)
gives additional necessary equations and an exact control showing why its
undeleted-domain cutoff cannot be transferred to a quartic deletion.
The [sharper contact estimate](../kb/astra_kernel_channel_hermite-2026-09-05.md)
also remains too weak to exclude the binding companion factor. These are
written proofs and exact finite checks, not new Lean proofs or prize closure.

A [rank-two far-line construction](../kb/astra_far_word_kernel-2026-09-05.md)
shows that farness does not repair the quotient-dimension comparison by
itself: the actual companion field still permits a contact subspace of
dimension 10121888390. It has no high-agreement family, identifying a
hypothesis the next estimate must use. A separate
[finite audit of the September 5 capacity preprint](../kb/astra_capacity_finite_gates-2026-09-05.md)
finds that its published parameter construction cannot fit our field or
length, and its stated list bound does not meet the numerical prize budget.
The external asymptotic result and its derivative method retain their own
scope; this audit supplies no prize solution.

The [contact-variation audit](../kb/astra_contact_variation-2026-09-05.md)
now gives a full-kernel countermodel to a general multiplicity-two shortcut:
three exact F17 examples have one-dimensional contact kernels, a genuine bad
MCA seed, and simple intersections of the first two tails. Their factor has
R degree one, so the binding C2 case remains open. The new examples also
have no nonzero polynomial Jacobi variation, illustrating why the existing
rigidity lemma does not imply a multiplicity improvement. These are written
arguments and finite checks, not new Lean proofs.

For the single-hole branch, the
[reduced exact-error algebra](../kb/astra_mca_exact_error_eliminant-2026-09-05.md)
removes padded locators and extra algebraic multiplicities. Its value
operator has a squarefree minimal polynomial whose degree is exactly the
number of distinct decoded values. Proving that degree at most n for every
received word remains the unresolved quantitative step.

The [large-field projection argument](../kb/astra_interleaved_projection-2026-09-05.md)
now preserves an exact scalar list budget B under every positive interleaving
arity when `binomial(B+1,2)<=q`. Both fixed field/budget profiles pass that
gate. It also preserves a uniform bound on linear-observable images, such
as omitted-point values, at the image level. This is a useful conditional
transfer, not a proof of either underlying scalar bound. The elementary
proof was independently reviewed and the finite projection/list controls pass.
The full-list equivalence and three field-size gates now pass Lean on both
pinned versions in [CI run 33970050552](https://github.com/lalalune/ArkLib/actions/runs/33970050552),
with nine clean new axiom reports per job. The linear-observable variant
remains a written result; no scalar production estimate or MCA bound follows
from the transfer alone.

The [order-two Hasse calculation](../kb/astra_hasse_order_two-2026-09-05.md)
provides an exact local-rank formula and a strict finite interpolation gain
at length 64: the stated order-two box passes at 34 agreements, while all
order-one slope caps with the fixed multiplicity and total cap first pass at
35. This example is inside the Johnson regime. The same small box fails
at companion production size, and supplies no decoded-list bound.

An [exact root-product obstruction](../kb/astra_mca_value_operator-2026-09-05.md)
also rules out identifying the decoded-value operator with a function of the
error-root product. Actual production-domain witnesses have equal exact
error products and distinct extrapolated values; the F17 control has three
values while its product operator is scalar. A successful degree bound must
use more than that cyclotomic identity.

The [selected-graph Jacobi constraint](../kb/astra_selected_family_constraint-2026-09-05.md)
adds an exact divisor: every nonzero fixed-seed polynomial deformation g
forces the agreement contact locator to divide `(F_R|f)*g`. Thus contact
sum greater than c+1 forces fixed-seed rigidity. In the stated 33/57
profile this needs at least 7320 high-contact agreement nodes. That gate is
not automatic, and rigidity does not count isolated solutions or reduce
the companion budget excess.

The [exact-locator rank theorem](../kb/astra_locator_rank_bound-2026-09-05.md)
extends the pencil bound: at the punctured production parameter shape,
rank r bounds a decoded family by `4^(r-1)`, including heterogeneous error
degrees. A uniform rank bound of 16 would meet the scalar production budget;
that rank bound remains unproved. Three integer polynomial identities,
4464 rational endpoint cases, a sharp rank-two family, and a heterogeneous
rank-three control pass. The generalized proof has not had independent
agent review or a Lean kernel check.

The [carrier counting lemmas](../kb/astra_carrier_dimension_bound-2026-09-05.md)
give a different conditional route: a coefficient-space carrier of controlled
dimension and total degree bounds the scalar list by an explicit product of
incidence ratios. A separate recurrence respects MCA's same-support no-joint
condition; an actual affine plane containing one witness per bad scalar
would meet the predecessor budget with allowance n-13. No such universal
carrier is constructed. Exact finite scalar and MCA controls pass.

The [bounded production Hasse search](../kb/astra_hasse_production-2026-09-05.md)
now excludes a positive dimension certificate in all 1426 specified small
multiplicity/derivative-cap profiles, for every nonnegative total cap T.
An exact slice recurrence reduces the infinite T tail to its negative slope.
The earlier first-derivative source at m=166 is reproduced as a calibration;
it is outside this search. The exclusion does not prove that production
interpolants are nonexistent or rule out other interpolation shapes.

The [rank-profile follow-up](../kb/astra_hasse_rank_profile-2026-09-05.md)
finds positive second-Hasse sources outside that small family. At the actual
companion radius, m=80,S1=24,S2=6,T=1042 gives a guaranteed source nullity
of 653072574. One ordered elimination per homogeneous slice answers all
contact cutoffs, and an exact common-factor shift handles the higher slices.
The checker passes 4500 comparisons against the earlier block expansion,
reproduces the 1426-profile exclusion, and finds 123 positive profiles in a
specified 528-profile larger search. The lower-degree extra cut has an
attractive conditional mixed cost, but properness on the components being
counted is unproved. There is no improved MCA allowance or Lean theorem yet.

The [third-Hasse source](../kb/astra_third_hasse_source-2026-09-05.md)
reduces the original total cap to 915 at m=99,S1=30,S2=8,S3=1, with
guaranteed nullity 1033048571. Seven thousand direct block checks, a separate
second-order reproduction, and a sanitized run pass. Its cleared cut bound
is larger, and properness remains unproved; the one-variable minimal-polynomial
descent does not apply unchanged to the two-variable relation ideal.

The [full second-Hasse containment example](../kb/astra_hasse_containment-2026-09-05.md)
shows why that qualifier matters: its full second-order kernel is nonzero
while the matching first-order kernel is empty, but every pullback is
divisible by the old regular factor. Seven complete finite matrix and
polynomial-identity controls pass, including the companion characteristic
at small n,w. Its uniform dimension margin is nonpositive, so the example
does not settle the positive production case.

The [component split](../kb/astra_hasse_component_split-2026-09-05.md) now
allows the extra equation to contain entire first-tail curves. Properness
on the irreducible surface suffices for a written counting argument using
ordinary Bezout bounds and the existing weighted multiplicity certificate.
At cutoff M=2048, all four production extra-cut degrees fit the conditional
binding-cell budget. A seven-profile derivative-trimming test does not force
the missing degree separation. Surface properness, independent proof review,
Lean integration, and the full phase recurrence remain open.

The [positive-margin kernel controls](../kb/astra_positive_kernel_factor-2026-09-05.md)
give a complete first-order kernel of dimension one despite a strictly
positive uniform margin. Its universal regular factor has a genuine bad
seed and simple selected tails. Four full-matrix calculations agree with
independent 4-by-5 Hermite reconstructions, including at the companion
characteristic. The separate positive second-order source escapes this
factor in every control; production surface properness remains open.

The [root-safe filtration](../kb/astra_root_safe_filtration-2026-09-05.md)
reduces every positive trimmed second-order certificate to a positive
first-order coefficient-slice certificate. An exact bounded calculation
excludes that lower-R route for multiplicities through 500 and R caps below
ten, covering every D<=m*A and unbounded total degree. Actual kernels can
still exist, and the untrimmed second-order properness question stays open.

The [acceleration-extension criterion](../kb/astra_acceleration_extension-2026-09-05.md)
gives a sufficient condition for properness of an untrimmed source. After
normalizing the received direction, a parameter-independent primitive
equation cannot divide its full kernel. A field-degree argument then handles
binding factors whose acceleration has algebraic degree at most two, using
the T=1042 or T=1031 source. This degree hypothesis is not known in general.
Three finite full-kernel controls and extension-field rank checks pass;
independent review, Lean integration, and general properness remain open.

The [coordinate and jet-repair follow-up](../kb/astra_acceleration_chart-2026-09-05.md)
allows up to w-2 zero direction entries without changing coordinates.
It also checks that low acceleration degree is not automatic: three
positive full first-order kernels have irreducible universal factors of
acceleration degree six and relative degree one, with regular bad seeds.
The examples are finite and do not realize the binding production flag.

The [regularity-cube audit](../kb/astra_tail_regularity_cube-2026-09-05.md)
proves an exact H^3 factor in raw tails and tests its removal from the
counting argument. The resulting support bound has worse R degree and
increases the binding cost. A binding-degree surface has exactly order
three at the excluded regularity locus at both production tail indices;
it does not supply full interpolation-kernel provenance. No improved
prize bound follows from this correction.

The [fixed-word differential carrier](../kb/astra_scalar_differential_carrier-2026-09-05.md)
now supplies an actual curve and degree bound for the scalar companion
profile. Its written argument gives at most 12546010856 degree-at-most-131071
polynomials with 181353 agreements on 262144 nodes over characteristic
2130706433, uniformly over received words. This is below the F_(p^6) list
budget, and the same cap transfers to every positive interleaving arity.
Thirty-six direct local matrices, exact reconstruction of a complete small
list, singular/independent-R controls, and all production arithmetic pass.
Independent mathematical review and Lean formalization are outstanding.
The MCA bound, the companion ProtocolClaim, and the sharp thresholds remain
open; a fixed-word list bound does not settle them at the same radius.

The [scalar next-derivative split](../kb/astra_scalar_tail_split-2026-09-05.md)
improves that written list bound to 4812927256. A proper tail cuts out finitely
many points; an identically zero tail yields coefficient curves of total
degree at most the source degree when the characteristic exceeds D. The
companion satisfies this stronger condition. Exact power-curve controls over
three fields and a Frobenius counterexample to dropping the condition pass.
The general geometric argument is not independently reviewed or formalized,
and the MCA/prize inequality remains open.

The [explicit scalar-kernel certificate](../kb/astra_scalar_kernel_witness-2026-09-05.md)
adds a complete construction check beyond Johnson on 13 nodes over F17.
The actual 300-column map has rank 295; a retained nonzero source passes
all 13 independent contact expansions and reconstructs every member of an
exhaustive 4913-polynomial census. Four closed finite predicates also pass
the Lean kernel with no axioms. The general production carrier theorem
and MCA bound remain outside that finite certificate's scope.

## Revisions and environment

* Original clone: `/Users/nubs/Git/arklib`, clean `main` at
  `8e2fc19130e2fea9e175c52b0953b88804b8f333`.
* Research worktree: `/Users/nubs/Git/arklib-proximity-astra`, local branch
  `codex/proximity-astra-20260904`, based on research commit
  `54007b004040a9cd0964dcb0a2413e86bc60ae8d`.
* Both source branch heads were rechecked against the remote on 5 September
  and remain at the revisions above.
* This Codex session's local metadata identifies `gpt-6-astra`, effort `ultra`.
* On the user's explicit follow-up authorization, the initial research was
  committed and pushed as `335b4a0e1`. Reviewed remote contribution
  [PR #542](https://github.com/lalalune/ArkLib/pull/542) was then cherry-picked
  with its original authorship preserved and pushed as `390c9e0f9`.
  The sharper remainder proof was pushed as `9fc80e92b`, and the kernel-checked
  finite certificate as `736d38cf2`.
* The source `main`, source `research/proximity-prize`, and pinned official
  companion heads had no new commits on the follow-up fetch. Open
  [PR #543](https://github.com/lalalune/ArkLib/pull/543) was inspected but not
  incorporated: it adds mechanical finite parameter checks without the missing
  structural estimate.
* The host initially had no `lean` or `lake`. A minimal official Lean
  `4.30.0-rc2` runtime was subsequently extracted under
  `/tmp/arklib-lean-bootstrap`, after checking the release asset's SHA-256.
  This supports core-only verification; the full Mathlib/ArkLib environment
  is still unavailable under the host's limited free disk space.

## Results and limits

| Result | Evidence | Limit |
|---|---|---|
| Complete order-eight, threshold-four monomial census is uniform in every odd-characteristic field with an eighth root of order eight; maximum nine | Exhaustive arithmetic in `Z[z]/(z^4+1)`; all relevant nonzero norms are powers of two | 64 monomial pencils, not arbitrary received-word pairs |
| Lean kernel accepts the complete finite monomial arithmetic predicate | Ordinary `by decide`, `import Std`, exit zero; axiom audit `[propext]` | Field-specialization and MCA interpretation remain written proofs |
| Explicit nonmonomial pencil has exactly ten bad scalars for every prime `p=1 mod8` outside six explicit exceptions | Cyclotomic norm certificate and exhaustive exceptional-field census | One constructed family, not the full MCA maximum |
| That construction has eleven scalars in specified `F41` and `F137` cells | Independent enumeration of scalar and affine-polynomial witnesses | Finite cells; generator choice matters for the constructed words |
| Cubic/quadratic ceiling count 40 and witness multiplicity profile follow by assembling G330 with existing generic lemmas | Written proof and an explicitly uncompiled Lean candidate | Existing lemmas assembled; no new kernel verification |
| CLM-043 remainder coefficient improves from 87 to 24, including arbitrary distinct nonzero evaluation sets over odd finite fields | Ordered-overlap proof using classical Hasse; six frozen cells and 581 additional subgroup cases | The main term `U` remains unbounded; this proof is not Lean formalized |
| Initial companion candidate 68.03 passes interpolation dimensions but fails the regenerated coarse factor budget | Published baseline reproduced exactly; candidate charge `274912523147183536` exceeds allocation `260136176662196960` | Positive interpolation nullity alone does not establish soundness; tighter variants remain research |
| Exact best product-label marginal cannot rescue the 256-fibre attack candidate | Subset-sum DP and independent Ramanujan formula agree on every label | Does not rule out concentration in the joint coefficient/product map |
| Quiet proof wrapper now propagates compiler failure | Reproduced missing-compiler false success, then 14 process-boundary checks | Process handling only, not mathematical validation |

The monomial result's extension-field coverage was independently checked using
all scalars and affine codewords in `F9` and `F25`. Its full 8-by-8 matrix was
also independently checked in prime fields. The nonmonomial construction gives
a uniform lower bound of ten at arbitrarily large fields, so its separation
from the monomial maximum is not solely a small-characteristic effect.

Proofs, exact definitions, reproduction instructions, and qualification of the
remaining obligations are in:

* [Monomial census](../kb/proximity-astra-monomial-census-2026-09-04.md).
* [Lean kernel verification and reproduction](../kb/astra-core-certificate-2026-09-04.md).
* [Explicit nonmonomial construction](../kb/proximity-astra-nonmonomial-witness-2026-09-04.md).
* [Nonmonomial census and complete exceptional table](../kb/proximity-astra-nonmonomial-exact-2026-09-04.md).
* [Ceiling assembly and audit of historical claims](../kb/proximity-astra-ceiling-bridge-2026-09-04.md).
* [Sharper CLM-043 remainder and its precise scope](../kb/proximity-astra-clm043-remainder-2026-09-04.md).
* [Companion target and parameter audit](../kb/proximity-astra-companion-2026-09-04.md).
* [Exact product-marginal obstruction](../kb/proximity-astra-orbit-product-marginal-2026-09-04.md).

## What prevents a prize claim

The [official grand challenges](https://proximityprize.org/) concern worst-case
MCA and interleaved list-decoding thresholds. The finite families proved here
do not control every received-word stack, production domain lengths, or all
four target rates. Historical prose in this repository sometimes claims more
than its formal theorem statements: the old `31/64` predecessor hypothesis is
already refuted, and `_DeltaStarDefinitive` does not prove that BGK is necessary
or equivalent to solving the prize. Its raw-energy hypothesis also fails in
the advertised deep regime. The audit note gives the exact source declarations.

The [live companion](https://better.codes/) stood at 68.02–116.13 induced
spot-check bits when inspected. These are threshold-derived scores, not a
claim of full-protocol security. Its pinned contract is
[`b34c0131cfa36b51111521541d7d3e35c8791082`](https://github.com/proximity-prize/proximity-prize/tree/b34c0131cfa36b51111521541d7d3e35c8791082).
The 68.03 candidate is not a new record: positive interpolation nullity is only
one part of the required argument. Reconstructing the phase recurrence exposes
an actual budget failure. Retaining the full z-dependent prefixes and recursively
closing all four sources improves the envelope to `274535875126515098`, still
`14399698464318138` above its allocation. These refinements therefore do not
yield a new score. A substantially sharper factor bound and the complete Lean
`ProtocolClaim` remain necessary.

## Local reproduction

From the research worktree:

```sh
python3 scripts/probes/astra_order_eight_monomial_certificate.py
python3 scripts/probes/astra_extension_field_check.py
python3 scripts/probes/astra_nonmonomial_witness.py
python3 scripts/probes/astra_nonmonomial_exact_census.py
python3 scripts/probes/astra_companion_parameters.py
python3 scripts/probes/astra_pg_iterate_exit_check.py
python3 scripts/probes/astra_clm043_remainder.py
python3 scripts/probes/astra_orbit_product_marginal.py
python3 scripts/probes/astra_companion_parameters.py --check-phases
```

These eight Python probes passed locally. The optional phase replay compiled
the C++ evaluator and reproduced the published baseline and all three rejected
candidate envelopes. An independent build with UndefinedBehaviorSanitizer also
passed all four modes and the bounded T-kernel search without diagnostics.
The repository-wide forbidden-token precheck
also passed, with nine pre-existing documented residual axioms. Full repository
validation then stopped at the build step with exit 127 because `lake` is absent.
The Lean assembly draft is kept outside the library import tree at
`docs/kb/proximity-astra-ceiling-draft.lean` until it can be compiled and audited.
The Mathlib-dependent wrapper attempt correctly exits 127 with
`lake: command not found`. Before the repair, the same quiet invocation incorrectly
exited zero and printed `OK`.

The separate core-only certificate subsequently passed:

```sh
lean scripts/probes/astra_core_certificate.lean
# 'AstraCoreCertificate.certificate' depends on axioms: [propext]
```

This actual kernel run took 68.91 seconds using the official Lean 4.30.0-rc2
runtime. It proves the finite Boolean audit; it does not validate the ceiling
draft or the complete ArkLib project. The [verification receipt](../kb/astra-core-certificate-2026-09-04.md)
records the exact command, resource use, and remaining formalization boundary.

Research changes are being committed and pushed to the authorized research
branch. The user's `main` checkout is unchanged. No email, prize submission,
or paid remote computation was performed.

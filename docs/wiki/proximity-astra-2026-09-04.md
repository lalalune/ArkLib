# Proximity Prize research receipt — 4 September 2026

**The grand prize problems remain unsolved in this work.** This session produced
exact finite-instance certificates, a sharper character-sum remainder bound,
a companion parameter search with open proof obligations, and a repair to a
verification wrapper that could falsely report success. Nothing was submitted
to a prize organizer. Verification status is recorded separately below.

## Revisions and environment

* Original clone: `/Users/nubs/Git/arklib`, clean `main` at
  `8e2fc19130e2fea9e175c52b0953b88804b8f333`.
* Research worktree: `/Users/nubs/Git/arklib-proximity-astra`, local branch
  `codex/proximity-astra-20260904`, based on research commit
  `54007b004040a9cd0964dcb0a2413e86bc60ae8d`.
* Both source branch heads were checked against the remote on 4 September.
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
one part of the required argument. New phase, factor-count, and quotient
certificates must be constructed and the complete `ProtocolClaim` must pass
Lean before submission is justified.

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
```

These eight Python probes passed locally. The repository-wide forbidden-token precheck
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

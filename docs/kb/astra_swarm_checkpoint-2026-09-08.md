# Ten-agent Proximity research checkpoint, 2026-09-08

The full order-sixteen production upper bound is now checked in Lean:
`mcaDeltaStar productionCode (1/2^128) <= 313174699/1073741824`.
The construction supplies 1073741828 distinct original same-support MCA-bad
scalars. Its 27 new axiom reports contain only `propext`, `Classical.choice`,
and `Quot.sound`; no residual hypothesis remains in the numeric theorem.
The [kernel receipt](../../scripts/probes/receipts/astra_order16_lean_20260908/kernel_receipt.json)
and independent semantic audit preserve exact source provenance.

This is not an exact threshold or a prize solution. The current bracket
remains `[268435457,313174699]/2^30`. The lower endpoint is a supremum lower
bound, not a safety claim at that endpoint.

## Research results

The [first-step safety argument](astra_mca_first_step-2026-09-08.md) now
proves the n-scalar bound when the full list of joint codeword pairs with
cores of at least `3n/4-1` contains at least two elements. Independent review
checked the three-source common-carrier argument, its exceptional decoders,
and the final mixed-core coverage inequality. The zero-source and singleton branches with dense directions remain open.
The [two-source rational-list proof](astra_mca_two_source-2026-09-08.md) and
[sparse-direction bounds](astra_mca_sparse_direction-2026-09-08.md) were also
independently reviewed. These safety proofs are reviewed written arguments;
their arithmetic and finite controls do not replace Lean formalization.

The follow-up batch strengthens this to a
[near-source theorem](astra_mca_near_source-2026-09-08.md): one joint core of
size at least `t=3n/4-1` and a distinct second core of size at least `t-1`
suffice. The coordinator and two agents independently reviewed the written
proof. Its degree-one and degree-two rational-list counting components now
pass Lean in [a new module](../../scripts/probes/astra_mca_rational_list.lean),
with ten clean axiom reports. The full MCA case split remains written.
The updated local event runner passes all 111 reports with no warnings;
[its receipt](../../scripts/probes/receipts/astra_firststep_next_20260908/kernel-receipt.json)
pins the new source and runner. Hosted verification of this follow-up is
separate from the earlier order-sixteen run below.

A [projective sparse-combination theorem](astra_mca_projective_sparse-2026-09-08.md)
proves the finite bad count at most `n-9` whenever any nonzero combination
of the received words is within 59652323 coordinates of the code. It accounts
for the projective infinity point explicitly. The
[singleton inverse lemma](astra_mca_singleton_inverse-2026-09-08.md) shows that
three exceptional decoders sharing `k-2` roots force the required second core.
A [puncturing reduction](astra_mca_singleton_puncture-2026-09-08.md) identifies
the remaining singleton subproblem as a structured rational-word problem;
an exact control rules out discarding that structure. None of these reductions
proves that a second near-high core or a sparse combination always exists.

The [degree-seven source optimum](astra_mca_order16_all_four-2026-09-08.md)
excludes a better core bound across every four-source family with the existing
common-factor degree budget and carrier. A second implementation evaluates
all 616000 compatible full partitions without the primary pruning. This
restricted optimum does not control other carriers or additional decoders.

Two order-32 neighborhoods were checked over the actual production field:
remove three old triple nodes and add five new ones, with and without allowing
relabeling at the removed nodes. The complete runs made 3228272 and 10995652
exact rank attempts, respectively, with no nonzero tuple. Both retained 2024
removal choices and kernel dimension six before adding constraints. These
are bounded searches, not an exclusion of arbitrary order-32 constructions.
Their receipts are in the [research receipt folder](../../scripts/probes/receipts/astra_swarm_20260908/manifest.json).
The search body was retained with an explicit output-directory option; the
ported wrapper passed a one-support smoke run. Full reproduction:

```sh
python3 scripts/probes/astra_mca_order32_relocation_search.py --output-dir /tmp
python3 scripts/probes/astra_mca_order32_relocation_search.py --relabel --output-dir /tmp
```

## Ten distinct agent assignments

All ten were dispatched with `gpt-6-astra` and `ultra` effort. The session
permits four concurrent agents including the coordinator, so the assignments
ran in batches of at most three children. Selected agents were reused for
proof repair and independent review.

| Agent | Completed assignment |
|---|---|
| 01 | Fork, upstream, branch, issue, and PR audit |
| 02 | Covered-scalar theorem, genuine spike exception, and full sparse-direction safety |
| 03 | Order-32 search and arbitrary-four-source degree-seven reduction |
| 04 | Explicit order-sixteen seed, generator link and full equality table |
| 05 | Actual sixteen-fiber allocation and production core cardinalities |
| 06 | Complete production received-word, event, probability and threshold theorem |
| 07 | Independent same-support, endpoint, and exceptional-scalar audit |
| 08 | Four-, three-, and two-source safety branches and exceptional-decoder structure |
| 09 | Current primary literature and official companion constants/quantifiers |
| 10 | Independent full census, three-source proof review and final theorem semantic audit |

## Remote state and verification boundary

The fork had no new external commits since the prior checkpoint. The
[remote audit](astra_remote_audit-2026-09-08.md) found real September 7–8
upstream work, including the Johnson MCA tracker and exception-counting APIs.
Exact review refs were fetched without merging incompatible toolchains.
The [literature audit](astra_literature_audit-2026-09-08.md) pins official
companion main and explains why its constants do not supply the production
n/P budget. The 68.04 companion direction was already known locally.

Local verification restored the matching Lean4.30.0-rc2 compiler and pinned
Mathlib dependencies, built the actual MCA substrate and certified prime,
and ran the existing polynomial/event checkers plus all three new modules.
The final event runner reported 101 allowed axiom reports, of which 27 are
new. Independent production-field seed checks, all-four-source censuses,
first-step controls, and three-source arithmetic checks passed. The first
local event attempt lacked the prime olean in the main ArkLib namespace;
a matching substrate build fixed that setup error before the successful run.
Both jobs passed in [hosted CI run 34298493883](https://github.com/lalalune/ArkLib/actions/runs/34298493883),
checked at commit `cbab84f1beb08d71f896f16e1af75dd45def7e9b`. The 27 new
reports execute in the ArkLib job. All 46 recorded source hashes match
that checked commit; [hosted provenance](../../scripts/probes/receipts/astra_order16_lean_20260908/hosted_kernel_receipt.json)
is retained separately from the local receipt.

The remaining mathematical objective is a bound on all bad scalars in the
zero-source and singleton cases with every nonzero combination far from the
code; an unsafe singleton must also lack any second core of size `t-1`.
The numerical threshold bracket has not changed. A matching unsafe/safe threshold
and the other challenge parameters also remain open. More source-pattern searches alone do not establish
that universal bound.

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
cores of at least `3n/4-1` has three or four elements. Independent review
checked the three-source common-carrier argument, its exceptional decoders,
and the final mixed-core coverage inequality. The zero-, one-, and two-source
branches remain open. These safety proofs are reviewed written arguments;
their arithmetic and finite controls do not replace Lean formalization.

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
| 02 | Covered-scalar theorem and first-step spike obstruction |
| 03 | Order-32 search and arbitrary-four-source degree-seven reduction |
| 04 | Explicit order-sixteen seed, generator link and full equality table |
| 05 | Actual sixteen-fiber allocation and production core cardinalities |
| 06 | Complete production received-word, event, probability and threshold theorem |
| 07 | Independent same-support, endpoint, and exceptional-scalar audit |
| 08 | Four- and three-source safety branches and exceptional-decoder structure |
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
Hosted CI status is recorded separately from the local receipt.

The remaining mathematical objective is a bound on all bad scalars in the
at-most-two-source cases, then a matching unsafe/safe threshold and the other
challenge parameters. More source-pattern searches alone do not establish
that universal bound.

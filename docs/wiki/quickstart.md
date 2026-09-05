# Quickstart

This page is the recommended agent playbook for commands and validation.
Use it as the main guide for routine local checks.

## Recommended Validation

For a convenient routine check, run:

```bash
./scripts/validate.sh
```

On a cold clone, fetch precompiled dependencies first:

```bash
./scripts/lake-locked.sh exe cache get
./scripts/validate.sh
```

## Concurrent Agent Builds (`lake-locked.sh`)

When several agents share a machine (even in different checkouts/worktrees), never run bare
`lake build` or `lake exe cache get`. Use the serialized wrapper, a drop-in replacement for
`lake`:

```bash
./scripts/lake-locked.sh build ArkLib.Some.Target
./scripts/lake-locked.sh exe cache get
```

This applies to helper scripts too: `scripts/pg-warm.sh` originally called bare `lake build`
and bypassed the lock (observed 2026-07-10: two warm builds plus a locked build ran three
simultaneous lake drivers compiling the same files); it now routes through `lake-locked.sh`.
If you write a script that builds, call the wrapper, never bare `lake`.

What it does (observed failure mode 2026-06-11: 7 concurrent lake builds plus a racing
`cache get` in shared checkouts produced 60+ lean workers on 12 cores, corrupted oleans, and
four builds silently recompiling all of Mathlib from source):

- **Per-checkout exclusive lock** (`.lake/agent-build.lock`): at most one lake invocation per
  checkout. A second invocation waits and then gets a warm incremental build instead of a
  corrupting race. Lake has no built-in lock and no `--jobs` cap in the pinned version.
- **Machine-wide build slots** (`~/.cache/lake-build-slots`, default 2, override with
  `LAKE_LOCKED_SLOTS`): caps total concurrent builds across all checkouts so each gets real
  cores instead of thrashing.
- **Mathlib cache guard**: if `.lake/packages/mathlib` is present but its root olean is
  missing, it runs `lake exe cache get` first (inside the lock). A build must never fall back
  to compiling Mathlib from source — that is hours of CPU and the main melt-down mode.
- **Stale-lock stealing**: locks carry a heartbeat refreshed every 30s; a lock whose heartbeat
  is older than `LAKE_LOCKED_STALE_SECS` (default 300) is presumed killed and stolen, so a
  `taskkill`ed build never wedges the queue.

`./scripts/validate.sh` and `./scripts/build-project.sh` already route their builds through the
wrapper. `LAKE_LOCKED_DISABLE=1` bypasses it (single-tenant machines, CI debugging).

Build hygiene on shared machines:

- One `lake exe cache get` to **completion** before the first build in a fresh checkout; never
  run it concurrently with builds in the same checkout (the wrapper enforces this).
- A build process tree (lake + lean workers) that has been running for far longer than the
  target warrants — for example a small-target build past 20–30 minutes that is grinding
  through `Mathlib/` files — usually indicates a clobbered cache, not a slow build. Kill the
  build tree (never agent processes), restore the cache, retry through the wrapper.

Do not use bare `lake update` as a routine cache-repair command. It re-resolves
`lake-manifest.json` and may delete/re-clone package directories while other checks are running.
Use `lake exe cache get` after syncing instead. Run `lake update` only when intentionally changing
dependency pins, and commit the resulting manifest together with the matching `lean-toolchain`.

### Recovering a corrupted or re-cloning `mathlib` package

Symptoms (tree-wide build failures, OOM, or stalls that are not your change):

- `.lake/packages/mathlib` is large on disk but has no checked-out source
  (e.g. `Mathlib/Algebra/Field/Basic.lean` is missing) or `git -C .lake/packages/mathlib rev-parse HEAD` fails.
- Many concurrent `git-remote-https ... mathlib4` clone processes are racing into that one
  directory, so it never converges and every session's build fails on missing `mathlib` oleans.

Root cause: a per-session package fetch checked out mathlib's default branch instead of the
manifest-pinned revision, and parallel sessions racing the same directory prevent convergence.

Non-destructive recovery (one actor at a time; do **not** `rm -rf` the shared package — the pinned
revision is usually already fetched inside it):

```bash
# 1. Pause (do not kill) the racing clones so the directory stops being overwritten.
pkill -STOP -f 'git-remote-https.*mathlib4'

# 2. Check out the revision pinned in lake-manifest.json (NOT the default branch).
#    Find the pin with: python3 -c "import json;print([p['rev'] for p in json.load(open('lake-manifest.json'))['packages'] if p['name']=='mathlib'][0])"
git -C .lake/packages/mathlib checkout -f <manifest-pinned-rev>

# 3. Decompress the matching precompiled oleans for that revision.
lake exe cache get

# 4. Verify a real build completes.
lake build ArkLib.Data.CodingTheory.ProximityGap.Collapse
```

Prevention: never run `lake update` for cache repair (see above); let a single coordinator do
package recovery; the only source of truth for the mathlib revision is the `mathlib` entry in
`lake-manifest.json`.

## Validation By Change Type

### Existing Lean files only

```bash
./scripts/validate.sh
```

### Added, renamed, or deleted files under `ArkLib/`

```bash
git add path/to/newfile.lean
./scripts/validate.sh
```

`./scripts/update-lib.sh` only considers tracked files, and now fails fast if untracked
`ArkLib/**/*.lean` files are present.

### Lean-heavy refactors or cleanup

```bash
./scripts/validate.sh --lint
```

This adds `./scripts/lint-style.sh` to the convenience wrapper. The main CI build currently runs
with lint disabled, so treat this as opt-in for now.
If the task is specifically Lean warning cleanup, follow
[`../skills/fix-lean-warnings.md`](../skills/fix-lean-warnings.md).

### Docstrings, blueprint, or website changes

```bash
./scripts/validate.sh --docs
```

For website or blueprint output, run:

```bash
./scripts/validate.sh --site
```

`./scripts/build-web.sh` is still what assembles the site, and it skips blueprint generation if
`leanblueprint` is not installed. If blueprint output matters, install it first:

```bash
python3 -m pip install leanblueprint
```

## Stale-Olean Kernel Errors (`unknown constant Semiring.toMonoid` etc.)

Symptom: `lake env lean <file>` (or `pg-iterate.sh`) fails with a KERNEL error
`(kernel) unknown constant 'Semiring.toMonoid'` (or another long-renamed instance path),
usually pointing at a line that merely *applies* an imported theorem. Cause: a `.olean` in the
import cone was compiled against a different toolchain/Mathlib revision (toolchain drift in the
shared checkout); the elaborator inlines a constant name that no longer exists.

Fix (verified 2026-07-09, three occurrences in one session):

```bash
./scripts/lake-locked.sh build <TheStaleModule>   # rebuild JUST the suspect module
```

Isolation recipe: binary-search the import cone with tiny `/tmp` test files that `#check` and
then *apply* the suspect theorems — `#check` alone does not force the failure; an application
in a real `theorem` does. Suspect first any module whose `.olean` mtime predates the last
toolchain bump (`ls -la .lake/build/lib/lean/.../*.olean`). Both ArkLib and Mathlib modules
can be affected (`Mathlib.LinearAlgebra.Matrix.AbsoluteValue` was one instance).

## Important Notes

- `./scripts/validate.sh` is the recommended convenience wrapper for routine local validation.
- By default it runs the forbidden-token precheck, `lake build`, the `ArkLib/Data/**` warning
  budget, the zero-hole sorry census, the flagship axiom audit, umbrella-import checks, docs
  integrity checks, and knowledge-base checks, so a clean local `validate.sh` matches the CI gate set
  (issue #111 parity).
- The lower-level scripts remain valid when you only want one specific check.
- `scripts/build-project.sh` is now just a compile-only helper, not the convenience wrapper.
- `scripts/README.md` is still useful as an inventory of helper scripts.
- Only run docs and site builds when those surfaces are relevant; they are slower and more
  tool-dependent than normal Lean builds.

## Optional Direct Commands

You can still run the underlying pieces directly when debugging a specific issue:

```bash
lake build
python3 ./scripts/forbidden_tokens.py
python3 ./scripts/sorry_census.py --fail-on-holes
python3 ./scripts/axiom_audit.py
./scripts/check-imports.sh
python3 ./scripts/check-docs-integrity.py
python3 ./scripts/kb/check_generated.py
python3 ./scripts/kb/lint.py --strict-cited-pages
```

If you specifically need to regenerate `ArkLib.lean`, use:

```bash
./scripts/update-lib.sh
```

If blueprint output matters and `leanblueprint` is missing:

```bash
python3 -m pip install leanblueprint
```

## CI Mapping

- [`../../.github/workflows/ci.yml`](../../.github/workflows/ci.yml)
  runs the timing-enabled main build on PRs and pushes to `main`, measures a
  clean build, a warm rebuild, and the `./scripts/validate.sh` path, then
  uploads timing artifacts and posts a comparison report on same-repo PRs.
  It also enforces the issue #47 verification gates: a fast precheck rejecting
  `native_decide`/`bv_decide`/custom `axiom` declarations in live source
  (`scripts/forbidden_tokens.py`), a comment-stripped sorry census requiring
  zero live holes (`scripts/sorry_census.py --fail-on-holes`), and a
  `#print axioms` sweep over the pinned flagship list
  (`scripts/axiom_audit.py` reading `scripts/flagship_axioms.txt`) that must
  stay within `propext`, `Classical.choice`, `Quot.sound`. Renaming or
  deleting a pinned flagship theorem without updating the list is a hard CI
  failure. As of issue #111 these same three gates also run from
  `./scripts/validate.sh`, so local validation matches CI.
- The forbidden-token precheck rejects every custom `axiom` *except* the
  documented, tracked residuals listed in
  [`../../scripts/residual_axioms.txt`](../../scripts/residual_axioms.txt) (route (a)
  of #111). Each allowlist entry names one residual axiom and the issue that owns its
  eventual discharge; an undocumented or newly added `axiom` still fails the gate, and a
  stale allowlist entry (matching no live axiom) prints a warning to prompt cleanup.
  `scripts/forbidden_tokens.py` also accepts explicit Lean files or directories for
  focused checks; stale allowlist warnings are only meaningful on the default full-tree scan.
- [`../../.github/workflows/check-imports.yml`](../../.github/workflows/check-imports.yml)
  checks that `ArkLib.lean` matches the tracked source tree.
- [`../../.github/workflows/docs-integrity.yml`](../../.github/workflows/docs-integrity.yml)
  checks local markdown links and the `CLAUDE.md` symlink.
- [`../../.github/workflows/proximity-strip-proof.yml`](../../.github/workflows/proximity-strip-proof.yml)
  checks the standalone Mathlib contact-strip projection, the Std
  arithmetic gates for the proposed 68.04 row, the finite C2 scalar-budget
  obstruction, and three T-interpolant dimension witnesses on the
  `codex/proximity-astra-20260904` research branch when a proof source or the workflow
  changes. Its two jobs use this repository's pinned dependencies (Lean
  4.30.0-rc2) and the official companion's `032154395c51fd6f77715a7f42d9a987ab9fb48a`
  pin (Lean 4.32.2), respectively. Each checks all eighteen
  named theorem reports against the repository's axiom allowlist, and rejects
  missing reports, compiler warnings, errors, or forbidden source tokens. It runs on a standard
  public-repository runner without artifact or cache uploads. This focused
  check is not a full ArkLib build or a companion `ProtocolClaim` check. See
  the [contact-strip research note](../kb/proximity-astra-contact-strip-2026-09-04.md)
  for local reproduction, the bounded source-limit search and its independent
  arithmetic audit, and remaining proof obligations. The
  [factor-partition follow-up](../kb/proximity-astra-factor-partition-2026-09-04.md)
  documents the optional `--check-partition` and `--check-dense-source` audit
  modes and their bounded negative results. The
  [C2 budget audit](../kb/astra_c2_budget_obstruction-2026-09-04.md) separates a
  removable rounding from the need for new geometric correlations; its scalar
  countermodel is not a polynomial counterexample. The
  [T-cutoff audit](../kb/astra_t_cutoff-2026-09-04.md) optimizes the quotient
  cutoff and records an improved, still failing count. The phase evaluator's
  `--quotient-cutoff K` flag defaults to 2 and requires `--joint` with
  `T.L = selected_total + K + 1`; the separate audit checks the dimension
  witness. Use `python3 scripts/probes/astra_t_audit.py --check-search --check-phases`
  to reproduce that search and the four full envelopes, or
  `--sanitize --phase-case least_old_point_charge` to check the search and
  improved envelope with undefined-behavior checks.
  The [geometric contact audit](../kb/astra_c2_geometry_contact_obstruction-2026-09-04.md)
  and [colon/Hermite audit](../kb/astra_colon_2026-09-04.md) document subsequent
  arguments and their exact Python probes. Those general mathematical
  arguments have independent review but are not part of the Lean proof suite.
  The [same-kernel descent](../kb/astra_kernel_descent_2026-09-04.md) strengthens
  the colon analysis by proving necessary contact-profile conditions for a
  universal positive-R factor in a full source kernel. Reproduce its exact
  checks with `python3 scripts/probes/astra_kernel_descent.py`.
  The [derivative repair and incidence bound](../kb/astra_incidence_derivative_repair-2026-09-04.md)
  strengthens the necessary profile conditions; reproduce with
  `python3 scripts/probes/astra_incidence_derivative_repair.py`.
  The [cap-nine repair audit](../kb/astra_kernel_lowr_2026-09-04.md) strengthens
  the high-order node count; run `python3 scripts/probes/astra_kernel_lowr_audit.py`.
  The [all-tail ideal scope check](../kb/astra_global_tail_ideal_scope-2026-09-04.md)
  has `python3 scripts/probes/astra_global_tail_ideal_check.py`; its example is
  outside C2 and fails large agreement. The separate
  [smooth-domain middle-band counterexample](../kb/astra_grand_smooth_middle_counterexample-2026-09-04.md)
  refutes `RegionMiddleExclusion`, an overly strong sufficient conjecture,
  with a field-uniform written proof and an actual three-codeword construction.
  Use `python3 scripts/probes/astra_grand_smooth_middle_counterexample.py`.
  Its [genuine-stack follow-up](../kb/astra_grand_stack_scope-2026-09-04.md)
  audits the remaining witness data and rules out a fourth sufficiently
  close codeword inside the known three-codeword affine span; run
  `python3 scripts/probes/astra_grand_stack_affine_span.py`.
  The [three-core MCA conversion](../kb/astra_mca_lift_three_core-2026-09-04.md)
  supplies actual bad-event witnesses and no-joint parity certificates on
  unchanged smooth domains; use `python3 scripts/probes/astra_mca_lift_three_core.py`.
  The [weighted secant bound](../kb/astra_family_incidence_secants-2026-09-04.md)
  links shared contacts to contained lines under an explicit non-plane
  component hypothesis; use `python3 scripts/probes/astra_family_incidence_secants.py`.
  The [profile-boundary analysis](../kb/astra_profile_boundary_2026-09-04.md)
  gives exact weight windows and a received-line factorization criterion;
  run `python3 scripts/probes/astra_profile_boundary.py` for the arithmetic
  and 72 polynomial substitution/inversion checks.
  The [balanced pair-cover criterion](../kb/astra_mca_paircover_target-2026-09-04.md)
  gives a conditional over-budget MCA construction, but its required
  polynomial triple remains unconstructed. The
  [exhaustive mu16 search](../kb/astra_mca_paircover_search-2026-09-04.md)
  excludes the degree-six seed over F65537 and in characteristic zero.
  Its reproduction command checks all 378378 original coefficient matrices
  independently under undefined-behavior sanitization.
  Use `python3 scripts/probes/astra_mca_paircover_conversion.py` for a
  positive control on different evaluation domains, with 266 independent
  no-joint parity certificates; it does not supply the production seed.
  The [production-field mu16 check](../kb/astra_mca_paircover_production-2026-09-04.md)
  has `python3 scripts/probes/astra_mca_paircover_production.py`.
  The [four-coset obstruction](../kb/astra_mca_paircover_four_cosets-2026-09-04.md)
  excludes its entire architecture in every admissible characteristic;
  use `python3 scripts/probes/astra_mca_paircover_four_cosets.py` for the
  small-domain rank checks in the production prime.
  The [two-generator bridge](../kb/astra_mca_two_generator_bridge-2026-09-04.md)
  supplies production-length polynomial bases by two-point deletion. The
  [hosted production count](../kb/astra_mca_production_count-2026-09-05.md)
  establishes the required n+1 finite directions and a computational upper
  bound; the universal matching lower bound remains open.
  Its [finite MCA certificates](../kb/astra_mca_two_generator_probe-2026-09-04.md)
  check 18,66,258 scalars on mu16, mu64, mu256, respectively. Run
  `python3 scripts/probes/astra_mca_two_generator_probe.py` for the complete
  irregular mu16 receipt, and
  `python3 scripts/probes/astra_mca_two_generator_delete_probe.py` for the
  three deletion cells with agreement and no-joint parity checks.
  The [compact production evaluator](../kb/astra_mca_twogen_lift_eval-2026-09-04.md)
  uses fourteen rational summands per ordinary point; run
  `python3 scripts/probes/astra_mca_twogen_lift_eval.py` for dense small-domain
  comparisons and the constant-size production checks. Its original partial
  count 268435460 was superseded by the completed hosted lower bound 1073741825.
  Run `python3 scripts/probes/astra_mca_hosted_receipt_check.py` to check the
  archived receipt hashes and exact field certificate without replaying the scan.
  The [native evaluator](../kb/astra_mca_native_eval-2026-09-04.md) provides
  exact finite-value counting with bounded partition arrays. Run
  `python3 scripts/probes/astra_mca_native_eval_check.py` for independent
  arithmetic, formula, batch, and counting checks; this default check never
  starts the production scan. Full scans use a separately requested command
  and report resource failures as incomplete.
  The [resumable driver](../kb/astra_mca_resumable_scan-2026-09-04.md) retains
  verified chunks and deterministic fingerprint lower bounds across resource
  interruptions. It requires a matching compiling acceptance receipt and
  defaults to plan-only mode.
  The [fixed-pencil predecessor obstruction](../kb/astra_mca_fixed_pencil_predecessor-2026-09-04.md)
  rules out full-cover constructions with at most five sufficiently large
  joint cores. It records necessary conditions for six cores and for four
  unequal cores; it does not prove the universal predecessor bound.
  The [six-pencil flat constraints](../kb/astra_mca_six_pencil_flats-2026-09-04.md)
  exclude one explicit quadrilateral construction, while the
  [incidence classification](../kb/astra_mca_six_pencil_types-2026-09-04.md)
  identifies seven remaining geometric types and stronger necessary overlap
  bounds. Their polynomial realizability and scalar counts remain open.
  The [sharp incidence thresholds](../kb/astra_mca_incidence_feasibility-2026-09-05.md)
  give common-domain set systems for every b>=4, so those counting constraints
  alone cannot exclude production. Actual two-triple polynomial realizations
  would have to satisfy two compatible degree-four-defect identities with
  no common rational right factor. Run
  `python3 scripts/probes/astra_mca_incidence_feasibility_check.py` for the
  seven minimal fixtures and exact construction arithmetic.
  The [locator consistency identities](../kb/astra_mca_six_locator_consistency-2026-09-04.md)
  force a three-dimensional polynomial span and a constant private-locator
  relation. The [cyclotomic locator constraints](../kb/astra_mca_cyclotomic_locator_constraints-2026-09-05.md)
  rule out common power lifts of order at least four for the concrete
  ten-point-defect pattern; reciprocity and the basic elliptic-cover bound
  do not exclude it. Run `python3 scripts/probes/astra_mca_cyclotomic_locator_check.py`
  for the exact bounded identities and production degree arithmetic.
  For one concrete remaining pattern, the
  [birationality argument](../kb/astra_mca_six_locator_birationality-2026-09-04.md)
  proves that its locator map would be birational; the genus bound still has
  positive slack and does not exclude that pattern.
  The [resultant equations](../kb/astra_mca_six_locator_resultants-2026-09-04.md)
  identify saturation with a split squarefree square and exclude infinity
  factors. Run `python3 scripts/probes/astra_mca_six_resultant_check.py` for
  the bounded identity checks; the necessary equations do not exclude every
  six-pencil configuration.
  The [low-degree saturation theorem](../kb/astra_mca_low_degree_saturation-2026-09-05.md)
  proves that four saturated points force a degree-two cover when b=2 and
  gives a sharp three-point example without that cover. Run
  `python3 scripts/probes/astra_mca_low_degree_saturation_check.py` for 930
  projective checks. A [six-square countermodel](../kb/astra_mca_six_square_countermodel-2026-09-05.md)
  shows that the square conditions alone do not force a cover at b=3:
  all eighteen scalar values are distinct, but the locator union needs 33
  points instead of the required 16. Run
  `python3 scripts/probes/astra_mca_six_square_countermodel_check.py` for the
  exact polynomial certificate. It is not an actual MCA counterexample.
  The [decoding-curve incidence bound](../kb/astra_mca_decoding_curve_incidence-2026-09-04.md)
  quantifies what a separately constructed curve carrier would suffice to
  prove. The existence of such a carrier for arbitrary MCA events is open.
  The [ordinary-MDS obstruction](../kb/astra_mca_mds_rank_obstruction-2026-09-05.md)
  proves that rank two and ordinary MDS generalized Hamming weights alone
  cannot provide the desired cap: a length-64 MDS code can have 84 isolated
  threshold-44 MCA vertices over the production field. This is not an RS
  realization. Run `python3 scripts/probes/astra_mca_mds_rank_obstruction.py`
  for its support, matching, and specialization-degree checks.
  The [single-hole reduction](../kb/astra_mca_single_hole_reduction-2026-09-05.md)
  identifies an exact MCA subfamily with the extrapolated-value image of a
  punctured RS list. Its large joint cores are rationally collinear but omit
  one domain point, so the full-cover obstruction does not apply. Run
  `python3 scripts/probes/astra_mca_single_hole_check.py` for its complete
  F17 control; the universal production value-image bound remains open.
  Its [locator formulation](../kb/astra_mca_single_hole_locator-2026-09-05.md)
  shows why the error-locator divisor requirement is essential: removing it
  admits almost every scalar even for a production-domain word. Run
  `python3 scripts/probes/astra_mca_single_hole_locator_check.py` for the
  independent finite comparison of actual and relaxed values.
  The [native-count workflow](../../.github/workflows/proximity-native-count.yml)
  runs the separately pinned, bounded-tested native source on a standard
  public-repository Linux runner. It preserves computation receipts; it does
  not run Lean or certify the universal prize theorem.
  The [anchor filter](../kb/astra_mca_anchor_multiplicity-2026-09-04.md)
  rules out pure power lifts as a general way to guarantee enough directions.
  The [Paley scope audit](../kb/astra_paley_scope-2026-09-04.md) distinguishes
  classical Paley conjectures from proven additive subgroup bounds and records
  a valid shifted-character specialization. Run
  `python3 scripts/probes/astra_paley_transfer.py` for its finite identities
  and exact production size gates.
  These results are not Lean formalized and establish no improved prize score.

## Manual Timing Helper

If you need to reproduce the timing workflow locally, the same helper script can
capture a measurement and render a report:

```bash
bash scripts/build_timing_report.sh run clean_build /tmp/build-timing.jsonl -- \
  bash -eo pipefail -c 'rm -rf .lake/build && lake build'
bash scripts/build_timing_report.sh render /tmp/build-timing.jsonl
```

## Swarm Verification Discipline

Hard-won rules for multi-agent sessions where several agents land commits on
`main` concurrently (distilled from the 2026-06-10 #232 frontier sessions):

- **An announced brick is not a brick.** Commit messages and `DISPROOF_LOG.md`
  entries can name theorems that never landed (found once: a theorem announced
  in a commit message existed nowhere in history). Before citing or building on
  a named lemma, `grep` the tree — not the log — and prefer
  `git log -S <name>` to confirm a Lean occurrence.
- **`#print axioms` lines are expected output.** Several modules end with
  `#print axioms <thm>` audit lines by convention. A zero-output compile gate
  must treat those lines as a pass signal (each should read exactly
  `[propext, Classical.choice, Quot.sound]`); anything else in the output —
  warnings, errors, `sorry` notices — is a failure.
- **Main-branch CI runs supersede in queue.** With
  `cancel-in-progress: ${{ github.ref != 'refs/heads/main' }}`, queued main
  runs are replaced by newer pushes; individual-push runs showing `cancelled`
  is normal. The head run validates the whole tree, so "CI green on every
  push" means: the most recent *completed* main run is green and contains your
  commits (`git merge-base --is-ancestor <sha> <ci-sha>`).
- **Joint-import check before declaring a batch done.** Single-file
  `lake env lean` passes do not rule out cross-module name clashes. After
  landing several new modules, build exactly those targets
  (`lake build <Module1> <Module2> …`) and compile a scratch file importing
  all of them together.
- **Rebase before every push; new files only.** Concurrent agents editing
  shared files (especially `ArkLib.lean`, `DISPROOF_LOG.md`) is the main
  collision source. One designated writer appends to shared logs; everyone
  else ships new modules and lets `./scripts/update-lib.sh` regenerate the
  import index at commit time.
- **After landing, confirm your commit survived: `git branch -r --contains
  <sha>`.** Concurrent lanes rewrite history; locally-green commits get
  dropped while the file content survives untracked on disk. Recovery is
  cheap — `git add` + re-commit the surviving file (byte-identical to the
  orphan blob), then push via a detached worktree if the main tree has other
  lanes' unstaged edits: `git worktree add /tmp/wt FETCH_HEAD && cd /tmp/wt &&
  git cherry-pick <sha> && git push fork HEAD:main`.
- **Agent deaths leave complete orphan files — check before re-proving.** A
  prover that hits its session limit after writing but before verifying
  leaves a finished (often fully correct) file at its target path. Before
  relaunching the brick, `git status --short` the target directory, compile
  the orphan, and fix at most the 1–2 mechanical tactic errors (recurring
  shapes: `Set.injOn_id` unification → introduce the `InjOn` proof as a
  `have`; `WithBot` casts → `WithBot.coe_le_coe.mpr`; `smul_eq_mul`
  commutation → `simp [smul_eq_mul]` then `ring`, since `simp [mul_comm]`
  loops).
- **A surprise `sorryAx` in `#print axioms` for a sorry-free file means stale
  imports, not a tainted proof.** Rebuild the import closure
  (`lake build <each imported module>`) and re-check before debugging the
  proof. Confirmed twice on 2026-06-10/11.

## Verification wrapper failure handling

`scripts/pg-iterate.sh` preserves a nonzero exit status from `lake env lean`,
including a missing toolchain or a terminated compiler. Quiet mode suppresses
routine output, not command failures. Successful elaboration with no printed
axiom audit is allowed; it does not itself establish which axioms a theorem uses.
To exercise this process boundary without installing Lean, run
`python3 scripts/probes/astra_pg_iterate_exit_check.py`. This regression check
does not verify any mathematical theorem.

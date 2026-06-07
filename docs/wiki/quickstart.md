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
lake exe cache get
./scripts/validate.sh
```

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

## Important Notes

- `./scripts/validate.sh` is the recommended convenience wrapper for routine local validation.
- By default it runs the three CI verification gates (`forbidden_tokens.py` precheck,
  `sorry_census.py --fail-on-holes`, and `axiom_audit.py`) alongside `lake build`,
  `./scripts/check-imports.sh`, and `python3 ./scripts/check-docs-integrity.py`, so a clean
  local `validate.sh` matches the CI gate set (issue #111 parity).
- The lower-level scripts remain valid when you only want one specific check.
- `scripts/build-project.sh` is now just a compile-only helper, not the convenience wrapper.
- `scripts/README.md` is still useful as an inventory of helper scripts.
- Only run docs and site builds when those surfaces are relevant; they are slower and more
  tool-dependent than normal Lean builds.

## Optional Direct Commands

You can still run the underlying pieces directly when debugging a specific issue:

```bash
lake build
./scripts/check-imports.sh
python3 ./scripts/check-docs-integrity.py
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

## Manual Timing Helper

If you need to reproduce the timing workflow locally, the same helper script can
capture a measurement and render a report:

```bash
bash scripts/build_timing_report.sh run clean_build /tmp/build-timing.jsonl -- \
  bash -eo pipefail -c 'rm -rf .lake/build && lake build'
bash scripts/build_timing_report.sh render /tmp/build-timing.jsonl
```

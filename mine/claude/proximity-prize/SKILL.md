---
name: proximity-prize
description: Mine the open δ* / proximity-gap problem with Claude Code. Use when the user wants to contribute a verified "brick" (an exact-arithmetic probe or an axiom-clean Lean lemma) to the Ethereum Foundation proximity prize on lalalune/ArkLib. Each run produces ONE checked result — a win or an honest refutation — and opens a PR.
---

# Mine the proximity prize with Claude Code

You are joining a crowd-sourced attack on an **open** research problem: pinning `δ*`,
the mutual-correlated-agreement threshold for Reed–Solomon codes, in the prize regime.
The Ethereum Foundation has a **$1,000,000** prize for resolving the proximity-gap
conjectures (https://proximityprize.org/). Nobody has solved the hard part in ~25 years —
including this fleet. **You are not expected to solve it.** You are expected to add ONE
small, *verified* brick and report honestly. A verified refutation counts as much as a
verified proof: both move the map.

The arbiter is never the model. It is the **Lean 4 kernel** (for proofs) or **exact
integer arithmetic** (for probes). If it isn't checked, it doesn't count.

## The one rule that matters

**Never fabricate.** No `sorry`, no new axioms, no `theorem foo : True := trivial`
placebos, no floating-point "it's basically zero", no "this likely holds". If you can't
verify it, you say so and submit nothing. Refute before you believe. This fleet has
shipped ~30 honest refutations; that is the job working, not the job failing.

## Do exactly one brick, then stop

### 1. Orient (always, every run)
- Read the map: https://deltastar-paper.pages.dev/ (the problem + where the wall is).
- Read the live frontier: GitHub issue **lalalune/ArkLib#389** (newest comments first —
  other miners post deep insight there) and `#371` (closed, but the lineage).
- In the repo: `AGENTS.md`, `ArkLib/Data/CodingTheory/ProximityGap/CLAUDE.md`, and
  `ArkLib/Data/CodingTheory/ProximityGap/DISPROOF_LOG.md` (every dead end, numbered `O###`).

### 2. Get the repo
```sh
gh repo fork lalalune/ArkLib --clone --remote   # forks to your account + clones
cd ArkLib
```
(If you already have push access, clone directly and skip the fork.)

### 3. Pick a SMALL target — and don't collide
Skim the newest `#389` comments and the open issues. Other agents *claim lanes in
comments* — do not take a lane someone is actively on, and check for existing open PRs on
the same thing first. Good starter targets, lowest friction first:

- **An exact-arithmetic probe (DEFAULT — no Lean toolchain needed).** Take any conjecture
  from `#389` / the paper / `DISPROOF_LOG.md` and test it with **exact integers** (Python
  `int`, `fractions` — never `float`) **in the prize regime** (constant rate ρ∈{1/2,1/4,1/8,1/16},
  a genuinely large field e.g. `q ≈ n·2^128`, smooth domain `μ_n`, `n=2^k`). Try hard to
  **break** it. A clean refutation in the prize regime is a brick. Put it in
  `scripts/probes/` next to the others; copy their style.
- **An axiom-clean Lean lemma** (if you have `elan`/`lake` + the mathlib cache set up): a
  small leaf file under `ArkLib/Data/CodingTheory/ProximityGap/`. Keep it a leaf (nothing
  else imports it) so it can't break the build.

### 4. Verify — the kernel/arithmetic is the judge
- **Probe:** it must run and be reproducible; print exact integers; state the regime and
  what was (dis)proven. Re-run it. A second, independently-written check is gold standard.
- **Lean:** `lake env lean <yourfile>.lean` must compile, and
  `#print axioms <your_theorem>` must show **only** `[propext, Classical.choice, Quot.sound]`
  with **no `sorryAx`**. (Use `./scripts/lake-locked.sh` if others may be building. Never
  bare `lake build`.) If it doesn't check, you have no brick — that's fine, report it.

### 5. Record the verdict
If it's a verdict (proof or refutation), add a dated entry to `DISPROOF_LOG.md`. Grep the
file for the highest `O###` first and use the next number (the log moves fast — re-grep
right before you write).

### 6. Submit — open the PR
```sh
git checkout -b mine/<short-handle>-<topic>
git add <only the files you intend>          # never `git add -A`
git commit -m "probe(#389): <one-line verdict>"   # author YOURSELF, no AI co-author trailers
git push -u origin HEAD
gh pr create --repo lalalune/ArkLib --fill
```
Then post a short, honest note on issue `#389` saying what you verified. **If you cannot
open a PR**, just post the verified finding (with the exact numbers / the probe) as a
`#389` comment — that still helps.

### 7. Report to the user, then stop
Tell them in plain words: what you tried, what the kernel/arithmetic actually confirmed,
what you did **not** establish, and the PR/comment link. One brick per run. Do not claim
the prize is solved — it is open.

## Staying in the prize regime (where most "results" die)
A statement that holds for tiny fields, at the Johnson radius `1−√ρ`, or that reduces to an
incomputable lemma, is **not** progress — the prize lives strictly inside the window
`(1−√ρ, 1−ρ−Θ(1/log n))` at `ε* = 2^−128`, `q ≈ n·2^128`. Before believing anything, ask:
does it survive at constant rate, huge `q`, and smooth `μ_n`? Many true things don't.

## Good citizen
Be nice to the machine (`nice`/`taskset` long jobs), don't spam duplicate PRs, credit prior
work, and keep every claim exactly as strong as what you checked — no more.

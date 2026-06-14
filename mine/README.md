# ⛏️ Mine the proximity prize

Point your own AI coding agent at an **open** million-dollar math problem and have it mine a
single **verified brick** — a result the Lean kernel or exact arithmetic actually checks,
not something a model just claims.

This is the crowd-sourced arm of the [δ\* campaign](https://deltastar-paper.pages.dev/) on
[`lalalune/ArkLib`](https://github.com/lalalune/ArkLib). The Ethereum Foundation has a
[$1,000,000 prize](https://proximityprize.org/) for resolving the proximity-gap conjectures
for Reed–Solomon codes. The hard part has been open for ~25 years. **It is not solved.**
Every contribution — a proof or an honest refutation — is published either way. Nobody has
mined with Claude Code before.

> **The deal, plainly:** the model proposes, the **kernel disposes**. Nothing ships unless
> it's checked. A verified *refutation* counts as much as a verified *proof* — both narrow
> the map. Never fabricate; claim exactly what you checked.

## Choose your miner

### 🤖 Claude Code
```sh
mkdir -p ~/.claude/skills/proximity-prize
curl -fsSL https://raw.githubusercontent.com/lalalune/ArkLib/main/mine/claude/proximity-prize/SKILL.md \
  -o ~/.claude/skills/proximity-prize/SKILL.md
```
If `~/.claude/skills/` didn't already exist, **restart Claude Code** (or start a
fresh session) so it picks up the new skill. Then open `claude` in any directory and run:
```
/proximity-prize
```
(or just say *"mine the proximity prize"*). It will orient on the live frontier, pick a
small uncontested target, produce one checked brick, and open a PR.

### 🧠 Codex
```sh
curl -fsSL https://raw.githubusercontent.com/lalalune/ArkLib/main/mine/codex/AGENTS.md \
  -o AGENTS.md
```
Run `codex` in that directory and tell it: *"follow AGENTS.md — mine one brick."*

## What a "brick" is
- **The default (no Lean toolchain needed):** an **exact-arithmetic probe** — a short
  script using exact integers (never floating point) that tests a conjecture from issue
  [#389](https://github.com/lalalune/ArkLib/issues/389) **in the prize regime** and tries
  to break it. A clean refutation in-regime is a real brick.
- **The proof path (needs `elan`/`lake` + the mathlib cache):** a small **axiom-clean**
  Lean 4 leaf lemma whose `#print axioms` shows only `propext, Classical.choice, Quot.sound`
  with no `sorryAx`.

## The prize regime (read this or your result won't count)
`δ*` lives strictly inside the window `(1−√ρ, 1−ρ−Θ(1/log n))` at error `ε* = 2^−128`, with
constant rate `ρ ∈ {1/2, 1/4, 1/8, 1/16}`, a huge field `q ≈ n·2^128`, and a smooth domain
`μ_n` (`n = 2^k`). Statements that only hold for tiny fields, at the Johnson radius, or that
defer to an incomputable lemma are **not** progress. Many true things fail here.

## Where to look
- The map: <https://deltastar-paper.pages.dev/>
- The live frontier: [issue #389](https://github.com/lalalune/ArkLib/issues/389) (newest
  comments first — miners post real insight there)
- Every dead end so far: `ArkLib/Data/CodingTheory/ProximityGap/DISPROOF_LOG.md`
- The agent guides: `AGENTS.md` and `ArkLib/Data/CodingTheory/ProximityGap/CLAUDE.md`

## Honesty charter
No `sorry`, no axioms, no placebo theorems, no float "≈ 0", no "likely holds." Refute before
you believe. Report what the check confirmed and what it did not. Author your commits
yourself with no AI co-author trailers. The prize is open — don't say otherwise.

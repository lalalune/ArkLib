# Mine the proximity prize with Codex

You are joining a crowd-sourced attack on an **open** research problem: pinning `δ*`, the
mutual-correlated-agreement threshold for Reed–Solomon codes, in the prize regime. The
Ethereum Foundation has a **$1,000,000** prize for resolving the proximity-gap conjectures
(https://proximityprize.org/). The hard part has been open ~25 years — including for this
fleet. **You are not expected to solve it.** Add ONE small *verified* brick and report
honestly. A verified refutation counts as much as a verified proof.

The arbiter is never you. It is the **Lean 4 kernel** (for proofs) or **exact integer
arithmetic** (for probes). If it isn't checked, it doesn't count.

## The one rule that matters
**Never fabricate.** No `sorry`, no new axioms, no `: True := trivial` placebos, no
floating-point "basically zero", no "this likely holds." If you can't verify it, submit
nothing and say so. Refute before you believe.

## Do exactly one brick, then stop

1. **Orient.** Read https://deltastar-paper.pages.dev/ (the map), GitHub issue
   `lalalune/ArkLib#389` (newest comments — other miners post real insight), and in-repo:
   `AGENTS.md`, `ArkLib/Data/CodingTheory/ProximityGap/CLAUDE.md`, and
   `.../ProximityGap/DISPROOF_LOG.md` (numbered `O###` dead ends).
2. **Get the repo.** `gh repo fork lalalune/ArkLib --clone --remote && cd ArkLib`
   (clone directly if you already have access).
3. **Pick a SMALL target, don't collide.** Other agents claim lanes in `#389` comments;
   check for existing open PRs first. Lowest friction first:
   - **Exact-arithmetic probe (DEFAULT — no Lean needed):** test any conjecture with exact
     integers (never `float`) **in the prize regime** — constant rate ρ∈{1/2,1/4,1/8,1/16},
     huge field `q ≈ n·2^128`, smooth domain `μ_n` (`n=2^k`). Try hard to **break** it. A
     clean refutation in-regime is a brick. Drop it in `scripts/probes/`, copy the style.
   - **Axiom-clean Lean leaf lemma** (needs `elan`/`lake` + mathlib cache): a small file
     under `.../ProximityGap/` that nothing imports.
4. **Verify.** Probe: runs, reproducible, exact integers, states the regime + verdict —
   re-run it. Lean: `lake env lean file.lean` compiles AND `#print axioms thm` shows only
   `[propext, Classical.choice, Quot.sound]`, no `sorryAx`. No check ⇒ no brick.
5. **Record.** If it's a verdict, add a dated `O###` entry to `DISPROOF_LOG.md` (grep for
   the highest number first; it moves fast).
6. **Submit.** New branch, stage only intended files (never `git add -A`), commit authored
   **yourself with no AI co-author trailers**, push, `gh pr create --repo lalalune/ArkLib
   --fill`, and post a short honest note on `#389`. Can't PR? Post the verified finding as a
   `#389` comment.
7. **Report, then stop.** Plain words: what you tried, what arithmetic/kernel actually
   confirmed, what you did NOT establish, the link. One brick per run. The prize is open —
   don't claim otherwise.

## Stay in the prize regime
Anything that holds only for tiny fields, at the Johnson radius `1−√ρ`, or that reduces to
an incomputable lemma is **not** progress. `δ*` lives strictly inside `(1−√ρ, 1−ρ−Θ(1/log
n))` at `ε* = 2^−128`. Ask of every claim: does it survive at constant rate, huge `q`,
smooth `μ_n`? Many true things don't.

Be a good citizen: `nice` long jobs, no duplicate PRs, credit prior work, claim exactly
what you checked.

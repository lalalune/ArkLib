# Engineering Journal — issue-closure campaign

A running log of findings, methodology, and rationale for the open-issue closure
campaign on this repository. Maintained alongside the work; newest entries last.

## Methodology

1. **Witness-gated loops.** Every goal is pinned to a runnable check (a compile +
   axiom audit, a numeric probe, an issue count) that exits 0 exactly when the goal
   is achieved. Self-assessment is never the exit condition.
2. **Axiom-clean bricks.** Every landed theorem must report
   `[propext, Classical.choice, Quot.sound]` under `#print axioms` — no `sorry`,
   no custom axioms, no vacuous `True` placeholders. The repo's
   `forbidden_tokens.py` precheck runs before every commit.
3. **Probe before prove.** Numeric side conditions are swept in Python at multiple
   scales before formalization. This caught a budget that could never close (the
   degenerate-cell bound at `n·|c|·D` exceeds the Johnson budget by a factor linear
   in `n`) and redirected the program to the tight `D/(k-1)` entry bound *before*
   weeks of Lean work were spent on an unsatisfiable inequality.
4. **Check before build.** Before any new lemma: grep the tree for existing
   versions, refutations, and consumers. Several planned bricks were found already
   in-tree (decode extraction, weight bounds, tail-kill machinery); several others
   were found *refuted* (non-monic kernels) — both outcomes redirect work cheaply.
5. **Consumer-shaped statements.** New theorems copy their hypothesis shapes
   verbatim from the consumers that will use them, so landing them never requires
   editing hot files others are working in. All work is additive.
6. **Decompose before the edge.** Multi-layer goals land as separate bricks
   (arithmetic core, then cast wrapper, then composition), each compiled and
   audited independently, so failures localize.

## Findings to date (below-Johnson MCA program, #302 / #304 / #334)

- The [Hab25] below-Johnson numeric edge reduces, fully in-tree, to a single
  per-factor-cell disjunct ("small or affinely improving"); every consumer layer
  (cell production, capture, counting, budget arithmetic) is proven and axiom-clean.
- The arithmetic side condition is satisfiable **only** at the tight Z-degree
  budget `n·|c|·(D/(k-1))` — discovered by numeric sweep, then formalized
  (`GSInterpolantZDegreeTight.lean`).
- On the 3-intersection window `2n + k ≤ 3t` the full pipeline closes with **zero
  side conditions** (`johnsonNumericBound_of_window_closed`).
- The final quantified statement is pinned as `JohnsonDischargeStatement`; the
  unconditional theorem is one per-stack production away, and the production
  reduces to the surface-factor divisibility composed from `FiberSectionCoherence`
  (Part 6) and the lane's weld-node selection.

## Campaign log

- Entry 1: gate armed on all 12 open issues + this journal. Scouting the
  residual-Prop discharge issues (#337, #338, #339) for mechanical closure;
  composition attempt for the #302 surface-factor production running in parallel.

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

- Entry 2: surface-factor production landed (the global section divisor with full
  decoded-family coherence, 8 declarations) via an isolated long-running build agent;
  its conclusion makes the lane's decode a single affine pencil on the whole close
  set. The Z-affine decomposition and the capture wire (reverse counting + per-scalar
  capture) now connect that conclusion to the capture funnel with a one-pair list.
  Hard lesson: `lake env lean` elaborates with default options and masked a missing
  binder that strict `lake build` (autoImplicit := false) rejects — new rule: every
  new file is strict-built before commit. Remaining for the #302 numeric edge: the
  per-stack assembly (production × decomposition × wire) and the production's four
  parameterized inputs (residual bundle instance, Claim-5.11 numerics, factor
  Z-budget descent, one counting comparison).

- Entry 3: the unconditional path is fully enumerated. The per-stack GS bundle has an
  in-tree producer with parameter-only side conditions; its box construction carries an
  explicit inner-degree cap that the new divisor-descent lemma transports to every
  factor. The top level splits per stack on the size of the close-proximity set: small
  sets close by direct counting (bad scalars inject into close ones), large sets
  activate the surface production's largeness conditions and close by the one-pair
  capture. Remaining: the dichotomy assembly, the residual-bundle input check, and the
  final statement.

- Entry 4: consistency probe on the weld's three numeric conditions found the window
  nearly empty as composed: the cover and threshold inequalities at a shared degree
  parameter force the matching threshold to 1 and pin the close-count exactly (with a
  divisibility constraint), while the smallness condition caps it by a constant. The
  surface route as currently wired covers only a thin family of stacks. Re-planning:
  examine the complement weld variant, or generalize the weld to decouple the two
  degree parameters (the paper's threshold scales with the close-count). The probe ran
  before the top assembly was built on the vacuous window — methodology item 3 doing
  its job.

- Entry 5: the thin window is fully diagnosed — only the full-coverage conversion
  forces the degenerate parameter pinning; the underlying point-selection has an open
  window in the complement form, with the threshold scaling correctly. Rerouting to
  partial coverage: scalars matched at every selected point inherit the pencil; the
  rest are counted against the per-point miss budget. The route is non-vacuous and the
  three pieces (partial pencil identity, escapee count, count assembly) are enumerated.

# Additions to VCV-io not yet in the pinned dependency

This directory mirrors VCV-io's module structure (`OracleComp/`, `EvalDist/`,
`ToMathlib/`, ...). Each file holds `simulateQ` / `OracleComp` / distribution
lemmas that ArkLib needs but that the currently-pinned VCVio commit predates,
plus ArkLib-local additions that are candidates for upstreaming.

Workflow: prefer landing general statements upstream in VCV-io under the same
names and the mirrored path; on the next VCVio bump, delete the corresponding
declaration here and let references resolve to the upstream version.

History note: `simulateQ_list_forIn` was staged here and has been deleted —
the VCVio pin (`5f7707fb`, Lean 4.30 bump) now contains it upstream. The
`simulateQ_addLift_add_liftM_left/right` routing pair
(`OracleComp/SimSemantics/SimulateQ.lean`) remains ArkLib-local and is an
upstream candidate.

# Issue #34/#35/#36 — VCVio v4.30.0-rc2 port surface + disk-full finding

Date: 2026-06-06

This records the **dependency-side** toolchain-churn breakage that gates every OracleReduction
build (and therefore #25/#13/#17-area bricks and the green root build #36). Distinct from the
CompPoly `ToPoly/Division` breakage tracked separately, which gates the proximity-gap tree.

## Root cause

`.lake/packages/VCVio` (pinned at `b87119d`, repo `lalalune/VCV-io`) targets `leanprover/lean4:v4.29.0`
(see its `CLAUDE.md`). ArkLib now pins `v4.30.0-rc2`. `grind` and some `simp`/`rfl` closers changed
between 4.29 and 4.30, so multiple VCVio proofs fail to compile under the current toolchain. Because
`ArkLib/OracleReduction/OracleInterface.lean` does `import VCVio` (the **umbrella**), the *entire*
VCVio library must compile for any OracleReduction module — so these are hard blockers, not optional.

## Fixes already verified (apply to `.lake/packages/VCVio`, build green under v4.30.0-rc2)

These three modules now build (`lake build ToMathlib.ProbabilityTheory.SPMF`,
`VCVio.OracleComp.ProbComp`, `VCVio.EvalDist.Defs.Instances` all succeed):

1. `ToMathlib/ProbabilityTheory/SPMF.lean` — `support_eq_preimage_some`: `by grind` →
   ```
   by ext x
      simp only [support_def, Function.mem_support, Set.mem_preimage, PMF.mem_support_iff,
        apply_eq_toPMF_some]
   ```
2. `VCVio/OracleComp/ProbComp.lean` — `probOutput_uniformSelectList` (`y :: ys` case): drop the
   trailing `rfl` (the preceding `simp` now closes the goal under 4.30; the `rfl` is "No goals").
3. `VCVio/EvalDist/Defs/Instances.lean`:
   - `HasEvalPMF PMF` `support_eq _ := by grind` → `support_eq _ := rfl` (the default `toSet =
     SPMF.support ∘ toSPMF` makes the field defeq).
   - `HasEvalPMF Id` `support_eq mx := by grind` → `by aesop`.
   - `HasEvalFinset Id` `coe_finSupport x := by ext y; grind` → `Finset.coe_singleton x`
     (`support x = {x.run}` is `rfl` for `Id`).

## Remaining VCVio surface (not yet ported)

Next frontier hit when building `ArkLib.OracleReduction.Composition.Sequential.General`:

- `VCVio/CryptoFoundations/MerkleTree/Inductive/Completeness.lean:51,55,59` — `functional_completeness`
  structural induction; `grind`/`grind [Vector.tail_cons, Vector.head_cons]` fail (cutsat). Likely
  fixable by unfolding `getPutativeRootWithHash`/`generateProof`/`buildMerkleTreeWithHash` (Defs.lean
  :100/135/170) + `getRootValue` with `simp [..., ih, Vector.tail_cons, Vector.head_cons]`.
- `VCVio/CryptoFoundations/MerkleTree/Inductive/Extractability.lean` — `grind` failures (deeper,
  tree extractor goals).
- A full `lake build` sweep of the VCVio lib is needed to enumerate the rest; treat this as a
  v4.29→v4.30 port of the VCVio library, not a one-off.

## Disk-full finding (blocks large rebuilds)

`/` (`/dev/nvme0n1p2`, 1.9T) is **100% full** (~8–11G free). The toolchain bump invalidated part of
the Mathlib olean cache, so builds were recompiling `Mathlib.CategoryTheory.*` etc. — large olean
churn — and tool stdout capture hit `ENOSPC` in `/tmp`. Reclaimed ~3G safely by deleting regenerable
codegen intermediates (`rm -rf .lake/**/build/ir`, oleans untouched). Sibling worktrees
(`~/arklib-lane-*`, `~/arklib-issue8`, …) and `rs-proximity-gaps` (14G) hold most of the rest; do not
delete other agents' worktrees. A full Mathlib rebuild needs more headroom than currently exists.

## Net

OracleReduction bricks cannot be build-verified until the VCVio v4.30 port completes; proximity-gap
bricks until CompPoly settles. Three VCVio modules are ported (diffs above). The n-ary
`seqCompose → binary append` reduction bricks for #25 are drafted in
`ArkLib/OracleReduction/Composition/Sequential/General.lean`
(`seqCompose_perfectCompleteness_of_append`), pending the port for CI verification.

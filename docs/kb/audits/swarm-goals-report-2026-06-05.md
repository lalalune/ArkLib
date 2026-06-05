# Swarm Goals Report

Date: 2026-06-05

Baseline report: [`zkvm-total-verification-report-2026-06-05.md`](zkvm-total-verification-report-2026-06-05.md)

Primary ledger: [`proximity-prize/GRIND-LEDGER.md`](proximity-prize/GRIND-LEDGER.md)

## Purpose

This report is the current dispatch note for a swarm of subagents working on ArkLib verification
closure. Treat the baseline report as the status source of truth and this file as the coordination
brief for the next wave of work.

## Current Baseline

As of the latest validation evidence on 2026-06-05, `./scripts/validate.sh` reached the Data
warning-budget check and reported `No ArkLib/Data non-sorry warnings found.` That run then failed
during the build phase for
`ArkLib.Data.CodingTheory.ProximityGap.BCIKS20.ListDecoding.Agreement`: Lean emitted only the known
`sorry` warnings for that file, then Lake reported a missing generated `Agreement.olean`. A direct
follow-up build of
`ArkLib.Data.CodingTheory.ProximityGap.BCIKS20.ListDecoding.Agreement` succeeded and produced the
artifact, so treat the original failure as a transient Lake/artifact blocker unless it reproduces in
the next full `./scripts/validate.sh` run.

Recent validation repair work also removed several transient blockers: the Binius ring-switching
prelude was updated to the profile-aware sumcheck context, `Whir/Folding.lean` was restored after a
duplicate appended block caused redeclaration failures, `Whir/FoldingScratchDev.lean` was reduced to
a declaration-free compatibility shim that points to the production
`Fold.folding_preserves_listdecoding_base_of_mca_bridge` theorem, `GK16Wronskian` was made to extend
the existing `ProximityPrizeLeaves` folded-Wronskian primitives instead of redeclaring them, and new
Data warning-budget failures in `ListDecoding/Bounds`, `AGL23Barrier`, `CZ25CapacityReduction`,
`BKR06SubspacePoly`, `RSListSize`, and `HenselSeriesCoeff` were reduced to zero non-sorry warnings.
Direct builds of `ArkLib.ProofSystem.Whir.FoldingScratchDev` and
`ArkLib.Data.CodingTheory.ProximityGap.BCIKS20.ListDecoding.Agreement` succeeded after these fixes.
Re-run `./scripts/validate.sh` before starting a new warning-budget batch because multiple agents
are changing umbrella imports, WHIR files, and proximity-prize files concurrently.

The proximity-prize keystone has a real conditional bridge in
`ArkLib.BetaToCurveCoeffPolys.curveCoeffPolys_of_betaRec`, but it still needs its section-5
extraction/setup hypotheses supplied and connected to the in-place `Curves.lean` theorem.

The existing audit distinguishes genuine kernel-clean bricks from wrappers that assume the target
goal. Subagents must preserve that distinction. A result only counts when it is kernel-clean or when
its remaining assumptions are explicitly named and justified as external section-5 data.

## Goals

1. Close the proximity-prize keystone without duplicating already completed work.
2. Assemble the real route from `betaRec` to `CurveCoeffPolys` by supplying the missing section-5
   data: matching points/cardinality, divisibility `Hlift H ∣ R`, gamma recentering, representative
   and degree hypotheses, and the `Pz`/boundary facts required by the existing conditional theorem.
3. Replace the trivial in-tree `beta_regular` path with `betaRec`, then prove `hcoeffPoly` and close
   `correlatedAgreement_affine_curves` in `Curves.lean`.
4. De-taint downstream STIR, WHIR, and FRI round-by-round soundness only after the upstream theorem
   is genuinely closed.
5. Reduce remaining executable `sorry`s where they sit on active proof paths, prioritizing real
   proof discharge over wrapper APIs.
6. Keep the ArkLib/Data warning budget at zero non-sorry warnings and make `./scripts/validate.sh`
   green by fixing the umbrella-imported build blockers.
7. Audit external admits, conjectures, and explicit hypotheses, separating acceptable formal
   interfaces from unresolved mathematical obligations.
8. Map claimed ArkLib theorems to the full zkVM verification stack and state which end-to-end
   components remain outside ArkLib.

## Subagent Instructions

Work from the current checkout and read the baseline report before starting. Avoid editing generated
files such as `ArkLib.lean` or derived output under `.lake/`, `blueprint/web/`, `blueprint/print/`,
`dependency_graphs/`, or `home_page/docs/`. Do not revert changes made by other agents. Coordinate
before touching shared high-contention files such as `Curves.lean`, `Agreement.lean`, and the
proximity-prize bridge files.

Every subagent report must include exact files, declarations, commands run, proof status, axiom
status where relevant, remaining assumptions, and blockers. Do not report a wrapper as proof
closure if it assumes the target theorem or the decisive witness. Prefer small kernel-clean Lean
proofs, targeted `lake build <module>` checks, and updates to the audit docs with concrete evidence.

## Suggested Workstreams

- Keystone integration: start from `ArkLib/ToMathlib/BetaToCurveCoeffPolys.lean` and the
  integration notes under `docs/kb/audits/proximity-prize/integration-2026-06-05/`; connect the
  existing `betaRec` bridge to section-5 data rather than re-proving the bridge.
- Gamma and beta path: fix the `x₀`/gamma recentering issue, replace `β_regular` with `betaRec`,
  and thread the resulting hypotheses into the `Curves.lean` front door.
- Validation repair: preserve the zero ArkLib/Data non-sorry warning budget, then re-run
  `./scripts/validate.sh`; if the prior `Agreement.olean` artifact failure reproduces, isolate
  whether it is a Lake artifact issue or a hidden elaboration failure.
- Sorry audit: inventory remaining executable `sorry`s on proof-critical paths and distinguish
  active gaps from documentation-only or intentionally abstract interfaces.
- ZKVM map: extend the baseline report's whole-stack analysis with theorem-to-component evidence
  and clear statements of what ArkLib does not yet verify.

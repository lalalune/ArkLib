# Swarm Goals Report

Date: 2026-06-05

Baseline report: [`zkvm-total-verification-report-2026-06-05.md`](zkvm-total-verification-report-2026-06-05.md)

Primary ledger: [`proximity-prize/GRIND-LEDGER.md`](proximity-prize/GRIND-LEDGER.md)

## Purpose

This report is the current dispatch note for a swarm of subagents working on ArkLib verification
closure. Treat the baseline report as the status source of truth and this file as the coordination
brief for the next wave of work.

## Current Baseline

The ArkLib/Data non-sorry warning budget has been reported clean by recent validation runs. In the
live checkout, `lake build ArkLib` now completes after the JH01 close-ball proof stabilization and
the stale scratch-import cleanup. Re-run `./scripts/validate.sh` before starting a new warning-budget
batch because multiple agents are changing umbrella imports and scratch files concurrently. The
proximity-prize keystone has a real conditional bridge in
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
- Validation repair: preserve the zero ArkLib/Data non-sorry warning budget, then repair the
  umbrella-imported build blockers exposed by `./scripts/update-lib.sh` and `./scripts/validate.sh`.
- Sorry audit: inventory remaining executable `sorry`s on proof-critical paths and distinguish
  active gaps from documentation-only or intentionally abstract interfaces.
- ZKVM map: extend the baseline report's whole-stack analysis with theorem-to-component evidence
  and clear statements of what ArkLib does not yet verify.

# Issue #321 — STIR/WHIR blueprint closeout audit (2026-06-10)

Scope: the STIR/WHIR security-theorem half of the blueprint closeout (#320 umbrella; #322 covers
FRI/Batched-FRI and coding theory). Cross-checked against the formalization state on `main` as of
2026-06-10 (post `a1e6fcc3c` blueprint refresh).

## What the blueprint now claims, and why it is honest

The `a1e6fcc3c` refresh rewrote the STIR chapter against the landed protocol objects
(`Stir/MultiRoundAssembly.lean`, `Stir/CheckingVerifier.lean`, `Stir/FullChain.lean`) and added the
WHIR keystone surface. The discipline adopted there — and the thing future editors must preserve —
is **named-hypothesis honesty**: open mathematical cores appear as named `Prop`-valued residuals
(`stirCheckingCABridge`, `StrictCoeffPolysResidual`, `mca_johnson_bound_CONJECTURE`), never as
`axiom`s and never silently absorbed into theorem statements.

## Formalization status snapshot (issue #301 / #302)

STIR (#301):
- `stir_main` / `stir_rbr_soundness` remain `def … : Prop` *statements* in `Stir/MainThm.lean`;
  they are discharged through front doors (`stir_main_of_checkingIOP_CA`,
  `stir_rbr_soundness_of_stirVSpec_secure_gap`) whose soundness leg consumes named CA residuals.
- Perfect completeness is **proven end-to-end** (single round, 3-slot blocks, full chain
  `[C_fold] ++ (g, C_out, C_shift)×M ++ [p, C_fin]`, both function and vector wire formats).
- Unconditional-but-vacuous regimes are flagged as such: the small-field discharge
  (`stir_main_of_checkingIOP_small_field`) pins `secpar = 0`; the window-corner CA feed
  (`Stir/WindowCAFeed.lean`) is genuine (non-vacuous) but confined to `⌊δ·n⌋ = 0`.
- The open math at sub-unit budgets: the `stirCheckingCABridge` CA→RBR accounting, shared with
  #302/#304 through the `UnifiedProducer` keystone.

WHIR (#302):
- `whirVectorIOP` is constructed; RBR knowledge soundness is discharged at indicator budgets, with
  the Schwartz–Zippel sub-unit upgrade machinery landed (`Whir/SchwartzZippelCore.lean`,
  `Whir/ThresholdKSF.lean`).
- Corollary 4.11's unique-decoding branch is **proven at every folding arity**
  (`Whir/MCARscCurveUDR` arc); the Johnson-radius branch reduces to one node: the BCIKS20
  Claim 5.9 / Lemma A.1 Λ-weight kernel (`hlin` in the `Hab25JohnsonDichotomy` bundle shape).
- `mca_johnson_bound_CONJECTURE` stays a live conjecture in-tree; the blueprint must keep
  presenting it as such.

## Caveats that must not be edited away

1. The assembled STIR forwarding-shell IOPP's rbr-soundness residual is likely **false as stated**
   for the shell verifier — soundness claims route through the *checking* verifier only.
2. The single-domain wire model makes the per-round fold degenerate (`combine_single_self`);
   paper-STIR's degree reduction is not reflected, and per-round budgets differ accordingly.
3. Every "unconditional" CA instance in-tree is either small-field (`err⋆ ≥ 1`, no security) or
   window-corner (`⌊δ·n⌋ = 0`); the Johnson-regime core is open and tracked on #302/#304.

## Verification gate

`./scripts/validate.sh --site` is the closeout gate (build + Data warning budget + sorry census +
axiom audit + docs/kb checks + API docs + blueprint site). Gate runs and fallout are reported on
issue #320. Note the Data warning budget is repo-wide hygiene (predates the blueprint work and is
dominated by research-frontier files), so a warning-budget failure is not by itself a blueprint
regression — but the docs/kb and site legs are blueprint-owned and must be green.

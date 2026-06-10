# Honesty Audit Playbook

How to find unproven-but-presented-as-proven content: the laundering patterns the CI gates miss,
how to detect each one, and confirmed historical findings. Use this when auditing a landing report,
a "PROVEN" issue comment, or a grant-completion claim.

## What the gates already catch

`./scripts/validate.sh` catches: `sorry`/`admit` holes (`sorry_census.py`), forbidden tokens
(`native_decide`, `bv_decide`, undocumented `axiom` — `forbidden_tokens.py`), flagship-theorem
axiom drift (`axiom_audit.py`). An auditor's job is everything those *cannot* see.

## Laundering patterns the gates miss

1. **`def … : Prop` presented as a theorem.** A `Prop` *statement* compiles green forever without
   being proven. Check: is the headline name a `theorem`, or a `def`/`structure` whose *discharge*
   is what actually matters? Find the discharging declaration and audit *that*.

2. **Hypothesis smuggling.** A "proof" of `P` that is really `H → P` with `H` doing all the work.
   Check the full hypothesis list of the discharging theorem, not the issue-comment prose. The
   repo convention is honest *named* residuals (e.g. `stirCheckingCABridge`,
   `StrictCoeffPolysResidual`) — a hypothesis with an innocuous binder name (`h`, `hAux`) that
   encodes the open core is the dishonest variant.

3. **Vacuous-regime unconditionality.** A theorem can be unconditional because its regime makes
   the bound trivial (error budget `≥ 1` = no security). Confirmed instances (honestly flagged at
   landing, kept as exemplars): the small-field STIR discharge (`err⋆ ≥ 1` pins `secpar = 0`); the
   small-field `mca_johnson_bound_CONJECTURE_smallField`. Audit question: *is there a satisfiable
   parameter set where the statement says something nontrivial?* Demand a non-vacuity witness.

4. **Unsatisfiable statements.** The dual failure: a residual stated against the wrong object can
   be *false*, so "discharging" work grinds an impossible goal — e.g. rbr-soundness stated against
   a forwarding-shell verifier that checks nothing (#301, caught in audit 2026-06-10). Audit
   question: can a trivial adversary win the stated game outright?

5. **Stale-olean / elaboration laundering.** `#print axioms` run against stale `.olean`s, or a
   declaration that silently picked up `sorryAx` through a failing dependency, reports clean while
   the source no longer elaborates. Confirmed instance: the `hQin` `=`→`≥` drift left three
   `stir_main_of_checkingIOP_*` welds elaborating via `sorryAx` while the build "passed" on stale
   artifacts. Detection: rebuild the focused module from scratch, then `#print axioms` — and never
   pipe `lake env lean` through `tail`/`head` (it masks the exit code; capture to a file and check
   `$?`).

6. **Phantom landings.** Issue comments claiming "pushed `X`" where the commit never reached any
   ref (lost worktree, interrupted lane). Confirmed instance: `PzFamilyUD.lean` was imported by a
   merged commit but exists in no ref — every full build broke. Detection:
   `git log --all -S <symbol>` before believing any landing report.

7. **Probe-free conjecture formalization.** Formalizing a quantified statement nobody
   counterexample-searched. House rule (from #232): write an exact-arithmetic probe under
   `scripts/probes/` and run it *before* formalizing; cite the probe counts. Several would-be
   "theorems" died as probes (see `Data/CodingTheory/ProximityGap/DISPROOF_LOG.md`).

8. **Misformalization of a paper invariant.** The statement proves/refutes something subtly
   different from the paper (wrong quantifier order, wrong normalization, an invariant the paper
   treats as an *output* hypothesized as an *input*). Detection: re-derive the statement from the
   paper independently before trusting a refutation or a proof; record the paper-to-Lean mapping
   next to the statement.

## Audit checklist (per claimed landing)

- [ ] `git log --all -S <headline-name>` — the commit exists and is on `main`.
- [ ] The headline is a `theorem` (or its discharge is identified and audited).
- [ ] Full hypothesis list read; every nontrivial hypothesis is a *named*, tracked residual.
- [ ] Non-vacuity: a satisfiable nontrivial parameter regime exists (or the vacuity is flagged).
- [ ] Fresh focused rebuild + `#print axioms` shows exactly `[propext, Classical.choice, Quot.sound]`.
- [ ] No new `axiom`, `native_decide`, `unsafe`, `implemented_by` in the diff.
- [ ] Issue comment matches what was actually proven (regime, budget, verifier variant).

# F-series statement-defect catalogue

## Purpose

This note records statement-level defects found while formalizing the proximity-prize material. The
common lesson is that a failed Lean proof can reveal a paper-interface mismatch rather than a missing
tactic.

## Catalogue

### F1: Power-series substitution at off-center points

Mathlib's `PowerSeries.HasSubst` requires the substituted series to have nilpotent constant
coefficient. Over a field this means constant coefficient zero. For the BCIKS shift `X -> X - x0`,
that condition holds only at `x0 = 0`. Off-center substitution therefore needs an explicit
hypothesis or a different formal interface.

Formal anchor: `ArkLib/ToMathlib/SubstFieldCaveat.lean`.

### F2: Claim 5.11 dependency DAG

The Claim 5.11 route is not a single isolated counting lemma. It depends on a structured chain of
section data, matching-set hypotheses, numerator bounds, and boundary cardinality inputs. The
residualized API should keep that DAG visible instead of hiding it behind one opaque admit.

### F3: Telescope-style equalities

Several prose arguments use telescoping equalities across dependent transports. In Lean these become
separate transport lemmas, not rewriting trivia. Treating them as named bridge lemmas keeps the proof
surface honest.

### F4: Nominal bundling

Some statements quantify over data that is only nominally bundled in the paper. The formal version
must distinguish inputs, derived witnesses, side conditions, and residual hypotheses so downstream
theorems do not silently assume conclusions.

### F5: Universal t blowup

Arguments that move from fixed `t` to all `t` can introduce a hidden quantifier blowup. The formal
interface should state whether the witness data is uniform in `t` or reconstructed separately for
each `t`.

### F6: Real-delta challenge encoding collapse

Challenge encodings that are clean over discrete parameters can collapse when phrased with a real
`delta` before rounding. Formal statements should make the integer parameter and its real
interpretation separate objects with explicit comparison lemmas.

## Methodological takeaway

The right response to these defects is not to weaken the final theorem silently. Keep the original
mathematical intent visible, isolate the exact missing bridge as a named residual, and prove the
remaining reductions against that residual.

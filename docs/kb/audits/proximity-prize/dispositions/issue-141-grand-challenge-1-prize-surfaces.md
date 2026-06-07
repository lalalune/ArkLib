# Issue 141: Grand Challenge 1 open prize surfaces (proximity)

Status: resolved (tracking issue; open mathematics retained as named hypotheses).

## Scope

Two genuinely open ABF26 Grand Challenge 1 conjectures live as honest `def : Prop` surfaces.
They are the actual research prize (the beyond-UDR Guruswami–Sudan list-decoder mass bound),
not closeable formalization debt:

- `ProximityGap.GrandChallenges.mcaConjecture`
  ([GrandChallenges.lean](../../../../ArkLib/Data/CodingTheory/ProximityGap/GrandChallenges.lean)) —
  uniform polynomial upper bound on `ε_mca`, ABF26 §4.5 (`conj:mca-conjecture`).
- `ProximityGap.MCAGS.epsMCAgs_prizeBound_conjecture`
  ([MCAGS.lean](../../../../ArkLib/Data/CodingTheory/ProximityGap/MCAGS.lean)) — GS-exposed form
  of Grand Challenge 1, stated against the real GS-exposed definitions (`epsMCAgs`, `gsListBound`).

## Decision

- Keep both as named `Prop` surfaces (hypotheses), not theorems. Carrying either as a theorem
  with `sorry` would launder the open prize into `sorryAx`; carrying it via an equivalent
  packaged form would launder it just as much. Neither is done.
- Every consumer takes the surface as an *explicit hypothesis* and derives a conditional result.
  These conditional reductions are the permitted partial progress and are linked to #141:
  - `mcaConjecture` consumers (all take `h : mcaConjecture`):
    `nonempty_mcaLowerWitness_of_mcaConjecture`, `exists_mcaLowerWitness_of_mcaConjecture`, the
    `ignoredSource`-named adapters in `GrandChallenges.lean`, and the lattice-threshold links
    `mcaThresholdExists_of_mcaConjecture` / `mcaThreshold_spec_of_mcaConjecture` (and their
    `ignoredSource` aliases) in `GrandChallengesLattice.lean`.
  - `epsMCAgs_prizeBound_conjecture`: the conditional reduction
    `MCAGS.epsMCAgs_prizeBound_of_massBound` in `MCAGSWitness.lean` derives the conjecture's
    existential from the explicitly-named per-stack mass bound `epsMCAgsMassBound`; the open
    beyond-UDR content is isolated into that hypothesis (plus the pivot-covering and
    faithful-family frontiers), not proved.
- Each surface's docstring now carries an explicit "Open-prize tracking (Issue #141)" paragraph
  cross-linking the two siblings, so the prize surfaces are not silently buried under local
  residual tickets (#52/#66/#78).
- The survey ledger
  ([open-problems-list-decoding-and-correlated-agreement.md](../../open-problems-list-decoding-and-correlated-agreement.md))
  rows `GC1`, `GC1-prize`, and `C4.5` record the #141 tracking and the named-hypothesis status.

## Relationship to neighbouring residual tickets

The `mcaConjecture` API status (compatibility surface vs. `ignoredSource` adapters) is the
subject of #78 (resolved). The GS-exposed reduction plumbing (mass bound, pivot covering,
faithful family) is the subject of #52/#66. #141 sits above both: it tracks the *open
mathematics* of the two prize surfaces themselves, so that the prize is visible independently of
those local reduction tickets.

## Regression search

```sh
rg -n 'mcaConjecture|epsMCAgs_prizeBound_conjecture|#141|Grand Challenge 1' \
  ArkLib/Data/CodingTheory/ProximityGap/GrandChallenges.lean \
  ArkLib/Data/CodingTheory/ProximityGap/GrandChallengesLattice.lean \
  ArkLib/Data/CodingTheory/ProximityGap/MCAGS.lean \
  ArkLib/Data/CodingTheory/ProximityGap/MCAGSWitness.lean \
  docs/kb/audits/open-problems-list-decoding-and-correlated-agreement.md \
  docs/kb/audits/proximity-prize
```

Expected result: both surfaces remain `def : Prop`; every exported consumer takes the surface as
an explicit hypothesis; the docstrings and the `GC1`/`GC1-prize`/`C4.5` ledger rows reference
#141. This is a tracking/visibility decision, not a rendered-paper theorem obligation — the two
conjectures stay open by design.

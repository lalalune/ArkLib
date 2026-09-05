# Lean-checked algebra and anchor selection for the MCA basis

Nine supporting theorems for the
[four-deletion construction](astra_mca_four_delete-2026-09-05.md) now pass
local Lean 4.30.0-rc2 with the repository's exact Mathlib pin. They verify
the initial determinant algebra, cofactor independence, fixed-anchor
selection, and division identities. **The complete production construction
and threshold theorem are not yet formalized.** The production upper bound
remains a written result; the matching universal lower bound remains open.

The source is
[`astra_mca_polynomial_basis.lean`](../../scripts/probes/astra_mca_polynomial_basis.lean).
It imports only the needed polynomial and ring-tactic modules. The existing
[two-version auxiliary workflow](../../.github/workflows/proximity-strip-proof.yml)
now includes all nine declarations and checks their explicit axiom reports.

## What the formal statements establish

`initial_determinant` proves the displayed old-basis identity in any
commutative ring, given `i*i=-1` and `j*(1-i)=1`. The variable h is arbitrary;
the determinant is independent of it and equals `t^4-1`. This is the
algebraic identity needed with `t=X^(n/4)` and h the fourth-quarter
interpolant. It does not itself construct that interpolant.

`change_basis_determinant` and `divided_determinant` prove how constant
linear combinations and exact column divisions change the determinant.
`remove_root_exact` applies the monic-linear root-division identity, and
`remove_root_degree` supplies the degree drop, including the zero case.

`cofactor_pair_independent` takes polynomials satisfying

```text
F_0=G_0+C*W_0,  F_1=G_1+C*W_1,
F_0,F_1 vanish on A;  G_0,G_1 vanish on B,
max(natDegree F_0,natDegree F_1) < card(A union B),
F_0*G_1-F_1*G_0 != 0.
```

It proves that W_0,W_1 have no nonzero constant scalar relation. A proposed
relation would give equal combinations of F and G, vanishing on A union B.
The root count makes both combinations zero, and the nonzero determinant
then forces both scalars to be zero. All these hypotheses are explicit;
the theorem does not silently assume a polynomial-module basis result.

## A simpler and quantitative anchor choice

`exists_separated_at_anchor` shows that **any** point eta with a nonzero
W evaluation row has a partner xi in A, provided the W polynomials are
independent and both have degree less than card A. No search over both
anchors is necessary for the existence proof.

The quantitative theorem `many_separated_at_anchor` gives

```text
card {xi in A : W_0(xi)*W_1(eta)-W_1(xi)*W_0(eta) != 0}
  >= card A - D
```

when both W polynomials have natural degree at most D. The determinant in
xi is a nonzero polynomial of degree at most D, so at most D candidates
are excluded. This holds over any field, regardless of its cardinality.

For the written construction set `a=(n-1)/3`, `k=n/2`. The first step has
`card A=a` and W-degree bound `k-(a+1)`. After one deletion pair these
become `a-1` and `(k-1)-(a+1)`. Both differences are `(a+1)/2`.
At production this is 178956971. The exact arithmetic is checked by
`production_anchor_margins`. Applying the count to the full construction
still requires the domain, nonzero-row and degree hypotheses to be wired.

## Remaining assembly

The Lean file does not yet construct H with its prescribed values, instantiate
the initial degree and pair-region data, or package two consecutive deletions
with their preserved roots and simple determinant. The four evaluation
functionals, finite-field ratio selection, actual same-support MCA witnesses,
probability bound and threshold ledger also remain to be connected to this
source. Existing repository lemmas already cover parts of that later chain,
including
[`_FiniteFunctionalRatioAvoidance.lean`](../../ArkLib/Data/CodingTheory/ProximityGap/Frontier/_FiniteFunctionalRatioAvoidance.lean)
and the support channel in
[`_SYZ3OverBudgetStackWitness.lean`](../../ArkLib/Data/CodingTheory/ProximityGap/Frontier/_SYZ3OverBudgetStackWitness.lean).
Their existence is not evidence that the new assembly is complete.

This formalization establishes supporting algebra for an upper-bound
construction. It supplies no universal lower bound, new companion score,
or grand-prize solution.

## Local reproduction

The checked environment is Lean 4.30.0-rc2 and Mathlib commit
`5450b53e5ddc75d46418fabb605edbf36bd0beb6`, matching the repository manifest.
The official macOS Lean archive was verified against release SHA-256
`6a23d26241fd78bcc3d1c24be97341bfe3f4635f2e6feabcbb5863035290ab1b`.
A separate Mathlib checkout hosts the selected 1380-module cache; the full
ArkLib build was not run. This keeps iteration independent of the cold
ArkLib frontier cache.

From a matching Mathlib environment, run:

```sh
lake env lean /absolute/path/to/arklib/scripts/probes/astra_mca_polynomial_basis.lean
```

The local audit requires all nine named reports, rejects compiler errors,
warnings and `sorryAx`, and permits only `propext`, `Classical.choice`, and
`Quot.sound`. The arithmetic theorem uses no axioms. Cross-version CI status
is recorded separately once its run completes.

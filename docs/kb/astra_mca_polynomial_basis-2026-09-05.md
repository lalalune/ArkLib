# Lean-checked construction of the MCA polynomial basis

Thirty-one supporting theorems for the
[four-deletion construction](astra_mca_four_delete-2026-09-05.md) now pass
local Lean 4.30.0-rc2 with the repository's exact Mathlib pin. They verify
the complete polynomial basis construction from a root domain: fourth-root
parameters, the balanced quarter partition, interpolation, the determinant,
and two consecutive deletion pairs. **The MCA witnesses and threshold
theorem are not yet formalized for this construction.** The production
upper bound remains a written result; the matching universal lower bound
remains open.

The source is
[`astra_mca_polynomial_basis.lean`](../../scripts/probes/astra_mca_polynomial_basis.lean).
It imports only the needed polynomial and ring-tactic modules. The existing
[two-version auxiliary workflow](../../.github/workflows/proximity-strip-proof.yml)
now includes all thirty-one declarations and checks their explicit axiom reports.

## The assembled root-domain theorem

`production_deleted_basis_from_roots` has exactly these mathematical
inputs: a field F, a finite set Omega with 1073741824 elements, and
`x^1073741824=1` at every point of Omega. It proves existence of A, B, S
and I with

```text
A union B union S union I = Omega,
A, B, S pairwise disjoint; I disjoint from their union,
card A=card B=357913939,
card S=357913942, card I=4,
PairRegionBasis A B S 536870910.
```

The last line contains four constructed polynomials with the required
roots and pair agreements, degree at most `k-2`, and determinant equal
to a nonzero scalar times the locator of A union B union S. This is the
polynomial input needed for the later four-generator MCA argument.
The field may be finite or infinite; only Omega is required to be finite.

`exists_fourth_root_parameters` constructs i and j from the domain.
If all its points satisfied `x^(2m)=1`, a root bound would give at most
2m points, contradicting its size 4m. A point outside that smaller root
set supplies `i=x^m`, with `i*i=-1`, and `j=(1-i)^(-1)`.

`exists_balanced_quarter_partition` proves that the four fibers of
`x -> x^m`, at `1,i,-1,-i`, each contain m points. The fibers are
disjoint, each has at most m points, and they cover all 4m points.
For `m=3q+1`, splitting the fourth fiber into q, q and q+1 points gives
the initial A, B, S sizes `m+q,m+q,m+q+1`. Production uses
`m=268435456` and `q=89478485`.

`interpolate_power_fiber` constructs the required H by Lagrange
interpolation. Its assigned fourth-fiber values are i, j*j and zero.
The checked coefficient identities imply `2*j*j=i`, so j*j supplies
the prescribed i/2 value directly. `initial_basis_from_interpolant`
checks the displayed polynomial formulas, all pair agreements, degree
bounds and determinant; `initial_basis_of_quarter_partition` supplies
H automatically. The existing deletion assembly then constructs I and
the reduced basis.

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

## Preservation under selected point deletions

`simple_locator_derivative` proves that the derivative of
`c*product_{y in S}(X-y)` is nonzero at every x in S when c is nonzero.
The proof factors out X-x and evaluates the derivative as a product of
nonzero differences. It works over every field, without a characteristic
assumption or a squarefreeness hypothesis hidden in the statement.

`cofactor_row_nonzero` then checks the step used to select an anchor:
at a point where both F components or both G components vanish, the W
row cannot also vanish if the determinant has a simple root there.
Otherwise all four F/G values would vanish, forcing the determinant's
derivative to vanish.

The defined operation is

```text
deleteAt(W0,W1,P0,P1,x)
  = (W1(x)*P0 - W0(x)*P1) / (X-x).
```

It uses polynomial division by a monic linear factor.
`killed_combination_roots` proves exact divisibility for the F, G and W
components at a valid pair-region point. `delete_at_preserves` proves
the divided relation `F'=G'+L*W'` and every other F/G root;
`delete_at_degree` bounds the new degree by D-1. The underlying lemmas
`remove_root_preserves_eval` and `remove_root_preserves_relation` also
handle zero polynomial components.

For selected xi and eta, let
`s=W0(xi)*W1(eta)-W1(xi)*W0(eta)`. The theorem
`two_anchor_deleted_determinant` proves

```text
(X-xi)*(X-eta)*(F'_0*G'_1-F'_1*G'_0)
  = s*(F0*G1-F1*G0),
F'_0*G'_1-F'_1*G'_0 != 0,
```

given s nonzero, the original determinant nonzero, and the selected F/G
root conditions. `deleted_locator_formula` cancels the two linear factors
and identifies the new determinant as `s*c` times the locator of
`(S.erase xi).erase eta`, when xi and eta are distinct members of S.
These identities support the assembled existence theorems below.

## Assembled deletion and production dimensions

`PairRegionBasis A B S D` records the four polynomial components, their
degree bounds, the F roots on A, the G roots on B, agreement on S, and
the determinant identity with a nonzero scalar and the full domain locator.
It is explicit polynomial data, not an assumed conclusion of the deletion
argument.

`cofactor_of_agreement` derives W and the bound
`natDegree W <= D-card S` from agreement of F and G on S. The proof
shows that the locator of S divides F-G, including when F-G is zero.
The assembled theorem no longer takes these cofactors as extra input.

`exists_basis_after_deletion` assumes pairwise disjoint A, B and S, an
initial `PairRegionBasis`, and the two strict numerical guards

```text
D < card(A union B),
D-card S < card A.
```

For any chosen eta in B, it proves that some xi in A gives
`PairRegionBasis (A.erase xi) (B.erase eta) S (D-1)`. The proof derives
cofactor independence, a nonzero anchor row and a separated partner, then
checks every field of the resulting basis. The determinant remains a
nonzero scalar times the locator of precisely the remaining points.

`exists_basis_after_two_deletions` applies this result twice. It tracks
the erased point sets, their disjointness and cardinalities, and all four
degree/root-count guards. The two A points are distinct, as are the two
B points; disjointness separates the A and B choices.

At the production dimensions, `production_basis_after_four_deletions`
checks the resulting implication:

```text
Input:  PairRegionBasis A B S 536870912,
        card A=card B=357913941, card S=357913942,
        A, B, S pairwise disjoint.
Output: A' subset A, B' subset B,
        card A'=card B'=357913939,
        PairRegionBasis A' B' S 536870910.
```

This theorem is a transformation of supplied initial data. The newer
`production_deleted_basis_from_roots` also constructs those initial data
from the domain hypotheses, using the interpolation and partition results.
Neither statement is a production threshold theorem.

## Remaining assembly

The root-domain theorem still needs to be instantiated with the existing
production field and root certificate, including the representation of
the evaluation domain in the actual Reed-Solomon code. The four evaluation
functionals, finite-field ratio selection, actual
same-support MCA witnesses, probability bound and threshold ledger also
remain to be connected. Existing repository lemmas cover parts of that
later chain, including
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
A separate Mathlib checkout hosts the selected polynomial module cache; the full
ArkLib build was not run. This keeps iteration independent of the cold
ArkLib frontier cache.

From a matching Mathlib environment, run:

```sh
lake env lean /absolute/path/to/arklib/scripts/probes/astra_mca_polynomial_basis.lean
```

The local audit requires all thirty-one named reports, rejects compiler errors,
warnings and `sorryAx`, and permits only `propext`, `Classical.choice`, and
`Quot.sound`. The arithmetic theorem uses no axioms. Cross-version CI status
is recorded separately once its run completes. The earlier eighteen-theorem
revision `8a8f40fc812039d22151922f15c087cd5d1e5ea8` passed both versions in
[run 33986904416](https://github.com/lalalune/ArkLib/actions/runs/33986904416);
that run does not verify subsequent assembly theorems.

The twenty-two-theorem revision `3c7470b6ae268279832bffc310bcefb90f4c188a`
compiled in both jobs, but the companion job of
[run 33987181911](https://github.com/lalalune/ArkLib/actions/runs/33987181911)
failed the warning audit because Mathlib renamed a locator-degree lemma.
The current source calculates that degree directly by induction, preserving
the strict warning check. A later CI run is needed to verify that repair
and the nine new construction theorems on the companion pin.

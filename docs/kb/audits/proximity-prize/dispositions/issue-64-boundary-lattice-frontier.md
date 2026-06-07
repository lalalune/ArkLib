# Issue #64 - exact lattice boundary disposition

**Status:** Disposed as originally stated. The requested bare exact-boundary residual is false.

The old issue asked to discharge the square-root lattice branch by proving that a merely nonempty
closed-boundary good-coefficient set forces correlated agreement. Current source instead contains a
formal counterexample:

- [`BoundaryCardResidualRefutation.lean`](../../../../../ArkLib/Data/CodingTheory/ProximityGap/BoundaryCardResidualRefutation.lean)
  constructs `iota = Fin 4`, `F = ZMod 5`, `deg = 1`, `k = 2`, and a stack `uBad`.
- `not_boundaryCardResidual` refutes the original cardinality residual.
- `not_boundaryCardLatticeResidual` refutes the isolated square-lattice residual.
- `not_boundaryCardLatticeData` refutes the current stronger lattice-data package for the same
  witness, since that package requires more good coefficients than the field contains.
- `not_boundaryCardQuantizationResiduals` refutes the packaged strict-plus-lattice residual surface
  through its lattice component.
- `not_boundaryProbabilityResidual` refutes the probability residual at the same endpoint.
- `not_delta_epsilon_correlatedAgreementCurves_boundary` refutes the corresponding
  `delta_epsilon_correlatedAgreementCurves` conclusion with `epsilon = errorBound`.

The mechanism is small. At `deg = 1` over four evaluation points, the Reed-Solomon code consists of
constant words, the Johnson endpoint is `delta = 1 / 2`, and `errorBound = 0`. The coefficient
`z = 0` gives a good curve point, so the good set and the probability premise are positive. But
`jointAgreement` would require two coordinates on which the word `domain : Fin 4 -> ZMod 5` agrees
with a constant codeword; injectivity of `domain` makes any such set have size at most one.

## Current Source Frontier

The exact boundary split still lives in
[`BoundaryCardResidual.lean`](../../../../../ArkLib/Data/CodingTheory/ProximityGap/BoundaryCardResidual.lean).

- `exists_lt_floor_eq_of_floor_lt` gives the non-lattice strict-subradius reduction.
- `floor_lt_of_lt_of_lattice` and `not_exists_lt_floor_eq_of_lattice` prove that the same-floor
  strict-subradius route is impossible at a lattice endpoint.
- `BoundaryCardLatticeResidual` is now documented as an assumption surface, not a theorem target
  derivable from nonemptiness.
- `BoundaryCardLatticeData` is a strong sufficient data package. The necessary-size lemmas
  `BoundaryCardLatticeData.field_card_ge_of_pos` and
  `BoundaryCardLatticeData.not_of_field_card_lt_of_pos` make explicit that the package is much
  stronger than positive-good-set nonemptiness in small fields. The refutation file instantiates
  this necessary-size obstruction for the `ZMod 5` witness.

The curve-facing source in
[`Curves.lean`](../../../../../ArkLib/Data/CodingTheory/ProximityGap/BCIKS20/Curves.lean) now records
that `BoundaryProbabilityResidual` is also only an assumption surface at the exact endpoint:
`errorBound = 0` collapses the probability threshold to positivity.

## Literature And Search Disposition

The searched literature supports treating this as a mismatch in the formal residual, not as a
missing endpoint proof.

- [BCIKS20 / ECCC TR20-083](https://eccc.weizmann.ac.il/report/2020/083/) states the RS proximity
  gap for radii smaller than the Johnson/Guruswami-Sudan list-decoding bound. That strict-radius
  language matches the in-tree non-lattice/strict-interior route and does not provide a bare
  closed-endpoint nonemptiness theorem.
- [Gao-Kan-Li 2024](https://eprint.iacr.org/2024/1810.pdf) improves quantitative proximity gaps
  within the one-and-a-half Johnson bound. Its setup is quantitative; it is not a proof that one
  good curve point at the closed Johnson endpoint forces correlated agreement.
- [On Proximity Gaps for Reed-Solomon Codes, 2025](https://www.math.toronto.edu/swastik/rs-proximity-gaps-2025.pdf)
  and [ECCC TR25-169](https://eccc.weizmann.ac.il/report/2025/169) study improved quantitative
  proximity-gap bounds and matching limitations. They reinforce that endpoint and near-endpoint
  statements require quantitative hypotheses.
- [From List-Decodability to Proximity Gaps](https://eprint.iacr.org/2025/870) explicitly routes
  proximity-gap statements through list-decodability hypotheses and quantitative error terms.
- [On Reed-Solomon Proximity Gaps Conjectures](https://eprint.iacr.org/2025/2046) is part of the
  same recent barrier literature: correlated-agreement claims that are too strong imply
  list-decoding strength that RS codes do not have.
- [Optimal Proximity Gap for Folded Reed-Solomon Codes via Subspace Designs](https://arxiv.org/abs/2601.10047)
  and [ECCC TR25-166](https://eccc.weizmann.ac.il/report/2025/166/) give positive proximity-gap
  results for folded/subspace-design/random RS-style families under their own structural and
  quantitative hypotheses.
- [A Syndrome-Space Approach to Proximity Gaps and Correlated Agreement for Random Linear Codes](https://arxiv.org/abs/2605.07595)
  is related newer work on random linear codes, but it does not imply the false bare RS endpoint
  residual used by issue #64.
- GitHub issue/code search found no external ArkLib proof of the residual. Code search returns
  definitions, mirrors, and downstream consumers of `delta_epsilon_correlatedAgreementCurves`, not
  a proof of the false endpoint residual. The live repository issue is already closed after earlier
  route-(a) work, but the stronger current conclusion is that route (b), as encoded by
  `BoundaryProbabilityResidual` with `epsilon = errorBound`, is also false.

## Replacement Obligation

Do not try to prove:

```lean
BoundaryCardResidual
BoundaryCardLatticeResidual
BoundaryCardLatticeData
BoundaryCardQuantizationResiduals
BoundaryProbabilityResidual
delta_epsilon_correlatedAgreementCurves ... (epsilon := errorBound ...)
```

from positive-good-set nonemptiness at the exact square-root endpoint. These are refuted by
`BoundaryCardResidualRefutation`.

Future boundary work must strengthen or change the interface. Plausible honest targets are:

- a nonzero quantitative threshold stronger than `k * errorBound` when `errorBound = 0`;
- an explicit cardinality hypothesis such as the bounds packaged in `BoundaryCardLatticeData`;
- a coefficient-polynomial extraction hypothesis matching the real Section 5 machinery;
- a theorem restricted to strict radii `delta < 1 - sqrtRate`, where the published arguments and
  the in-tree quantization route have compatible hypotheses.

## Focused Audit Commands

```sh
rg -n 'not_boundaryCardResidual|not_boundaryCardLatticeData|not_boundaryCardQuantizationResiduals|not_boundaryProbabilityResidual|not_delta_epsilon_correlatedAgreementCurves_boundary' ArkLib/Data/CodingTheory/ProximityGap/BoundaryCardResidualRefutation.lean
rg -n 'floor_lt_of_lt_of_lattice|not_exists_lt_floor_eq_of_lattice|field_card_ge_of_pos' ArkLib/Data/CodingTheory/ProximityGap/BoundaryCardResidual.lean
python3 scripts/forbidden_tokens.py ArkLib/Data/CodingTheory/ProximityGap/BoundaryCardResidual.lean ArkLib/Data/CodingTheory/ProximityGap/BoundaryCardResidualRefutation.lean
lake build ArkLib.Data.CodingTheory.ProximityGap.BoundaryCardResidualRefutation:olean
```

# ArkLib proof-gap index (2026-06-06)

This index closes the umbrella audit role for ArkLib proof gaps. It records how to reproduce the
census and where each named residual family is tracked. Focused issues own the remaining proof work;
this document prevents the same residual surfaces from being rediscovered as anonymous holes.

## Audit commands

Raw proof holes and project-level assumptions:

```sh
rg -n --glob '*.lean' '^\s*(sorry|admit)\b|:=\s*(by\s+)?(sorry|admit)\b|by\s+(sorry|admit)\b|\baxiom\s+[A-Za-z_]|opaque\s+[A-Za-z_]' ArkLib
```

Named residual APIs:

```sh
rg -n --glob '*.lean' '^(noncomputable\s+)?(def|structure|class|theorem|lemma)\s+\w*Residual\w*|\b\w*Residual\w*\s*:' ArkLib
```

Placeholders, explicit hypotheses, and roadmap markers:

```sh
rg -n --glob '*.lean' 'opaque\s+\w+|placeholder|stub|TODO|FIXME|named residual|explicit hypothesis|remaining unproven|only remaining|sole residual|single remaining' ArkLib
```

## Focused issue map

| Residual surface | Tracking issue |
|---|---|
| BCIKS20 correlated agreement: `StrictCoeffPolysResidual`, `BoundaryCardResidual` | #7 |
| BCIKS20 Claim 5.7 graph/count/factorization residuals | #8 |
| BCIKS20 Appendix-A Hensel term weights and Faà-di-Bruno vanishing | #9 |
| Hab25 Johnson MCA residuals | #10 |
| ABF26 Lemma 4.6 hard direction | #11 |
| GG25 line-decodability multi-gamma coverage | #12 |
| LogUp Protocol 2 completeness and soundness residuals | #13 |
| Batched FRI query-round soundness residuals | #14 |
| Duplex-sponge Fiat-Shamir statistical-distance placeholder | #15 |
| ToyProblem KoalaBear opaque code placeholder | #16 |
| SendWitness knowledge-soundness placeholder reductions | #17 |
| ToyProblem protocol and leaderboard residual anchors | #18 |
| RingSwitching and Binius completeness plumbing | #19 |
| WHIR MCA conjecture placeholders and envelope bounds | #20 |
| External list-decoding, Johnson, interleaving, and subspace-design APIs | #21 |
| CS25/BCHKS/BGKS bridges and deep-hole probability inputs | #22 |
| Historical proximity-prize docs and inventories | #23 |
| FRI/STIR soundness accounting and proximity-gap residuals | #24 |
| OracleReduction sequential composition and Fiat-Shamir run equality | #25 |
| Commitment/folding placeholder modules | #26 |
| L13 beta existence with `betaRec` witness | #27 |
| ToyProblem rewinding-extractor framework | #28 |
| RingSwitching KState weakening | #29 |
| KoalaBear numeric anchors | #30 |
| L6.12 ToyStep4/SoundnessBounds integration | #31 |
| Binius new-API Prelude and Basic call sites | #32 |
| Binius step residuals after Prelude port | #33 |
| Toolchain and Mathlib rebuild stabilization | #34 |
| Axiom audits pending toolchain rebuild | #35 |
| Final global verification report refresh | #36 |
| BKR06 final arithmetic side conditions | #38 |
| Grand MCA radius-one middle-band extremal count | #39 |
| Upstream PRs to Verified-zkEVM/ArkLib | #44 |
| ABF26 errata to Proximity Prize judges | #45 |
| ABF26 §4 CapacityBounds external CA/MCA theorem family | #48 |
| Johnson-family bounds: Joh62 Jqℓ + MDS Johnson corollary | #49 |
| GGR11 interleaved list-size recursion + erase-decode tree | #50 |
| Multiplicative rigidity: product-coset + in-band cluster bounds | #51 |
| MCAGS beyond-UDR GS-list mass bound | #52 |
| ABF26 §3 list-decoding theorem family | #54 |
| Grand challenges MCA-attainment counterpart / stale reference | #55 |
| Grand LD four-rate numeric Johnson/Elias certificates | #56 |
| Grand MCA faithful lattice-threshold brackets at four rates | #57 |
| Grand challenges singular/plural lattice encoding bridges | #58 |
| Proximity-prize audit doc refresh (this index family) | #59 |

Closed second-pass issues (#37, #40-#43, #46-#47, #53) are recorded in the refreshed
proximity-prize index; see "Related indexes" below.

## Interpretation

The current tree should be read as residualized, not silently complete. A focused issue is the
source of ownership for each residual family. If a proof route is mathematically false or external
to ArkLib's current formal scope, it should be documented as such rather than hidden behind `True`,
`opaque`, or a broad placeholder.

## Related indexes

* `docs/kb/audits/proximity-prize/CURRENT-RESIDUALIZED-TREE-2026-06-06.md`
* `ArkLib/Data/CodingTheory/ProximityGap/PermanentlyBlocked.lean`
* `ArkLib/Data/CodingTheory/ProximityGap/ExternalDebt.lean`

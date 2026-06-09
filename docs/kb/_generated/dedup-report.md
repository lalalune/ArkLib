# ArkLib dedup-candidate report

Generated from `docs/kb/_generated/declarations.json`. **Eyeball, do not auto-rewrite.** The point is to surface name collisions and doc-string overlap that *might* indicate an opportunity to consolidate.

## Stats

- `ArkLib` — 1481 files, 20494 declarations

## Same short-name across multiple files (645 groups)

Each group lists declarations sharing a short name across ≥2 files. Most are legitimate (overloaded interface, paper-shape vs general form), but the list is the right anchor to look for duplicates.

### `reduction` (13 declarations, 12 files)

- `def KZG.CommitmentScheme.reduction` [ArkLib\CommitmentScheme\KZG\FunctionBinding\Basic.lean:115](../../../ArkLib\CommitmentScheme\KZG\FunctionBinding\Basic.lean#L115) — The reduction breaking ARSDH using a successful function-binding adversary. The reduction follows th
- `def CheckClaim.reduction` [ArkLib\ProofSystem\Component\CheckClaim.lean:56](../../../ArkLib\ProofSystem\Component\CheckClaim.lean#L56) — The reduction for the `CheckClaim` reduction.
- `def DoNothing.reduction` [ArkLib\ProofSystem\Component\DoNothing.lean:44](../../../ArkLib\ProofSystem\Component\DoNothing.lean#L44) — The reduction for the `DoNothing` reduction. - Prover simply returns the statement and witness. - Ve
- `def NoInteraction.reduction` [ArkLib\ProofSystem\Component\NoInteraction.lean:62](../../../ArkLib\ProofSystem\Component\NoInteraction.lean#L62) — The no-interaction reduction can be specified by a tuple of functions: - `mapStmt : StmtIn → OracleC
- `def ReduceClaim.reduction` [ArkLib\ProofSystem\Component\ReduceClaim.lean:59](../../../ArkLib\ProofSystem\Component\ReduceClaim.lean#L59) — The reduction for the `ReduceClaim` reduction.
- `def SendWitness.reduction` [ArkLib\ProofSystem\Component\SendWitness.lean:78](../../../ArkLib\ProofSystem\Component\SendWitness.lean#L78) — (no docstring)
- `def Fri.Spec.reduction` [ArkLib\ProofSystem\Fri\Spec\General.lean:107](../../../ArkLib\ProofSystem\Fri\Spec\General.lean#L107) — (no docstring)
- `inductive reduction` [ArkLib\ProofSystem\Logup\Security\BridgeAndAppendResiduals.lean:36](../../../ArkLib\ProofSystem\Logup\Security\BridgeAndAppendResiduals.lean#L36) — (no docstring)
- `def Sumcheck.Spec.reduction` [ArkLib\ProofSystem\Sumcheck\Spec\General.lean:168](../../../ArkLib\ProofSystem\Sumcheck\Spec\General.lean#L168) — The sum-check protocol as a reduction
- `def Sumcheck.Spec.SingleRound.Simple.reduction` [ArkLib\ProofSystem\Sumcheck\Spec\SingleRound.lean:642](../../../ArkLib\ProofSystem\Sumcheck\Spec\SingleRound.lean#L642) — The reduction for the simple description of a single round of sum-check
- `def Sumcheck.Spec.SingleRound.reduction` [ArkLib\ProofSystem\Sumcheck\Spec\SingleRound.lean:1377](../../../ArkLib\ProofSystem\Sumcheck\Spec\SingleRound.lean#L1377) — The sum-check reduction for the `i`-th round of the sum-check protocol
- `def ToyProblem.Spec.reduction` [ArkLib\ProofSystem\ToyProblem\Spec\General.lean:499](../../../ArkLib\ProofSystem\ToyProblem\Spec\General.lean#L499) — Honest reduction for Construction 6.2: the package `{prover, verifier}` over the bundled-input `Redu
- `def ToyProblem.SimplifiedIOR.reduction` [ArkLib\ProofSystem\ToyProblem\Spec\SimplifiedIOR.lean:168](../../../ArkLib\ProofSystem\ToyProblem\Spec\SimplifiedIOR.lean#L168) — Honest reduction for Construction 6.9.

### `agree` (13 declarations, 11 files)

- `def CodeGeometry.agree` [ArkLib\Data\CodingTheory\CodeGeometry.lean:38](../../../ArkLib\Data\CodingTheory\CodeGeometry.lean#L38) — (no docstring)
- `def ArkLib.JohnsonBound.agree` [ArkLib\Data\CodingTheory\JohnsonBound\ListSize.lean:54](../../../ArkLib\Data\CodingTheory\JohnsonBound\ListSize.lean#L54) — The number of coordinates on which `c` and `w` agree.
- `def ProximityGap.WeightedAgreement.agree` [ArkLib\Data\CodingTheory\ProximityGap\Basic.lean:236](../../../ArkLib\Data\CodingTheory\ProximityGap\Basic.lean#L236) — Relative `μ`-agreement between words `u` and `v`.
- `def ConcretePin.agree` [ArkLib\Data\CodingTheory\ProximityGap\DeltaStarConcretePinF17.lean:85](../../../ArkLib\Data\CodingTheory\ProximityGap\DeltaStarConcretePinF17.lean#L85) — Agreement count of a line `(b, c)` with a word `w` over the domain `G`.
- `def R10ExactDelta.agree` [ArkLib\Data\CodingTheory\ProximityGap\DeltaStarExactCrossoverF17.lean:90](../../../ArkLib\Data\CodingTheory\ProximityGap\DeltaStarExactCrossoverF17.lean#L90) — Agreement of `w` with the line `(b,c)`: number of domain points `x ∈ G` (with paired word value `wx
- `def R11DeltaTable.Row1.agree` [ArkLib\Data\CodingTheory\ProximityGap\DeltaStarTableSmoothInstances.lean:122](../../../ArkLib\Data\CodingTheory\ProximityGap\DeltaStarTableSmoothInstances.lean#L122) — Agreement of `w₁` with the quadratic `(b,c,d)` on `G`.
- `def R11DeltaTable.Row2.agree` [ArkLib\Data\CodingTheory\ProximityGap\DeltaStarTableSmoothInstances.lean:182](../../../ArkLib\Data\CodingTheory\ProximityGap\DeltaStarTableSmoothInstances.lean#L182) — Agreement of `w₂` with the line `(b,c)` on `G`.
- `def R11DeltaTable.Row3.agree` [ArkLib\Data\CodingTheory\ProximityGap\DeltaStarTableSmoothInstances.lean:239](../../../ArkLib\Data\CodingTheory\ProximityGap\DeltaStarTableSmoothInstances.lean#L239) — Agreement of `w₃` with the line `(b,c)` on `G`.
- `def R14GS.agree` [ArkLib\Data\CodingTheory\ProximityGap\GSPipelineAssembly.lean:79](../../../ArkLib\Data\CodingTheory\ProximityGap\GSPipelineAssembly.lean#L79) — Number of evaluation points where `f` agrees with the received word `w`.
- `def ArkLib.CodingTheory.FourthMoment.agree` [ArkLib\Data\CodingTheory\ProximityGap\JohnsonFourthMomentNoGo.lean:84](../../../ArkLib\Data\CodingTheory\ProximityGap\JohnsonFourthMomentNoGo.lean#L84) — Number of coordinates on which `x` and `y` agree (same convention as `JohnsonSimplexBound`).
- `def ArkLib.CodingTheory.JohnsonSimplex.agree` [ArkLib\Data\CodingTheory\ProximityGap\JohnsonSimplexBound.lean:35](../../../ArkLib\Data\CodingTheory\ProximityGap\JohnsonSimplexBound.lean#L35) — Number of coordinates on which `x` and `y` agree.
- `def ArkLib.CodingTheory.ListThresholdWellDefined.agree` [ArkLib\Data\CodingTheory\ProximityGap\ListThresholdWellDefined.lean:41](../../../ArkLib\Data\CodingTheory\ProximityGap\ListThresholdWellDefined.lean#L41) — The agreement count of a codeword `c` with a received word `w`.
- `def ArkLib.ProximityGap.RSPrizeDataPoint.agree` [ArkLib\Data\CodingTheory\ProximityGap\RSListSizeDataPoint.lean:52](../../../ArkLib\Data\CodingTheory\ProximityGap\RSListSizeDataPoint.lean#L52) — Number of coordinates on which the received word `w` agrees with codeword `(a0, a1)`.

### `pSpec` (13 declarations, 11 files)

- `def RandomQuery.pSpec` [ArkLib\ProofSystem\Component\RandomQuery.lean:56](../../../ArkLib\ProofSystem\Component\RandomQuery.lean#L56) — (no docstring)
- `def SendClaim.pSpec` [ArkLib\ProofSystem\Component\SendClaim.lean:32](../../../ArkLib\ProofSystem\Component\SendClaim.lean#L32) — (no docstring)
- `def SendWitness.pSpec` [ArkLib\ProofSystem\Component\SendWitness.lean:54](../../../ArkLib\ProofSystem\Component\SendWitness.lean#L54) — (no docstring)
- `def Fri.Spec.FoldPhase.pSpec` [ArkLib\ProofSystem\Fri\Spec\SingleRound.lean:340](../../../ArkLib\ProofSystem\Fri\Spec\SingleRound.lean#L340) — Each round of the FRI protocol begins with the verifier sending a random field element as the challe
- `def Fri.Spec.FinalFoldPhase.pSpec` [ArkLib\ProofSystem\Fri\Spec\SingleRound.lean:645](../../../ArkLib\ProofSystem\Fri\Spec\SingleRound.lean#L645) — The final folding round of the FRI protocol begins with the verifier sending a random field element
- `def Fri.Spec.QueryRound.pSpec` [ArkLib\ProofSystem\Fri\Spec\SingleRound.lean:956](../../../ArkLib\ProofSystem\Fri\Spec\SingleRound.lean#L956) — (no docstring)
- `def Logup.pSpec` [ArkLib\ProofSystem\Logup\Protocol.lean:80](../../../ArkLib\ProofSystem\Logup\Protocol.lean#L80) — Protocol 2 transcript shape: the outer LogUp messages followed by ArkLib's generic sumcheck.
- `def StirIOP.Round.pSpec` [ArkLib\ProofSystem\Stir\RoundProtocol.lean:60](../../../ArkLib\ProofSystem\Stir\RoundProtocol.lean#L60) — The protocol spec of one STIR fold round: the verifier first sends a folding challenge in `F` (`V_to
- `def Sumcheck.Spec.pSpec` [ArkLib\ProofSystem\Sumcheck\Spec\General.lean:125](../../../ArkLib\ProofSystem\Sumcheck\Spec\General.lean#L125) — The protocol specification for the general sum-check protocol, which is the composition of the singl
- `def Sumcheck.Spec.SingleRound.pSpec` [ArkLib\ProofSystem\Sumcheck\Spec\SingleRound.lean:149](../../../ArkLib\ProofSystem\Sumcheck\Spec\SingleRound.lean#L149) — The protocol specification for a single round of sum-check. Has the form `⟨!v[.P_to_V, .V_to_P], !v[
- `def ToyProblem.Spec.pSpec` [ArkLib\ProofSystem\ToyProblem\Spec\General.lean:132](../../../ArkLib\ProofSystem\ToyProblem\Spec\General.lean#L132) — Protocol specification for Construction 6.2: three rounds, in the order V → P  (γ : F)            --
- `def ToyProblem.SimplifiedIOR.pSpec` [ArkLib\ProofSystem\ToyProblem\Spec\SimplifiedIOR.lean:108](../../../ArkLib\ProofSystem\ToyProblem\Spec\SimplifiedIOR.lean#L108) — Protocol specification for Construction 6.9: a single `V → P` round sending the combination randomne
- `def WhirIOP.FoldRound.pSpec` [ArkLib\ProofSystem\Whir\FoldRound.lean:149](../../../ArkLib\ProofSystem\Whir\FoldRound.lean#L149) — Protocol spec: the verifier sends a fold challenge `α : F`, then the prover sends the folded oracle

### `oracleVerifier` (11 declarations, 10 files)

- `def CheckClaim.oracleVerifier` [ArkLib\ProofSystem\Component\CheckClaim.lean:250](../../../ArkLib\ProofSystem\Component\CheckClaim.lean#L250) — The oracle verifier for the `CheckClaim` oracle reduction.
- `def DoNothing.oracleVerifier` [ArkLib\ProofSystem\Component\DoNothing.lean:106](../../../ArkLib\ProofSystem\Component\DoNothing.lean#L106) — The oracle verifier for the `DoNothing` oracle reduction.
- `def RandomQuery.oracleVerifier` [ArkLib\ProofSystem\Component\RandomQuery.lean:88](../../../ArkLib\ProofSystem\Component\RandomQuery.lean#L88) — The oracle verifier simply returns the challenge, and performs no checks.
- `def ReduceClaim.oracleVerifier` [ArkLib\ProofSystem\Component\ReduceClaim.lean:260](../../../ArkLib\ProofSystem\Component\ReduceClaim.lean#L260) — The oracle verifier for the `ReduceClaim` oracle reduction.
- `def SendClaim.oracleVerifier` [ArkLib\ProofSystem\Component\SendClaim.lean:67](../../../ArkLib\ProofSystem\Component\SendClaim.lean#L67) — The verifier checks that the relationship `rel oldStmt newStmt` holds. It has access to the original
- `def SendSingleWitness.oracleVerifier` [ArkLib\ProofSystem\Component\SendWitness.lean:353](../../../ArkLib\ProofSystem\Component\SendWitness.lean#L353) — The oracle verifier for the `SendSingleWitness` oracle reduction. The verifier receives the input st
- `def RingSwitching.BatchingPhase.oracleVerifier` [ArkLib\ProofSystem\RingSwitching\BatchingPhase.lean:196](../../../ArkLib\ProofSystem\RingSwitching\BatchingPhase.lean#L196) — (no docstring)
- `def Sumcheck.Spec.oracleVerifier` [ArkLib\ProofSystem\Sumcheck\Spec\General.lean:158](../../../ArkLib\ProofSystem\Sumcheck\Spec\General.lean#L158) — The oracle verifier for the (full) sum-check protocol
- `def Sumcheck.Spec.SingleRound.Simple.oracleVerifier` [ArkLib\ProofSystem\Sumcheck\Spec\SingleRound.lean:702](../../../ArkLib\ProofSystem\Sumcheck\Spec\SingleRound.lean#L702) — (no docstring)
- `def Sumcheck.Spec.SingleRound.oracleVerifier` [ArkLib\ProofSystem\Sumcheck\Spec\SingleRound.lean:1358](../../../ArkLib\ProofSystem\Sumcheck\Spec\SingleRound.lean#L1358) — The oracle verifier for the `i`-th round of the sum-check protocol. Migrated to the new `OracleState
- `def ToyProblem.Spec.oracleVerifier` [ArkLib\ProofSystem\ToyProblem\Spec\General.lean:576](../../../ArkLib\ProofSystem\ToyProblem\Spec\General.lean#L576) — Oracle verifier for Construction 6.2. Queries the prover's message `g` once and the two oracle codew

### `OracleStatement` (10 declarations, 10 files)

- `abbrev Interaction.OracleStatement` [ArkLib\Interaction\Oracle\Core.lean:100](../../../ArkLib\Interaction\Oracle\Core.lean#L100) — (no docstring)
- `def BatchedFri.Spec.OracleStatement` [ArkLib\ProofSystem\BatchedFri\Spec\SingleRound.lean:46](../../../ArkLib\ProofSystem\BatchedFri\Spec\SingleRound.lean#L46) — An oracle for each batched polynomial.
- `def Binius.BinaryBasefold.OracleStatement` [ArkLib\ProofSystem\Binius\BinaryBasefold\Basic.lean:746](../../../ArkLib\ProofSystem\Binius\BinaryBasefold\Basic.lean#L746) — For the `i`-th round of the protocol, there will be oracle statements corresponding to all committed
- `def R1CS.OracleStatement` [ArkLib\ProofSystem\ConstraintSystem\R1CS.lean:48](../../../ArkLib\ProofSystem\ConstraintSystem\R1CS.lean#L48) — (no docstring)
- `def Fri.Spec.OracleStatement` [ArkLib\ProofSystem\Fri\Spec\SingleRound.lean:89](../../../ArkLib\ProofSystem\Fri\Spec\SingleRound.lean#L89) — For the `i`-th round of the protocol, there will be `i + 1` oracle statements, one for the beginning
- `abbrev Spartan.Spec.OracleStatement` [ArkLib\ProofSystem\Spartan\Basic.lean:60](../../../ArkLib\ProofSystem\Spartan\Basic.lean#L60) — This unfolds to `A, B, C : Matrix (Fin 2 ^ ℓ_m) (Fin 2 ^ ℓ_n) R`
- `def StirIOP.OracleStatement` [ArkLib\ProofSystem\Stir\MainThm.lean:84](../../../ArkLib\ProofSystem\Stir\MainThm.lean#L84) — `OracleStatement` defines the oracle message type for a multi-indexed setting: given base input type
- `def Sumcheck.Spec.OracleStatement` [ArkLib\ProofSystem\Sumcheck\Spec\SingleRound.lean:136](../../../ArkLib\ProofSystem\Sumcheck\Spec\SingleRound.lean#L136) — Oracle statement for sum-check, which is a multivariate polynomial over `n` variables of individual
- `def ToyProblem.Spec.OracleStatement` [ArkLib\ProofSystem\ToyProblem\Spec\General.lean:99](../../../ArkLib\ProofSystem\ToyProblem\Spec\General.lean#L99) — Oracle statements of Construction 6.2: the two purported codewords `f₁, f₂ : ι → F`. The verifier on
- `def WhirIOP.OracleStatement` [ArkLib\ProofSystem\Whir\RBRSoundness.lean:146](../../../ArkLib\ProofSystem\Whir\RBRSoundness.lean#L146) — `OracleStatement` defines the oracle message type for a multi-indexed setting: given base input type

### `oracleReduction` (11 declarations, 9 files)

- `def CheckClaim.oracleReduction` [ArkLib\ProofSystem\Component\CheckClaim.lean:258](../../../ArkLib\ProofSystem\Component\CheckClaim.lean#L258) — The oracle reduction for the `CheckClaim` oracle reduction.
- `def DoNothing.oracleReduction` [ArkLib\ProofSystem\Component\DoNothing.lean:116](../../../ArkLib\ProofSystem\Component\DoNothing.lean#L116) — The oracle reduction for the `DoNothing` oracle reduction. - Prover simply returns the (non-oracle a
- `def RandomQuery.oracleReduction` [ArkLib\ProofSystem\Component\RandomQuery.lean:106](../../../ArkLib\ProofSystem\Component\RandomQuery.lean#L106) — Combine the trivial prover and this verifier to form the `RandomQuery` oracle reduction: the input o
- `def ReduceClaim.oracleReduction` [ArkLib\ProofSystem\Component\ReduceClaim.lean:277](../../../ArkLib\ProofSystem\Component\ReduceClaim.lean#L277) — The oracle reduction for the `ReduceClaim` oracle reduction.
- `def SendClaim.oracleReduction` [ArkLib\ProofSystem\Component\SendClaim.lean:96](../../../ArkLib\ProofSystem\Component\SendClaim.lean#L96) — Combine the prover and verifier into an oracle reduction. The input has no statement or witness, but
- `def SendSingleWitness.oracleReduction` [ArkLib\ProofSystem\Component\SendWitness.lean:366](../../../ArkLib\ProofSystem\Component\SendWitness.lean#L366) — (no docstring)
- `def Sumcheck.Spec.oracleReduction` [ArkLib\ProofSystem\Sumcheck\Spec\General.lean:180](../../../ArkLib\ProofSystem\Sumcheck\Spec\General.lean#L180) — The sum-check protocol as an oracle reduction
- `def Sumcheck.Spec.SingleRound.Simpler.oracleReduction` [ArkLib\ProofSystem\Sumcheck\Spec\SingleRound.lean:566](../../../ArkLib\ProofSystem\Sumcheck\Spec\SingleRound.lean#L566) — (no docstring)
- `def Sumcheck.Spec.SingleRound.Simple.oracleReduction` [ArkLib\ProofSystem\Sumcheck\Spec\SingleRound.lean:721](../../../ArkLib\ProofSystem\Sumcheck\Spec\SingleRound.lean#L721) — (no docstring)
- `def Sumcheck.Spec.SingleRound.oracleReduction` [ArkLib\ProofSystem\Sumcheck\Spec\SingleRound.lean:1387](../../../ArkLib\ProofSystem\Sumcheck\Spec\SingleRound.lean#L1387) — The sum-check oracle reduction for the `i`-th round of the sum-check protocol. Migrated to the new `
- `def ToyProblem.Spec.oracleReduction` [ArkLib\ProofSystem\ToyProblem\Spec\General.lean:608](../../../ArkLib\ProofSystem\ToyProblem\Spec\General.lean#L608) — Honest oracle reduction for Construction 6.2: the `OracleProver` / `OracleVerifier` pair packaged as

### `verifier` (11 declarations, 9 files)

- `def CheckClaim.verifier` [ArkLib\ProofSystem\Component\CheckClaim.lean:51](../../../ArkLib\ProofSystem\Component\CheckClaim.lean#L51) — The verifier for the `CheckClaim` reduction.
- `def DoNothing.verifier` [ArkLib\ProofSystem\Component\DoNothing.lean:35](../../../ArkLib\ProofSystem\Component\DoNothing.lean#L35) — The verifier for the `DoNothing` reduction.
- `def NoInteraction.verifier` [ArkLib\ProofSystem\Component\NoInteraction.lean:53](../../../ArkLib\ProofSystem\Component\NoInteraction.lean#L53) — The verifier in a no-interaction reduction takes an empty transcript, and hence reduce to a function
- `def ReduceClaim.verifier` [ArkLib\ProofSystem\Component\ReduceClaim.lean:55](../../../ArkLib\ProofSystem\Component\ReduceClaim.lean#L55) — The verifier for the `ReduceClaim` reduction.
- `def SendWitness.verifier` [ArkLib\ProofSystem\Component\SendWitness.lean:74](../../../ArkLib\ProofSystem\Component\SendWitness.lean#L74) — (no docstring)
- `def Sumcheck.Spec.verifier` [ArkLib\ProofSystem\Sumcheck\Spec\General.lean:149](../../../ArkLib\ProofSystem\Sumcheck\Spec\General.lean#L149) — The verifier for the (full) sum-check protocol
- `def Sumcheck.Spec.SingleRound.Simple.verifier` [ArkLib\ProofSystem\Sumcheck\Spec\SingleRound.lean:633](../../../ArkLib\ProofSystem\Sumcheck\Spec\SingleRound.lean#L633) — The verifier for the simple description of a single round of sum-check
- `def Sumcheck.Spec.SingleRound.verifier` [ArkLib\ProofSystem\Sumcheck\Spec\SingleRound.lean:1348](../../../ArkLib\ProofSystem\Sumcheck\Spec\SingleRound.lean#L1348) — The verifier for the `i`-th round of the sum-check protocol
- `def Sumcheck.Spec.SingleRound.Unfolded.verifier` [ArkLib\ProofSystem\Sumcheck\Spec\SingleRound.lean:1896](../../../ArkLib\ProofSystem\Sumcheck\Spec\SingleRound.lean#L1896) — The (non-oracle) verifier of the sum-check protocol for the `i`-th round, where `i < n + 1`
- `def ToyProblem.Spec.verifier` [ArkLib\ProofSystem\ToyProblem\Spec\General.lean:485](../../../ArkLib\ProofSystem\ToyProblem\Spec\General.lean#L485) — Honest verifier for Construction 6.2. Takes the bundled input `(stmt, oStmt) = ((v, μ₁, μ₂), (f₁, f₂
- `def ToyProblem.SimplifiedIOR.verifier` [ArkLib\ProofSystem\ToyProblem\Spec\SimplifiedIOR.lean:157](../../../ArkLib\ProofSystem\ToyProblem\Spec\SimplifiedIOR.lean#L157) — Honest verifier for Construction 6.9. Reads `γ` from the transcript and produces the new statement `

### `inputRelation` (11 declarations, 8 files)

- `def BatchedFri.Spec.inputRelation` [ArkLib\ProofSystem\BatchedFri\Spec\General.lean:67](../../../ArkLib\ProofSystem\BatchedFri\Spec\General.lean#L67) — (no docstring)
- `def BatchedFri.Spec.BatchingRound.inputRelation` [ArkLib\ProofSystem\BatchedFri\Spec\SingleRound.lean:69](../../../ArkLib\ProofSystem\BatchedFri\Spec\SingleRound.lean#L69) — (no docstring)
- `def Fri.Spec.inputRelation` [ArkLib\ProofSystem\Fri\Spec\General.lean:46](../../../ArkLib\ProofSystem\Fri\Spec\General.lean#L46) — (no docstring)
- `def Fri.Spec.FoldPhase.inputRelation` [ArkLib\ProofSystem\Fri\Spec\SingleRound.lean:275](../../../ArkLib\ProofSystem\Fri\Spec\SingleRound.lean#L275) — The FRI non-final folding round input relation, with proximity parameter `0 < δ`, for the `i`-th rou
- `def Fri.Spec.FinalFoldPhase.inputRelation` [ArkLib\ProofSystem\Fri\Spec\SingleRound.lean:584](../../../ArkLib\ProofSystem\Fri\Spec\SingleRound.lean#L584) — Input relation for the final folding round, with proximity parameter `0 < δ`. The round-`k` codeword
- `def Fri.Spec.QueryRound.inputRelation` [ArkLib\ProofSystem\Fri\Spec\SingleRound.lean:935](../../../ArkLib\ProofSystem\Fri\Spec\SingleRound.lean#L935) — (no docstring)
- `def Logup.inputRelation` [ArkLib\ProofSystem\Logup\Common.lean:264](../../../ArkLib\ProofSystem\Logup\Common.lean#L264) — Semantic input relation for Protocol 2: every lookup-column value occurs in the table range.
- `def Sumcheck.Spec.SingleRound.Simpler.inputRelation` [ArkLib\ProofSystem\Sumcheck\Spec\SingleRound.lean:338](../../../ArkLib\ProofSystem\Sumcheck\Spec\SingleRound.lean#L338) — (no docstring)
- `def Sumcheck.Spec.SingleRound.Simple.inputRelation` [ArkLib\ProofSystem\Sumcheck\Spec\SingleRound.lean:596](../../../ArkLib\ProofSystem\Sumcheck\Spec\SingleRound.lean#L596) — (no docstring)
- `def ToyProblem.Spec.inputRelation` [ArkLib\ProofSystem\ToyProblem\Spec\General.lean:187](../../../ArkLib\ProofSystem\ToyProblem\Spec\General.lean#L187) — The IOR-shaped input relation derived from `ToyProblem.relation` (Definition 6.1). `((v, μ₁, μ₂), (f
- `def WhirIOP.FoldRound.inputRelation` [ArkLib\ProofSystem\Whir\FoldRound.lean:210](../../../ArkLib\ProofSystem\Whir\FoldRound.lean#L210) — Input relation: the committed oracle is a codeword of the level-`j` smooth code of degree-budget `M

### `oracleProver` (9 declarations, 8 files)

- `def CheckClaim.oracleProver` [ArkLib\ProofSystem\Component\CheckClaim.lean:237](../../../ArkLib\ProofSystem\Component\CheckClaim.lean#L237) — The oracle prover for the `CheckClaim` oracle reduction.
- `def DoNothing.oracleProver` [ArkLib\ProofSystem\Component\DoNothing.lean:101](../../../ArkLib\ProofSystem\Component\DoNothing.lean#L101) — The oracle prover for the `DoNothing` oracle reduction.
- `def RandomQuery.oracleProver` [ArkLib\ProofSystem\Component\RandomQuery.lean:68](../../../ArkLib\ProofSystem\Component\RandomQuery.lean#L68) — The prover is trivial: it has no messages to send.  It only receives the verifier's challenge `q`, a
- `def ReduceClaim.oracleProver` [ArkLib\ProofSystem\Component\ReduceClaim.lean:250](../../../ArkLib\ProofSystem\Component\ReduceClaim.lean#L250) — The oracle prover for the `ReduceClaim` oracle reduction.
- `def SendClaim.oracleProver` [ArkLib\ProofSystem\Component\SendClaim.lean:40](../../../ArkLib\ProofSystem\Component\SendClaim.lean#L40) — The prover takes in the old oracle statement as input, and sends it as the protocol message.
- `def SendWitness.oracleProver` [ArkLib\ProofSystem\Component\SendWitness.lean:269](../../../ArkLib\ProofSystem\Component\SendWitness.lean#L269) — The oracle prover for the `SendWitness` oracle reduction. For each round `i : Fin (FinEnum.card ιw)`
- `def SendSingleWitness.oracleProver` [ArkLib\ProofSystem\Component\SendWitness.lean:337](../../../ArkLib\ProofSystem\Component\SendWitness.lean#L337) — The oracle prover for the `SendSingleWitness` oracle reduction. The prover sends the witness `wit` t
- `def RingSwitching.BatchingPhase.oracleProver` [ArkLib\ProofSystem\RingSwitching\BatchingPhase.lean:148](../../../ArkLib\ProofSystem\RingSwitching\BatchingPhase.lean#L148) — (no docstring)
- `def ToyProblem.Spec.oracleProver` [ArkLib\ProofSystem\ToyProblem\Spec\General.lean:528](../../../ArkLib\ProofSystem\ToyProblem\Spec\General.lean#L528) — Same as `prover` but exposed at the `OracleProver` signature. The underlying `Prover` is identical (

### `prover` (9 declarations, 8 files)

- `def CheckClaim.prover` [ArkLib\ProofSystem\Component\CheckClaim.lean:40](../../../ArkLib\ProofSystem\Component\CheckClaim.lean#L40) — The prover for the `CheckClaim` reduction.
- `def DoNothing.prover` [ArkLib\ProofSystem\Component\DoNothing.lean:31](../../../ArkLib\ProofSystem\Component\DoNothing.lean#L31) — The prover for the `DoNothing` reduction.
- `def NoInteraction.prover` [ArkLib\ProofSystem\Component\NoInteraction.lean:43](../../../ArkLib\ProofSystem\Component\NoInteraction.lean#L43) — The prover in a no-interaction reduction can be specified by a tuple of functions: - `mapStmt : Stmt
- `def ReduceClaim.prover` [ArkLib\ProofSystem\Component\ReduceClaim.lean:47](../../../ArkLib\ProofSystem\Component\ReduceClaim.lean#L47) — The prover for the `ReduceClaim` reduction.
- `def SendWitness.prover` [ArkLib\ProofSystem\Component\SendWitness.lean:64](../../../ArkLib\ProofSystem\Component\SendWitness.lean#L64) — (no docstring)
- `def Sumcheck.Spec.SingleRound.Simple.prover` [ArkLib\ProofSystem\Sumcheck\Spec\SingleRound.lean:611](../../../ArkLib\ProofSystem\Sumcheck\Spec\SingleRound.lean#L611) — The prover in the simple description of a single round of sum-check. Takes in input `target : R` and
- `def Sumcheck.Spec.SingleRound.Unfolded.prover` [ArkLib\ProofSystem\Sumcheck\Spec\SingleRound.lean:1886](../../../ArkLib\ProofSystem\Sumcheck\Spec\SingleRound.lean#L1886) — The overall prover for the `i`-th round of the sum-check protocol, where `i < n`. This is only well-
- `def ToyProblem.Spec.prover` [ArkLib\ProofSystem\ToyProblem\Spec\General.lean:441](../../../ArkLib\ProofSystem\ToyProblem\Spec\General.lean#L441) — Honest prover for Construction 6.2. After receiving the combination randomness `γ`, the prover sends
- `def ToyProblem.SimplifiedIOR.prover` [ArkLib\ProofSystem\ToyProblem\Spec\SimplifiedIOR.lean:126](../../../ArkLib\ProofSystem\ToyProblem\Spec\SimplifiedIOR.lean#L126) — Honest prover for Construction 6.9. After receiving `γ`, sets the new witness `M_new := M₀ + γ·M₁` a

### `relation` (9 declarations, 8 files)

- `def ArkLib.Lattices.ModuleSIS.relation` [ArkLib\Data\Lattices\ModuleSIS.lean:82](../../../ArkLib\Data\Lattices\ModuleSIS.lean#L82) — The kernel-form Module-SIS relation for a fixed matrix `A`: `z` is nonzero, short, and lies in the k
- `def ConstraintSystem.relation` [ArkLib\ProofSystem\ConstraintSystem\Basic.lean:68](../../../ArkLib\ProofSystem\ConstraintSystem\Basic.lean#L68) — The underlying set-theoretic relation at a given index.
- `def Lookup.relation` [ArkLib\ProofSystem\ConstraintSystem\Lookup.lean:25](../../../ArkLib\ProofSystem\ConstraintSystem\Lookup.lean#L25) — The lookup relation. Takes in a collection of values and a table, both containers for elements of ty
- `def MemoryChecking.ReadOnly.relation` [ArkLib\ProofSystem\ConstraintSystem\MemoryChecking.lean:128](../../../ArkLib\ProofSystem\ConstraintSystem\MemoryChecking.lean#L128) — The read-only memory checking relation. It takes a memory `mem` and a list of read operations `ops`.
- `def MemoryChecking.ReadWrite.relation` [ArkLib\ProofSystem\ConstraintSystem\MemoryChecking.lean:161](../../../ArkLib\ProofSystem\ConstraintSystem\MemoryChecking.lean#L161) — The read-write memory checking relation. It takes an initial memory `startMem`, a final memory `fina
- `def Plonk.relation` [ArkLib\ProofSystem\ConstraintSystem\Plonk.lean:193](../../../ArkLib\ProofSystem\ConstraintSystem\Plonk.lean#L193) — To define a relation based on the constraint system, we extend it with: - A natural number `ℓ ≤ m` r
- `def R1CS.relation` [ArkLib\ProofSystem\ConstraintSystem\R1CS.lean:61](../../../ArkLib\ProofSystem\ConstraintSystem\R1CS.lean#L61) — The R1CS relation: `(A *ᵥ 𝕫) * (B *ᵥ 𝕫) = (C *ᵥ 𝕫)`, where `*` is understood to mean component-wise
- `abbrev Spartan.Spec.relation` [ArkLib\ProofSystem\Spartan\Basic.lean:68](../../../ArkLib\ProofSystem\Spartan\Basic.lean#L68) — This unfolds to `(A *ᵥ 𝕫) * (B *ᵥ 𝕫) = (C *ᵥ 𝕫)`, where `𝕫 = 𝕩 ‖ 𝕨`
- `def ToyProblem.relation` [ArkLib\ProofSystem\ToyProblem\Definitions.lean:78](../../../ArkLib\ProofSystem\ToyProblem\Definitions.lean#L78) — **Definition 6.1 of [ABF26]** (toy problem relation `R_C^ℓ`). Given a base code `C ⊆ (ι → F)` (the p

### `outputRelation` (10 declarations, 7 files)

- `def BatchedFri.Spec.BatchingRound.outputRelation` [ArkLib\ProofSystem\BatchedFri\Spec\SingleRound.lean:85](../../../ArkLib\ProofSystem\BatchedFri\Spec\SingleRound.lean#L85) — (no docstring)
- `def Fri.Spec.outputRelation` [ArkLib\ProofSystem\Fri\Spec\General.lean:56](../../../ArkLib\ProofSystem\Fri\Spec\General.lean#L56) — (no docstring)
- `def Fri.Spec.FoldPhase.outputRelation` [ArkLib\ProofSystem\Fri\Spec\SingleRound.lean:303](../../../ArkLib\ProofSystem\Fri\Spec\SingleRound.lean#L303) — The FRI non-final folding round output relation, with proximity parameter `0 < δ`, for the `i`-th ro
- `def Fri.Spec.FinalFoldPhase.outputRelation` [ArkLib\ProofSystem\Fri\Spec\SingleRound.lean:613](../../../ArkLib\ProofSystem\Fri\Spec\SingleRound.lean#L613) — Output relation for the final folding round. After the final round the prover sends a polynomial in
- `def Fri.Spec.QueryRound.outputRelation` [ArkLib\ProofSystem\Fri\Spec\SingleRound.lean:943](../../../ArkLib\ProofSystem\Fri\Spec\SingleRound.lean#L943) — (no docstring)
- `def Logup.outputRelation` [ArkLib\ProofSystem\Logup\Common.lean:299](../../../ArkLib\ProofSystem\Logup\Common.lean#L299) — The full protocol has a trivial final relation: successful verification returns `Unit`.
- `def Sumcheck.Spec.SingleRound.Simpler.outputRelation` [ArkLib\ProofSystem\Sumcheck\Spec\SingleRound.lean:367](../../../ArkLib\ProofSystem\Sumcheck\Spec\SingleRound.lean#L367) — (no docstring)
- `def Sumcheck.Spec.SingleRound.Simple.outputRelation` [ArkLib\ProofSystem\Sumcheck\Spec\SingleRound.lean:599](../../../ArkLib\ProofSystem\Sumcheck\Spec\SingleRound.lean#L599) — (no docstring)
- `def ToyProblem.Spec.outputRelation` [ArkLib\ProofSystem\ToyProblem\Spec\General.lean:266](../../../ArkLib\ProofSystem\ToyProblem\Spec\General.lean#L266) — The IOR-shaped *relaxed* output relation derived from `ToyProblem.relaxedRelation` (Definition 6.3).
- `def WhirIOP.FoldRound.outputRelation` [ArkLib\ProofSystem\Whir\FoldRound.lean:216](../../../ArkLib\ProofSystem\Whir\FoldRound.lean#L216) — Output relation: the folded oracle is a codeword of the level-`(j+1)` smooth code of degree-budget `

### `Witness` (6 declarations, 6 files)

- `def BatchedFri.Spec.Witness` [ArkLib\ProofSystem\BatchedFri\Spec\SingleRound.lean:54](../../../ArkLib\ProofSystem\BatchedFri\Spec\SingleRound.lean#L54) — The Batched FRI protocol has as witness for each batched polynomial that is supposed to correspond t
- `structure Binius.BinaryBasefold.Witness` [ArkLib\ProofSystem\Binius\BinaryBasefold\Basic.lean:767](../../../ArkLib\ProofSystem\Binius\BinaryBasefold\Basic.lean#L767) — The round witness for round `i` of `t ∈ L[≤ 2][X Fin ℓ]` and `Hᵢ(Xᵢ, ..., Xₗ₋₁) := h(r₀', ..., rᵢ₋₁'
- `def R1CS.Witness` [ArkLib\ProofSystem\ConstraintSystem\R1CS.lean:51](../../../ArkLib\ProofSystem\ConstraintSystem\R1CS.lean#L51) — (no docstring)
- `def Fri.Spec.Witness` [ArkLib\ProofSystem\Fri\Spec\SingleRound.lean:110](../../../ArkLib\ProofSystem\Fri\Spec\SingleRound.lean#L110) — The FRI protocol has as witness the polynomial that is supposed to correspond to the codeword in the
- `abbrev Spartan.Spec.Witness` [ArkLib\ProofSystem\Spartan\Basic.lean:64](../../../ArkLib\ProofSystem\Spartan\Basic.lean#L64) — This unfolds to `𝕨 : Fin 2 ^ ℓ_w → R`
- `def ToyProblem.Spec.Witness` [ArkLib\ProofSystem\ToyProblem\Spec\General.lean:107](../../../ArkLib\ProofSystem\ToyProblem\Spec\General.lean#L107) — Honest witness: the underlying messages `M₁, M₂ : Fin k → F` whose encodings are the oracle codeword

### `Statement` (5 declarations, 5 files)

- `def R1CS.Statement` [ArkLib\ProofSystem\ConstraintSystem\R1CS.lean:45](../../../ArkLib\ProofSystem\ConstraintSystem\R1CS.lean#L45) — (no docstring)
- `def Fri.Spec.Statement` [ArkLib\ProofSystem\Fri\Spec\SingleRound.lean:80](../../../ArkLib\ProofSystem\Fri\Spec\SingleRound.lean#L80) — For the `i`-th round of the protocol, the input statement is equal to the challenges sent from round
- `abbrev Spartan.Spec.Statement` [ArkLib\ProofSystem\Spartan\Basic.lean:56](../../../ArkLib\ProofSystem\Spartan\Basic.lean#L56) — This unfolds to `𝕩 : Fin (2 ^ ℓ_n - 2 ^ ℓ_w) → R`
- `structure Sumcheck.Structured.Statement` [ArkLib\ProofSystem\Sumcheck\Structured.lean:197](../../../ArkLib\ProofSystem\Sumcheck\Structured.lean#L197) — Statement per iterated sumcheck round
- `def ToyProblem.Spec.Statement` [ArkLib\ProofSystem\ToyProblem\Spec\General.lean:93](../../../ArkLib\ProofSystem\ToyProblem\Spec\General.lean#L93) — Input (explicit) statement of Construction 6.2: the linear-constraint vector `v ∈ F^k` and the two c

### `oracleReduction_perfectCompleteness` (6 declarations, 5 files)

- `theorem DoNothing.oracleReduction_perfectCompleteness` [ArkLib\ProofSystem\Component\DoNothing.lean:126](../../../ArkLib\ProofSystem\Component\DoNothing.lean#L126) — The `DoNothing` oracle reduction satisfies perfect completeness for any relation.
- `theorem Sumcheck.Spec.oracleReduction_perfectCompleteness` [ArkLib\ProofSystem\Sumcheck\Spec\OracleCompleteness.lean:65](../../../ArkLib\ProofSystem\Sumcheck\Spec\OracleCompleteness.lean#L65) — **Full multi-round sum-check perfect completeness (oracle level), modulo the verifier bridge.** `Ora
- `theorem Sumcheck.Spec.SingleRound.oracleReduction_perfectCompleteness` [ArkLib\ProofSystem\Sumcheck\Spec\OracleCompletenessThreaded.lean:80](../../../ArkLib\ProofSystem\Sumcheck\Spec\OracleCompletenessThreaded.lean#L80) — **Per-round oracle perfect completeness.** The `i`-th-round oracle reduction `SingleRound.oracleRedu
- `theorem Sumcheck.Spec.oracleReduction_perfectCompleteness` [ArkLib\ProofSystem\Sumcheck\Spec\OracleCompletenessThreaded.lean:117](../../../ArkLib\ProofSystem\Sumcheck\Spec\OracleCompletenessThreaded.lean#L117) — **Full multi-round sum-check perfect completeness (oracle level) — without the false bridge.** Assem
- `theorem Sumcheck.Spec.SingleRound.Simple.oracleReduction_perfectCompleteness` [ArkLib\ProofSystem\Sumcheck\Spec\SingleRound.lean:1033](../../../ArkLib\ProofSystem\Sumcheck\Spec\SingleRound.lean#L1033) — Perfect completeness for the oracle reduction
- `theorem ToyProblem.Spec.oracleReduction_perfectCompleteness` [ArkLib\ProofSystem\ToyProblem\Spec\General.lean:945](../../../ArkLib\ProofSystem\ToyProblem\Spec\General.lean#L945) — **Honest completeness for Construction 6.2** (protocol-level form). The honest oracle reduction is p

### `OStmtIn` (5 declarations, 4 files)

- `def RandomQuery.OStmtIn` [ArkLib\ProofSystem\Component\RandomQuery.lean:36](../../../ArkLib\ProofSystem\Component\RandomQuery.lean#L36) — (no docstring)
- `def Logup.OStmtIn` [ArkLib\ProofSystem\Logup\Common.lean:241](../../../ArkLib\ProofSystem\Logup\Common.lean#L241) — Input oracle statements: the table `t` and lookup columns `fᵢ`, as multilinear oracles.
- `def Sumcheck.Spec.SingleRound.Simpler.OStmtIn` [ArkLib\ProofSystem\Sumcheck\Spec\SingleRound.lean:336](../../../ArkLib\ProofSystem\Sumcheck\Spec\SingleRound.lean#L336) — (no docstring)
- `def Sumcheck.Spec.SingleRound.Simple.OStmtIn` [ArkLib\ProofSystem\Sumcheck\Spec\SingleRound.lean:591](../../../ArkLib\ProofSystem\Sumcheck\Spec\SingleRound.lean#L591) — (no docstring)
- `def WhirIOP.FoldRound.OStmtIn` [ArkLib\ProofSystem\Whir\FoldRound.lean:135](../../../ArkLib\ProofSystem\Whir\FoldRound.lean#L135) — The oracle message type for this round: the single committed codeword as a function on the relevant

### `OStmtOut` (5 declarations, 4 files)

- `def RandomQuery.OStmtOut` [ArkLib\ProofSystem\Component\RandomQuery.lean:37](../../../ArkLib\ProofSystem\Component\RandomQuery.lean#L37) — (no docstring)
- `def Logup.OStmtOut` [ArkLib\ProofSystem\Logup\Common.lean:290](../../../ArkLib\ProofSystem\Logup\Common.lean#L290) — Output oracle statements for the full LogUp protocol.
- `def Sumcheck.Spec.SingleRound.Simpler.OStmtOut` [ArkLib\ProofSystem\Sumcheck\Spec\SingleRound.lean:365](../../../ArkLib\ProofSystem\Sumcheck\Spec\SingleRound.lean#L365) — (no docstring)
- `def Sumcheck.Spec.SingleRound.Simple.OStmtOut` [ArkLib\ProofSystem\Sumcheck\Spec\SingleRound.lean:594](../../../ArkLib\ProofSystem\Sumcheck\Spec\SingleRound.lean#L594) — (no docstring)
- `def WhirIOP.FoldRound.OStmtOut` [ArkLib\ProofSystem\Whir\FoldRound.lean:138](../../../ArkLib\ProofSystem\Whir\FoldRound.lean#L138) — (no docstring)

### `StmtIn` (5 declarations, 4 files)

- `def RandomQuery.StmtIn` [ArkLib\ProofSystem\Component\RandomQuery.lean:33](../../../ArkLib\ProofSystem\Component\RandomQuery.lean#L33) — (no docstring)
- `structure Logup.StmtIn` [ArkLib\ProofSystem\Logup\Common.lean:233](../../../ArkLib\ProofSystem\Logup\Common.lean#L233) — Public parameter assumptions for Protocol 2. The paper fixes a finite field with characteristic larg
- `def Sumcheck.Spec.StmtIn` [ArkLib\ProofSystem\Sumcheck\Spec\General.lean:137](../../../ArkLib\ProofSystem\Sumcheck\Spec\General.lean#L137) — The input statement for the (full) sum-check protocol, which contains only the target sum value
- `def Sumcheck.Spec.SingleRound.Simpler.StmtIn` [ArkLib\ProofSystem\Sumcheck\Spec\SingleRound.lean:335](../../../ArkLib\ProofSystem\Sumcheck\Spec\SingleRound.lean#L335) — (no docstring)
- `def Sumcheck.Spec.SingleRound.Simple.StmtIn` [ArkLib\ProofSystem\Sumcheck\Spec\SingleRound.lean:585](../../../ArkLib\ProofSystem\Sumcheck\Spec\SingleRound.lean#L585) — (no docstring)

### `reduction_perfectCompleteness` (5 declarations, 4 files)

- `theorem DoNothing.reduction_perfectCompleteness` [ArkLib\ProofSystem\Component\DoNothing.lean:52](../../../ArkLib\ProofSystem\Component\DoNothing.lean#L52) — The `DoNothing` reduction satisfies perfect completeness for any relation.
- `theorem Fri.Spec.Completeness.reduction_perfectCompleteness` [ArkLib\ProofSystem\Fri\Spec\Completeness.lean:111](../../../ArkLib\ProofSystem\Fri\Spec\Completeness.lean#L111) — **Brick D — composed FRI reduction perfect completeness.** The honest FRI protocol is perfectly comp
- `theorem Sumcheck.Spec.reduction_perfectCompleteness` [ArkLib\ProofSystem\Sumcheck\Spec\Completeness.lean:87](../../../ArkLib\ProofSystem\Sumcheck\Spec\Completeness.lean#L87) — **Full multi-round sum-check perfect completeness (`Reduction` level).** Assembled from the per-roun
- `theorem Sumcheck.Spec.SingleRound.Simple.reduction_perfectCompleteness` [ArkLib\ProofSystem\Sumcheck\Spec\SingleRound.lean:742](../../../ArkLib\ProofSystem\Sumcheck\Spec\SingleRound.lean#L742) — Perfect completeness for the (non-oracle) reduction
- `theorem Sumcheck.Spec.SingleRound.reduction_perfectCompleteness` [ArkLib\ProofSystem\Sumcheck\Spec\SingleRound.lean:1785](../../../ArkLib\ProofSystem\Sumcheck\Spec\SingleRound.lean#L1785) — (no docstring)

### `agreeCount` (4 declarations, 4 files)

- `def ArkLib.CodingTheory.Round4InteriorList.agreeCount` [ArkLib\Data\CodingTheory\ProximityGap\InteriorListCountBridge.lean:199](../../../ArkLib\Data\CodingTheory\ProximityGap\InteriorListCountBridge.lean#L199) — The agreement count (number of coordinates where two words coincide).
- `def ArkLib.CodingTheory.CapacityLowerSharpen.agreeCount` [ArkLib\Data\CodingTheory\ProximityGap\ListCapacityFieldIndependent.lean:185](../../../ArkLib\Data\CodingTheory\ProximityGap\ListCapacityFieldIndependent.lean#L185) — The agreement count (number of coordinates where two words coincide).
- `def R15MCAGap.agreeCount` [ArkLib\Data\CodingTheory\ProximityGap\MCABadScalarSpreadBridge.lean:59](../../../ArkLib\Data\CodingTheory\ProximityGap\MCABadScalarSpreadBridge.lean#L59) — Number of coordinates on which the word `w` agrees with the word `c`.
- `def RSDeltaStar.agreeCount` [ArkLib\Data\CodingTheory\ProximityGap\RSAveragingDeltaStarUpper.lean:145](../../../ArkLib\Data\CodingTheory\ProximityGap\RSAveragingDeltaStarUpper.lean#L145) — Number of evaluation points where the codeword `tupleToPoly c` agrees with the word `w`.

### `agreeSet` (4 declarations, 4 files)

- `def ConcretePin.agreeSet` [ArkLib\Data\CodingTheory\ProximityGap\DeltaStarConcretePinF17.lean:169](../../../ArkLib\Data\CodingTheory\ProximityGap\DeltaStarConcretePinF17.lean#L169) — The agreement set of a line `(b, c)` with `w` inside `G`.
- `def LinePairCooccurrence.agreeSet` [ArkLib\Data\CodingTheory\ProximityGap\LinePairCooccurrenceBound.lean:57](../../../ArkLib\Data\CodingTheory\ProximityGap\LinePairCooccurrenceBound.lean#L57) — Coordinates where `u` and `v` agree.
- `def R15Bracket.agreeSet` [ArkLib\Data\CodingTheory\ProximityGap\PrizeScaleBracketFull.lean:180](../../../ArkLib\Data\CodingTheory\ProximityGap\PrizeScaleBracketFull.lean#L180) — The agreement set of two words.
- `def ProximityPrizeCA.agreeSet` [ArkLib\Data\CodingTheory\ProximityPrizeCA.lean:35](../../../ArkLib\Data\CodingTheory\ProximityPrizeCA.lean#L35) — The agreement set of two words.

### `disagreementSet` (4 declarations, 4 files)

- `def disagreementSet` [ArkLib\Data\CodingTheory\ProximityGap\DG25\MainResults.lean:63](../../../ArkLib\Data\CodingTheory\ProximityGap\DG25\MainResults.lean#L63) — The set D = Δ^{2m}(U, V), columns where U₀≠V₀ or U₁≠V₁. Specialisation of the canonical `Code.disagr
- `def Binius.BinaryBasefold.disagreementSet` [ArkLib\ProofSystem\Binius\BinaryBasefold\Code.lean:136](../../../ArkLib\ProofSystem\Binius\BinaryBasefold\Code.lean#L136) — Disagreement set Δ : The set of points where two functions disagree. For functions f^(i) and g^(i),
- `def Quotienting.disagreementSet` [ArkLib\ProofSystem\Stir\Quotienting.lean:121](../../../ArkLib\ProofSystem\Stir\Quotienting.lean#L121) — We define the set disagreementSet(f,ι,S,Ans) as the set of all points x ∈ ι that lie in S such that
- `def BlockRelDistance.disagreementSet` [ArkLib\ProofSystem\Whir\BlockRelDistance.lean:104](../../../ArkLib\ProofSystem\Whir\BlockRelDistance.lean#L104) — Let C be a smooth ReedSolomon code `C = RS[F, ι^(2ⁱ), φ', m]` and `f,g : ι^(2ⁱ) → F`, then the (i,k)

### `honestTranscriptDist_oracleReduction_evalDist` (4 declarations, 4 files)

- `theorem RandomQuery.honestTranscriptDist_oracleReduction_evalDist` [ArkLib\ProofSystem\Component\RandomQuery.lean:212](../../../ArkLib\ProofSystem\Component\RandomQuery.lean#L212) — The honest transcript distribution for `RandomQuery` is definitionally the simulator distribution.
- `theorem ReduceClaim.honestTranscriptDist_oracleReduction_evalDist` [ArkLib\ProofSystem\Component\ReduceClaim.lean:372](../../../ArkLib\ProofSystem\Component\ReduceClaim.lean#L372) — The honest transcript distribution for the plain `ReduceClaim` oracle reduction is the deterministic
- `theorem SendClaim.honestTranscriptDist_oracleReduction_evalDist` [ArkLib\ProofSystem\Component\SendClaim.lean:254](../../../ArkLib\ProofSystem\Component\SendClaim.lean#L254) — The honest transcript distribution for `SendClaim` is exactly the simulator distribution, because th
- `theorem SendSingleWitness.honestTranscriptDist_oracleReduction_evalDist` [ArkLib\ProofSystem\Component\SendWitness.lean:438](../../../ArkLib\ProofSystem\Component\SendWitness.lean#L438) — The honest transcript distribution for `SendSingleWitness` is the deterministic one-message transcri

### `instOracleVerifierAppendCoherent` (4 declarations, 4 files)

- `instance RandomQuery.instOracleVerifierAppendCoherent` [ArkLib\ProofSystem\Component\RandomQuery.lean:112](../../../ArkLib\ProofSystem\Component\RandomQuery.lean#L112) — (no docstring)
- `instance SendSingleWitness.instOracleVerifierAppendCoherent` [ArkLib\ProofSystem\Component\SendWitness.lean:372](../../../ArkLib\ProofSystem\Component\SendWitness.lean#L372) — (no docstring)
- `instance RingSwitching.BatchingPhase.instOracleVerifierAppendCoherent` [ArkLib\ProofSystem\RingSwitching\BatchingPhase.lean:239](../../../ArkLib\ProofSystem\RingSwitching\BatchingPhase.lean#L239) — The batching-phase oracle verifier passes every output oracle through to the unchanged input oracle
- `instance Sumcheck.Spec.SingleRound.instOracleVerifierAppendCoherent` [ArkLib\ProofSystem\Sumcheck\Spec\SingleRound.lean:1365](../../../ArkLib\ProofSystem\Sumcheck\Spec\SingleRound.lean#L1365) — The `i`-th-round oracle verifier routes its (single) output oracle to the (unchanged) input oracle (

### `oracleReduction_isHVZK` (4 declarations, 4 files)

- `theorem DoNothing.oracleReduction_isHVZK` [ArkLib\ProofSystem\Component\DoNothing.lean:194](../../../ArkLib\ProofSystem\Component\DoNothing.lean#L194) — The `DoNothing` oracle reduction has an explicit perfect-HVZK simulator for any oracle-input relatio
- `theorem RandomQuery.oracleReduction_isHVZK` [ArkLib\ProofSystem\Component\RandomQuery.lean:240](../../../ArkLib\ProofSystem\Component\RandomQuery.lean#L240) — `RandomQuery` has an explicit perfect-HVZK simulator as an oracle reduction.
- `theorem ReduceClaim.oracleReduction_isHVZK` [ArkLib\ProofSystem\Component\ReduceClaim.lean:423](../../../ArkLib\ProofSystem\Component\ReduceClaim.lean#L423) — The plain `ReduceClaim` oracle reduction has an explicit perfect-HVZK simulator for any input relati
- `theorem SendClaim.oracleReduction_isHVZK` [ArkLib\ProofSystem\Component\SendClaim.lean:285](../../../ArkLib\ProofSystem\Component\SendClaim.lean#L285) — `SendClaim` has an explicit perfect-HVZK simulator as an oracle reduction.

### `oracleReduction_isStatHVZK` (4 declarations, 4 files)

- `theorem DoNothing.oracleReduction_isStatHVZK` [ArkLib\ProofSystem\Component\DoNothing.lean:202](../../../ArkLib\ProofSystem\Component\DoNothing.lean#L202) — The `DoNothing` oracle reduction has statistical HVZK for any oracle-input relation and error budget
- `theorem RandomQuery.oracleReduction_isStatHVZK` [ArkLib\ProofSystem\Component\RandomQuery.lean:248](../../../ArkLib\ProofSystem\Component\RandomQuery.lean#L248) — `RandomQuery` has statistical HVZK at every error budget as an oracle reduction.
- `theorem ReduceClaim.oracleReduction_isStatHVZK` [ArkLib\ProofSystem\Component\ReduceClaim.lean:434](../../../ArkLib\ProofSystem\Component\ReduceClaim.lean#L434) — The plain `ReduceClaim` oracle reduction has statistical HVZK for any input relation and error budge
- `theorem SendClaim.oracleReduction_isStatHVZK` [ArkLib\ProofSystem\Component\SendClaim.lean:295](../../../ArkLib\ProofSystem\Component\SendClaim.lean#L295) — `SendClaim` has statistical HVZK at every error budget as an oracle reduction.

### `oracleReduction_perfectHVZK` (4 declarations, 4 files)

- `theorem DoNothing.oracleReduction_perfectHVZK` [ArkLib\ProofSystem\Component\DoNothing.lean:176](../../../ArkLib\ProofSystem\Component\DoNothing.lean#L176) — The `DoNothing` oracle reduction is perfectly HVZK for any oracle-input relation.
- `theorem RandomQuery.oracleReduction_perfectHVZK` [ArkLib\ProofSystem\Component\RandomQuery.lean:221](../../../ArkLib\ProofSystem\Component\RandomQuery.lean#L221) — `RandomQuery` is perfectly HVZK as an oracle reduction: it has no private witness, and the single ve
- `theorem ReduceClaim.oracleReduction_perfectHVZK` [ArkLib\ProofSystem\Component\ReduceClaim.lean:400](../../../ArkLib\ProofSystem\Component\ReduceClaim.lean#L400) — The plain `ReduceClaim` oracle reduction is perfectly HVZK for any input relation: it has no message
- `theorem SendClaim.oracleReduction_perfectHVZK` [ArkLib\ProofSystem\Component\SendClaim.lean:264](../../../ArkLib\ProofSystem\Component\SendClaim.lean#L264) — `SendClaim` is perfectly HVZK as an oracle reduction for any input relation: the protocol has no pri

### `oracleReduction_statisticalHVZK` (4 declarations, 4 files)

- `theorem DoNothing.oracleReduction_statisticalHVZK` [ArkLib\ProofSystem\Component\DoNothing.lean:185](../../../ArkLib\ProofSystem\Component\DoNothing.lean#L185) — The `DoNothing` oracle reduction is statistically HVZK for any oracle-input relation and error budge
- `theorem RandomQuery.oracleReduction_statisticalHVZK` [ArkLib\ProofSystem\Component\RandomQuery.lean:231](../../../ArkLib\ProofSystem\Component\RandomQuery.lean#L231) — Perfect HVZK implies statistical HVZK for `RandomQuery` at every error budget.
- `theorem ReduceClaim.oracleReduction_statisticalHVZK` [ArkLib\ProofSystem\Component\ReduceClaim.lean:412](../../../ArkLib\ProofSystem\Component\ReduceClaim.lean#L412) — Perfect HVZK implies statistical HVZK for the plain `ReduceClaim` oracle reduction at every error bu
- `theorem SendClaim.oracleReduction_statisticalHVZK` [ArkLib\ProofSystem\Component\SendClaim.lean:275](../../../ArkLib\ProofSystem\Component\SendClaim.lean#L275) — Perfect HVZK implies statistical HVZK for `SendClaim` at every error budget.

### `oracleVerifier_rbrKnowledgeSoundness` (4 declarations, 4 files)

- `theorem DoNothing.oracleVerifier_rbrKnowledgeSoundness` [ArkLib\ProofSystem\Component\DoNothing.lean:132](../../../ArkLib\ProofSystem\Component\DoNothing.lean#L132) — The `DoNothing` oracle verifier is perfectly round-by-round knowledge sound.
- `theorem RandomQuery.oracleVerifier_rbrKnowledgeSoundness` [ArkLib\ProofSystem\Component\RandomQuery.lean:351](../../../ArkLib\ProofSystem\Component\RandomQuery.lean#L351) — The `RandomQuery` oracle reduction is round-by-round knowledge sound. The key fact governing the sou
- `theorem ReduceClaim.oracleVerifier_rbrKnowledgeSoundness` [ArkLib\ProofSystem\Component\ReduceClaim.lean:489](../../../ArkLib\ProofSystem\Component\ReduceClaim.lean#L489) — The `ReduceClaim` oracle reduction satisfies perfect round-by-round knowledge soundness. Note that s
- `theorem Sumcheck.Spec.SingleRound.Simple.oracleVerifier_rbrKnowledgeSoundness` [ArkLib\ProofSystem\Sumcheck\Spec\SingleRound.lean:1220](../../../ArkLib\ProofSystem\Sumcheck\Spec\SingleRound.lean#L1220) — Round-by-round knowledge soundness for the oracle verifier

### `reduction_completeness` (4 declarations, 4 files)

- `theorem CheckClaim.reduction_completeness` [ArkLib\ProofSystem\Component\CheckClaim.lean:71](../../../ArkLib\ProofSystem\Component\CheckClaim.lean#L71) — The `CheckClaim` reduction satisfies perfect completeness with respect to the predicate as the input
- `theorem NoInteraction.reduction_completeness` [ArkLib\ProofSystem\Component\NoInteraction.lean:93](../../../ArkLib\ProofSystem\Component\NoInteraction.lean#L93) — Completeness of a no-interaction reduction. **Faithfulness of the hypothesis `hRel`.** `Reduction.ru
- `theorem ReduceClaim.reduction_completeness` [ArkLib\ProofSystem\Component\ReduceClaim.lean:69](../../../ArkLib\ProofSystem\Component\ReduceClaim.lean#L69) — The `ReduceClaim` reduction satisfies perfect completeness for any relation.
- `theorem SendWitness.reduction_completeness` [ArkLib\ProofSystem\Component\SendWitness.lean:174](../../../ArkLib\ProofSystem\Component\SendWitness.lean#L174) — The `SendWitness` reduction satisfies perfect completeness.

### `coeffPoly` (4 declarations, 4 files)

- `def GSHasse.coeffPoly` [ArkLib\Data\CodingTheory\ProximityGap\GSHasseMultiplicity.lean:135](../../../ArkLib\Data\CodingTheory\ProximityGap\GSHasseMultiplicity.lean#L135) — The bivariate polynomial (element of `F[X][Y]`, outer variable `Y`) with coefficient `c' (i, j)` on
- `def GSInterp.coeffPoly` [ArkLib\Data\CodingTheory\ProximityGap\GSInterpolationExistence.lean:98](../../../ArkLib\Data\CodingTheory\ProximityGap\GSInterpolationExistence.lean#L98) — The bivariate polynomial (element of `F[X][Y]`, outer variable `Y`) with coefficient `c' (i, j)` on
- `def R15.coeffPoly` [ArkLib\Data\CodingTheory\ProximityGap\SudanListBound.lean:105](../../../ArkLib\Data\CodingTheory\ProximityGap\SudanListBound.lean#L105) — The bivariate polynomial (element of `F[X][Y]`, outer variable `Y`) with coefficient `c' (i, j)` on
- `def R15.coeffPoly` [ArkLib\Data\CodingTheory\ProximityGap\SudanListBoundFull.lean:105](../../../ArkLib\Data\CodingTheory\ProximityGap\SudanListBoundFull.lean#L105) — The bivariate polynomial (element of `F[X][Y]`, outer variable `Y`) with coefficient `c' (i, j)` on

### `coeffPoly_coeff` (4 declarations, 4 files)

- `lemma GSHasse.coeffPoly_coeff` [ArkLib\Data\CodingTheory\ProximityGap\GSHasseMultiplicity.lean:139](../../../ArkLib\Data\CodingTheory\ProximityGap\GSHasseMultiplicity.lean#L139) — (no docstring)
- `lemma GSInterp.coeffPoly_coeff` [ArkLib\Data\CodingTheory\ProximityGap\GSInterpolationExistence.lean:102](../../../ArkLib\Data\CodingTheory\ProximityGap\GSInterpolationExistence.lean#L102) — (no docstring)
- `lemma R15.coeffPoly_coeff` [ArkLib\Data\CodingTheory\ProximityGap\SudanListBound.lean:109](../../../ArkLib\Data\CodingTheory\ProximityGap\SudanListBound.lean#L109) — (no docstring)
- `lemma R15.coeffPoly_coeff` [ArkLib\Data\CodingTheory\ProximityGap\SudanListBoundFull.lean:109](../../../ArkLib\Data\CodingTheory\ProximityGap\SudanListBoundFull.lean#L109) — (no docstring)

### `exists_ne_zero_map_eq_zero_of_finrank_lt` (4 declarations, 4 files)

- `theorem GSHasse.exists_ne_zero_map_eq_zero_of_finrank_lt` [ArkLib\Data\CodingTheory\ProximityGap\GSHasseMultiplicity.lean:51](../../../ArkLib\Data\CodingTheory\ProximityGap\GSHasseMultiplicity.lean#L51) — (no docstring)
- `theorem GSInterp.exists_ne_zero_map_eq_zero_of_finrank_lt` [ArkLib\Data\CodingTheory\ProximityGap\GSInterpolationExistence.lean:37](../../../ArkLib\Data\CodingTheory\ProximityGap\GSInterpolationExistence.lean#L37) — (no docstring)
- `theorem R15.exists_ne_zero_map_eq_zero_of_finrank_lt` [ArkLib\Data\CodingTheory\ProximityGap\SudanListBound.lean:51](../../../ArkLib\Data\CodingTheory\ProximityGap\SudanListBound.lean#L51) — (no docstring)
- `theorem R15.exists_ne_zero_map_eq_zero_of_finrank_lt` [ArkLib\Data\CodingTheory\ProximityGap\SudanListBoundFull.lean:51](../../../ArkLib\Data\CodingTheory\ProximityGap\SudanListBoundFull.lean#L51) — (no docstring)

### `gsSupport` (4 declarations, 4 files)

- `def GSHasse.gsSupport` [ArkLib\Data\CodingTheory\ProximityGap\GSHasseMultiplicity.lean:69](../../../ArkLib\Data\CodingTheory\ProximityGap\GSHasseMultiplicity.lean#L69) — Monomial support of the GS interpolation space: pairs `(i, j)` with `i + (k-1)·j < D`, organized as
- `def GSInterp.gsSupport` [ArkLib\Data\CodingTheory\ProximityGap\GSInterpolationExistence.lean:55](../../../ArkLib\Data\CodingTheory\ProximityGap\GSInterpolationExistence.lean#L55) — Monomial support of the GS interpolation space: pairs `(i, j)` with `i + (k-1)·j < D`, organized as
- `def R15.gsSupport` [ArkLib\Data\CodingTheory\ProximityGap\SudanListBound.lean:69](../../../ArkLib\Data\CodingTheory\ProximityGap\SudanListBound.lean#L69) — Monomial support of the Sudan interpolation space: pairs `(i, j)` with `i + (k-1)·j < D`, organized
- `def R15.gsSupport` [ArkLib\Data\CodingTheory\ProximityGap\SudanListBoundFull.lean:69](../../../ArkLib\Data\CodingTheory\ProximityGap\SudanListBoundFull.lean#L69) — Monomial support of the Sudan interpolation space: pairs `(i, j)` with `i + (k-1)·j < D`, organized

### `gsSupport_card` (4 declarations, 4 files)

- `lemma GSHasse.gsSupport_card` [ArkLib\Data\CodingTheory\ProximityGap\GSHasseMultiplicity.lean:89](../../../ArkLib\Data\CodingTheory\ProximityGap\GSHasseMultiplicity.lean#L89) — Exact count of the monomial support: `∑_{j<D} (D - (k-1)·j)`.
- `lemma GSInterp.gsSupport_card` [ArkLib\Data\CodingTheory\ProximityGap\GSInterpolationExistence.lean:75](../../../ArkLib\Data\CodingTheory\ProximityGap\GSInterpolationExistence.lean#L75) — Exact count of the monomial support: `∑_{j<D} (D - (k-1)·j)`.
- `lemma R15.gsSupport_card` [ArkLib\Data\CodingTheory\ProximityGap\SudanListBound.lean:82](../../../ArkLib\Data\CodingTheory\ProximityGap\SudanListBound.lean#L82) — Exact count of the monomial support: `∑_{j<D} (D - (k-1)·j)`.
- `lemma R15.gsSupport_card` [ArkLib\Data\CodingTheory\ProximityGap\SudanListBoundFull.lean:82](../../../ArkLib\Data\CodingTheory\ProximityGap\SudanListBoundFull.lean#L82) — Exact count of the monomial support: `∑_{j<D} (D - (k-1)·j)`.

### `gsSupport_weight_lt` (4 declarations, 4 files)

- `lemma GSHasse.gsSupport_weight_lt` [ArkLib\Data\CodingTheory\ProximityGap\GSHasseMultiplicity.lean:72](../../../ArkLib\Data\CodingTheory\ProximityGap\GSHasseMultiplicity.lean#L72) — (no docstring)
- `lemma GSInterp.gsSupport_weight_lt` [ArkLib\Data\CodingTheory\ProximityGap\GSInterpolationExistence.lean:58](../../../ArkLib\Data\CodingTheory\ProximityGap\GSInterpolationExistence.lean#L58) — (no docstring)
- `lemma R15.gsSupport_weight_lt` [ArkLib\Data\CodingTheory\ProximityGap\SudanListBound.lean:72](../../../ArkLib\Data\CodingTheory\ProximityGap\SudanListBound.lean#L72) — (no docstring)
- `lemma R15.gsSupport_weight_lt` [ArkLib\Data\CodingTheory\ProximityGap\SudanListBoundFull.lean:72](../../../ArkLib\Data\CodingTheory\ProximityGap\SudanListBoundFull.lean#L72) — (no docstring)

### `natDegree_eval_lt` (4 declarations, 4 files)

- `theorem GSHasse.natDegree_eval_lt` [ArkLib\Data\CodingTheory\ProximityGap\GSHasseMultiplicity.lean:381](../../../ArkLib\Data\CodingTheory\ProximityGap\GSHasseMultiplicity.lean#L381) — Weighted-degree transfer (as in the multiplicity-1 brick): the support-form weighted degree bound gi
- `theorem GSRootOrder.natDegree_eval_lt` [ArkLib\Data\CodingTheory\ProximityGap\GSRootOrderStep.lean:24](../../../ArkLib\Data\CodingTheory\ProximityGap\GSRootOrderStep.lean#L24) — **Weighted-degree transfer.** If every `Y`-coefficient of `Q : (F[X])[Y]` obeys the `(1, k−1)`-weigh
- `theorem R15.natDegree_eval_lt` [ArkLib\Data\CodingTheory\ProximityGap\SudanListBound.lean:211](../../../ArkLib\Data\CodingTheory\ProximityGap\SudanListBound.lean#L211) — Weighted-degree transfer: the univariate restriction `Q(X, f(X))` has degree `< D`.
- `theorem R15.natDegree_eval_lt` [ArkLib\Data\CodingTheory\ProximityGap\SudanListBoundFull.lean:211](../../../ArkLib\Data\CodingTheory\ProximityGap\SudanListBoundFull.lean#L211) — Weighted-degree transfer: the univariate restriction `Q(X, f(X))` has degree `< D`.

### `foldl_add_eq_sum` (4 declarations, 4 files)

- `theorem Spartan.Spec.foldl_add_eq_sum` [ArkLib\ProofSystem\Spartan\FirstSumcheckMulVec.lean:36](../../../ArkLib\ProofSystem\Spartan\FirstSumcheckMulVec.lean#L36) — A left fold that accumulates `acc + g y` over a list equals `acc` plus the list sum of `g`.
- `theorem Spartan.Spec.foldl_add_eq_sum` [ArkLib\ProofSystem\Spartan\FirstSumcheckZeroEval.lean:39](../../../ArkLib\ProofSystem\Spartan\FirstSumcheckZeroEval.lean#L39) — A left fold that accumulates `acc + g y` over a list equals `acc` plus the list sum of `g`.
- `theorem Sumcheck.Spec.SingleRound.foldl_add_eq_sum` [ArkLib\ProofSystem\Sumcheck\Spec\SimpleRoundCoherent.lean:78](../../../ArkLib\ProofSystem\Sumcheck\Spec\SimpleRoundCoherent.lean#L78) — A left fold that accumulates `acc + g y` over a list equals `acc` plus the list sum of `g`.
- `theorem Sumcheck.Spec.SingleRound.foldl_add_eq_sum` [ArkLib\ProofSystem\Sumcheck\Spec\SingleRoundFaithful.lean:56](../../../ArkLib\ProofSystem\Sumcheck\Spec\SingleRoundFaithful.lean#L56) — A left fold that accumulates `acc + g y` over a list equals `acc` plus the list sum of `g`. (Local c

### `prizeRates_le_half` (4 declarations, 4 files)

- `lemma ProximityGap.prizeRates_le_half` [ArkLib\Data\CodingTheory\ProximityGap\GrandChallengeDecision.lean:141](../../../ArkLib\Data\CodingTheory\ProximityGap\GrandChallengeDecision.lean#L141) — Every prize rate is `≤ 1/2`.
- `lemma ProximityGap.GrandChallengesLattice.prizeRates_le_half` [ArkLib\Data\CodingTheory\ProximityGap\GrandChallengeInteriorJ1.lean:626](../../../ArkLib\Data\CodingTheory\ProximityGap\GrandChallengeInteriorJ1.lean#L626) — Every ABF26 prize rate is at most `1/2`.
- `lemma ProximityGap.prizeRates_le_half` [ArkLib\Data\CodingTheory\ProximityGap\GrandChallengeLDFourRate.lean:208](../../../ArkLib\Data\CodingTheory\ProximityGap\GrandChallengeLDFourRate.lean#L208) — Every ABF26 prize rate is at most `1/2`.
- `lemma ProximityGap.prizeRates_le_half` [ArkLib\Data\CodingTheory\ProximityGap\MCASecondMoment.lean:363](../../../ArkLib\Data\CodingTheory\ProximityGap\MCASecondMoment.lean#L363) — Every prize rate is at most `1/2`.

### `completeness` (6 declarations, 3 files)

- `abbrev DuplexSpongeFS.NARG.completeness` [ArkLib\OracleReduction\FiatShamir\DuplexSponge\Basic.lean:59](../../../ArkLib\OracleReduction\FiatShamir\DuplexSponge\Basic.lean#L59) — Paper-facing alias for CO25 Section 3.4 completeness.
- `def Reduction.completeness` [ArkLib\OracleReduction\Security\Basic.lean:117](../../../ArkLib\OracleReduction\Security\Basic.lean#L117) — A reduction satisfies **completeness** with regards to: - an initialization function `init : ProbCom
- `def OracleReduction.completeness` [ArkLib\OracleReduction\Security\Basic.lean:463](../../../ArkLib\OracleReduction\Security\Basic.lean#L463) — Completeness of an oracle reduction is the same as for non-oracle reductions.
- `def Proof.completeness` [ArkLib\OracleReduction\Security\Basic.lean:517](../../../ArkLib\OracleReduction\Security\Basic.lean#L517) — (no docstring)
- `def OracleProof.completeness` [ArkLib\OracleReduction\Security\Basic.lean:546](../../../ArkLib\OracleReduction\Security\Basic.lean#L546) — Completeness of an oracle reduction is the same as for non-oracle reductions.
- `theorem SendClaim.completeness` [ArkLib\ProofSystem\Component\SendClaim.lean:114](../../../ArkLib\ProofSystem\Component\SendClaim.lean#L114) — (no docstring)

### `soundness` (6 declarations, 3 files)

- `abbrev DuplexSpongeFS.NARG.soundness` [ArkLib\OracleReduction\FiatShamir\DuplexSponge\Basic.lean:72](../../../ArkLib\OracleReduction\FiatShamir\DuplexSponge\Basic.lean#L72) — Paper-facing alias for CO25 Section 3.4 soundness.
- `def Verifier.soundness` [ArkLib\OracleReduction\Security\Basic.lean:295](../../../ArkLib\OracleReduction\Security\Basic.lean#L295) — A reduction satisfies **soundness** with error `soundnessError ≥ 0` and with respect to input langua
- `def OracleVerifier.soundness` [ArkLib\OracleReduction\Security\Basic.lean:484](../../../ArkLib\OracleReduction\Security\Basic.lean#L484) — Soundness of an oracle reduction is the same as for non-oracle reductions.
- `def Proof.soundness` [ArkLib\OracleReduction\Security\Basic.lean:527](../../../ArkLib\OracleReduction\Security\Basic.lean#L527) — (no docstring)
- `def OracleProof.soundness` [ArkLib\OracleReduction\Security\Basic.lean:563](../../../ArkLib\OracleReduction\Security\Basic.lean#L563) — Soundness of an oracle reduction is the same as for non-oracle reductions.
- `def Verifier.StateRestoration.soundness` [ArkLib\OracleReduction\Security\StateRestoration.lean:127](../../../ArkLib\OracleReduction\Security\StateRestoration.lean#L127) — State-restoration soundness

### `aStar` (5 declarations, 3 files)

- `def R10ExactDelta.aStar` [ArkLib\Data\CodingTheory\ProximityGap\DeltaStarExactCrossoverF17.lean:82](../../../ArkLib\Data\CodingTheory\ProximityGap\DeltaStarExactCrossoverF17.lean#L82) — The crossover threshold `a* = 4` (relative distance `δ* = 1 - 4/16 = 3/4`).
- `def R11DeltaTable.Row1.aStar` [ArkLib\Data\CodingTheory\ProximityGap\DeltaStarTableSmoothInstances.lean:138](../../../ArkLib\Data\CodingTheory\ProximityGap\DeltaStarTableSmoothInstances.lean#L138) — The crossover threshold `a* = 5` (`δ* = 1 - 5/16 = 11/16`).
- `def R11DeltaTable.Row2.aStar` [ArkLib\Data\CodingTheory\ProximityGap\DeltaStarTableSmoothInstances.lean:196](../../../ArkLib\Data\CodingTheory\ProximityGap\DeltaStarTableSmoothInstances.lean#L196) — The crossover threshold `a* = 3` (`δ* = 1 - 3/8 = 5/8`).
- `def R11DeltaTable.Row3.aStar` [ArkLib\Data\CodingTheory\ProximityGap\DeltaStarTableSmoothInstances.lean:253](../../../ArkLib\Data\CodingTheory\ProximityGap\DeltaStarTableSmoothInstances.lean#L253) — The crossover threshold `a* = 3` (`δ* = 1 - 3/8 = 5/8`).
- `def ArkLib.CodingTheory.ListThresholdWellDefined.aStar` [ArkLib\Data\CodingTheory\ProximityGap\ListThresholdWellDefined.lean:157](../../../ArkLib\Data\CodingTheory\ProximityGap\ListThresholdWellDefined.lean#L157) — **The threshold, as a named object:** the minimal agreement demand meeting the budget.

### `ratchet` (5 declarations, 3 files)

- `def DomainSeparator.ratchet` [ArkLib\Data\Hash\DomainSep.lean:255](../../../ArkLib\Data\Hash\DomainSep.lean#L255) — Ratchet the state. Rust interface: ```rust pub fn ratchet(self) -> Self ```
- `def DuplexSponge.ratchet` [ArkLib\Data\Hash\DuplexSponge.lean:612](../../../ArkLib\Data\Hash\DuplexSponge.lean#L612) — ### Ratchet the sponge state for domain separation Algorithm (from Rust implementation): 1. Permute
- `def HashStateWithInstructions.ratchet` [ArkLib\OracleReduction\FiatShamir\DuplexSponge\State.lean:217](../../../ArkLib\OracleReduction\FiatShamir\DuplexSponge\State.lean#L217) — Perform a ratchet operation. Rust interface: ```rust pub fn ratchet(&mut self) -> Result<(), DomainS
- `def FSVerifierState.ratchet` [ArkLib\OracleReduction\FiatShamir\DuplexSponge\State.lean:348](../../../ArkLib\OracleReduction\FiatShamir\DuplexSponge\State.lean#L348) — Signal the end of statement with ratcheting. Rust interface: ```rust pub fn ratchet(&mut self) -> Re
- `def FSProverState.ratchet` [ArkLib\OracleReduction\FiatShamir\DuplexSponge\State.lean:459](../../../ArkLib\OracleReduction\FiatShamir\DuplexSponge\State.lean#L459) — Ratchet the protocol state. Rust interface: ```rust pub fn ratchet(&mut self) -> Result<(), DomainSe

### `Adversary` (4 declarations, 3 files)

- `def AGM.Adversary` [ArkLib\AGM\Basic.lean:468](../../../ArkLib\AGM\Basic.lean#L468) — An adversary in the Algebraic Group Model (AGM) is defined as follows: - It is given knowledge of th
- `abbrev ArkLib.Lattices.Ajtai.InnerOuter.WeakBinding.Adversary` [ArkLib\CommitmentScheme\Ajtai\InnerOuter\Security.lean:92](../../../ArkLib\CommitmentScheme\Ajtai\InnerOuter\Security.lean#L92) — A weak-binding adversary outputs two weak openings for the same commitment.
- `abbrev ArkLib.Lattices.SIS.Adversary` [ArkLib\Data\Lattices\ModuleSIS.lean:53](../../../ArkLib\Data\Lattices\ModuleSIS.lean#L53) — A search adversary for a SIS-style problem.
- `abbrev ArkLib.Lattices.ModuleSIS.Adversary` [ArkLib\Data\Lattices\ModuleSIS.lean:96](../../../ArkLib\Data\Lattices\ModuleSIS.lean#L96) — A Module-SIS adversary.

### `StmtOut` (4 declarations, 3 files)

- `def RandomQuery.StmtOut` [ArkLib\ProofSystem\Component\RandomQuery.lean:34](../../../ArkLib\ProofSystem\Component\RandomQuery.lean#L34) — (no docstring)
- `def Logup.StmtOut` [ArkLib\ProofSystem\Logup\Common.lean:280](../../../ArkLib\ProofSystem\Logup\Common.lean#L280) — The full LogUp protocol returns no additional public data on success.
- `def Sumcheck.Spec.SingleRound.Simpler.StmtOut` [ArkLib\ProofSystem\Sumcheck\Spec\SingleRound.lean:364](../../../ArkLib\ProofSystem\Sumcheck\Spec\SingleRound.lean#L364) — (no docstring)
- `def Sumcheck.Spec.SingleRound.Simple.StmtOut` [ArkLib\ProofSystem\Sumcheck\Spec\SingleRound.lean:588](../../../ArkLib\ProofSystem\Sumcheck\Spec\SingleRound.lean#L588) — (no docstring)

### `append` (4 declarations, 3 files)

- `def AGM.GroupRepresentation.append` [ArkLib\AGM\RepresentationLemmas.lean:164](../../../ArkLib\AGM\RepresentationLemmas.lean#L164) — **Representations compose multiplicatively.** Concatenating the bases and exponent vectors of two al
- `def Interaction.Oracle.Spec.append` [ArkLib\Interaction\Oracle\Spec.lean:216](../../../ArkLib\Interaction\Oracle\Spec.lean#L216) — (no docstring)
- `abbrev ProtocolSpec.append` [ArkLib\OracleReduction\ProtocolSpec\SeqCompose.lean:49](../../../ArkLib\OracleReduction\ProtocolSpec\SeqCompose.lean#L49) — Appending two `ProtocolSpec`s
- `def ProtocolSpec.FullTranscript.append` [ArkLib\OracleReduction\ProtocolSpec\SeqCompose.lean:160](../../../ArkLib\OracleReduction\ProtocolSpec\SeqCompose.lean#L160) — Appending two transcripts for two `ProtocolSpec`s

### `correctness` (4 declarations, 3 files)

- `def Commitment.correctness` [ArkLib\CommitmentScheme\Basic.lean:88](../../../ArkLib\CommitmentScheme\Basic.lean#L88) — A commitment scheme satisfies **correctness** with error `correctnessError` if for all `data : Data`
- `def CommitmentScheme.correctness` [ArkLib\CommitmentScheme\CommitmentScheme.lean:64](../../../ArkLib\CommitmentScheme\CommitmentScheme.lean#L64) — A commitment scheme satisfies **correctness** with error `correctnessError` if, for every message, t
- `theorem KZG.correctness` [ArkLib\CommitmentScheme\KZG\Correctness.lean:51](../../../ArkLib\CommitmentScheme\KZG\Correctness.lean#L51) — Algebraic correctness of one KZG opening for a coefficient vector.
- `theorem KZG.CommitmentScheme.correctness` [ArkLib\CommitmentScheme\KZG\Correctness.lean:161](../../../ArkLib\CommitmentScheme\KZG\Correctness.lean#L161) — The KZG scheme satisfies perfect correctness as defined in `CommitmentScheme`.

### `drop` (4 declarations, 3 files)

- `def Fin.drop` [ArkLib\Data\Fin\Tuple\Defs.lean:60](../../../ArkLib\Data\Fin\Tuple\Defs.lean#L60) — Drop the first `m` elements of an `n`-tuple where `m ≤ n`, returning an `(n - m)`-tuple.
- `def ProtocolSpec.drop` [ArkLib\OracleReduction\ProtocolSpec\Basic.lean:129](../../../ArkLib\OracleReduction\ProtocolSpec\Basic.lean#L129) — Drop the first `m ≤ n` rounds of a `ProtocolSpec n`
- `abbrev ProtocolSpec.FullTranscript.drop` [ArkLib\OracleReduction\ProtocolSpec\Basic.lean:186](../../../ArkLib\OracleReduction\ProtocolSpec\Basic.lean#L186) — (no docstring)
- `def SumcheckDomain.drop` [ArkLib\ProofSystem\Sumcheck\Domain.lean:133](../../../ArkLib\ProofSystem\Sumcheck\Domain.lean#L133) — Drop the first `j` coordinates, leaving the domain on the remaining `k - j` coordinates: coordinate

### `toFinset` (4 declarations, 3 files)

- `def ReedSolomon.toFinset` [ArkLib\Data\CodingTheory\ReedSolomon.lean:97](../../../ArkLib\Data\CodingTheory\ReedSolomon.lean#L97) — (no docstring)
- `def Domain.CosetFftDomainClass.toFinset` [ArkLib\Data\Domain\CosetFftDomain\Defs.lean:242](../../../ArkLib\Data\Domain\CosetFftDomain\Defs.lean#L242) — (no docstring)
- `abbrev Domain.CosetFftDomain.toFinset` [ArkLib\Data\Domain\CosetFftDomain\Defs.lean:258](../../../ArkLib\Data\Domain\CosetFftDomain\Defs.lean#L258) — (no docstring)
- `abbrev Domain.FftDomain.toFinset` [ArkLib\Data\Domain\FftDomain\Defs.lean:126](../../../ArkLib\Data\Domain\FftDomain\Defs.lean#L126) — (no docstring)

### `G_card` (3 declarations, 3 files)

- `theorem ArkLib.ProximityGap.AdditiveEnergyFullGroupClosedForm.G_card` [ArkLib\Data\CodingTheory\ProximityGap\AdditiveEnergyFullGroupClosedForm.lean:44](../../../ArkLib\Data\CodingTheory\ProximityGap\AdditiveEnergyFullGroupClosedForm.lean#L44) — (no docstring)
- `theorem ArkLib.ProximityGap.SubgroupAdditiveEnergyF17.G_card` [ArkLib\Data\CodingTheory\ProximityGap\SubgroupAdditiveEnergyF17.lean:47](../../../ArkLib\Data\CodingTheory\ProximityGap\SubgroupAdditiveEnergyF17.lean#L47) — (no docstring)
- `theorem ArkLib.ProximityGap.SubgroupRepCountFiniteFieldCounterexample.G_card` [ArkLib\Data\CodingTheory\ProximityGap\SubgroupRepCountFiniteFieldCounterexample.lean:51](../../../ArkLib\Data\CodingTheory\ProximityGap\SubgroupRepCountFiniteFieldCounterexample.lean#L51) — `G` has `8` elements (it is the full subgroup of `8`-th roots of unity, since `8 ∣ 16 = \|F₁₇ˣ\|`).

### `L_subset_code` (3 declarations, 3 files)

- `theorem ArkLib.CodingTheory.TinyInteriorPin.L_subset_code` [ArkLib\Data\CodingTheory\ProximityGap\ListInteriorDataPointF7.lean:127](../../../ArkLib\Data\CodingTheory\ProximityGap\ListInteriorDataPointF7.lean#L127) — **Every element of `L` is a Reed–Solomon codeword of degree `< 2`.** This is the non-vacuity witness
- `theorem ArkLib.CodingTheory.TinyInteriorK3.L_subset_code` [ArkLib\Data\CodingTheory\ProximityGap\ListInteriorPinF11K3.lean:152](../../../ArkLib\Data\CodingTheory\ProximityGap\ListInteriorPinF11K3.lean#L152) — **Every element of `L` is a Reed–Solomon codeword of degree `< 3`.** Non-vacuity: `L` lives inside t
- `theorem ArkLib.CodingTheory.Round3SmoothF17.L_subset_code` [ArkLib\Data\CodingTheory\ProximityGap\ListInteriorPinF17Subgroup.lean:162](../../../ArkLib\Data\CodingTheory\ProximityGap\ListInteriorPinF17Subgroup.lean#L162) — **Every element of `L` is a smooth-domain Reed–Solomon codeword of degree `< 2`.** This is the non-v

### `Message` (3 declarations, 3 files)

- `abbrev ArkLib.Lattices.Ajtai.InnerOuter.Message` [ArkLib\CommitmentScheme\Ajtai\InnerOuter\Scheme.lean:122](../../../ArkLib\CommitmentScheme\Ajtai\InnerOuter\Scheme.lean#L122) — Messages: block vectors over the message row space.
- `abbrev ArkLib.Lattices.Ajtai.Simple.Message` [ArkLib\CommitmentScheme\Ajtai\Simple\Scheme.lean:32](../../../ArkLib\CommitmentScheme\Ajtai\Simple\Scheme.lean#L32) — Messages: column vectors over `Rq Φ`.
- `def ProtocolSpec.Message` [ArkLib\OracleReduction\ProtocolSpec\Basic.lean:78](../../../ArkLib\OracleReduction\ProtocolSpec\Basic.lean#L78) — The type of the `i`-th message in a protocol specification. This does not distinguish between messag

### `Opening` (3 declarations, 3 files)

- `structure ArkLib.Lattices.Ajtai.InnerOuter.Opening` [ArkLib\CommitmentScheme\Ajtai\InnerOuter\Scheme.lean:98](../../../ArkLib\CommitmentScheme\Ajtai\InnerOuter\Scheme.lean#L98) — A Hachi/Greyhound *weak opening* `(sᵢ, t̂ᵢ, cᵢ)ᵢ`: the decomposition data `(sᵢ, t̂ᵢ)` (`Decomp`) ext
- `abbrev ArkLib.Lattices.Ajtai.Simple.Opening` [ArkLib\CommitmentScheme\Ajtai\Simple\Scheme.lean:43](../../../ArkLib\CommitmentScheme\Ajtai\Simple\Scheme.lean#L43) — The simple Ajtai commitment has no auxiliary opening data.
- `structure Commitment.Opening` [ArkLib\CommitmentScheme\Basic.lean:59](../../../ArkLib\CommitmentScheme\Basic.lean#L59) — The opening protocol used to prove a claimed oracle response for committed data.

### `OutputStatement` (3 declarations, 3 files)

- `abbrev Sumcheck.Spec.OutputStatement` [ArkLib\ProofSystem\Sumcheck\Spec\SingleRound.lean:131](../../../ArkLib\ProofSystem\Sumcheck\Spec\SingleRound.lean#L131) — (no docstring)
- `def ToyProblem.Spec.OutputStatement` [ArkLib\ProofSystem\ToyProblem\Spec\General.lean:112](../../../ArkLib\ProofSystem\ToyProblem\Spec\General.lean#L112) — Output statement: the IOR is a yes/no test — accept (return `()`) or short-circuit to `none` via `Op
- `def ToyProblem.SimplifiedIOR.OutputStatement` [ArkLib\ProofSystem\ToyProblem\Spec\SimplifiedIOR.lean:72](../../../ArkLib\ProofSystem\ToyProblem\Spec\SimplifiedIOR.lean#L72) — Output statement for C6.9: the new `(v, μ_new)` pair. The constraint count drops from 2 to 1 (a sing

### `Params` (3 declarations, 3 files)

- `structure Poseidon2.Params` [ArkLib\Data\Hash\Poseidon2.lean:412](../../../ArkLib\Data\Hash\Poseidon2.lean#L412) — The parameters determining a Poseidon2 permutation (over the KoalaBear field)
- `structure StirIOP.Params` [ArkLib\ProofSystem\Stir\MainThm.lean:35](../../../ArkLib\ProofSystem\Stir\MainThm.lean#L35) — **Per‑round protocol parameters:** For a fixed depth `M`, the reduction runs `M + 1` rounds. In roun
- `structure WhirIOP.Params` [ArkLib\ProofSystem\Whir\RBRSoundness.lean:54](../../../ArkLib\ProofSystem\Whir\RBRSoundness.lean#L54) — ** Per‑round protocol parameters. ** For a fixed depth `M`, the reduction runs `M + 1` rounds. In ro

### `Prover` (4 declarations, 3 files)

- `abbrev Interaction.Oracle.Prover` [ArkLib\Interaction\Oracle\Core.lean:1140](../../../ArkLib\Interaction\Oracle\Core.lean#L1140) — (no docstring)
- `abbrev Interaction.Prover` [ArkLib\Interaction\Reduction.lean:115](../../../ArkLib\Interaction\Reduction.lean#L115) — (no docstring)
- `structure Prover` [ArkLib\OracleReduction\Basic.lean:168](../../../ArkLib\OracleReduction\Basic.lean#L168) — (no docstring)
- `structure Prover` [ArkLib\OracleReduction\Basic.lean:413](../../../ArkLib\OracleReduction\Basic.lean#L413) — The type of honest provers for an interactive reduction with `n` messages. This consists of: - `PrvS

### `PublicParams` (3 declarations, 3 files)

- `structure ArkLib.Lattices.Ajtai.InnerOuter.PublicParams` [ArkLib\CommitmentScheme\Ajtai\InnerOuter\Scheme.lean:77](../../../ArkLib\CommitmentScheme\Ajtai\InnerOuter\Scheme.lean#L77) — Public parameters: inner Ajtai matrix `A` and outer Ajtai matrix `B`.
- `abbrev ArkLib.Lattices.Ajtai.Simple.PublicParams` [ArkLib\CommitmentScheme\Ajtai\Simple\Scheme.lean:29](../../../ArkLib\CommitmentScheme\Ajtai\Simple\Scheme.lean#L29) — Public parameters: the Ajtai matrix `A`.
- `structure Spartan.PublicParams` [ArkLib\ProofSystem\Spartan\Basic.lean:26](../../../ArkLib\ProofSystem\Spartan\Basic.lean#L26) — The public parameters of the (padded) Spartan protocol. Consists of the number of bits of the R1CS d

### `Reduction` (3 declarations, 3 files)

- `structure Interaction.Oracle.Reduction` [ArkLib\Interaction\Oracle\Core.lean:1217](../../../ArkLib\Interaction\Oracle\Core.lean#L1217) — (no docstring)
- `structure Interaction.Reduction` [ArkLib\Interaction\Reduction.lean:187](../../../ArkLib\Interaction\Reduction.lean#L187) — (no docstring)
- `structure Reduction` [ArkLib\OracleReduction\Basic.lean:760](../../../ArkLib\OracleReduction\Basic.lean#L760) — An **interactive reduction** for a given protocol specification `pSpec`, and relative to oracles def

### `StraightlineExtractor` (3 declarations, 3 files)

- `abbrev Commitment.StraightlineExtractor` [ArkLib\CommitmentScheme\Basic.lean:178](../../../ArkLib\CommitmentScheme\Basic.lean#L178) — A **straightline extractor** for a commitment scheme takes in the commitment, the log of queries mad
- `def CommitmentScheme.StraightlineExtractor` [ArkLib\CommitmentScheme\CommitmentScheme.lean:123](../../../ArkLib\CommitmentScheme\CommitmentScheme.lean#L123) — A **straightline extractor** for a standard commitment scheme takes the commitment and the log of qu
- `abbrev DuplexSpongeFS.NARG.StraightlineExtractor` [ArkLib\OracleReduction\FiatShamir\DuplexSponge\Basic.lean:86](../../../ArkLib\OracleReduction\FiatShamir\DuplexSponge\Basic.lean#L86) — Paper-facing alias for the straightline extractor interface used in Section 3.4.

### `Verifier` (3 declarations, 3 files)

- `structure Interaction.Oracle.Verifier` [ArkLib\Interaction\Oracle\Core.lean:1180](../../../ArkLib\Interaction\Oracle\Core.lean#L1180) — (no docstring)
- `abbrev Interaction.Verifier` [ArkLib\Interaction\Reduction.lean:130](../../../ArkLib\Interaction\Reduction.lean#L130) — (no docstring)
- `structure Verifier` [ArkLib\OracleReduction\Basic.lean:438](../../../ArkLib\OracleReduction\Basic.lean#L438) — A verifier of an interactive protocol is a function that takes in the input statement and the transc

### `absorb` (3 declarations, 3 files)

- `def DomainSeparator.absorb` [ArkLib\Data\Hash\DomainSep.lean:216](../../../ArkLib\Data\Hash\DomainSep.lean#L216) — Absorb `count` native elements. Rust interface: ```rust pub fn absorb(self, count: usize, label: &st
- `def DuplexSponge.absorb` [ArkLib\Data\Hash\DuplexSponge.lean:416](../../../ArkLib\Data\Hash\DuplexSponge.lean#L416) — ### Absorb a list of units into the sponge (paper version) Paper algorithm (process one element at a
- `def HashStateWithInstructions.absorb` [ArkLib\OracleReduction\FiatShamir\DuplexSponge\State.lean:110](../../../ArkLib\OracleReduction\FiatShamir\DuplexSponge\State.lean#L110) — Perform secure absorption of elements into the sponge. Rust interface: ```rust pub fn absorb(&mut se

### `antipodal_of_sum_zero` (3 declarations, 3 files)

- `theorem R12J.antipodal_of_sum_zero` [ArkLib\Data\CodingTheory\ProximityGap\JointT2Unconditional.lean:118](../../../ArkLib\Data\CodingTheory\ProximityGap\JointT2Unconditional.lean#L118) — **Antipodal tightness engine.** If the first `N` powers of `g` are `K`-linearly independent, any sub
- `theorem R12.antipodal_of_sum_zero` [ArkLib\Data\CodingTheory\ProximityGap\LamLeungUnconditionalGeneral.lean:95](../../../ArkLib\Data\CodingTheory\ProximityGap\LamLeungUnconditionalGeneral.lean#L95) — **General antipodal tightness.** If the first `N` powers of `ζ` are `K`-linearly independent (UNCOND
- `theorem R11.antipodal_of_sum_zero` [ArkLib\Data\CodingTheory\ProximityGap\LamLeungUnconditionalQ.lean:91](../../../ArkLib\Data\CodingTheory\ProximityGap\LamLeungUnconditionalQ.lean#L91) — **General unconditional antipodal tightness.** If the first `N` powers of `ζ` are `K`-linearly indep

### `badSet` (3 declarations, 3 files)

- `def Round17CAPair.badSet` [ArkLib\Data\CodingTheory\ProximityGap\CAPairExtractionEngine.lean:108](../../../ArkLib\Data\CodingTheory\ProximityGap\CAPairExtractionEngine.lean#L108) — `γ` is **`a`-bad** for `(f₁, f₂)` w.r.t. the code `C` if `f₁ + γ·f₂` agrees with some codeword on at
- `def LinePairCooccurrence.badSet` [ArkLib\Data\CodingTheory\ProximityGap\LinePairCooccurrenceBound.lean:85](../../../ArkLib\Data\CodingTheory\ProximityGap\LinePairCooccurrenceBound.lean#L85) — The bad set: line parameters whose point has agreement `≥ a` with both `c` and `c'`.
- `def ProximityGap.MCANearCapacity.badSet` [ArkLib\Data\CodingTheory\ProximityGap\MCANearCapacityLowerBound.lean:115](../../../ArkLib\Data\CodingTheory\ProximityGap\MCANearCapacityLowerBound.lean#L115) — The bad-scalar set `{ -(2j+1) : 0 ≤ j < n-1 }`.

### `binding` (3 declarations, 3 files)

- `def Commitment.binding` [ArkLib\CommitmentScheme\Basic.lean:170](../../../ArkLib\CommitmentScheme\Basic.lean#L170) — A commitment scheme satisfies **(evaluation) binding** with error `bindingError` if for all adversar
- `def CommitmentScheme.binding` [ArkLib\CommitmentScheme\CommitmentScheme.lean:104](../../../ArkLib\CommitmentScheme\CommitmentScheme.lean#L104) — A commitment scheme satisfies **binding** with error `bindingError` if every adversary's probability
- `theorem KZG.CommitmentScheme.binding` [ArkLib\CommitmentScheme\KZG\Binding.lean:737](../../../ArkLib\CommitmentScheme\KZG\Binding.lean#L737) — The KZG scheme satisfies evaluation binding provided `t`-SDH holds.

### `c0_isRS` (3 declarations, 3 files)

- `lemma ArkLib.CodingTheory.TinyInteriorPin.c0_isRS` [ArkLib\Data\CodingTheory\ProximityGap\ListInteriorDataPointF7.lean:95](../../../ArkLib\Data\CodingTheory\ProximityGap\ListInteriorDataPointF7.lean#L95) — (no docstring)
- `lemma ArkLib.CodingTheory.TinyInteriorK3.c0_isRS` [ArkLib\Data\CodingTheory\ProximityGap\ListInteriorPinF11K3.lean:113](../../../ArkLib\Data\CodingTheory\ProximityGap\ListInteriorPinF11K3.lean#L113) — (no docstring)
- `lemma ArkLib.CodingTheory.Round3SmoothF17.c0_isRS` [ArkLib\Data\CodingTheory\ProximityGap\ListInteriorPinF17Subgroup.lean:130](../../../ArkLib\Data\CodingTheory\ProximityGap\ListInteriorPinF17Subgroup.lean#L130) — (no docstring)

### `c1_isRS` (3 declarations, 3 files)

- `lemma ArkLib.CodingTheory.TinyInteriorPin.c1_isRS` [ArkLib\Data\CodingTheory\ProximityGap\ListInteriorDataPointF7.lean:97](../../../ArkLib\Data\CodingTheory\ProximityGap\ListInteriorDataPointF7.lean#L97) — (no docstring)
- `lemma ArkLib.CodingTheory.TinyInteriorK3.c1_isRS` [ArkLib\Data\CodingTheory\ProximityGap\ListInteriorPinF11K3.lean:117](../../../ArkLib\Data\CodingTheory\ProximityGap\ListInteriorPinF11K3.lean#L117) — (no docstring)
- `lemma ArkLib.CodingTheory.Round3SmoothF17.c1_isRS` [ArkLib\Data\CodingTheory\ProximityGap\ListInteriorPinF17Subgroup.lean:133](../../../ArkLib\Data\CodingTheory\ProximityGap\ListInteriorPinF17Subgroup.lean#L133) — (no docstring)

### `c2_isRS` (3 declarations, 3 files)

- `lemma ArkLib.CodingTheory.TinyInteriorPin.c2_isRS` [ArkLib\Data\CodingTheory\ProximityGap\ListInteriorDataPointF7.lean:101](../../../ArkLib\Data\CodingTheory\ProximityGap\ListInteriorDataPointF7.lean#L101) — (no docstring)
- `lemma ArkLib.CodingTheory.TinyInteriorK3.c2_isRS` [ArkLib\Data\CodingTheory\ProximityGap\ListInteriorPinF11K3.lean:121](../../../ArkLib\Data\CodingTheory\ProximityGap\ListInteriorPinF11K3.lean#L121) — (no docstring)
- `lemma ArkLib.CodingTheory.Round3SmoothF17.c2_isRS` [ArkLib\Data\CodingTheory\ProximityGap\ListInteriorPinF17Subgroup.lean:136](../../../ArkLib\Data\CodingTheory\ProximityGap\ListInteriorPinF17Subgroup.lean#L136) — (no docstring)

### `c3_isRS` (3 declarations, 3 files)

- `lemma ArkLib.CodingTheory.TinyInteriorPin.c3_isRS` [ArkLib\Data\CodingTheory\ProximityGap\ListInteriorDataPointF7.lean:105](../../../ArkLib\Data\CodingTheory\ProximityGap\ListInteriorDataPointF7.lean#L105) — (no docstring)
- `lemma ArkLib.CodingTheory.TinyInteriorK3.c3_isRS` [ArkLib\Data\CodingTheory\ProximityGap\ListInteriorPinF11K3.lean:125](../../../ArkLib\Data\CodingTheory\ProximityGap\ListInteriorPinF11K3.lean#L125) — (no docstring)
- `lemma ArkLib.CodingTheory.Round3SmoothF17.c3_isRS` [ArkLib\Data\CodingTheory\ProximityGap\ListInteriorPinF17Subgroup.lean:139](../../../ArkLib\Data\CodingTheory\ProximityGap\ListInteriorPinF17Subgroup.lean#L139) — (no docstring)

### `c4_isRS` (3 declarations, 3 files)

- `lemma ArkLib.CodingTheory.TinyInteriorPin.c4_isRS` [ArkLib\Data\CodingTheory\ProximityGap\ListInteriorDataPointF7.lean:109](../../../ArkLib\Data\CodingTheory\ProximityGap\ListInteriorDataPointF7.lean#L109) — (no docstring)
- `lemma ArkLib.CodingTheory.TinyInteriorK3.c4_isRS` [ArkLib\Data\CodingTheory\ProximityGap\ListInteriorPinF11K3.lean:129](../../../ArkLib\Data\CodingTheory\ProximityGap\ListInteriorPinF11K3.lean#L129) — (no docstring)
- `lemma ArkLib.CodingTheory.Round3SmoothF17.c4_isRS` [ArkLib\Data\CodingTheory\ProximityGap\ListInteriorPinF17Subgroup.lean:142](../../../ArkLib\Data\CodingTheory\ProximityGap\ListInteriorPinF17Subgroup.lean#L142) — (no docstring)

### `c5_isRS` (3 declarations, 3 files)

- `lemma ArkLib.CodingTheory.TinyInteriorPin.c5_isRS` [ArkLib\Data\CodingTheory\ProximityGap\ListInteriorDataPointF7.lean:113](../../../ArkLib\Data\CodingTheory\ProximityGap\ListInteriorDataPointF7.lean#L113) — (no docstring)
- `lemma ArkLib.CodingTheory.TinyInteriorK3.c5_isRS` [ArkLib\Data\CodingTheory\ProximityGap\ListInteriorPinF11K3.lean:133](../../../ArkLib\Data\CodingTheory\ProximityGap\ListInteriorPinF11K3.lean#L133) — (no docstring)
- `lemma ArkLib.CodingTheory.Round3SmoothF17.c5_isRS` [ArkLib\Data\CodingTheory\ProximityGap\ListInteriorPinF17Subgroup.lean:145](../../../ArkLib\Data\CodingTheory\ProximityGap\ListInteriorPinF17Subgroup.lean#L145) — (no docstring)

### `card_filter_eval_zero_le` (3 declarations, 3 files)

- `lemma ProximityGap.card_filter_eval_zero_le` [ArkLib\Data\CodingTheory\ProximityGap\BCIKS20\Curves\AgreementCount.lean:45](../../../ArkLib\Data\CodingTheory\ProximityGap\BCIKS20\Curves\AgreementCount.lean#L45) — Root-set cardinality bound (reproved inline to keep imports light): over a finite field a nonzero po
- `theorem RingSwitching.card_filter_eval_zero_le` [ArkLib\ProofSystem\RingSwitching\Prelude.lean:1813](../../../ArkLib\ProofSystem\RingSwitching\Prelude.lean#L1813) — **Root-set cardinality bound.** Over an integral domain `L`, the number of field elements at which a
- `theorem Polynomial.card_filter_eval_zero_le` [ArkLib\ToMathlib\ExtractedIssueBricks.lean:57](../../../ArkLib\ToMathlib\ExtractedIssueBricks.lean#L57) — **Root-set cardinality bound.** Over a finite integral domain `L`, a nonzero `p : L[X]` vanishes at

### `cards` (3 declarations, 3 files)

- `theorem ArkLib.ProximityGap.SubgroupAdditiveEnergyFermat257.cards` [ArkLib\Data\CodingTheory\ProximityGap\SubgroupAdditiveEnergyFermat257.lean:64](../../../ArkLib\Data\CodingTheory\ProximityGap\SubgroupAdditiveEnergyFermat257.lean#L64) — (no docstring)
- `theorem ArkLib.ProximityGap.SubgroupAdditiveEnergyFermat65537.cards` [ArkLib\Data\CodingTheory\ProximityGap\SubgroupAdditiveEnergyFermat65537.lean:54](../../../ArkLib\Data\CodingTheory\ProximityGap\SubgroupAdditiveEnergyFermat65537.lean#L54) — (no docstring)
- `theorem ArkLib.ProximityGap.SubgroupAdditiveEnergyTowerF17.cards` [ArkLib\Data\CodingTheory\ProximityGap\SubgroupAdditiveEnergyTowerF17.lean:49](../../../ArkLib\Data\CodingTheory\ProximityGap\SubgroupAdditiveEnergyTowerF17.lean#L49) — (no docstring)

### `choose_le_add_add` (3 declarations, 3 files)

- `theorem Round14ConstantGap.choose_le_add_add` [ArkLib\Data\CodingTheory\ProximityGap\DeltaStarConstantGapBelowCapacity.lean:56](../../../ArkLib\Data\CodingTheory\ProximityGap\DeltaStarConstantGapBelowCapacity.lean#L56) — **The Pascal shift.** `C(n, m) ≤ C(n + j, m + j)` for every `j` (iterate the one-step).
- `theorem R15Bracket.choose_le_add_add` [ArkLib\Data\CodingTheory\ProximityGap\PrizeScaleBracketFull.lean:283](../../../ArkLib\Data\CodingTheory\ProximityGap\PrizeScaleBracketFull.lean#L283) — The Pascal shift: `C(n, m) ≤ C(n + j, m + j)`.
- `theorem Round18Bracket.choose_le_add_add` [ArkLib\Data\CodingTheory\ProximityGap\TwoSidedBracketPrizeScale.lean:205](../../../ArkLib\Data\CodingTheory\ProximityGap\TwoSidedBracketPrizeScale.lean#L205) — Pascal shift `C(n,m) ≤ C(n+j, m+j)`.

### `cliqueLocator` (3 declarations, 3 files)

- `def Round19Clique.cliqueLocator` [ArkLib\Data\CodingTheory\ProximityGap\Conjecture41CliqueBeachhead.lean:62](../../../ArkLib\Data\CodingTheory\ProximityGap\Conjecture41CliqueBeachhead.lean#L62) — The error locator of the clique support `E_α = W ∖ {α}`: `Λ_{E_α}(X) = ∏_{β ∈ W.erase α} (X − β)` —
- `def Round20CliqueKernel.cliqueLocator` [ArkLib\Data\CodingTheory\ProximityGap\Conjecture41CliqueKernelStructure.lean:60](../../../ArkLib\Data\CodingTheory\ProximityGap\Conjecture41CliqueKernelStructure.lean#L60) — The clique error locator at vertex `α`: `Λ_{W∖{α}} = ∏_{β ∈ W.erase α} (X − β)`.
- `def Round21Relations.cliqueLocator` [ArkLib\Data\CodingTheory\ProximityGap\Conjecture41CliqueRelationModule.lean:56](../../../ArkLib\Data\CodingTheory\ProximityGap\Conjecture41CliqueRelationModule.lean#L56) — The clique error locator at vertex `α`: `Λ_{W∖{α}} = ∏_{β ∈ W.erase α} (X − β)`.

### `cliqueLocator_eval_other` (3 declarations, 3 files)

- `theorem Round19Clique.cliqueLocator_eval_other` [ArkLib\Data\CodingTheory\ProximityGap\Conjecture41CliqueBeachhead.lean:67](../../../ArkLib\Data\CodingTheory\ProximityGap\Conjecture41CliqueBeachhead.lean#L67) — **Diagonal evaluation, off-diagonal:** for `α' ∈ W`, `α' ≠ α`, the locator of `E_α` vanishes at `α'`
- `theorem Round20CliqueKernel.cliqueLocator_eval_other` [ArkLib\Data\CodingTheory\ProximityGap\Conjecture41CliqueKernelStructure.lean:105](../../../ArkLib\Data\CodingTheory\ProximityGap\Conjecture41CliqueKernelStructure.lean#L105) — Locator evaluation at the vertices: `Λ_{E_α}(β) = 0` for `β ∈ W`, `β ≠ α`.
- `theorem Round21Relations.cliqueLocator_eval_other` [ArkLib\Data\CodingTheory\ProximityGap\Conjecture41CliqueRelationModule.lean:78](../../../ArkLib\Data\CodingTheory\ProximityGap\Conjecture41CliqueRelationModule.lean#L78) — Locator evaluation off the diagonal vanishes.

### `cliqueLocator_eval_self_ne_zero` (3 declarations, 3 files)

- `theorem Round19Clique.cliqueLocator_eval_self_ne_zero` [ArkLib\Data\CodingTheory\ProximityGap\Conjecture41CliqueBeachhead.lean:84](../../../ArkLib\Data\CodingTheory\ProximityGap\Conjecture41CliqueBeachhead.lean#L84) — (no docstring)
- `theorem Round20CliqueKernel.cliqueLocator_eval_self_ne_zero` [ArkLib\Data\CodingTheory\ProximityGap\Conjecture41CliqueKernelStructure.lean:178](../../../ArkLib\Data\CodingTheory\ProximityGap\Conjecture41CliqueKernelStructure.lean#L178) — Locator self-evaluation is nonzero (distinct nodes).
- `theorem Round21Relations.cliqueLocator_eval_self_ne_zero` [ArkLib\Data\CodingTheory\ProximityGap\Conjecture41CliqueRelationModule.lean:86](../../../ArkLib\Data\CodingTheory\ProximityGap\Conjecture41CliqueRelationModule.lean#L86) — Locator self-evaluation is nonzero.

### `coeffVec` (3 declarations, 3 files)

- `def Round19Clique.coeffVec` [ArkLib\Data\CodingTheory\ProximityGap\Conjecture41CliqueBeachhead.lean:121](../../../ArkLib\Data\CodingTheory\ProximityGap\Conjecture41CliqueBeachhead.lean#L121) — The coefficient vector of a polynomial, truncated to `Fin N`.
- `def ArkLib.CodingTheory.Round7GeneralT.coeffVec` [ArkLib\Data\CodingTheory\ProximityGap\ListInteriorUnconditionalGeneralT.lean:188](../../../ArkLib\Data\CodingTheory\ProximityGap\ListInteriorUnconditionalGeneralT.lean#L188) — The **top-`t`-coefficient vector** of the monic root product `∏_{i∈S}(X − D i)` over the index windo
- `def CPoly.CMvPolynomial.degreeLE.coeffVec` [ArkLib\Data\MvPolynomial\ComputableDegreeLE.lean:111](../../../ArkLib\Data\MvPolynomial\ComputableDegreeLE.lean#L111) — Coefficient vector for a bounded-degree computable univariate polynomial.

### `coeff_pow_sub_at` (3 declarations, 3 files)

- `theorem ProximityPrize.HenselExistence.coeff_pow_sub_at` [ArkLib\Data\Polynomial\HenselExistence.lean:89](../../../ArkLib\Data\Polynomial\HenselExistence.lean#L89) — Local copy of `NewtonLinearization.coeff_pow_sub_at` (order-`t` Newton linearization).
- `theorem ProximityPrize.HenselSeriesCoeff.coeff_pow_sub_at` [ArkLib\Data\Polynomial\HenselSeriesCoeff.lean:94](../../../ArkLib\Data\Polynomial\HenselSeriesCoeff.lean#L94) — **LEMMA B (Newton power linearization).** Local copy of `NewtonLinearization.coeff_pow_sub_at`.
- `theorem ProximityPrize.NewtonLinearization.coeff_pow_sub_at` [ArkLib\Data\Polynomial\NewtonLinearization.lean:98](../../../ArkLib\Data\Polynomial\NewtonLinearization.lean#L98) — **Newton linearization at order `t`.** Under the below-`t` agreement hypothesis with `0 < t`, writin

### `coeff_pow_sub_below` (3 declarations, 3 files)

- `theorem ProximityPrize.HenselExistence.coeff_pow_sub_below` [ArkLib\Data\Polynomial\HenselExistence.lean:72](../../../ArkLib\Data\Polynomial\HenselExistence.lean#L72) — Local copy of `NewtonLinearization.coeff_pow_sub_below` (truncation propagation).
- `theorem ProximityPrize.HenselSeriesCoeff.coeff_pow_sub_below` [ArkLib\Data\Polynomial\HenselSeriesCoeff.lean:76](../../../ArkLib\Data\Polynomial\HenselSeriesCoeff.lean#L76) — **LEMMA A (truncation propagation).** Agreement below order `t` propagates to every power. Local cop
- `theorem ProximityPrize.NewtonLinearization.coeff_pow_sub_below` [ArkLib\Data\Polynomial\NewtonLinearization.lean:62](../../../ArkLib\Data\Polynomial\NewtonLinearization.lean#L62) — **Truncation propagation.** If `γ₁ γ₂ : R⟦X⟧` agree at every coefficient `j < t`, then so do `γ₁^i`

### `commit` (3 declarations, 3 files)

- `def ArkLib.Lattices.Ajtai.Simple.commit` [ArkLib\CommitmentScheme\Ajtai\Simple\Scheme.lean:38](../../../ArkLib\CommitmentScheme\Ajtai\Simple\Scheme.lean#L38) — Deterministically commit by multiplying the public matrix by the message vector.
- `def KZG.commit` [ArkLib\CommitmentScheme\KZG\Basic.lean:55](../../../ArkLib\CommitmentScheme\KZG\Basic.lean#L55) — To commit to an `n + 1`-tuple of coefficients `coeffs` (corresponding to a polynomial of maximum deg
- `def SimpleRO.commit` [ArkLib\CommitmentScheme\SimpleRO.lean:43](../../../ArkLib\CommitmentScheme\SimpleRO.lean#L43) — (no docstring)

### `commitmentScheme` (3 declarations, 3 files)

- `def ArkLib.Lattices.Ajtai.InnerOuter.commitmentScheme` [ArkLib\CommitmentScheme\Ajtai\InnerOuter\Scheme.lean:200](../../../ArkLib\CommitmentScheme\Ajtai\InnerOuter\Scheme.lean#L200) — The inner-outer Ajtai commitment as a `CommitmentScheme`, verified with the Hachi/Greyhound weak ver
- `def ArkLib.Lattices.Ajtai.Simple.commitmentScheme` [ArkLib\CommitmentScheme\Ajtai\Simple\Scheme.lean:56](../../../ArkLib\CommitmentScheme\Ajtai\Simple\Scheme.lean#L56) — The simple Ajtai commitment as a `CommitmentScheme`. An opening is accepted only when the message sa
- `def SimpleRO.commitmentScheme` [ArkLib\CommitmentScheme\SimpleRO.lean:83](../../../ArkLib\CommitmentScheme\SimpleRO.lean#L83) — (no docstring)

### `coreInteractionOracleReduction` (3 declarations, 3 files)

- `def coreInteractionOracleReduction` [ArkLib\ProofSystem\Binius\BinaryBasefold\CoreInteractionPhase.lean:1117](../../../ArkLib\ProofSystem\Binius\BinaryBasefold\CoreInteractionPhase.lean#L1117) — (no docstring)
- `def Binius.FRIBinius.CoreInteractionPhase.coreInteractionOracleReduction` [ArkLib\ProofSystem\Binius\FRIBinius\CoreInteractionPhase.lean:1655](../../../ArkLib\ProofSystem\Binius\FRIBinius\CoreInteractionPhase.lean#L1655) — The final oracle reduction that composes sumcheckFold with finalSumcheckStep
- `def RingSwitching.SumcheckPhase.coreInteractionOracleReduction` [ArkLib\ProofSystem\RingSwitching\SumcheckPhase.lean:1807](../../../ArkLib\ProofSystem\RingSwitching\SumcheckPhase.lean#L1807) — Large-field reduction: Sumcheck seqCompose, then append FinalSum

### `coreInteractionOracleVerifier` (3 declarations, 3 files)

- `def coreInteractionOracleVerifier` [ArkLib\ProofSystem\Binius\BinaryBasefold\CoreInteractionPhase.lean:1101](../../../ArkLib\ProofSystem\Binius\BinaryBasefold\CoreInteractionPhase.lean#L1101) — (no docstring)
- `def Binius.FRIBinius.CoreInteractionPhase.coreInteractionOracleVerifier` [ArkLib\ProofSystem\Binius\FRIBinius\CoreInteractionPhase.lean:1636](../../../ArkLib\ProofSystem\Binius\FRIBinius\CoreInteractionPhase.lean#L1636) — The final oracle verifier that composes sumcheckFold with finalSumcheckStep
- `def RingSwitching.SumcheckPhase.coreInteractionOracleVerifier` [ArkLib\ProofSystem\RingSwitching\SumcheckPhase.lean:1771](../../../ArkLib\ProofSystem\RingSwitching\SumcheckPhase.lean#L1771) — Large-field reduction verifier: Sumcheck seqCompose, then append FinalSum

### `coset_card` (3 declarations, 3 files)

- `theorem Code.coset_card` [ArkLib\Data\CodingTheory\Basic\CosetFarCount.lean:31](../../../ArkLib\Data\CodingTheory\Basic\CosetFarCount.lean#L31) — A coset `{w \| w - w₀ ∈ C}` of a linear code `C` has cardinality `\|C\|`.
- `theorem ArkLib.ProximityGap.CosetConcentration.coset_card` [ArkLib\Data\CodingTheory\ProximityGap\CosetPowerSumConcentration.lean:96](../../../ArkLib\Data\CodingTheory\ProximityGap\CosetPowerSumConcentration.lean#L96) — A coset of a primitive `h`-th root, with `g ≠ 0`, has exactly `h` elements.
- `theorem ArkLib.ProximityGap.HybridDepthNoGo.coset_card` [ArkLib\Data\CodingTheory\ProximityGap\HybridConcentrationDepthNoGo.lean:102](../../../ArkLib\Data\CodingTheory\ProximityGap\HybridConcentrationDepthNoGo.lean#L102) — (no docstring)

### `epsMCA_le_one` (3 declarations, 3 files)

- `theorem ProximityGap.epsMCA_le_one` [ArkLib\Data\CodingTheory\ProximityGap\Errors.lean:316](../../../ArkLib\Data\CodingTheory\ProximityGap\Errors.lean#L316) — The MCA error is bounded by the total probability mass.
- `theorem ProximityGap.MCAGS.epsMCA_le_one` [ArkLib\Data\CodingTheory\ProximityGap\GrandChallenge141PrizeMath.lean:92](../../../ArkLib\Data\CodingTheory\ProximityGap\GrandChallenge141PrizeMath.lean#L92) — **The abstract MCA error is a probability ceiling: `ε_mca ≤ 1`.** (Companion to `epsMCAgs_le_one`; t
- `theorem CodingTheory.Bridge.epsMCA_le_one` [ArkLib\ToMathlib\BridgeListDecodingCA.lean:77](../../../ArkLib\ToMathlib\BridgeListDecodingCA.lean#L77) — **`ε_mca ≤ 1`.** The mutual-correlated-agreement error is a supremum of PMF probabilities, hence at

### `fiber` (3 declarations, 3 files)

- `def AveragingCrossover.fiber` [ArkLib\Data\CodingTheory\ProximityGap\AveragingFiberConservation.lean:81](../../../ArkLib\Data\CodingTheory\ProximityGap\AveragingFiberConservation.lean#L81) — The fiber of `Φ` over a target tuple `y`, restricted to `a`-subsets.
- `def ArkLib.ProximityGap.Rigidity.fiber` [ArkLib\Data\CodingTheory\ProximityGap\CosetExactCount.lean:45](../../../ArkLib\Data\CodingTheory\ProximityGap\CosetExactCount.lean#L45) — (no docstring)
- `def ArkLib.ProximityGap.Round5SecondMoment.fiber` [ArkLib\Data\CodingTheory\ProximityGap\SubsetSumPigeonholeManyTargets.lean:96](../../../ArkLib\Data\CodingTheory\ProximityGap\SubsetSumPigeonholeManyTargets.lean#L96) — The `target`-fiber `A_target = { S ∈ powersetCard a G : ∑_{x∈S} x = target }`, whose card is `subset

### `finalSumcheckKStateProp` (3 declarations, 3 files)

- `def Binius.BinaryBasefold.CoreInteraction.finalSumcheckKStateProp` [ArkLib\ProofSystem\Binius\BinaryBasefold\Steps\FinalSumcheck.lean:1668](../../../ArkLib\ProofSystem\Binius\BinaryBasefold\Steps\FinalSumcheck.lean#L1668) — (no docstring)
- `def Binius.FRIBinius.CoreInteractionPhase.finalSumcheckKStateProp` [ArkLib\ProofSystem\Binius\FRIBinius\CoreInteractionPhase.lean:1357](../../../ArkLib\ProofSystem\Binius\FRIBinius\CoreInteractionPhase.lean#L1357) — (no docstring)
- `def RingSwitching.SumcheckPhase.finalSumcheckKStateProp` [ArkLib\ProofSystem\RingSwitching\SumcheckPhase.lean:1535](../../../ArkLib\ProofSystem\RingSwitching\SumcheckPhase.lean#L1535) — (no docstring)

### `finalSumcheckKnowledgeStateFunction` (3 declarations, 3 files)

- `def Binius.BinaryBasefold.CoreInteraction.finalSumcheckKnowledgeStateFunction` [ArkLib\ProofSystem\Binius\BinaryBasefold\Steps\FinalSumcheck.lean:1698](../../../ArkLib\ProofSystem\Binius\BinaryBasefold\Steps\FinalSumcheck.lean#L1698) — (no docstring)
- `def Binius.FRIBinius.CoreInteractionPhase.finalSumcheckKnowledgeStateFunction` [ArkLib\ProofSystem\Binius\FRIBinius\CoreInteractionPhase.lean:1397](../../../ArkLib\ProofSystem\Binius\FRIBinius\CoreInteractionPhase.lean#L1397) — The knowledge state function for the final sumcheck step
- `def RingSwitching.SumcheckPhase.finalSumcheckKnowledgeStateFunction` [ArkLib\ProofSystem\RingSwitching\SumcheckPhase.lean:1573](../../../ArkLib\ProofSystem\RingSwitching\SumcheckPhase.lean#L1573) — The knowledge state function for the final sumcheck step

### `finalSumcheckOracleReduction` (3 declarations, 3 files)

- `def Binius.BinaryBasefold.CoreInteraction.finalSumcheckOracleReduction` [ArkLib\ProofSystem\Binius\BinaryBasefold\Steps\FinalSumcheck.lean:126](../../../ArkLib\ProofSystem\Binius\BinaryBasefold\Steps\FinalSumcheck.lean#L126) — (no docstring)
- `def Binius.FRIBinius.CoreInteractionPhase.finalSumcheckOracleReduction` [ArkLib\ProofSystem\Binius\FRIBinius\CoreInteractionPhase.lean:667](../../../ArkLib\ProofSystem\Binius\FRIBinius\CoreInteractionPhase.lean#L667) — The oracle reduction for the final sumcheck step
- `def RingSwitching.SumcheckPhase.finalSumcheckOracleReduction` [ArkLib\ProofSystem\RingSwitching\SumcheckPhase.lean:1306](../../../ArkLib\ProofSystem\RingSwitching\SumcheckPhase.lean#L1306) — The oracle reduction for the final sumcheck step

### `finalSumcheckOracleReduction_perfectCompleteness` (3 declarations, 3 files)

- `theorem Binius.BinaryBasefold.CoreInteraction.finalSumcheckOracleReduction_perfectCompleteness` [ArkLib\ProofSystem\Binius\BinaryBasefold\Steps\FinalSumcheck.lean:141](../../../ArkLib\ProofSystem\Binius\BinaryBasefold\Steps\FinalSumcheck.lean#L141) — (no docstring)
- `theorem Binius.FRIBinius.CoreInteractionPhase.finalSumcheckOracleReduction_perfectCompleteness` [ArkLib\ProofSystem\Binius\FRIBinius\CoreInteractionPhase.lean:1128](../../../ArkLib\ProofSystem\Binius\FRIBinius\CoreInteractionPhase.lean#L1128) — Perfect completeness for the final sumcheck step
- `theorem RingSwitching.SumcheckPhase.finalSumcheckOracleReduction_perfectCompleteness` [ArkLib\ProofSystem\RingSwitching\SumcheckPhase.lean:1449](../../../ArkLib\ProofSystem\RingSwitching\SumcheckPhase.lean#L1449) — **Final-sumcheck perfect completeness — proven.** The single-message final sumcheck reduction is per

### `finalSumcheckOracleVerifier_rbrKnowledgeSoundness` (3 declarations, 3 files)

- `theorem Binius.BinaryBasefold.CoreInteraction.finalSumcheckOracleVerifier_rbrKnowledgeSoundness` [ArkLib\ProofSystem\Binius\BinaryBasefold\Steps\FinalSumcheck.lean:1892](../../../ArkLib\ProofSystem\Binius\BinaryBasefold\Steps\FinalSumcheck.lean#L1892) — (no docstring)
- `theorem Binius.FRIBinius.CoreInteractionPhase.finalSumcheckOracleVerifier_rbrKnowledgeSoundness` [ArkLib\ProofSystem\Binius\FRIBinius\CoreInteractionPhase.lean:1609](../../../ArkLib\ProofSystem\Binius\FRIBinius\CoreInteractionPhase.lean#L1609) — Round-by-round knowledge soundness for the final sumcheck step
- `theorem RingSwitching.SumcheckPhase.finalSumcheckOracleVerifier_rbrKnowledgeSoundness` [ArkLib\ProofSystem\RingSwitching\SumcheckPhase.lean:1704](../../../ArkLib\ProofSystem\RingSwitching\SumcheckPhase.lean#L1704) — Round-by-round knowledge soundness for the final sumcheck step

### `finalSumcheckProver` (3 declarations, 3 files)

- `def Binius.BinaryBasefold.CoreInteraction.finalSumcheckProver` [ArkLib\ProofSystem\Binius\BinaryBasefold\Steps\FinalSumcheck.lean:66](../../../ArkLib\ProofSystem\Binius\BinaryBasefold\Steps\FinalSumcheck.lean#L66) — (no docstring)
- `def Binius.FRIBinius.CoreInteractionPhase.finalSumcheckProver` [ArkLib\ProofSystem\Binius\FRIBinius\CoreInteractionPhase.lean:609](../../../ArkLib\ProofSystem\Binius\FRIBinius\CoreInteractionPhase.lean#L609) — The prover for the final sumcheck step
- `def RingSwitching.SumcheckPhase.finalSumcheckProver` [ArkLib\ProofSystem\RingSwitching\SumcheckPhase.lean:1209](../../../ArkLib\ProofSystem\RingSwitching\SumcheckPhase.lean#L1209) — The prover for the final sumcheck step

### `finalSumcheckRbrExtractor` (3 declarations, 3 files)

- `def Binius.BinaryBasefold.CoreInteraction.finalSumcheckRbrExtractor` [ArkLib\ProofSystem\Binius\BinaryBasefold\Steps\FinalSumcheck.lean:1626](../../../ArkLib\ProofSystem\Binius\BinaryBasefold\Steps\FinalSumcheck.lean#L1626) — (no docstring)
- `def Binius.FRIBinius.CoreInteractionPhase.finalSumcheckRbrExtractor` [ArkLib\ProofSystem\Binius\FRIBinius\CoreInteractionPhase.lean:1319](../../../ArkLib\ProofSystem\Binius\FRIBinius\CoreInteractionPhase.lean#L1319) — The round-by-round extractor for the final sumcheck step
- `def RingSwitching.SumcheckPhase.finalSumcheckRbrExtractor` [ArkLib\ProofSystem\RingSwitching\SumcheckPhase.lean:1515](../../../ArkLib\ProofSystem\RingSwitching\SumcheckPhase.lean#L1515) — The round-by-round extractor for the final sumcheck step

### `finalSumcheckVerifier` (3 declarations, 3 files)

- `def Binius.BinaryBasefold.CoreInteraction.finalSumcheckVerifier` [ArkLib\ProofSystem\Binius\BinaryBasefold\Steps\FinalSumcheck.lean:100](../../../ArkLib\ProofSystem\Binius\BinaryBasefold\Steps\FinalSumcheck.lean#L100) — (no docstring)
- `def Binius.FRIBinius.CoreInteractionPhase.finalSumcheckVerifier` [ArkLib\ProofSystem\Binius\FRIBinius\CoreInteractionPhase.lean:643](../../../ArkLib\ProofSystem\Binius\FRIBinius\CoreInteractionPhase.lean#L643) — The verifier for the final sumcheck step
- `def RingSwitching.SumcheckPhase.finalSumcheckVerifier` [ArkLib\ProofSystem\RingSwitching\SumcheckPhase.lean:1245](../../../ArkLib\ProofSystem\RingSwitching\SumcheckPhase.lean#L1245) — The verifier for the final sumcheck step

### `foldOracleReduction` (3 declarations, 3 files)

- `def Binius.BinaryBasefold.CoreInteraction.foldOracleReduction` [ArkLib\ProofSystem\Binius\BinaryBasefold\Steps\Fold.lean:114](../../../ArkLib\ProofSystem\Binius\BinaryBasefold\Steps\Fold.lean#L114) — (no docstring)
- `def Fri.Spec.FoldPhase.foldOracleReduction` [ArkLib\ProofSystem\Fri\Spec\SingleRound.lean:518](../../../ArkLib\ProofSystem\Fri\Spec\SingleRound.lean#L518) — The oracle reduction that is the `i`-th round of the FRI protocol.
- `def WhirIOP.FoldRound.foldOracleReduction` [ArkLib\ProofSystem\Whir\FoldRound.lean:201](../../../ArkLib\ProofSystem\Whir\FoldRound.lean#L201) — The honest WHIR fold round as an oracle reduction.

### `fullOracleProof` (3 declarations, 3 files)

- `def Binius.BinaryBasefold.FullBinaryBasefold.fullOracleProof` [ArkLib\ProofSystem\Binius\BinaryBasefold\General.lean:102](../../../ArkLib\ProofSystem\Binius\BinaryBasefold\General.lean#L102) — The full Binary Basefold protocol as a Proof
- `def Binius.FRIBinius.FullFRIBinius.fullOracleProof` [ArkLib\ProofSystem\Binius\FRIBinius\General.lean:171](../../../ArkLib\ProofSystem\Binius\FRIBinius\General.lean#L171) — The full Binary Basefold protocol as a Proof
- `def RingSwitching.FullRingSwitching.fullOracleProof` [ArkLib\ProofSystem\RingSwitching\General.lean:96](../../../ArkLib\ProofSystem\RingSwitching\General.lean#L96) — The full Binary Basefold protocol as a Proof

### `fullOracleReduction` (3 declarations, 3 files)

- `def Binius.BinaryBasefold.FullBinaryBasefold.fullOracleReduction` [ArkLib\ProofSystem\Binius\BinaryBasefold\General.lean:74](../../../ArkLib\ProofSystem\Binius\BinaryBasefold\General.lean#L74) — The reduction for the full Binary Basefold protocol
- `def Binius.FRIBinius.FullFRIBinius.fullOracleReduction` [ArkLib\ProofSystem\Binius\FRIBinius\General.lean:140](../../../ArkLib\ProofSystem\Binius\FRIBinius\General.lean#L140) — The reduction for the full Binary Basefold protocol
- `def RingSwitching.FullRingSwitching.fullOracleReduction` [ArkLib\ProofSystem\RingSwitching\General.lean:84](../../../ArkLib\ProofSystem\RingSwitching\General.lean#L84) — The reduction for the full Binary Basefold protocol

### `fullOracleReduction_perfectCompleteness` (3 declarations, 3 files)

- `theorem Binius.BinaryBasefold.FullBinaryBasefold.fullOracleReduction_perfectCompleteness` [ArkLib\ProofSystem\Binius\BinaryBasefold\General.lean:117](../../../ArkLib\ProofSystem\Binius\BinaryBasefold\General.lean#L117) — Perfect completeness for the full Binary Basefold protocol (reduction)
- `theorem Binius.FRIBinius.FullFRIBinius.fullOracleReduction_perfectCompleteness` [ArkLib\ProofSystem\Binius\FRIBinius\General.lean:191](../../../ArkLib\ProofSystem\Binius\FRIBinius\General.lean#L191) — Perfect completeness for the full Binary Basefold protocol (reduction)
- `theorem RingSwitching.FullRingSwitching.fullOracleReduction_perfectCompleteness` [ArkLib\ProofSystem\RingSwitching\General.lean:171](../../../ArkLib\ProofSystem\RingSwitching\General.lean#L171) — Perfect completeness for the full ring-switching reduction, conditional on the explicit phase-level

### `fullOracleVerifier` (3 declarations, 3 files)

- `def Binius.BinaryBasefold.FullBinaryBasefold.fullOracleVerifier` [ArkLib\ProofSystem\Binius\BinaryBasefold\General.lean:51](../../../ArkLib\ProofSystem\Binius\BinaryBasefold\General.lean#L51) — The oracle verifier for the full Binary Basefold protocol
- `def Binius.FRIBinius.FullFRIBinius.fullOracleVerifier` [ArkLib\ProofSystem\Binius\FRIBinius\General.lean:114](../../../ArkLib\ProofSystem\Binius\FRIBinius\General.lean#L114) — The oracle verifier for the full Binary Basefold protocol
- `def RingSwitching.FullRingSwitching.fullOracleVerifier` [ArkLib\ProofSystem\RingSwitching\General.lean:60](../../../ArkLib\ProofSystem\RingSwitching\General.lean#L60) — The oracle verifier for the full Binary Basefold protocol

### `fullOracleVerifier_rbrKnowledgeSoundness` (3 declarations, 3 files)

- `theorem Binius.BinaryBasefold.FullBinaryBasefold.fullOracleVerifier_rbrKnowledgeSoundness` [ArkLib\ProofSystem\Binius\BinaryBasefold\General.lean:149](../../../ArkLib\ProofSystem\Binius\BinaryBasefold\General.lean#L149) — Round-by-round knowledge soundness for the full Binary Basefold oracle verifier
- `theorem Binius.FRIBinius.FullFRIBinius.fullOracleVerifier_rbrKnowledgeSoundness` [ArkLib\ProofSystem\Binius\FRIBinius\General.lean:237](../../../ArkLib\ProofSystem\Binius\FRIBinius\General.lean#L237) — Round-by-round knowledge soundness for the full FRI-Binius oracle verifier.
- `theorem RingSwitching.FullRingSwitching.fullOracleVerifier_rbrKnowledgeSoundness` [ArkLib\ProofSystem\RingSwitching\General.lean:247](../../../ArkLib\ProofSystem\RingSwitching\General.lean#L247) — Round-by-round knowledge soundness for the full ring-switching oracle verifier. `IsDomain K` (with t

### `fullRbrKnowledgeError` (3 declarations, 3 files)

- `def Binius.BinaryBasefold.FullBinaryBasefold.fullRbrKnowledgeError` [ArkLib\ProofSystem\Binius\BinaryBasefold\General.lean:139](../../../ArkLib\ProofSystem\Binius\BinaryBasefold\General.lean#L139) — Combined RBR knowledge soundness error for the full protocol
- `def Binius.FRIBinius.FullFRIBinius.fullRbrKnowledgeError` [ArkLib\ProofSystem\Binius\FRIBinius\General.lean:227](../../../ArkLib\ProofSystem\Binius\FRIBinius\General.lean#L227) — Combined RBR knowledge error for full FRI-Binius.
- `def RingSwitching.FullRingSwitching.fullRbrKnowledgeError` [ArkLib\ProofSystem\RingSwitching\General.lean:231](../../../ArkLib\ProofSystem\RingSwitching\General.lean#L231) — (no docstring)

### `hammingBall` (3 declarations, 3 files)

- `def ListDecodable.hammingBall` [ArkLib\Data\CodingTheory\ListDecodability.lean:27](../../../ArkLib\Data\CodingTheory\ListDecodability.lean#L27) — Hamming ball of radius `r` centred at a word `y`.
- `def Round13bSecondMoment.hammingBall` [ArkLib\Data\CodingTheory\ProximityGap\BallIntersectionSecondMomentLinear.lean:27](../../../ArkLib\Data\CodingTheory\ProximityGap\BallIntersectionSecondMomentLinear.lean#L27) — The Hamming ball of radius `r` around `c`.
- `def ArkLib.CodingTheory.Round13BallInter.hammingBall` [ArkLib\Data\CodingTheory\ProximityGap\ListAroundBallIntersectionKernel.lean:77](../../../ArkLib\Data\CodingTheory\ProximityGap\ListAroundBallIntersectionKernel.lean#L77) — The Hamming ball of radius `r` around `c`, as a finset of all words (the ambient `Fin n → F` is fini

### `honestTranscriptDist_reduction_evalDist` (3 declarations, 3 files)

- `theorem CheckClaim.honestTranscriptDist_reduction_evalDist` [ArkLib\ProofSystem\Component\CheckClaim.lean:121](../../../ArkLib\ProofSystem\Component\CheckClaim.lean#L121) — The honest transcript distribution for a valid `CheckClaim` statement is the deterministic empty tra
- `theorem ReduceClaim.honestTranscriptDist_reduction_evalDist` [ArkLib\ProofSystem\Component\ReduceClaim.lean:116](../../../ArkLib\ProofSystem\Component\ReduceClaim.lean#L116) — The honest transcript distribution for `ReduceClaim` is the deterministic empty transcript. The mapp
- `theorem SendWitness.honestTranscriptDist_reduction_evalDist` [ArkLib\ProofSystem\Component\SendWitness.lean:109](../../../ArkLib\ProofSystem\Component\SendWitness.lean#L109) — The honest transcript distribution for `SendWitness` is the deterministic one-message transcript con

### `hypotheses_satisfiable_zmod13` (3 declarations, 3 files)

- `theorem ArkLib.ProximityGap.Round8CompleteSquare.hypotheses_satisfiable_zmod13` [ArkLib\Data\CodingTheory\ProximityGap\MixedGaussSumCompleteSquare.lean:223](../../../ArkLib\Data\CodingTheory\ProximityGap\MixedGaussSumCompleteSquare.lean#L223) — **Non-vacuity (concrete odd-characteristic field with a primitive additive character).** `F = ZMod 1
- `theorem ArkLib.ProximityGap.Round8MixedGauss.hypotheses_satisfiable_zmod13` [ArkLib\Data\CodingTheory\ProximityGap\MixedGaussSumDiagonal.lean:221](../../../ArkLib\Data\CodingTheory\ProximityGap\MixedGaussSumDiagonal.lean#L221) — **Non-vacuity: a concrete odd-characteristic field with a primitive additive character.** `F = ZMod
- `theorem ArkLib.ProximityGap.Round7QuadraticGauss.hypotheses_satisfiable_zmod13` [ArkLib\Data\CodingTheory\ProximityGap\QuadraticGaussSumMagnitude.lean:279](../../../ArkLib\Data\CodingTheory\ProximityGap\QuadraticGaussSumMagnitude.lean#L279) — **Non-vacuity: a concrete odd-characteristic field with a primitive additive character.** `F = ZMod

### `knowledgeStateFunction` (3 declarations, 3 files)

- `def CheckClaim.knowledgeStateFunction` [ArkLib\ProofSystem\Component\CheckClaim.lean:174](../../../ArkLib\ProofSystem\Component\CheckClaim.lean#L174) — The knowledge state function for the `CheckClaim` reduction. Since there is no challenge round, the
- `def RandomQuery.knowledgeStateFunction` [ArkLib\ProofSystem\Component\RandomQuery.lean:306](../../../ArkLib\ProofSystem\Component\RandomQuery.lean#L306) — The knowledge state function for the `RandomQuery` oracle reduction.
- `def ReduceClaim.knowledgeStateFunction` [ArkLib\ProofSystem\Component\ReduceClaim.lean:192](../../../ArkLib\ProofSystem\Component\ReduceClaim.lean#L192) — The knowledge state function for the `ReduceClaim` reduction.

### `linearIndependent_pow_le` (3 declarations, 3 files)

- `theorem R12J.linearIndependent_pow_le` [ArkLib\Data\CodingTheory\ProximityGap\JointT2Unconditional.lean:93](../../../ArkLib\Data\CodingTheory\ProximityGap\JointT2Unconditional.lean#L93) — UNCONDITIONAL: over a field `K`, the first `N` powers of `ζ` are `K`-linearly independent whenever `
- `theorem R12.linearIndependent_pow_le` [ArkLib\Data\CodingTheory\ProximityGap\LamLeungUnconditionalGeneral.lean:62](../../../ArkLib\Data\CodingTheory\ProximityGap\LamLeungUnconditionalGeneral.lean#L62) — UNCONDITIONAL: over a field `K`, the first `N` powers of `ζ` are `K`-linearly independent whenever `
- `theorem R11.linearIndependent_pow_le` [ArkLib\Data\CodingTheory\ProximityGap\LamLeungUnconditionalQ.lean:54](../../../ArkLib\Data\CodingTheory\ProximityGap\LamLeungUnconditionalQ.lean#L54) — UNCONDITIONAL: over a field `K`, the first `N` powers of `ζ` are `K`-linearly independent whenever `

### `loc` (3 declarations, 3 files)

- `def C2CoreBound.loc` [ArkLib\Data\CodingTheory\ProximityGap\C2CoreEliminationBound.lean:62](../../../ArkLib\Data\CodingTheory\ProximityGap\C2CoreEliminationBound.lean#L62) — The error-locator polynomial of a support `E ⊆ F`.
- `def NormalRank.loc` [ArkLib\Data\CodingTheory\ProximityGap\NormalRankSharpThreshold.lean:52](../../../ArkLib\Data\CodingTheory\ProximityGap\NormalRankSharpThreshold.lean#L52) — The error-locator polynomial of a support `E ⊆ F` (also in `C2CoreBound.loc`; duplicated here to kee
- `def TopLine.loc` [ArkLib\Data\CodingTheory\ProximityGap\TopDirectionLineCount.lean:55](../../../ArkLib\Data\CodingTheory\ProximityGap\TopDirectionLineCount.lean#L55) — The error-locator polynomial of a support.

### `oracleReduction_completeness` (3 declarations, 3 files)

- `theorem RandomQuery.oracleReduction_completeness` [ArkLib\ProofSystem\Component\RandomQuery.lean:130](../../../ArkLib\ProofSystem\Component\RandomQuery.lean#L130) — The `RandomQuery` oracle reduction is perfectly complete.
- `theorem ReduceClaim.oracleReduction_completeness` [ArkLib\ProofSystem\Component\ReduceClaim.lean:293](../../../ArkLib\ProofSystem\Component\ReduceClaim.lean#L293) — The `ReduceClaim` oracle reduction satisfies perfect completeness for any relation. Proof strategy m
- `theorem SendSingleWitness.oracleReduction_completeness` [ArkLib\ProofSystem\Component\SendWitness.lean:514](../../../ArkLib\ProofSystem\Component\SendWitness.lean#L514) — The `SendSingleWitness` oracle reduction satisfies perfect completeness.

### `p0_deg` (3 declarations, 3 files)

- `lemma ArkLib.CodingTheory.TinyInteriorPin.p0_deg` [ArkLib\Data\CodingTheory\ProximityGap\ListInteriorDataPointF7.lean:118](../../../ArkLib\Data\CodingTheory\ProximityGap\ListInteriorDataPointF7.lean#L118) — (no docstring)
- `lemma ArkLib.CodingTheory.TinyInteriorK3.p0_deg` [ArkLib\Data\CodingTheory\ProximityGap\ListInteriorPinF11K3.lean:142](../../../ArkLib\Data\CodingTheory\ProximityGap\ListInteriorPinF11K3.lean#L142) — (no docstring)
- `lemma ArkLib.CodingTheory.Round3SmoothF17.p0_deg` [ArkLib\Data\CodingTheory\ProximityGap\ListInteriorPinF17Subgroup.lean:152](../../../ArkLib\Data\CodingTheory\ProximityGap\ListInteriorPinF17Subgroup.lean#L152) — (no docstring)

### `p1_deg` (3 declarations, 3 files)

- `lemma ArkLib.CodingTheory.TinyInteriorPin.p1_deg` [ArkLib\Data\CodingTheory\ProximityGap\ListInteriorDataPointF7.lean:119](../../../ArkLib\Data\CodingTheory\ProximityGap\ListInteriorDataPointF7.lean#L119) — (no docstring)
- `lemma ArkLib.CodingTheory.TinyInteriorK3.p1_deg` [ArkLib\Data\CodingTheory\ProximityGap\ListInteriorPinF11K3.lean:143](../../../ArkLib\Data\CodingTheory\ProximityGap\ListInteriorPinF11K3.lean#L143) — (no docstring)
- `lemma ArkLib.CodingTheory.Round3SmoothF17.p1_deg` [ArkLib\Data\CodingTheory\ProximityGap\ListInteriorPinF17Subgroup.lean:153](../../../ArkLib\Data\CodingTheory\ProximityGap\ListInteriorPinF17Subgroup.lean#L153) — (no docstring)

### `p2_deg` (3 declarations, 3 files)

- `lemma ArkLib.CodingTheory.TinyInteriorPin.p2_deg` [ArkLib\Data\CodingTheory\ProximityGap\ListInteriorDataPointF7.lean:120](../../../ArkLib\Data\CodingTheory\ProximityGap\ListInteriorDataPointF7.lean#L120) — (no docstring)
- `lemma ArkLib.CodingTheory.TinyInteriorK3.p2_deg` [ArkLib\Data\CodingTheory\ProximityGap\ListInteriorPinF11K3.lean:144](../../../ArkLib\Data\CodingTheory\ProximityGap\ListInteriorPinF11K3.lean#L144) — (no docstring)
- `lemma ArkLib.CodingTheory.Round3SmoothF17.p2_deg` [ArkLib\Data\CodingTheory\ProximityGap\ListInteriorPinF17Subgroup.lean:154](../../../ArkLib\Data\CodingTheory\ProximityGap\ListInteriorPinF17Subgroup.lean#L154) — (no docstring)

### `p3_deg` (3 declarations, 3 files)

- `lemma ArkLib.CodingTheory.TinyInteriorPin.p3_deg` [ArkLib\Data\CodingTheory\ProximityGap\ListInteriorDataPointF7.lean:121](../../../ArkLib\Data\CodingTheory\ProximityGap\ListInteriorDataPointF7.lean#L121) — (no docstring)
- `lemma ArkLib.CodingTheory.TinyInteriorK3.p3_deg` [ArkLib\Data\CodingTheory\ProximityGap\ListInteriorPinF11K3.lean:145](../../../ArkLib\Data\CodingTheory\ProximityGap\ListInteriorPinF11K3.lean#L145) — (no docstring)
- `lemma ArkLib.CodingTheory.Round3SmoothF17.p3_deg` [ArkLib\Data\CodingTheory\ProximityGap\ListInteriorPinF17Subgroup.lean:155](../../../ArkLib\Data\CodingTheory\ProximityGap\ListInteriorPinF17Subgroup.lean#L155) — (no docstring)

### `p4_deg` (3 declarations, 3 files)

- `lemma ArkLib.CodingTheory.TinyInteriorPin.p4_deg` [ArkLib\Data\CodingTheory\ProximityGap\ListInteriorDataPointF7.lean:122](../../../ArkLib\Data\CodingTheory\ProximityGap\ListInteriorDataPointF7.lean#L122) — (no docstring)
- `lemma ArkLib.CodingTheory.TinyInteriorK3.p4_deg` [ArkLib\Data\CodingTheory\ProximityGap\ListInteriorPinF11K3.lean:146](../../../ArkLib\Data\CodingTheory\ProximityGap\ListInteriorPinF11K3.lean#L146) — (no docstring)
- `lemma ArkLib.CodingTheory.Round3SmoothF17.p4_deg` [ArkLib\Data\CodingTheory\ProximityGap\ListInteriorPinF17Subgroup.lean:156](../../../ArkLib\Data\CodingTheory\ProximityGap\ListInteriorPinF17Subgroup.lean#L156) — (no docstring)

### `p5_deg` (3 declarations, 3 files)

- `lemma ArkLib.CodingTheory.TinyInteriorPin.p5_deg` [ArkLib\Data\CodingTheory\ProximityGap\ListInteriorDataPointF7.lean:123](../../../ArkLib\Data\CodingTheory\ProximityGap\ListInteriorDataPointF7.lean#L123) — (no docstring)
- `lemma ArkLib.CodingTheory.TinyInteriorK3.p5_deg` [ArkLib\Data\CodingTheory\ProximityGap\ListInteriorPinF11K3.lean:147](../../../ArkLib\Data\CodingTheory\ProximityGap\ListInteriorPinF11K3.lean#L147) — (no docstring)
- `lemma ArkLib.CodingTheory.Round3SmoothF17.p5_deg` [ArkLib\Data\CodingTheory\ProximityGap\ListInteriorPinF17Subgroup.lean:157](../../../ArkLib\Data\CodingTheory\ProximityGap\ListInteriorPinF17Subgroup.lean#L157) — (no docstring)

### `phi` (3 declarations, 3 files)

- `def CodingTheory.Bounds.phi` [ArkLib\Data\CodingTheory\ListDecoding\Bounds\GuruswamiSudanListSize.lean:48](../../../ArkLib\Data\CodingTheory\ListDecoding\Bounds\GuruswamiSudanListSize.lean#L48) — Explicit `F`-algebra retraction of `psi`, sending `Y ↦ X₁` and coefficients `g(X) ↦ g(X₀)`.
- `def ArkLib.CodingTheory.JohnsonSimplex.phi` [ArkLib\Data\CodingTheory\ProximityGap\JohnsonSimplexBound.lean:42](../../../ArkLib\Data\CodingTheory\ProximityGap\JohnsonSimplexBound.lean#L42) — The q-ary simplex embedding: `φ(x)(i,c) = 1` if `x i = c`, else `0`.
- `def Logup.phi` [ArkLib\ProofSystem\Logup\Common.lean:685](../../../ArkLib\ProofSystem\Logup\Common.lean#L685) — The denominator term `φᵢ(u)` from Protocol 2.

### `reduction_isHVZK` (3 declarations, 3 files)

- `theorem CheckClaim.reduction_isHVZK` [ArkLib\ProofSystem\Component\CheckClaim.lean:156](../../../ArkLib\ProofSystem\Component\CheckClaim.lean#L156) — `CheckClaim` has an explicit perfect-HVZK simulator.
- `theorem DoNothing.reduction_isHVZK` [ArkLib\ProofSystem\Component\DoNothing.lean:79](../../../ArkLib\ProofSystem\Component\DoNothing.lean#L79) — The `DoNothing` reduction has an explicit perfect-HVZK simulator for any relation.
- `theorem ReduceClaim.reduction_isHVZK` [ArkLib\ProofSystem\Component\ReduceClaim.lean:153](../../../ArkLib\ProofSystem\Component\ReduceClaim.lean#L153) — `ReduceClaim` has an explicit perfect-HVZK simulator for any input relation.

### `reduction_isStatHVZK` (3 declarations, 3 files)

- `theorem CheckClaim.reduction_isStatHVZK` [ArkLib\ProofSystem\Component\CheckClaim.lean:161](../../../ArkLib\ProofSystem\Component\CheckClaim.lean#L161) — `CheckClaim` has statistical HVZK at every error budget.
- `theorem DoNothing.reduction_isStatHVZK` [ArkLib\ProofSystem\Component\DoNothing.lean:85](../../../ArkLib\ProofSystem\Component\DoNothing.lean#L85) — The `DoNothing` reduction has statistical HVZK for any relation and error budget.
- `theorem ReduceClaim.reduction_isStatHVZK` [ArkLib\ProofSystem\Component\ReduceClaim.lean:159](../../../ArkLib\ProofSystem\Component\ReduceClaim.lean#L159) — `ReduceClaim` has statistical HVZK for any input relation and error budget.

### `reduction_perfectHVZK` (3 declarations, 3 files)

- `theorem CheckClaim.reduction_perfectHVZK` [ArkLib\ProofSystem\Component\CheckClaim.lean:142](../../../ArkLib\ProofSystem\Component\CheckClaim.lean#L142) — `CheckClaim` is perfectly HVZK for the predicate relation. The simulator is the identity transcript
- `theorem DoNothing.reduction_perfectHVZK` [ArkLib\ProofSystem\Component\DoNothing.lean:64](../../../ArkLib\ProofSystem\Component\DoNothing.lean#L64) — The `DoNothing` reduction is perfectly HVZK for any relation.
- `theorem ReduceClaim.reduction_perfectHVZK` [ArkLib\ProofSystem\Component\ReduceClaim.lean:138](../../../ArkLib\ProofSystem\Component\ReduceClaim.lean#L138) — `ReduceClaim` is perfectly HVZK for any input relation: it has no messages or challenges, so the ide

### `reduction_statisticalHVZK` (3 declarations, 3 files)

- `theorem CheckClaim.reduction_statisticalHVZK` [ArkLib\ProofSystem\Component\CheckClaim.lean:150](../../../ArkLib\ProofSystem\Component\CheckClaim.lean#L150) — Perfect HVZK implies statistical HVZK at every error budget.
- `theorem DoNothing.reduction_statisticalHVZK` [ArkLib\ProofSystem\Component\DoNothing.lean:71](../../../ArkLib\ProofSystem\Component\DoNothing.lean#L71) — The `DoNothing` reduction is statistically HVZK for any relation and error budget.
- `theorem ReduceClaim.reduction_statisticalHVZK` [ArkLib\ProofSystem\Component\ReduceClaim.lean:146](../../../ArkLib\ProofSystem\Component\ReduceClaim.lean#L146) — Perfect HVZK implies statistical HVZK for `ReduceClaim` at every error budget.

### `relOut` (3 declarations, 3 files)

- `def CheckClaim.relOut` [ArkLib\ProofSystem\Component\CheckClaim.lean:64](../../../ArkLib\ProofSystem\Component\CheckClaim.lean#L64) — (no docstring)
- `def RandomQuery.relOut` [ArkLib\ProofSystem\Component\RandomQuery.lean:52](../../../ArkLib\ProofSystem\Component\RandomQuery.lean#L52) — The output relation states that if the verifier's single query was `q`, then `a` and `b` agree on th
- `def SendClaim.relOut` [ArkLib\ProofSystem\Component\SendClaim.lean:102](../../../ArkLib\ProofSystem\Component\SendClaim.lean#L102) — (no docstring)

### `rename_finCongr_heq` (3 declarations, 3 files)

- `lemma RingSwitching.SumcheckPhase.rename_finCongr_heq` [ArkLib\ProofSystem\RingSwitching\SumcheckPhase.lean:316](../../../ArkLib\ProofSystem\RingSwitching\SumcheckPhase.lean#L316) — Renaming a polynomial along the canonical index `finCongr` of a (propositional) dimension equality `
- `lemma Sumcheck.Structured.rename_finCongr_heq` [ArkLib\ProofSystem\Sumcheck\Structured\SingleRound.lean:140](../../../ArkLib\ProofSystem\Sumcheck\Structured\SingleRound.lean#L140) — Renaming a polynomial along the canonical index `finCongr` of a dimension equality is heterogeneousl
- `theorem MvPolynomial.rename_finCongr_heq` [ArkLib\ToMathlib\ExtractedIssueBricks.lean:46](../../../ArkLib\ToMathlib\ExtractedIssueBricks.lean#L46) — Renaming along the canonical `finCongr` of a dimension equality is heterogeneously equal to the orig

### `root` (3 declarations, 3 files)

- `def R12J.root` [ArkLib\Data\CodingTheory\ProximityGap\JointT2Unconditional.lean:107](../../../ArkLib\Data\CodingTheory\ProximityGap\JointT2Unconditional.lean#L107) — Value of the root indexed by `(j,b)` under the antipodal pairing: `root g (j,false) = g^j`, `root g
- `def R12.root` [ArkLib\Data\CodingTheory\ProximityGap\LamLeungUnconditionalGeneral.lean:80](../../../ArkLib\Data\CodingTheory\ProximityGap\LamLeungUnconditionalGeneral.lean#L80) — The value of the root indexed by `(j,b)`: `root(j,false) = ζ^j`, `root(j,true) = -ζ^j`.
- `def R11.root` [ArkLib\Data\CodingTheory\ProximityGap\LamLeungUnconditionalQ.lean:77](../../../ArkLib\Data\CodingTheory\ProximityGap\LamLeungUnconditionalQ.lean#L77) — The complex value of the root indexed by `(j,b)` under the antipodal pairing `root(j,false) = ζ^j`,

### `root_true_eq` (3 declarations, 3 files)

- `theorem R12J.root_true_eq` [ArkLib\Data\CodingTheory\ProximityGap\JointT2Unconditional.lean:111](../../../ArkLib\Data\CodingTheory\ProximityGap\JointT2Unconditional.lean#L111) — The `(j,true)` root is the genuine `(j+N)`-th power of `g` when `g^N=-1`.
- `theorem R12.root_true_eq` [ArkLib\Data\CodingTheory\ProximityGap\LamLeungUnconditionalGeneral.lean:86](../../../ArkLib\Data\CodingTheory\ProximityGap\LamLeungUnconditionalGeneral.lean#L86) — For a 2N-th root of unity with `ζ^N = -1`, the `(j,true)` root is the genuine `(j+N)`-th power of `ζ
- `theorem R11.root_true_eq` [ArkLib\Data\CodingTheory\ProximityGap\LamLeungUnconditionalQ.lean:82](../../../ArkLib\Data\CodingTheory\ProximityGap\LamLeungUnconditionalQ.lean#L82) — For a 2N-th root of unity with `ζ^N = -1`, the `(j,true)` root really is the `(j+N)`-th genuine powe

### `simulateQ_simOracle2_messageQuery` (3 declarations, 3 files)

- `lemma RingSwitching.BatchingPhase.simulateQ_simOracle2_messageQuery` [ArkLib\ProofSystem\RingSwitching\BatchingPhase.lean:71](../../../ArkLib\ProofSystem\RingSwitching\BatchingPhase.lean#L71) — Local message-query collapse for `OracleInterface.simOracle2`.
- `lemma RingSwitching.simulateQ_simOracle2_messageQuery` [ArkLib\ProofSystem\RingSwitching\Prelude.lean:1476](../../../ArkLib\ProofSystem\RingSwitching\Prelude.lean#L1476) — **`simOracle2` message-query collapse (`OracleComp` form).** Simulating, via `simOracle2 oSpec t₁ t₂
- `lemma ToyProblem.Spec.simulateQ_simOracle2_messageQuery` [ArkLib\ProofSystem\ToyProblem\Spec\General.lean:718](../../../ArkLib\ProofSystem\ToyProblem\Spec\General.lean#L718) — `simOracle2` message-query collapse (`OracleComp` form), RIGHT (message) family.

### `squeeze` (3 declarations, 3 files)

- `def DomainSeparator.squeeze` [ArkLib\Data\Hash\DomainSep.lean:241](../../../ArkLib\Data\Hash\DomainSep.lean#L241) — Squeeze `count` native elements. Rust interface: ```rust pub fn squeeze(self, count: usize, label: &
- `def DuplexSponge.squeeze` [ArkLib\Data\Hash\DuplexSponge.lean:512](../../../ArkLib\Data\Hash\DuplexSponge.lean#L512) — ### Squeeze out a vector of units from the sponge (paper version) We differ from the paper version i
- `def HashStateWithInstructions.squeeze` [ArkLib\OracleReduction\FiatShamir\DuplexSponge\State.lean:149](../../../ArkLib\OracleReduction\FiatShamir\DuplexSponge\State.lean#L149) — Perform a secure squeeze operation. Rust interface: ```rust pub fn squeeze(&mut self, output: &mut [

### `subsetSumCount` (3 declarations, 3 files)

- `def ArkLib.ProximityGap.Round4CharacterSum.subsetSumCount` [ArkLib\Data\CodingTheory\ProximityGap\SubsetSumCharacterSum.lean:94](../../../ArkLib\Data\CodingTheory\ProximityGap\SubsetSumCharacterSum.lean#L94) — The subgroup subset-sum count `N(m, target) = #{ S ⊆ G : \|S\| = m, ∑_{x∈S} x = target }`, as a `Finse
- `def ArkLib.ProximityGap.Round4PairingRecursion.subsetSumCount` [ArkLib\Data\CodingTheory\ProximityGap\SubsetSumPairingInflate.lean:238](../../../ArkLib\Data\CodingTheory\ProximityGap\SubsetSumPairingInflate.lean#L238) — **The subset-sum count.** `N(g, c, target)` is the number of subsets `S ⊆ G` (modelled as `Finset (F
- `def ArkLib.ProximityGap.Round4NewtonVietaUpper.subsetSumCount` [ArkLib\Data\CodingTheory\ProximityGap\SubsetSumPigeonholeFiber.lean:88](../../../ArkLib\Data\CodingTheory\ProximityGap\SubsetSumPigeonholeFiber.lean#L88) — The §7 **subgroup subset-sum fiber count** `N(a, target)`: the number of size-`a` subsets of the gro

### `sum_char_eq_ite` (3 declarations, 3 files)

- `theorem ArkLib.ProximityGap.MomentCollisionSpectral.sum_char_eq_ite` [ArkLib\Data\CodingTheory\ProximityGap\MomentCollisionSpectral.lean:70](../../../ArkLib\Data\CodingTheory\ProximityGap\MomentCollisionSpectral.lean#L70) — Second orthogonality relation, restated: `∑_{ψ} ψ y = \|A\| · [y = 0]`.
- `theorem ArkLib.ProximityGap.Round9SubgroupCharExpansion.sum_char_eq_ite` [ArkLib\Data\CodingTheory\ProximityGap\Round9SubgroupCharExpansion.lean:80](../../../ArkLib\Data\CodingTheory\ProximityGap\Round9SubgroupCharExpansion.lean#L80) — **Second orthogonality, full form.** `∑_{χ} χ(a) = \|M\|` if `a = 1`, else `0`.
- `lemma ArkLib.CodingTheory.CharacterSum.sum_char_eq_ite` [ArkLib\Data\CodingTheory\ProximityGap\SubgroupCharacterSumNoGo.lean:97](../../../ArkLib\Data\CodingTheory\ProximityGap\SubgroupCharacterSumNoGo.lean#L97) — **Per-coordinate character orthogonality.** For each `i`, the sum over additive characters of `F` of

### `toVerifier` (3 declarations, 3 files)

- `def Interaction.OracleDecoration.OracleReduction.toVerifier` [ArkLib\Interaction\Oracle\Core.lean:1096](../../../ArkLib\Interaction\Oracle\Core.lean#L1096) — (no docstring)
- `def Interaction.PublicCoinVerifier.toVerifier` [ArkLib\Interaction\Reduction.lean:162](../../../ArkLib\Interaction\Reduction.lean#L162) — (no docstring)
- `def OracleVerifier.toVerifier` [ArkLib\OracleReduction\Basic.lean:553](../../../ArkLib\OracleReduction\Basic.lean#L553) — An oracle verifier can be seen as a (non-oracle) verifier by providing the oracle interface using it

### `transcriptSimulator` (3 declarations, 3 files)

- `def RandomQuery.transcriptSimulator` [ArkLib\ProofSystem\Component\RandomQuery.lean:203](../../../ArkLib\ProofSystem\Component\RandomQuery.lean#L203) — The simulator for `RandomQuery`: the protocol is witness-free, so the simulator can rerun the honest
- `def SendClaim.transcriptSimulator` [ArkLib\ProofSystem\Component\SendClaim.lean:246](../../../ArkLib\ProofSystem\Component\SendClaim.lean#L246) — The simulator for `SendClaim`: the component has no private witness, so the simulator can run the ho
- `def SendWitness.transcriptSimulator` [ArkLib\ProofSystem\Component\SendWitness.lean:103](../../../ArkLib\ProofSystem\Component\SendWitness.lean#L103) — The simulator for the `SendWitness` reduction when the relation's witness is determined by the input

### `verify` (3 declarations, 3 files)

- `def ArkLib.Lattices.Ajtai.Simple.verify` [ArkLib\CommitmentScheme\Ajtai\Simple\Scheme.lean:46](../../../ArkLib\CommitmentScheme\Ajtai\Simple\Scheme.lean#L46) — Verify a simple Ajtai opening by checking the matrix product.
- `def SimpleRO.verify` [ArkLib\CommitmentScheme\SimpleRO.lean:50](../../../ArkLib\CommitmentScheme\SimpleRO.lean#L50) — (no docstring)
- `def OracleVerifier.Append.verify` [ArkLib\OracleReduction\Composition\Sequential\Append.lean:377](../../../ArkLib\OracleReduction\Composition\Sequential\Append.lean#L377) — The composite `verify`: run `V₁` (routed by `router₁`) to obtain the intermediate statement, then ru

### `zeta` (3 declarations, 3 files)

- `def R12J.General.zeta` [ArkLib\Data\CodingTheory\ProximityGap\JointT2Unconditional.lean:168](../../../ArkLib\Data\CodingTheory\ProximityGap\JointT2Unconditional.lean#L168) — The primitive `2^m`-th root of unity we work with.
- `def Concrete.zeta` [ArkLib\Data\CodingTheory\ProximityGap\LamLeungUnconditionalGeneral.lean:209](../../../ArkLib\Data\CodingTheory\ProximityGap\LamLeungUnconditionalGeneral.lean#L209) — The explicit primitive `2^m`-th root of unity `exp(2πi/2^m)` in `ℂ`.
- `def ArkLib.ProximityGap.SubgroupQuadraticSecondMoment.zeta` [ArkLib\Data\CodingTheory\ProximityGap\SubgroupQuadraticSecondMoment.lean:54](../../../ArkLib\Data\CodingTheory\ProximityGap\SubgroupQuadraticSecondMoment.lean#L54) — The quadratic subgroup Gauss sum at frequency `b`: `ζ_b = ∑_{x∈G} ψ(b·x²)`.

### `card_le_natDegreeY_of_sub_C_dvd` (3 declarations, 3 files)

- `theorem R14.card_le_natDegreeY_of_sub_C_dvd` [ArkLib\Data\CodingTheory\ProximityGap\GSYDegreeListCap.lean:45](../../../ArkLib\Data\CodingTheory\ProximityGap\GSYDegreeListCap.lean#L45) — **Y-degree list cap.**  If `Q ≠ 0` in `(F[X])[Y]` and every `f` in the finite set `S ⊆ F[X]` gives a
- `theorem R15.card_le_natDegreeY_of_sub_C_dvd` [ArkLib\Data\CodingTheory\ProximityGap\SudanListBound.lean:259](../../../ArkLib\Data\CodingTheory\ProximityGap\SudanListBound.lean#L259) — **Y-degree list cap.** If `Q ≠ 0` in `(F[X])[Y]` and every `f ∈ S` gives a linear factor `Y - C f` o
- `theorem R15.card_le_natDegreeY_of_sub_C_dvd` [ArkLib\Data\CodingTheory\ProximityGap\SudanListBoundFull.lean:259](../../../ArkLib\Data\CodingTheory\ProximityGap\SudanListBoundFull.lean#L259) — **Y-degree list cap.** If `Q ≠ 0` in `(F[X])[Y]` and every `f ∈ S` gives a linear factor `Y - C f` o

### `coeffPoly_evalEval` (3 declarations, 3 files)

- `lemma GSInterp.coeffPoly_evalEval` [ArkLib\Data\CodingTheory\ProximityGap\GSInterpolationExistence.lean:119](../../../ArkLib\Data\CodingTheory\ProximityGap\GSInterpolationExistence.lean#L119) — (no docstring)
- `lemma R15.coeffPoly_evalEval` [ArkLib\Data\CodingTheory\ProximityGap\SudanListBound.lean:126](../../../ArkLib\Data\CodingTheory\ProximityGap\SudanListBound.lean#L126) — (no docstring)
- `lemma R15.coeffPoly_evalEval` [ArkLib\Data\CodingTheory\ProximityGap\SudanListBoundFull.lean:126](../../../ArkLib\Data\CodingTheory\ProximityGap\SudanListBoundFull.lean#L126) — (no docstring)

### `evalAtPoints` (3 declarations, 3 files)

- `def GSInterp.evalAtPoints` [ArkLib\Data\CodingTheory\ProximityGap\GSInterpolationExistence.lean:133](../../../ArkLib\Data\CodingTheory\ProximityGap\GSInterpolationExistence.lean#L133) — The linear map sending a coefficient vector supported on `S` to the values of the associated bivaria
- `def R15.evalAtPoints` [ArkLib\Data\CodingTheory\ProximityGap\SudanListBound.lean:140](../../../ArkLib\Data\CodingTheory\ProximityGap\SudanListBound.lean#L140) — The linear map sending a coefficient vector supported on `S` to the values of the associated bivaria
- `def R15.evalAtPoints` [ArkLib\Data\CodingTheory\ProximityGap\SudanListBoundFull.lean:140](../../../ArkLib\Data\CodingTheory\ProximityGap\SudanListBoundFull.lean#L140) — The linear map sending a coefficient vector supported on `S` to the values of the associated bivaria

### `evalAtPoints_apply` (3 declarations, 3 files)

- `lemma GSInterp.evalAtPoints_apply` [ArkLib\Data\CodingTheory\ProximityGap\GSInterpolationExistence.lean:143](../../../ArkLib\Data\CodingTheory\ProximityGap\GSInterpolationExistence.lean#L143) — (no docstring)
- `lemma R15.evalAtPoints_apply` [ArkLib\Data\CodingTheory\ProximityGap\SudanListBound.lean:150](../../../ArkLib\Data\CodingTheory\ProximityGap\SudanListBound.lean#L150) — (no docstring)
- `lemma R15.evalAtPoints_apply` [ArkLib\Data\CodingTheory\ProximityGap\SudanListBoundFull.lean:150](../../../ArkLib\Data\CodingTheory\ProximityGap\SudanListBoundFull.lean#L150) — (no docstring)

### `factor_of_agreement` (3 declarations, 3 files)

- `theorem GSRootOrder.factor_of_agreement` [ArkLib\Data\CodingTheory\ProximityGap\GSRootOrderStep.lean:52](../../../ArkLib\Data\CodingTheory\ProximityGap\GSRootOrderStep.lean#L52) — **The root-order / factor step (Sudan, multiplicity 1).**  Let `Q : (F[X])[Y]` satisfy the `(1, k−1)
- `theorem R15.factor_of_agreement` [ArkLib\Data\CodingTheory\ProximityGap\SudanListBound.lean:233](../../../ArkLib\Data\CodingTheory\ProximityGap\SudanListBound.lean#L233) — **Root-order / factor step (multiplicity 1).** `≥ D` vanishing points of the degree-`< D` univariate
- `theorem R15.factor_of_agreement` [ArkLib\Data\CodingTheory\ProximityGap\SudanListBoundFull.lean:233](../../../ArkLib\Data\CodingTheory\ProximityGap\SudanListBoundFull.lean#L233) — **Root-order / factor step (multiplicity 1).** `≥ D` vanishing points of the degree-`< D` univariate

### `rs_lambda_high_rate_jh01` (3 declarations, 3 files)

- `theorem CodingTheory.rs_lambda_high_rate_jh01` [ArkLib\Data\CodingTheory\ListDecoding\Bounds.lean:2083](../../../ArkLib\Data\CodingTheory\ListDecoding\Bounds.lean#L2083) — **ABF26 Theorem 3.14 [JH01 Thm 2], repaired list-size form.** Large-rate Reed-Solomon lower bound. F
- `theorem CodingTheory.rs_lambda_high_rate_jh01` [ArkLib\Data\CodingTheory\ListDecoding\Bounds\RandomAndReedSolomon.lean:764](../../../ArkLib\Data\CodingTheory\ListDecoding\Bounds\RandomAndReedSolomon.lean#L764) — **ABF26 Theorem 3.14 [JH01 Thm 2], repaired list-size form.** Large-rate Reed-Solomon lower bound. F
- `theorem CodingTheory.ReedSolomon.rs_lambda_high_rate_jh01` [ArkLib\Data\CodingTheory\ListDecoding\JH01.lean:214](../../../ArkLib\Data\CodingTheory\ListDecoding\JH01.lean#L214) — ABF26 Theorem 3.14 / JH01 Theorem 2, in a repaired list-size form.  For every `j ≥ 2`, infinitely ma

### `sudan_interpolation_exists` (3 declarations, 3 files)

- `theorem GSInterp.sudan_interpolation_exists` [ArkLib\Data\CodingTheory\ProximityGap\GSInterpolationExistence.lean:150](../../../ArkLib\Data\CodingTheory\ProximityGap\GSInterpolationExistence.lean#L150) — (no docstring)
- `theorem R15.sudan_interpolation_exists` [ArkLib\Data\CodingTheory\ProximityGap\SudanListBound.lean:156](../../../ArkLib\Data\CodingTheory\ProximityGap\SudanListBound.lean#L156) — **Sudan (multiplicity-1) interpolation existence.**
- `theorem R15.sudan_interpolation_exists` [ArkLib\Data\CodingTheory\ProximityGap\SudanListBoundFull.lean:156](../../../ArkLib\Data\CodingTheory\ProximityGap\SudanListBoundFull.lean#L156) — **Sudan (multiplicity-1) interpolation existence.**

### `support` (3 declarations, 3 files)

- `def support` [ArkLib\Data\CodingTheory\ProximityGap\PromotedHypothesesB.lean:64](../../../ArkLib\Data\CodingTheory\ProximityGap\PromotedHypothesesB.lean#L64) — (no docstring)
- `def ArkLib.ProximityGap.Round5SecondMoment.support` [ArkLib\Data\CodingTheory\ProximityGap\SubsetSumPigeonholeManyTargets.lean:146](../../../ArkLib\Data\CodingTheory\ProximityGap\SubsetSumPigeonholeManyTargets.lean#L146) — The **support**: the set of targets actually hit by some size-`a` subset sum, `{ target : N(a, targe
- `def support` [ArkLib\Data\CodingTheory\Quarantine\CandidateHypotheses.lean:20](../../../ArkLib\Data\CodingTheory\Quarantine\CandidateHypotheses.lean#L20) — (no docstring)

### `uniform_event_mass` (3 declarations, 3 files)

- `lemma OutOfDomSmpl.uniform_event_mass` [ArkLib\ProofSystem\Stir\OutOfDomSmpl.lean:55](../../../ArkLib\ProofSystem\Stir\OutOfDomSmpl.lean#L55) — The mass that the `Pr_{...}[...]` PMF encoding assigns to an event under uniform sampling is exactly
- `lemma OutOfDomSmpl.uniform_event_mass` [ArkLib\ProofSystem\Whir\OutofDomainSmpl.lean:166](../../../ArkLib\ProofSystem\Whir\OutofDomainSmpl.lean#L166) — The mass that the `Pr_{...}[...]` PMF encoding assigns to an event under uniform sampling is exactly
- `theorem uniform_event_mass` [ArkLib\ToMathlib\CountingAgreementBricks.lean:109](../../../ArkLib\ToMathlib\CountingAgreementBricks.lean#L109) — The mass of a finite event under the uniform distribution is its cardinality divided by the sample-s

### `frs_list_decoding_capacity_cz25_of_coordFiberCap_T218_prop` (3 declarations, 3 files)

- `theorem CodingTheory.frs_list_decoding_capacity_cz25_of_coordFiberCap_T218_prop` [ArkLib\Data\CodingTheory\ListDecoding\Bounds.lean:2293](../../../ArkLib\Data\CodingTheory\ListDecoding\Bounds.lean#L2293) — Prop-level C3.5 endpoint from coordinate-fiber cap plus T2.18. This wraps the unfolded reduction `fr
- `theorem CodingTheory.frs_list_decoding_capacity_cz25_of_coordFiberCap_T218_prop` [ArkLib\Data\CodingTheory\ListDecoding\Bounds\SubspaceDesign.lean:221](../../../ArkLib\Data\CodingTheory\ListDecoding\Bounds\SubspaceDesign.lean#L221) — Prop-level C3.5 endpoint from coordinate-fiber cap plus T2.18. This wraps the unfolded reduction `fr
- `theorem CodingTheory.frs_list_decoding_capacity_cz25_of_coordFiberCap_T218_prop` [ArkLib\Data\CodingTheory\ListDecoding\CZ25CapacityPropEndpoint.lean:64](../../../ArkLib\Data\CodingTheory\ListDecoding\CZ25CapacityPropEndpoint.lean#L64) — **ABF26 Corollary 3.5 [CZ25 Cor 2.21] — named-`Prop` endpoint from the coordinate-fiber cap.** Concl

### `prizeRate_floor_add_one_le` (3 declarations, 3 files)

- `lemma ProximityGap.prizeRate_floor_add_one_le` [ArkLib\Data\CodingTheory\ProximityGap\GrandChallengeDecision.lean:149](../../../ArkLib\Data\CodingTheory\ProximityGap\GrandChallengeDecision.lean#L149) — For `n ≥ 2`, every prize-rate degree satisfies `k_j + 1 ≤ n`.
- `lemma ProximityGap.prizeRate_floor_add_one_le` [ArkLib\Data\CodingTheory\ProximityGap\GrandChallengeLDFourRate.lean:218](../../../ArkLib\Data\CodingTheory\ProximityGap\GrandChallengeLDFourRate.lean#L218) — If the evaluation domain has at least two points, each prize degree is strictly below the block leng
- `lemma ProximityGap.prizeRate_floor_add_one_le` [ArkLib\Data\CodingTheory\ProximityGap\MCASecondMoment.lean:371](../../../ArkLib\Data\CodingTheory\ProximityGap\MCASecondMoment.lean#L371) — For `n ≥ 2`, every prize-rate degree satisfies `k_j + 1 ≤ n`.

### `cast_id` (9 declarations, 2 files)

- `theorem Prover.cast_id` [ArkLib\OracleReduction\Cast.lean:53](../../../ArkLib\OracleReduction\Cast.lean#L53) — (no docstring)
- `theorem OracleProver.cast_id` [ArkLib\OracleReduction\Cast.lean:77](../../../ArkLib\OracleReduction\Cast.lean#L77) — (no docstring)
- `theorem Verifier.cast_id` [ArkLib\OracleReduction\Cast.lean:99](../../../ArkLib\OracleReduction\Cast.lean#L99) — (no docstring)
- `theorem Reduction.cast_id` [ArkLib\OracleReduction\Cast.lean:272](../../../ArkLib\OracleReduction\Cast.lean#L272) — (no docstring)
- `theorem ProtocolSpec.cast_id` [ArkLib\OracleReduction\ProtocolSpec\Cast.lean:35](../../../ArkLib\OracleReduction\ProtocolSpec\Cast.lean#L35) — (no docstring)
- `theorem ProtocolSpec.MessageIdx.cast_id` [ArkLib\OracleReduction\ProtocolSpec\Cast.lean:79](../../../ArkLib\OracleReduction\ProtocolSpec\Cast.lean#L79) — (no docstring)
- `theorem ProtocolSpec.ChallengeIdx.cast_id` [ArkLib\OracleReduction\ProtocolSpec\Cast.lean:118](../../../ArkLib\OracleReduction\ProtocolSpec\Cast.lean#L118) — (no docstring)
- `theorem ProtocolSpec.Transcript.cast_id` [ArkLib\OracleReduction\ProtocolSpec\Cast.lean:162](../../../ArkLib\OracleReduction\ProtocolSpec\Cast.lean#L162) — (no docstring)
- `theorem ProtocolSpec.FullTranscript.cast_id` [ArkLib\OracleReduction\ProtocolSpec\Cast.lean:188](../../../ArkLib\OracleReduction\ProtocolSpec\Cast.lean#L188) — (no docstring)

### `proj` (8 declarations, 2 files)

- `def Round16SelfSimilar.proj` [ArkLib\Data\CodingTheory\ProximityGap\SmoothDomainSelfSimilarity.lean:62](../../../ArkLib\Data\CodingTheory\ProximityGap\SmoothDomainSelfSimilarity.lean#L62) — The index fiber map `π : Fin (s·e) → Fin s`, `i ↦ i % s` (the index-level power map).
- `def Statement.Lens.proj` [ArkLib\OracleReduction\LiftContext\Lens.lean:49](../../../ArkLib\OracleReduction\LiftContext\Lens.lean#L49) — Transport input statements from the outer context to the inner context
- `def OracleStatement.Lens.proj` [ArkLib\OracleReduction\LiftContext\Lens.lean:109](../../../ArkLib\OracleReduction\LiftContext\Lens.lean#L109) — Transport input statements from the outer context to the inner context This is the projection compon
- `def Witness.Lens.proj` [ArkLib\OracleReduction\LiftContext\Lens.lean:236](../../../ArkLib\OracleReduction\LiftContext\Lens.lean#L236) — Transport input witness from the outer context to the inner context
- `def Context.Lens.proj` [ArkLib\OracleReduction\LiftContext\Lens.lean:263](../../../ArkLib\OracleReduction\LiftContext\Lens.lean#L263) — Projection of the context.
- `def OracleContext.Lens.proj` [ArkLib\OracleReduction\LiftContext\Lens.lean:300](../../../ArkLib\OracleReduction\LiftContext\Lens.lean#L300) — Projection of the context.
- `def Witness.InvLens.proj` [ArkLib\OracleReduction\LiftContext\Lens.lean:339](../../../ArkLib\OracleReduction\LiftContext\Lens.lean#L339) — Projection of the witness.
- `def Extractor.Lens.proj` [ArkLib\OracleReduction\LiftContext\Lens.lean:372](../../../ArkLib\OracleReduction\LiftContext\Lens.lean#L372) — Transport the tuple of (input statement, output witness) from the outer context to the inner context

### `seqCompose` (8 declarations, 2 files)

- `def Prover.seqCompose` [ArkLib\OracleReduction\Composition\Sequential\General.lean:37](../../../ArkLib\OracleReduction\Composition\Sequential\General.lean#L37) — Sequential composition of provers, defined via iteration of the composition (append) of two provers.
- `def Verifier.seqCompose` [ArkLib\OracleReduction\Composition\Sequential\General.lean:75](../../../ArkLib\OracleReduction\Composition\Sequential\General.lean#L75) — Sequential composition of verifiers, defined via iteration of the composition (append) of two verifi
- `def Reduction.seqCompose` [ArkLib\OracleReduction\Composition\Sequential\General.lean:104](../../../ArkLib\OracleReduction\Composition\Sequential\General.lean#L104) — Sequential composition of reductions, defined via sequential composition of provers and verifiers (o
- `def OracleProver.seqCompose` [ArkLib\OracleReduction\Composition\Sequential\General.lean:135](../../../ArkLib\OracleReduction\Composition\Sequential\General.lean#L135) — Sequential composition of provers in oracle reductions, defined via sequential composition of prover
- `def OracleVerifier.seqCompose` [ArkLib\OracleReduction\Composition\Sequential\General.lean:188](../../../ArkLib\OracleReduction\Composition\Sequential\General.lean#L188) — Sequential composition of oracle verifiers (in oracle reductions), defined via iteration of the comp
- `def OracleReduction.seqCompose` [ArkLib\OracleReduction\Composition\Sequential\General.lean:310](../../../ArkLib\OracleReduction\Composition\Sequential\General.lean#L310) — Sequential composition of oracle reductions, defined via sequential composition of oracle provers an
- `def ProtocolSpec.seqCompose` [ArkLib\OracleReduction\ProtocolSpec\SeqCompose.lean:335](../../../ArkLib\OracleReduction\ProtocolSpec\SeqCompose.lean#L335) — Sequential composition of a family of `ProtocolSpec`s, indexed by `i : Fin m`. Defined for definitio
- `def ProtocolSpec.FullTranscript.seqCompose` [ArkLib\OracleReduction\ProtocolSpec\SeqCompose.lean:393](../../../ArkLib\OracleReduction\ProtocolSpec\SeqCompose.lean#L393) — Sequential composition of a family of `FullTranscript`s, indexed by `i : Fin m`. Defined for definit

### `seqCompose_zero` (7 declarations, 2 files)

- `lemma Prover.seqCompose_zero` [ArkLib\OracleReduction\Composition\Sequential\General.lean:48](../../../ArkLib\OracleReduction\Composition\Sequential\General.lean#L48) — (no docstring)
- `lemma Verifier.seqCompose_zero` [ArkLib\OracleReduction\Composition\Sequential\General.lean:83](../../../ArkLib\OracleReduction\Composition\Sequential\General.lean#L83) — (no docstring)
- `lemma Reduction.seqCompose_zero` [ArkLib\OracleReduction\Composition\Sequential\General.lean:113](../../../ArkLib\OracleReduction\Composition\Sequential\General.lean#L113) — (no docstring)
- `lemma OracleVerifier.seqCompose_zero` [ArkLib\OracleReduction\Composition\Sequential\General.lean:204](../../../ArkLib\OracleReduction\Composition\Sequential\General.lean#L204) — (no docstring)
- `lemma OracleReduction.seqCompose_zero` [ArkLib\OracleReduction\Composition\Sequential\General.lean:347](../../../ArkLib\OracleReduction\Composition\Sequential\General.lean#L347) — (no docstring)
- `theorem ProtocolSpec.seqCompose_zero` [ArkLib\OracleReduction\ProtocolSpec\SeqCompose.lean:351](../../../ArkLib\OracleReduction\ProtocolSpec\SeqCompose.lean#L351) — (no docstring)
- `theorem ProtocolSpec.FullTranscript.seqCompose_zero` [ArkLib\OracleReduction\ProtocolSpec\SeqCompose.lean:398](../../../ArkLib\OracleReduction\ProtocolSpec\SeqCompose.lean#L398) — (no docstring)

### `concat` (5 declarations, 2 files)

- `def ProtocolSpec.MessagesUpTo.concat` [ArkLib\OracleReduction\ProtocolSpec\Basic.lean:416](../../../ArkLib\OracleReduction\ProtocolSpec\Basic.lean#L416) — Concatenate the `k`-th message to the end of the tuple of messages up to round `k`, assuming round `
- `def ProtocolSpec.ChallengesUpTo.concat` [ArkLib\OracleReduction\ProtocolSpec\Basic.lean:465](../../../ArkLib\OracleReduction\ProtocolSpec\Basic.lean#L465) — Concatenate the `k`-th challenge to the end of the tuple of challenges up to round `k`, assuming rou
- `abbrev ProtocolSpec.Transcript.concat` [ArkLib\OracleReduction\ProtocolSpec\Basic.lean:504](../../../ArkLib\OracleReduction\ProtocolSpec\Basic.lean#L504) — Concatenate a message to the end of a partial transcript. This is definitionally equivalent to `Fin.
- `abbrev ProtocolSpec.concat` [ArkLib\OracleReduction\ProtocolSpec\SeqCompose.lean:44](../../../ArkLib\OracleReduction\ProtocolSpec\SeqCompose.lean#L44) — Concatenate a round with direction `dir` and type `Message` to the end of a `ProtocolSpec`
- `def ProtocolSpec.FullTranscript.concat` [ArkLib\OracleReduction\ProtocolSpec\SeqCompose.lean:168](../../../ArkLib\OracleReduction\ProtocolSpec\SeqCompose.lean#L168) — Adding a message with a given direction and type to the end of a `Transcript`

### `knowledgeSoundness` (5 declarations, 2 files)

- `def Verifier.knowledgeSoundness` [ArkLib\OracleReduction\Security\Basic.lean:357](../../../ArkLib\OracleReduction\Security\Basic.lean#L357) — A reduction satisfies **(straightline) knowledge soundness** with error `knowledgeError ≥ 0` and wit
- `def OracleVerifier.knowledgeSoundness` [ArkLib\OracleReduction\Security\Basic.lean:492](../../../ArkLib\OracleReduction\Security\Basic.lean#L492) — Knowledge soundness of an oracle reduction is the same as for non-oracle reductions.
- `def Proof.knowledgeSoundness` [ArkLib\OracleReduction\Security\Basic.lean:533](../../../ArkLib\OracleReduction\Security\Basic.lean#L533) — (no docstring)
- `def OracleProof.knowledgeSoundness` [ArkLib\OracleReduction\Security\Basic.lean:571](../../../ArkLib\OracleReduction\Security\Basic.lean#L571) — Knowledge soundness of an oracle reduction is the same as for non-oracle reductions.
- `def Verifier.StateRestoration.knowledgeSoundness` [ArkLib\OracleReduction\Security\StateRestoration.lean:195](../../../ArkLib\OracleReduction\Security\StateRestoration.lean#L195) — State-restoration knowledge soundness (w/ straightline extractor).

### `new` (5 declarations, 2 files)

- `def DomainSeparator.Op.new` [ArkLib\Data\Hash\DomainSep.lean:138](../../../ArkLib\Data\Hash\DomainSep.lean#L138) — Construct a new `Op` from a character `id` and a count number `count : Option Nat`. Returns error if
- `def DomainSeparator.new` [ArkLib\Data\Hash\DomainSep.lean:193](../../../ArkLib\Data\Hash\DomainSep.lean#L193) — Create a new DomainSeparator with the domain separator. Rust interface: ```rust pub fn new(session_i
- `def HashStateWithInstructions.new` [ArkLib\OracleReduction\FiatShamir\DuplexSponge\State.lean:98](../../../ArkLib\OracleReduction\FiatShamir\DuplexSponge\State.lean#L98) — Initialize a stateful hash object from a domain separator. Rust interface: ```rust pub fn new(domain
- `def FSVerifierState.new` [ArkLib\OracleReduction\FiatShamir\DuplexSponge\State.lean:275](../../../ArkLib\OracleReduction\FiatShamir\DuplexSponge\State.lean#L275) — Create a new VerifierState from a domain separator and NARG string. Rust interface: ```rust pub fn n
- `def FSProverState.new` [ArkLib\OracleReduction\FiatShamir\DuplexSponge\State.lean:416](../../../ArkLib\OracleReduction\FiatShamir\DuplexSponge\State.lean#L416) — Create a new `FSProverState` from a domain separator and RNG. Rust interface: ```rust pub fn new(dom

### `perfectCompleteness` (5 declarations, 2 files)

- `abbrev DuplexSpongeFS.NARG.perfectCompleteness` [ArkLib\OracleReduction\FiatShamir\DuplexSponge\Basic.lean:66](../../../ArkLib\OracleReduction\FiatShamir\DuplexSponge\Basic.lean#L66) — Paper-facing alias for CO25 Section 3.4 perfect completeness.
- `def Reduction.perfectCompleteness` [ArkLib\OracleReduction\Security\Basic.lean:126](../../../ArkLib\OracleReduction\Security\Basic.lean#L126) — A reduction satisfies **perfect completeness** if it satisfies completeness with error `0`.
- `def OracleReduction.perfectCompleteness` [ArkLib\OracleReduction\Security\Basic.lean:472](../../../ArkLib\OracleReduction\Security\Basic.lean#L472) — Perfect completeness of an oracle reduction is the same as for non-oracle reductions.
- `def Proof.perfectCompleteness` [ArkLib\OracleReduction\Security\Basic.lean:522](../../../ArkLib\OracleReduction\Security\Basic.lean#L522) — (no docstring)
- `def OracleProof.perfectCompleteness` [ArkLib\OracleReduction\Security\Basic.lean:555](../../../ArkLib\OracleReduction\Security\Basic.lean#L555) — Perfect completeness of an oracle reduction is the same as for non-oracle reductions.

### `cast_eq_dcast₂` (4 declarations, 2 files)

- `theorem Verifier.cast_eq_dcast₂` [ArkLib\OracleReduction\Cast.lean:107](../../../ArkLib\OracleReduction\Cast.lean#L107) — (no docstring)
- `theorem ProtocolSpec.MessageIdx.cast_eq_dcast₂` [ArkLib\OracleReduction\ProtocolSpec\Cast.lean:91](../../../ArkLib\OracleReduction\ProtocolSpec\Cast.lean#L91) — (no docstring)
- `theorem ProtocolSpec.ChallengeIdx.cast_eq_dcast₂` [ArkLib\OracleReduction\ProtocolSpec\Cast.lean:130](../../../ArkLib\OracleReduction\ProtocolSpec\Cast.lean#L130) — (no docstring)
- `theorem ProtocolSpec.FullTranscript.cast_eq_dcast₂` [ArkLib\OracleReduction\ProtocolSpec\Cast.lean:194](../../../ArkLib\OracleReduction\ProtocolSpec\Cast.lean#L194) — (no docstring)

### `crossover_gt` (4 declarations, 2 files)

- `theorem R10ExactDelta.crossover_gt` [ArkLib\Data\CodingTheory\ProximityGap\DeltaStarExactCrossoverF17.lean:119](../../../ArkLib\Data\CodingTheory\ProximityGap\DeltaStarExactCrossoverF17.lean#L119) — Lower side: just below, at `a* - 1 = 3`, the list strictly exceeds `B = 10`.
- `theorem R11DeltaTable.Row1.crossover_gt` [ArkLib\Data\CodingTheory\ProximityGap\DeltaStarTableSmoothInstances.lean:154](../../../ArkLib\Data\CodingTheory\ProximityGap\DeltaStarTableSmoothInstances.lean#L154) — Lower side: the list strictly exceeds `B` one step below.
- `theorem R11DeltaTable.Row2.crossover_gt` [ArkLib\Data\CodingTheory\ProximityGap\DeltaStarTableSmoothInstances.lean:211](../../../ArkLib\Data\CodingTheory\ProximityGap\DeltaStarTableSmoothInstances.lean#L211) — Lower side: the list strictly exceeds `B` one step below.
- `theorem R11DeltaTable.Row3.crossover_gt` [ArkLib\Data\CodingTheory\ProximityGap\DeltaStarTableSmoothInstances.lean:268](../../../ArkLib\Data\CodingTheory\ProximityGap\DeltaStarTableSmoothInstances.lean#L268) — Lower side: the list strictly exceeds `B` one step below.

### `crossover_le` (4 declarations, 2 files)

- `theorem R10ExactDelta.crossover_le` [ArkLib\Data\CodingTheory\ProximityGap\DeltaStarExactCrossoverF17.lean:116](../../../ArkLib\Data\CodingTheory\ProximityGap\DeltaStarExactCrossoverF17.lean#L116) — Upper side: at the crossover `a* = 4` the list fits the bound `B = 10`.
- `theorem R11DeltaTable.Row1.crossover_le` [ArkLib\Data\CodingTheory\ProximityGap\DeltaStarTableSmoothInstances.lean:152](../../../ArkLib\Data\CodingTheory\ProximityGap\DeltaStarTableSmoothInstances.lean#L152) — Upper side: the list fits `B = 10` at the crossover.
- `theorem R11DeltaTable.Row2.crossover_le` [ArkLib\Data\CodingTheory\ProximityGap\DeltaStarTableSmoothInstances.lean:209](../../../ArkLib\Data\CodingTheory\ProximityGap\DeltaStarTableSmoothInstances.lean#L209) — Upper side: the list fits `B = 10` at the crossover.
- `theorem R11DeltaTable.Row3.crossover_le` [ArkLib\Data\CodingTheory\ProximityGap\DeltaStarTableSmoothInstances.lean:266](../../../ArkLib\Data\CodingTheory\ProximityGap\DeltaStarTableSmoothInstances.lean#L266) — Upper side: the list fits `B = 10` at the crossover.

### `instDCast₂` (4 declarations, 2 files)

- `instance Prover.instDCast₂` [ArkLib\OracleReduction\Cast.lean:60](../../../ArkLib\OracleReduction\Cast.lean#L60) — (no docstring)
- `instance ProtocolSpec.MessageIdx.instDCast₂` [ArkLib\OracleReduction\ProtocolSpec\Cast.lean:87](../../../ArkLib\OracleReduction\ProtocolSpec\Cast.lean#L87) — (no docstring)
- `instance ProtocolSpec.ChallengeIdx.instDCast₂` [ArkLib\OracleReduction\ProtocolSpec\Cast.lean:126](../../../ArkLib\OracleReduction\ProtocolSpec\Cast.lean#L126) — (no docstring)
- `instance ProtocolSpec.FullTranscript.instDCast₂` [ArkLib\OracleReduction\ProtocolSpec\Cast.lean:190](../../../ArkLib\OracleReduction\ProtocolSpec\Cast.lean#L190) — (no docstring)

### `interior` (4 declarations, 2 files)

- `theorem R10ExactDelta.interior` [ArkLib\Data\CodingTheory\ProximityGap\DeltaStarExactCrossoverF17.lean:125](../../../ArkLib\Data\CodingTheory\ProximityGap\DeltaStarExactCrossoverF17.lean#L125) — The crossover is strictly **interior** to the open prize window: `k < a*` (i.e. `δ* < 1 - k/n`, abov
- `theorem R11DeltaTable.Row1.interior` [ArkLib\Data\CodingTheory\ProximityGap\DeltaStarTableSmoothInstances.lean:160](../../../ArkLib\Data\CodingTheory\ProximityGap\DeltaStarTableSmoothInstances.lean#L160) — The crossover is strictly interior: `k < a*` and `a*² < k·n` (`3 < 5` and `25 < 48 = 3·16`).
- `theorem R11DeltaTable.Row2.interior` [ArkLib\Data\CodingTheory\ProximityGap\DeltaStarTableSmoothInstances.lean:217](../../../ArkLib\Data\CodingTheory\ProximityGap\DeltaStarTableSmoothInstances.lean#L217) — The crossover is strictly interior: `k < a*` and `a*² < k·n` (`2 < 3` and `9 < 16 = 2·8`).
- `theorem R11DeltaTable.Row3.interior` [ArkLib\Data\CodingTheory\ProximityGap\DeltaStarTableSmoothInstances.lean:274](../../../ArkLib\Data\CodingTheory\ProximityGap\DeltaStarTableSmoothInstances.lean#L274) — The crossover is strictly interior: `k < a*` and `a*² < k·n` (`2 < 3` and `9 < 16 = 2·8`).

### `listSize` (4 declarations, 2 files)

- `def R10ExactDelta.listSize` [ArkLib\Data\CodingTheory\ProximityGap\DeltaStarExactCrossoverF17.lean:99](../../../ArkLib\Data\CodingTheory\ProximityGap\DeltaStarExactCrossoverF17.lean#L99) — The list size at agreement threshold `a`: number of lines `(b,c)` whose agreement with `w` is at lea
- `def R11DeltaTable.Row1.listSize` [ArkLib\Data\CodingTheory\ProximityGap\DeltaStarTableSmoothInstances.lean:135](../../../ArkLib\Data\CodingTheory\ProximityGap\DeltaStarTableSmoothInstances.lean#L135) — `listSize a = \|Λ(C, δ)\|`, `δ = 1 - a/16`.
- `def R11DeltaTable.Row2.listSize` [ArkLib\Data\CodingTheory\ProximityGap\DeltaStarTableSmoothInstances.lean:193](../../../ArkLib\Data\CodingTheory\ProximityGap\DeltaStarTableSmoothInstances.lean#L193) — `listSize a = \|Λ(C, δ)\|`, `δ = 1 - a/8`.
- `def R11DeltaTable.Row3.listSize` [ArkLib\Data\CodingTheory\ProximityGap\DeltaStarTableSmoothInstances.lean:250](../../../ArkLib\Data\CodingTheory\ProximityGap\DeltaStarTableSmoothInstances.lean#L250) — `listSize a = \|Λ(C, δ)\|`, `δ = 1 - a/8`.

### `subdomain` (4 declarations, 2 files)

- `def Domain.CosetFftDomainClass.subdomain` [ArkLib\Data\Domain\CosetFftDomain\Subdomain.lean:88](../../../ArkLib\Data\Domain\CosetFftDomain\Subdomain.lean#L88) — Given a smooth coset FFT domain `ω` of log-order `n` this function returns its subdomain of log-orde
- `abbrev Domain.CosetFftDomain.subdomain` [ArkLib\Data\Domain\CosetFftDomain\Subdomain.lean:449](../../../ArkLib\Data\Domain\CosetFftDomain\Subdomain.lean#L449) — (no docstring)
- `def Domain.FftDomainClass.subdomain` [ArkLib\Data\Domain\FftDomain\Subdomain.lean:44](../../../ArkLib\Data\Domain\FftDomain\Subdomain.lean#L44) — (no docstring)
- `abbrev Domain.FftDomain.subdomain` [ArkLib\Data\Domain\FftDomain\Subdomain.lean:134](../../../ArkLib\Data\Domain\FftDomain\Subdomain.lean#L134) — (no docstring)

### `toList` (4 declarations, 2 files)

- `def Domain.CosetFftDomainClass.toList` [ArkLib\Data\Domain\CosetFftDomain\ToList.lean:37](../../../ArkLib\Data\Domain\CosetFftDomain\ToList.lean#L37) — (no docstring)
- `def Domain.CosetFftDomain.toList` [ArkLib\Data\Domain\CosetFftDomain\ToList.lean:52](../../../ArkLib\Data\Domain\CosetFftDomain\ToList.lean#L52) — Convert a coset FFT domain into a list of all its members with proofs the members belong to the FFT
- `def Domain.FftDomain.toList` [ArkLib\Data\Domain\CosetFftDomain\ToList.lean:63](../../../ArkLib\Data\Domain\CosetFftDomain\ToList.lean#L63) — Convert a FFT domain into a list of all its members with proofs the members belong to the FFT domain
- `def ProtocolSpec.EncodedMessagesBefore.toList` [ArkLib\OracleReduction\FiatShamir\DuplexSponge\Defs.lean:77](../../../ArkLib\OracleReduction\FiatShamir\DuplexSponge\Defs.lean#L77) — Flatten to a sigma-list for consumers still expecting `List (Sigma ...)`.

### `D_injective` (3 declarations, 2 files)

- `theorem ArkLib.CodingTheory.Round3SmoothF17.D_injective` [ArkLib\Data\CodingTheory\ProximityGap\ListInteriorPinF17Subgroup.lean:90](../../../ArkLib\Data\CodingTheory\ProximityGap\ListInteriorPinF17Subgroup.lean#L90) — The domain map is injective (it is an `Embedding`, but we record the underlying statement).
- `lemma RSDeltaStar.Concrete.D_injective` [ArkLib\Data\CodingTheory\ProximityGap\RSAveragingDeltaStarUpper.lean:280](../../../ArkLib\Data\CodingTheory\ProximityGap\RSAveragingDeltaStarUpper.lean#L280) — `D` is injective (so this is a genuine RS evaluation domain).
- `lemma RSDeltaStar.ConcretePos.D_injective` [ArkLib\Data\CodingTheory\ProximityGap\RSAveragingDeltaStarUpper.lean:363](../../../ArkLib\Data\CodingTheory\ProximityGap\RSAveragingDeltaStarUpper.lean#L363) — `D` is injective.

### `accepts` (3 declarations, 2 files)

- `def Plonk.Gate.accepts` [ArkLib\ProofSystem\ConstraintSystem\Plonk.lean:58](../../../ArkLib\ProofSystem\ConstraintSystem\Plonk.lean#L58) — A gate accepts an input vector `x` if its evaluation at `x` is zero.
- `def Plonk.ConstraintSystem.accepts` [ArkLib\ProofSystem\ConstraintSystem\Plonk.lean:129](../../../ArkLib\ProofSystem\ConstraintSystem\Plonk.lean#L129) — A constraint system accepts an input vector `x` if all of its gates accept `x`.
- `def ToyProblem.Spec.accepts` [ArkLib\ProofSystem\ToyProblem\Spec\General.lean:176](../../../ArkLib\ProofSystem\ToyProblem\Spec\General.lean#L176) — The §6.1 decision predicate, factored out so completeness proofs and the verifier object share the s

### `advantage` (3 declarations, 2 files)

- `def ArkLib.Lattices.Ajtai.InnerOuter.WeakBinding.advantage` [ArkLib\CommitmentScheme\Ajtai\InnerOuter\Security.lean:409](../../../ArkLib\CommitmentScheme\Ajtai\InnerOuter\Security.lean#L409) — Weak-binding advantage.
- `def ArkLib.Lattices.SIS.advantage` [ArkLib\Data\Lattices\ModuleSIS.lean:62](../../../ArkLib\Data\Lattices\ModuleSIS.lean#L62) — Search advantage for a SIS-style problem.
- `def ArkLib.Lattices.ModuleSIS.advantage` [ArkLib\Data\Lattices\ModuleSIS.lean:106](../../../ArkLib\Data\Lattices\ModuleSIS.lean#L106) — The Module-SIS advantage.

### `domain` (3 declarations, 2 files)

- `def ArkLib.BoundaryCardResidualRefutation.domain` [ArkLib\Data\CodingTheory\ProximityGap\BoundaryCardResidualRefutation.lean:53](../../../ArkLib\Data\CodingTheory\ProximityGap\BoundaryCardResidualRefutation.lean#L53) — Four distinct evaluation points in `ZMod 5`.
- `def Fri.Domain.domain` [ArkLib\ProofSystem\Fri\Domain.lean:41](../../../ArkLib\ProofSystem\Fri\Domain.lean#L41) — Allows us to enumerate the elements of the subgroup defined above.
- `def Fri.CosetDomain.domain` [ArkLib\ProofSystem\Fri\Domain.lean:451](../../../ArkLib\ProofSystem\Fri\Domain.lean#L451) — (no docstring)

### `experiment` (3 declarations, 2 files)

- `def ArkLib.Lattices.Ajtai.InnerOuter.WeakBinding.experiment` [ArkLib\CommitmentScheme\Ajtai\InnerOuter\Security.lean:396](../../../ArkLib\CommitmentScheme\Ajtai\InnerOuter\Security.lean#L396) — The Hachi/Greyhound weak-binding experiment. ## Ordinary vs. weak binding *Ordinary (exact) binding*
- `def ArkLib.Lattices.SIS.experiment` [ArkLib\Data\Lattices\ModuleSIS.lean:56](../../../ArkLib\Data\Lattices\ModuleSIS.lean#L56) — The SIS experiment: sample a challenge, run the adversary, check validity.
- `def ArkLib.Lattices.ModuleSIS.experiment` [ArkLib\Data\Lattices\ModuleSIS.lean:101](../../../ArkLib\Data\Lattices\ModuleSIS.lean#L101) — The Module-SIS experiment.

### `extract` (3 declarations, 2 files)

- `def Fin.extract` [ArkLib\Data\Fin\Tuple\Defs.lean:73](../../../ArkLib\Data\Fin\Tuple\Defs.lean#L73) — Extract a sub-tuple from a `Fin`-tuple, from index `start` to `stop - 1`.
- `def ProtocolSpec.extract` [ArkLib\OracleReduction\ProtocolSpec\Basic.lean:137](../../../ArkLib\OracleReduction\ProtocolSpec\Basic.lean#L137) — Extract the slice of the rounds of a `ProtocolSpec n` from `start` to `stop - 1`.
- `abbrev ProtocolSpec.FullTranscript.extract` [ArkLib\OracleReduction\ProtocolSpec\Basic.lean:194](../../../ArkLib\OracleReduction\ProtocolSpec\Basic.lean#L194) — (no docstring)

### `fst` (3 declarations, 2 files)

- `def Prover.fst` [ArkLib\OracleReduction\Composition\Sequential\SeamDecomposition.lean:52](../../../ArkLib\OracleReduction\Composition\Sequential\SeamDecomposition.lean#L52) — **Phase-1 seam restriction of a (malicious) prover** over `pSpec₁ ++ₚ pSpec₂`. Runs rounds `0 .. m-1
- `def ProtocolSpec.Transcript.fst` [ArkLib\OracleReduction\ProtocolSpec\SeqCompose.lean:132](../../../ArkLib\OracleReduction\ProtocolSpec\SeqCompose.lean#L132) — The first half of a partial transcript for a concatenated protocol, up to round `k < m + n + 1`. Thi
- `def ProtocolSpec.FullTranscript.fst` [ArkLib\OracleReduction\ProtocolSpec\SeqCompose.lean:217](../../../ArkLib\OracleReduction\ProtocolSpec\SeqCompose.lean#L217) — The first half of a transcript for a concatenated protocol

### `mem_toFinset_iff_mem` (3 declarations, 2 files)

- `lemma Domain.CosetFftDomainClass.mem_toFinset_iff_mem` [ArkLib\Data\Domain\CosetFftDomain\Mem.lean:71](../../../ArkLib\Data\Domain\CosetFftDomain\Mem.lean#L71) — (no docstring)
- `lemma Domain.CosetFftDomain.mem_toFinset_iff_mem` [ArkLib\Data\Domain\CosetFftDomain\Mem.lean:117](../../../ArkLib\Data\Domain\CosetFftDomain\Mem.lean#L117) — (no docstring)
- `lemma Domain.FftDomain.mem_toFinset_iff_mem` [ArkLib\Data\Domain\FftDomain\Mem.lean:69](../../../ArkLib\Data\Domain\FftDomain\Mem.lean#L69) — (no docstring)

### `rdrop` (3 declarations, 2 files)

- `abbrev Fin.rdrop` [ArkLib\Data\Fin\Tuple\Defs.lean:68](../../../ArkLib\Data\Fin\Tuple\Defs.lean#L68) — Drop the last `m` elements of an `n`-tuple where `m ≤ n`, returning an `(n - m)`-tuple. This is defi
- `def ProtocolSpec.rdrop` [ArkLib\OracleReduction\ProtocolSpec\Basic.lean:133](../../../ArkLib\OracleReduction\ProtocolSpec\Basic.lean#L133) — Drop the last `m ≤ n` rounds of a `ProtocolSpec n`
- `abbrev ProtocolSpec.FullTranscript.rdrop` [ArkLib\OracleReduction\ProtocolSpec\Basic.lean:190](../../../ArkLib\OracleReduction\ProtocolSpec\Basic.lean#L190) — (no docstring)

### `rtake` (3 declarations, 2 files)

- `def Fin.rtake` [ArkLib\Data\Fin\Tuple\Defs.lean:55](../../../ArkLib\Data\Fin\Tuple\Defs.lean#L55) — Take the last `m` elements of a finite vector
- `def ProtocolSpec.rtake` [ArkLib\OracleReduction\ProtocolSpec\Basic.lean:125](../../../ArkLib\OracleReduction\ProtocolSpec\Basic.lean#L125) — Take the last `m ≤ n` rounds of a `ProtocolSpec n`
- `abbrev ProtocolSpec.FullTranscript.rtake` [ArkLib\OracleReduction\ProtocolSpec\Basic.lean:182](../../../ArkLib\OracleReduction\ProtocolSpec\Basic.lean#L182) — Take the last `m ≤ n` rounds of a (full) transcript for a protocol specification `pSpec`

### `snd` (3 declarations, 2 files)

- `def Prover.snd` [ArkLib\OracleReduction\Composition\Sequential\SeamDecomposition.lean:90](../../../ArkLib\OracleReduction\Composition\Sequential\SeamDecomposition.lean#L90) — **Phase-2 seam restriction of a (malicious) prover** over `pSpec₁ ++ₚ pSpec₂`. Resumes from `P`'s se
- `def ProtocolSpec.Transcript.snd` [ArkLib\OracleReduction\ProtocolSpec\SeqCompose.lean:141](../../../ArkLib\OracleReduction\ProtocolSpec\SeqCompose.lean#L141) — The second half of a partial transcript for a concatenated protocol.
- `def ProtocolSpec.FullTranscript.snd` [ArkLib\OracleReduction\ProtocolSpec\SeqCompose.lean:223](../../../ArkLib\OracleReduction\ProtocolSpec\SeqCompose.lean#L223) — The second half of a transcript for a concatenated protocol

### `BindingAdversary` (2 declarations, 2 files)

- `structure Commitment.BindingAdversary` [ArkLib\CommitmentScheme\Basic.lean:116](../../../ArkLib\CommitmentScheme\Basic.lean#L116) — An adversary in the (evaluation) binding game returns a commitment `cm`, a query `q`, two purported
- `structure CommitmentScheme.BindingAdversary` [ArkLib\CommitmentScheme\CommitmentScheme.lean:89](../../../ArkLib\CommitmentScheme\CommitmentScheme.lean#L89) — An adversary in the binding game returns a commitment and two purported openings to possibly differe

### `ChallengeIdx` (2 declarations, 2 files)

- `def ProtocolSpec.ChallengeIdx` [ArkLib\OracleReduction\ProtocolSpec\Basic.lean:66](../../../ArkLib\OracleReduction\ProtocolSpec\Basic.lean#L66) — Subtype of `Fin n` for the indices corresponding to challenges in a protocol specification
- `def ProtocolSpec.VectorSpec.ChallengeIdx` [ArkLib\OracleReduction\VectorIOR.lean:54](../../../ArkLib\OracleReduction\VectorIOR.lean#L54) — The type of indices for challenges in a `VectorSpec`.

### `Codec` (2 declarations, 2 files)

- `abbrev DuplexSpongeFS.Codec` [ArkLib\OracleReduction\FiatShamir\DuplexSponge\Basic.lean:204](../../../ArkLib\OracleReduction\FiatShamir\DuplexSponge\Basic.lean#L204) — Paper-facing alias for CO25 Definition 4.1 codecs.
- `class ProtocolSpec.Codec` [ArkLib\OracleReduction\FiatShamir\DuplexSponge\Defs.lean:99](../../../ArkLib\OracleReduction\FiatShamir\DuplexSponge\Defs.lean#L99) — Codec class for CO25 Definition 4.1. `Codec pSpec U` is the generic-parameter carrier for everything

### `Commit` (2 declarations, 2 files)

- `structure Commitment.Commit` [ArkLib\CommitmentScheme\Basic.lean:53](../../../ArkLib\CommitmentScheme\Basic.lean#L53) — The commitment algorithm, parameterized by the committer key and the data to commit.
- `structure CommitmentScheme.Commit` [ArkLib\CommitmentScheme\CommitmentScheme.lean:38](../../../ArkLib\CommitmentScheme\CommitmentScheme.lean#L38) — The commitment algorithm, returning both the commitment and its opening value.

### `Commitment` (2 declarations, 2 files)

- `abbrev ArkLib.Lattices.Ajtai.InnerOuter.Commitment` [ArkLib\CommitmentScheme\Ajtai\InnerOuter\Scheme.lean:126](../../../ArkLib\CommitmentScheme\Ajtai\InnerOuter\Scheme.lean#L126) — Inner-outer commitments live in the outer row space.
- `abbrev ArkLib.Lattices.Ajtai.Simple.Commitment` [ArkLib\CommitmentScheme\Ajtai\Simple\Scheme.lean:35](../../../ArkLib\CommitmentScheme\Ajtai\Simple\Scheme.lean#L35) — Commitments: row vectors over `Rq Φ`.

### `CommitmentType` (2 declarations, 2 files)

- `abbrev BCSTransparentEndToEnd.CommitmentType` [ArkLib\ProofSystem\BCS\TransparentEndToEnd.lean:75](../../../ArkLib\ProofSystem\BCS\TransparentEndToEnd.lean#L75) — The transparent commitment type: a commitment is the data itself.
- `abbrev T.CommitmentType` [ArkLib\t3.lean:9](../../../ArkLib\t3.lean#L9) — (no docstring)

### `ConstraintSystem` (2 declarations, 2 files)

- `structure ConstraintSystem` [ArkLib\ProofSystem\ConstraintSystem\Basic.lean:49](../../../ArkLib\ProofSystem\ConstraintSystem\Basic.lean#L49) — A **constraint system** packages a family of indexed relations into a single bundle. For each `i : I
- `def Plonk.ConstraintSystem` [ArkLib\ProofSystem\ConstraintSystem\Plonk.lean:116](../../../ArkLib\ProofSystem\ConstraintSystem\Plonk.lean#L116) — A Plonk constraint system is a vector of `numGates` gates, each parametrized by the underlying ring

### `CurveCoeffPolys` (2 declarations, 2 files)

- `def ArkLib.BetaToCurveCoeffPolys.CurveCoeffPolys` [ArkLib\ToMathlib\BetaToCurveCoeffPolys.lean:100](../../../ArkLib\ToMathlib\BetaToCurveCoeffPolys.lean#L100) — Asserts that each coefficient of the decoded polynomial $P(z)$ at index $j < deg$ is interpolated by
- `def ArkLib.KeystoneCapstone.CurveCoeffPolys` [ArkLib\ToMathlib\KeystoneCapstone.lean:92](../../../ArkLib\ToMathlib\KeystoneCapstone.lean#L92) — (no docstring)

### `ExtractabilityAdversary` (2 declarations, 2 files)

- `abbrev Commitment.ExtractabilityAdversary` [ArkLib\CommitmentScheme\Basic.lean:183](../../../ArkLib\CommitmentScheme\Basic.lean#L183) — An adversary in the extractability game is an oracle computation that returns a commitment, a query,
- `structure CommitmentScheme.ExtractabilityAdversary` [ArkLib\CommitmentScheme\CommitmentScheme.lean:137](../../../ArkLib\CommitmentScheme\CommitmentScheme.lean#L137) — An adversary in the extractability game returns a commitment, a claimed message/opening pair, and au

### `FinalOracleStatement` (2 declarations, 2 files)

- `def Fri.Spec.FinalOracleStatement` [ArkLib\ProofSystem\Fri\Spec\SingleRound.lean:97](../../../ArkLib\ProofSystem\Fri\Spec\SingleRound.lean#L97) — (no docstring)
- `def Spartan.Spec.Bricks.FinalOracleStatement` [ArkLib\ToMathlib\SpartanBricks.lean:102](../../../ArkLib\ToMathlib\SpartanBricks.lean#L102) — The terminal oracle-statement family: unchanged from after the second sum-check (`bundled (v_A,v_B,v

### `FinalStatement` (2 declarations, 2 files)

- `def Fri.Spec.FinalStatement` [ArkLib\ProofSystem\Fri\Spec\SingleRound.lean:83](../../../ArkLib\ProofSystem\Fri\Spec\SingleRound.lean#L83) — (no docstring)
- `def Spartan.Spec.Bricks.FinalStatement` [ArkLib\ToMathlib\SpartanBricks.lean:97](../../../ArkLib\ToMathlib\SpartanBricks.lean#L97) — The terminal claim statement type: the full Spartan statement after the second sum-check (`(r_y, (r_

### `FinalSumcheckWit` (2 declarations, 2 files)

- `def Binius.BinaryBasefold.CoreInteraction.FinalSumcheckWit` [ArkLib\ProofSystem\Binius\BinaryBasefold\Steps\FinalSumcheck.lean:1620](../../../ArkLib\ProofSystem\Binius\BinaryBasefold\Steps\FinalSumcheck.lean#L1620) — (no docstring)
- `def Binius.FRIBinius.CoreInteractionPhase.FinalSumcheckWit` [ArkLib\ProofSystem\Binius\FRIBinius\CoreInteractionPhase.lean:1313](../../../ArkLib\ProofSystem\Binius\FRIBinius\CoreInteractionPhase.lean#L1313) — (no docstring)

### `G_eighth_roots` (2 declarations, 2 files)

- `theorem ArkLib.ProximityGap.SubgroupAdditiveEnergyF17.G_eighth_roots` [ArkLib\Data\CodingTheory\ProximityGap\SubgroupAdditiveEnergyF17.lean:49](../../../ArkLib\Data\CodingTheory\ProximityGap\SubgroupAdditiveEnergyF17.lean#L49) — (no docstring)
- `theorem ArkLib.ProximityGap.SubgroupRepCountFiniteFieldCounterexample.G_eighth_roots` [ArkLib\Data\CodingTheory\ProximityGap\SubgroupRepCountFiniteFieldCounterexample.lean:48](../../../ArkLib\Data\CodingTheory\ProximityGap\SubgroupRepCountFiniteFieldCounterexample.lean#L48) — Every element of `G` is an `8`-th root of unity (`x^8 = 1`).

### `GenMutualCorrParams` (2 declarations, 2 files)

- `class Fold.GenMutualCorrParams` [ArkLib\ProofSystem\Whir\Folding.lean:683](../../../ArkLib\ProofSystem\Whir\Folding.lean#L683) — The `GenMutualCorrParams` class captures the necessary parameters and assumptions to model a sequenc
- `class WhirIOP.GenMutualCorrParams` [ArkLib\ProofSystem\Whir\RBRSoundness.lean:85](../../../ArkLib\ProofSystem\Whir\RBRSoundness.lean#L85) — `GenMutualCorrParams` binds together a set of smooth ReedSolomon codes `C_{i : M + 1, j : foldingPar

### `H16` (2 declarations, 2 files)

- `def ArkLib.ProximityGap.SubgroupAdditiveEnergyFermat257.H16` [ArkLib\Data\CodingTheory\ProximityGap\SubgroupAdditiveEnergyFermat257.lean:61](../../../ArkLib\Data\CodingTheory\ProximityGap\SubgroupAdditiveEnergyFermat257.lean#L61) — Order-16 subgroup of `F₂₅₇^×`.
- `def ArkLib.ProximityGap.SubgroupAdditiveEnergyFermat65537.H16` [ArkLib\Data\CodingTheory\ProximityGap\SubgroupAdditiveEnergyFermat65537.lean:51](../../../ArkLib\Data\CodingTheory\ProximityGap\SubgroupAdditiveEnergyFermat65537.lean#L51) — Order-16 subgroup of `F₆₅₅₃₇^×`.

### `Hypercube` (2 declarations, 2 files)

- `def ArkLib.CodingTheory.Research.Hypercube` [ArkLib\Data\CodingTheory\Quarantine\CandidateMultilinearHypercube.lean:20](../../../ArkLib\Data\CodingTheory\Quarantine\CandidateMultilinearHypercube.lean#L20) — The Boolean Hypercube domain defined over the field F.
- `def Logup.Hypercube` [ArkLib\ProofSystem\Logup\Common.lean:35](../../../ArkLib\ProofSystem\Logup\Common.lean#L35) — The boolean hypercube with `2^n` points. The paper writes this domain as `H = {±1}^n`; we use bit ve

### `KeyGen` (2 declarations, 2 files)

- `structure Commitment.KeyGen` [ArkLib\CommitmentScheme\Basic.lean:49](../../../ArkLib\CommitmentScheme\Basic.lean#L49) — Key generation for a commitment scheme, producing a committer key and a verifier key.
- `structure CommitmentScheme.KeyGen` [ArkLib\CommitmentScheme\CommitmentScheme.lean:34](../../../ArkLib\CommitmentScheme\CommitmentScheme.lean#L34) — The key-generation algorithm, returning separate keys for the committer and verifier.

### `MLE_eval_eq_sum_eqTilde` (2 declarations, 2 files)

- `theorem MvPolynomial.MLE_eval_eq_sum_eqTilde` [ArkLib\Data\MvPolynomial\Multilinear.lean:319](../../../ArkLib\Data\MvPolynomial\Multilinear.lean#L319) — **MLE evaluation as an eq-weighted sum over the hypercube.**  Evaluating the multilinear extension a
- `lemma RingSwitching.MLE_eval_eq_sum_eqTilde` [ArkLib\ProofSystem\RingSwitching\Prelude.lean:1074](../../../ArkLib\ProofSystem\RingSwitching\Prelude.lean#L1074) — **MLE evaluation as an `eq̃`-weighted hypercube sum.** Evaluating the multilinear extension `MLE f`

### `MessageIdx` (2 declarations, 2 files)

- `def ProtocolSpec.MessageIdx` [ArkLib\OracleReduction\ProtocolSpec\Basic.lean:61](../../../ArkLib\OracleReduction\ProtocolSpec\Basic.lean#L61) — Subtype of `Fin n` for the indices corresponding to messages in a protocol specification
- `def ProtocolSpec.VectorSpec.MessageIdx` [ArkLib\OracleReduction\VectorIOR.lean:50](../../../ArkLib\OracleReduction\VectorIOR.lean#L50) — The type of indices for messages in a `VectorSpec`.

### `OStmt` (2 declarations, 2 files)

- `def StirIOP.Round.OStmt` [ArkLib\ProofSystem\Stir\RoundProtocol.lean:53](../../../ArkLib\ProofSystem\Stir\RoundProtocol.lean#L53) — The single-index oracle statement family for a STIR fold round: the prover holds one oracle function
- `def WhirIOP.Construction.OStmt` [ArkLib\ToMathlib\WhirBricksConstruction.lean:49](../../../ArkLib\ToMathlib\WhirBricksConstruction.lean#L49) — The single-index oracle statement family for the WHIR Vector IOPP: the prover holds one oracle funct

### `OracleProver` (2 declarations, 2 files)

- `abbrev Interaction.OracleDecoration.OracleProver` [ArkLib\Interaction\Oracle\Core.lean:898](../../../ArkLib\Interaction\Oracle\Core.lean#L898) — (no docstring)
- `def OracleProver` [ArkLib\OracleReduction\Basic.lean:446](../../../ArkLib\OracleReduction\Basic.lean#L446) — An **(oracle) prover** in an interactive **oracle** reduction is a prover in the non-oracle reductio

### `OracleReduction` (2 declarations, 2 files)

- `structure Interaction.OracleDecoration.OracleReduction` [ArkLib\Interaction\Oracle\Core.lean:928](../../../ArkLib\Interaction\Oracle\Core.lean#L928) — (no docstring)
- `structure OracleReduction` [ArkLib\OracleReduction\Basic.lean:768](../../../ArkLib\OracleReduction\Basic.lean#L768) — An **interactive oracle reduction** for a given protocol specification `pSpec`, and relative to orac

### `OracleVerifier` (3 declarations, 2 files)

- `structure Interaction.OracleVerifier` [ArkLib\Interaction\Oracle\Core.lean:1042](../../../ArkLib\Interaction\Oracle\Core.lean#L1042) — (no docstring)
- `structure OracleVerifier` [ArkLib\OracleReduction\Basic.lean:175](../../../ArkLib\OracleReduction\Basic.lean#L175) — (no docstring)
- `structure OracleVerifier` [ArkLib\OracleReduction\Basic.lean:466](../../../ArkLib\OracleReduction\Basic.lean#L466) — An **(oracle) verifier** of an interactive **oracle** reduction consists of: - an oracle computation

### `OuterRunSamplesChallenge` (2 declarations, 2 files)

- `def OuterRunSamplesChallenge` [ArkLib\ProofSystem\Logup\Security\OuterRunSamplesChallenge.lean:24](../../../ArkLib\ProofSystem\Logup\Security\OuterRunSamplesChallenge.lean#L24) — (no docstring)
- `def Logup.OuterRunSamplesChallenge` [ArkLib\ProofSystem\Logup\Security\OuterSoundnessReal.lean:221](../../../ArkLib\ProofSystem\Logup\Security\OuterSoundnessReal.lean#L221) — **The genuine residual interface: the outer run samples the challenge.** This is the *only* gap betw

### `OutputOracleStatement` (2 declarations, 2 files)

- `def ToyProblem.Spec.OutputOracleStatement` [ArkLib\ProofSystem\ToyProblem\Spec\General.lean:116](../../../ArkLib\ProofSystem\ToyProblem\Spec\General.lean#L116) — Output oracle statement: the IOR has no output oracle component.
- `def ToyProblem.SimplifiedIOR.OutputOracleStatement` [ArkLib\ProofSystem\ToyProblem\Spec\SimplifiedIOR.lean:77](../../../ArkLib\ProofSystem\ToyProblem\Spec\SimplifiedIOR.lean#L77) — Output oracle statement: the single combined codeword `f_new := f₁ + γ·f₂ : ι → F`.

### `OutputWitness` (2 declarations, 2 files)

- `def ToyProblem.Spec.OutputWitness` [ArkLib\ProofSystem\ToyProblem\Spec\General.lean:120](../../../ArkLib\ProofSystem\ToyProblem\Spec\General.lean#L120) — Output witness: empty.
- `def ToyProblem.SimplifiedIOR.OutputWitness` [ArkLib\ProofSystem\ToyProblem\Spec\SimplifiedIOR.lean:81](../../../ArkLib\ProofSystem\ToyProblem\Spec\SimplifiedIOR.lean#L81) — Output witness for C6.9: the combined message `M_new := M₁ + γ·M₂`.

### `ParamConditions` (2 declarations, 2 files)

- `structure StirIOP.ParamConditions` [ArkLib\ProofSystem\Stir\MainThm.lean:55](../../../ArkLib\ProofSystem\Stir\MainThm.lean#L55) — **Conditions that protocol parameters must satisfy.** - `h_deg` : initial degree `deg` is a power of
- `structure WhirIOP.ParamConditions` [ArkLib\ProofSystem\Whir\RBRSoundness.lean:66](../../../ArkLib\ProofSystem\Whir\RBRSoundness.lean#L66) — ** Conditions that protocol parameters must satisfy. ** h_m : m = varCount₀ h_sumkLt : ∑ i : Fin (M

### `PerRoundProximityGap` (2 declarations, 2 files)

- `def ArkLib.ProofSystem.Stir.ErrorAccumulation.PerRoundProximityGap` [ArkLib\ProofSystem\Stir\ErrorAccumulation.lean:307](../../../ArkLib\ProofSystem\Stir\ErrorAccumulation.lean#L307) — The keystone, abstracted. `PerRoundProximityGap e ProxGapBound` says the accounting per-round error
- `def Core2Keystone.PerRoundProximityGap` [ArkLib\ProofSystem\Whir\KeystoneReduction.lean:52](../../../ArkLib\ProofSystem\Whir\KeystoneReduction.lean#L52) — Verbatim copy of `Issue24FRISTIR.PerRoundProximityGap` (`Stir/SoundnessAccumulation.lean:253`): the

### `Pr_badStack_eq_one` (2 declarations, 2 files)

- `theorem ProximityGap.MCAGSPrizeRefutation.Pr_badStack_eq_one` [ArkLib\Data\CodingTheory\ProximityGap\MCAGSPrizeRefutation.lean:64](../../../ArkLib\Data\CodingTheory\ProximityGap\MCAGSPrizeRefutation.lean#L64) — **The bad event has probability 1.** Since `mcaEventGSrow_badStack` holds for every `γ`, the event i
- `theorem Pr_badStack_eq_one` [ArkLib\MCAGSRefutationCore_keep.lean:63](../../../ArkLib\MCAGSRefutationCore_keep.lean#L63) — **The bad event has probability 1.** Since `mcaEventGSrow_badStack` holds for every `γ`, the event i

### `Proof` (2 declarations, 2 files)

- `abbrev Interaction.Proof` [ArkLib\Interaction\Reduction.lean:232](../../../ArkLib\Interaction\Reduction.lean#L232) — (no docstring)
- `def Proof` [ArkLib\OracleReduction\Basic.lean:792](../../../ArkLib\OracleReduction\Basic.lean#L792) — An **interactive proof (IP)** is an interactive reduction where the output statement is a boolean, t

### `RS_correlatedAgreement_affineLines` (2 declarations, 2 files)

- `theorem ProximityGap.RS_correlatedAgreement_affineLines` [ArkLib\Data\CodingTheory\ProximityGap\BCIKS20\AffineLines\Main.lean:52](../../../ArkLib\Data\CodingTheory\ProximityGap\BCIKS20\AffineLines\Main.lean#L52) — Theorem 1.4 (Main Theorem — Correlated agreement over lines) in [BCIKS20]. Take a Reed-Solomon code
- `theorem RS_correlatedAgreement_affineLines` [ArkLib\Data\CodingTheory\ProximityGap\BoundaryCardResidualAffineLineRefutation.lean:19](../../../ArkLib\Data\CodingTheory\ProximityGap\BoundaryCardResidualAffineLineRefutation.lean#L19) — (no docstring)

### `RewindingExtractor` (2 declarations, 2 files)

- `abbrev DuplexSpongeFS.NARG.RewindingExtractor` [ArkLib\OracleReduction\FiatShamir\DuplexSponge\Basic.lean:155](../../../ArkLib\OracleReduction\FiatShamir\DuplexSponge\Basic.lean#L155) — Paper-facing alias for the rewinding extractor interface from CO25 Definition 3.8.
- `def Extractor.RewindingExtractor` [ArkLib\ToMathlib\RewindingExtractor.lean:115](../../../ArkLib\ToMathlib\RewindingExtractor.lean#L115) — A **rewinding extractor** for the 2-special-sound case: given the recorded prefix and **two** comple

### `Scheme` (2 declarations, 2 files)

- `structure Commitment.Scheme` [ArkLib\CommitmentScheme\Basic.lean:64](../../../ArkLib\CommitmentScheme\Basic.lean#L64) — A commitment scheme with key generation, commitment, and opening algorithms.
- `structure CommitmentScheme.Scheme` [ArkLib\CommitmentScheme\CommitmentScheme.lean:46](../../../ArkLib\CommitmentScheme\CommitmentScheme.lean#L46) — An ordinary commitment scheme.

### `SpongeState` (2 declarations, 2 files)

- `class SpongeState` [ArkLib\Data\Hash\DuplexSponge.lean:255](../../../ArkLib\Data\Hash\DuplexSponge.lean#L255) — Type class for the state of a cryptographic permutation used in the duplex sponge construction. Rust
- `abbrev DuplexSpongeFS.SpongeState` [ArkLib\OracleReduction\FiatShamir\DuplexSponge\Basic.lean:42](../../../ArkLib\OracleReduction\FiatShamir\DuplexSponge\Basic.lean#L42) — Paper-facing alias for the canonical duplex-sponge state used in CO25 Section 3.3.

### `SumcheckLensProjComplete` (2 declarations, 2 files)

- `def Logup.SumcheckLensProjComplete` [ArkLib\ProofSystem\Logup\Security\SumcheckCompletenessClose.lean:99](../../../ArkLib\ProofSystem\Logup\Security\SumcheckCompletenessClose.lean#L99) — **The `proj_complete` half of `OracleContext.Lens.IsComplete` for the LogUp sum-check lens.** Every
- `def SumcheckLensProjComplete` [ArkLib\ProofSystem\Logup\Security\SumcheckLensProjComplete.lean:16](../../../ArkLib\ProofSystem\Logup\Security\SumcheckLensProjComplete.lean#L16) — (no docstring)

### `SumcheckMultiplierParam` (2 declarations, 2 files)

- `structure Sumcheck.Structured.SumcheckMultiplierParam` [ArkLib\ProofSystem\Sumcheck\Structured.lean:85](../../../ArkLib\ProofSystem\Sumcheck\Structured.lean#L85) — Parameters describing how the round polynomial `H` is built from the witness `t`: `H = P · Q(t)`, wh
- `structure Sumcheck.Structured.Prismalinear.SumcheckMultiplierParam` [ArkLib\ProofSystem\Sumcheck\Structured\Prismalinear.lean:50](../../../ArkLib\ProofSystem\Sumcheck\Structured\Prismalinear.lean#L50) — Parameters describing how a *prismalinear* round polynomial `H = P · Q(t)` is built from the witness

### `SumcheckWitness` (2 declarations, 2 files)

- `abbrev RingSwitching.SumcheckWitness` [ArkLib\ProofSystem\RingSwitching\Prelude.lean:237](../../../ArkLib\ProofSystem\RingSwitching\Prelude.lean#L237) — (no docstring)
- `structure Sumcheck.Structured.SumcheckWitness` [ArkLib\ProofSystem\Sumcheck\Structured.lean:231](../../../ArkLib\ProofSystem\Sumcheck\Structured.lean#L231) — Witness for the structured sumcheck at round `i`: - `t'` — the original multilinear polynomial (the

### `TranscriptSimulator` (2 declarations, 2 files)

- `abbrev OracleReduction.TranscriptSimulator` [ArkLib\OracleReduction\Security\OracleZeroKnowledge.lean:38](../../../ArkLib\OracleReduction\Security\OracleZeroKnowledge.lean#L38) — Transcript simulators for oracle reductions are simulators for the associated non-oracle reduction,
- `def Reduction.TranscriptSimulator` [ArkLib\OracleReduction\Security\ZeroKnowledge.lean:62](../../../ArkLib\OracleReduction\Security\ZeroKnowledge.lean#L62) — A transcript simulator produces, from the input statement alone, a distribution over full transcript

### `Verifier.run` (2 declarations, 2 files)

- `def Interaction.Verifier.run` [ArkLib\Interaction\Reduction.lean:262](../../../ArkLib\Interaction\Reduction.lean#L262) — (no docstring)
- `def Verifier.run` [ArkLib\OracleReduction\Execution.lean:137](../../../ArkLib\OracleReduction\Execution.lean#L137) — Run the (non-oracle) verifier in an interactive reduction. It takes in the input statement and the t

### `WhirRbrKeystone` (2 declarations, 2 files)

- `def Core2Keystone.WhirRbrKeystone` [ArkLib\ProofSystem\Whir\KeystoneReduction.lean:80](../../../ArkLib\ProofSystem\Whir\KeystoneReduction.lean#L80) — Verbatim copy of `Issue113WHIR.WhirRbrKeystone` (`Whir/RbrBudgetAccounting.lean:238`): the `SoundOk`
- `def Issue113WHIR.WhirRbrKeystone` [ArkLib\ProofSystem\Whir\RbrBudgetAccounting.lean:253](../../../ArkLib\ProofSystem\Whir\RbrBudgetAccounting.lean#L253) — **Named residual (the genuine open per-round soundness math).** `WhirRbrKeystone` abstracts the per-

### `WitIn` (2 declarations, 2 files)

- `def RandomQuery.WitIn` [ArkLib\ProofSystem\Component\RandomQuery.lean:39](../../../ArkLib\ProofSystem\Component\RandomQuery.lean#L39) — (no docstring)
- `def Logup.WitIn` [ArkLib\ProofSystem\Logup\Common.lean:368](../../../ArkLib\ProofSystem\Logup\Common.lean#L368) — Protocol 2 has no private witness beyond the input oracles at this layer.

### `agree_add_hammingDist` (2 declarations, 2 files)

- `theorem CodeGeometry.agree_add_hammingDist` [ArkLib\Data\CodingTheory\CodeGeometry.lean:42](../../../ArkLib\Data\CodingTheory\CodeGeometry.lean#L42) — Agreement and Hamming distance partition the coordinate set.
- `theorem ArkLib.JohnsonBound.agree_add_hammingDist` [ArkLib\Data\CodingTheory\JohnsonBound\ListSize.lean:57](../../../ArkLib\Data\CodingTheory\JohnsonBound\ListSize.lean#L57) — Agreement plus Hamming distance equals the block length.

### `agreement` (2 declarations, 2 files)

- `def R14Derand.agreement` [ArkLib\Data\CodingTheory\ProximityGap\DerandomizationFrontier.lean:60](../../../ArkLib\Data\CodingTheory\ProximityGap\DerandomizationFrontier.lean#L60) — Absolute agreement: the number of coordinates where two words coincide.
- `def Round16SelfSimilar.agreement` [ArkLib\Data\CodingTheory\ProximityGap\SmoothDomainSelfSimilarity.lean:129](../../../ArkLib\Data\CodingTheory\ProximityGap\SmoothDomainSelfSimilarity.lean#L129) — Agreement count of a polynomial `g` with a word `w` over a domain `D`.

### `all_agree_ge_three` (2 declarations, 2 files)

- `theorem ArkLib.CodingTheory.TinyInteriorPin.all_agree_ge_three` [ArkLib\Data\CodingTheory\ProximityGap\ListInteriorDataPointF7.lean:148](../../../ArkLib\Data\CodingTheory\ProximityGap\ListInteriorDataPointF7.lean#L148) — **Interior agreement.** Every codeword in `L` agrees with the received word `w` on `≥ 3` coordinates
- `theorem ArkLib.CodingTheory.Round3SmoothF17.all_agree_ge_three` [ArkLib\Data\CodingTheory\ProximityGap\ListInteriorPinF17Subgroup.lean:181](../../../ArkLib\Data\CodingTheory\ProximityGap\ListInteriorPinF17Subgroup.lean#L181) — **Interior agreement.** Every codeword in `L` agrees with the received word `w` on `≥ 3` coordinates

### `answer_instDefault` (2 declarations, 2 files)

- `lemma RingSwitching.BatchingPhase.answer_instDefault` [ArkLib\ProofSystem\RingSwitching\BatchingPhase.lean:66](../../../ArkLib\ProofSystem\RingSwitching\BatchingPhase.lean#L66) — The default oracle interface (`OracleInterface.instDefault`, used by the ring-switching message orac
- `lemma ToyProblem.Spec.answer_instDefault` [ArkLib\ProofSystem\ToyProblem\Spec\General.lean:628](../../../ArkLib\ProofSystem\ToyProblem\Spec\General.lean#L628) — `answer` of the default oracle interface is the identity (the message itself).

### `appendRight` (2 declarations, 2 files)

- `def Interaction.OracleDecoration.QueryHandle.appendRight` [ArkLib\Interaction\Oracle\Core.lean:202](../../../ArkLib\Interaction\Oracle\Core.lean#L202) — (no docstring)
- `def ProtocolSpec.Transcript.appendRight` [ArkLib\OracleReduction\ProtocolSpec\TranscriptRecompose.lean:56](../../../ArkLib\OracleReduction\ProtocolSpec\TranscriptRecompose.lean#L56) — Append a full `pSpec₁` transcript and a *partial* `pSpec₂` transcript into a partial transcript for

### `append_left_injective` (2 declarations, 2 files)

- `theorem Fin.append_left_injective` [ArkLib\Data\Fin\Basic.lean:262](../../../ArkLib\Data\Fin\Basic.lean#L262) — (no docstring)
- `theorem ProtocolSpec.append_left_injective` [ArkLib\OracleReduction\ProtocolSpec\SeqCompose.lean:68](../../../ArkLib\OracleReduction\ProtocolSpec\SeqCompose.lean#L68) — (no docstring)

### `append_perfectCompleteness_msg_proof` (2 declarations, 2 files)

- `theorem OracleReduction.append_perfectCompleteness_msg_proof` [ArkLib\OracleReduction\Composition\Sequential\AppendPerfectCompletenessOracle.lean:81](../../../ArkLib\OracleReduction\Composition\Sequential\AppendPerfectCompletenessOracle.lean#L81) — **Oracle-level perfect-completeness keystone (message seam).** Perfect completeness of `R₁.append R₂
- `theorem Reduction.append_perfectCompleteness_msg_proof` [ArkLib\OracleReduction\Composition\Sequential\AppendPerfectCompletenessProof.lean:108](../../../ArkLib\OracleReduction\Composition\Sequential\AppendPerfectCompletenessProof.lean#L108) — (no docstring)

### `append_right_injective` (2 declarations, 2 files)

- `theorem Fin.append_right_injective` [ArkLib\Data\Fin\Basic.lean:270](../../../ArkLib\Data\Fin\Basic.lean#L270) — (no docstring)
- `theorem ProtocolSpec.append_right_injective` [ArkLib\OracleReduction\ProtocolSpec\SeqCompose.lean:78](../../../ArkLib\OracleReduction\ProtocolSpec\SeqCompose.lean#L78) — (no docstring)

### `averaging_crossover` (2 declarations, 2 files)

- `theorem R10Bracket.averaging_crossover` [ArkLib\Data\CodingTheory\ProximityGap\BestProvableBracket.lean:51](../../../ArkLib\Data\CodingTheory\ProximityGap\BestProvableBracket.lean#L51) — AVERAGING crossover. If the averaging list lower bound `maxList * q^t ≥ C(n,a)` holds (i.e. `maxList
- `theorem ArkLib.CodingTheory.Round9Bracket.averaging_crossover` [ArkLib\Data\CodingTheory\ProximityGap\DeltaStarAveragingBracket.lean:45](../../../ArkLib\Data\CodingTheory\ProximityGap\DeltaStarAveragingBracket.lean#L45) — **Averaging crossover (arithmetic core).** Given the pigeonhole averaging bound `C(n, k+t) ≤ q^t · L

### `averaging_list_lower_bound` (2 declarations, 2 files)

- `theorem ArkLib.CodingTheory.Round11RSAveraging.averaging_list_lower_bound` [ArkLib\Data\CodingTheory\ProximityGap\AveragingListLowerBoundRS.lean:204](../../../ArkLib\Data\CodingTheory\ProximityGap\AveragingListLowerBoundRS.lean#L204) — **Main theorem — the averaging list LOWER bound as a genuine RS statement.** Fix a finite field `F`,
- `theorem RSDeltaStar.averaging_list_lower_bound` [ArkLib\Data\CodingTheory\ProximityGap\RSAveragingDeltaStarUpper.lean:203](../../../ArkLib\Data\CodingTheory\ProximityGap\RSAveragingDeltaStarUpper.lean#L203) — **Averaging list lower bound from an injection.** An injection from the size-`(k+t)` subsets into `l

### `averaging_pigeonhole` (2 declarations, 2 files)

- `theorem ArkLib.CodingTheory.Round11RSAveraging.averaging_pigeonhole` [ArkLib\Data\CodingTheory\ProximityGap\AveragingListLowerBoundRS.lean:166](../../../ArkLib\Data\CodingTheory\ProximityGap\AveragingListLowerBoundRS.lean#L166) — Pigeonhole over the elementary-symmetric classes.  For ANY classifying map `cls` of the `a`-subsets
- `theorem RSDeltaStar.averaging_pigeonhole` [ArkLib\Data\CodingTheory\ProximityGap\RSAveragingDeltaStarUpper.lean:188](../../../ArkLib\Data\CodingTheory\ProximityGap\RSAveragingDeltaStarUpper.lean#L188) — **Averaging pigeonhole.** If `phi : alpha -> C x E` injects a finite family `S` whose first componen

### `badCount_udr_le` (2 declarations, 2 files)

- `theorem ProximityGap.UDRwire.badCount_udr_le` [ArkLib\Data\CodingTheory\ProximityGap\MCAUDRBound.lean:53](../../../ArkLib\Data\CodingTheory\ProximityGap\MCAUDRBound.lean#L53) — (no docstring)
- `theorem ProximityGap.UDR.badCount_udr_le` [ArkLib\Data\CodingTheory\ProximityGap\UDRBadCount.lean:74](../../../ArkLib\Data\CodingTheory\ProximityGap\UDRBadCount.lean#L74) — (no docstring)

### `badGamma_le` (2 declarations, 2 files)

- `theorem ProximityGap.UDRwire.badGamma_le` [ArkLib\Data\CodingTheory\ProximityGap\MCAUDRBound.lean:35](../../../ArkLib\Data\CodingTheory\ProximityGap\MCAUDRBound.lean#L35) — (no docstring)
- `theorem ProximityGap.UDR.badGamma_le` [ArkLib\Data\CodingTheory\ProximityGap\UDRBadCount.lean:56](../../../ArkLib\Data\CodingTheory\ProximityGap\UDRBadCount.lean#L56) — (no docstring)

### `badPolyAgreement` (2 declarations, 2 files)

- `def Issue29Ring.badPolyAgreement` [ArkLib\ProofSystem\RingSwitching\TraceTensorAlgebra.lean:39](../../../ArkLib\ProofSystem\RingSwitching\TraceTensorAlgebra.lean#L39) — **Named per-round residual = the weakened-KState bad event.** The prover message `p` differs from th
- `def KStateWeaken.badPolyAgreement` [ArkLib\ToMathlib\KStateWeaken.lean:70](../../../ArkLib\ToMathlib\KStateWeaken.lean#L70) — **Named per-round residual (weakened KState surface).** `badPolyAgreement r p q` is the bad event to

### `badStack` (2 declarations, 2 files)

- `def ProximityGap.MCAGSPrizeRefutation.badStack` [ArkLib\Data\CodingTheory\ProximityGap\MCAGSPrizeRefutation.lean:29](../../../ArkLib\Data\CodingTheory\ProximityGap\MCAGSPrizeRefutation.lean#L29) — The adversarial stack: row 0 = `w₀`, row 1 = `0`.
- `def badStack` [ArkLib\MCAGSRefutationCore_keep.lean:28](../../../ArkLib\MCAGSRefutationCore_keep.lean#L28) — The adversarial stack: row 0 = `w₀`, row 1 = `0`.

### `badStack_one` (2 declarations, 2 files)

- `theorem ProximityGap.MCAGSPrizeRefutation.badStack_one` [ArkLib\Data\CodingTheory\ProximityGap\MCAGSPrizeRefutation.lean:32](../../../ArkLib\Data\CodingTheory\ProximityGap\MCAGSPrizeRefutation.lean#L32) — (no docstring)
- `theorem badStack_one` [ArkLib\MCAGSRefutationCore_keep.lean:31](../../../ArkLib\MCAGSRefutationCore_keep.lean#L31) — (no docstring)

### `badStack_zero` (2 declarations, 2 files)

- `theorem ProximityGap.MCAGSPrizeRefutation.badStack_zero` [ArkLib\Data\CodingTheory\ProximityGap\MCAGSPrizeRefutation.lean:31](../../../ArkLib\Data\CodingTheory\ProximityGap\MCAGSPrizeRefutation.lean#L31) — (no docstring)
- `theorem badStack_zero` [ArkLib\MCAGSRefutationCore_keep.lean:30](../../../ArkLib\MCAGSRefutationCore_keep.lean#L30) — (no docstring)

### `badSumcheckEventProp` (2 declarations, 2 files)

- `def Binius.BinaryBasefold.badSumcheckEventProp` [ArkLib\ProofSystem\Binius\BinaryBasefold\Relations.lean:496](../../../ArkLib\ProofSystem\Binius\BinaryBasefold\Relations.lean#L496) — (no docstring)
- `def RingSwitching.SumcheckPhase.badSumcheckEventProp` [ArkLib\ProofSystem\RingSwitching\SumcheckPhase.lean:257](../../../ArkLib\ProofSystem\RingSwitching\SumcheckPhase.lean#L257) — **Named weakened-KState bad event for one ring-switching sumcheck round.** The prover's degree-`≤ 2`

### `batchingCoreRbrKnowledgeError` (2 declarations, 2 files)

- `def Binius.FRIBinius.FullFRIBinius.batchingCoreRbrKnowledgeError` [ArkLib\ProofSystem\Binius\FRIBinius\General.lean:217](../../../ArkLib\ProofSystem\Binius\FRIBinius\General.lean#L217) — Combined RBR knowledge error for batching + core interaction.
- `def RingSwitching.FullRingSwitching.batchingCoreRbrKnowledgeError` [ArkLib\ProofSystem\RingSwitching\General.lean:225](../../../ArkLib\ProofSystem\RingSwitching\General.lean#L225) — (no docstring)

### `batchingCoreReduction` (2 declarations, 2 files)

- `def Binius.FRIBinius.FullFRIBinius.batchingCoreReduction` [ArkLib\ProofSystem\Binius\FRIBinius\General.lean:95](../../../ArkLib\ProofSystem\Binius\FRIBinius\General.lean#L95) — (no docstring)
- `def RingSwitching.FullRingSwitching.batchingCoreReduction` [ArkLib\ProofSystem\RingSwitching\General.lean:66](../../../ArkLib\ProofSystem\RingSwitching\General.lean#L66) — (no docstring)

### `batchingCoreVerifier` (2 declarations, 2 files)

- `def Binius.FRIBinius.FullFRIBinius.batchingCoreVerifier` [ArkLib\ProofSystem\Binius\FRIBinius\General.lean:77](../../../ArkLib\ProofSystem\Binius\FRIBinius\General.lean#L77) — (no docstring)
- `def RingSwitching.FullRingSwitching.batchingCoreVerifier` [ArkLib\ProofSystem\RingSwitching\General.lean:42](../../../ArkLib\ProofSystem\RingSwitching\General.lean#L42) — (no docstring)

### `binomial_separation` (2 declarations, 2 files)

- `theorem ProximityGap.MultiplicativeRigidity.binomial_separation` [ArkLib\Data\CodingTheory\ProximityGap\MultiplicativeRigidityFiber.lean:154](../../../ArkLib\Data\CodingTheory\ProximityGap\MultiplicativeRigidityFiber.lean#L154) — **Binomial separation.** If `0 < b < a ≤ k`, then two distinct monomials `c₁ * X ^ a` and `c₂ * X ^
- `theorem MultiplicativeRigidity.binomial_separation` [ArkLib\Data\CodingTheory\ProximityGap\MultiplicativeRigidityZMod.lean:170](../../../ArkLib\Data\CodingTheory\ProximityGap\MultiplicativeRigidityZMod.lean#L170) — **Binomial separation.** Packaging of coset rigidity in the form the dossier consumes: if `b < a < k

### `c0_ne_c1` (2 declarations, 2 files)

- `theorem JohnsonBound.FamilyRefutation.c0_ne_c1` [ArkLib\Data\CodingTheory\JohnsonBound\FamilyRefutation.lean:39](../../../ArkLib\Data\CodingTheory\JohnsonBound\FamilyRefutation.lean#L39) — The three codewords are pairwise distinct.
- `theorem JohnsonBound.JqlRefutation.c0_ne_c1` [ArkLib\Data\CodingTheory\JohnsonBound\FamilyRefutationComplete.lean:79](../../../ArkLib\Data\CodingTheory\JohnsonBound\FamilyRefutationComplete.lean#L79) — The three codewords are pairwise distinct.

### `c0_ne_c2` (2 declarations, 2 files)

- `theorem JohnsonBound.FamilyRefutation.c0_ne_c2` [ArkLib\Data\CodingTheory\JohnsonBound\FamilyRefutation.lean:40](../../../ArkLib\Data\CodingTheory\JohnsonBound\FamilyRefutation.lean#L40) — (no docstring)
- `theorem JohnsonBound.JqlRefutation.c0_ne_c2` [ArkLib\Data\CodingTheory\JohnsonBound\FamilyRefutationComplete.lean:80](../../../ArkLib\Data\CodingTheory\JohnsonBound\FamilyRefutationComplete.lean#L80) — (no docstring)

### `c1_ne_c2` (2 declarations, 2 files)

- `theorem JohnsonBound.FamilyRefutation.c1_ne_c2` [ArkLib\Data\CodingTheory\JohnsonBound\FamilyRefutation.lean:41](../../../ArkLib\Data\CodingTheory\JohnsonBound\FamilyRefutation.lean#L41) — (no docstring)
- `theorem JohnsonBound.JqlRefutation.c1_ne_c2` [ArkLib\Data\CodingTheory\JohnsonBound\FamilyRefutationComplete.lean:81](../../../ArkLib\Data\CodingTheory\JohnsonBound\FamilyRefutationComplete.lean#L81) — (no docstring)

### `c6_isRS` (2 declarations, 2 files)

- `lemma ArkLib.CodingTheory.TinyInteriorK3.c6_isRS` [ArkLib\Data\CodingTheory\ProximityGap\ListInteriorPinF11K3.lean:137](../../../ArkLib\Data\CodingTheory\ProximityGap\ListInteriorPinF11K3.lean#L137) — (no docstring)
- `lemma ArkLib.CodingTheory.Round3SmoothF17.c6_isRS` [ArkLib\Data\CodingTheory\ProximityGap\ListInteriorPinF17Subgroup.lean:148](../../../ArkLib\Data\CodingTheory\ProximityGap\ListInteriorPinF17Subgroup.lean#L148) — (no docstring)

### `card` (2 declarations, 2 files)

- `theorem Probability.SizeSubset.card` [ArkLib\Data\Probability\Combinatorial.lean:47](../../../ArkLib\Data\Probability\Combinatorial.lean#L47) — The number of size-`n` subsets of a finite type is `\|α\| choose n`.
- `theorem Probability.SizedSubset.card` [ArkLib\Data\Probability\UniformSubset.lean:43](../../../ArkLib\Data\Probability\UniformSubset.lean#L43) — (no docstring)

### `card_allQueriesIn` (2 declarations, 2 files)

- `theorem Issue14Scratch.card_allQueriesIn` [ArkLib\ProofSystem\BatchedFri\QueryRoundAnalysis.lean:35](../../../ArkLib\ProofSystem\BatchedFri\QueryRoundAnalysis.lean#L35) — (= `Fri.QueryRound.card_allQueriesIn`) The number of length-`t` query tuples landing entirely in `G`
- `theorem Fri.QueryRound.card_allQueriesIn` [ArkLib\ProofSystem\BatchedFri\Security.lean:353](../../../ArkLib\ProofSystem\BatchedFri\Security.lean#L353) — The number of length-`t` query tuples landing entirely in a set `G` is `\|G\| ^ t`. This counts the ac

### `card_filter_eval_eq_le_natDegree` (2 declarations, 2 files)

- `theorem Issue29Ring.card_filter_eval_eq_le_natDegree` [ArkLib\ProofSystem\RingSwitching\TraceTensorAlgebra.lean:52](../../../ArkLib\ProofSystem\RingSwitching\TraceTensorAlgebra.lean#L52) — **Root-counting core (Schwartz–Zippel, finite-field form).** For two distinct polynomials, the set o
- `theorem KStateWeaken.card_filter_eval_eq_le_natDegree` [ArkLib\ToMathlib\KStateWeaken.lean:91](../../../ArkLib\ToMathlib\KStateWeaken.lean#L91) — **Root-counting core (CompPoly-free).** For two *distinct* polynomials, the set of challenges on whi

### `card_filter_forall_pi` (2 declarations, 2 files)

- `lemma OutOfDomSmpl.card_filter_forall_pi` [ArkLib\ProofSystem\Stir\OutOfDomSmpl.lean:71](../../../ArkLib\ProofSystem\Stir\OutOfDomSmpl.lean#L71) — Counting a coordinatewise event: the tuples satisfying `Q` in every coordinate form the `piFinset` o
- `theorem card_filter_forall_pi` [ArkLib\ToMathlib\CountingAgreementBricks.lean:76](../../../ArkLib\ToMathlib\CountingAgreementBricks.lean#L76) — Count of length-`s` tuples whose every coordinate satisfies `Q` equals `(#Q)^s`.

### `card_filter_ne_zero` (2 declarations, 2 files)

- `theorem ArkLib.CodingTheory.BallVolume.card_filter_ne_zero` [ArkLib\Data\CodingTheory\ProximityGap\BallVolume.lean:33](../../../ArkLib\Data\CodingTheory\ProximityGap\BallVolume.lean#L33) — The number of nonzero field elements is `q - 1`.
- `theorem ArkLib.RandomLinearCode.card_filter_ne_zero` [ArkLib\Data\CodingTheory\RandomLinearCodeFirstMoment.lean:53](../../../ArkLib\Data\CodingTheory\RandomLinearCodeFirstMoment.lean#L53) — The number of nonzero messages is `qᵏ − 1`.

### `card_wordStack_eq` (2 declarations, 2 files)

- `theorem CS25.card_wordStack_eq` [ArkLib\Data\CodingTheory\ProximityGap\CS25JointProxBound.lean:255](../../../ArkLib\Data\CodingTheory\ProximityGap\CS25JointProxBound.lean#L255) — **`#stacks = Q^n`** for the interleaved alphabet `Q = \|κ→A\|`, `n = \|ι\|`.
- `theorem CodingTheory.card_wordStack_eq` [ArkLib\Data\CodingTheory\ProximityGap\CS25SecondMomentIsolation.lean:38](../../../ArkLib\Data\CodingTheory\ProximityGap\CS25SecondMomentIsolation.lean#L38) — The number of two-row stacks over `ι → F` equals `\|ι→F\|²`.

### `charSum` (2 declarations, 2 files)

- `def ArkLib.CodingTheory.HasseWeilInstances.charSum` [ArkLib\Data\CodingTheory\ProximityGap\HasseWeilBoundInstances.lean:88](../../../ArkLib\Data\CodingTheory\ProximityGap\HasseWeilBoundInstances.lean#L88) — The complete quadratic character sum `∑ₓ χ(f x)`.
- `def ArkLib.ProximityGap.MomentCollisionSpectral.charSum` [ArkLib\Data\CodingTheory\ProximityGap\MomentCollisionSpectral.lean:66](../../../ArkLib\Data\CodingTheory\ProximityGap\MomentCollisionSpectral.lean#L66) — The Fourier coefficient `T ψ = ∑_S ψ (stat S)`.

### `choose_le_succ_succ` (2 declarations, 2 files)

- `theorem Round14ConstantGap.choose_le_succ_succ` [ArkLib\Data\CodingTheory\ProximityGap\DeltaStarConstantGapBelowCapacity.lean:51](../../../ArkLib\Data\CodingTheory\ProximityGap\DeltaStarConstantGapBelowCapacity.lean#L51) — One-step Pascal: `C(n, m) ≤ C(n+1, m+1)` (the RHS is `C(n,m) + C(n,m+1)`).
- `theorem R15Bracket.choose_le_succ_succ` [ArkLib\Data\CodingTheory\ProximityGap\PrizeScaleBracketFull.lean:278](../../../ArkLib\Data\CodingTheory\ProximityGap\PrizeScaleBracketFull.lean#L278) — (no docstring)

### `choose_prime_pow_cast_eq_zero` (2 declarations, 2 files)

- `lemma ArkLib.ProximityGap.Issue232Bricks.choose_prime_pow_cast_eq_zero` [ArkLib\Data\CodingTheory\ProximityGap\Issue232VerifiedBricks.lean:73](../../../ArkLib\Data\CodingTheory\ProximityGap\Issue232VerifiedBricks.lean#L73) — **Char-`p` middle binomial vanishing.** In a commutative ring of prime characteristic `p`, `C(p^a, m
- `lemma ProximityGap.LinearizedPolynomialHasse.choose_prime_pow_cast_eq_zero` [ArkLib\Data\CodingTheory\ProximityGap\LinearizedPolynomialHasse.lean:70](../../../ArkLib\Data\CodingTheory\ProximityGap\LinearizedPolynomialHasse.lean#L70) — **Char-`p` middle binomial vanishing.** For a commutative ring of characteristic `p` (prime), `(p^a)

### `cliqueLocator_natDegree` (2 declarations, 2 files)

- `theorem Round19Clique.cliqueLocator_natDegree` [ArkLib\Data\CodingTheory\ProximityGap\Conjecture41CliqueBeachhead.lean:124](../../../ArkLib\Data\CodingTheory\ProximityGap\Conjecture41CliqueBeachhead.lean#L124) — The clique locator has `natDegree = \|W\| − 1` (product of `\|W\|−1` monic linears).
- `theorem Round20CliqueKernel.cliqueLocator_natDegree` [ArkLib\Data\CodingTheory\ProximityGap\Conjecture41CliqueKernelStructure.lean:84](../../../ArkLib\Data\CodingTheory\ProximityGap\Conjecture41CliqueKernelStructure.lean#L84) — Locator degree: `natDegree Λ_{E_α} = \|W\| − 1` for `α ∈ W`.

### `code` (2 declarations, 2 files)

- `def ArkLib.ProximityGap.Round3SubgroupSumsetDirect.code` [ArkLib\Data\CodingTheory\ProximityGap\SubgroupSumsetThreePowUpper.lean:112](../../../ArkLib\Data\CodingTheory\ProximityGap\SubgroupSumsetThreePowUpper.lean#L112) — The `{−1,0,1}` coefficient code of a full-domain subset `S ⊆ Fin (N+N)` at low index `j`, as an elem
- `def ReedSolomon.code` [ArkLib\Data\CodingTheory\ReedSolomon.lean:62](../../../ArkLib\Data\CodingTheory\ReedSolomon.lean#L62) — The Reed-Solomon code for polynomials of degree less than `deg` and evaluation points `domain`.

### `coeffHom` (2 declarations, 2 files)

- `def ProximityPrize.BCIKS20.GammaGenuine.coeffHom` [ArkLib\Data\CodingTheory\ProximityGap\BCIKS20\GammaGenuine.lean:87](../../../ArkLib\Data\CodingTheory\ProximityGap\BCIKS20\GammaGenuine.lean#L87) — The per-`Y`-coefficient ring hom `F[X][Y] → (𝕃 H)⟦X⟧`: recenter the `X`-layer at `x₀` (`taylorAlgHom
- `def ArkLib.Lattices.CyclotomicModulus.Rq.coeffHom` [ArkLib\Data\Lattices\CyclotomicRing\Rq.lean:175](../../../ArkLib\Data\Lattices\CyclotomicRing\Rq.lean#L175) — Reading off the `k`-th coefficient of the underlying polynomial, as an additive homomorphism `Rq Φ →

### `coeff_S_eq_zero_of_lt` (2 declarations, 2 files)

- `theorem ProximityPrize.HenselExistence.coeff_S_eq_zero_of_lt` [ArkLib\Data\Polynomial\HenselExistence.lean:203](../../../ArkLib\Data\Polynomial\HenselExistence.lean#L203) — The `t`-th partial sum is supported on `[0, t]`: every coefficient above order `t` vanishes. (`S t`
- `theorem ProximityPrize.HenselSeriesCoeff.coeff_S_eq_zero_of_lt` [ArkLib\Data\Polynomial\HenselSeriesCoeff.lean:280](../../../ArkLib\Data\Polynomial\HenselSeriesCoeff.lean#L280) — `S t` is supported on `[0, t]`: every coefficient above order `t` vanishes.

### `coeff_S_stable` (2 declarations, 2 files)

- `theorem ProximityPrize.HenselExistence.coeff_S_stable` [ArkLib\Data\Polynomial\HenselExistence.lean:214](../../../ArkLib\Data\Polynomial\HenselExistence.lean#L214) — Coefficient stability: for `j ≤ t`, `coeff j (S t) = coeff j (S j)`. The diagonal value is reached a
- `theorem ProximityPrize.HenselSeriesCoeff.coeff_S_stable` [ArkLib\Data\Polynomial\HenselSeriesCoeff.lean:290](../../../ArkLib\Data\Polynomial\HenselSeriesCoeff.lean#L290) — Coefficient stability: for `j ≤ t`, `coeff j (S t) = coeff j (S j)`.

### `coeff_S_succ_of_le` (2 declarations, 2 files)

- `theorem ProximityPrize.HenselExistence.coeff_S_succ_of_le` [ArkLib\Data\Polynomial\HenselExistence.lean:197](../../../ArkLib\Data\Polynomial\HenselExistence.lean#L197) — Adding the order-`(t+1)` monomial leaves coefficients `≤ t` unchanged.
- `theorem ProximityPrize.HenselSeriesCoeff.coeff_S_succ_of_le` [ArkLib\Data\Polynomial\HenselSeriesCoeff.lean:275](../../../ArkLib\Data\Polynomial\HenselSeriesCoeff.lean#L275) — Adding the order-`(t+1)` monomial leaves coefficients `≤ t` unchanged.

### `coeff_aeval_eq_sum_range` (2 declarations, 2 files)

- `theorem ProximityPrize.HenselExistence.coeff_aeval_eq_sum_range` [ArkLib\Data\Polynomial\HenselExistence.lean:65](../../../ArkLib\Data\Polynomial\HenselExistence.lean#L65) — Local copy of `NewtonLinearization.coeff_aeval_eq_sum_range`: `coeff n (aeval γ P) = ∑_{i ≤ deg P} P
- `theorem ProximityPrize.NewtonLinearization.coeff_aeval_eq_sum_range` [ArkLib\Data\Polynomial\NewtonLinearization.lean:166](../../../ArkLib\Data\Polynomial\NewtonLinearization.lean#L166) — Local restatement of the `HasSubst`-free `aeval`-coefficient expansion (this is `ProximityPrize.coef

### `coeff_aeval_sub_at` (2 declarations, 2 files)

- `theorem ProximityPrize.HenselExistence.coeff_aeval_sub_at` [ArkLib\Data\Polynomial\HenselExistence.lean:147](../../../ArkLib\Data\Polynomial\HenselExistence.lean#L147) — Local copy of `NewtonLinearization.coeff_aeval_sub_at` (the `P'(c)`-linear response). For `P : R[X]`
- `theorem ProximityPrize.NewtonLinearization.coeff_aeval_sub_at` [ArkLib\Data\Polynomial\NewtonLinearization.lean:186](../../../ArkLib\Data\Polynomial\NewtonLinearization.lean#L186) — **Newton/Hensel linearization of the composed series (P2 form).** For a polynomial `P` over `R` and

### `coeff_toPoly` (2 declarations, 2 files)

- `theorem ArkLib.Lattices.CyclotomicModulus.coeff_toPoly` [ArkLib\Data\Lattices\CyclotomicRing\Galois\Automorphism.lean:124](../../../ArkLib\Data\Lattices\CyclotomicRing\Galois\Automorphism.lean#L124) — **(S3)** Coefficient bridge: the Mathlib and `CPolynomial` coefficients agree.
- `lemma UniPoly.coeff_toPoly` [ArkLib\Data\UniPoly\Basic.lean:785](../../../ArkLib\Data\UniPoly\Basic.lean#L785) — characterize `p.toPoly` by showing that its coefficients are exactly the coefficients of `p`

### `coeff_γ` (2 declarations, 2 files)

- `theorem ProximityPrize.HenselExistence.coeff_γ` [ArkLib\Data\Polynomial\HenselExistence.lean:227](../../../ArkLib\Data\Polynomial\HenselExistence.lean#L227) — (no docstring)
- `theorem ProximityPrize.HenselSeriesCoeff.coeff_γ` [ArkLib\Data\Polynomial\HenselSeriesCoeff.lean:303](../../../ArkLib\Data\Polynomial\HenselSeriesCoeff.lean#L303) — (no docstring)

### `coeff_γ_eq_S` (2 declarations, 2 files)

- `theorem ProximityPrize.HenselExistence.coeff_γ_eq_S` [ArkLib\Data\Polynomial\HenselExistence.lean:236](../../../ArkLib\Data\Polynomial\HenselExistence.lean#L236) — `γ` agrees with the `t`-th partial sum below order `t + 1`.
- `theorem ProximityPrize.HenselSeriesCoeff.coeff_γ_eq_S` [ArkLib\Data\Polynomial\HenselSeriesCoeff.lean:312](../../../ArkLib\Data\Polynomial\HenselSeriesCoeff.lean#L312) — `γ` agrees with the `t`-th partial sum below order `t + 1`.

### `coeffs` (2 declarations, 2 files)

- `def Polynomial.Bivariate.coeffs` [ArkLib\Data\Polynomial\Bivariate.lean:34](../../../ArkLib\Data\Polynomial\Bivariate.lean#L34) — The set of coefficients of a bivariate polynomial.
- `def UniPoly.coeffs` [ArkLib\Data\UniPoly\Basic.lean:41](../../../ArkLib\Data\UniPoly\Basic.lean#L41) — (no docstring)

### `collision` (2 declarations, 2 files)

- `theorem ArkLib.CodingTheory.Collision.collision` [ArkLib\Data\CodingTheory\ProximityGap\CollisionLemma.lean:40](../../../ArkLib\Data\CodingTheory\ProximityGap\CollisionLemma.lean#L40) — **Collision lemma.** If `P` is `r`-close to `u₀+γ·u₁` and `P'` is `r`-close to `u₀+γ'·u₁` with `γ ≠
- `def ArkLib.ProximityGap.MomentCollisionSpectral.collision` [ArkLib\Data\CodingTheory\ProximityGap\MomentCollisionSpectral.lean:62](../../../ArkLib\Data\CodingTheory\ProximityGap\MomentCollisionSpectral.lean#L62) — Statistic-collision count for an arbitrary finite-abelian-group-valued statistic.

### `computeRoundPoly` (2 declarations, 2 files)

- `def Sumcheck.Structured.computeRoundPoly` [ArkLib\ProofSystem\Sumcheck\Structured.lean:130](../../../ArkLib\ProofSystem\Sumcheck\Structured.lean#L130) — The general round polynomial `H = P · Q(t)`, where `P = param.multpoly ctx` is the public multilinea
- `def Sumcheck.Structured.Prismalinear.computeRoundPoly` [ArkLib\ProofSystem\Sumcheck\Structured\Prismalinear.lean:70](../../../ArkLib\ProofSystem\Sumcheck\Structured\Prismalinear.lean#L70) — The *prismalinear* round polynomial `H = P · Q(t)`, where `P = param.multpoly ctx` has per-variable

### `constCode` (2 declarations, 2 files)

- `def ProximityGap.MCANearCapacity.constCode` [ArkLib\Data\CodingTheory\ProximityGap\MCANearCapacityLowerBound.lean:59](../../../ArkLib\Data\CodingTheory\ProximityGap\MCANearCapacityLowerBound.lean#L59) — The length-`n` constant (repetition) Reed–Solomon code `RS[ZMod p, ·, 1]`: the degree-`<1` polynomia
- `def ProximityGap.MCAWitnessSpread.Example.constCode` [ArkLib\Data\CodingTheory\ProximityGap\MCAWitnessSpreadExample.lean:46](../../../ArkLib\Data\CodingTheory\ProximityGap\MCAWitnessSpreadExample.lean#L46) — The constant-functions (repetition) code over `ZMod 3` on three coordinates. It is the rate-`1/3` Re

### `constantCoeff_γ` (2 declarations, 2 files)

- `theorem ProximityPrize.HenselExistence.constantCoeff_γ` [ArkLib\Data\Polynomial\HenselExistence.lean:231](../../../ArkLib\Data\Polynomial\HenselExistence.lean#L231) — The constant coefficient of the Newton root is the prescribed root `c`.
- `theorem ProximityPrize.HenselSeriesCoeff.constantCoeff_γ` [ArkLib\Data\Polynomial\HenselSeriesCoeff.lean:307](../../../ArkLib\Data\Polynomial\HenselSeriesCoeff.lean#L307) — The constant coefficient of the Newton root is the prescribed root `c`.

### `coord` (2 declarations, 2 files)

- `def CodingTheory.ExtensionFieldPresentation.coord` [ArkLib\Data\CodingTheory\ExtensionCodes.lean:100](../../../ArkLib\Data\CodingTheory\ExtensionCodes.lean#L100) — The `j`-th coordinate `φᵢ : F →ₗ[B] B` of an extension-field presentation, as a `B`-linear map.
- `def MuTwoPowDerandRefutation.coord` [ArkLib\Data\CodingTheory\ProximityGap\MuTwoPowDerandRIMRank.lean:49](../../../ArkLib\Data\CodingTheory\ProximityGap\MuTwoPowDerandRIMRank.lean#L49) — The coordinate (in `Fin 8`) of the edge represented by each row of `rimMatrix`.

### `coreInteractionOracleRbrKnowledgeError` (2 declarations, 2 files)

- `def coreInteractionOracleRbrKnowledgeError` [ArkLib\ProofSystem\Binius\BinaryBasefold\CoreInteractionPhase.lean:1166](../../../ArkLib\ProofSystem\Binius\BinaryBasefold\CoreInteractionPhase.lean#L1166) — (no docstring)
- `def Binius.FRIBinius.CoreInteractionPhase.coreInteractionOracleRbrKnowledgeError` [ArkLib\ProofSystem\Binius\FRIBinius\CoreInteractionPhase.lean:1717](../../../ArkLib\ProofSystem\Binius\FRIBinius\CoreInteractionPhase.lean#L1717) — (no docstring)

### `coreInteractionOracleReduction_perfectCompleteness` (2 declarations, 2 files)

- `theorem coreInteractionOracleReduction_perfectCompleteness` [ArkLib\ProofSystem\Binius\BinaryBasefold\CoreInteractionPhase.lean:1137](../../../ArkLib\ProofSystem\Binius\BinaryBasefold\CoreInteractionPhase.lean#L1137) — (no docstring)
- `theorem Binius.FRIBinius.CoreInteractionPhase.coreInteractionOracleReduction_perfectCompleteness` [ArkLib\ProofSystem\Binius\FRIBinius\CoreInteractionPhase.lean:1677](../../../ArkLib\ProofSystem\Binius\FRIBinius\CoreInteractionPhase.lean#L1677) — Perfect completeness for the core interaction oracle reduction

### `coreInteractionOracleVerifier_rbrKnowledgeSoundness` (2 declarations, 2 files)

- `theorem coreInteractionOracleVerifier_rbrKnowledgeSoundness` [ArkLib\ProofSystem\Binius\BinaryBasefold\CoreInteractionPhase.lean:1174](../../../ArkLib\ProofSystem\Binius\BinaryBasefold\CoreInteractionPhase.lean#L1174) — (no docstring)
- `theorem Binius.FRIBinius.CoreInteractionPhase.coreInteractionOracleVerifier_rbrKnowledgeSoundness` [ArkLib\ProofSystem\Binius\FRIBinius\CoreInteractionPhase.lean:1726](../../../ArkLib\ProofSystem\Binius\FRIBinius\CoreInteractionPhase.lean#L1726) — Round-by-round knowledge soundness for the core interaction oracle verifier

### `correlatedAgreement_affine_curves_of_lattice_data` (2 declarations, 2 files)

- `theorem ArkLib.BoundaryCardResidual.correlatedAgreement_affine_curves_of_lattice_data` [ArkLib\Data\CodingTheory\ProximityGap\BoundaryCardResidual.lean:877](../../../ArkLib\Data\CodingTheory\ProximityGap\BoundaryCardResidual.lean#L877) — [BCIKS20] Theorem 1.5 consuming concrete square-lattice data. This is the data-level counterpart of
- `theorem ArkLib.BoundaryDischarge.correlatedAgreement_affine_curves_of_lattice_data` [ArkLib\ToMathlib\BoundaryDischarge.lean:542](../../../ArkLib\ToMathlib\BoundaryDischarge.lean#L542) — The affine-curves keystone can consume the exact lattice branch through the smaller `BoundaryCardLat

### `correlatedAgreement_affine_curves_of_lattice_data_isSquare` (2 declarations, 2 files)

- `theorem ArkLib.BoundaryCardResidual.correlatedAgreement_affine_curves_of_lattice_data_isSquare` [ArkLib\Data\CodingTheory\ProximityGap\BoundaryCardResidual.lean:993](../../../ArkLib\Data\CodingTheory\ProximityGap\BoundaryCardResidual.lean#L993) — Curve-facing square-endpoint adapter from concrete lattice data. This is the data-level counterpart
- `theorem ArkLib.BoundaryDischarge.correlatedAgreement_affine_curves_of_lattice_data_isSquare` [ArkLib\ToMathlib\BoundaryDischarge.lean:605](../../../ArkLib\ToMathlib\BoundaryDischarge.lean#L605) — Curve-facing square-endpoint adapter from `BoundaryCardLatticeData`.  This is the lattice-data count

### `coset` (2 declarations, 2 files)

- `def ArkLib.ProximityGap.CosetConcentration.coset` [ArkLib\Data\CodingTheory\ProximityGap\CosetPowerSumConcentration.lean:92](../../../ArkLib\Data\CodingTheory\ProximityGap\CosetPowerSumConcentration.lean#L92) — The coset `g · ⟨ζ⟩` as a finset (image of `range h` under `l ↦ g·ζ^l`).
- `def ArkLib.ProximityGap.HybridDepthNoGo.coset` [ArkLib\Data\CodingTheory\ProximityGap\HybridConcentrationDepthNoGo.lean:99](../../../ArkLib\Data\CodingTheory\ProximityGap\HybridConcentrationDepthNoGo.lean#L99) — The deep coset as a finset; for a primitive `h`-th root and `g ≠ 0` it has exactly `h` elements and

### `coset_finset_powersum_zero` (2 declarations, 2 files)

- `theorem ArkLib.ProximityGap.CosetConcentration.coset_finset_powersum_zero` [ArkLib\Data\CodingTheory\ProximityGap\CosetPowerSumConcentration.lean:104](../../../ArkLib\Data\CodingTheory\ProximityGap\CosetPowerSumConcentration.lean#L104) — Power sum of degree `i` (`1 ≤ i < h`) over a single coset finset is `0`.
- `theorem ArkLib.ProximityGap.HybridDepthNoGo.coset_finset_powersum_zero` [ArkLib\Data\CodingTheory\ProximityGap\HybridConcentrationDepthNoGo.lean:109](../../../ArkLib\Data\CodingTheory\ProximityGap\HybridConcentrationDepthNoGo.lean#L109) — (no docstring)

### `coset_powersum_zero` (2 declarations, 2 files)

- `theorem ArkLib.ProximityGap.CosetConcentration.coset_powersum_zero` [ArkLib\Data\CodingTheory\ProximityGap\CosetPowerSumConcentration.lean:74](../../../ArkLib\Data\CodingTheory\ProximityGap\CosetPowerSumConcentration.lean#L74) — **Coset power-sum vanishing (load-bearing).** `ζ ^ h = 1`, `ζ ^ i ≠ 1` ⟹ the `i`-th power sum over t
- `theorem ArkLib.ProximityGap.HybridDepthNoGo.coset_powersum_zero` [ArkLib\Data\CodingTheory\ProximityGap\HybridConcentrationDepthNoGo.lean:80](../../../ArkLib\Data\CodingTheory\ProximityGap\HybridConcentrationDepthNoGo.lean#L80) — **Coset power-sum vanishing (the deep atom).** `ζ^h = 1`, `ζ^i ≠ 1` ⟹ the `i`-th power sum over the

### `coset_powersum_zero_of_lt` (2 declarations, 2 files)

- `theorem ArkLib.ProximityGap.CosetConcentration.coset_powersum_zero_of_lt` [ArkLib\Data\CodingTheory\ProximityGap\CosetPowerSumConcentration.lean:84](../../../ArkLib\Data\CodingTheory\ProximityGap\CosetPowerSumConcentration.lean#L84) — **All low power-sums vanish on a coset.** Primitive `h`-th root `ζ`, `1 ≤ i < h`.
- `theorem ArkLib.ProximityGap.HybridDepthNoGo.coset_powersum_zero_of_lt` [ArkLib\Data\CodingTheory\ProximityGap\HybridConcentrationDepthNoGo.lean:90](../../../ArkLib\Data\CodingTheory\ProximityGap\HybridConcentrationDepthNoGo.lean#L90) — A coset of a primitive `h`-th root kills the first `h−1` power sums.

### `decidablePred_badPolyAgreement` (2 declarations, 2 files)

- `instance Issue29Ring.decidablePred_badPolyAgreement` [ArkLib\ProofSystem\RingSwitching\TraceTensorAlgebra.lean:42](../../../ArkLib\ProofSystem\RingSwitching\TraceTensorAlgebra.lean#L42) — (no docstring)
- `instance KStateWeaken.decidablePred_badPolyAgreement` [ArkLib\ToMathlib\KStateWeaken.lean:74](../../../ArkLib\ToMathlib\KStateWeaken.lean#L74) — (no docstring)

### `decoder` (2 declarations, 2 files)

- `def BerlekampWelch.decoder` [ArkLib\Data\CodingTheory\BerlekampWelch\BerlekampWelch.lean:52](../../../ArkLib\Data\CodingTheory\BerlekampWelch\BerlekampWelch.lean#L52) — Berlekamp-Welch decoder for Reed-Solomon codes. Given received codeword evaluations with potential e
- `def GuruswamiSudan.decoder` [ArkLib\Data\CodingTheory\GuruswamiSudan\GuruswamiSudan.lean:113](../../../ArkLib\Data\CodingTheory\GuruswamiSudan\GuruswamiSudan.lean#L113) — Specification-level Guruswami-Sudan decoder. This finite-field specification enumerates all degree-`

### `degree` (2 declarations, 2 files)

- `def UniPoly.degree` [ArkLib\Data\UniPoly\Basic.lean:66](../../../ArkLib\Data\UniPoly\Basic.lean#L66) — Return the degree of a `UniPoly`.
- `def StirIOP.degree` [ArkLib\ProofSystem\Stir\MainThm.lean:45](../../../ArkLib\ProofSystem\Stir\MainThm.lean#L45) — **Degree after `i` folds:** The starting degree is `deg`; every fold divides it by `foldingParamⱼ (j

### `dist` (2 declarations, 2 files)

- `def Code.dist` [ArkLib\Data\CodingTheory\Basic\Distance.lean:169](../../../ArkLib\Data\CodingTheory\Basic\Distance.lean#L169) — The Hamming distance of a code `C` is the minimum Hamming distance between any two distinct elements
- `def dist` [ArkLib\Data\CodingTheory\Quarantine\CandidateHypotheses.lean:21](../../../ArkLib\Data\CodingTheory\Quarantine\CandidateHypotheses.lean#L21) — (no docstring)

### `dom` (2 declarations, 2 files)

- `def ProximityGap.MCANearCapacityQuadratic.dom` [ArkLib\Data\CodingTheory\ProximityGap\MCANearCapacityQuadratic.lean:80](../../../ArkLib\Data\CodingTheory\ProximityGap\MCANearCapacityQuadratic.lean#L80) — The arithmetic evaluation domain `i ↦ (i : ZMod p)`, an embedding once `n ≤ p`.
- `def ArkLib.ProximityGap.RSPrizeDataPoint.dom` [ArkLib\Data\CodingTheory\ProximityGap\RSListSizeDataPoint.lean:42](../../../ArkLib\Data\CodingTheory\ProximityGap\RSListSizeDataPoint.lean#L42) — The smooth multiplicative domain mu_8 ⊂ (ZMod 17)ˣ : the eight 8th roots of unity, listed.

### `domain_implies_char_ne_2` (2 declarations, 2 files)

- `lemma Domain.CosetFftDomainClass.domain_implies_char_ne_2` [ArkLib\Data\Domain\CosetFftDomain\Ops.lean:98](../../../ArkLib\Data\Domain\CosetFftDomain\Ops.lean#L98) — (no docstring)
- `lemma Domain.FftDomainClass.domain_implies_char_ne_2` [ArkLib\Data\Domain\FftDomain\Ops.lean:134](../../../ArkLib\Data\Domain\FftDomain\Ops.lean#L134) — (no docstring)

### `duplexSpongeTraceEntry` (2 declarations, 2 files)

- `abbrev OracleSpec.duplexSpongeTraceEntry` [ArkLib\OracleReduction\FiatShamir\DuplexSponge\Defs.lean:371](../../../ArkLib\OracleReduction\FiatShamir\DuplexSponge\Defs.lean#L371) — The type of a single entry in a duplex sponge query trace. Implicit-parameter companion to `DSTraceS
- `abbrev DuplexSpongeFS.DSTraceStorage.duplexSpongeTraceEntry` [ArkLib\OracleReduction\FiatShamir\DuplexSponge\Security\TraceDataStructures.lean:48](../../../ArkLib\OracleReduction\FiatShamir\DuplexSponge\Security\TraceDataStructures.lean#L48) — A single query-answer entry of a `DuplexSpongeTrace`, i.e. one element of the underlying `QueryLog`

### `empty` (2 declarations, 2 files)

- `def DuplexSpongeFS.DSTraceStorage.ListBacked.empty` [ArkLib\OracleReduction\FiatShamir\DuplexSponge\Security\TraceDataStructures.lean:530](../../../ArkLib\OracleReduction\FiatShamir\DuplexSponge\Security\TraceDataStructures.lean#L530) — (no docstring)
- `def ProtocolSpec.empty` [ArkLib\OracleReduction\ProtocolSpec\Basic.lean:55](../../../ArkLib\OracleReduction\ProtocolSpec\Basic.lean#L55) — The empty protocol specification, with no messages or challenges, written as `!p[]`.

### `energy_H16` (2 declarations, 2 files)

- `theorem ArkLib.ProximityGap.SubgroupAdditiveEnergyFermat257.energy_H16` [ArkLib\Data\CodingTheory\ProximityGap\SubgroupAdditiveEnergyFermat257.lean:71](../../../ArkLib\Data\CodingTheory\ProximityGap\SubgroupAdditiveEnergyFermat257.lean#L71) — (no docstring)
- `theorem ArkLib.ProximityGap.SubgroupAdditiveEnergyFermat65537.energy_H16` [ArkLib\Data\CodingTheory\ProximityGap\SubgroupAdditiveEnergyFermat65537.lean:63](../../../ArkLib\Data\CodingTheory\ProximityGap\SubgroupAdditiveEnergyFermat65537.lean#L63) — **Order-16 energy is `720 ≤ 768 = 3\|G\|²`** — anti-concentration HOLDS here, whereas at `q = 257` the

### `energy_H8` (2 declarations, 2 files)

- `theorem ArkLib.ProximityGap.SubgroupAdditiveEnergyFermat257.energy_H8` [ArkLib\Data\CodingTheory\ProximityGap\SubgroupAdditiveEnergyFermat257.lean:70](../../../ArkLib\Data\CodingTheory\ProximityGap\SubgroupAdditiveEnergyFermat257.lean#L70) — (no docstring)
- `theorem ArkLib.ProximityGap.SubgroupAdditiveEnergyFermat65537.energy_H8` [ArkLib\Data\CodingTheory\ProximityGap\SubgroupAdditiveEnergyFermat65537.lean:58](../../../ArkLib\Data\CodingTheory\ProximityGap\SubgroupAdditiveEnergyFermat65537.lean#L58) — **Order-8 energy is the `q`-independent char-0 value `168`** — identical to `F₂₅₇`, confirming minim

### `epsCA_ge_one_sub_inv_of_allButOne` (2 declarations, 2 files)

- `theorem CodingTheory.Bridge.AllButOne.epsCA_ge_one_sub_inv_of_allButOne` [ArkLib\ToMathlib\BGKS20AllButOne.lean:102](../../../ArkLib\ToMathlib\BGKS20AllButOne.lean#L102) — **T5.4 endpoint from the "all but one scalar" producer.** Under the hypotheses of `nearCertainBadLin
- `theorem CodingTheory.Bridge.epsCA_ge_one_sub_inv_of_allButOne` [ArkLib\ToMathlib\NearCertainBadLineProof.lean:103](../../../ArkLib\ToMathlib\NearCertainBadLineProof.lean#L103) — **T5.4 endpoint from an all-but-one near-certain bad line.**

### `epsCA_le_one` (2 declarations, 2 files)

- `theorem ProximityGap.epsCA_le_one` [ArkLib\Data\CodingTheory\ProximityGap\Errors.lean:247](../../../ArkLib\Data\CodingTheory\ProximityGap\Errors.lean#L247) — The CA error is bounded by the total probability mass.
- `theorem CodingTheory.Bridge.epsCA_le_one` [ArkLib\ToMathlib\BridgeListDecodingCA.lean:65](../../../ArkLib\ToMathlib\BridgeListDecodingCA.lean#L65) — **`ε_ca ≤ 1`.** The correlated-agreement error is a supremum of values each of which is either `0` o

### `epsMCAgs_badList_eq_one` (2 declarations, 2 files)

- `theorem ProximityGap.MCAGSPrizeRefutation.epsMCAgs_badList_eq_one` [ArkLib\Data\CodingTheory\ProximityGap\MCAGSPrizeRefutation.lean:82](../../../ArkLib\Data\CodingTheory\ProximityGap\MCAGSPrizeRefutation.lean#L82) — **`epsMCAgs = 1` for the adversarial list family.** This is the refutation kernel: a non-faithful `L
- `theorem epsMCAgs_badList_eq_one` [ArkLib\MCAGSRefutationCore_keep.lean:81](../../../ArkLib\MCAGSRefutationCore_keep.lean#L81) — **`epsMCAgs = 1` for the adversarial list family.** This is the refutation kernel: a non-faithful `L

### `epsRbr` (2 declarations, 2 files)

- `def Core2Keystone.epsRbr` [ArkLib\ProofSystem\Whir\KeystoneReduction.lean:72](../../../ArkLib\ProofSystem\Whir\KeystoneReduction.lean#L72) — The WHIR per-challenge RBR error (verbatim from `Whir/RbrBudgetAccounting.lean:74`).
- `def Issue113WHIR.epsRbr` [ArkLib\ProofSystem\Whir\RbrBudgetAccounting.lean:74](../../../ArkLib\ProofSystem\Whir\RbrBudgetAccounting.lean#L74) — The WHIR per-challenge RBR error: the maximum over the budget set. Mirror of `whir_rbr_soundness`'s

### `epsRbr_le_of_forall_le` (2 declarations, 2 files)

- `theorem Core2Keystone.epsRbr_le_of_forall_le` [ArkLib\ProofSystem\Whir\KeystoneReduction.lean:278](../../../ArkLib\ProofSystem\Whir\KeystoneReduction.lean#L278) — **§3.2 — antitone transport to a dominating budget (the keystone budget is tight).** The `epsRbr` bu
- `theorem Issue113WHIR.epsRbr_le_of_forall_le` [ArkLib\ProofSystem\Whir\RbrBudgetAccounting.lean:158](../../../ArkLib\ProofSystem\Whir\RbrBudgetAccounting.lean#L158) — **Tightness / universal property: `ε_rbr` is the SMALLEST uniform per-challenge bound.** If a candid

### `eqPoly_evalC_eq_C_eval` (2 declarations, 2 files)

- `theorem Spartan.Spec.eqPoly_evalC_eq_C_eval` [ArkLib\ProofSystem\Spartan\SecondSumcheckReduction.lean:41](../../../ArkLib\ProofSystem\Spartan\SecondSumcheckReduction.lean#L41) — (no docstring)
- `theorem Spartan.eqPoly_evalC_eq_C_eval` [ArkLib\ProofSystem\Spartan\SumcheckDegreeBound.lean:31](../../../ArkLib\ProofSystem\Spartan\SumcheckDegreeBound.lean#L31) — Fixing the `eqPolynomial` row variables at `r_x` via `C` commutes with `C` of the base-ring evaluati

### `eval` (2 declarations, 2 files)

- `def UniPoly.eval` [ArkLib\Data\UniPoly\Basic.lean:412](../../../ArkLib\Data\UniPoly\Basic.lean#L412) — Evaluates a `UniPoly` at a given value
- `def Plonk.Gate.eval` [ArkLib\ProofSystem\ConstraintSystem\Plonk.lean:54](../../../ArkLib\ProofSystem\ConstraintSystem\Plonk.lean#L54) — Evaluate a gate on a given input vector.

### `evalDist_cast_uniformSample` (2 declarations, 2 files)

- `theorem Prover.evalDist_cast_uniformSample` [ArkLib\OracleReduction\Composition\Sequential\ChallengeSeamBridge.lean:74](../../../ArkLib\OracleReduction\Composition\Sequential\ChallengeSeamBridge.lean#L74) — **Atom 2: uniform sampling is invariant under transport along a type equality.** For `h : A = B` wit
- `theorem OptionTStateT.evalDist_cast_uniformSample` [ArkLib\OracleReduction\RunUnroll.lean:369](../../../ArkLib\OracleReduction\RunUnroll.lean#L369) — **Transport of uniform sampling along a type equality.** If `α = β` (propositionally), the uniform s

### `evalDist_map_bijective_uniformSample` (2 declarations, 2 files)

- `theorem ArkLib.SeamChallengeRestriction.evalDist_map_bijective_uniformSample` [ArkLib\OracleReduction\Composition\Sequential\SeamChallengeRestriction.lean:49](../../../ArkLib\OracleReduction\Composition\Sequential\SeamChallengeRestriction.lean#L49) — **Uniform sampling pushed along a bijection.** For a bijection `f : α → β`, the pushforward of the u
- `theorem OptionTStateT.evalDist_map_bijective_uniformSample` [ArkLib\OracleReduction\RunUnroll.lean:384](../../../ArkLib\OracleReduction\RunUnroll.lean#L384) — **Uniform sampling pushed along a bijection.** Generalizes `evalDist_cast_uniformSample` from a type

### `evalOnPoints_injOn_degreeLT` (2 declarations, 2 files)

- `theorem ArkLib.CS25.evalOnPoints_injOn_degreeLT` [ArkLib\Data\CodingTheory\ProximityGap\CS25RSEncodingInjective.lean:28](../../../ArkLib\Data\CodingTheory\ProximityGap\CS25RSEncodingInjective.lean#L28) — **Reed–Solomon encoding injectivity.**  For `k ≤ n`, `evalOnPoints` is injective on degree-`<k` poly
- `theorem ReedSolomon.evalOnPoints_injOn_degreeLT` [ArkLib\Data\CodingTheory\ProximityGap\ReedSolomonUniqueDecode.lean:63](../../../ArkLib\Data\CodingTheory\ProximityGap\ReedSolomonUniqueDecode.lean#L63) — **Reed–Solomon evaluation injectivity.**  A degree-`< k` polynomial is determined by its Reed–Solomo

### `evalX_myR` (2 declarations, 2 files)

- `lemma BCIKS20.HenselNumerator.WeightWitness.evalX_myR` [ArkLib\Data\CodingTheory\ProximityGap\BCIKS20\P1MonicWeightRefutation.lean:82](../../../ArkLib\Data\CodingTheory\ProximityGap\BCIKS20\P1MonicWeightRefutation.lean#L82) — (no docstring)
- `lemma BCIKS20.HenselNumerator.Witness.evalX_myR` [ArkLib\Data\CodingTheory\ProximityGap\BCIKS20\P2OrderZeroRefutationWitness.lean:87](../../../ArkLib\Data\CodingTheory\ProximityGap\BCIKS20\P2OrderZeroRefutationWitness.lean#L87) — `evalX (C 0) R = H = 2·Y`.

### `exists_coordinate_subset_with_many_nonbad_of_heavy_complement_card` (2 declarations, 2 files)

- `lemma ProximityGap.exists_coordinate_subset_with_many_nonbad_of_heavy_complement_card` [ArkLib\Data\CodingTheory\ProximityGap\BCIKS20\ListDecoding\Agreement.lean:6727](../../../ArkLib\Data\CodingTheory\ProximityGap\BCIKS20\ListDecoding\Agreement.lean#L6727) — Complement-to-incidence form of the heavy-coordinate argument.  If a coordinate is not heavy for the
- `lemma ArkLib.Claim511.exists_coordinate_subset_with_many_nonbad_of_heavy_complement_card` [ArkLib\ToMathlib\Claim511.lean:129](../../../ArkLib\ToMathlib\Claim511.lean#L129) — **Complement-to-incidence selection.** If at least `r` coordinates are *not* heavy (each bad for `<

### `exists_ne_zero_map_eq_zero` (2 declarations, 2 files)

- `theorem GSMultInterp.exists_ne_zero_map_eq_zero` [ArkLib\Data\CodingTheory\GuruswamiSudan\MultiplicityInterpolation.lean:215](../../../ArkLib\Data\CodingTheory\GuruswamiSudan\MultiplicityInterpolation.lean#L215) — **Abstract underdetermined-system existence** (mirrors `BCKHS25.exists_ne_zero_map_eq_zero`): a line
- `theorem BCKHS25.exists_ne_zero_map_eq_zero` [ArkLib\Data\CodingTheory\ProximityGap\BCKHS25\Interpolation.lean:71](../../../ArkLib\Data\CodingTheory\ProximityGap\BCKHS25\Interpolation.lean#L71) — Abstract underdetermined-system existence: a linear map between finite-dimensional spaces with stric

### `exists_subset_card_eq_of_le_card` (2 declarations, 2 files)

- `lemma ProximityGap.exists_subset_card_eq_of_le_card` [ArkLib\Data\CodingTheory\ProximityGap\BCIKS20\ListDecoding\Agreement.lean:6677](../../../ArkLib\Data\CodingTheory\ProximityGap\BCIKS20\ListDecoding\Agreement.lean#L6677) — Select exactly `r` elements from a finite set once its cardinality is large enough.  This is the fin
- `lemma ArkLib.Claim511.exists_subset_card_eq_of_le_card` [ArkLib\ToMathlib\Claim511.lean:119](../../../ArkLib\ToMathlib\Claim511.lean#L119) — Select exactly `r` elements from a finite set once its cardinality is large enough.  Final selection

### `extractability` (2 declarations, 2 files)

- `def Commitment.extractability` [ArkLib\CommitmentScheme\Basic.lean:242](../../../ArkLib\CommitmentScheme\Basic.lean#L242) — A commitment scheme satisfies **extractability** with error `extractabilityError` if there exists a
- `def CommitmentScheme.extractability` [ArkLib\CommitmentScheme\CommitmentScheme.lean:159](../../../ArkLib\CommitmentScheme\CommitmentScheme.lean#L159) — A commitment scheme satisfies **extractability** with error `extractabilityError` if there exists a

### `extractor` (2 declarations, 2 files)

- `def CheckClaim.extractor` [ArkLib\ProofSystem\Component\CheckClaim.lean:167](../../../ArkLib\ProofSystem\Component\CheckClaim.lean#L167) — The round-by-round extractor for the `CheckClaim` reduction. Trivial since the witness is `Unit`.
- `def ReduceClaim.extractor` [ArkLib\ProofSystem\Component\ReduceClaim.lean:166](../../../ArkLib\ProofSystem\Component\ReduceClaim.lean#L166) — The round-by-round extractor for the `ReduceClaim` (oracle) reduction. Requires a mapping `mapWitInv

### `fact_prime_eleven` (2 declarations, 2 files)

- `instance ArkLib.CodingTheory.TinyInteriorF11.fact_prime_eleven` [ArkLib\Data\CodingTheory\ProximityGap\ListInteriorPinF11.lean:58](../../../ArkLib\Data\CodingTheory\ProximityGap\ListInteriorPinF11.lean#L58) — `11` is prime, so `ZMod 11` is a field, making `RS[F₁₁, F₁₁, 2]` a genuine Reed–Solomon code.
- `instance ArkLib.CodingTheory.TinyInteriorK3.fact_prime_eleven` [ArkLib\Data\CodingTheory\ProximityGap\ListInteriorPinF11K3.lean:81](../../../ArkLib\Data\CodingTheory\ProximityGap\ListInteriorPinF11K3.lean#L81) — `11` is prime, so `ZMod 11` is a field. This is what makes `RS[F₁₁, F₁₁, 3]` a genuine Reed–Solomon

### `failureProbability` (2 declarations, 2 files)

- `abbrev DuplexSpongeFS.NARG.failureProbability` [ArkLib\OracleReduction\FiatShamir\DuplexSponge\Basic.lean:132](../../../ArkLib\OracleReduction\FiatShamir\DuplexSponge\Basic.lean#L132) — Paper-facing alias for CO25 Definition 3.7 failure probability.
- `def Verifier.failureProbability` [ArkLib\OracleReduction\Security\Rewinding.lean:163](../../../ArkLib\OracleReduction\Security\Rewinding.lean#L163) — CO25 Definition 3.7, adapted to ArkLib's non-interactive verifier interface. The paper's size bound

### `failureProbabilityFamily` (2 declarations, 2 files)

- `abbrev DuplexSpongeFS.NARG.failureProbabilityFamily` [ArkLib\OracleReduction\FiatShamir\DuplexSponge\Basic.lean:142](../../../ArkLib\OracleReduction\FiatShamir\DuplexSponge\Basic.lean#L142) — Paper-facing alias for CO25 Definition 3.7 with explicit security parameter `λ`.
- `def Verifier.failureProbabilityFamily` [ArkLib\OracleReduction\Security\Rewinding.lean:249](../../../ArkLib\OracleReduction\Security\Rewinding.lean#L249) — CO25 Definition 3.7 with the security parameter `λ` made explicit as an external index.

### `fiatShamir_completeness_of_runEq` (2 declarations, 2 files)

- `theorem Reduction.fiatShamir_completeness_of_runEq` [ArkLib\OracleReduction\FiatShamir\Basic.lean:424](../../../ArkLib\OracleReduction\FiatShamir\Basic.lean#L424) — Basic Fiat-Shamir completeness follows from the named run-equality residual and completeness of the
- `theorem Issue116.fiatShamir_completeness_of_runEq` [ArkLib\OracleReduction\FiatShamir\CompletenessUnroll.lean:79](../../../ArkLib\OracleReduction\FiatShamir\CompletenessUnroll.lean#L79) — Forward direction packaged for downstream users: basic FS completeness from the run-equality residua

### `fiatShamir_completeness_unroll_of_runEq` (2 declarations, 2 files)

- `theorem Reduction.fiatShamir_completeness_unroll_of_runEq` [ArkLib\OracleReduction\FiatShamir\Basic.lean:387](../../../ArkLib\OracleReduction\FiatShamir\Basic.lean#L387) — The named run-equality residual is enough to unroll basic-Fiat-Shamir completeness to the explicit h
- `theorem Issue116.fiatShamir_completeness_unroll_of_runEq` [ArkLib\OracleReduction\FiatShamir\CompletenessUnroll.lean:65](../../../ArkLib\OracleReduction\FiatShamir\CompletenessUnroll.lean#L65) — Completeness of the transformed one-message basic Fiat-Shamir reduction is equivalent to the explici

### `fiberCount` (2 declarations, 2 files)

- `def AveragingCrossover.fiberCount` [ArkLib\Data\CodingTheory\ProximityGap\AveragingFiberConservation.lean:85](../../../ArkLib\Data\CodingTheory\ProximityGap\AveragingFiberConservation.lean#L85) — The fiber count over a target.
- `def Round18Bracket.fiberCount` [ArkLib\Data\CodingTheory\ProximityGap\TwoSidedBracketPrizeScale.lean:47](../../../ArkLib\Data\CodingTheory\ProximityGap\TwoSidedBracketPrizeScale.lean#L47) — The fiber count `m x = #{c : x ∈ A c}`.

### `finSumFinEquiv_symm_dite` (2 declarations, 2 files)

- `theorem RingSwitching.finSumFinEquiv_symm_dite` [ArkLib\ProofSystem\RingSwitching\Prelude.lean:1593](../../../ArkLib\ProofSystem\RingSwitching\Prelude.lean#L1593) — Value-form of `finSumFinEquiv.symm`: classify the index by whether its value is `< m`.
- `theorem finSumFinEquiv_symm_dite` [ArkLib\ToMathlib\FinSumMvPolyBricks.lean:25](../../../ArkLib\ToMathlib\FinSumMvPolyBricks.lean#L25) — Value-form classification of `finSumFinEquiv.symm`.

### `finalSumcheckKnowledgeError` (2 declarations, 2 files)

- `def Binius.BinaryBasefold.CoreInteraction.finalSumcheckKnowledgeError` [ArkLib\ProofSystem\Binius\BinaryBasefold\Steps\FinalSumcheck.lean:318](../../../ArkLib\ProofSystem\Binius\BinaryBasefold\Steps\FinalSumcheck.lean#L318) — (no docstring)
- `def Binius.FRIBinius.CoreInteractionPhase.finalSumcheckKnowledgeError` [ArkLib\ProofSystem\Binius\FRIBinius\CoreInteractionPhase.lean:1308](../../../ArkLib\ProofSystem\Binius\FRIBinius\CoreInteractionPhase.lean#L1308) — RBR knowledge error for the final sumcheck step

### `finalSumcheckStepLogic` (2 declarations, 2 files)

- `def Binius.BinaryBasefold.CoreInteraction.finalSumcheckStepLogic` [ArkLib\ProofSystem\Binius\BinaryBasefold\ReductionLogic.lean:902](../../../ArkLib\ProofSystem\Binius\BinaryBasefold\ReductionLogic.lean#L902) — The Logic Instance for the final sumcheck step. This is a 1-message protocol where the prover sends
- `def Binius.FRIBinius.CoreInteractionPhase.finalSumcheckStepLogic` [ArkLib\ProofSystem\Binius\FRIBinius\CoreInteractionPhase.lean:576](../../../ArkLib\ProofSystem\Binius\FRIBinius\CoreInteractionPhase.lean#L576) — The logic instance for the FRI final sumcheck step.

### `finalSumcheckStep_is_logic_complete` (2 declarations, 2 files)

- `lemma Binius.BinaryBasefold.CoreInteraction.finalSumcheckStep_is_logic_complete` [ArkLib\ProofSystem\Binius\BinaryBasefold\ReductionLogic.lean:1371](../../../ArkLib\ProofSystem\Binius\BinaryBasefold\ReductionLogic.lean#L1371) — (no docstring)
- `lemma Binius.FRIBinius.CoreInteractionPhase.finalSumcheckStep_is_logic_complete` [ArkLib\ProofSystem\Binius\FRIBinius\CoreInteractionPhase.lean:1075](../../../ArkLib\ProofSystem\Binius\FRIBinius\CoreInteractionPhase.lean#L1075) — Strong completeness of the FRI final sumcheck logic step.

### `finalSumcheckStep_verifierCheck_passed` (2 declarations, 2 files)

- `lemma Binius.BinaryBasefold.CoreInteraction.finalSumcheckStep_verifierCheck_passed` [ArkLib\ProofSystem\Binius\BinaryBasefold\ReductionLogic.lean:1215](../../../ArkLib\ProofSystem\Binius\BinaryBasefold\ReductionLogic.lean#L1215) — The verifier check passes in the final sumcheck step. **Proof structure:** 1. From `sumcheckConsiste
- `lemma Binius.FRIBinius.CoreInteractionPhase.finalSumcheckStep_verifierCheck_passed` [ArkLib\ProofSystem\Binius\FRIBinius\CoreInteractionPhase.lean:990](../../../ArkLib\ProofSystem\Binius\FRIBinius\CoreInteractionPhase.lean#L990) — Verifier check passes in the FRI final sumcheck logic step.

### `firstOracleWitnessConsistency_unique` (2 declarations, 2 files)

- `lemma Binius.BBFSmallFieldIOPCS.firstOracleWitnessConsistency_unique` [ArkLib\ProofSystem\Binius\BBFSmallFieldIOPCS.lean:172](../../../ArkLib\ProofSystem\Binius\BBFSmallFieldIOPCS.lean#L172) — Uniqueness of the polynomial witness from first-oracle UDR-compatibility.
- `lemma Binius.BinaryBasefold.CoreInteraction.firstOracleWitnessConsistency_unique` [ArkLib\ProofSystem\Binius\BinaryBasefold\Steps\Fold.lean:762](../../../ArkLib\ProofSystem\Binius\BinaryBasefold\Steps\Fold.lean#L762) — (no docstring)

### `floor_lt_of_lt_of_lattice` (2 declarations, 2 files)

- `theorem ArkLib.Issue64Boundary.floor_lt_of_lt_of_lattice` [ArkLib\Data\CodingTheory\ProximityGap\BoundaryCardLatticeSlice.lean:93](../../../ArkLib\Data\CodingTheory\ProximityGap\BoundaryCardLatticeSlice.lean#L93) — **At a lattice point, every strict sub-radius drops the floor.**  If `δ·n` is an integer (`(⌊δ·n⌋ :
- `theorem ArkLib.BoundaryCardResidual.floor_lt_of_lt_of_lattice` [ArkLib\Data\CodingTheory\ProximityGap\BoundaryCardResidual.lean:172](../../../ArkLib\Data\CodingTheory\ProximityGap\BoundaryCardResidual.lean#L172) — **At a lattice endpoint, every strict sub-radius has strictly smaller floor.**  This is the exact co

### `foldOracleReduction_perfectCompleteness` (2 declarations, 2 files)

- `theorem Binius.BinaryBasefold.CoreInteraction.foldOracleReduction_perfectCompleteness` [ArkLib\ProofSystem\Binius\BinaryBasefold\Steps\Fold.lean:162](../../../ArkLib\ProofSystem\Binius\BinaryBasefold\Steps\Fold.lean#L162) — (no docstring)
- `theorem WhirIOP.FoldRound.foldOracleReduction_perfectCompleteness` [ArkLib\ProofSystem\Whir\FoldRound.lean:265](../../../ArkLib\ProofSystem\Whir\FoldRound.lean#L265) — **Perfect completeness of the honest WHIR fold round.** The honest prover folds its committed codewo

### `foldProver` (2 declarations, 2 files)

- `def Fri.Spec.FoldPhase.foldProver` [ArkLib\ProofSystem\Fri\Spec\SingleRound.lean:391](../../../ArkLib\ProofSystem\Fri\Spec\SingleRound.lean#L391) — The prover for the `i`-th round of the FRI protocol. It first receives the challenge, then does an `
- `def WhirIOP.FoldRound.foldProver` [ArkLib\ProofSystem\Whir\FoldRound.lean:174](../../../ArkLib\ProofSystem\Whir\FoldRound.lean#L174) — The honest fold-round prover. It receives `α`, folds its committed function, and sends the folded or

### `foldVerifier` (2 declarations, 2 files)

- `def Fri.Spec.FoldPhase.foldVerifier` [ArkLib\ProofSystem\Fri\Spec\SingleRound.lean:438](../../../ArkLib\ProofSystem\Fri\Spec\SingleRound.lean#L438) — The oracle verifier for the `i`-th non-final folding round of the FRI protocol.
- `def WhirIOP.FoldRound.foldVerifier` [ArkLib\ProofSystem\Whir\FoldRound.lean:192](../../../ArkLib\ProofSystem\Whir\FoldRound.lean#L192) — The honest fold-round verifier. It performs no consistency check (that is deferred to the query phas

### `four_pow_le_shift_choose` (2 declarations, 2 files)

- `theorem Round14ConstantGap.four_pow_le_shift_choose` [ArkLib\Data\CodingTheory\ProximityGap\DeltaStarConstantGapBelowCapacity.lean:68](../../../ArkLib\Data\CodingTheory\ProximityGap\DeltaStarConstantGapBelowCapacity.lean#L68) — **Rate-1/2 engine.** For `t < m`: `4^{m−t} ≤ 2(m−t) · C(2m, m+t)`. Chain: `C(2m, m+t) ≥ C(2(m−t), m−
- `theorem R15Bracket.four_pow_le_shift_choose` [ArkLib\Data\CodingTheory\ProximityGap\PrizeScaleBracketFull.lean:292](../../../ArkLib\Data\CodingTheory\ProximityGap\PrizeScaleBracketFull.lean#L292) — Central-binomial lower bound after a Pascal shift by `2t`: `4^(m−t) ≤ 2(m−t) · C(2m, m+t)` for `t <

### `fullPspec` (2 declarations, 2 files)

- `def Binius.FRIBinius.FullFRIBinius.fullPspec` [ArkLib\ProofSystem\Binius\FRIBinius\General.lean:54](../../../ArkLib\ProofSystem\Binius\FRIBinius\General.lean#L54) — (no docstring)
- `def RingSwitching.fullPspec` [ArkLib\ProofSystem\RingSwitching\Spec.lean:57](../../../ArkLib\ProofSystem\RingSwitching\Spec.lean#L57) — (no docstring)

### `getBit_eq_testBit` (2 declarations, 2 files)

- `lemma Binius.BinaryBasefold.QueryPhase.getBit_eq_testBit` [ArkLib\ProofSystem\Binius\BinaryBasefold\QueryPhase.lean:302](../../../ArkLib\ProofSystem\Binius\BinaryBasefold\QueryPhase.lean#L302) — (no docstring)
- `lemma Binius.BinaryBasefold.getBit_eq_testBit` [ArkLib\ProofSystem\Binius\BinaryBasefold\Soundness\Lift.lean:42](../../../ArkLib\ProofSystem\Binius\BinaryBasefold\Soundness\Lift.lean#L42) — (no docstring)

### `getSumcheckRoundPoly_eval_eq_sum_snoc` (2 declarations, 2 files)

- `theorem RingSwitching.SumcheckPhase.getSumcheckRoundPoly_eval_eq_sum_snoc` [ArkLib\ProofSystem\RingSwitching\SumcheckPhase.lean:296](../../../ArkLib\ProofSystem\RingSwitching\SumcheckPhase.lean#L296) — **Target (b): `getSumcheckRoundPoly` value as a cube sum (LAST-variable/`snoc` form, defect-#20 repa
- `theorem Sumcheck.Structured.getSumcheckRoundPoly_eval_eq_sum_snoc` [ArkLib\ProofSystem\Sumcheck\Structured\SingleRound.lean:117](../../../ArkLib\ProofSystem\Sumcheck\Structured\SingleRound.lean#L117) — **Round-univariate evaluation as a survivor-cube sum (last-variable / `snoc` form).** Evaluating the

### `gs_list_size_bound` (2 declarations, 2 files)

- `theorem GSListSizeBound.gs_list_size_bound` [ArkLib\Data\CodingTheory\GuruswamiSudan\ListSizeBound.lean:130](../../../ArkLib\Data\CodingTheory\GuruswamiSudan\ListSizeBound.lean#L130) — **Guruswami–Sudan list-size bound.** Let `Q : F[X][Y]` be a nonzero interpolant of `(1, k-1)`-weight
- `theorem CodingTheory.Bounds.gs_list_size_bound` [ArkLib\Data\CodingTheory\ListDecoding\Bounds\GuruswamiSudanListSize.lean:91](../../../ArkLib\Data\CodingTheory\ListDecoding\Bounds\GuruswamiSudanListSize.lean#L91) — **Guruswami–Sudan list-size bound.** If `Q ≠ 0` has `Y`-degree `≤ deg_Y`, then the set of candidate

### `guruswami_sudan_for_proximity_gap_existence` (2 declarations, 2 files)

- `lemma GuruswamiSudan.guruswami_sudan_for_proximity_gap_existence` [ArkLib\Data\CodingTheory\GuruswamiSudan\GuruswamiSudan.lean:758](../../../ArkLib\Data\CodingTheory\GuruswamiSudan\GuruswamiSudan.lean#L758) — Constructive witness extraction for the Guruswami–Sudan system. When the computable `hasWitnessC` ch
- `lemma ProximityGap.guruswami_sudan_for_proximity_gap_existence` [ArkLib\Data\CodingTheory\ProximityGap\BCIKS20\ListDecoding\Guruswami.lean:201](../../../ArkLib\Data\CodingTheory\ProximityGap\BCIKS20\ListDecoding\Guruswami.lean#L201) — The first part of Lemma 5.3 from [BCIKS20]. Given `D_X` (`proximity_gap_degree_bound`) and `δ₀` (`pr

### `guruswami_sudan_for_proximity_gap_property` (2 declarations, 2 files)

- `lemma GuruswamiSudan.guruswami_sudan_for_proximity_gap_property` [ArkLib\Data\CodingTheory\GuruswamiSudan\GuruswamiSudan.lean:797](../../../ArkLib\Data\CodingTheory\GuruswamiSudan\GuruswamiSudan.lean#L797) — Constructive witness property for the Guruswami–Sudan system. When `m > 0` and the codeword polynomi
- `lemma ProximityGap.guruswami_sudan_for_proximity_gap_property` [ArkLib\Data\CodingTheory\ProximityGap\BCIKS20\ListDecoding\Guruswami.lean:213](../../../ArkLib\Data\CodingTheory\ProximityGap\BCIKS20\ListDecoding\Guruswami.lean#L213) — The second part of Lemma 5.3 from [BCIKS20]. For any solution `Q` of the Guruswami-Sudan system, and

### `h30_agreement_lower_bound` (2 declarations, 2 files)

- `theorem ArkLib.ProximityGap.PromotedHypotheses.h30_agreement_lower_bound` [ArkLib\Data\CodingTheory\ProximityGap\PromotedHypotheses.lean:40](../../../ArkLib\Data\CodingTheory\ProximityGap\PromotedHypotheses.lean#L40) — (no docstring)
- `theorem h30_agreement_lower_bound` [ArkLib\Data\CodingTheory\ProximityGap\PromotedHypothesesC.lean:11](../../../ArkLib\Data\CodingTheory\ProximityGap\PromotedHypothesesC.lean#L11) — H30: Any vector must agree with some codeword on `k` coordinates. Since we can interpolate on any se

### `ham_c0_c1` (2 declarations, 2 files)

- `theorem JohnsonBound.FamilyRefutation.ham_c0_c1` [ArkLib\Data\CodingTheory\JohnsonBound\FamilyRefutation.lean:44](../../../ArkLib\Data\CodingTheory\JohnsonBound\FamilyRefutation.lean#L44) — Pairwise Hamming distances.
- `theorem JohnsonBound.JqlRefutation.ham_c0_c1` [ArkLib\Data\CodingTheory\JohnsonBound\FamilyRefutationComplete.lean:84](../../../ArkLib\Data\CodingTheory\JohnsonBound\FamilyRefutationComplete.lean#L84) — Pairwise Hamming distances.

### `ham_c0_c2` (2 declarations, 2 files)

- `theorem JohnsonBound.FamilyRefutation.ham_c0_c2` [ArkLib\Data\CodingTheory\JohnsonBound\FamilyRefutation.lean:45](../../../ArkLib\Data\CodingTheory\JohnsonBound\FamilyRefutation.lean#L45) — (no docstring)
- `theorem JohnsonBound.JqlRefutation.ham_c0_c2` [ArkLib\Data\CodingTheory\JohnsonBound\FamilyRefutationComplete.lean:85](../../../ArkLib\Data\CodingTheory\JohnsonBound\FamilyRefutationComplete.lean#L85) — (no docstring)

### `ham_c1_c2` (2 declarations, 2 files)

- `theorem JohnsonBound.FamilyRefutation.ham_c1_c2` [ArkLib\Data\CodingTheory\JohnsonBound\FamilyRefutation.lean:46](../../../ArkLib\Data\CodingTheory\JohnsonBound\FamilyRefutation.lean#L46) — (no docstring)
- `theorem JohnsonBound.JqlRefutation.ham_c1_c2` [ArkLib\Data\CodingTheory\JohnsonBound\FamilyRefutationComplete.lean:86](../../../ArkLib\Data\CodingTheory\JohnsonBound\FamilyRefutationComplete.lean#L86) — (no docstring)

### `hammingDist_add_right` (2 declarations, 2 files)

- `theorem GHSZ02RS.hammingDist_add_right` [ArkLib\Data\CodingTheory\ListDecoding\GHSZ02Foundations.lean:91](../../../ArkLib\Data\CodingTheory\ListDecoding\GHSZ02Foundations.lean#L91) — Hamming distance is translation-invariant on the right.
- `lemma ArkLib.CodingTheory.ListMoments.hammingDist_add_right` [ArkLib\Data\CodingTheory\ProximityGap\ListSizeMoments.lean:41](../../../ArkLib\Data\CodingTheory\ProximityGap\ListSizeMoments.lean#L41) — **Hamming distance is translation invariant**: adding the same `v` to both arguments leaves the dist

### `hammingDist_sub_right` (2 declarations, 2 files)

- `theorem Round13bSecondMoment.hammingDist_sub_right` [ArkLib\Data\CodingTheory\ProximityGap\BallIntersectionSecondMomentLinear.lean:36](../../../ArkLib\Data\CodingTheory\ProximityGap\BallIntersectionSecondMomentLinear.lean#L36) — **Translation invariance of Hamming distance:** `Δ(x−z, y−z) = Δ(x, y)`, via `hammingDist_comp` with
- `theorem ArkLib.CS25.hammingDist_sub_right` [ArkLib\Data\CodingTheory\ProximityGap\CS25SecondMomentReduction.lean:35](../../../ArkLib\Data\CodingTheory\ProximityGap\CS25SecondMomentReduction.lean#L35) — Hamming distance is translation invariant: `Δ₀(w, c) = Δ₀(w - c, 0)`.

### `hasseCoeff` (2 declarations, 2 files)

- `def GSMultInterp.hasseCoeff` [ArkLib\Data\CodingTheory\GuruswamiSudan\MultiplicityInterpolation.lean:136](../../../ArkLib\Data\CodingTheory\GuruswamiSudan\MultiplicityInterpolation.lean#L136) — The order-`(a, b)` *Hasse coefficient* of the bivariate polynomial `Q = ∑_{(s,t)∈monoIdx} c(s,t)·X^s
- `def ArkLib.GS.hasseCoeff` [ArkLib\Data\CodingTheory\ProximityGap\BivariateVanishing.lean:67](../../../ArkLib\Data\CodingTheory\ProximityGap\BivariateVanishing.lean#L67) — The bivariate Hasse–Taylor coefficient of bidegree `(i, j)` of `Q` at `(a, b)`: take the `j`-th oute

### `hasseDerivX_monomial` (2 declarations, 2 files)

- `lemma BCIKS20.HenselNumerator.WeightWitness.hasseDerivX_monomial` [ArkLib\Data\CodingTheory\ProximityGap\BCIKS20\P1MonicWeightRefutation.lean:47](../../../ArkLib\Data\CodingTheory\ProximityGap\BCIKS20\P1MonicWeightRefutation.lean#L47) — (no docstring)
- `lemma BCIKS20.HenselNumerator.Witness.hasseDerivX_monomial` [ArkLib\Data\CodingTheory\ProximityGap\BCIKS20\P2OrderZeroRefutationWitness.lean:54](../../../ArkLib\Data\CodingTheory\ProximityGap\BCIKS20\P2OrderZeroRefutationWitness.lean#L54) — `Δ_X` on a single `Y`-monomial.

### `hasseDeriv_X_pow_prime_pow_sub_one` (2 declarations, 2 files)

- `theorem ArkLib.ProximityGap.Issue232Bricks.hasseDeriv_X_pow_prime_pow_sub_one` [ArkLib\Data\CodingTheory\ProximityGap\Issue232VerifiedBricks.lean:87](../../../ArkLib\Data\CodingTheory\ProximityGap\Issue232VerifiedBricks.lean#L87) — **Hasse–Lucas collapse of the vanishing polynomial.** Over a characteristic-`p` ring, `hasseDeriv m
- `theorem ProximityGap.LinearizedPolynomialHasse.hasseDeriv_X_pow_prime_pow_sub_one` [ArkLib\Data\CodingTheory\ProximityGap\LinearizedPolynomialHasse.lean:92](../../../ArkLib\Data\CodingTheory\ProximityGap\LinearizedPolynomialHasse.lean#L92) — **Inseparable vanishing-polynomial form.** In characteristic `p`, `hasseDeriv m (X^{p^a} - 1) = 0` f

### `hasseDeriv_eval_eq_sum` (2 declarations, 2 files)

- `theorem Issue9Hensel.hasseDeriv_eval_eq_sum` [ArkLib\Data\CodingTheory\ProximityGap\BCIKS20\HasseEvalConnectives.lean:29](../../../ArkLib\Data\CodingTheory\ProximityGap\BCIKS20\HasseEvalConnectives.lean#L29) — (no docstring)
- `theorem Polynomial.hasseDeriv_eval_eq_sum` [ArkLib\ToMathlib\Polynomial\HasseDerivEval.lean:36](../../../ArkLib\ToMathlib\Polynomial\HasseDerivEval.lean#L36) — **Hasse-derivative evaluation identity (★).** The evaluation of the order-`k` Hasse derivative of `p

### `heavyCoords_card_mul_le` (2 declarations, 2 files)

- `lemma ProximityGap.heavyCoords_card_mul_le` [ArkLib\Data\CodingTheory\ProximityGap\BCIKS20\ListDecoding\Agreement.lean:6685](../../../ArkLib\Data\CodingTheory\ProximityGap\BCIKS20\ListDecoding\Agreement.lean#L6685) — Generic double-counting brick for Claim 5.11. If each `z ∈ S` has at most `m` bad coordinates, then
- `lemma ArkLib.Claim511.heavyCoords_card_mul_le` [ArkLib\ToMathlib\Claim511.lean:78](../../../ArkLib\ToMathlib\Claim511.lean#L78) — **Double-counting brick.** If each `z ∈ S` has at most `m` bad coordinates, then the coordinates tha

### `hint` (2 declarations, 2 files)

- `def DomainSeparator.hint` [ArkLib\Data\Hash\DomainSep.lean:230](../../../ArkLib\Data\Hash\DomainSep.lean#L230) — Hint `count` native elements. Rust interface: ```rust pub fn hint(self, label: &str) -> Self ```
- `def HashStateWithInstructions.hint` [ArkLib\OracleReduction\FiatShamir\DuplexSponge\State.lean:192](../../../ArkLib\OracleReduction\FiatShamir\DuplexSponge\State.lean#L192) — Process a hint operation. Rust interface: ```rust pub fn hint(&mut self) -> Result<(), DomainSeparat

### `id_isHVZK` (2 declarations, 2 files)

- `theorem OracleReduction.id_isHVZK` [ArkLib\OracleReduction\Security\OracleZeroKnowledge.lean:332](../../../ArkLib\OracleReduction\Security\OracleZeroKnowledge.lean#L332) — The zero-round identity oracle reduction is HVZK for any oracle-input relation.
- `theorem Reduction.id_isHVZK` [ArkLib\OracleReduction\Security\ZeroKnowledge.lean:375](../../../ArkLib\OracleReduction\Security\ZeroKnowledge.lean#L375) — The zero-round identity reduction is honest-verifier zero-knowledge for any relation.

### `id_isStatHVZK` (2 declarations, 2 files)

- `theorem OracleReduction.id_isStatHVZK` [ArkLib\OracleReduction\Security\OracleZeroKnowledge.lean:342](../../../ArkLib\OracleReduction\Security\OracleZeroKnowledge.lean#L342) — The zero-round identity oracle reduction is statistical HVZK for any oracle-input relation and any e
- `theorem Reduction.id_isStatHVZK` [ArkLib\OracleReduction\Security\ZeroKnowledge.lean:384](../../../ArkLib\OracleReduction\Security\ZeroKnowledge.lean#L384) — The zero-round identity reduction is statistically honest-verifier zero-knowledge for any relation a

### `id_perfectHVZK` (2 declarations, 2 files)

- `theorem OracleReduction.id_perfectHVZK` [ArkLib\OracleReduction\Security\OracleZeroKnowledge.lean:304](../../../ArkLib\OracleReduction\Security\OracleZeroKnowledge.lean#L304) — The zero-round identity oracle reduction is perfect HVZK for any oracle-input relation.
- `theorem Reduction.id_perfectHVZK` [ArkLib\OracleReduction\Security\ZeroKnowledge.lean:355](../../../ArkLib\OracleReduction\Security\ZeroKnowledge.lean#L355) — The zero-round identity reduction satisfies perfect honest-verifier zero-knowledge for any input rel

### `id_statisticalHVZK` (2 declarations, 2 files)

- `theorem OracleReduction.id_statisticalHVZK` [ArkLib\OracleReduction\Security\OracleZeroKnowledge.lean:318](../../../ArkLib\OracleReduction\Security\OracleZeroKnowledge.lean#L318) — The zero-round identity oracle reduction is statistical HVZK for any oracle-input relation and any e
- `theorem Reduction.id_statisticalHVZK` [ArkLib\OracleReduction\Security\ZeroKnowledge.lean:366](../../../ArkLib\OracleReduction\Security\ZeroKnowledge.lean#L366) — The zero-round identity reduction satisfies statistical honest-verifier zero-knowledge for any relat

### `inflate` (2 declarations, 2 files)

- `def ArkLib.ProximityGap.Round4PairingRecursion.inflate` [ArkLib\Data\CodingTheory\ProximityGap\SubsetSumPairingInflate.lean:166](../../../ArkLib\Data\CodingTheory\ProximityGap\SubsetSumPairingInflate.lean#L166) — The inflated subset built from a base `B` and a set `P` of (untouched) pairs to double: `B ∪ doubled
- `def ArkLib.ProximityGap.Round4ZeroSumInflation.inflate` [ArkLib\Data\CodingTheory\ProximityGap\SubsetSumZeroInflation.lean:86](../../../ArkLib\Data\CodingTheory\ProximityGap\SubsetSumZeroInflation.lean#L86) — The inflation map: glue a base window `S₀` onto the union of a chosen collection `T` of zero-sum pai

### `injOn` (2 declarations, 2 files)

- `lemma Domain.CosetFftDomain.injOn` [ArkLib\Data\Domain\CosetFftDomain\Defs.lean:233](../../../ArkLib\Data\Domain\CosetFftDomain\Defs.lean#L233) — (no docstring)
- `lemma Domain.FftDomain.injOn` [ArkLib\Data\Domain\FftDomain\Defs.lean:116](../../../ArkLib\Data\Domain\FftDomain\Defs.lean#L116) — (no docstring)

### `injective` (2 declarations, 2 files)

- `lemma Domain.CosetFftDomain.injective` [ArkLib\Data\Domain\CosetFftDomain\Defs.lean:228](../../../ArkLib\Data\Domain\CosetFftDomain\Defs.lean#L228) — (no docstring)
- `lemma Domain.FftDomain.injective` [ArkLib\Data\Domain\FftDomain\Defs.lean:112](../../../ArkLib\Data\Domain\FftDomain\Defs.lean#L112) — (no docstring)

### `instFactDeg` (2 declarations, 2 files)

- `instance BCIKS20.HenselNumerator.WeightWitness.instFactDeg` [ArkLib\Data\CodingTheory\ProximityGap\BCIKS20\P1MonicWeightRefutation.lean:77](../../../ArkLib\Data\CodingTheory\ProximityGap\BCIKS20\P1MonicWeightRefutation.lean#L77) — (no docstring)
- `instance BCIKS20.HenselNumerator.Witness.instFactDeg` [ArkLib\Data\CodingTheory\ProximityGap\BCIKS20\P2OrderZeroRefutationWitness.lean:84](../../../ArkLib\Data\CodingTheory\ProximityGap\BCIKS20\P2OrderZeroRefutationWitness.lean#L84) — (no docstring)

### `instFactIrr` (2 declarations, 2 files)

- `instance BCIKS20.HenselNumerator.WeightWitness.instFactIrr` [ArkLib\Data\CodingTheory\ProximityGap\BCIKS20\P1MonicWeightRefutation.lean:76](../../../ArkLib\Data\CodingTheory\ProximityGap\BCIKS20\P1MonicWeightRefutation.lean#L76) — (no docstring)
- `instance BCIKS20.HenselNumerator.Witness.instFactIrr` [ArkLib\Data\CodingTheory\ProximityGap\BCIKS20\P2OrderZeroRefutationWitness.lean:83](../../../ArkLib\Data\CodingTheory\ProximityGap\BCIKS20\P2OrderZeroRefutationWitness.lean#L83) — (no docstring)

### `interior_list_two_sided` (2 declarations, 2 files)

- `theorem ArkLib.CodingTheory.Round3SmoothF17.interior_list_two_sided` [ArkLib\Data\CodingTheory\ProximityGap\ListInteriorPinF17Subgroup.lean:239](../../../ArkLib\Data\CodingTheory\ProximityGap\ListInteriorPinF17Subgroup.lean#L239) — **Two-sided interior list-size pin for the smooth-domain code `RS[F₁₇, ⟨2⟩, 2]` at `δ = 5/8`.** Ther
- `theorem ArkLib.CodingTheory.TinyInteriorTwoSided.interior_list_two_sided` [ArkLib\Data\CodingTheory\ProximityGap\ListInteriorTwoSidedF7.lean:197](../../../ArkLib\Data\CodingTheory\ProximityGap\ListInteriorTwoSidedF7.lean#L197) — **Two-sided interior list-size pin for `RS[F₇, F₇, 2]` at `δ = 4/7`.** There exists a received word

### `interior_radius_concrete_t2` (2 declarations, 2 files)

- `theorem ArkLib.CodingTheory.Round5SliceRankT2.interior_radius_concrete_t2` [ArkLib\Data\CodingTheory\ProximityGap\ListInteriorT2TwoSymmetric.lean:370](../../../ArkLib\Data\CodingTheory\ProximityGap\ListInteriorT2TwoSymmetric.lean#L370) — **The `t = 2` interior hypothesis is non-vacuous (concrete instance).** At `k = 50`, `n = 220`: `(k+
- `theorem ArkLib.CodingTheory.Round6Stepanov.interior_radius_concrete_t2` [ArkLib\Data\CodingTheory\ProximityGap\StepanovPointCountEngine.lean:248](../../../ArkLib\Data\CodingTheory\ProximityGap\StepanovPointCountEngine.lean#L248) — **The joint-count containment is non-vacuous.** For `t = 2` the agreement size `a = k+2` is the genu

### `interpolate` (2 declarations, 2 files)

- `def ReedSolomon.interpolate` [ArkLib\Data\CodingTheory\ReedSolomon.lean:631](../../../ArkLib\Data\CodingTheory\ReedSolomon.lean#L631) — The linear map that maps a codeword `f : ι → F` to a degree < \|ι\| polynomial p, such that `p(x) = f(
- `def UniPoly.Lagrange.interpolate` [ArkLib\Data\UniPoly\Basic.lean:1120](../../../ArkLib\Data\UniPoly\Basic.lean#L1120) — This function produces the polynomial which is of degree n and is equal to r i at ω^i for i = 0, 1,

### `isHVZK` (2 declarations, 2 files)

- `def OracleReduction.isHVZK` [ArkLib\OracleReduction\Security\OracleZeroKnowledge.lean:62](../../../ArkLib\OracleReduction\Security\OracleZeroKnowledge.lean#L62) — Existential perfect HVZK for an oracle reduction.
- `def Reduction.isHVZK` [ArkLib\OracleReduction\Security\ZeroKnowledge.lean:90](../../../ArkLib\OracleReduction\Security\ZeroKnowledge.lean#L90) — A reduction is honest-verifier zero-knowledge for relation `rel` if some simulator achieves perfect

### `isHVZK.congr_honestDist` (2 declarations, 2 files)

- `theorem OracleReduction.isHVZK.congr_honestDist` [ArkLib\ToMathlib\OracleZKTransferBricks.lean:397](../../../ArkLib\ToMathlib\OracleZKTransferBricks.lean#L397) — **OracleReduction `isHVZK` transfers along an equal honest distribution.**
- `theorem Reduction.isHVZK.congr_honestDist` [ArkLib\ToMathlib\ZKTransferBricks.lean:480](../../../ArkLib\ToMathlib\ZKTransferBricks.lean#L480) — **`isHVZK` transfers along an `evalDist`-equal honest distribution.**

### `isHVZK.congr_honestDist_symm` (2 declarations, 2 files)

- `theorem OracleReduction.isHVZK.congr_honestDist_symm` [ArkLib\ToMathlib\OracleZKTransferBricks.lean:424](../../../ArkLib\ToMathlib\OracleZKTransferBricks.lean#L424) — **OracleReduction `isHVZK` honest-distribution congruence with opposite-order equality.**
- `theorem Reduction.isHVZK.congr_honestDist_symm` [ArkLib\ToMathlib\ZKTransferBricks.lean:506](../../../ArkLib\ToMathlib\ZKTransferBricks.lean#L506) — **`isHVZK` honest-distribution congruence with opposite-order equality.**

### `isHVZK.isStatHVZK` (2 declarations, 2 files)

- `theorem OracleReduction.isHVZK.isStatHVZK` [ArkLib\OracleReduction\Security\OracleZeroKnowledge.lean:151](../../../ArkLib\OracleReduction\Security\OracleZeroKnowledge.lean#L151) — Perfect HVZK existence for oracle reductions implies statistical HVZK existence.
- `theorem Reduction.isHVZK.isStatHVZK` [ArkLib\OracleReduction\Security\ZeroKnowledge.lean:198](../../../ArkLib\OracleReduction\Security\ZeroKnowledge.lean#L198) — **Perfect HVZK implies statistical HVZK existence** at any error.

### `isHVZK.isStatHVZK_mono_relation_error` (2 declarations, 2 files)

- `theorem OracleReduction.isHVZK.isStatHVZK_mono_relation_error` [ArkLib\OracleReduction\Security\OracleZeroKnowledge.lean:275](../../../ArkLib\OracleReduction\Security\OracleZeroKnowledge.lean#L275) — Perfect HVZK existence for oracle reductions transports to statistical HVZK on a restricted relation
- `theorem Reduction.isHVZK.isStatHVZK_mono_relation_error` [ArkLib\OracleReduction\Security\ZeroKnowledge.lean:305](../../../ArkLib\OracleReduction\Security\ZeroKnowledge.lean#L305) — **Perfect HVZK existence gives statistical HVZK on any subrelation and relaxed error.**

### `isHVZK.mono_relation` (2 declarations, 2 files)

- `theorem OracleReduction.isHVZK.mono_relation` [ArkLib\OracleReduction\Security\OracleZeroKnowledge.lean:118](../../../ArkLib\OracleReduction\Security\OracleZeroKnowledge.lean#L118) — `isHVZK` for oracle reductions is antitone in the relation.
- `theorem Reduction.isHVZK.mono_relation` [ArkLib\OracleReduction\Security\ZeroKnowledge.lean:167](../../../ArkLib\OracleReduction\Security\ZeroKnowledge.lean#L167) — **`isHVZK` is antitone in the relation.** HVZK for `rel` implies HVZK for any `rel' ⊆ rel` (the same

### `isHVZK.triangle_honestDist_symm_zero` (2 declarations, 2 files)

- `theorem OracleReduction.isHVZK.triangle_honestDist_symm_zero` [ArkLib\ToMathlib\OracleZKTransferBricks.lean:523](../../../ArkLib\ToMathlib\OracleZKTransferBricks.lean#L523) — **Existential symmetric-facing zero-error approximate honest-distribution transfer for exact HVZK at
- `theorem Reduction.isHVZK.triangle_honestDist_symm_zero` [ArkLib\ToMathlib\ZKTransferBricks.lean:597](../../../ArkLib\ToMathlib\ZKTransferBricks.lean#L597) — **Existential symmetric-facing zero-error approximate honest-distribution transfer for exact HVZK.**

### `isHVZK.triangle_honestDist_zero` (2 declarations, 2 files)

- `theorem OracleReduction.isHVZK.triangle_honestDist_zero` [ArkLib\ToMathlib\OracleZKTransferBricks.lean:509](../../../ArkLib\ToMathlib\OracleZKTransferBricks.lean#L509) — **Existential zero-error approximate honest-distribution transfer for exact HVZK at the OracleReduct
- `theorem Reduction.isHVZK.triangle_honestDist_zero` [ArkLib\ToMathlib\ZKTransferBricks.lean:583](../../../ArkLib\ToMathlib\ZKTransferBricks.lean#L583) — **Existential zero-error approximate honest-distribution transfer for exact HVZK.**

### `isHVZK_iff_isStatHVZK_zero` (2 declarations, 2 files)

- `theorem OracleReduction.isHVZK_iff_isStatHVZK_zero` [ArkLib\OracleReduction\Security\OracleZeroKnowledge.lean:174](../../../ArkLib\OracleReduction\Security\OracleZeroKnowledge.lean#L174) — Perfect HVZK existence for oracle reductions is equivalent to zero-error statistical HVZK existence.
- `theorem Reduction.isHVZK_iff_isStatHVZK_zero` [ArkLib\OracleReduction\Security\ZeroKnowledge.lean:218](../../../ArkLib\OracleReduction\Security\ZeroKnowledge.lean#L218) — **Perfect HVZK existence is equivalent to zero-error statistical HVZK existence.**

### `isHVZK_of_const_eq_honestDist` (2 declarations, 2 files)

- `theorem OracleReduction.isHVZK_of_const_eq_honestDist` [ArkLib\ToMathlib\OracleZKTransferBricks.lean:372](../../../ArkLib\ToMathlib\OracleZKTransferBricks.lean#L372) — **OracleReduction `isHVZK` from the symmetric-facing constant-simulator criterion.**
- `theorem Reduction.isHVZK_of_const_eq_honestDist` [ArkLib\ToMathlib\ZKTransferBricks.lean:455](../../../ArkLib\ToMathlib\ZKTransferBricks.lean#L455) — **`isHVZK` from the symmetric-facing constant-simulator criterion.**

### `isHVZK_of_honestDist_eq_const` (2 declarations, 2 files)

- `theorem OracleReduction.isHVZK_of_honestDist_eq_const` [ArkLib\ToMathlib\OracleZKTransferBricks.lean:347](../../../ArkLib\ToMathlib\OracleZKTransferBricks.lean#L347) — **OracleReduction `isHVZK` from the constant-simulator criterion.**
- `theorem Reduction.isHVZK_of_honestDist_eq_const` [ArkLib\ToMathlib\ZKTransferBricks.lean:432](../../../ArkLib\ToMathlib\ZKTransferBricks.lean#L432) — **`isHVZK` from the constant-simulator criterion.**

### `isPrimitiveRoot_zeta` (2 declarations, 2 files)

- `theorem R12J.General.isPrimitiveRoot_zeta` [ArkLib\Data\CodingTheory\ProximityGap\JointT2Unconditional.lean:171](../../../ArkLib\Data\CodingTheory\ProximityGap\JointT2Unconditional.lean#L171) — `zeta m` is a primitive `2^m`-th root of unity.
- `theorem Concrete.isPrimitiveRoot_zeta` [ArkLib\Data\CodingTheory\ProximityGap\LamLeungUnconditionalGeneral.lean:212](../../../ArkLib\Data\CodingTheory\ProximityGap\LamLeungUnconditionalGeneral.lean#L212) — `zeta m` is a primitive `2^m`-th root of unity (`m ≥ 1`).

### `isStatHVZK` (2 declarations, 2 files)

- `def OracleReduction.isStatHVZK` [ArkLib\OracleReduction\Security\OracleZeroKnowledge.lean:71](../../../ArkLib\OracleReduction\Security\OracleZeroKnowledge.lean#L71) — Existential statistical HVZK for an oracle reduction.
- `def Reduction.isStatHVZK` [ArkLib\OracleReduction\Security\ZeroKnowledge.lean:98](../../../ArkLib\OracleReduction\Security\ZeroKnowledge.lean#L98) — A reduction is *statistically* honest-verifier zero-knowledge with error `ε` if some simulator achie

### `isStatHVZK.congr_honestDist` (2 declarations, 2 files)

- `theorem OracleReduction.isStatHVZK.congr_honestDist` [ArkLib\ToMathlib\OracleZKTransferBricks.lean:410](../../../ArkLib\ToMathlib\OracleZKTransferBricks.lean#L410) — **OracleReduction `isStatHVZK` transfers along an equal honest distribution.**
- `theorem Reduction.isStatHVZK.congr_honestDist` [ArkLib\ToMathlib\ZKTransferBricks.lean:493](../../../ArkLib\ToMathlib\ZKTransferBricks.lean#L493) — **`isStatHVZK` transfers along an `evalDist`-equal honest distribution.**

### `isStatHVZK.congr_honestDist_symm` (2 declarations, 2 files)

- `theorem OracleReduction.isStatHVZK.congr_honestDist_symm` [ArkLib\ToMathlib\OracleZKTransferBricks.lean:436](../../../ArkLib\ToMathlib\OracleZKTransferBricks.lean#L436) — **OracleReduction `isStatHVZK` honest-distribution congruence with opposite-order equality.**
- `theorem Reduction.isStatHVZK.congr_honestDist_symm` [ArkLib\ToMathlib\ZKTransferBricks.lean:518](../../../ArkLib\ToMathlib\ZKTransferBricks.lean#L518) — **`isStatHVZK` honest-distribution congruence with opposite-order equality.**

### `isStatHVZK.mono_error` (2 declarations, 2 files)

- `theorem OracleReduction.isStatHVZK.mono_error` [ArkLib\OracleReduction\Security\OracleZeroKnowledge.lean:198](../../../ArkLib\OracleReduction\Security\OracleZeroKnowledge.lean#L198) — `isStatHVZK` for oracle reductions is monotone in the error bound.
- `theorem Reduction.isStatHVZK.mono_error` [ArkLib\OracleReduction\Security\ZeroKnowledge.lean:240](../../../ArkLib\OracleReduction\Security\ZeroKnowledge.lean#L240) — **`isStatHVZK` is monotone in the error.**

### `isStatHVZK.mono_relation` (2 declarations, 2 files)

- `theorem OracleReduction.isStatHVZK.mono_relation` [ArkLib\OracleReduction\Security\OracleZeroKnowledge.lean:187](../../../ArkLib\OracleReduction\Security\OracleZeroKnowledge.lean#L187) — `isStatHVZK` for oracle reductions is antitone in the relation.
- `theorem Reduction.isStatHVZK.mono_relation` [ArkLib\OracleReduction\Security\ZeroKnowledge.lean:230](../../../ArkLib\OracleReduction\Security\ZeroKnowledge.lean#L230) — **`isStatHVZK` is antitone in the relation.**

### `isStatHVZK.mono_relation_error` (2 declarations, 2 files)

- `theorem OracleReduction.isStatHVZK.mono_relation_error` [ArkLib\OracleReduction\Security\OracleZeroKnowledge.lean:261](../../../ArkLib\OracleReduction\Security\OracleZeroKnowledge.lean#L261) — Existential statistical HVZK for oracle reductions transports across both relation restriction and e
- `theorem Reduction.isStatHVZK.mono_relation_error` [ArkLib\OracleReduction\Security\ZeroKnowledge.lean:295](../../../ArkLib\OracleReduction\Security\ZeroKnowledge.lean#L295) — **Existential statistical HVZK transports across both relation restriction and error relaxation.** T

### `isStatHVZK.triangle_honestDist` (2 declarations, 2 files)

- `theorem OracleReduction.isStatHVZK.triangle_honestDist` [ArkLib\ToMathlib\OracleZKTransferBricks.lean:449](../../../ArkLib\ToMathlib\OracleZKTransferBricks.lean#L449) — **Existential approximate honest-distribution transfer at the OracleReduction API boundary.**
- `theorem Reduction.isStatHVZK.triangle_honestDist` [ArkLib\ToMathlib\ZKTransferBricks.lean:530](../../../ArkLib\ToMathlib\ZKTransferBricks.lean#L530) — **Existential approximate honest-distribution transfer for statistical HVZK.**

### `isStatHVZK.triangle_honestDist_symm` (2 declarations, 2 files)

- `theorem OracleReduction.isStatHVZK.triangle_honestDist_symm` [ArkLib\ToMathlib\OracleZKTransferBricks.lean:464](../../../ArkLib\ToMathlib\OracleZKTransferBricks.lean#L464) — **Existential symmetric-facing approximate honest-distribution transfer at the OracleReduction API b
- `theorem Reduction.isStatHVZK.triangle_honestDist_symm` [ArkLib\ToMathlib\ZKTransferBricks.lean:543](../../../ArkLib\ToMathlib\ZKTransferBricks.lean#L543) — **Existential symmetric-facing approximate honest-distribution transfer.**

### `isStatHVZK.triangle_honestDist_symm_zero` (2 declarations, 2 files)

- `theorem OracleReduction.isStatHVZK.triangle_honestDist_symm_zero` [ArkLib\ToMathlib\OracleZKTransferBricks.lean:494](../../../ArkLib\ToMathlib\OracleZKTransferBricks.lean#L494) — **Existential symmetric-facing zero-error approximate honest-distribution transfer for statistical H
- `theorem Reduction.isStatHVZK.triangle_honestDist_symm_zero` [ArkLib\ToMathlib\ZKTransferBricks.lean:570](../../../ArkLib\ToMathlib\ZKTransferBricks.lean#L570) — **Existential symmetric-facing zero-error approximate honest-distribution transfer for statistical H

### `isStatHVZK.triangle_honestDist_zero` (2 declarations, 2 files)

- `theorem OracleReduction.isStatHVZK.triangle_honestDist_zero` [ArkLib\ToMathlib\OracleZKTransferBricks.lean:479](../../../ArkLib\ToMathlib\OracleZKTransferBricks.lean#L479) — **Existential zero-error approximate honest-distribution transfer for statistical HVZK at the Oracle
- `theorem Reduction.isStatHVZK.triangle_honestDist_zero` [ArkLib\ToMathlib\ZKTransferBricks.lean:556](../../../ArkLib\ToMathlib\ZKTransferBricks.lean#L556) — **Existential zero-error approximate honest-distribution transfer for statistical HVZK.**

### `isStatHVZK_of_const_eq_honestDist` (2 declarations, 2 files)

- `theorem OracleReduction.isStatHVZK_of_const_eq_honestDist` [ArkLib\ToMathlib\OracleZKTransferBricks.lean:384](../../../ArkLib\ToMathlib\OracleZKTransferBricks.lean#L384) — **OracleReduction `isStatHVZK` from the symmetric-facing constant-simulator criterion.**
- `theorem Reduction.isStatHVZK_of_const_eq_honestDist` [ArkLib\ToMathlib\ZKTransferBricks.lean:467](../../../ArkLib\ToMathlib\ZKTransferBricks.lean#L467) — **`isStatHVZK` from the symmetric-facing constant-simulator criterion.**

### `isStatHVZK_of_honestDist_eq_const` (2 declarations, 2 files)

- `theorem OracleReduction.isStatHVZK_of_honestDist_eq_const` [ArkLib\ToMathlib\OracleZKTransferBricks.lean:359](../../../ArkLib\ToMathlib\OracleZKTransferBricks.lean#L359) — **OracleReduction `isStatHVZK` from the constant-simulator criterion.**
- `theorem Reduction.isStatHVZK_of_honestDist_eq_const` [ArkLib\ToMathlib\ZKTransferBricks.lean:443](../../../ArkLib\ToMathlib\ZKTransferBricks.lean#L443) — **`isStatHVZK` from the constant-simulator criterion.**

### `isStatHVZK_zero.isHVZK` (2 declarations, 2 files)

- `theorem OracleReduction.isStatHVZK_zero.isHVZK` [ArkLib\OracleReduction\Security\OracleZeroKnowledge.lean:162](../../../ArkLib\OracleReduction\Security\OracleZeroKnowledge.lean#L162) — Zero-error statistical HVZK existence for oracle reductions recovers perfect HVZK existence.
- `theorem Reduction.isStatHVZK_zero.isHVZK` [ArkLib\OracleReduction\Security\ZeroKnowledge.lean:208](../../../ArkLib\OracleReduction\Security\ZeroKnowledge.lean#L208) — **Zero-error statistical HVZK existence is perfect HVZK existence.**

### `isStatHVZK_zero.isHVZK_mono_relation` (2 declarations, 2 files)

- `theorem OracleReduction.isStatHVZK_zero.isHVZK_mono_relation` [ArkLib\OracleReduction\Security\OracleZeroKnowledge.lean:287](../../../ArkLib\OracleReduction\Security\OracleZeroKnowledge.lean#L287) — Zero-error statistical HVZK existence for oracle reductions transports back to perfect HVZK existenc
- `theorem Reduction.isStatHVZK_zero.isHVZK_mono_relation` [ArkLib\OracleReduction\Security\ZeroKnowledge.lean:315](../../../ArkLib\OracleReduction\Security\ZeroKnowledge.lean#L315) — **Zero-error statistical HVZK existence transports back to perfect HVZK existence on a subrelation.*

### `iterated_fold_to_const_strict` (2 declarations, 2 files)

- `lemma Binius.BinaryBasefold.CoreInteraction.iterated_fold_to_const_strict` [ArkLib\ProofSystem\Binius\BinaryBasefold\ReductionLogic.lean:972](../../../ArkLib\ProofSystem\Binius\BinaryBasefold\ReductionLogic.lean#L972) — **Strict version**: When folding the last oracle to level `ℓ` (final sumcheck), the iterated fold of
- `lemma Binius.FRIBinius.CoreInteractionPhase.iterated_fold_to_const_strict` [ArkLib\ProofSystem\Binius\FRIBinius\CoreInteractionPhase.lean:732](../../../ArkLib\ProofSystem\Binius\FRIBinius\CoreInteractionPhase.lean#L732) — Strict helper: folding the last oracle block in the final sumcheck step yields the constant function

### `jointAgreeSet` (2 declarations, 2 files)

- `def Round17CAPair.jointAgreeSet` [ArkLib\Data\CodingTheory\ProximityGap\CAPairExtractionEngine.lean:56](../../../ArkLib\Data\CodingTheory\ProximityGap\CAPairExtractionEngine.lean#L56) — The joint agreement set of the pair `(f₁, f₂)` with the codeword pair `(g₁, g₂)`.
- `def ProximityPrizeCA.jointAgreeSet` [ArkLib\Data\CodingTheory\ProximityPrizeCA.lean:39](../../../ArkLib\Data\CodingTheory\ProximityPrizeCA.lean#L39) — The joint agreement set of two word pairs.

### `knowledgeSoundness.mono_error` (2 declarations, 2 files)

- `theorem Verifier.knowledgeSoundness.mono_error` [ArkLib\OracleReduction\Security\Basic.lean:381](../../../ArkLib\OracleReduction\Security\Basic.lean#L381) — Straightline knowledge soundness is monotone in the allowed knowledge error.
- `theorem Verifier.StateRestoration.knowledgeSoundness.mono_error` [ArkLib\OracleReduction\Security\StateRestoration.lean:218](../../../ArkLib\OracleReduction\Security\StateRestoration.lean#L218) — State-restoration knowledge soundness is monotone in the allowed knowledge-soundness error.

### `knowledgeSoundness.mono_relations` (2 declarations, 2 files)

- `theorem Verifier.knowledgeSoundness.mono_relations` [ArkLib\OracleReduction\Security\Basic.lean:397](../../../ArkLib\OracleReduction\Security\Basic.lean#L397) — Straightline knowledge soundness is monotone in the input and output relations. If knowledge soundne
- `theorem Verifier.StateRestoration.knowledgeSoundness.mono_relations` [ArkLib\OracleReduction\Security\StateRestoration.lean:232](../../../ArkLib\OracleReduction\Security\StateRestoration.lean#L232) — State-restoration knowledge soundness is monotone under enlarging the valid input relation and shrin

### `lambda_le_ggr11_of_Lambda_top` (2 declarations, 2 files)

- `theorem InterleavedCode.GGR11.lambda_le_ggr11_of_Lambda_top` [ArkLib\ToMathlib\GGR11Interleaved.lean:404](../../../ArkLib\ToMathlib\GGR11Interleaved.lean#L404) — Generic end-to-end infinite-list regime: if the base list size is infinite and the Red budget is pos
- `theorem InterleavedCode.GGR11Reconnect.lambda_le_ggr11_of_Lambda_top` [ArkLib\ToMathlib\GGR11Reconnect.lean:134](../../../ArkLib\ToMathlib\GGR11Reconnect.lean#L134) — **Infinite-list regime, reconnected.** When the base list size is infinite and the GGR11 Red budget

### `lambda_le_ggr11_of_le_exp` (2 declarations, 2 files)

- `theorem InterleavedCode.GGR11.lambda_le_ggr11_of_le_exp` [ArkLib\ToMathlib\GGR11Interleaved.lean:394](../../../ArkLib\ToMathlib\GGR11Interleaved.lean#L394) — Generic end-to-end elementary regime: if the Red budget already dominates the interleaving factor, t
- `theorem InterleavedCode.GGR11Reconnect.lambda_le_ggr11_of_le_exp` [ArkLib\ToMathlib\GGR11Reconnect.lean:122](../../../ArkLib\ToMathlib\GGR11Reconnect.lean#L122) — **Elementary regime, reconnected.** When the GGR11 Red budget already dominates the interleaving fac

### `lambda_le_ggr11_of_perWordBound` (2 declarations, 2 files)

- `theorem InterleavedCode.GGR11.lambda_le_ggr11_of_perWordBound` [ArkLib\ToMathlib\GGR11Interleaved.lean:118](../../../ArkLib\ToMathlib\GGR11Interleaved.lean#L118) — **Reduction of the GGR11 interleaved list-size bound to its per-word form.** Given the per-received-
- `theorem InterleavedCode.GGR11Reconnect.lambda_le_ggr11_of_perWordBound` [ArkLib\ToMathlib\GGR11Reconnect.lean:110](../../../ArkLib\ToMathlib\GGR11Reconnect.lean#L110) — **Reconnect (per-word form).** The bare bound follows from the (coarser) per-received-word residual

### `lambda_le_ggr11_of_treeFrontier` (2 declarations, 2 files)

- `theorem InterleavedCode.GGR11.lambda_le_ggr11_of_treeFrontier` [ArkLib\ToMathlib\GGR11Interleaved.lean:291](../../../ArkLib\ToMathlib\GGR11Interleaved.lean#L291) — End-to-end GGR11 list-size bound from the granular named frontier.
- `theorem InterleavedCode.GGR11Reconnect.lambda_le_ggr11_of_treeFrontier` [ArkLib\ToMathlib\GGR11Reconnect.lean:100](../../../ArkLib\ToMathlib\GGR11Reconnect.lean#L100) — **Reconnect (named frontier form).** The bare bound follows from the granular per-received-word `GGR

### `lambda_le_ggr11_of_treeStructure` (2 declarations, 2 files)

- `theorem InterleavedCode.GGR11.lambda_le_ggr11_of_treeStructure` [ArkLib\ToMathlib\GGR11Interleaved.lean:283](../../../ArkLib\ToMathlib\GGR11Interleaved.lean#L283) — **End-to-end:** the GGR11 interleaved list-size bound from the refined tree-existence residual.
- `theorem InterleavedCode.GGR11Reconnect.lambda_le_ggr11_of_treeStructure` [ArkLib\ToMathlib\GGR11Reconnect.lean:90](../../../ArkLib\ToMathlib\GGR11Reconnect.lean#L90) — **Reconnect (tree-existence form).** The bare `InterleavedCode.lambda_le_ggr11` bound follows from t

### `leftpad` (2 declarations, 2 files)

- `def Fin.leftpad` [ArkLib\Data\Fin\Tuple\Defs.lean:96](../../../ArkLib\Data\Fin\Tuple\Defs.lean#L96) — Pad a `Fin`-indexed vector on the left with an element `a`. This becomes truncation if `n < m`.
- `def Matrix.leftpad` [ArkLib\Data\Matrix\Basic.lean:25](../../../ArkLib\Data\Matrix\Basic.lean#L25) — (no docstring)

### `liftContext_completeness` (2 declarations, 2 files)

- `theorem OracleReduction.liftContext_completeness` [ArkLib\OracleReduction\LiftContext\OracleReduction.lean:242](../../../ArkLib\OracleReduction\LiftContext\OracleReduction.lean#L242) — STATEMENT REPAIR (2026-06-04): completeness lifting now additionally takes the verifier's oracle-rou
- `theorem Reduction.liftContext_completeness` [ArkLib\OracleReduction\LiftContext\Reduction.lean:776](../../../ArkLib\OracleReduction\LiftContext\Reduction.lean#L776) — Lifting the reduction preserves completeness, assuming the lens satisfies its completeness condition

### `liftContext_knowledgeSoundness` (2 declarations, 2 files)

- `theorem OracleVerifier.liftContext_knowledgeSoundness` [ArkLib\OracleReduction\LiftContext\OracleReduction.lean:292](../../../ArkLib\OracleReduction\LiftContext\OracleReduction.lean#L292) — (no docstring)
- `theorem Verifier.liftContext_knowledgeSoundness` [ArkLib\OracleReduction\LiftContext\Reduction.lean:928](../../../ArkLib\OracleReduction\LiftContext\Reduction.lean#L928) — (no docstring)

### `liftContext_perfectCompleteness` (2 declarations, 2 files)

- `theorem OracleReduction.liftContext_perfectCompleteness` [ArkLib\OracleReduction\LiftContext\OracleReduction.lean:252](../../../ArkLib\OracleReduction\LiftContext\OracleReduction.lean#L252) — (no docstring)
- `theorem Reduction.liftContext_perfectCompleteness` [ArkLib\OracleReduction\LiftContext\Reduction.lean:881](../../../ArkLib\OracleReduction\LiftContext\Reduction.lean#L881) — (no docstring)

### `liftContext_rbr_knowledgeSoundness` (2 declarations, 2 files)

- `theorem OracleVerifier.liftContext_rbr_knowledgeSoundness` [ArkLib\OracleReduction\LiftContext\OracleReduction.lean:351](../../../ArkLib\OracleReduction\LiftContext\OracleReduction.lean#L351) — (no docstring)
- `theorem Verifier.liftContext_rbr_knowledgeSoundness` [ArkLib\OracleReduction\LiftContext\Reduction.lean:1674](../../../ArkLib\OracleReduction\LiftContext\Reduction.lean#L1674) — (no docstring)

### `liftContext_rbr_soundness` (2 declarations, 2 files)

- `theorem OracleVerifier.liftContext_rbr_soundness` [ArkLib\OracleReduction\LiftContext\OracleReduction.lean:312](../../../ArkLib\OracleReduction\LiftContext\OracleReduction.lean#L312) — (no docstring)
- `theorem Verifier.liftContext_rbr_soundness` [ArkLib\OracleReduction\LiftContext\Reduction.lean:1425](../../../ArkLib\OracleReduction\LiftContext\Reduction.lean#L1425) — (no docstring)

### `liftContext_soundness` (2 declarations, 2 files)

- `theorem OracleVerifier.liftContext_soundness` [ArkLib\OracleReduction\LiftContext\OracleReduction.lean:276](../../../ArkLib\OracleReduction\LiftContext\OracleReduction.lean#L276) — Lifting the reduction preserves soundness, assuming the lens satisfies its soundness conditions. STA
- `theorem Verifier.liftContext_soundness` [ArkLib\OracleReduction\LiftContext\Reduction.lean:902](../../../ArkLib\OracleReduction\LiftContext\Reduction.lean#L902) — Lifting a verifier context preserves soundness, supplied as an explicit residual.

### `liftM_optionT_run_eq_seam_right` (2 declarations, 2 files)

- `theorem Reduction.liftM_optionT_run_eq_seam_right` [ArkLib\OracleReduction\Composition\Sequential\AppendSeamBridges.lean:77](../../../ArkLib\OracleReduction\Composition\Sequential\AppendSeamBridges.lean#L77) — **`(liftM g).run = liftM g.run` across the `pSpec₂` challenge seam.** The `pSpec₂` analogue of `lift
- `theorem Verifier.liftM_optionT_run_eq_seam_right` [ArkLib\OracleReduction\Composition\Sequential\AppendSoundnessMsgProof.lean:194](../../../ArkLib\OracleReduction\Composition\Sequential\AppendSoundnessMsgProof.lean#L194) — (no docstring)

### `lift_oc_optionT_coh_right` (2 declarations, 2 files)

- `theorem Reduction.lift_oc_optionT_coh_right` [ArkLib\OracleReduction\Composition\Sequential\AppendSeamBridges.lean:112](../../../ArkLib\OracleReduction\Composition\Sequential\AppendSeamBridges.lean#L112) — **`OptionT`-lift coherence for a phase computation across the `pSpec₂` seam.** The `pSpec₂` analogue
- `theorem Verifier.lift_oc_optionT_coh_right` [ArkLib\OracleReduction\Composition\Sequential\AppendSoundnessMsgProof.lean:177](../../../ArkLib\OracleReduction\Composition\Sequential\AppendSoundnessMsgProof.lean#L177) — (no docstring)

### `listAt` (2 declarations, 2 files)

- `def ArkLib.ProximityGap.RSPrizeDataPoint.listAt` [ArkLib\Data\CodingTheory\ProximityGap\RSListSizeDataPoint.lean:57](../../../ArkLib\Data\CodingTheory\ProximityGap\RSListSizeDataPoint.lean#L57) — The list-decoding list at agreement radius `a` for received word `w`, as a `Finset` of the coefficie
- `def RSAsymptKernel.listAt` [ArkLib\Data\CodingTheory\ProximityGap\RSMDSListBound.lean:202](../../../ArkLib\Data\CodingTheory\ProximityGap\RSMDSListBound.lean#L202) — The finite set ("list") of `RS[F,n,k]` codewords of weight at most `w`.

### `loc_natDegree` (2 declarations, 2 files)

- `lemma NormalRank.loc_natDegree` [ArkLib\Data\CodingTheory\ProximityGap\NormalRankSharpThreshold.lean:57](../../../ArkLib\Data\CodingTheory\ProximityGap\NormalRankSharpThreshold.lean#L57) — (no docstring)
- `lemma TopLine.loc_natDegree` [ArkLib\Data\CodingTheory\ProximityGap\TopDirectionLineCount.lean:73](../../../ArkLib\Data\CodingTheory\ProximityGap\TopDirectionLineCount.lean#L73) — (no docstring)

### `map` (2 declarations, 2 files)

- `def AGM.GroupRepresentation.map` [ArkLib\AGM\Basic.lean:109](../../../ArkLib\AGM\Basic.lean#L109) — **Functoriality of representations under group homomorphisms.** A group hom `f : G →* H` transports
- `def Fin.map` [ArkLib\Data\Fin\Sigma.lean:499](../../../ArkLib\Data\Fin\Sigma.lean#L499) — (no docstring)

### `mapEquiv` (2 declarations, 2 files)

- `def Probability.SizeSubset.mapEquiv` [ArkLib\Data\Probability\Combinatorial.lean:92](../../../ArkLib\Data\Probability\Combinatorial.lean#L92) — Transport a size-`n` subset across an equivalence of ambient types.
- `def Probability.SizedSubset.mapEquiv` [ArkLib\Data\Probability\UniformSubset.lean:54](../../../ArkLib\Data\Probability\UniformSubset.lean#L54) — Map an `n`-element subset across an equivalence of ambient finite types.

### `masterKStateProp` (2 declarations, 2 files)

- `def Binius.BinaryBasefold.masterKStateProp` [ArkLib\ProofSystem\Binius\BinaryBasefold\Basic.lean:1399](../../../ArkLib\ProofSystem\Binius\BinaryBasefold\Basic.lean#L1399) — Before V's challenge of the `i-th` foldStep, we ignore the bad-folding-event of the `i-th` oracle if
- `def RingSwitching.masterKStateProp` [ArkLib\ProofSystem\RingSwitching\Prelude.lean:459](../../../ArkLib\ProofSystem\RingSwitching\Prelude.lean#L459) — (no docstring)

### `mcaBad` (2 declarations, 2 files)

- `def ProximityGap.mcaBad` [ArkLib\Data\CodingTheory\Connections\EpsMCABadGlue.lean:72](../../../ArkLib\Data\CodingTheory\Connections\EpsMCABadGlue.lean#L72) — For a fixed stack `(u₀, u₁)` and radius `δ`, the finset of "bad" scalars `γ ∈ F` for which the `mcaE
- `def R15MCAGap.mcaBad` [ArkLib\Data\CodingTheory\ProximityGap\MCABadScalarSpreadBridge.lean:82](../../../ArkLib\Data\CodingTheory\ProximityGap\MCABadScalarSpreadBridge.lean#L82) — The MCA bad event at scalar `γ`: the pencil word `f1 + γ·f2` is close to the code, yet the pair `(f1

### `mcaBadCount` (2 declarations, 2 files)

- `def ProximityGap.mcaBadCount` [ArkLib\Data\CodingTheory\ProximityGap\MCABadCount.lean:45](../../../ArkLib\Data\CodingTheory\ProximityGap\MCABadCount.lean#L45) — The number of bad scalars `γ : F` realising the MCA event for the pair `(u₀, u₁)` at radius `δ`.
- `def R15MCAGap.mcaBadCount` [ArkLib\Data\CodingTheory\ProximityGap\MCABadScalarSpreadBridge.lean:96](../../../ArkLib\Data\CodingTheory\ProximityGap\MCABadScalarSpreadBridge.lean#L96) — The number of MCA-bad scalars on the pencil through `f1` in direction `f2`.

### `mcaEventGSrow_badStack` (2 declarations, 2 files)

- `theorem ProximityGap.MCAGSPrizeRefutation.mcaEventGSrow_badStack` [ArkLib\Data\CodingTheory\ProximityGap\MCAGSPrizeRefutation.lean:36](../../../ArkLib\Data\CodingTheory\ProximityGap\MCAGSPrizeRefutation.lean#L36) — **Key lemma.** For any nonzero codeword `w₀ ∈ C` and any `δ ≤ 1`, the GS-row bad event fires at the
- `theorem mcaEventGSrow_badStack` [ArkLib\MCAGSRefutationCore_keep.lean:35](../../../ArkLib\MCAGSRefutationCore_keep.lean#L35) — **Key lemma.** For any nonzero codeword `w₀ ∈ C` and any `δ ≤ 1`, the GS-row bad event fires at the

### `mem_C_iff` (2 declarations, 2 files)

- `theorem JohnsonBound.FamilyRefutation.mem_C_iff` [ArkLib\Data\CodingTheory\JohnsonBound\FamilyRefutation.lean:49](../../../ArkLib\Data\CodingTheory\JohnsonBound\FamilyRefutation.lean#L49) — Membership in `C` is membership in the explicit three-element set.
- `theorem JohnsonBound.JqlRefutation.mem_C_iff` [ArkLib\Data\CodingTheory\JohnsonBound\FamilyRefutationComplete.lean:89](../../../ArkLib\Data\CodingTheory\JohnsonBound\FamilyRefutationComplete.lean#L89) — Membership in `C` is membership in the explicit three-element set.

### `mem_gsSupport` (2 declarations, 2 files)

- `lemma GSHasse.mem_gsSupport` [ArkLib\Data\CodingTheory\ProximityGap\GSHasseMultiplicity.lean:81](../../../ArkLib\Data\CodingTheory\ProximityGap\GSHasseMultiplicity.lean#L81) — (no docstring)
- `lemma GSInterp.mem_gsSupport` [ArkLib\Data\CodingTheory\ProximityGap\GSInterpolationExistence.lean:67](../../../ArkLib\Data\CodingTheory\ProximityGap\GSInterpolationExistence.lean#L67) — (no docstring)

### `mem_support_simulateQ_id'_liftM_query` (2 declarations, 2 files)

- `lemma OptionT.mem_support_simulateQ_id'_liftM_query` [ArkLib\ToVCVio\Lemmas.lean:430](../../../ArkLib\ToVCVio\Lemmas.lean#L430) — **Generic**: any element of the range of a query is in the support of `simulateQ (fun t => liftM (qu
- `lemma mem_support_simulateQ_id'_liftM_query` [ArkLib\ToVCVio\Simulation.lean:217](../../../ArkLib\ToVCVio\Simulation.lean#L217) — (no docstring)

### `minDist_C` (2 declarations, 2 files)

- `theorem JohnsonBound.FamilyRefutation.minDist_C` [ArkLib\Data\CodingTheory\JohnsonBound\FamilyRefutation.lean:54](../../../ArkLib\Data\CodingTheory\JohnsonBound\FamilyRefutation.lean#L54) — Every distinct pair of codewords has Hamming distance `≥ 1`, and the pair `(c0, c1)` attains `1`. He
- `theorem JohnsonBound.JqlRefutation.minDist_C` [ArkLib\Data\CodingTheory\JohnsonBound\FamilyRefutationComplete.lean:97](../../../ArkLib\Data\CodingTheory\JohnsonBound\FamilyRefutationComplete.lean#L97) — **`Code.minDist C = 1`.**  The defining set of distinct-pair distances is `{1, 2}` (`d(c0,c1) = d(c0

### `mk_eq_trunc_of_tail_zero` (2 declarations, 2 files)

- `theorem ArkLib.BetaToCurveCoeffPolys.mk_eq_trunc_of_tail_zero` [ArkLib\ToMathlib\BetaToCurveCoeffPolysOffcentre.lean:86](../../../ArkLib\ToMathlib\BetaToCurveCoeffPolysOffcentre.lean#L86) — A power series whose coefficients vanish from index `k` on **is** (the coercion of) its `k`-truncati
- `theorem PowerSeries.mk_eq_trunc_of_tail_zero` [ArkLib\ToMathlib\ExtractedIssueBricks.lean:77](../../../ArkLib\ToMathlib\ExtractedIssueBricks.lean#L77) — A power series whose coefficients vanish from index `k` on equals the coercion of its `k`-truncation

### `multilinearWeight` (2 declarations, 2 files)

- `def multilinearWeight` [ArkLib\Data\CodingTheory\Prelims.lean:23](../../../ArkLib\Data\CodingTheory\Prelims.lean#L23) — The tensor product weight `⊗_{i=0}^{ϑ-1}(1 - rᵢ, rᵢ)` for a specific index `i` given randomness `r`.
- `def Issue33Binius.multilinearWeight` [ArkLib\ProofSystem\Binius\BinaryBasefold\MultilinearWeightRecursion.lean:24](../../../ArkLib\ProofSystem\Binius\BinaryBasefold\MultilinearWeightRecursion.lean#L24) — Tensor product weight `⊗_{j<ϑ}(1 - r_j, r_j)` at index `i` given challenges `r`. This is a verbatim

### `myH` (2 declarations, 2 files)

- `abbrev BCIKS20.HenselNumerator.WeightWitness.myH` [ArkLib\Data\CodingTheory\ProximityGap\BCIKS20\P1MonicWeightRefutation.lean:39](../../../ArkLib\Data\CodingTheory\ProximityGap\BCIKS20\P1MonicWeightRefutation.lean#L39) — Monic separable irreducible `H = Y² − 2` over `(ZMod 3)[X]`.
- `abbrev BCIKS20.HenselNumerator.Witness.myH` [ArkLib\Data\CodingTheory\ProximityGap\BCIKS20\P2OrderZeroRefutationWitness.lean:45](../../../ArkLib\Data\CodingTheory\ProximityGap\BCIKS20\P2OrderZeroRefutationWitness.lean#L45) — Non-monic irreducible `H = 2·Y` over `ℚ[X]` (leading coeff `2`, a unit ⟹ associate of `Y`).

### `myH_irreducible` (2 declarations, 2 files)

- `lemma BCIKS20.HenselNumerator.WeightWitness.myH_irreducible` [ArkLib\Data\CodingTheory\ProximityGap\BCIKS20\P1MonicWeightRefutation.lean:72](../../../ArkLib\Data\CodingTheory\ProximityGap\BCIKS20\P1MonicWeightRefutation.lean#L72) — (no docstring)
- `lemma BCIKS20.HenselNumerator.Witness.myH_irreducible` [ArkLib\Data\CodingTheory\ProximityGap\BCIKS20\P2OrderZeroRefutationWitness.lean:72](../../../ArkLib\Data\CodingTheory\ProximityGap\BCIKS20\P2OrderZeroRefutationWitness.lean#L72) — (no docstring)

### `myH_leadingCoeff` (2 declarations, 2 files)

- `lemma BCIKS20.HenselNumerator.WeightWitness.myH_leadingCoeff` [ArkLib\Data\CodingTheory\ProximityGap\BCIKS20\P1MonicWeightRefutation.lean:59](../../../ArkLib\Data\CodingTheory\ProximityGap\BCIKS20\P1MonicWeightRefutation.lean#L59) — (no docstring)
- `lemma BCIKS20.HenselNumerator.Witness.myH_leadingCoeff` [ArkLib\Data\CodingTheory\ProximityGap\BCIKS20\P2OrderZeroRefutationWitness.lean:64](../../../ArkLib\Data\CodingTheory\ProximityGap\BCIKS20\P2OrderZeroRefutationWitness.lean#L64) — (no docstring)

### `myH_natDegree` (2 declarations, 2 files)

- `lemma BCIKS20.HenselNumerator.WeightWitness.myH_natDegree` [ArkLib\Data\CodingTheory\ProximityGap\BCIKS20\P1MonicWeightRefutation.lean:53](../../../ArkLib\Data\CodingTheory\ProximityGap\BCIKS20\P1MonicWeightRefutation.lean#L53) — (no docstring)
- `lemma BCIKS20.HenselNumerator.Witness.myH_natDegree` [ArkLib\Data\CodingTheory\ProximityGap\BCIKS20\P2OrderZeroRefutationWitness.lean:60](../../../ArkLib\Data\CodingTheory\ProximityGap\BCIKS20\P2OrderZeroRefutationWitness.lean#L60) — (no docstring)

### `myH_separable` (2 declarations, 2 files)

- `lemma BCIKS20.HenselNumerator.WeightWitness.myH_separable` [ArkLib\Data\CodingTheory\ProximityGap\BCIKS20\P1MonicWeightRefutation.lean:89](../../../ArkLib\Data\CodingTheory\ProximityGap\BCIKS20\P1MonicWeightRefutation.lean#L89) — (no docstring)
- `lemma BCIKS20.HenselNumerator.Witness.myH_separable` [ArkLib\Data\CodingTheory\ProximityGap\BCIKS20\P2OrderZeroRefutationWitness.lean:96](../../../ArkLib\Data\CodingTheory\ProximityGap\BCIKS20\P2OrderZeroRefutationWitness.lean#L96) — (no docstring)

### `myHyp` (2 declarations, 2 files)

- `lemma BCIKS20.HenselNumerator.WeightWitness.myHyp` [ArkLib\Data\CodingTheory\ProximityGap\BCIKS20\P1MonicWeightRefutation.lean:102](../../../ArkLib\Data\CodingTheory\ProximityGap\BCIKS20\P1MonicWeightRefutation.lean#L102) — (no docstring)
- `lemma BCIKS20.HenselNumerator.Witness.myHyp` [ArkLib\Data\CodingTheory\ProximityGap\BCIKS20\P2OrderZeroRefutationWitness.lean:102](../../../ArkLib\Data\CodingTheory\ProximityGap\BCIKS20\P2OrderZeroRefutationWitness.lean#L102) — (no docstring)

### `myR` (2 declarations, 2 files)

- `abbrev BCIKS20.HenselNumerator.WeightWitness.myR` [ArkLib\Data\CodingTheory\ProximityGap\BCIKS20\P1MonicWeightRefutation.lean:43](../../../ArkLib\Data\CodingTheory\ProximityGap\BCIKS20\P1MonicWeightRefutation.lean#L43) — `R = Y² − 2 + u·s` (`u` = lift var, `s` = ground var): the high lift-direction degree breaks the wei
- `abbrev BCIKS20.HenselNumerator.Witness.myR` [ArkLib\Data\CodingTheory\ProximityGap\BCIKS20\P2OrderZeroRefutationWitness.lean:48](../../../ArkLib\Data\CodingTheory\ProximityGap\BCIKS20\P2OrderZeroRefutationWitness.lean#L48) — Witness `R = X_mid²·Y² + 2·Y + X_mid` in `ℚ[X][X][Y]`.

### `myR_natDegree` (2 declarations, 2 files)

- `lemma BCIKS20.HenselNumerator.WeightWitness.myR_natDegree` [ArkLib\Data\CodingTheory\ProximityGap\BCIKS20\P1MonicWeightRefutation.lean:79](../../../ArkLib\Data\CodingTheory\ProximityGap\BCIKS20\P1MonicWeightRefutation.lean#L79) — (no docstring)
- `lemma BCIKS20.HenselNumerator.Witness.myR_natDegree` [ArkLib\Data\CodingTheory\ProximityGap\BCIKS20\P2OrderZeroRefutationWitness.lean:92](../../../ArkLib\Data\CodingTheory\ProximityGap\BCIKS20\P2OrderZeroRefutationWitness.lean#L92) — (no docstring)

### `natDegree_taylor_lt` (2 declarations, 2 files)

- `theorem ArkLib.BetaToCurveCoeffPolys.natDegree_taylor_lt` [ArkLib\ToMathlib\BetaToCurveCoeffPolysOffcentre.lean:141](../../../ArkLib\ToMathlib\BetaToCurveCoeffPolysOffcentre.lean#L141) — Taylor shift preserves the strict degree bound of a coefficient profile.
- `theorem Polynomial.natDegree_taylor_lt` [ArkLib\ToMathlib\ExtractedIssueBricks.lean:67](../../../ArkLib\ToMathlib\ExtractedIssueBricks.lean#L67) — A strict degree bound transports through a Taylor shift.

### `nearCertainBadLine_of_allButOne` (2 declarations, 2 files)

- `theorem CodingTheory.Bridge.AllButOne.nearCertainBadLine_of_allButOne` [ArkLib\ToMathlib\BGKS20AllButOne.lean:86](../../../ArkLib\ToMathlib\BGKS20AllButOne.lean#L86) — **"All but one scalar" producer (BGKS20 line-witness shape).** Given a stack `u` that is **not** joi
- `theorem CodingTheory.Bridge.nearCertainBadLine_of_allButOne` [ArkLib\ToMathlib\NearCertainBadLineProof.lean:84](../../../ArkLib\ToMathlib\NearCertainBadLineProof.lean#L84) — **All-but-one producer for `NearCertainBadLine`.** If a stack is not jointly close and every scalar

### `nodal` (2 declarations, 2 files)

- `def Round21Relations.nodal` [ArkLib\Data\CodingTheory\ProximityGap\Conjecture41CliqueRelationModule.lean:60](../../../ArkLib\Data\CodingTheory\ProximityGap\Conjecture41CliqueRelationModule.lean#L60) — The nodal polynomial `Λ_W = ∏_{β ∈ W} (X − β)`.
- `def UniPoly.Lagrange.nodal` [ArkLib\Data\UniPoly\Basic.lean:1112](../../../ArkLib\Data\UniPoly\Basic.lean#L1112) — (no docstring)

### `nonvacuity_zmod5` (2 declarations, 2 files)

- `theorem ArkLib.ProximityGap.Round9SubgroupQuadraticHalving.nonvacuity_zmod5` [ArkLib\Data\CodingTheory\ProximityGap\SubgroupQuadraticHalving.lean:212](../../../ArkLib\Data\CodingTheory\ProximityGap\SubgroupQuadraticHalving.lean#L212) — **Non-vacuity witness.** Over `F = ZMod 5`, `2` is a primitive `4`-th root of unity (`2¹=2, 2²=4, 2³
- `theorem ArkLib.ProximityGap.Round8SeamARecursion.nonvacuity_zmod5` [ArkLib\Data\CodingTheory\ProximityGap\SubgroupSquaresHalvingRecursion.lean:261](../../../ArkLib\Data\CodingTheory\ProximityGap\SubgroupSquaresHalvingRecursion.lean#L261) — **Non-vacuity: a concrete order-`4` smooth subgroup whose squares are the order-`2` subgroup.** Over

### `nonvacuous_zmod13` (2 declarations, 2 files)

- `theorem ArkLib.CodingTheory.Round8FullConcentration.nonvacuous_zmod13` [ArkLib\Data\CodingTheory\ProximityGap\ListInteriorQIndependentNegSymm.lean:375](../../../ArkLib\Data\CodingTheory\ProximityGap\ListInteriorQIndependentNegSymm.lean#L375) — **Non-vacuity (concrete `ZMod 13`, `D = id`, `H = {1,2,3}`, `t = 2`, `k = 3`).** With `ι = ZMod 13`,
- `theorem ArkLib.CodingTheory.Round7Concentration.nonvacuous_zmod13` [ArkLib\Data\CodingTheory\ProximityGap\SubsetSumNegSymmConcentration.lean:312](../../../ArkLib\Data\CodingTheory\ProximityGap\SubsetSumNegSymmConcentration.lean#L312) — **Non-vacuity (the bound is genuine, not `0 ≤ …`).** Over `F = ZMod 13` (`13` prime, `(2:ZMod 13) ≠

### `not_exists_lt_floor_eq_of_lattice` (2 declarations, 2 files)

- `theorem ArkLib.Issue64Boundary.not_exists_lt_floor_eq_of_lattice` [ArkLib\Data\CodingTheory\ProximityGap\BoundaryCardLatticeSlice.lean:112](../../../ArkLib\Data\CodingTheory\ProximityGap\BoundaryCardLatticeSlice.lean#L112) — **The strict-below same-floor witness set is empty at a lattice point.**  Direct corollary of `floor
- `theorem ArkLib.BoundaryCardResidual.not_exists_lt_floor_eq_of_lattice` [ArkLib\Data\CodingTheory\ProximityGap\BoundaryCardResidual.lean:186](../../../ArkLib\Data\CodingTheory\ProximityGap\BoundaryCardResidual.lean#L186) — **No strict sub-radius has the same floor at a lattice endpoint.**  This records the precise failure

### `not_uniformEpsMCAgsPrizeBoundConjecture` (2 declarations, 2 files)

- `theorem ProximityGap.MCAGSPrizeRefutation.not_uniformEpsMCAgsPrizeBoundConjecture` [ArkLib\Data\CodingTheory\ProximityGap\MCAGSPrizeRefutation.lean:102](../../../ArkLib\Data\CodingTheory\ProximityGap\MCAGSPrizeRefutation.lean#L102) — **MAIN THEOREM (#141): the formalized uniform prize conjecture is FALSE.** `uniformEpsMCAgsPrizeBoun
- `theorem not_uniformEpsMCAgsPrizeBoundConjecture` [ArkLib\MCAGSRefutationCore_keep.lean:101](../../../ArkLib\MCAGSRefutationCore_keep.lean#L101) — **MAIN THEOREM (#141): the formalized uniform prize conjecture is FALSE.** `uniformEpsMCAgsPrizeBoun

### `one_le_Lambda_of_nonempty` (2 declarations, 2 files)

- `theorem CodingTheory.one_le_Lambda_of_nonempty` [ArkLib\Data\CodingTheory\ListSizeVolumeBound.lean:184](../../../ArkLib\Data\CodingTheory\ListSizeVolumeBound.lean#L184) — **List-size lower bound `1 ≤ \|Λ(C,δ)\|` for a nonempty code and `δ ≥ 0`.** Any codeword is `0`-close
- `lemma InterleavedCode.GGR11.one_le_Lambda_of_nonempty` [ArkLib\ToMathlib\GGR11TreeConstruction.lean:1247](../../../ArkLib\ToMathlib\GGR11TreeConstruction.lean#L1247) — With a nonempty code, a nonnegative radius, and finite lists, the maximised list size is at least on

### `openingPSpec` (2 declarations, 2 files)

- `def SimpleRO.openingPSpec` [ArkLib\CommitmentScheme\SimpleRO.lean:56](../../../ArkLib\CommitmentScheme\SimpleRO.lean#L56) — (no docstring)
- `abbrev Commitment.Transparent.openingPSpec` [ArkLib\CommitmentScheme\Transparent.lean:45](../../../ArkLib\CommitmentScheme\Transparent.lean#L45) — The one-message protocol specification of the transparent opening: the prover sends a single (conten

### `oracleVerifier_toVerifier_run` (2 declarations, 2 files)

- `theorem ReduceClaim.oracleVerifier_toVerifier_run` [ArkLib\ProofSystem\Component\ReduceClaim.lean:267](../../../ArkLib\ProofSystem\Component\ReduceClaim.lean#L267) — Running the (oracle) verifier of the `ReduceClaim` oracle reduction deterministically returns the ma
- `theorem SendSingleWitness.oracleVerifier_toVerifier_run` [ArkLib\ProofSystem\Component\SendWitness.lean:404](../../../ArkLib\ProofSystem\Component\SendWitness.lean#L404) — (no docstring)

### `p6_deg` (2 declarations, 2 files)

- `lemma ArkLib.CodingTheory.TinyInteriorK3.p6_deg` [ArkLib\Data\CodingTheory\ProximityGap\ListInteriorPinF11K3.lean:148](../../../ArkLib\Data\CodingTheory\ProximityGap\ListInteriorPinF11K3.lean#L148) — (no docstring)
- `lemma ArkLib.CodingTheory.Round3SmoothF17.p6_deg` [ArkLib\Data\CodingTheory\ProximityGap\ListInteriorPinF17Subgroup.lean:158](../../../ArkLib\Data\CodingTheory\ProximityGap\ListInteriorPinF17Subgroup.lean#L158) — (no docstring)

### `pSpecCoreInteraction` (2 declarations, 2 files)

- `def Binius.BinaryBasefold.pSpecCoreInteraction` [ArkLib\ProofSystem\Binius\BinaryBasefold\Spec.lean:248](../../../ArkLib\ProofSystem\Binius\BinaryBasefold\Spec.lean#L248) — (no docstring)
- `def RingSwitching.pSpecCoreInteraction` [ArkLib\ProofSystem\RingSwitching\Spec.lean:50](../../../ArkLib\ProofSystem\RingSwitching\Spec.lean#L50) — (no docstring)

### `pSpecFold` (2 declarations, 2 files)

- `def Binius.BinaryBasefold.pSpecFold` [ArkLib\ProofSystem\Binius\BinaryBasefold\Spec.lean:201](../../../ArkLib\ProofSystem\Binius\BinaryBasefold\Spec.lean#L201) — (no docstring)
- `def Fri.Spec.pSpecFold` [ArkLib\ProofSystem\Fri\Spec\General.lean:66](../../../ArkLib\ProofSystem\Fri\Spec\General.lean#L66) — (no docstring)

### `pSpecSumcheckRound` (2 declarations, 2 files)

- `abbrev RingSwitching.pSpecSumcheckRound` [ArkLib\ProofSystem\RingSwitching\Spec.lean:41](../../../ArkLib\ProofSystem\RingSwitching\Spec.lean#L41) — (no docstring)
- `def Sumcheck.Structured.pSpecSumcheckRound` [ArkLib\ProofSystem\Sumcheck\Structured\SingleRound.lean:256](../../../ArkLib\ProofSystem\Sumcheck\Structured\SingleRound.lean#L256) — Protocol spec for one round of the structured sumcheck: P sends a degree-≤`d` univariate `h_i(X) ∈ L

### `pSpec_dir_zero` (2 declarations, 2 files)

- `theorem StirIOP.Round.pSpec_dir_zero` [ArkLib\ProofSystem\Stir\RoundProtocol.lean:65](../../../ArkLib\ProofSystem\Stir\RoundProtocol.lean#L65) — (no docstring)
- `theorem Sumcheck.Spec.SingleRound.pSpec_dir_zero` [ArkLib\ProofSystem\Sumcheck\Spec\Completeness.lean:70](../../../ArkLib\ProofSystem\Sumcheck\Spec\Completeness.lean#L70) — The sum-check round protocol leads with the prover's univariate-polynomial message.

### `perfectCorrectness` (2 declarations, 2 files)

- `def Commitment.perfectCorrectness` [ArkLib\CommitmentScheme\Basic.lean:109](../../../ArkLib\CommitmentScheme\Basic.lean#L109) — A commitment scheme satisfies **perfect correctness** if it satisfies correctness with no error.
- `def CommitmentScheme.perfectCorrectness` [ArkLib\CommitmentScheme\CommitmentScheme.lean:74](../../../ArkLib\CommitmentScheme\CommitmentScheme.lean#L74) — A commitment scheme satisfies **perfect correctness** if it satisfies correctness with no error.

### `perfectHVZK` (2 declarations, 2 files)

- `def OracleReduction.perfectHVZK` [ArkLib\OracleReduction\Security\OracleZeroKnowledge.lean:44](../../../ArkLib\OracleReduction\Security\OracleZeroKnowledge.lean#L44) — Perfect HVZK for an oracle reduction, delegated through `OracleReduction.toReduction`.
- `def Reduction.perfectHVZK` [ArkLib\OracleReduction\Security\ZeroKnowledge.lean:69](../../../ArkLib\OracleReduction\Security\ZeroKnowledge.lean#L69) — A reduction satisfies perfect honest-verifier zero-knowledge with respect to a simulator and relatio

### `perfectHVZK.congr_honestDist` (2 declarations, 2 files)

- `theorem OracleReduction.perfectHVZK.congr_honestDist` [ArkLib\ToMathlib\OracleZKTransferBricks.lean:33](../../../ArkLib\ToMathlib\OracleZKTransferBricks.lean#L33) — **OracleReduction perfect HVZK transfers along an equal honest distribution.**
- `theorem Reduction.perfectHVZK.congr_honestDist` [ArkLib\ToMathlib\ZKTransferBricks.lean:64](../../../ArkLib\ToMathlib\ZKTransferBricks.lean#L64) — **Perfect HVZK transfers along an `evalDist`-equal honest distribution.** If two reductions have the

### `perfectHVZK.congr_honestDist_symm` (2 declarations, 2 files)

- `theorem OracleReduction.perfectHVZK.congr_honestDist_symm` [ArkLib\ToMathlib\OracleZKTransferBricks.lean:59](../../../ArkLib\ToMathlib\OracleZKTransferBricks.lean#L59) — **OracleReduction perfect HVZK honest-distribution congruence with opposite-order equality.**
- `theorem Reduction.perfectHVZK.congr_honestDist_symm` [ArkLib\ToMathlib\ZKTransferBricks.lean:96](../../../ArkLib\ToMathlib\ZKTransferBricks.lean#L96) — **Perfect HVZK honest-distribution congruence with opposite-order equality.**

### `perfectHVZK.isHVZK` (2 declarations, 2 files)

- `theorem OracleReduction.perfectHVZK.isHVZK` [ArkLib\ToMathlib\OracleZKTransferBricks.lean:130](../../../ArkLib\ToMathlib\OracleZKTransferBricks.lean#L130) — **A concrete OracleReduction perfect-HVZK simulator witnesses existential HVZK.**
- `theorem Reduction.perfectHVZK.isHVZK` [ArkLib\ToMathlib\ZKTransferBricks.lean:174](../../../ArkLib\ToMathlib\ZKTransferBricks.lean#L174) — **A concrete perfect-HVZK simulator witnesses existential HVZK.**

### `perfectHVZK.isHVZK_of_simulator_congr` (2 declarations, 2 files)

- `theorem OracleReduction.perfectHVZK.isHVZK_of_simulator_congr` [ArkLib\ToMathlib\OracleZKTransferBricks.lean:152](../../../ArkLib\ToMathlib\OracleZKTransferBricks.lean#L152) — **Package an OracleReduction perfect-HVZK proof after normalizing the simulator distribution.**
- `theorem Reduction.perfectHVZK.isHVZK_of_simulator_congr` [ArkLib\ToMathlib\ZKTransferBricks.lean:194](../../../ArkLib\ToMathlib\ZKTransferBricks.lean#L194) — **Package a perfect-HVZK proof after normalizing the simulator distribution.**

### `perfectHVZK.isHVZK_of_simulator_congr_symm` (2 declarations, 2 files)

- `theorem OracleReduction.perfectHVZK.isHVZK_of_simulator_congr_symm` [ArkLib\ToMathlib\OracleZKTransferBricks.lean:176](../../../ArkLib\ToMathlib\OracleZKTransferBricks.lean#L176) — **Package an OracleReduction perfect-HVZK proof after simulator normalization in the opposite direct
- `theorem Reduction.perfectHVZK.isHVZK_of_simulator_congr_symm` [ArkLib\ToMathlib\ZKTransferBricks.lean:216](../../../ArkLib\ToMathlib\ZKTransferBricks.lean#L216) — **Package a perfect-HVZK proof after simulator normalization in the opposite direction.**

### `perfectHVZK.mono_relation` (2 declarations, 2 files)

- `theorem OracleReduction.perfectHVZK.mono_relation` [ArkLib\OracleReduction\Security\OracleZeroKnowledge.lean:107](../../../ArkLib\OracleReduction\Security\OracleZeroKnowledge.lean#L107) — Perfect HVZK for oracle reductions is antitone in the relation.
- `theorem Reduction.perfectHVZK.mono_relation` [ArkLib\OracleReduction\Security\ZeroKnowledge.lean:156](../../../ArkLib\OracleReduction\Security\ZeroKnowledge.lean#L156) — **Perfect HVZK is antitone in the relation.** A simulator that matches the honest transcript distrib

### `perfectHVZK.simulator_congr` (2 declarations, 2 files)

- `theorem OracleReduction.perfectHVZK.simulator_congr` [ArkLib\ToMathlib\OracleZKTransferBricks.lean:86](../../../ArkLib\ToMathlib\OracleZKTransferBricks.lean#L86) — **OracleReduction perfect HVZK is preserved under an equal simulator distribution.**
- `theorem Reduction.perfectHVZK.simulator_congr` [ArkLib\ToMathlib\ZKTransferBricks.lean:123](../../../ArkLib\ToMathlib\ZKTransferBricks.lean#L123) — **Perfect HVZK is preserved under an `evalDist`-equal simulator.** Swapping in a simulator that prod

### `perfectHVZK.simulator_congr_symm` (2 declarations, 2 files)

- `theorem OracleReduction.perfectHVZK.simulator_congr_symm` [ArkLib\ToMathlib\OracleZKTransferBricks.lean:108](../../../ArkLib\ToMathlib\OracleZKTransferBricks.lean#L108) — **OracleReduction perfect HVZK simulator congruence with opposite-order equality.**
- `theorem Reduction.perfectHVZK.simulator_congr_symm` [ArkLib\ToMathlib\ZKTransferBricks.lean:152](../../../ArkLib\ToMathlib\ZKTransferBricks.lean#L152) — **Perfect HVZK simulator congruence with opposite-order equality.**

### `perfectHVZK.statisticalHVZK` (2 declarations, 2 files)

- `theorem OracleReduction.perfectHVZK.statisticalHVZK` [ArkLib\OracleReduction\Security\OracleZeroKnowledge.lean:96](../../../ArkLib\OracleReduction\Security\OracleZeroKnowledge.lean#L96) — Perfect HVZK for oracle reductions implies statistical HVZK with any error bound.
- `theorem Reduction.perfectHVZK.statisticalHVZK` [ArkLib\OracleReduction\Security\ZeroKnowledge.lean:137](../../../ArkLib\OracleReduction\Security\ZeroKnowledge.lean#L137) — Perfect HVZK implies statistical HVZK with any error `ε`.

### `perfectHVZK.statisticalHVZK_mono_relation` (2 declarations, 2 files)

- `theorem OracleReduction.perfectHVZK.statisticalHVZK_mono_relation` [ArkLib\OracleReduction\Security\OracleZeroKnowledge.lean:224](../../../ArkLib\OracleReduction\Security\OracleZeroKnowledge.lean#L224) — Perfect HVZK for oracle reductions transports to statistical HVZK on a subrelation at any error. The
- `theorem Reduction.perfectHVZK.statisticalHVZK_mono_relation` [ArkLib\OracleReduction\Security\ZeroKnowledge.lean:262](../../../ArkLib\OracleReduction\Security\ZeroKnowledge.lean#L262) — **Perfect HVZK transports to statistical HVZK on a subrelation at any error.** The same simulator is

### `perfectHVZK.triangle_honestDist_symm_zero` (2 declarations, 2 files)

- `theorem OracleReduction.perfectHVZK.triangle_honestDist_symm_zero` [ArkLib\ToMathlib\OracleZKTransferBricks.lean:283](../../../ArkLib\ToMathlib\OracleZKTransferBricks.lean#L283) — Symmetric-facing zero-error approximate honest-distribution transfer for perfect HVZK at the OracleR
- `theorem Reduction.perfectHVZK.triangle_honestDist_symm_zero` [ArkLib\ToMathlib\ZKTransferBricks.lean:362](../../../ArkLib\ToMathlib\ZKTransferBricks.lean#L362) — Symmetric-facing zero-error approximate honest-distribution transfer for perfect HVZK.

### `perfectHVZK.triangle_honestDist_zero` (2 declarations, 2 files)

- `theorem OracleReduction.perfectHVZK.triangle_honestDist_zero` [ArkLib\ToMathlib\OracleZKTransferBricks.lean:269](../../../ArkLib\ToMathlib\OracleZKTransferBricks.lean#L269) — **Zero-error approximate honest-distribution transfer for perfect HVZK at the OracleReduction API bo
- `theorem Reduction.perfectHVZK.triangle_honestDist_zero` [ArkLib\ToMathlib\ZKTransferBricks.lean:342](../../../ArkLib\ToMathlib\ZKTransferBricks.lean#L342) — **Zero-error approximate honest-distribution transfer for perfect HVZK.** If the honest-transcript b

### `perfectHVZK_iff_statisticalHVZK_zero` (2 declarations, 2 files)

- `theorem OracleReduction.perfectHVZK_iff_statisticalHVZK_zero` [ArkLib\OracleReduction\Security\OracleZeroKnowledge.lean:85](../../../ArkLib\OracleReduction\Security\OracleZeroKnowledge.lean#L85) — Perfect HVZK for oracle reductions is exactly statistical HVZK with error `0`.
- `theorem Reduction.perfectHVZK_iff_statisticalHVZK_zero` [ArkLib\OracleReduction\Security\ZeroKnowledge.lean:109](../../../ArkLib\OracleReduction\Security\ZeroKnowledge.lean#L109) — Perfect HVZK is exactly statistical HVZK with error `0`.

### `perfectHVZK_of_const_eq_honestDist` (2 declarations, 2 files)

- `theorem OracleReduction.perfectHVZK_of_const_eq_honestDist` [ArkLib\ToMathlib\OracleZKTransferBricks.lean:321](../../../ArkLib\ToMathlib\OracleZKTransferBricks.lean#L321) — **Symmetric-facing OracleReduction constant-simulator criterion for perfect HVZK.**
- `theorem Reduction.perfectHVZK_of_const_eq_honestDist` [ArkLib\ToMathlib\ZKTransferBricks.lean:406](../../../ArkLib\ToMathlib\ZKTransferBricks.lean#L406) — **Symmetric-facing constant-simulator criterion for perfect HVZK.**

### `perfectHVZK_of_honestDist_eq_const` (2 declarations, 2 files)

- `theorem OracleReduction.perfectHVZK_of_honestDist_eq_const` [ArkLib\ToMathlib\OracleZKTransferBricks.lean:296](../../../ArkLib\ToMathlib\OracleZKTransferBricks.lean#L296) — **OracleReduction constant-simulator criterion for perfect HVZK.**
- `theorem Reduction.perfectHVZK_of_honestDist_eq_const` [ArkLib\ToMathlib\ZKTransferBricks.lean:380](../../../ArkLib\ToMathlib\ZKTransferBricks.lean#L380) — **Constant-simulator criterion for perfect HVZK.** If the honest transcript distribution is `evalDis

### `perfectlyCorrect` (2 declarations, 2 files)

- `theorem ArkLib.Lattices.Ajtai.InnerOuter.perfectlyCorrect` [ArkLib\CommitmentScheme\Ajtai\InnerOuter\Correctness.lean:198](../../../ArkLib\CommitmentScheme\Ajtai\InnerOuter\Correctness.lean#L198) — **Unconditional perfect correctness with the concrete binary decomposition.** Both message and inner
- `theorem ArkLib.Lattices.Ajtai.Simple.perfectlyCorrect` [ArkLib\CommitmentScheme\Ajtai\Simple\Correctness.lean:33](../../../ArkLib\CommitmentScheme\Ajtai\Simple\Correctness.lean#L33) — Simple Ajtai commitments are correct on short messages: an honest commitment to a message accepted b

### `pow_eq_card_eq_zero_or_gcd` (2 declarations, 2 files)

- `theorem ProximityGap.MultiplicativeRigidity.pow_eq_card_eq_zero_or_gcd` [ArkLib\Data\CodingTheory\ProximityGap\MultiplicativeRigidityFiber.lean:63](../../../ArkLib\Data\CodingTheory\ProximityGap\MultiplicativeRigidityFiber.lean#L63) — **Lemma 1 (monomial agreement / coset rigidity).** In a finite cyclic commutative group `G` of order
- `theorem MultiplicativeRigidity.pow_eq_card_eq_zero_or_gcd` [ArkLib\Data\CodingTheory\ProximityGap\MultiplicativeRigidityZMod.lean:99](../../../ArkLib\Data\CodingTheory\ProximityGap\MultiplicativeRigidityZMod.lean#L99) — **Coset rigidity / monomial agreement (core).** In a finite cyclic group `G` of order `n = Fintype.c

### `pow_half_eq_neg_one` (2 declarations, 2 files)

- `theorem R12.pow_half_eq_neg_one` [ArkLib\Data\CodingTheory\ProximityGap\LamLeungUnconditionalGeneral.lean:165](../../../ArkLib\Data\CodingTheory\ProximityGap\LamLeungUnconditionalGeneral.lean#L165) — For a primitive `2^m`-th root of unity `ζ` (`m ≥ 1`), `ζ^{2^{m-1}} = -1`: `ζ^{2^{m-1}}` is a primiti
- `theorem ArkLib.ProximityGap.Round3SubgroupSumsetDirect.pow_half_eq_neg_one` [ArkLib\Data\CodingTheory\ProximityGap\SubgroupSumsetThreePowUpper.lean:79](../../../ArkLib\Data\CodingTheory\ProximityGap\SubgroupSumsetThreePowUpper.lean#L79) — For a primitive `2N`-th root of unity `ζ` (`N ≥ 1`), `ζ^N = -1`: `ζ^N` is a primitive square root of

### `probEvent_bind_eq_one` (2 declarations, 2 files)

- `lemma OracleComp.probEvent_bind_eq_one` [ArkLib\OracleReduction\ProbOneBindCompose.lean:40](../../../ArkLib\OracleReduction\ProbOneBindCompose.lean#L40) — **Probability-one bind composition.** If `mx` satisfies `p` with probability `1`, and `f a` satisfie
- `theorem probEvent_bind_eq_one` [ArkLib\ToMathlib\ProbEventBindOne.lean:29](../../../ArkLib\ToMathlib\ProbEventBindOne.lean#L29) — **Two-stage perfect composition.** If `mx` produces an output satisfying `P` with probability 1, and

### `probEvent_optionT_mk_eq_elim` (2 declarations, 2 files)

- `lemma probEvent_optionT_mk_eq_elim` [ArkLib\OracleReduction\Composition\Sequential\AppendSoundnessProof.lean:71](../../../ArkLib\OracleReduction\Composition\Sequential\AppendSoundnessProof.lean#L71) — **`OptionT.mk` event = `Option.elim`-bad event on the underlying computation.** Bridges the soundnes
- `theorem Verifier.StateFunction.probEvent_optionT_mk_eq_elim` [ArkLib\OracleReduction\Security\RoundByRound.lean:292](../../../ArkLib\OracleReduction\Security\RoundByRound.lean#L292) — **`OptionT` probEvent as a success-conjunction on the underlying computation.**  An `OptionT ProbCom

### `probEvent_uniformSample_eq_Pr_uniform` (2 declarations, 2 files)

- `theorem RingSwitching.BatchingPhase.probEvent_uniformSample_eq_Pr_uniform` [ArkLib\ProofSystem\RingSwitching\BatchingPhase.lean:57](../../../ArkLib\ProofSystem\RingSwitching\BatchingPhase.lean#L57) — Bridge the framework's `SampleableType` uniform sampler to the PMF uniform notation used by Schwartz
- `theorem RingSwitching.SumcheckPhase.probEvent_uniformSample_eq_Pr_uniform` [ArkLib\ProofSystem\RingSwitching\SumcheckPhase.lean:63](../../../ArkLib\ProofSystem\RingSwitching\SumcheckPhase.lean#L63) — Bridge the framework's `SampleableType` uniform sampler to the PMF uniform notation used by some sta

### `prod_X_sub_C_injOn_subsets` (2 declarations, 2 files)

- `theorem ArkLib.CodingTheory.Round4InteriorList.prod_X_sub_C_injOn_subsets` [ArkLib\Data\CodingTheory\ProximityGap\InteriorListCountBridge.lean:128](../../../ArkLib\Data\CodingTheory\ProximityGap\InteriorListCountBridge.lean#L128) — The two root products are equal as polynomials iff the subsets are equal (`D` injective).
- `theorem ArkLib.CodingTheory.CapacityLowerSharpen.prod_X_sub_C_injOn_subsets` [ArkLib\Data\CodingTheory\ProximityGap\ListCapacityFieldIndependent.lean:128](../../../ArkLib\Data\CodingTheory\ProximityGap\ListCapacityFieldIndependent.lean#L128) — The two root products are equal as polynomials iff the subsets are equal (`D` injective).

### `prop_4_23_singleRepetition_proximityCheck_bound` (2 declarations, 2 files)

- `theorem Binius.BinaryBasefold.QueryPhase.prop_4_23_singleRepetition_proximityCheck_bound` [ArkLib\ProofSystem\Binius\BinaryBasefold\QueryPhase.lean:2690](../../../ArkLib\ProofSystem\Binius\BinaryBasefold\QueryPhase.lean#L2690) — **Single Repetition Proximity Check Bound (Proposition 4.24)** For a single repetition of the proxim
- `theorem Binius.BinaryBasefold.prop_4_23_singleRepetition_proximityCheck_bound` [ArkLib\ProofSystem\Binius\BinaryBasefold\Soundness\QueryPhaseSoundness.lean:1267](../../../ArkLib\ProofSystem\Binius\BinaryBasefold\Soundness\QueryPhaseSoundness.lean#L1267) — **Proposition 4.24** (Query-phase soundness, assuming no bad events). If any oracle is non-compliant

### `proximityCondition` (2 declarations, 2 files)

- `def MutualCorrAgreement.proximityCondition` [ArkLib\ProofSystem\Whir\MutualCorrAgreement.lean:56](../../../ArkLib\ProofSystem\Whir\MutualCorrAgreement.lean#L56) — For `parℓ` functions `fᵢ : ι → 𝔽`, distance `δ`, generator function `GenFun: 𝔽 → parℓ → 𝔽` and linea
- `def Generator.proximityCondition` [ArkLib\ProofSystem\Whir\ProximityGen.lean:38](../../../ArkLib\ProofSystem\Whir\ProximityGen.lean#L38) — For `l` functions `fᵢ : ι → 𝔽`, distance `δ`, generator function `GenFun: 𝔽 → parℓ → 𝔽ˡ` and linear

### `queryCodeword` (2 declarations, 2 files)

- `def Binius.BinaryBasefold.QueryPhase.queryCodeword` [ArkLib\ProofSystem\Binius\BinaryBasefold\Soundness\QueryPhasePrelims.lean:182](../../../ArkLib\ProofSystem\Binius\BinaryBasefold\Soundness\QueryPhasePrelims.lean#L182) — Oracle query helper: query a committed codeword at a given domain point. Restricted to codeword indi
- `def Fri.Spec.QueryRound.queryCodeword` [ArkLib\ProofSystem\Fri\Spec\SingleRound.lean:1019](../../../ArkLib\ProofSystem\Fri\Spec\SingleRound.lean#L1019) — (no docstring)

### `queryOracleReduction` (2 declarations, 2 files)

- `def Binius.BinaryBasefold.QueryPhase.queryOracleReduction` [ArkLib\ProofSystem\Binius\BinaryBasefold\QueryPhase.lean:174](../../../ArkLib\ProofSystem\Binius\BinaryBasefold\QueryPhase.lean#L174) — The oracle reduction for the final query phase.
- `def Fri.Spec.QueryRound.queryOracleReduction` [ArkLib\ProofSystem\Fri\Spec\SingleRound.lean:1137](../../../ArkLib\ProofSystem\Fri\Spec\SingleRound.lean#L1137) — (no docstring)

### `rbrBudgetSet` (2 declarations, 2 files)

- `def Core2Keystone.rbrBudgetSet` [ArkLib\ProofSystem\Whir\KeystoneReduction.lean:57](../../../ArkLib\ProofSystem\Whir\KeystoneReduction.lean#L57) — The WHIR per-challenge RBR budget set (verbatim shape from `Whir/RbrBudgetAccounting.lean`). Reprodu
- `def Issue113WHIR.rbrBudgetSet` [ArkLib\ProofSystem\Whir\RbrBudgetAccounting.lean:55](../../../ArkLib\ProofSystem\Whir\RbrBudgetAccounting.lean#L55) — The WHIR RBR budget set: the union of the four per-round budget families, as a `Finset ℝ≥0`. This is

### `rbrBudgetSet_nonempty` (2 declarations, 2 files)

- `theorem Core2Keystone.rbrBudgetSet_nonempty` [ArkLib\ProofSystem\Whir\KeystoneReduction.lean:63](../../../ArkLib\ProofSystem\Whir\KeystoneReduction.lean#L63) — (no docstring)
- `theorem Issue113WHIR.rbrBudgetSet_nonempty` [ArkLib\ProofSystem\Whir\RbrBudgetAccounting.lean:62](../../../ArkLib\ProofSystem\Whir\RbrBudgetAccounting.lean#L62) — The budget set is nonempty (it contains `ε_fin`). This is the side condition the in-tree `max' (by s

### `rbrExtractionFailureEvent` (2 declarations, 2 files)

- `def RingSwitching.BatchingPhase.rbrExtractionFailureEvent` [ArkLib\ProofSystem\RingSwitching\BatchingPhase.lean:911](../../../ArkLib\ProofSystem\RingSwitching\BatchingPhase.lean#L911) — Extraction-failure/doom-escape event for the batching phase RBR proof.
- `def RingSwitching.SumcheckPhase.rbrExtractionFailureEvent` [ArkLib\ProofSystem\RingSwitching\SumcheckPhase.lean:893](../../../ArkLib\ProofSystem\RingSwitching\SumcheckPhase.lean#L893) — Extraction failure implies a witness-dependent bad sumcheck event. The extracted `witMid` also carri

### `reduction_verifier_eq_verifier` (2 declarations, 2 files)

- `lemma Sumcheck.Spec.reduction_verifier_eq_verifier` [ArkLib\ProofSystem\Sumcheck\Spec\General.lean:193](../../../ArkLib\ProofSystem\Sumcheck\Spec\General.lean#L193) — (no docstring)
- `lemma Sumcheck.Spec.SingleRound.reduction_verifier_eq_verifier` [ArkLib\ProofSystem\Sumcheck\Spec\SingleRound.lean:1401](../../../ArkLib\ProofSystem\Sumcheck\Spec\SingleRound.lean#L1401) — (no docstring)

### `relIn` (2 declarations, 2 files)

- `def CheckClaim.relIn` [ArkLib\ProofSystem\Component\CheckClaim.lean:61](../../../ArkLib\ProofSystem\Component\CheckClaim.lean#L61) — (no docstring)
- `def RandomQuery.relIn` [ArkLib\ProofSystem\Component\RandomQuery.lean:44](../../../ArkLib\ProofSystem\Component\RandomQuery.lean#L44) — The input relation is that the two oracles are equal.

### `rewindingKnowledgeSoundness` (2 declarations, 2 files)

- `abbrev DuplexSpongeFS.NARG.rewindingKnowledgeSoundness` [ArkLib\OracleReduction\FiatShamir\DuplexSponge\Basic.lean:159](../../../ArkLib\OracleReduction\FiatShamir\DuplexSponge\Basic.lean#L159) — Paper-facing alias for CO25 Definition 3.8 rewinding knowledge soundness.
- `def Verifier.rewindingKnowledgeSoundness` [ArkLib\OracleReduction\Security\Rewinding.lean:211](../../../ArkLib\OracleReduction\Security\Rewinding.lean#L211) — CO25 Definition 3.8, adapted to ArkLib's non-interactive argument interface. ArkLib's `Prover.NARG`

### `rewindingKnowledgeSoundnessFamily` (2 declarations, 2 files)

- `abbrev DuplexSpongeFS.NARG.rewindingKnowledgeSoundnessFamily` [ArkLib\OracleReduction\FiatShamir\DuplexSponge\Basic.lean:176](../../../ArkLib\OracleReduction\FiatShamir\DuplexSponge\Basic.lean#L176) — Paper-facing alias for CO25 Definition 3.8 with explicit security parameter `λ`.
- `def Verifier.rewindingKnowledgeSoundnessFamily` [ArkLib\OracleReduction\Security\Rewinding.lean:264](../../../ArkLib\OracleReduction\Security\Rewinding.lean#L264) — CO25 Definition 3.8 with the security parameter `λ` made explicit as an external index. This is a wr

### `rightpad` (2 declarations, 2 files)

- `def Fin.rightpad` [ArkLib\Data\Fin\Tuple\Defs.lean:90](../../../ArkLib\Data\Fin\Tuple\Defs.lean#L90) — Pad a `Fin`-indexed vector on the right with an element `a`. This becomes truncation if `n < m`.
- `def Matrix.rightpad` [ArkLib\Data\Matrix\Basic.lean:21](../../../ArkLib\Data\Matrix\Basic.lean#L21) — (no docstring)

### `roundKnowledgeError` (2 declarations, 2 files)

- `abbrev RingSwitching.SumcheckPhase.roundKnowledgeError` [ArkLib\ProofSystem\RingSwitching\SumcheckPhase.lean:251](../../../ArkLib\ProofSystem\RingSwitching\SumcheckPhase.lean#L251) — Repaired local bound for the current round-by-round proof. The degree-two bad-event lemma below is t
- `def Sumcheck.Structured.roundKnowledgeError` [ArkLib\ProofSystem\Sumcheck\Structured\SingleRound.lean:473](../../../ArkLib\ProofSystem\Sumcheck\Structured\SingleRound.lean#L473) — Round-by-round knowledge error for a single round of the structured sumcheck: the Schwartz–Zippel bo

### `run` (2 declarations, 2 files)

- `def AGM.Adversary.run` [ArkLib\AGM\Basic.lean:484](../../../ArkLib\AGM\Basic.lean#L484) — Running the adversary on a given table, returning the list of group elements it is supposed to outpu
- `def Prover.run` [ArkLib\OracleReduction\Execution.lean:97](../../../ArkLib\OracleReduction\Execution.lean#L97) — Run the prover in an interactive reduction. Returns the output statement and witness, and the transc

### `secondSCVP_mem_restrictDegree` (2 declarations, 2 files)

- `theorem Spartan.Spec.secondSCVP_mem_restrictDegree` [ArkLib\ProofSystem\Spartan\SecondSumcheckReduction.lean:76](../../../ArkLib\ProofSystem\Spartan\SecondSumcheckReduction.lean#L76) — The second sum-check virtual polynomial has degree `<= 2` per variable.
- `theorem Spartan.secondSCVP_mem_restrictDegree` [ArkLib\ProofSystem\Spartan\SumcheckDegreeBound.lean:74](../../../ArkLib\ProofSystem\Spartan\SumcheckDegreeBound.lean#L74) — **Degree bound of the second sum-check virtual polynomial** (`≤ 2` per variable): packages `ℳ(Y)` fo

### `seqComposeError_eq_append` (2 declarations, 2 files)

- `theorem Verifier.seqComposeError_eq_append` [ArkLib\OracleReduction\Composition\Sequential\General.lean:608](../../../ArkLib\OracleReduction\Composition\Sequential\General.lean#L608) — The RBR error of a sequential composition, expressed via `seqComposeChallengeIdxToSigma` over the *g
- `theorem ArkLib.SeqComposeRbrSoundness.seqComposeError_eq_append` [ArkLib\ProofSystem\Sumcheck\Spec\SeqComposeRbrSoundness.lean:150](../../../ArkLib\ProofSystem\Sumcheck\Spec\SeqComposeRbrSoundness.lean#L150) — **The composed RBR error, indexed via `seqComposeChallengeIdxToSigma` over the global challenge inde

### `seqCompose_perfectCompleteness_threaded` (2 declarations, 2 files)

- `theorem OracleReduction.seqCompose_perfectCompleteness_threaded` [ArkLib\OracleReduction\Composition\Sequential\SeqComposeOracleCompleteness.lean:107](../../../ArkLib\OracleReduction\Composition\Sequential\SeqComposeOracleCompleteness.lean#L107) — **n-ary message-seam `seqCompose` perfect completeness for oracle reductions (issue #29).** Every co
- `theorem Reduction.seqCompose_perfectCompleteness_threaded` [ArkLib\OracleReduction\Composition\Sequential\SeqComposePerfectCompletenessThreaded.lean:59](../../../ArkLib\OracleReduction\Composition\Sequential\SeqComposePerfectCompletenessThreaded.lean#L59) — **n-ary message-seam `seqCompose` perfect completeness, keystones inlined.** Every component is none

### `shiftSeries` (2 declarations, 2 files)

- `def ArkLib.Claim59Conditional.shiftSeries` [ArkLib\ToMathlib\Claim59Conditional.lean:53](../../../ArkLib\ToMathlib\Claim59Conditional.lean#L53) — The BCIKS shift series corresponding to the substitution $X \mapsto X - x_0$.
- `def ArkLib.SubstFieldCaveat.shiftSeries` [ArkLib\ToMathlib\SubstFieldCaveat.lean:75](../../../ArkLib\ToMathlib\SubstFieldCaveat.lean#L75) — The shift series corresponding to the substitution $X \mapsto X - x_0$.

### `simulateQ_optionT_failure'` (2 declarations, 2 files)

- `theorem Logup.simulateQ_optionT_failure'` [ArkLib\ProofSystem\Logup\Security\OuterRun.lean:52](../../../ArkLib\ProofSystem\Logup\Security\OuterRun.lean#L52) — `simulateQ` commutes with `OptionT` `failure`.
- `theorem RingSwitching.SumcheckPhase.simulateQ_optionT_failure'` [ArkLib\ProofSystem\RingSwitching\SumcheckPhase.lean:102](../../../ArkLib\ProofSystem\RingSwitching\SumcheckPhase.lean#L102) — `simulateQ` commutes with `OptionT` `failure`, for an arbitrary lawful target monad `m` (so it appli

### `simulateQ_optionT_pure'` (2 declarations, 2 files)

- `theorem Logup.simulateQ_optionT_pure'` [ArkLib\ProofSystem\Logup\Security\OuterRun.lean:44](../../../ArkLib\ProofSystem\Logup\Security\OuterRun.lean#L44) — `simulateQ` commutes with `OptionT.pure`.
- `theorem RingSwitching.SumcheckPhase.simulateQ_optionT_pure'` [ArkLib\ProofSystem\RingSwitching\SumcheckPhase.lean:91](../../../ArkLib\ProofSystem\RingSwitching\SumcheckPhase.lean#L91) — `simulateQ` commutes with `OptionT.pure` (no explicit empty-spec universes).

### `simulateQ_oracleVerify_eq` (2 declarations, 2 files)

- `lemma Sumcheck.Spec.SingleRound.Simple.simulateQ_oracleVerify_eq` [ArkLib\ProofSystem\Sumcheck\Spec\SingleRound.lean:965](../../../ArkLib\ProofSystem\Sumcheck\Spec\SingleRound.lean#L965) — Closed form of the simulated oracle-verifier `verify`: the inner `simOracle2` simulation collapses t
- `theorem ToyProblem.Spec.simulateQ_oracleVerify_eq` [ArkLib\ProofSystem\ToyProblem\Spec\General.lean:788](../../../ArkLib\ProofSystem\ToyProblem\Spec\General.lean#L788) — **Closed form of the compiled toy-problem oracle verifier.** Simulating `oracleVerifier.verify` agai

### `simulateQ_simOracle2_query` (2 declarations, 2 files)

- `lemma RingSwitching.BatchingPhase.simulateQ_simOracle2_query` [ArkLib\ProofSystem\RingSwitching\BatchingPhase.lean:84](../../../ArkLib\ProofSystem\RingSwitching\BatchingPhase.lean#L84) — OptionT/query form of `simulateQ_simOracle2_messageQuery`.
- `lemma RingSwitching.simulateQ_simOracle2_query` [ArkLib\ProofSystem\RingSwitching\Prelude.lean:1498](../../../ArkLib\ProofSystem\RingSwitching\Prelude.lean#L1498) — **`simOracle2` message-query collapse (`OptionT`-`query` form).** The same reduction as `simulateQ_s

### `simulateQ_simOracle_foldlM` (2 declarations, 2 files)

- `theorem simulateQ_simOracle_foldlM` [ArkLib\OracleReduction\SimOracleFoldlM.lean:27](../../../ArkLib\OracleReduction\SimOracleFoldlM.lean#L27) — If every step of a `foldlM` simulates (under the honest single-family oracle) to a pure value, the w
- `lemma Spartan.Spec.simulateQ_simOracle_foldlM` [ArkLib\ProofSystem\Spartan\SecondSumcheckFaithful.lean:75](../../../ArkLib\ProofSystem\Spartan\SecondSumcheckFaithful.lean#L75) — Simulating a `foldlM` whose every step simulates to a pure value collapses to the `foldl` of the pur

### `singleton_bound` (2 declarations, 2 files)

- `theorem singleton_bound` [ArkLib\Data\CodingTheory\Basic\LinearCode.lean:121](../../../ArkLib\Data\CodingTheory\Basic\LinearCode.lean#L121) — **Singleton bound** for arbitrary codes
- `theorem ArkLib.CS25.singleton_bound` [ArkLib\Data\CodingTheory\SingletonBound.lean:30](../../../ArkLib\Data\CodingTheory\SingletonBound.lean#L30) — **Singleton bound.**  A code with minimum distance `≥ d` (`d ≥ 1`) has at most `q^(n−(d−1))` codewor

### `soundness.mono_error` (2 declarations, 2 files)

- `theorem Verifier.soundness.mono_error` [ArkLib\OracleReduction\Security\Basic.lean:315](../../../ArkLib\OracleReduction\Security\Basic.lean#L315) — Verifier soundness is monotone in the allowed soundness error.
- `theorem Verifier.StateRestoration.soundness.mono_error` [ArkLib\OracleReduction\Security\StateRestoration.lean:143](../../../ArkLib\OracleReduction\Security\StateRestoration.lean#L143) — State-restoration soundness is monotone in the allowed soundness error.

### `soundness.mono_languages` (2 declarations, 2 files)

- `theorem Verifier.soundness.mono_languages` [ArkLib\OracleReduction\Security\Basic.lean:331](../../../ArkLib\OracleReduction\Security\Basic.lean#L331) — Verifier soundness is monotone in the input and output languages. If soundness holds for a smaller h
- `theorem Verifier.StateRestoration.soundness.mono_languages` [ArkLib\OracleReduction\Security\StateRestoration.lean:157](../../../ArkLib\OracleReduction\Security\StateRestoration.lean#L157) — State-restoration soundness is monotone under enlarging the honest input language and shrinking the

### `sq_mem_half` (2 declarations, 2 files)

- `theorem ArkLib.ProximityGap.Round9SubgroupQuadraticHalving.sq_mem_half` [ArkLib\Data\CodingTheory\ProximityGap\SubgroupQuadraticHalving.lean:72](../../../ArkLib\Data\CodingTheory\ProximityGap\SubgroupQuadraticHalving.lean#L72) — **Squaring lands in the half-order subgroup.** If `x ∈ μ_{2m}` (so `x^{2m}=1`) then `x² ∈ μ_m`, beca
- `theorem ArkLib.ProximityGap.Round8SeamARecursion.sq_mem_half` [ArkLib\Data\CodingTheory\ProximityGap\SubgroupSquaresHalvingRecursion.lean:98](../../../ArkLib\Data\CodingTheory\ProximityGap\SubgroupSquaresHalvingRecursion.lean#L98) — **Squaring lands in the half-order subgroup.** If `x ∈ G = nthRootsFinset (2m) 1` (so `x^{2m}=1`), t

### `sq_sum_le_card_support_mul_sum_sq` (2 declarations, 2 files)

- `theorem Finset.sq_sum_le_card_support_mul_sum_sq` [ArkLib\ToMathlib\SqSumCardSupport.lean:20](../../../ArkLib\ToMathlib\SqSumCardSupport.lean#L20) — (no docstring)
- `theorem ArkLib.sq_sum_le_card_support_mul_sum_sq` [ArkLib\ToMathlib\SupportSqBound.lean:25](../../../ArkLib\ToMathlib\SupportSqBound.lean#L25) — **Cauchy-Schwarz support bound.** Over a finite type, `(∑ f)² ≤ \|support f\| · (∑ f²)`.

### `srcPSpec` (2 declarations, 2 files)

- `abbrev BCSTransparentEndToEnd.srcPSpec` [ArkLib\ProofSystem\BCS\TransparentEndToEnd.lean:67](../../../ArkLib\ProofSystem\BCS\TransparentEndToEnd.lean#L67) — The source interactive (oracle) protocol spec: a single prover message of type `Data`.
- `abbrev T.srcPSpec` [ArkLib\t3.lean:7](../../../ArkLib\t3.lean#L7) — (no docstring)

### `statisticalHVZK` (2 declarations, 2 files)

- `def OracleReduction.statisticalHVZK` [ArkLib\OracleReduction\Security\OracleZeroKnowledge.lean:53](../../../ArkLib\OracleReduction\Security\OracleZeroKnowledge.lean#L53) — Statistical HVZK for an oracle reduction, delegated through `OracleReduction.toReduction`.
- `def Reduction.statisticalHVZK` [ArkLib\OracleReduction\Security\ZeroKnowledge.lean:80](../../../ArkLib\OracleReduction\Security\ZeroKnowledge.lean#L80) — A reduction satisfies statistical honest-verifier zero-knowledge with error `ε` if the simulator's t

### `statisticalHVZK.congr_honestDist` (2 declarations, 2 files)

- `theorem OracleReduction.statisticalHVZK.congr_honestDist` [ArkLib\ToMathlib\OracleZKTransferBricks.lean:46](../../../ArkLib\ToMathlib\OracleZKTransferBricks.lean#L46) — **OracleReduction statistical HVZK transfers along an equal honest distribution.**
- `theorem Reduction.statisticalHVZK.congr_honestDist` [ArkLib\ToMathlib\ZKTransferBricks.lean:80](../../../ArkLib\ToMathlib\ZKTransferBricks.lean#L80) — **Statistical HVZK transfers along an `evalDist`-equal honest distribution.** The same simulator and

### `statisticalHVZK.congr_honestDist_symm` (2 declarations, 2 files)

- `theorem OracleReduction.statisticalHVZK.congr_honestDist_symm` [ArkLib\ToMathlib\OracleZKTransferBricks.lean:73](../../../ArkLib\ToMathlib\OracleZKTransferBricks.lean#L73) — **OracleReduction statistical HVZK honest-distribution congruence with opposite-order equality.**
- `theorem Reduction.statisticalHVZK.congr_honestDist_symm` [ArkLib\ToMathlib\ZKTransferBricks.lean:109](../../../ArkLib\ToMathlib\ZKTransferBricks.lean#L109) — **Statistical HVZK honest-distribution congruence with opposite-order equality.**

### `statisticalHVZK.isStatHVZK` (2 declarations, 2 files)

- `theorem OracleReduction.statisticalHVZK.isStatHVZK` [ArkLib\ToMathlib\OracleZKTransferBricks.lean:141](../../../ArkLib\ToMathlib\OracleZKTransferBricks.lean#L141) — **A concrete OracleReduction statistical-HVZK simulator witnesses existential statistical HVZK.**
- `theorem Reduction.statisticalHVZK.isStatHVZK` [ArkLib\ToMathlib\ZKTransferBricks.lean:184](../../../ArkLib\ToMathlib\ZKTransferBricks.lean#L184) — **A concrete statistical-HVZK simulator witnesses existential statistical HVZK.**

### `statisticalHVZK.isStatHVZK_of_simulator_congr` (2 declarations, 2 files)

- `theorem OracleReduction.statisticalHVZK.isStatHVZK_of_simulator_congr` [ArkLib\ToMathlib\OracleZKTransferBricks.lean:164](../../../ArkLib\ToMathlib\OracleZKTransferBricks.lean#L164) — **Package an OracleReduction statistical-HVZK proof after normalizing the simulator distribution.**
- `theorem Reduction.statisticalHVZK.isStatHVZK_of_simulator_congr` [ArkLib\ToMathlib\ZKTransferBricks.lean:205](../../../ArkLib\ToMathlib\ZKTransferBricks.lean#L205) — **Package a statistical-HVZK proof after normalizing the simulator distribution.**

### `statisticalHVZK.isStatHVZK_of_simulator_congr_symm` (2 declarations, 2 files)

- `theorem OracleReduction.statisticalHVZK.isStatHVZK_of_simulator_congr_symm` [ArkLib\ToMathlib\OracleZKTransferBricks.lean:188](../../../ArkLib\ToMathlib\OracleZKTransferBricks.lean#L188) — **Package an OracleReduction statistical-HVZK proof after simulator normalization in the opposite di
- `theorem Reduction.statisticalHVZK.isStatHVZK_of_simulator_congr_symm` [ArkLib\ToMathlib\ZKTransferBricks.lean:227](../../../ArkLib\ToMathlib\ZKTransferBricks.lean#L227) — **Package a statistical-HVZK proof after simulator normalization in the opposite direction.**

### `statisticalHVZK.mono_error` (2 declarations, 2 files)

- `theorem OracleReduction.statisticalHVZK.mono_error` [ArkLib\OracleReduction\Security\OracleZeroKnowledge.lean:140](../../../ArkLib\OracleReduction\Security\OracleZeroKnowledge.lean#L140) — Statistical HVZK for oracle reductions is monotone in the error bound.
- `theorem Reduction.statisticalHVZK.mono_error` [ArkLib\OracleReduction\Security\ZeroKnowledge.lean:188](../../../ArkLib\OracleReduction\Security\ZeroKnowledge.lean#L188) — **Statistical HVZK is monotone in the error.** A simulator within total-variation distance `ε₁` is a

### `statisticalHVZK.mono_relation` (2 declarations, 2 files)

- `theorem OracleReduction.statisticalHVZK.mono_relation` [ArkLib\OracleReduction\Security\OracleZeroKnowledge.lean:129](../../../ArkLib\OracleReduction\Security\OracleZeroKnowledge.lean#L129) — Statistical HVZK for oracle reductions is antitone in the relation.
- `theorem Reduction.statisticalHVZK.mono_relation` [ArkLib\OracleReduction\Security\ZeroKnowledge.lean:177](../../../ArkLib\OracleReduction\Security\ZeroKnowledge.lean#L177) — **Statistical HVZK is antitone in the relation.**

### `statisticalHVZK.mono_relation_error` (2 declarations, 2 files)

- `theorem OracleReduction.statisticalHVZK.mono_relation_error` [ArkLib\OracleReduction\Security\OracleZeroKnowledge.lean:211](../../../ArkLib\OracleReduction\Security\OracleZeroKnowledge.lean#L211) — Statistical HVZK for oracle reductions transports across both relation restriction and error relaxat
- `theorem Reduction.statisticalHVZK.mono_relation_error` [ArkLib\OracleReduction\Security\ZeroKnowledge.lean:250](../../../ArkLib\OracleReduction\Security\ZeroKnowledge.lean#L250) — **Statistical HVZK transports across both relation restriction and error relaxation.**

### `statisticalHVZK.simulator_congr` (2 declarations, 2 files)

- `theorem OracleReduction.statisticalHVZK.simulator_congr` [ArkLib\ToMathlib\OracleZKTransferBricks.lean:97](../../../ArkLib\ToMathlib\OracleZKTransferBricks.lean#L97) — **OracleReduction statistical HVZK is preserved under an equal simulator distribution.**
- `theorem Reduction.statisticalHVZK.simulator_congr` [ArkLib\ToMathlib\ZKTransferBricks.lean:138](../../../ArkLib\ToMathlib\ZKTransferBricks.lean#L138) — **Statistical HVZK is preserved under an `evalDist`-equal simulator.** Swapping in a simulator that

### `statisticalHVZK.simulator_congr_symm` (2 declarations, 2 files)

- `theorem OracleReduction.statisticalHVZK.simulator_congr_symm` [ArkLib\ToMathlib\OracleZKTransferBricks.lean:119](../../../ArkLib\ToMathlib\OracleZKTransferBricks.lean#L119) — **OracleReduction statistical HVZK simulator congruence with opposite-order equality.**
- `theorem Reduction.statisticalHVZK.simulator_congr_symm` [ArkLib\ToMathlib\ZKTransferBricks.lean:163](../../../ArkLib\ToMathlib\ZKTransferBricks.lean#L163) — **Statistical HVZK simulator congruence with opposite-order equality.**

### `statisticalHVZK.simulator_triangle` (2 declarations, 2 files)

- `theorem OracleReduction.statisticalHVZK.simulator_triangle` [ArkLib\ToMathlib\OracleZKTransferBricks.lean:199](../../../ArkLib\ToMathlib\OracleZKTransferBricks.lean#L199) — **Triangle composition of statistical HVZK at the OracleReduction API boundary.**
- `theorem Reduction.statisticalHVZK.simulator_triangle` [ArkLib\ToMathlib\ZKTransferBricks.lean:240](../../../ArkLib\ToMathlib\ZKTransferBricks.lean#L240) — **Triangle composition of statistical HVZK.** If `sim₁` is within `ε₁` of the honest distribution an

### `statisticalHVZK.triangle_honestDist` (2 declarations, 2 files)

- `theorem OracleReduction.statisticalHVZK.triangle_honestDist` [ArkLib\ToMathlib\OracleZKTransferBricks.lean:213](../../../ArkLib\ToMathlib\OracleZKTransferBricks.lean#L213) — **Approximate honest-distribution transfer at the OracleReduction API boundary.**
- `theorem Reduction.statisticalHVZK.triangle_honestDist` [ArkLib\ToMathlib\ZKTransferBricks.lean:265](../../../ArkLib\ToMathlib\ZKTransferBricks.lean#L265) — **Approximate honest-distribution transfer for statistical HVZK.** If a simulator is statistical-HVZ

### `statisticalHVZK.triangle_honestDist_symm` (2 declarations, 2 files)

- `theorem OracleReduction.statisticalHVZK.triangle_honestDist_symm` [ArkLib\ToMathlib\OracleZKTransferBricks.lean:227](../../../ArkLib\ToMathlib\OracleZKTransferBricks.lean#L227) — **Symmetric-facing approximate honest-distribution transfer at the OracleReduction API boundary.**
- `theorem Reduction.statisticalHVZK.triangle_honestDist_symm` [ArkLib\ToMathlib\ZKTransferBricks.lean:291](../../../ArkLib\ToMathlib\ZKTransferBricks.lean#L291) — **Symmetric-facing approximate honest-distribution transfer.** This is the same result as `statistic

### `statisticalHVZK.triangle_honestDist_symm_zero` (2 declarations, 2 files)

- `theorem OracleReduction.statisticalHVZK.triangle_honestDist_symm_zero` [ArkLib\ToMathlib\OracleZKTransferBricks.lean:255](../../../ArkLib\ToMathlib\OracleZKTransferBricks.lean#L255) — Symmetric-facing zero-error approximate honest-distribution transfer for statistical HVZK at the Ora
- `theorem Reduction.statisticalHVZK.triangle_honestDist_symm_zero` [ArkLib\ToMathlib\ZKTransferBricks.lean:324](../../../ArkLib\ToMathlib\ZKTransferBricks.lean#L324) — Symmetric-facing zero-error approximate honest-distribution transfer for statistical HVZK.

### `statisticalHVZK.triangle_honestDist_zero` (2 declarations, 2 files)

- `theorem OracleReduction.statisticalHVZK.triangle_honestDist_zero` [ArkLib\ToMathlib\OracleZKTransferBricks.lean:241](../../../ArkLib\ToMathlib\OracleZKTransferBricks.lean#L241) — **Zero-error approximate honest-distribution transfer for statistical HVZK at the OracleReduction AP
- `theorem Reduction.statisticalHVZK.triangle_honestDist_zero` [ArkLib\ToMathlib\ZKTransferBricks.lean:308](../../../ArkLib\ToMathlib\ZKTransferBricks.lean#L308) — **Zero-error approximate honest-distribution transfer for statistical HVZK.** If the honest transcri

### `statisticalHVZK_of_const_eq_honestDist` (2 declarations, 2 files)

- `theorem OracleReduction.statisticalHVZK_of_const_eq_honestDist` [ArkLib\ToMathlib\OracleZKTransferBricks.lean:334](../../../ArkLib\ToMathlib\OracleZKTransferBricks.lean#L334) — **Symmetric-facing OracleReduction constant-simulator criterion for statistical HVZK.**
- `theorem Reduction.statisticalHVZK_of_const_eq_honestDist` [ArkLib\ToMathlib\ZKTransferBricks.lean:419](../../../ArkLib\ToMathlib\ZKTransferBricks.lean#L419) — **Symmetric-facing constant-simulator criterion for statistical HVZK.**

### `statisticalHVZK_of_honestDist_eq_const` (2 declarations, 2 files)

- `theorem OracleReduction.statisticalHVZK_of_honestDist_eq_const` [ArkLib\ToMathlib\OracleZKTransferBricks.lean:308](../../../ArkLib\ToMathlib\OracleZKTransferBricks.lean#L308) — **OracleReduction constant-simulator criterion for statistical HVZK.**
- `theorem Reduction.statisticalHVZK_of_honestDist_eq_const` [ArkLib\ToMathlib\ZKTransferBricks.lean:394](../../../ArkLib\ToMathlib\ZKTransferBricks.lean#L394) — **Statistical constant-simulator criterion.** If the honest transcript distribution is `evalDist`-eq

### `statisticalHVZK_zero.perfectHVZK` (2 declarations, 2 files)

- `theorem OracleReduction.statisticalHVZK_zero.perfectHVZK` [ArkLib\OracleReduction\Security\OracleZeroKnowledge.lean:236](../../../ArkLib\OracleReduction\Security\OracleZeroKnowledge.lean#L236) — Zero-error statistical HVZK for oracle reductions converts back to perfect HVZK for the same simulat
- `theorem Reduction.statisticalHVZK_zero.perfectHVZK` [ArkLib\OracleReduction\Security\ZeroKnowledge.lean:272](../../../ArkLib\OracleReduction\Security\ZeroKnowledge.lean#L272) — **Zero-error statistical HVZK converts back to perfect HVZK for the same simulator.**

### `statisticalHVZK_zero.perfectHVZK_mono_relation` (2 declarations, 2 files)

- `theorem OracleReduction.statisticalHVZK_zero.perfectHVZK_mono_relation` [ArkLib\OracleReduction\Security\OracleZeroKnowledge.lean:248](../../../ArkLib\OracleReduction\Security\OracleZeroKnowledge.lean#L248) — Zero-error statistical HVZK for oracle reductions transports back to perfect HVZK on a subrelation.
- `theorem Reduction.statisticalHVZK_zero.perfectHVZK_mono_relation` [ArkLib\OracleReduction\Security\ZeroKnowledge.lean:283](../../../ArkLib\OracleReduction\Security\ZeroKnowledge.lean#L283) — **Zero-error statistical HVZK transports back to perfect HVZK on a subrelation.** The same simulator

### `subdomainZeroEquiv` (2 declarations, 2 files)

- `def Domain.CosetFftDomainClass.subdomainZeroEquiv` [ArkLib\Data\Domain\CosetFftDomain\Subdomain.lean:133](../../../ArkLib\Data\Domain\CosetFftDomain\Subdomain.lean#L133) — The zeroth subdomain has the same finite set of field points as the ambient domain.
- `def Fri.subdomainZeroEquiv` [ArkLib\ProofSystem\BatchedFri\Security.lean:1626](../../../ArkLib\ProofSystem\BatchedFri\Security.lean#L1626) — The round-zero Batched FRI subdomain is equivalent to the original evaluation domain.

### `subgroup_mixed_sum_is_partial` (2 declarations, 2 files)

- `theorem ArkLib.ProximityGap.Round8CompleteSquare.subgroup_mixed_sum_is_partial` [ArkLib\Data\CodingTheory\ProximityGap\MixedGaussSumCompleteSquare.lean:192](../../../ArkLib\Data\CodingTheory\ProximityGap\MixedGaussSumCompleteSquare.lean#L192) — **The subgroup mixed sum is a PARTIAL sum — the open delimiter.** The complete-the-square reduction
- `theorem ArkLib.ProximityGap.Round8MixedGauss.subgroup_mixed_sum_is_partial` [ArkLib\Data\CodingTheory\ProximityGap\MixedGaussSumDiagonal.lean:206](../../../ArkLib\Data\CodingTheory\ProximityGap\MixedGaussSumDiagonal.lean#L206) — **The subgroup mixed sum is a PARTIAL Gauss sum — the open delimiter.** The collision count `M2` ove

### `sum_div_mul_prod_eq_sum_mul_prod_erase` (2 declarations, 2 files)

- `theorem Logup.sum_div_mul_prod_eq_sum_mul_prod_erase` [ArkLib\ProofSystem\Logup\Common.lean:755](../../../ArkLib\ProofSystem\Logup\Common.lean#L755) — (no docstring)
- `theorem Finset.sum_div_mul_prod_eq_sum_mul_prod_erase` [ArkLib\ToMathlib\ProtocolCountingBricks.lean:30](../../../ArkLib\ToMathlib\ProtocolCountingBricks.lean#L30) — **LogUp clear-denominators core.** `(∑ num/den)·(∏ den) = ∑ num·∏_{erase} den`.

### `sumcheckConsistencyProp` (2 declarations, 2 files)

- `def Binius.BinaryBasefold.sumcheckConsistencyProp` [ArkLib\ProofSystem\Binius\BinaryBasefold\Basic.lean:1162](../../../ArkLib\ProofSystem\Binius\BinaryBasefold\Basic.lean#L1162) — Sumcheck consistency: the claimed sumcheck target equals the sum of `H` over the boolean hypercube o
- `def Sumcheck.Structured.sumcheckConsistencyProp` [ArkLib\ProofSystem\Sumcheck\Structured.lean:212](../../../ArkLib\ProofSystem\Sumcheck\Structured.lean#L212) — Sumcheck consistency: the claimed sum equals the actual polynomial evaluation sum over the evaluatio

### `sumcheckFoldOracleReduction` (2 declarations, 2 files)

- `def sumcheckFoldOracleReduction` [ArkLib\ProofSystem\Binius\BinaryBasefold\CoreInteractionPhase.lean:813](../../../ArkLib\ProofSystem\Binius\BinaryBasefold\CoreInteractionPhase.lean#L813) — (no docstring)
- `def Binius.FRIBinius.CoreInteractionPhase.sumcheckFoldOracleReduction` [ArkLib\ProofSystem\Binius\FRIBinius\CoreInteractionPhase.lean:154](../../../ArkLib\ProofSystem\Binius\FRIBinius\CoreInteractionPhase.lean#L154) — (no docstring)

### `sumcheckFoldOracleReduction_perfectCompleteness` (2 declarations, 2 files)

- `theorem sumcheckFoldOracleReduction_perfectCompleteness` [ArkLib\ProofSystem\Binius\BinaryBasefold\CoreInteractionPhase.lean:918](../../../ArkLib\ProofSystem\Binius\BinaryBasefold\CoreInteractionPhase.lean#L918) — (no docstring)
- `theorem Binius.FRIBinius.CoreInteractionPhase.sumcheckFoldOracleReduction_perfectCompleteness` [ArkLib\ProofSystem\Binius\FRIBinius\CoreInteractionPhase.lean:252](../../../ArkLib\ProofSystem\Binius\FRIBinius\CoreInteractionPhase.lean#L252) — (no docstring)

### `sumcheckFoldOracleVerifier` (2 declarations, 2 files)

- `def sumcheckFoldOracleVerifier` [ArkLib\ProofSystem\Binius\BinaryBasefold\CoreInteractionPhase.lean:529](../../../ArkLib\ProofSystem\Binius\BinaryBasefold\CoreInteractionPhase.lean#L529) — (no docstring)
- `def Binius.FRIBinius.CoreInteractionPhase.sumcheckFoldOracleVerifier` [ArkLib\ProofSystem\Binius\FRIBinius\CoreInteractionPhase.lean:147](../../../ArkLib\ProofSystem\Binius\FRIBinius\CoreInteractionPhase.lean#L147) — (no docstring)

### `sumcheckFoldOracleVerifier_rbrKnowledgeSoundness` (2 declarations, 2 files)

- `theorem sumcheckFoldOracleVerifier_rbrKnowledgeSoundness` [ArkLib\ProofSystem\Binius\BinaryBasefold\CoreInteractionPhase.lean:1072](../../../ArkLib\ProofSystem\Binius\BinaryBasefold\CoreInteractionPhase.lean#L1072) — (no docstring)
- `theorem Binius.FRIBinius.CoreInteractionPhase.sumcheckFoldOracleVerifier_rbrKnowledgeSoundness` [ArkLib\ProofSystem\Binius\FRIBinius\CoreInteractionPhase.lean:442](../../../ArkLib\ProofSystem\Binius\FRIBinius\CoreInteractionPhase.lean#L442) — (no docstring)

### `support_mk` (2 declarations, 2 files)

- `lemma ReduceClaim.support_mk` [ArkLib\ProofSystem\Component\ReduceClaim.lean:181](../../../ArkLib\ProofSystem\Component\ReduceClaim.lean#L181) — (no docstring)
- `lemma OptionT.support_mk` [ArkLib\ToVCVio\Lemmas.lean:106](../../../ArkLib\ToVCVio\Lemmas.lean#L106) — (no docstring)

### `synd` (2 declarations, 2 files)

- `def C2CoreBound.synd` [ArkLib\Data\CodingTheory\ProximityGap\C2CoreEliminationBound.lean:59](../../../ArkLib\Data\CodingTheory\ProximityGap\C2CoreEliminationBound.lean#L59) — The coefficient-window syndrome pairing: `⟨P, s⟩ = ∑_{j < N} P_j · s_j`.
- `def TopLine.synd` [ArkLib\Data\CodingTheory\ProximityGap\TopDirectionLineCount.lean:52](../../../ArkLib\Data\CodingTheory\ProximityGap\TopDirectionLineCount.lean#L52) — The coefficient-window syndrome pairing `⟨P, s⟩ = ∑_{j<N} P_j s_j`.

### `syndr` (2 declarations, 2 files)

- `def C2CoreBound.syndr` [ArkLib\Data\CodingTheory\ProximityGap\C2CoreEliminationBound.lean:65](../../../ArkLib\Data\CodingTheory\ProximityGap\C2CoreEliminationBound.lean#L65) — The `r`-shifted syndrome functional of a support.
- `def TopLine.syndr` [ArkLib\Data\CodingTheory\ProximityGap\TopDirectionLineCount.lean:58](../../../ArkLib\Data\CodingTheory\ProximityGap\TopDirectionLineCount.lean#L58) — The `r`-shifted syndrome functional.

### `toMLE_evalC_eq_sum` (2 declarations, 2 files)

- `theorem Spartan.Spec.toMLE_evalC_eq_sum` [ArkLib\ProofSystem\Spartan\SecondSumcheckReduction.lean:50](../../../ArkLib\ProofSystem\Spartan\SecondSumcheckReduction.lean#L50) — (no docstring)
- `theorem Spartan.toMLE_evalC_eq_sum` [ArkLib\ProofSystem\Spartan\SumcheckDegreeBound.lean:41](../../../ArkLib\ProofSystem\Spartan\SumcheckDegreeBound.lean#L41) — **Polynomial-level partial evaluation of `Matrix.toMLE`.** Fixing the row variables at `r_x` yields

### `toMLE_evalC_mem_restrictDegree` (2 declarations, 2 files)

- `theorem Spartan.Spec.toMLE_evalC_mem_restrictDegree` [ArkLib\ProofSystem\Spartan\SecondSumcheckReduction.lean:62](../../../ArkLib\ProofSystem\Spartan\SecondSumcheckReduction.lean#L62) — (no docstring)
- `theorem Spartan.toMLE_evalC_mem_restrictDegree` [ArkLib\ProofSystem\Spartan\SumcheckDegreeBound.lean:54](../../../ArkLib\ProofSystem\Spartan\SumcheckDegreeBound.lean#L54) — **The row-fixed matrix MLE is multilinear in the column variables (degree ≤ 1).**

### `toMonadDecoration` (2 declarations, 2 files)

- `def Interaction.OracleDecoration.toMonadDecoration` [ArkLib\Interaction\Oracle\Core.lean:802](../../../ArkLib\Interaction\Oracle\Core.lean#L802) — (no docstring)
- `def Interaction.Oracle.Spec.toMonadDecoration` [ArkLib\Interaction\Oracle\Spec.lean:193](../../../ArkLib\Interaction\Oracle\Spec.lean#L193) — (no docstring)

### `toOracleSpec` (2 declarations, 2 files)

- `def Interaction.Oracle.Spec.toOracleSpec` [ArkLib\Interaction\Oracle\Spec.lean:158](../../../ArkLib\Interaction\Oracle\Spec.lean#L158) — (no docstring)
- `def OracleInterface.toOracleSpec` [ArkLib\OracleReduction\OracleInterface.lean:92](../../../ArkLib\OracleReduction\OracleInterface.lean#L92) — Converts an indexed type family of oracle interfaces into an oracle specification. Notation: `[v]ₒ`

### `toPoly` (2 declarations, 2 files)

- `def GSMultInterp.toPoly` [ArkLib\Data\CodingTheory\GuruswamiSudan\DictionaryBridge.lean:26](../../../ArkLib\Data\CodingTheory\GuruswamiSudan\DictionaryBridge.lean#L26) — The bivariate polynomial `∑_{(s,t)∈monoIdx} c(s,t)·X^s·Y^t` carried by a coefficient vector `c`, as
- `def UniPoly.toPoly` [ArkLib\Data\UniPoly\Basic.lean:758](../../../ArkLib\Data\UniPoly\Basic.lean#L758) — Convert a `UniPoly` to a (mathlib) `Polynomial`.

### `toPoly_add` (2 declarations, 2 files)

- `theorem GSMultInterp.toPoly_add` [ArkLib\Data\CodingTheory\GuruswamiSudan\DictionaryBridge.lean:48](../../../ArkLib\Data\CodingTheory\GuruswamiSudan\DictionaryBridge.lean#L48) — `toPoly` is additive in the coefficient vector.
- `theorem UniPoly.toPoly_add` [ArkLib\Data\UniPoly\Basic.lean:854](../../../ArkLib\Data\UniPoly\Basic.lean#L854) — `UniPoly` addition is mapped to `Polynomial` addition

### `totient_two_pow` (2 declarations, 2 files)

- `theorem ArkLib.ProximityGap.SubsetSumLowerLoop50.totient_two_pow` [ArkLib\Data\CodingTheory\ProximityGap\CandidateSubsetSumLowerLoop50.lean:183](../../../ArkLib\Data\CodingTheory\ProximityGap\CandidateSubsetSumLowerLoop50.lean#L183) — `φ(2^m) = 2^{m-1}` for `m ≥ 1`.
- `theorem R12.totient_two_pow` [ArkLib\Data\CodingTheory\ProximityGap\LamLeungUnconditionalGeneral.lean:140](../../../ArkLib\Data\CodingTheory\ProximityGap\LamLeungUnconditionalGeneral.lean#L140) — `φ(2^m) = 2^{m-1}` for `m ≥ 1`.

### `two_ne_zero_zmod13` (2 declarations, 2 files)

- `theorem ArkLib.CodingTheory.Round6MultCharacter.two_ne_zero_zmod13` [ArkLib\Data\CodingTheory\ProximityGap\SubsetSumE2PowerSumReduction.lean:339](../../../ArkLib\Data\CodingTheory\ProximityGap\SubsetSumE2PowerSumReduction.lean#L339) — **`(2 : F) ≠ 0` is realized in the smooth-domain regime (concrete witness `F = ZMod 13`).** The smoo
- `theorem ArkLib.CodingTheory.Round7PaleyZygmund.two_ne_zero_zmod13` [ArkLib\Data\CodingTheory\ProximityGap\SubsetSumPaleyZygmundDichotomy.lean:384](../../../ArkLib\Data\CodingTheory\ProximityGap\SubsetSumPaleyZygmundDichotomy.lean#L384) — **`(2 : ZMod 13) ≠ 0` — the smooth-domain regime is realized.** The smooth `2^k`-subgroup lives in o

### `ubad` (2 declarations, 2 files)

- `def CodingTheory.LineDecodingRefutation.ubad` [ArkLib\Data\CodingTheory\ProximityGap\LineDecodingRefutation.lean:113](../../../ArkLib\Data\CodingTheory\ProximityGap\LineDecodingRefutation.lean#L113) — The refuting stack: `u 0 = 0`, `u 1 = 1` (the all-ones word of `Fin 1 → ZMod 2`).
- `def ProximityGap.MCAZeroCode.ubad` [ArkLib\Data\CodingTheory\ProximityGap\MCAZeroCodeExact.lean:57](../../../ArkLib\Data\CodingTheory\ProximityGap\MCAZeroCodeExact.lean#L57) — The refuting/witness stack: `u 0 = 0`, `u 1 = 𝟙` (the all-ones word `ι → F`).

### `ubad_one` (2 declarations, 2 files)

- `theorem CodingTheory.LineDecodingRefutation.ubad_one` [ArkLib\Data\CodingTheory\ProximityGap\LineDecodingRefutation.lean:118](../../../ArkLib\Data\CodingTheory\ProximityGap\LineDecodingRefutation.lean#L118) — (no docstring)
- `theorem ProximityGap.MCAZeroCode.ubad_one` [ArkLib\Data\CodingTheory\ProximityGap\MCAZeroCodeExact.lean:61](../../../ArkLib\Data\CodingTheory\ProximityGap\MCAZeroCodeExact.lean#L61) — (no docstring)

### `ubad_zero` (2 declarations, 2 files)

- `theorem CodingTheory.LineDecodingRefutation.ubad_zero` [ArkLib\Data\CodingTheory\ProximityGap\LineDecodingRefutation.lean:115](../../../ArkLib\Data\CodingTheory\ProximityGap\LineDecodingRefutation.lean#L115) — (no docstring)
- `theorem ProximityGap.MCAZeroCode.ubad_zero` [ArkLib\Data\CodingTheory\ProximityGap\MCAZeroCodeExact.lean:59](../../../ArkLib\Data\CodingTheory\ProximityGap\MCAZeroCodeExact.lean#L59) — (no docstring)

### `umCode` (2 declarations, 2 files)

- `def ReedSolomon.Multiplicity.umCode` [ArkLib\Data\CodingTheory\ReedSolomon\Multiplicity.lean:97](../../../ArkLib\Data\CodingTheory\ReedSolomon\Multiplicity.lean#L97) — **ABF26 Definition A.7 [GW13, KSY14]** — the univariate multiplicity code `UM[F, L, k, s]`. Defined
- `def CodingTheory.umCode` [ArkLib\Data\CodingTheory\SubspaceDesign.lean:1105](../../../ArkLib\Data\CodingTheory\SubspaceDesign.lean#L1105) — **ABF26 DA.7 (Univariate Multiplicity codes)**. The UM code `UM[F, L, k, s]`: `UM[F, L, k, s] := { f

### `uniform` (2 declarations, 2 files)

- `def OracleReduction.OracleDistribution.uniform` [ArkLib\OracleReduction\Security\OracleDistribution.lean:119](../../../ArkLib\OracleReduction\Security\OracleDistribution.lean#L119) — Uniform full-table sampling. Requires `SampleableType` over the dependent product `OracleFamily spec
- `def SumcheckDomain.uniform` [ArkLib\ProofSystem\Sumcheck\Domain.lean:74](../../../ArkLib\ProofSystem\Sumcheck\Domain.lean#L74) — The *uniform* domain: the same `m`-point embedding `D₀` in every one of the `k` coordinates. Its `cu

### `unroll_2_message_VP` (2 declarations, 2 files)

- `theorem StirIOP.Round.unroll_2_message_VP` [ArkLib\ProofSystem\Stir\RoundCompleteness.lean:55](../../../ArkLib\ProofSystem\Stir\RoundCompleteness.lean#L55) — (no docstring)
- `theorem WhirIOP.FoldRound.unroll_2_message_VP` [ArkLib\ProofSystem\Whir\FoldRound.lean:65](../../../ArkLib\ProofSystem\Whir\FoldRound.lean#L65) — (no docstring)

### `urow0` (2 declarations, 2 files)

- `def ProximityGap.MCANearCapacityGK.urow0` [ArkLib\Data\CodingTheory\ProximityGap\MCANearCapacityGeneralRate.lean:121](../../../ArkLib\Data\CodingTheory\ProximityGap\MCANearCapacityGeneralRate.lean#L121) — First row `u₀ i = (domain i)ᵏ⁺¹`.
- `def ProximityGap.MCANearCapacity.urow0` [ArkLib\Data\CodingTheory\ProximityGap\MCANearCapacityLowerBound.lean:62](../../../ArkLib\Data\CodingTheory\ProximityGap\MCANearCapacityLowerBound.lean#L62) — First row `u₀ i = i²`.

### `urow1` (2 declarations, 2 files)

- `def ProximityGap.MCANearCapacityGK.urow1` [ArkLib\Data\CodingTheory\ProximityGap\MCANearCapacityGeneralRate.lean:123](../../../ArkLib\Data\CodingTheory\ProximityGap\MCANearCapacityGeneralRate.lean#L123) — Second row `u₁ i = (domain i)ᵏ`.
- `def ProximityGap.MCANearCapacity.urow1` [ArkLib\Data\CodingTheory\ProximityGap\MCANearCapacityLowerBound.lean:64](../../../ArkLib\Data\CodingTheory\ProximityGap\MCANearCapacityLowerBound.lean#L64) — Second row `u₁ i = i`.

### `vanishesToOrder` (2 declarations, 2 files)

- `def GSMultInterp.vanishesToOrder` [ArkLib\Data\CodingTheory\GuruswamiSudan\MultiplicityInterpolation.lean:153](../../../ArkLib\Data\CodingTheory\GuruswamiSudan\MultiplicityInterpolation.lean#L153) — `Q` (given by coefficient vector `c`) **vanishes to order `m`** at `(x₀, y₀)`: every Hasse coefficie
- `def ArkLib.GS.vanishesToOrder` [ArkLib\Data\CodingTheory\ProximityGap\BivariateVanishing.lean:60](../../../ArkLib\Data\CodingTheory\ProximityGap\BivariateVanishing.lean#L60) — `Q : F[X][Y]` **vanishes to order `m` at `(a, b)`** when, for every `Y`-index `j`, the inner Taylor

### `vecL2NormSq` (2 declarations, 2 files)

- `def ArkLib.Lattices.CyclotomicModulus.vecL2NormSq` [ArkLib\Data\Lattices\CyclotomicRing\NormBounds\Basic.lean:91](../../../ArkLib\Data\Lattices\CyclotomicRing\NormBounds\Basic.lean#L91) — Centered squared-`ℓ₂` norm of a vector: the sum of entrywise norms.
- `def ArkLib.Lattices.CenteredCoeffView.vecL2NormSq` [ArkLib\Data\Lattices\CyclotomicRing\Norms.lean:80](../../../ArkLib\Data\Lattices\CyclotomicRing\Norms.lean#L80) — Vector squared `ℓ₂` norm: the sum of entrywise squared `ℓ₂` norms.

### `verifier_rbrKnowledgeSoundness` (2 declarations, 2 files)

- `theorem DoNothing.verifier_rbrKnowledgeSoundness` [ArkLib\ProofSystem\Component\DoNothing.lean:58](../../../ArkLib\ProofSystem\Component\DoNothing.lean#L58) — The `DoNothing` verifier is perfectly round-by-round knowledge sound.
- `theorem ReduceClaim.verifier_rbrKnowledgeSoundness` [ArkLib\ProofSystem\Component\ReduceClaim.lean:225](../../../ArkLib\ProofSystem\Component\ReduceClaim.lean#L225) — The `ReduceClaim` oracle reduction satisfies perfect round-by-round knowledge soundness. Note that s

### `verifyOpening` (2 declarations, 2 files)

- `def KZG.verifyOpening` [ArkLib\CommitmentScheme\KZG\Basic.lean:69](../../../ArkLib\CommitmentScheme\KZG\Basic.lean#L69) — To verify a KZG opening `opening` for a commitment `commitment` at point `z` with claimed evaluation
- `def InductiveMerkleTree.verifyOpening` [ArkLib\CommitmentScheme\MerkleTree\Batch.lean:101](../../../ArkLib\CommitmentScheme\MerkleTree\Batch.lean#L101) — Verify one packaged opening against a claimed root, in `OracleComp (spec α)`.

### `weight_Λ_over_𝒪_add_le` (2 declarations, 2 files)

- `lemma BCIKS20.HenselNumerator.weight_Λ_over_𝒪_add_le` [ArkLib\Data\CodingTheory\ProximityGap\BCIKS20\HenselNumerator.lean:650](../../../ArkLib\Data\CodingTheory\ProximityGap\BCIKS20\HenselNumerator.lean#L650) — `Λ_𝒪(a + b) ≤ max(Λ_𝒪 a, Λ_𝒪 b)`: sub-additivity over `𝒪 H`.
- `lemma ArkLib.weight_Λ_over_𝒪_add_le` [ArkLib\ToMathlib\WeightLambdaCalculus.lean:82](../../../ArkLib\ToMathlib\WeightLambdaCalculus.lean#L82) — Sub-additivity of the `𝒪`-weight under addition: `Λ(a + b) ≤ max (Λ a) (Λ b)`.

### `weight_Λ_over_𝒪_mul_le` (2 declarations, 2 files)

- `lemma BCIKS20.HenselNumerator.weight_Λ_over_𝒪_mul_le` [ArkLib\Data\CodingTheory\ProximityGap\BCIKS20\HenselNumerator.lean:635](../../../ArkLib\Data\CodingTheory\ProximityGap\BCIKS20\HenselNumerator.lean#L635) — `Λ_𝒪(a · b) ≤ Λ_𝒪(a) + Λ_𝒪(b)`: sub-multiplicativity over `𝒪 H`.  Take the canonical representatives
- `lemma ArkLib.weight_Λ_over_𝒪_mul_le` [ArkLib\ToMathlib\WeightLambdaCalculus.lean:143](../../../ArkLib\ToMathlib\WeightLambdaCalculus.lean#L143) — Sub-multiplicativity of the `𝒪`-weight: `Λ(a · b) ≤ Λ a + Λ b`. This is the central inequality the A

### `weight_Λ_over_𝒪_neg` (2 declarations, 2 files)

- `lemma BCIKS20.HenselNumerator.weight_Λ_over_𝒪_neg` [ArkLib\Data\CodingTheory\ProximityGap\BCIKS20\HenselNumerator.lean:665](../../../ArkLib\Data\CodingTheory\ProximityGap\BCIKS20\HenselNumerator.lean#L665) — `Λ_𝒪(-a) = Λ_𝒪(a)`: the `𝒪`-weight is negation-invariant (`mk (-ra) = -a`, `weight_Λ_neg`).
- `lemma ArkLib.weight_Λ_over_𝒪_neg` [ArkLib\ToMathlib\WeightLambdaCalculus.lean:99](../../../ArkLib\ToMathlib\WeightLambdaCalculus.lean#L99) — Sub-additivity of the `𝒪`-weight under negation: it is invariant.

### `weight_Λ_over_𝒪_pow_le` (2 declarations, 2 files)

- `lemma BCIKS20.HenselNumerator.weight_Λ_over_𝒪_pow_le` [ArkLib\Data\CodingTheory\ProximityGap\BCIKS20\HenselNumerator.lean:691](../../../ArkLib\Data\CodingTheory\ProximityGap\BCIKS20\HenselNumerator.lean#L691) — `Λ_𝒪(a ^ k) ≤ k • Λ_𝒪(a)` (i.e. `≤ k · Λ_𝒪(a)` in `WithBot ℕ`): the power bound over `𝒪 H`, by induc
- `lemma ArkLib.weight_Λ_over_𝒪_pow_le` [ArkLib\ToMathlib\WeightLambdaCalculus.lean:158](../../../ArkLib\ToMathlib\WeightLambdaCalculus.lean#L158) — Sub-multiplicativity for powers: `Λ(a ^ n) ≤ n • Λ a` (with `0 • Λ a = 0`, matching `weight_Λ_over_𝒪

### `weight_Λ_over_𝒪_sum_le` (2 declarations, 2 files)

- `lemma BCIKS20.HenselNumerator.weight_Λ_over_𝒪_sum_le` [ArkLib\Data\CodingTheory\ProximityGap\BCIKS20\HenselNumerator.lean:677](../../../ArkLib\Data\CodingTheory\ProximityGap\BCIKS20\HenselNumerator.lean#L677) — `Λ_𝒪(∑ᵢ f i) ≤ sup of Λ_𝒪(f i)`: the `𝒪`-weight of a finite sum is bounded by the sup of the summand
- `lemma ArkLib.weight_Λ_over_𝒪_sum_le` [ArkLib\ToMathlib\WeightLambdaCalculus.lean:124](../../../ArkLib\ToMathlib\WeightLambdaCalculus.lean#L124) — The `𝒪`-weight of a finite sum is bounded by the `sup` of the summands' weights.

### `witnessStructuralInvariant` (2 declarations, 2 files)

- `def Binius.BinaryBasefold.witnessStructuralInvariant` [ArkLib\ProofSystem\Binius\BinaryBasefold\Basic.lean:1154](../../../ArkLib\ProofSystem\Binius\BinaryBasefold\Basic.lean#L1154) — This condition ensures that the witness polynomial `H` has the correct structure `eq(...) * t(...)`
- `def RingSwitching.witnessStructuralInvariant` [ArkLib\ProofSystem\RingSwitching\Prelude.lean:452](../../../ArkLib\ProofSystem\RingSwitching\Prelude.lean#L452) — This condition ensures that the witness polynomial `H` has the correct structure `A(...) * t'(...)`

### `witness_list_card_seven` (2 declarations, 2 files)

- `theorem ArkLib.CodingTheory.TinyInteriorK3.witness_list_card_seven` [ArkLib\Data\CodingTheory\ProximityGap\ListInteriorPinF11K3.lean:168](../../../ArkLib\Data\CodingTheory\ProximityGap\ListInteriorPinF11K3.lean#L168) — **The list has exactly seven elements.** All seven explicit codewords are pairwise distinct.
- `theorem ArkLib.CodingTheory.Round3SmoothF17.witness_list_card_seven` [ArkLib\Data\CodingTheory\ProximityGap\ListInteriorPinF17Subgroup.lean:177](../../../ArkLib\Data\CodingTheory\ProximityGap\ListInteriorPinF17Subgroup.lean#L177) — **The list has exactly seven elements.** All seven explicit smooth-domain codewords are pairwise dis

### `BCSCompilerFrontierReady.security` (2 declarations, 2 files)

- `theorem OracleReduction.BCSCompilerFrontierReady.security` [ArkLib\OracleReduction\BCS\Basic.lean:1493](../../../ArkLib\OracleReduction\BCS\Basic.lean#L1493) — Project the security-preservation obligations from a ready BCS compiler frontier.
- `theorem OracleReduction.BCSCompilerFrontierReady.security` [ArkLib\OracleReduction\BCS\FrontierBricks.lean:80](../../../ArkLib\OracleReduction\BCS\FrontierBricks.lean#L80) — **Project the five security targets** from a ready BCS compiler frontier. The security counterpart o

### `B_eq` (2 declarations, 2 files)

- `theorem CodingTheory.ABF26C38.B_eq` [ArkLib\Data\CodingTheory\ListDecoding\Bounds.lean:702](../../../ArkLib\Data\CodingTheory\ListDecoding\Bounds.lean#L702) — (no docstring)
- `theorem CodingTheory.ABF26C38.B_eq` [ArkLib\Data\CodingTheory\ListDecoding\Bounds\General.lean:573](../../../ArkLib\Data\CodingTheory\ListDecoding\Bounds\General.lean#L573) — (no docstring)

### `H_matrix` (2 declarations, 2 files)

- `def H_matrix` [ArkLib\Data\CodingTheory\ProximityGap\PromotedHypothesesB.lean:23](../../../ArkLib\Data\CodingTheory\ProximityGap\PromotedHypothesesB.lean#L23) — (no docstring)
- `def H_matrix` [ArkLib\Data\CodingTheory\Quarantine\CandidateHypothesesRefutations.lean:22](../../../ArkLib\Data\CodingTheory\Quarantine\CandidateHypothesesRefutations.lean#L22) — (no docstring)

### `OracleInterface` (3 declarations, 2 files)

- `structure OracleInterface` [ArkLib\OracleReduction\Basic.lean:88](../../../ArkLib\OracleReduction\Basic.lean#L88) — (no docstring)
- `structure OracleInterface` [ArkLib\OracleReduction\Basic.lean:162](../../../ArkLib\OracleReduction\Basic.lean#L162) — (no docstring)
- `class OracleInterface` [ArkLib\OracleReduction\OracleInterface.lean:52](../../../ArkLib\OracleReduction\OracleInterface.lean#L52) — `OracleInterface` is a type class that provides an oracle interface for a type `Message`. It consist

### `RestrictedFaaDiBrunoPartitionMatchAt.zero_of_unclearedHasseCoeff_div_W_natDegree` (2 declarations, 2 files)

- `theorem BCIKS20.HenselNumerator.RestrictedFaaDiBrunoPartitionMatchAt.zero_of_unclearedHasseCoeff_div_W_natDegree` [ArkLib\Data\CodingTheory\ProximityGap\BCIKS20\P2Reabsorb.lean:442](../../../ArkLib\Data\CodingTheory\ProximityGap\BCIKS20\P2Reabsorb.lean#L442) — The un-cleared-over-`W ^ R.natDegree` target builds the normalized partition order-zero match under
- `theorem BCIKS20.HenselNumerator.RestrictedFaaDiBrunoPartitionMatchAt.zero_of_unclearedHasseCoeff_div_W_natDegree` [ArkLib\Data\CodingTheory\ProximityGap\BCIKS20\RestrictedFaaDiBrunoExtract.lean:301](../../../ArkLib\Data\CodingTheory\ProximityGap\BCIKS20\RestrictedFaaDiBrunoExtract.lean#L301) — **Build the normalized partition order-zero residual from the uncleared-Hasse/`W^natDegree` equation

### `alpha12_injective` (2 declarations, 2 files)

- `lemma R15.alpha12_injective` [ArkLib\Data\CodingTheory\ProximityGap\SudanListBound.lean:388](../../../ArkLib\Data\CodingTheory\ProximityGap\SudanListBound.lean#L388) — Injectivity of the evaluation points `0, 1, …, 11` in `ZMod 13`.
- `lemma R15.alpha12_injective` [ArkLib\Data\CodingTheory\ProximityGap\SudanListBoundFull.lean:388](../../../ArkLib\Data\CodingTheory\ProximityGap\SudanListBoundFull.lean#L388) — Injectivity of the evaluation points `0, 1, …, 11` in `ZMod 13`.

### `appendStage₁_run_eq_liftM` (2 declarations, 2 files)

- `theorem Reduction.appendStage₁_run_eq_liftM` [ArkLib\OracleReduction\Composition\Sequential\AppendSeamBridges.lean:175](../../../ArkLib\OracleReduction\Composition\Sequential\AppendSeamBridges.lean#L175) — **The `OptionT.run` of the phase-1 stage body equals `liftM` of `R₁.run`'s `OptionT.run`.** `appendS
- `theorem Reduction.appendStage₁_run_eq_liftM` [ArkLib\OracleReduction\Composition\Sequential\AppendSeamBridges2.lean:143](../../../ArkLib\OracleReduction\Composition\Sequential\AppendSeamBridges2.lean#L143) — **The `OptionT.run` of the phase-1 stage body equals `liftM` of `R₁.run`'s `OptionT.run`.** `appendS

### `audit` (2 declarations, 2 files)

- `axiom audit` [ArkLib\ProofSystem\Logup\Security\LogupCompletenessUncond.lean:75](../../../ArkLib\ProofSystem\Logup\Security\LogupCompletenessUncond.lean#L75) — (no docstring)
- `axiom audit` [ArkLib\ProofSystem\Logup\Security\LogupSoundnessUncond.lean:84](../../../ArkLib\ProofSystem\Logup\Security\LogupSoundnessUncond.lean#L84) — (no docstring)

### `choose_pow_le_qEntropy` (2 declarations, 2 files)

- `theorem CodingTheory.choose_pow_le_qEntropy` [ArkLib\Data\CodingTheory\EntropyVolumeUpper.lean:55](../../../ArkLib\Data\CodingTheory\EntropyVolumeUpper.lean#L55) — **Single-term q-ary entropy UPPER bound.**  For `2 ≤ q`, `0 < k`, `k < n`: `C(n,k) · (q-1)^k ≤ q^{n·
- `theorem CodingTheory.choose_pow_le_qEntropy` [ArkLib\Data\CodingTheory\EntropyVolumeUpperBound.lean:53](../../../ArkLib\Data\CodingTheory\EntropyVolumeUpperBound.lean#L53) — **Per-term `q`-ary entropy upper bound.** For `2 ≤ q`, `0 < k`, `k < n`, `C(n,k) · (q-1)^k ≤ q^{n ·

### `choose_real` (2 declarations, 2 files)

- `theorem CodingTheory.ABF26C38.choose_real` [ArkLib\Data\CodingTheory\ListDecoding\Bounds.lean:639](../../../ArkLib\Data\CodingTheory\ListDecoding\Bounds.lean#L639) — (no docstring)
- `theorem CodingTheory.ABF26C38.choose_real` [ArkLib\Data\CodingTheory\ListDecoding\Bounds\General.lean:510](../../../ArkLib\Data\CodingTheory\ListDecoding\Bounds\General.lean#L510) — (no docstring)

### `coeff_ehQ_eq_leading` (2 declarations, 2 files)

- `lemma MvPolynomial.coeff_ehQ_eq_leading` [ArkLib\ToMathlib\RestrictedSumset.lean:223](../../../ArkLib\ToMathlib\RestrictedSumset.lean#L223) — The coefficient of the top monomial `X₀^{n-1} X₁^{n-2}` in `ehQ C'` (with `\|C'\| = 2(n-2)`) equals it
- `lemma MvPolynomial.coeff_ehQ_eq_leading` [ArkLib\ToMathlib\RestrictedSumsetGeneral.lean:278](../../../ArkLib\ToMathlib\RestrictedSumsetGeneral.lean#L278) — `ehQ h Cset` differs from the leading part `vdmX h · y^{\|Cset\|}` by a polynomial of strictly smaller

### `coeff_zero_of_natDegree_lt` (2 declarations, 2 files)

- `lemma ProximityGap.coeff_zero_of_natDegree_lt` [ArkLib\Data\CodingTheory\ProximityGap\BCIKS20\Curves.lean:694](../../../ArkLib\Data\CodingTheory\ProximityGap\BCIKS20\Curves.lean#L694) — (no docstring)
- `lemma ProximityGap.coeff_zero_of_natDegree_lt` [ArkLib\Data\CodingTheory\ProximityGap\BCIKS20\Curves\Assembly.lean:31](../../../ArkLib\Data\CodingTheory\ProximityGap\BCIKS20\Curves\Assembly.lean#L31) — (no docstring)

### `core_stirling_add` (2 declarations, 2 files)

- `theorem CodingTheory.ABF26C38.core_stirling_add` [ArkLib\Data\CodingTheory\ListDecoding\Bounds.lean:458](../../../ArkLib\Data\CodingTheory\ListDecoding\Bounds.lean#L458) — (no docstring)
- `theorem CodingTheory.ABF26C38.core_stirling_add` [ArkLib\Data\CodingTheory\ListDecoding\Bounds\General.lean:329](../../../ArkLib\Data\CodingTheory\ListDecoding\Bounds\General.lean#L329) — (no docstring)

### `decodeLT_ne_of_val_ne` (2 declarations, 2 files)

- `lemma OutOfDomSmpl.decodeLT_ne_of_val_ne` [ArkLib\ProofSystem\Stir\OutOfDomSmpl.lean:87](../../../ArkLib\ProofSystem\Stir\OutOfDomSmpl.lean#L87) — Distinct codewords decode to distinct polynomials: the decoded polynomial interpolates the codeword
- `lemma OutOfDomSmpl.decodeLT_ne_of_val_ne` [ArkLib\ProofSystem\Whir\OutofDomainSmpl.lean:181](../../../ArkLib\ProofSystem\Whir\OutofDomainSmpl.lean#L181) — Distinct smooth codewords decode to distinct univariate polynomials (the decoded polynomial interpol

### `ehQ` (2 declarations, 2 files)

- `def MvPolynomial.ehQ` [ArkLib\ToMathlib\RestrictedSumset.lean:218](../../../ArkLib\ToMathlib\RestrictedSumset.lean#L218) — **The Erdős–Heilbronn polynomial** for a padded sumset `C'`.
- `def MvPolynomial.ehQ` [ArkLib\ToMathlib\RestrictedSumsetGeneral.lean:273](../../../ArkLib\ToMathlib\RestrictedSumsetGeneral.lean#L273) — **The general Erdős–Heilbronn polynomial** for a padded sumset `C'`.

### `ehY` (2 declarations, 2 files)

- `def MvPolynomial.ehY` [ArkLib\ToMathlib\RestrictedSumset.lean:169](../../../ArkLib\ToMathlib\RestrictedSumset.lean#L169) — Abbreviation for the "diagonal" variable `y = X₀ + X₁`.
- `def MvPolynomial.ehY` [ArkLib\ToMathlib\RestrictedSumsetGeneral.lean:191](../../../ArkLib\ToMathlib\RestrictedSumsetGeneral.lean#L191) — The "diagonal" variable `y = ∑_k X k`.

### `epsMCAgs_prizeBound_conjecture_holds` (2 declarations, 2 files)

- `theorem ProximityGap.MCAGS.epsMCAgs_prizeBound_conjecture_holds` [ArkLib\Data\CodingTheory\ProximityGap\GrandChallenge141PrizeMath.lean:134](../../../ArkLib\Data\CodingTheory\ProximityGap\GrandChallenge141PrizeMath.lean#L134) — **The per-input GS-exposed prize conjecture is a theorem.** `epsMCAgs_prizeBound_conjecture` quantif
- `theorem ProximityGap.MCAGS.epsMCAgs_prizeBound_conjecture_holds` [ArkLib\Data\CodingTheory\ProximityGap\GrandChallenge141UniformResolved.lean:78](../../../ArkLib\Data\CodingTheory\ProximityGap\GrandChallenge141UniformResolved.lean#L78) — **The fixed-field uniform GS-exposed prize conjecture is a theorem.** Take `c₁ = c₂ = 0` and `c₃ = n

### `evalEval_congr` (2 declarations, 2 files)

- `lemma R15.evalEval_congr` [ArkLib\Data\CodingTheory\ProximityGap\SudanListBound.lean:302](../../../ArkLib\Data\CodingTheory\ProximityGap\SudanListBound.lean#L302) — The double evaluation `Q(a, f(a))` depends on `f` only through the value `f(a)`.
- `lemma R15.evalEval_congr` [ArkLib\Data\CodingTheory\ProximityGap\SudanListBoundFull.lean:302](../../../ArkLib\Data\CodingTheory\ProximityGap\SudanListBoundFull.lean#L302) — The double evaluation `Q(a, f(a))` depends on `f` only through the value `f(a)`.

### `eval_ehQ_eq_zero` (2 declarations, 2 files)

- `lemma MvPolynomial.eval_ehQ_eq_zero` [ArkLib\ToMathlib\RestrictedSumset.lean:294](../../../ArkLib\ToMathlib\RestrictedSumset.lean#L294) — `ehQ Cset` vanishes at every point `s : Fin 2 → F` whose two coordinates either coincide, or sum to
- `lemma MvPolynomial.eval_ehQ_eq_zero` [ArkLib\ToMathlib\RestrictedSumsetGeneral.lean:335](../../../ArkLib\ToMathlib\RestrictedSumsetGeneral.lean#L335) — `ehQ h Cset` vanishes at every point `s : Fin h → F` whose coordinates are not all distinct, or whos

### `eval_eval_eq_sum` (2 declarations, 2 files)

- `lemma R15.eval_eval_eq_sum` [ArkLib\Data\CodingTheory\ProximityGap\SudanListBound.lean:293](../../../ArkLib\Data\CodingTheory\ProximityGap\SudanListBound.lean#L293) — Expansion of the double evaluation `Q(a, f(a))` as a sum over the `Y`-support.
- `lemma R15.eval_eval_eq_sum` [ArkLib\Data\CodingTheory\ProximityGap\SudanListBoundFull.lean:293](../../../ArkLib\Data\CodingTheory\ProximityGap\SudanListBoundFull.lean#L293) — Expansion of the double evaluation `Q(a, f(a))` as a sum over the `Y`-support.

### `exists_code_of_randomLinearLambdaLowerEvent` (2 declarations, 2 files)

- `theorem CodingTheory.exists_code_of_randomLinearLambdaLowerEvent` [ArkLib\Data\CodingTheory\ListDecoding\Bounds.lean:1529](../../../ArkLib\Data\CodingTheory\ListDecoding\Bounds.lean#L1529) — A good generator matrix gives the existential code witness used by the legacy front door.
- `theorem CodingTheory.exists_code_of_randomLinearLambdaLowerEvent` [ArkLib\Data\CodingTheory\ListDecoding\Bounds\RandomAndReedSolomon.lean:210](../../../ArkLib\Data\CodingTheory\ListDecoding\Bounds\RandomAndReedSolomon.lean#L210) — A good generator matrix gives the existential code witness used by the legacy front door.

### `exists_code_of_randomLinearLambdaLowerFirstMomentResidual` (2 declarations, 2 files)

- `theorem CodingTheory.exists_code_of_randomLinearLambdaLowerFirstMomentResidual` [ArkLib\Data\CodingTheory\ListDecoding\Bounds.lean:1543](../../../ArkLib\Data\CodingTheory\ListDecoding\Bounds.lean#L1543) — The pointwise first-moment residual supplies the legacy existential-code witness.
- `theorem CodingTheory.exists_code_of_randomLinearLambdaLowerFirstMomentResidual` [ArkLib\Data\CodingTheory\ListDecoding\Bounds\RandomAndReedSolomon.lean:224](../../../ArkLib\Data\CodingTheory\ListDecoding\Bounds\RandomAndReedSolomon.lean#L224) — The pointwise first-moment residual supplies the legacy existential-code witness.

### `exists_randomLinearLambdaLowerEvent_of_probability_pos` (2 declarations, 2 files)

- `theorem CodingTheory.exists_randomLinearLambdaLowerEvent_of_probability_pos` [ArkLib\Data\CodingTheory\ListDecoding\Bounds.lean:1467](../../../ArkLib\Data\CodingTheory\ListDecoding\Bounds.lean#L1467) — A positive success probability supplies a concrete good generator matrix.
- `theorem CodingTheory.exists_randomLinearLambdaLowerEvent_of_probability_pos` [ArkLib\Data\CodingTheory\ListDecoding\Bounds\RandomAndReedSolomon.lean:148](../../../ArkLib\Data\CodingTheory\ListDecoding\Bounds\RandomAndReedSolomon.lean#L148) — A positive success probability supplies a concrete good generator matrix.

### `exists_representative_center_sum_hammingDist_le` (2 declarations, 2 files)

- `theorem CodingTheory.exists_representative_center_sum_hammingDist_le` [ArkLib\Data\CodingTheory\ListDecoding\Bounds.lean:1003](../../../ArkLib\Data\CodingTheory\ListDecoding\Bounds.lean#L1003) — **ST20 plurality-center averaging core (in-tree, fully proven).** Given `ℓ + 1` words `c₀, …, c_ℓ :
- `theorem CodingTheory.exists_representative_center_sum_hammingDist_le` [ArkLib\Data\CodingTheory\ListDecoding\Bounds\General.lean:874](../../../ArkLib\Data\CodingTheory\ListDecoding\Bounds\General.lean#L874) — **ST20 plurality-center averaging core (in-tree, fully proven).** Given `ℓ + 1` words `c₀, …, c_ℓ :

### `fact_eq_ss` (2 declarations, 2 files)

- `theorem CodingTheory.ABF26C38.fact_eq_ss` [ArkLib\Data\CodingTheory\ListDecoding\Bounds.lean:588](../../../ArkLib\Data\CodingTheory\ListDecoding\Bounds.lean#L588) — (no docstring)
- `theorem CodingTheory.ABF26C38.fact_eq_ss` [ArkLib\Data\CodingTheory\ListDecoding\Bounds\General.lean:459](../../../ArkLib\Data\CodingTheory\ListDecoding\Bounds\General.lean#L459) — (no docstring)

### `finset_card_ge_of_pred_natCast_le_ennreal_lt` (2 declarations, 2 files)

- `lemma ProximityGap.finset_card_ge_of_pred_natCast_le_ennreal_lt` [ArkLib\Data\CodingTheory\ProximityGap\BCIKS20\Curves.lean:127](../../../ArkLib\Data\CodingTheory\ProximityGap\BCIKS20\Curves.lean#L127) — (no docstring)
- `theorem ProximityGap.finset_card_ge_of_pred_natCast_le_ennreal_lt` [ArkLib\Data\CodingTheory\ProximityGap\BCIKS20\Curves\Assembly.lean:131](../../../ArkLib\Data\CodingTheory\ProximityGap\BCIKS20\Curves\Assembly.lean#L131) — Convert an ENNReal lower bound on a finite set cardinality into a natural number weak cardinality bo

### `finset_card_gt_of_natCast_le_ennreal_lt` (2 declarations, 2 files)

- `lemma ProximityGap.finset_card_gt_of_natCast_le_ennreal_lt` [ArkLib\Data\CodingTheory\ProximityGap\BCIKS20\Curves.lean:120](../../../ArkLib\Data\CodingTheory\ProximityGap\BCIKS20\Curves.lean#L120) — (no docstring)
- `theorem ProximityGap.finset_card_gt_of_natCast_le_ennreal_lt` [ArkLib\Data\CodingTheory\ProximityGap\BCIKS20\Curves\Assembly.lean:120](../../../ArkLib\Data\CodingTheory\ProximityGap\BCIKS20\Curves\Assembly.lean#L120) — Convert an ENNReal lower bound on a finite set cardinality into a natural number strict cardinality

### `for` (2 declarations, 2 files)

- `theorem for` [ArkLib\OracleReduction\Composition\Sequential\AppendPerfectCompletenessProof.lean:14](../../../ArkLib\OracleReduction\Composition\Sequential\AppendPerfectCompletenessProof.lean#L14) — (no docstring)
- `theorem for` [ArkLib\ProofSystem\Logup\Security\Soundness.lean:46](../../../ArkLib\ProofSystem\Logup\Security\Soundness.lean#L46) — (no docstring)

### `frs_list_decoding_capacity_cz25` (2 declarations, 2 files)

- `def CodingTheory.frs_list_decoding_capacity_cz25` [ArkLib\Data\CodingTheory\ListDecoding\Bounds.lean:2188](../../../ArkLib\Data\CodingTheory\ListDecoding\Bounds.lean#L2188) — **ABF26 Corollary 3.5 [CZ25 Corollary 2.21].** Folded Reed-Solomon codes are list-decodable up to ca
- `def CodingTheory.frs_list_decoding_capacity_cz25` [ArkLib\Data\CodingTheory\ListDecoding\Bounds\SubspaceDesign.lean:116](../../../ArkLib\Data\CodingTheory\ListDecoding\Bounds\SubspaceDesign.lean#L116) — **ABF26 Corollary 3.5 [CZ25 Corollary 2.21].** Folded Reed-Solomon codes are list-decodable up to ca

### `frs_list_decoding_capacity_cz25_of_T218_le_one_eta_eq_one_div_nat_prop` (2 declarations, 2 files)

- `theorem CodingTheory.frs_list_decoding_capacity_cz25_of_T218_le_one_eta_eq_one_div_nat_prop` [ArkLib\Data\CodingTheory\ListDecoding\Bounds.lean:2260](../../../ArkLib\Data\CodingTheory\ListDecoding\Bounds.lean#L2260) — Prop-level C3.5 endpoint from the unique-list/T2.18 easy slice, using the documented reciprocal-natu
- `theorem CodingTheory.frs_list_decoding_capacity_cz25_of_T218_le_one_eta_eq_one_div_nat_prop` [ArkLib\Data\CodingTheory\ListDecoding\Bounds\SubspaceDesign.lean:188](../../../ArkLib\Data\CodingTheory\ListDecoding\Bounds\SubspaceDesign.lean#L188) — Prop-level C3.5 endpoint from the unique-list/T2.18 easy slice, using the documented reciprocal-natu

### `frs_list_decoding_capacity_cz25_of_T218_le_one_prop` (2 declarations, 2 files)

- `theorem CodingTheory.frs_list_decoding_capacity_cz25_of_T218_le_one_prop` [ArkLib\Data\CodingTheory\ListDecoding\Bounds.lean:2237](../../../ArkLib\Data\CodingTheory\ListDecoding\Bounds.lean#L2237) — Prop-level C3.5 endpoint from the unique-list/T2.18 easy slice. This wraps the unfolded reduction `f
- `theorem CodingTheory.frs_list_decoding_capacity_cz25_of_T218_le_one_prop` [ArkLib\Data\CodingTheory\ListDecoding\Bounds\SubspaceDesign.lean:165](../../../ArkLib\Data\CodingTheory\ListDecoding\Bounds\SubspaceDesign.lean#L165) — Prop-level C3.5 endpoint from the unique-list/T2.18 easy slice. This wraps the unfolded reduction `f

### `frs_list_decoding_capacity_cz25_of_coordFiberCap_T218_eta_eq_one_div_nat_prop` (2 declarations, 2 files)

- `theorem CodingTheory.frs_list_decoding_capacity_cz25_of_coordFiberCap_T218_eta_eq_one_div_nat_prop` [ArkLib\Data\CodingTheory\ListDecoding\Bounds.lean:2350](../../../ArkLib\Data\CodingTheory\ListDecoding\Bounds.lean#L2350) — Prop-level C3.5 endpoint from coordinate-fiber cap plus T2.18, using the documented reciprocal-natur
- `theorem CodingTheory.frs_list_decoding_capacity_cz25_of_coordFiberCap_T218_eta_eq_one_div_nat_prop` [ArkLib\Data\CodingTheory\ListDecoding\Bounds\SubspaceDesign.lean:278](../../../ArkLib\Data\CodingTheory\ListDecoding\Bounds\SubspaceDesign.lean#L278) — Prop-level C3.5 endpoint from coordinate-fiber cap plus T2.18, using the documented reciprocal-natur

### `frs_list_decoding_capacity_cz25_of_coordFiberCap_admissible_eta_eq_one_div_nat_prop` (2 declarations, 2 files)

- `theorem CodingTheory.frs_list_decoding_capacity_cz25_of_coordFiberCap_admissible_eta_eq_one_div_nat_prop` [ArkLib\Data\CodingTheory\ListDecoding\Bounds.lean:2406](../../../ArkLib\Data\CodingTheory\ListDecoding\Bounds.lean#L2406) — Prop-level C3.5 endpoint from coordinate-fiber cap plus the admissible GK16 FRS bridge, using the re
- `theorem CodingTheory.frs_list_decoding_capacity_cz25_of_coordFiberCap_admissible_eta_eq_one_div_nat_prop` [ArkLib\Data\CodingTheory\ListDecoding\Bounds\SubspaceDesign.lean:334](../../../ArkLib\Data\CodingTheory\ListDecoding\Bounds\SubspaceDesign.lean#L334) — Prop-level C3.5 endpoint from coordinate-fiber cap plus the admissible GK16 FRS bridge, using the re

### `frs_list_decoding_capacity_cz25_of_coordFiberCap_admissible_prop` (2 declarations, 2 files)

- `theorem CodingTheory.frs_list_decoding_capacity_cz25_of_coordFiberCap_admissible_prop` [ArkLib\Data\CodingTheory\ListDecoding\Bounds.lean:2331](../../../ArkLib\Data\CodingTheory\ListDecoding\Bounds.lean#L2331) — Prop-level C3.5 endpoint from coordinate-fiber cap plus the admissible GK16 FRS bridge.
- `theorem CodingTheory.frs_list_decoding_capacity_cz25_of_coordFiberCap_admissible_prop` [ArkLib\Data\CodingTheory\ListDecoding\Bounds\SubspaceDesign.lean:259](../../../ArkLib\Data\CodingTheory\ListDecoding\Bounds\SubspaceDesign.lean#L259) — Prop-level C3.5 endpoint from coordinate-fiber cap plus the admissible GK16 FRS bridge.

### `frs_list_decoding_capacity_cz25_of_coordFiberCap_injective_eta_eq_one_div_nat_prop` (2 declarations, 2 files)

- `theorem CodingTheory.frs_list_decoding_capacity_cz25_of_coordFiberCap_injective_eta_eq_one_div_nat_prop` [ArkLib\Data\CodingTheory\ListDecoding\Bounds.lean:2378](../../../ArkLib\Data\CodingTheory\ListDecoding\Bounds.lean#L2378) — Prop-level C3.5 endpoint from coordinate-fiber cap plus the injective GK16 FRS bridge, using the rec
- `theorem CodingTheory.frs_list_decoding_capacity_cz25_of_coordFiberCap_injective_eta_eq_one_div_nat_prop` [ArkLib\Data\CodingTheory\ListDecoding\Bounds\SubspaceDesign.lean:306](../../../ArkLib\Data\CodingTheory\ListDecoding\Bounds\SubspaceDesign.lean#L306) — Prop-level C3.5 endpoint from coordinate-fiber cap plus the injective GK16 FRS bridge, using the rec

### `frs_list_decoding_capacity_cz25_of_coordFiberCap_injective_prop` (2 declarations, 2 files)

- `theorem CodingTheory.frs_list_decoding_capacity_cz25_of_coordFiberCap_injective_prop` [ArkLib\Data\CodingTheory\ListDecoding\Bounds.lean:2312](../../../ArkLib\Data\CodingTheory\ListDecoding\Bounds.lean#L2312) — Prop-level C3.5 endpoint from coordinate-fiber cap plus the injective GK16 FRS bridge.
- `theorem CodingTheory.frs_list_decoding_capacity_cz25_of_coordFiberCap_injective_prop` [ArkLib\Data\CodingTheory\ListDecoding\Bounds\SubspaceDesign.lean:240](../../../ArkLib\Data\CodingTheory\ListDecoding\Bounds\SubspaceDesign.lean#L240) — Prop-level C3.5 endpoint from coordinate-fiber cap plus the injective GK16 FRS bridge.

### `frs_list_decoding_capacity_cz25_of_coordFiberCap_orderOf_ge_of_cosetSep_eta_eq_one_div_nat_prop` (2 declarations, 2 files)

- `theorem CodingTheory.frs_list_decoding_capacity_cz25_of_coordFiberCap_orderOf_ge_of_cosetSep_eta_eq_one_div_nat_prop` [ArkLib\Data\CodingTheory\ListDecoding\Bounds.lean:2506](../../../ArkLib\Data\CodingTheory\ListDecoding\Bounds.lean#L2506) — Prop-level C3.5 endpoint from coordinate-fiber cap plus the order/coset-separation T2.18 front door,
- `theorem CodingTheory.frs_list_decoding_capacity_cz25_of_coordFiberCap_orderOf_ge_of_cosetSep_eta_eq_one_div_nat_prop` [ArkLib\Data\CodingTheory\ListDecoding\Bounds\SubspaceDesign.lean:434](../../../ArkLib\Data\CodingTheory\ListDecoding\Bounds\SubspaceDesign.lean#L434) — Prop-level C3.5 endpoint from coordinate-fiber cap plus the order/coset-separation T2.18 front door,

### `frs_list_decoding_capacity_cz25_of_coordFiberCap_orderOf_ge_of_cosetSep_prop` (2 declarations, 2 files)

- `theorem CodingTheory.frs_list_decoding_capacity_cz25_of_coordFiberCap_orderOf_ge_of_cosetSep_prop` [ArkLib\Data\CodingTheory\ListDecoding\Bounds.lean:2484](../../../ArkLib\Data\CodingTheory\ListDecoding\Bounds.lean#L2484) — Prop-level C3.5 endpoint from coordinate-fiber cap plus the order/coset-separation T2.18 front door.
- `theorem CodingTheory.frs_list_decoding_capacity_cz25_of_coordFiberCap_orderOf_ge_of_cosetSep_prop` [ArkLib\Data\CodingTheory\ListDecoding\Bounds\SubspaceDesign.lean:412](../../../ArkLib\Data\CodingTheory\ListDecoding\Bounds\SubspaceDesign.lean#L412) — Prop-level C3.5 endpoint from coordinate-fiber cap plus the order/coset-separation T2.18 front door.

### `frs_list_decoding_capacity_cz25_of_coordFiberCap_orderOf_ge_of_inter_eta_eq_one_div_nat_prop` (2 declarations, 2 files)

- `theorem CodingTheory.frs_list_decoding_capacity_cz25_of_coordFiberCap_orderOf_ge_of_inter_eta_eq_one_div_nat_prop` [ArkLib\Data\CodingTheory\ListDecoding\Bounds.lean:2455](../../../ArkLib\Data\CodingTheory\ListDecoding\Bounds.lean#L2455) — Prop-level C3.5 endpoint from coordinate-fiber cap plus the order/inter T2.18 front door, using the
- `theorem CodingTheory.frs_list_decoding_capacity_cz25_of_coordFiberCap_orderOf_ge_of_inter_eta_eq_one_div_nat_prop` [ArkLib\Data\CodingTheory\ListDecoding\Bounds\SubspaceDesign.lean:383](../../../ArkLib\Data\CodingTheory\ListDecoding\Bounds\SubspaceDesign.lean#L383) — Prop-level C3.5 endpoint from coordinate-fiber cap plus the order/inter T2.18 front door, using the

### `frs_list_decoding_capacity_cz25_of_coordFiberCap_orderOf_ge_of_inter_prop` (2 declarations, 2 files)

- `theorem CodingTheory.frs_list_decoding_capacity_cz25_of_coordFiberCap_orderOf_ge_of_inter_prop` [ArkLib\Data\CodingTheory\ListDecoding\Bounds.lean:2434](../../../ArkLib\Data\CodingTheory\ListDecoding\Bounds.lean#L2434) — Prop-level C3.5 endpoint from coordinate-fiber cap plus the order/inter T2.18 front door. This keeps
- `theorem CodingTheory.frs_list_decoding_capacity_cz25_of_coordFiberCap_orderOf_ge_of_inter_prop` [ArkLib\Data\CodingTheory\ListDecoding\Bounds\SubspaceDesign.lean:362](../../../ArkLib\Data\CodingTheory\ListDecoding\Bounds\SubspaceDesign.lean#L362) — Prop-level C3.5 endpoint from coordinate-fiber cap plus the order/inter T2.18 front door. This keeps

### `frs_list_decoding_capacity_cz25_of_residuals` (2 declarations, 2 files)

- `theorem CodingTheory.frs_list_decoding_capacity_cz25_of_residuals` [ArkLib\Data\CodingTheory\ListDecoding\Bounds.lean:2137](../../../ArkLib\Data\CodingTheory\ListDecoding\Bounds.lean#L2137) — **ABF26 Corollary 3.5 [CZ25 Cor 2.21] — honest reduction form.** The *full in-tree-provable content*
- `theorem CodingTheory.frs_list_decoding_capacity_cz25_of_residuals` [ArkLib\Data\CodingTheory\ListDecoding\Bounds\SubspaceDesign.lean:65](../../../ArkLib\Data\CodingTheory\ListDecoding\Bounds\SubspaceDesign.lean#L65) — **ABF26 Corollary 3.5 [CZ25 Cor 2.21] — honest reduction form.** The *full in-tree-provable content*

### `frs_list_decoding_capacity_cz25_of_residuals_prop` (2 declarations, 2 files)

- `theorem CodingTheory.frs_list_decoding_capacity_cz25_of_residuals_prop` [ArkLib\Data\CodingTheory\ListDecoding\Bounds.lean:2212](../../../ArkLib\Data\CodingTheory\ListDecoding\Bounds.lean#L2212) — Prop-level wrapper for ABF26 C3.5. This closes the external statement `frs_list_decoding_capacity_cz
- `theorem CodingTheory.frs_list_decoding_capacity_cz25_of_residuals_prop` [ArkLib\Data\CodingTheory\ListDecoding\Bounds\SubspaceDesign.lean:140](../../../ArkLib\Data\CodingTheory\ListDecoding\Bounds\SubspaceDesign.lean#L140) — Prop-level wrapper for ABF26 C3.5. This closes the external statement `frs_list_decoding_capacity_cz

### `hasseEvalAtRoot_eq_unclearedHasseCoeff_div_W_natDegree_of_partitionMatchAt_zero` (2 declarations, 2 files)

- `theorem BCIKS20.HenselNumerator.hasseEvalAtRoot_eq_unclearedHasseCoeff_div_W_natDegree_of_partitionMatchAt_zero` [ArkLib\Data\CodingTheory\ProximityGap\BCIKS20\P2Reabsorb.lean:429](../../../ArkLib\Data\CodingTheory\ProximityGap\BCIKS20\P2Reabsorb.lean#L429) — Under the legitimate nonzero/degree hypotheses, any normalized partition order-zero match exposes th
- `theorem BCIKS20.HenselNumerator.hasseEvalAtRoot_eq_unclearedHasseCoeff_div_W_natDegree_of_partitionMatchAt_zero` [ArkLib\Data\CodingTheory\ProximityGap\BCIKS20\RestrictedFaaDiBrunoExtract.lean:313](../../../ArkLib\Data\CodingTheory\ProximityGap\BCIKS20\RestrictedFaaDiBrunoExtract.lean#L313) — **Project the uncleared-Hasse/`W^natDegree` equation from the normalized partition order-zero residu

### `hasseEvalAtRoot_eq_unclearedHasseCoeff_div_W_natDegree_of_restrictedMatchAt_zero` (2 declarations, 2 files)

- `theorem BCIKS20.HenselNumerator.hasseEvalAtRoot_eq_unclearedHasseCoeff_div_W_natDegree_of_restrictedMatchAt_zero` [ArkLib\Data\CodingTheory\ProximityGap\BCIKS20\P2Reabsorb.lean:378](../../../ArkLib\Data\CodingTheory\ProximityGap\BCIKS20\P2Reabsorb.lean#L378) — Under the legitimate nonzero/degree hypotheses, any carved order-zero match exposes the cleared-vs-u
- `theorem BCIKS20.HenselNumerator.hasseEvalAtRoot_eq_unclearedHasseCoeff_div_W_natDegree_of_restrictedMatchAt_zero` [ArkLib\Data\CodingTheory\ProximityGap\BCIKS20\RestrictedFaaDiBrunoExtract.lean:340](../../../ArkLib\Data\CodingTheory\ProximityGap\BCIKS20\RestrictedFaaDiBrunoExtract.lean#L340) — **Project the uncleared-Hasse/`W^natDegree` equation directly from the carved order-zero P2 core** (

### `johnsonDenom` (2 declarations, 2 files)

- `def ArkLib.JohnsonBound.johnsonDenom` [ArkLib\Data\CodingTheory\JohnsonBound\ListSize.lean:159](../../../ArkLib\Data\CodingTheory\JohnsonBound\ListSize.lean#L159) — The **Johnson denominator** `(n - e)² - n·(n - d)`. The Johnson regime is where it is positive.
- `def ArkLib.JohnsonBound.johnsonDenom` [ArkLib\Data\CodingTheory\ProximityGap\Issue244Refutation.lean:11](../../../ArkLib\Data\CodingTheory\ProximityGap\Issue244Refutation.lean#L11) — (no docstring)

### `large_alphabet_barrier_bdg24_agl23` (2 declarations, 2 files)

- `theorem CodingTheory.large_alphabet_barrier_bdg24_agl23` [ArkLib\Data\CodingTheory\ListDecoding\Bounds.lean:1371](../../../ArkLib\Data\CodingTheory\ListDecoding\Bounds.lean#L1371) — **ABF26 Theorem 3.10 [BDG24, AGL23].** Large-alphabet barrier for generalized Singleton attainment.
- `theorem CodingTheory.large_alphabet_barrier_bdg24_agl23` [ArkLib\Data\CodingTheory\ListDecoding\Bounds\RandomAndReedSolomon.lean:52](../../../ArkLib\Data\CodingTheory\ListDecoding\Bounds\RandomAndReedSolomon.lean#L52) — **ABF26 Theorem 3.10 [BDG24, AGL23].** Large-alphabet barrier for generalized Singleton attainment.

### `linear_C_le_generalized_singleton_st20` (2 declarations, 2 files)

- `theorem CodingTheory.linear_C_le_generalized_singleton_st20` [ArkLib\Data\CodingTheory\ListDecoding\Bounds.lean:1245](../../../ArkLib\Data\CodingTheory\ListDecoding\Bounds.lean#L1245) — **ABF26 Theorem 3.9 [ST20 Thm 1.2], linear refinement.** Generalized Singleton bound for list decodi
- `theorem CodingTheory.linear_C_le_generalized_singleton_st20` [ArkLib\Data\CodingTheory\ListDecoding\Bounds\General.lean:1116](../../../ArkLib\Data\CodingTheory\ListDecoding\Bounds\General.lean#L1116) — **ABF26 Theorem 3.9 [ST20 Thm 1.2], linear refinement.** Generalized Singleton bound for list decodi

### `linear_lambda_ge_elias_volume_eli57` (2 declarations, 2 files)

- `theorem CodingTheory.linear_lambda_ge_elias_volume_eli57` [ArkLib\Data\CodingTheory\ListDecoding\Bounds.lean:221](../../../ArkLib\Data\CodingTheory\ListDecoding\Bounds.lean#L221) — **ABF26 Lemma 3.7 [Eli57].** Elias volume lower bound on list size: `\|Λ(C, δ)\| ≥ Vol_q(δ, n) / q^(n-
- `theorem CodingTheory.linear_lambda_ge_elias_volume_eli57` [ArkLib\Data\CodingTheory\ListDecoding\Bounds\General.lean:92](../../../ArkLib\Data\CodingTheory\ListDecoding\Bounds\General.lean#L92) — **ABF26 Lemma 3.7 [Eli57].** Elias volume lower bound on list size: `\|Λ(C, δ)\| ≥ Vol_q(δ, n) / q^(n-

### `linear_lambda_ge_entropy_volume` (2 declarations, 2 files)

- `theorem CodingTheory.linear_lambda_ge_entropy_volume` [ArkLib\Data\CodingTheory\ListDecoding\Bounds.lean:919](../../../ArkLib\Data\CodingTheory\ListDecoding\Bounds.lean#L919) — **ABF26 Corollary 3.8.** Volume-based lower bound on list size, using the MS77 volume estimate `Vol_
- `theorem CodingTheory.linear_lambda_ge_entropy_volume` [ArkLib\Data\CodingTheory\ListDecoding\Bounds\General.lean:790](../../../ArkLib\Data\CodingTheory\ListDecoding\Bounds\General.lean#L790) — **ABF26 Corollary 3.8.** Volume-based lower bound on list size, using the MS77 volume estimate `Vol_

### `master_eq` (2 declarations, 2 files)

- `theorem CodingTheory.ABF26C38.master_eq` [ArkLib\Data\CodingTheory\ListDecoding\Bounds.lean:654](../../../ArkLib\Data\CodingTheory\ListDecoding\Bounds.lean#L654) — (no docstring)
- `theorem CodingTheory.ABF26C38.master_eq` [ArkLib\Data\CodingTheory\ListDecoding\Bounds\General.lean:525](../../../ArkLib\Data\CodingTheory\ListDecoding\Bounds\General.lean#L525) — (no docstring)

### `mcaPrizeLatticeResolved_with_spec_and_adjacent_brackets_of_with_spec` (2 declarations, 2 files)

- `theorem ProximityGap.GrandChallengesLattice.mcaPrizeLatticeResolved_with_spec_and_adjacent_brackets_of_with_spec` [ArkLib\Data\CodingTheory\ProximityGap\LineDecodingGrandChallengesPrizeSpec.lean:1487](../../../ArkLib\Data\CodingTheory\ProximityGap\LineDecodingGrandChallengesPrizeSpec.lean#L1487) — Add the immediate lower and adjacent upper lattice brackets to a concrete adjacent `mcaPrizeLatticeR
- `theorem ProximityGap.GrandChallengesLattice.mcaPrizeLatticeResolved_with_spec_and_adjacent_brackets_of_with_spec` [ArkLib\Data\CodingTheory\ProximityGap\MCAGSLatticePrizeSpec.lean:882](../../../ArkLib\Data\CodingTheory\ProximityGap\MCAGSLatticePrizeSpec.lean#L882) — Add the immediate lower and adjacent upper lattice brackets to a concrete adjacent `mcaPrizeLatticeR

### `mem_support_uniformRandomLinearGeneratorMatrix` (2 declarations, 2 files)

- `theorem CodingTheory.mem_support_uniformRandomLinearGeneratorMatrix` [ArkLib\Data\CodingTheory\ListDecoding\Bounds.lean:1417](../../../ArkLib\Data\CodingTheory\ListDecoding\Bounds.lean#L1417) — Every generator matrix lies in the support of the uniform generator-matrix distribution.
- `theorem CodingTheory.mem_support_uniformRandomLinearGeneratorMatrix` [ArkLib\Data\CodingTheory\ListDecoding\Bounds\RandomAndReedSolomon.lean:98](../../../ArkLib\Data\CodingTheory\ListDecoding\Bounds\RandomAndReedSolomon.lean#L98) — Every generator matrix lies in the support of the uniform generator-matrix distribution.

### `ms77_lattice` (2 declarations, 2 files)

- `theorem CodingTheory.ABF26C38.ms77_lattice` [ArkLib\Data\CodingTheory\ListDecoding\Bounds.lean:749](../../../ArkLib\Data\CodingTheory\ListDecoding\Bounds.lean#L749) — (no docstring)
- `theorem CodingTheory.ABF26C38.ms77_lattice` [ArkLib\Data\CodingTheory\ListDecoding\Bounds\General.lean:620](../../../ArkLib\Data\CodingTheory\ListDecoding\Bounds\General.lean#L620) — (no docstring)

### `natDegreeY_le` (2 declarations, 2 files)

- `lemma R15.natDegreeY_le` [ArkLib\Data\CodingTheory\ProximityGap\SudanListBound.lean:311](../../../ArkLib\Data\CodingTheory\ProximityGap\SudanListBound.lean#L311) — The per-monomial weighted-degree bound forces `deg_Y Q ≤ (D-1)/(k-1)` (for `k ≥ 2`), since the leadi
- `lemma R15.natDegreeY_le` [ArkLib\Data\CodingTheory\ProximityGap\SudanListBoundFull.lean:311](../../../ArkLib\Data\CodingTheory\ProximityGap\SudanListBoundFull.lean#L311) — The per-monomial weighted-degree bound forces `deg_Y Q ≤ (D-1)/(k-1)` (for `k ≥ 2`), since the leadi

### `pins` (2 declarations, 2 files)

- `structure pins` [ArkLib\Data\CodingTheory\ProximityGap\JointT2FiberTightness.lean:42](../../../ArkLib\Data\CodingTheory\ProximityGap\JointT2FiberTightness.lean#L42) — (no docstring)
- `structure pins` [ArkLib\Data\CodingTheory\ProximityGap\ListRecoveryInterleavedGap.lean:18](../../../ArkLib\Data\CodingTheory\ProximityGap\ListRecoveryInterleavedGap.lean#L18) — (no docstring)

### `power_identity` (2 declarations, 2 files)

- `theorem CodingTheory.ABF26C38.power_identity` [ArkLib\Data\CodingTheory\ListDecoding\Bounds.lean:619](../../../ArkLib\Data\CodingTheory\ListDecoding\Bounds.lean#L619) — (no docstring)
- `theorem CodingTheory.ABF26C38.power_identity` [ArkLib\Data\CodingTheory\ListDecoding\Bounds\General.lean:490](../../../ArkLib\Data\CodingTheory\ListDecoding\Bounds\General.lean#L490) — (no docstring)

### `qpow_eq_exp` (2 declarations, 2 files)

- `theorem CodingTheory.ABF26C38.qpow_eq_exp` [ArkLib\Data\CodingTheory\ListDecoding\Bounds.lean:734](../../../ArkLib\Data\CodingTheory\ListDecoding\Bounds.lean#L734) — (no docstring)
- `theorem CodingTheory.ABF26C38.qpow_eq_exp` [ArkLib\Data\CodingTheory\ListDecoding\Bounds\General.lean:605](../../../ArkLib\Data\CodingTheory\ListDecoding\Bounds\General.lean#L605) — (no docstring)

### `radical_collapse` (2 declarations, 2 files)

- `theorem CodingTheory.ABF26C38.radical_collapse` [ArkLib\Data\CodingTheory\ListDecoding\Bounds.lean:597](../../../ArkLib\Data\CodingTheory\ListDecoding\Bounds.lean#L597) — (no docstring)
- `theorem CodingTheory.ABF26C38.radical_collapse` [ArkLib\Data\CodingTheory\ListDecoding\Bounds\General.lean:468](../../../ArkLib\Data\CodingTheory\ListDecoding\Bounds\General.lean#L468) — (no docstring)

### `randomLinearCodeOfGeneratorMatrix` (2 declarations, 2 files)

- `def CodingTheory.randomLinearCodeOfGeneratorMatrix` [ArkLib\Data\CodingTheory\ListDecoding\Bounds.lean:1425](../../../ArkLib\Data\CodingTheory\ListDecoding\Bounds.lean#L1425) — The linear code generated by the rows of a sampled generator matrix.
- `def CodingTheory.randomLinearCodeOfGeneratorMatrix` [ArkLib\Data\CodingTheory\ListDecoding\Bounds\RandomAndReedSolomon.lean:106](../../../ArkLib\Data\CodingTheory\ListDecoding\Bounds\RandomAndReedSolomon.lean#L106) — The linear code generated by the rows of a sampled generator matrix.

### `randomLinearLambdaLowerEvent` (2 declarations, 2 files)

- `def CodingTheory.randomLinearLambdaLowerEvent` [ArkLib\Data\CodingTheory\ListDecoding\Bounds.lean:1438](../../../ArkLib\Data\CodingTheory\ListDecoding\Bounds.lean#L1438) — The GLMRSW22 list-size lower-bound event for one sampled generator matrix.
- `def CodingTheory.randomLinearLambdaLowerEvent` [ArkLib\Data\CodingTheory\ListDecoding\Bounds\RandomAndReedSolomon.lean:119](../../../ArkLib\Data\CodingTheory\ListDecoding\Bounds\RandomAndReedSolomon.lean#L119) — The GLMRSW22 list-size lower-bound event for one sampled generator matrix.

### `randomLinearLambdaLowerFirstMomentResidual` (2 declarations, 2 files)

- `def CodingTheory.randomLinearLambdaLowerFirstMomentResidual` [ArkLib\Data\CodingTheory\ListDecoding\Bounds.lean:1461](../../../ArkLib\Data\CodingTheory\ListDecoding\Bounds.lean#L1461) — Pointwise GLMRSW22 first-moment residual at fixed field, blocklength, generator dimension, and rate
- `def CodingTheory.randomLinearLambdaLowerFirstMomentResidual` [ArkLib\Data\CodingTheory\ListDecoding\Bounds\RandomAndReedSolomon.lean:142](../../../ArkLib\Data\CodingTheory\ListDecoding\Bounds\RandomAndReedSolomon.lean#L142) — Pointwise GLMRSW22 first-moment residual at fixed field, blocklength, generator dimension, and rate

### `randomLinearLambdaLowerFirstMomentResidual_of_exists_event` (2 declarations, 2 files)

- `theorem CodingTheory.randomLinearLambdaLowerFirstMomentResidual_of_exists_event` [ArkLib\Data\CodingTheory\ListDecoding\Bounds.lean:1519](../../../ArkLib\Data\CodingTheory\ListDecoding\Bounds.lean#L1519) — A concrete successful generator matrix supplies the named first-moment residual.
- `theorem CodingTheory.randomLinearLambdaLowerFirstMomentResidual_of_exists_event` [ArkLib\Data\CodingTheory\ListDecoding\Bounds\RandomAndReedSolomon.lean:200](../../../ArkLib\Data\CodingTheory\ListDecoding\Bounds\RandomAndReedSolomon.lean#L200) — A concrete successful generator matrix supplies the named first-moment residual.

### `randomLinearLambdaLowerProbability` (2 declarations, 2 files)

- `def CodingTheory.randomLinearLambdaLowerProbability` [ArkLib\Data\CodingTheory\ListDecoding\Bounds.lean:1448](../../../ArkLib\Data\CodingTheory\ListDecoding\Bounds.lean#L1448) — Success probability of the GLMRSW22 lower-bound event under uniform generator matrices.
- `def CodingTheory.randomLinearLambdaLowerProbability` [ArkLib\Data\CodingTheory\ListDecoding\Bounds\RandomAndReedSolomon.lean:129](../../../ArkLib\Data\CodingTheory\ListDecoding\Bounds\RandomAndReedSolomon.lean#L129) — Success probability of the GLMRSW22 lower-bound event under uniform generator matrices.

### `randomLinearLambdaLowerProbability_pos_of_exists_event` (2 declarations, 2 files)

- `theorem CodingTheory.randomLinearLambdaLowerProbability_pos_of_exists_event` [ArkLib\Data\CodingTheory\ListDecoding\Bounds.lean:1502](../../../ArkLib\Data\CodingTheory\ListDecoding\Bounds.lean#L1502) — Conversely, one good generator matrix gives positive success probability. This uses only the full su
- `theorem CodingTheory.randomLinearLambdaLowerProbability_pos_of_exists_event` [ArkLib\Data\CodingTheory\ListDecoding\Bounds\RandomAndReedSolomon.lean:183](../../../ArkLib\Data\CodingTheory\ListDecoding\Bounds\RandomAndReedSolomon.lean#L183) — Conversely, one good generator matrix gives positive success probability. This uses only the full su

### `random_linear_lambda_lower_glmrsw22` (2 declarations, 2 files)

- `def CodingTheory.random_linear_lambda_lower_glmrsw22` [ArkLib\Data\CodingTheory\ListDecoding\Bounds.lean:1577](../../../ArkLib\Data\CodingTheory\ListDecoding\Bounds.lean#L1577) — **ABF26 Theorem 3.11 [GLMRSW22 Thm 4.1].** Random linear code lower bound. Fix a prime `q`, `δ ∈ (0,
- `def CodingTheory.random_linear_lambda_lower_glmrsw22` [ArkLib\Data\CodingTheory\ListDecoding\Bounds\RandomAndReedSolomon.lean:258](../../../ArkLib\Data\CodingTheory\ListDecoding\Bounds\RandomAndReedSolomon.lean#L258) — **ABF26 Theorem 3.11 [GLMRSW22 Thm 4.1].** Random linear code lower bound. Fix a prime `q`, `δ ∈ (0,

### `random_linear_lambda_lower_glmrsw22_of_first_moment_residual` (2 declarations, 2 files)

- `theorem CodingTheory.random_linear_lambda_lower_glmrsw22_of_first_moment_residual` [ArkLib\Data\CodingTheory\ListDecoding\Bounds.lean:1673](../../../ArkLib\Data\CodingTheory\ListDecoding\Bounds.lean#L1673) — A named first-moment residual family supplies the legacy existential GLMRSW22 front door.
- `theorem CodingTheory.random_linear_lambda_lower_glmrsw22_of_first_moment_residual` [ArkLib\Data\CodingTheory\ListDecoding\Bounds\RandomAndReedSolomon.lean:354](../../../ArkLib\Data\CodingTheory\ListDecoding\Bounds\RandomAndReedSolomon.lean#L354) — A named first-moment residual family supplies the legacy existential GLMRSW22 front door.

### `random_linear_lambda_lower_glmrsw22_of_random_generator_matrix` (2 declarations, 2 files)

- `theorem CodingTheory.random_linear_lambda_lower_glmrsw22_of_random_generator_matrix` [ArkLib\Data\CodingTheory\ListDecoding\Bounds.lean:1623](../../../ArkLib\Data\CodingTheory\ListDecoding\Bounds.lean#L1623) — Positive probability in the random-generator-matrix form reassembles the legacy existential GLMRSW22
- `theorem CodingTheory.random_linear_lambda_lower_glmrsw22_of_random_generator_matrix` [ArkLib\Data\CodingTheory\ListDecoding\Bounds\RandomAndReedSolomon.lean:304](../../../ArkLib\Data\CodingTheory\ListDecoding\Bounds\RandomAndReedSolomon.lean#L304) — Positive probability in the random-generator-matrix form reassembles the legacy existential GLMRSW22

### `random_linear_lambda_lower_glmrsw22_random_generator_matrix` (2 declarations, 2 files)

- `def CodingTheory.random_linear_lambda_lower_glmrsw22_random_generator_matrix` [ArkLib\Data\CodingTheory\ListDecoding\Bounds.lean:1607](../../../ArkLib\Data\CodingTheory\ListDecoding\Bounds.lean#L1607) — Faithful random-generator-matrix form of the GLMRSW22 lower bound, with the high-probability estimat
- `def CodingTheory.random_linear_lambda_lower_glmrsw22_random_generator_matrix` [ArkLib\Data\CodingTheory\ListDecoding\Bounds\RandomAndReedSolomon.lean:288](../../../ArkLib\Data\CodingTheory\ListDecoding\Bounds\RandomAndReedSolomon.lean#L288) — Faithful random-generator-matrix form of the GLMRSW22 lower bound, with the high-probability estimat

### `random_linear_lambda_lower_glmrsw22_random_generator_matrix_of_first_moment_residual` (2 declarations, 2 files)

- `theorem CodingTheory.random_linear_lambda_lower_glmrsw22_random_generator_matrix_of_first_moment_residual` [ArkLib\Data\CodingTheory\ListDecoding\Bounds.lean:1654](../../../ArkLib\Data\CodingTheory\ListDecoding\Bounds.lean#L1654) — A named first-moment residual family supplies the faithful random-generator-matrix GLMRSW22 surface.
- `theorem CodingTheory.random_linear_lambda_lower_glmrsw22_random_generator_matrix_of_first_moment_residual` [ArkLib\Data\CodingTheory\ListDecoding\Bounds\RandomAndReedSolomon.lean:335](../../../ArkLib\Data\CodingTheory\ListDecoding\Bounds\RandomAndReedSolomon.lean#L335) — A named first-moment residual family supplies the faithful random-generator-matrix GLMRSW22 surface.

### `random_rs_list_decoding` (2 declarations, 2 files)

- `def CodingTheory.random_rs_list_decoding` [ArkLib\Data\CodingTheory\ListDecoding\Bounds.lean:189](../../../ArkLib\Data\CodingTheory\ListDecoding\Bounds.lean#L189) — **ABF26 Theorem 3.6 [AGL24 Thm 1.1], statement front door.** For a finite field `F`, a positive leng
- `def CodingTheory.random_rs_list_decoding` [ArkLib\Data\CodingTheory\ListDecoding\Bounds\General.lean:60](../../../ArkLib\Data\CodingTheory\ListDecoding\Bounds\General.lean#L60) — **ABF26 Theorem 3.6 [AGL24 Thm 1.1], statement front door.** For a finite field `F`, a positive leng

### `reduction_append_perfectCompleteness_msg` (2 declarations, 2 files)

- `theorem Reduction.reduction_append_perfectCompleteness_msg` [ArkLib\OracleReduction\Composition\Sequential\AppendPerfectCompletenessMsg.lean:414](../../../ArkLib\OracleReduction\Composition\Sequential\AppendPerfectCompletenessMsg.lean#L414) — **Append perfect completeness, residual-free (message-seam case).** The public composition theorem w
- `def Reduction.reduction_append_perfectCompleteness_msg` [ArkLib\whir113keystone.lean:17](../../../ArkLib\whir113keystone.lean#L17) — Residual for append perfect-completeness in the message-first case. The previous theorem body ended

### `restrictedFaaDiBrunoPartitionZeroPowerSum_eq_hasseEvalAtRoot` (2 declarations, 2 files)

- `theorem BCIKS20.HenselNumerator.restrictedFaaDiBrunoPartitionZeroPowerSum_eq_hasseEvalAtRoot` [ArkLib\Data\CodingTheory\ProximityGap\BCIKS20\P2Reabsorb.lean:156](../../../ArkLib\Data\CodingTheory\ProximityGap\BCIKS20\P2Reabsorb.lean#L156) — **Order-zero LHS reabsorption.**  After the order-zero branch collapse in `P2Assembly`, the survivin
- `theorem BCIKS20.HenselNumerator.restrictedFaaDiBrunoPartitionZeroPowerSum_eq_hasseEvalAtRoot` [ArkLib\Data\CodingTheory\ProximityGap\BCIKS20\RestrictedFaaDiBrunoExtract.lean:95](../../../ArkLib\Data\CodingTheory\ProximityGap\BCIKS20\RestrictedFaaDiBrunoExtract.lean#L95) — **Order-zero partition power-sum = cleared root evaluation.**

### `restrictedMatchAt_zero_iff_unclearedHasseCoeff_div_W_natDegree` (2 declarations, 2 files)

- `theorem BCIKS20.HenselNumerator.restrictedMatchAt_zero_iff_unclearedHasseCoeff_div_W_natDegree` [ArkLib\Data\CodingTheory\ProximityGap\BCIKS20\P2Reabsorb.lean:415](../../../ArkLib\Data\CodingTheory\ProximityGap\BCIKS20\P2Reabsorb.lean#L415) — Fixed order-zero P2 is exactly the isolated cleared-vs-uncleared equality under the explicit degree/
- `theorem BCIKS20.HenselNumerator.restrictedMatchAt_zero_iff_unclearedHasseCoeff_div_W_natDegree` [ArkLib\Data\CodingTheory\ProximityGap\BCIKS20\RestrictedFaaDiBrunoExtract.lean:287](../../../ArkLib\Data\CodingTheory\ProximityGap\BCIKS20\RestrictedFaaDiBrunoExtract.lean#L287) — **Order-zero carved P2 core ⟺ the uncleared-Hasse/`W^natDegree` equation (axiom-clean).** This is th

### `restrictedMatchRecursionPartitionFormZeroSingleBCoeff_eq_unclearedHasseCoeff_div_W_natDegree` (2 declarations, 2 files)

- `theorem BCIKS20.HenselNumerator.restrictedMatchRecursionPartitionFormZeroSingleBCoeff_eq_unclearedHasseCoeff_div_W_natDegree` [ArkLib\Data\CodingTheory\ProximityGap\BCIKS20\P2Reabsorb.lean:301](../../../ArkLib\Data\CodingTheory\ProximityGap\BCIKS20\P2Reabsorb.lean#L301) — If `ζ` is nonzero and `R` has degree at least two, the canonical single-`B_coeff` RHS target cancels
- `theorem BCIKS20.HenselNumerator.restrictedMatchRecursionPartitionFormZeroSingleBCoeff_eq_unclearedHasseCoeff_div_W_natDegree` [ArkLib\Data\CodingTheory\ProximityGap\BCIKS20\RestrictedFaaDiBrunoExtract.lean:118](../../../ArkLib\Data\CodingTheory\ProximityGap\BCIKS20\RestrictedFaaDiBrunoExtract.lean#L118) — **Order-zero recursion-side single B-coefficient = uncleared Hasse coeff over `W^natDegree`.**

### `restrictedPartitionMatchAt_zero_iff_unclearedHasseCoeff_div_W_natDegree` (2 declarations, 2 files)

- `theorem BCIKS20.HenselNumerator.restrictedPartitionMatchAt_zero_iff_unclearedHasseCoeff_div_W_natDegree` [ArkLib\Data\CodingTheory\ProximityGap\BCIKS20\P2Reabsorb.lean:456](../../../ArkLib\Data\CodingTheory\ProximityGap\BCIKS20\P2Reabsorb.lean#L456) — The normalized partition order-zero P2 residual is exactly the isolated un-cleared-over-`W ^ R.natDe
- `theorem BCIKS20.HenselNumerator.restrictedPartitionMatchAt_zero_iff_unclearedHasseCoeff_div_W_natDegree` [ArkLib\Data\CodingTheory\ProximityGap\BCIKS20\RestrictedFaaDiBrunoExtract.lean:326](../../../ArkLib\Data\CodingTheory\ProximityGap\BCIKS20\RestrictedFaaDiBrunoExtract.lean#L326) — **Normalized partition order-zero residual ⟺ the uncleared-Hasse/`W^natDegree` equation.** The parti

### `robbins_upper` (2 declarations, 2 files)

- `theorem CodingTheory.ABF26C38.robbins_upper` [ArkLib\Data\CodingTheory\ListDecoding\Bounds.lean:357](../../../ArkLib\Data\CodingTheory\ListDecoding\Bounds.lean#L357) — (no docstring)
- `theorem CodingTheory.ABF26C38.robbins_upper` [ArkLib\Data\CodingTheory\ListDecoding\Bounds\General.lean:228](../../../ArkLib\Data\CodingTheory\ListDecoding\Bounds\General.lean#L228) — (no docstring)

### `rs_lambda_large_prime_ghsz02` (2 declarations, 2 files)

- `def CodingTheory.rs_lambda_large_prime_ghsz02` [ArkLib\Data\CodingTheory\ListDecoding\Bounds.lean:2050](../../../ArkLib\Data\CodingTheory\ListDecoding\Bounds.lean#L2050) — **ABF26 Theorem 3.13 [GHSZ02 Cor 20].** Reed-Solomon large list-size over prime fields. Fix `0 < α,
- `def CodingTheory.rs_lambda_large_prime_ghsz02` [ArkLib\Data\CodingTheory\ListDecoding\Bounds\RandomAndReedSolomon.lean:731](../../../ArkLib\Data\CodingTheory\ListDecoding\Bounds\RandomAndReedSolomon.lean#L731) — **ABF26 Theorem 3.13 [GHSZ02 Cor 20].** Reed-Solomon large list-size over prime fields. Fix `0 < α,

### `rs_lambda_large_prime_ghsz02_of_injection` (2 declarations, 2 files)

- `theorem CodingTheory.rs_lambda_large_prime_ghsz02_of_injection` [ArkLib\Data\CodingTheory\ListDecoding\Bounds.lean:1984](../../../ArkLib\Data\CodingTheory\ListDecoding\Bounds.lean#L1984) — **ABF26 Theorem 3.13 [GHSZ02 Cor 20] — narrowed-residual (injection) form.** A strictly *smaller* re
- `theorem CodingTheory.rs_lambda_large_prime_ghsz02_of_injection` [ArkLib\Data\CodingTheory\ListDecoding\Bounds\RandomAndReedSolomon.lean:665](../../../ArkLib\Data\CodingTheory\ListDecoding\Bounds\RandomAndReedSolomon.lean#L665) — **ABF26 Theorem 3.13 [GHSZ02 Cor 20] — narrowed-residual (injection) form.** A strictly *smaller* re

### `rs_lambda_large_prime_ghsz02_of_residuals` (2 declarations, 2 files)

- `theorem CodingTheory.rs_lambda_large_prime_ghsz02_of_residuals` [ArkLib\Data\CodingTheory\ListDecoding\Bounds.lean:1952](../../../ArkLib\Data\CodingTheory\ListDecoding\Bounds.lean#L1952) — **ABF26 Theorem 3.13 [GHSZ02 Cor 20] — honest reduction form (per-instance).** The *in-tree-provable
- `theorem CodingTheory.rs_lambda_large_prime_ghsz02_of_residuals` [ArkLib\Data\CodingTheory\ListDecoding\Bounds\RandomAndReedSolomon.lean:633](../../../ArkLib\Data\CodingTheory\ListDecoding\Bounds\RandomAndReedSolomon.lean#L633) — **ABF26 Theorem 3.13 [GHSZ02 Cor 20] — honest reduction form (per-instance).** The *in-tree-provable

### `rs_lambda_superpoly_extension_bkr06` (2 declarations, 2 files)

- `def CodingTheory.rs_lambda_superpoly_extension_bkr06` [ArkLib\Data\CodingTheory\ListDecoding\Bounds.lean:1915](../../../ArkLib\Data\CodingTheory\ListDecoding\Bounds.lean#L1915) — **ABF26 Theorem 3.12 [BKR06 Cor 2.2].** Reed-Solomon superpolynomial list-size over extension fields
- `def CodingTheory.rs_lambda_superpoly_extension_bkr06` [ArkLib\Data\CodingTheory\ListDecoding\Bounds\RandomAndReedSolomon.lean:596](../../../ArkLib\Data\CodingTheory\ListDecoding\Bounds\RandomAndReedSolomon.lean#L596) — **ABF26 Theorem 3.12 [BKR06 Cor 2.2].** Reed-Solomon superpolynomial list-size over extension fields

### `rs_lambda_superpoly_extension_bkr06_of_family` (2 declarations, 2 files)

- `theorem CodingTheory.rs_lambda_superpoly_extension_bkr06_of_family` [ArkLib\Data\CodingTheory\ListDecoding\Bounds.lean:1846](../../../ArkLib\Data\CodingTheory\ListDecoding\Bounds.lean#L1846) — **ABF26 Theorem 3.12 [BKR06 Cor 2.2] — corrected extension/family reduction form.** The genuine, dis
- `theorem CodingTheory.rs_lambda_superpoly_extension_bkr06_of_family` [ArkLib\Data\CodingTheory\ListDecoding\Bounds\RandomAndReedSolomon.lean:527](../../../ArkLib\Data\CodingTheory\ListDecoding\Bounds\RandomAndReedSolomon.lean#L527) — **ABF26 Theorem 3.12 [BKR06 Cor 2.2] — corrected extension/family reduction form.** The genuine, dis

### `rs_lambda_superpoly_extension_bkr06_of_injection` (2 declarations, 2 files)

- `theorem CodingTheory.rs_lambda_superpoly_extension_bkr06_of_injection` [ArkLib\Data\CodingTheory\ListDecoding\Bounds.lean:1765](../../../ArkLib\Data\CodingTheory\ListDecoding\Bounds.lean#L1765) — **ABF26 Theorem 3.12 [BKR06 Cor 2.2] — narrowed-residual form (fiber-count consuming).** A strictly
- `theorem CodingTheory.rs_lambda_superpoly_extension_bkr06_of_injection` [ArkLib\Data\CodingTheory\ListDecoding\Bounds\RandomAndReedSolomon.lean:446](../../../ArkLib\Data\CodingTheory\ListDecoding\Bounds\RandomAndReedSolomon.lean#L446) — **ABF26 Theorem 3.12 [BKR06 Cor 2.2] — narrowed-residual form (fiber-count consuming).** A strictly

### `rs_lambda_superpoly_extension_bkr06_of_residuals` (2 declarations, 2 files)

- `theorem CodingTheory.rs_lambda_superpoly_extension_bkr06_of_residuals` [ArkLib\Data\CodingTheory\ListDecoding\Bounds.lean:1711](../../../ArkLib\Data\CodingTheory\ListDecoding\Bounds.lean#L1711) — **ABF26 Theorem 3.12 [BKR06 Cor 2.2] — honest reduction form (per-instance).** The *in-tree-provable
- `theorem CodingTheory.rs_lambda_superpoly_extension_bkr06_of_residuals` [ArkLib\Data\CodingTheory\ListDecoding\Bounds\RandomAndReedSolomon.lean:392](../../../ArkLib\Data\CodingTheory\ListDecoding\Bounds\RandomAndReedSolomon.lean#L392) — **ABF26 Theorem 3.12 [BKR06 Cor 2.2] — honest reduction form (per-instance).** The *in-tree-provable

### `sqrtpi_exp_le_two` (2 declarations, 2 files)

- `theorem CodingTheory.ABF26C38.sqrtpi_exp_le_two` [ArkLib\Data\CodingTheory\ListDecoding\Bounds.lean:436](../../../ArkLib\Data\CodingTheory\ListDecoding\Bounds.lean#L436) — (no docstring)
- `theorem CodingTheory.ABF26C38.sqrtpi_exp_le_two` [ArkLib\Data\CodingTheory\ListDecoding\Bounds\General.lean:307](../../../ArkLib\Data\CodingTheory\ListDecoding\Bounds\General.lean#L307) — (no docstring)

### `ss2_eq` (2 declarations, 2 files)

- `theorem CodingTheory.ABF26C38.ss2_eq` [ArkLib\Data\CodingTheory\ListDecoding\Bounds.lean:418](../../../ArkLib\Data\CodingTheory\ListDecoding\Bounds.lean#L418) — (no docstring)
- `theorem CodingTheory.ABF26C38.ss2_eq` [ArkLib\Data\CodingTheory\ListDecoding\Bounds\General.lean:289](../../../ArkLib\Data\CodingTheory\ListDecoding\Bounds\General.lean#L289) — (no docstring)

### `ss3_eq` (2 declarations, 2 files)

- `theorem CodingTheory.ABF26C38.ss3_eq` [ArkLib\Data\CodingTheory\ListDecoding\Bounds.lean:427](../../../ArkLib\Data\CodingTheory\ListDecoding\Bounds.lean#L427) — (no docstring)
- `theorem CodingTheory.ABF26C38.ss3_eq` [ArkLib\Data\CodingTheory\ListDecoding\Bounds\General.lean:298](../../../ArkLib\Data\CodingTheory\ListDecoding\Bounds\General.lean#L298) — (no docstring)

### `st20_attach_fiber_ge` (2 declarations, 2 files)

- `theorem CodingTheory.st20_attach_fiber_ge` [ArkLib\Data\CodingTheory\ListDecoding\Bounds.lean:1072](../../../ArkLib\Data\CodingTheory\ListDecoding\Bounds.lean#L1072) — (no docstring)
- `theorem CodingTheory.st20_attach_fiber_ge` [ArkLib\Data\CodingTheory\ListDecoding\Bounds\General.lean:943](../../../ArkLib\Data\CodingTheory\ListDecoding\Bounds\General.lean#L943) — (no docstring)

### `st20_dist_bound` (2 declarations, 2 files)

- `theorem CodingTheory.st20_dist_bound` [ArkLib\Data\CodingTheory\ListDecoding\Bounds.lean:1160](../../../ArkLib\Data\CodingTheory\ListDecoding\Bounds.lean#L1160) — (no docstring)
- `theorem CodingTheory.st20_dist_bound` [ArkLib\Data\CodingTheory\ListDecoding\Bounds\General.lean:1031](../../../ArkLib\Data\CodingTheory\ListDecoding\Bounds\General.lean#L1031) — (no docstring)

### `st20_kernel_extract` (2 declarations, 2 files)

- `theorem CodingTheory.st20_kernel_extract` [ArkLib\Data\CodingTheory\ListDecoding\Bounds.lean:1118](../../../ArkLib\Data\CodingTheory\ListDecoding\Bounds.lean#L1118) — (no docstring)
- `theorem CodingTheory.st20_kernel_extract` [ArkLib\Data\CodingTheory\ListDecoding\Bounds\General.lean:989](../../../ArkLib\Data\CodingTheory\ListDecoding\Bounds\General.lean#L989) — (no docstring)

### `st20_nat_ineq` (2 declarations, 2 files)

- `theorem CodingTheory.st20_nat_ineq` [ArkLib\Data\CodingTheory\ListDecoding\Bounds.lean:1100](../../../ArkLib\Data\CodingTheory\ListDecoding\Bounds.lean#L1100) — (no docstring)
- `theorem CodingTheory.st20_nat_ineq` [ArkLib\Data\CodingTheory\ListDecoding\Bounds\General.lean:971](../../../ArkLib\Data\CodingTheory\ListDecoding\Bounds\General.lean#L971) — (no docstring)

### `st20_ncard_eq` (2 declarations, 2 files)

- `theorem CodingTheory.st20_ncard_eq` [ArkLib\Data\CodingTheory\ListDecoding\Bounds.lean:1210](../../../ArkLib\Data\CodingTheory\ListDecoding\Bounds.lean#L1210) — (no docstring)
- `theorem CodingTheory.st20_ncard_eq` [ArkLib\Data\CodingTheory\ListDecoding\Bounds\General.lean:1081](../../../ArkLib\Data\CodingTheory\ListDecoding\Bounds\General.lean#L1081) — (no docstring)

### `st20_range_fiber_ge` (2 declarations, 2 files)

- `theorem CodingTheory.st20_range_fiber_ge` [ArkLib\Data\CodingTheory\ListDecoding\Bounds.lean:1046](../../../ArkLib\Data\CodingTheory\ListDecoding\Bounds.lean#L1046) — (no docstring)
- `theorem CodingTheory.st20_range_fiber_ge` [ArkLib\Data\CodingTheory\ListDecoding\Bounds\General.lean:917](../../../ArkLib\Data\CodingTheory\ListDecoding\Bounds\General.lean#L917) — (no docstring)

### `subspaceDesign_list_decoding_cz25` (2 declarations, 2 files)

- `theorem CodingTheory.subspaceDesign_list_decoding_cz25` [ArkLib\Data\CodingTheory\ListDecoding\Bounds.lean:2109](../../../ArkLib\Data\CodingTheory\ListDecoding\Bounds.lean#L2109) — **ABF26 Theorem 3.4 [CZ25 Theorem B.5].** τ-subspace-design codes are list-decodable up to capacity,
- `theorem CodingTheory.subspaceDesign_list_decoding_cz25` [ArkLib\Data\CodingTheory\ListDecoding\Bounds\SubspaceDesign.lean:37](../../../ArkLib\Data\CodingTheory\ListDecoding\Bounds\SubspaceDesign.lean#L37) — **ABF26 Theorem 3.4 [CZ25 Theorem B.5].** τ-subspace-design codes are list-decodable up to capacity,

### `sudan_list_bound` (2 declarations, 2 files)

- `theorem R15.sudan_list_bound` [ArkLib\Data\CodingTheory\ProximityGap\SudanListBound.lean:335](../../../ArkLib\Data\CodingTheory\ProximityGap\SudanListBound.lean#L335) — **End-to-end Sudan (multiplicity-1) list bound.**  Let `F` be a field, `α : Fin n → F` injective eva
- `theorem R15.sudan_list_bound` [ArkLib\Data\CodingTheory\ProximityGap\SudanListBoundFull.lean:335](../../../ArkLib\Data\CodingTheory\ProximityGap\SudanListBoundFull.lean#L335) — **End-to-end Sudan (multiplicity-1) list bound.**  Let `F` be a field, `α : Fin n → F` injective eva

### `sudan_list_bound_ZMod13` (2 declarations, 2 files)

- `theorem R15.sudan_list_bound_ZMod13` [ArkLib\Data\CodingTheory\ProximityGap\SudanListBound.lean:402](../../../ArkLib\Data\CodingTheory\ProximityGap\SudanListBound.lean#L402) — **Concrete Sudan instance.** Over `ZMod 13` with the 12 evaluation points `0,…,11`: any list of poly
- `theorem R15.sudan_list_bound_ZMod13` [ArkLib\Data\CodingTheory\ProximityGap\SudanListBoundFull.lean:402](../../../ArkLib\Data\CodingTheory\ProximityGap\SudanListBoundFull.lean#L402) — **Concrete Sudan instance.** Over `ZMod 13` with the 12 evaluation points `0,…,11`: any list of poly

### `sudan_list_bound_filter` (2 declarations, 2 files)

- `theorem R15.sudan_list_bound_filter` [ArkLib\Data\CodingTheory\ProximityGap\SudanListBound.lean:371](../../../ArkLib\Data\CodingTheory\ProximityGap\SudanListBound.lean#L371) — Filter form (when `F` has decidable equality): the agreement hypothesis stated as a cardinality of `
- `theorem R15.sudan_list_bound_filter` [ArkLib\Data\CodingTheory\ProximityGap\SudanListBoundFull.lean:371](../../../ArkLib\Data\CodingTheory\ProximityGap\SudanListBoundFull.lean#L371) — Filter form (when `F` has decidable equality): the agreement hypothesis stated as a cardinality of `

### `sum_map_two_mul_sub_one` (2 declarations, 2 files)

- `lemma BCIKS20.HenselNumerator.sum_map_two_mul_sub_one` [ArkLib\Data\CodingTheory\ProximityGap\BCIKS20\P2KeystoneReindex.lean:183](../../../ArkLib\Data\CodingTheory\ProximityGap\BCIKS20\P2KeystoneReindex.lean#L183) — Auxiliary: `∑_{l ∈ λ} (2 l - 1) = 2 c - (number of parts)` (truncated ℕ subtraction). The per-part s
- `theorem BCIKS20.HenselNumerator.sum_map_two_mul_sub_one` [ArkLib\Data\CodingTheory\ProximityGap\BCIKS20\RestrictedFaaDiBrunoXiTelescope.lean:94](../../../ArkLib\Data\CodingTheory\ProximityGap\BCIKS20\RestrictedFaaDiBrunoXiTelescope.lean#L94) — **The LHS `ξ`-denominator exponent of a partition (axiom-clean).** The assembled-series coefficient

### `support_uniformRandomLinearGeneratorMatrix` (2 declarations, 2 files)

- `theorem CodingTheory.support_uniformRandomLinearGeneratorMatrix` [ArkLib\Data\CodingTheory\ListDecoding\Bounds.lean:1410](../../../ArkLib\Data\CodingTheory\ListDecoding\Bounds.lean#L1410) — (no docstring)
- `theorem CodingTheory.support_uniformRandomLinearGeneratorMatrix` [ArkLib\Data\CodingTheory\ListDecoding\Bounds\RandomAndReedSolomon.lean:91](../../../ArkLib\Data\CodingTheory\ListDecoding\Bounds\RandomAndReedSolomon.lean#L91) — (no docstring)

### `threshold_lt_pow_div` (2 declarations, 2 files)

- `theorem CodingTheory.threshold_lt_pow_div` [ArkLib\Data\CodingTheory\ProximityGap\ListDecodingCapacityOverflow.lean:40](../../../ArkLib\Data\CodingTheory\ProximityGap\ListDecodingCapacityOverflow.lean#L40) — **`rpow` overflow bridge.** For `q > 1`, `0 < n1`, `0 < εq`, if `logb q (n1·εq) < E` then `εq < q^E
- `theorem CodingTheory.threshold_lt_pow_div` [ArkLib\Data\CodingTheory\ProximityGap\UpToCapacityListDecodingFalse.lean:45](../../../ArkLib\Data\CodingTheory\ProximityGap\UpToCapacityListDecodingFalse.lean#L45) — **`rpow` overflow bridge.** For `q > 1`, `0 < n1`, `0 < εq`, `logb q (n1·εq) < E → εq < q^E/n1`.

### `totalDegree_ehQ_le` (2 declarations, 2 files)

- `lemma MvPolynomial.totalDegree_ehQ_le` [ArkLib\ToMathlib\RestrictedSumset.lean:265](../../../ArkLib\ToMathlib\RestrictedSumset.lean#L265) — `ehQ Cset` has total degree at most `\|Cset\| + 1`.
- `lemma MvPolynomial.totalDegree_ehQ_le` [ArkLib\ToMathlib\RestrictedSumsetGeneral.lean:316](../../../ArkLib\ToMathlib\RestrictedSumsetGeneral.lean#L316) — `ehQ h Cset` has total degree at most `deg(vdmX) + \|Cset\|`.

### `totalDegree_prod_sub_pow_le` (2 declarations, 2 files)

- `lemma MvPolynomial.totalDegree_prod_sub_pow_le` [ArkLib\ToMathlib\RestrictedSumset.lean:183](../../../ArkLib\ToMathlib\RestrictedSumset.lean#L183) — **Leading-part difference bound.** The product `∏_{c ∈ s} (y - C c)` differs from `y^{\|s\|}` by a pol
- `lemma MvPolynomial.totalDegree_prod_sub_pow_le` [ArkLib\ToMathlib\RestrictedSumsetGeneral.lean:195](../../../ArkLib\ToMathlib\RestrictedSumsetGeneral.lean#L195) — **Leading-part difference bound.** The product `∏_{c ∈ s} (y - C c)` differs from `y^{\|s\|}` by a pol

### `two_element_list_witness` (2 declarations, 2 files)

- `theorem R15.two_element_list_witness` [ArkLib\Data\CodingTheory\ProximityGap\SudanListBound.lean:425](../../../ArkLib\Data\CodingTheory\ProximityGap\SudanListBound.lean#L425) — **Non-vacuity / genuine list regime.**  For the explicit received word `wWit` over `ZMod 13`, the ex
- `theorem R15.two_element_list_witness` [ArkLib\Data\CodingTheory\ProximityGap\SudanListBoundFull.lean:425](../../../ArkLib\Data\CodingTheory\ProximityGap\SudanListBoundFull.lean#L425) — **Non-vacuity / genuine list regime.**  For the explicit received word `wWit` over `ZMod 13`, the ex

### `uniformRandomLinearCode` (2 declarations, 2 files)

- `def CodingTheory.uniformRandomLinearCode` [ArkLib\Data\CodingTheory\ListDecoding\Bounds.lean:1431](../../../ArkLib\Data\CodingTheory\ListDecoding\Bounds.lean#L1431) — The pushforward distribution on linear codes induced by uniform generator matrices.
- `def CodingTheory.uniformRandomLinearCode` [ArkLib\Data\CodingTheory\ListDecoding\Bounds\RandomAndReedSolomon.lean:112](../../../ArkLib\Data\CodingTheory\ListDecoding\Bounds\RandomAndReedSolomon.lean#L112) — The pushforward distribution on linear codes induced by uniform generator matrices.

### `uniformRandomLinearGeneratorMatrix` (2 declarations, 2 files)

- `def CodingTheory.uniformRandomLinearGeneratorMatrix` [ArkLib\Data\CodingTheory\ListDecoding\Bounds.lean:1397](../../../ArkLib\Data\CodingTheory\ListDecoding\Bounds.lean#L1397) — Uniform sampling of `k × \|ι\|` generator matrices over a finite alphabet.
- `def CodingTheory.uniformRandomLinearGeneratorMatrix` [ArkLib\Data\CodingTheory\ListDecoding\Bounds\RandomAndReedSolomon.lean:78](../../../ArkLib\Data\CodingTheory\ListDecoding\Bounds\RandomAndReedSolomon.lean#L78) — Uniform sampling of `k × \|ι\|` generator matrices over a finite alphabet.

### `wWit` (2 declarations, 2 files)

- `def R15.wWit` [ArkLib\Data\CodingTheory\ProximityGap\SudanListBound.lean:418](../../../ArkLib\Data\CodingTheory\ProximityGap\SudanListBound.lean#L418) — Explicit received word: agrees with `X` on indices `0,…,5` and with `0` on `6,…,11` (and on `0`).
- `def R15.wWit` [ArkLib\Data\CodingTheory\ProximityGap\SudanListBoundFull.lean:418](../../../ArkLib\Data\CodingTheory\ProximityGap\SudanListBoundFull.lean#L418) — Explicit received word: agrees with `X` on indices `0,…,5` and with `0` on `6,…,11` (and on `0`).

### `w_in_C` (2 declarations, 2 files)

- `lemma w_in_C` [ArkLib\Data\CodingTheory\ProximityGap\PromotedHypothesesB.lean:52](../../../ArkLib\Data\CodingTheory\ProximityGap\PromotedHypothesesB.lean#L52) — (no docstring)
- `lemma w_in_C` [ArkLib\Data\CodingTheory\Quarantine\CandidateHypothesesRefutations.lean:35](../../../ArkLib\Data\CodingTheory\Quarantine\CandidateHypothesesRefutations.lean#L35) — (no docstring)

### `weight` (2 declarations, 2 files)

- `def weight` [ArkLib\Data\CodingTheory\ProximityGap\PromotedHypothesesB.lean:58](../../../ArkLib\Data\CodingTheory\ProximityGap\PromotedHypothesesB.lean#L58) — (no docstring)
- `def weight` [ArkLib\Data\CodingTheory\Quarantine\CandidateHypotheses.lean:19](../../../ArkLib\Data\CodingTheory\Quarantine\CandidateHypotheses.lean#L19) — (no docstring)

### `whose` (2 declarations, 2 files)

- `instance whose` [ArkLib\Data\CodingTheory\JohnsonBound\FamilyRefutationComplete.lean:19](../../../ArkLib\Data\CodingTheory\JohnsonBound\FamilyRefutationComplete.lean#L19) — (no docstring)
- `theorem whose` [ArkLib\Data\CodingTheory\ProximityGap\BatchedFRIProof.lean:18](../../../ArkLib\Data\CodingTheory\ProximityGap\BatchedFRIProof.lean#L18) — (no docstring)

### `with` (2 declarations, 2 files)

- `instance with` [ArkLib\Data\CodingTheory\ProximityGap\GrandChallengeLDAttainment.lean:32](../../../ArkLib\Data\CodingTheory\ProximityGap\GrandChallengeLDAttainment.lean#L32) — (no docstring)
- `theorem with` [ArkLib\Data\CodingTheory\ProximityGap\PermanentlyBlocked.lean:55](../../../ArkLib\Data\CodingTheory\ProximityGap\PermanentlyBlocked.lean#L55) — (no docstring)

## Near-duplicate docstrings (Jaccard ≥ 0.85, 120 cross-file pairs)

Each pair has docstrings sharing a high fraction of (4+-letter) words, in different files. Most are unrelated coincidences in boilerplate; look for pairs where the *concept* matches.

- **1.00** `ArkLib.CS25.code_covered_count_johnson_radius_entropy` [ArkLib\Data\CodingTheory\ProximityGap\CS25CodeCoveredFractionJohnsonEntropy.lean:66](../../../ArkLib\Data\CodingTheory\ProximityGap\CS25CodeCoveredFractionJohnsonEntropy.lean#L66) vs `ArkLib.CS25.rs_covered_count_johnson_radius_entropy` [ArkLib\Data\CodingTheory\ProximityGap\CS25RSCoveredFractionJohnsonEntropy.lean:66](../../../ArkLib\Data\CodingTheory\ProximityGap\CS25RSCoveredFractionJohnsonEntropy.lean#L66)
    - a: **Existential entropy-form covered fraction up to the Johnson radius (#232).**  The qualitative John
    - b: **Existential entropy-form RS covered fraction up to the Johnson radius (#232).** The qualitative RS
- **1.00** `ArkLib.CS25.code_covered_count_johnson_radius_sqrt_entropy` [ArkLib\Data\CodingTheory\ProximityGap\CS25CodeCoveredFractionJohnsonEntropy.lean:89](../../../ArkLib\Data\CodingTheory\ProximityGap\CS25CodeCoveredFractionJohnsonEntropy.lean#L89) vs `ArkLib.CS25.rs_covered_count_johnson_radius_sqrt_entropy` [ArkLib\Data\CodingTheory\ProximityGap\CS25RSCoveredFractionJohnsonEntropy.lean:91](../../../ArkLib\Data\CodingTheory\ProximityGap\CS25RSCoveredFractionJohnsonEntropy.lean#L91)
    - a: **Entropy covered fraction from the explicit sqrt-form Johnson radius (#232).**  The textbook `√(T·B
    - b: **Entropy RS covered fraction from the explicit sqrt-form Johnson radius (#232).**  The textbook `√(
- **1.00** `ArkLib.CodingTheory.CapacityLowerSharpen.agreeCount` [ArkLib\Data\CodingTheory\ProximityGap\ListCapacityFieldIndependent.lean:185](../../../ArkLib\Data\CodingTheory\ProximityGap\ListCapacityFieldIndependent.lean#L185) vs `ArkLib.CodingTheory.Round4InteriorList.agreeCount` [ArkLib\Data\CodingTheory\ProximityGap\InteriorListCountBridge.lean:199](../../../ArkLib\Data\CodingTheory\ProximityGap\InteriorListCountBridge.lean#L199)
    - a: The agreement count (number of coordinates where two words coincide).
    - b: The agreement count (number of coordinates where two words coincide).
- **1.00** `ArkLib.CodingTheory.CapacityLowerSharpen.pS_eval_eq_on_S` [ArkLib\Data\CodingTheory\ProximityGap\ListCapacityFieldIndependent.lean:82](../../../ArkLib\Data\CodingTheory\ProximityGap\ListCapacityFieldIndependent.lean#L82) vs `ArkLib.CodingTheory.Round4InteriorList.pSt_eval_eq_on_S` [ArkLib\Data\CodingTheory\ProximityGap\InteriorListCountBridge.lean:89](../../../ArkLib\Data\CodingTheory\ProximityGap\InteriorListCountBridge.lean#L89)
    - a: `p_S` agrees with `g` (the received word) on every coordinate of `S`: the product vanishes on `S`, s
    - b: `p_S` agrees with `g` (the received word) on every coordinate of `S`: the product vanishes on `S`, s
- **1.00** `ArkLib.CodingTheory.CapacityLowerSharpen.prod_X_sub_C_injOn_subsets` [ArkLib\Data\CodingTheory\ProximityGap\ListCapacityFieldIndependent.lean:128](../../../ArkLib\Data\CodingTheory\ProximityGap\ListCapacityFieldIndependent.lean#L128) vs `ArkLib.CodingTheory.Round4InteriorList.prod_X_sub_C_injOn_subsets` [ArkLib\Data\CodingTheory\ProximityGap\InteriorListCountBridge.lean:128](../../../ArkLib\Data\CodingTheory\ProximityGap\InteriorListCountBridge.lean#L128)
    - a: The two root products are equal as polynomials iff the subsets are equal (`D` injective).
    - b: The two root products are equal as polynomials iff the subsets are equal (`D` injective).
- **1.00** `ArkLib.CodingTheory.TinyInteriorF11.DD` [ArkLib\Data\CodingTheory\ProximityGap\ListInteriorPinF11.lean:61](../../../ArkLib\Data\CodingTheory\ProximityGap\ListInteriorPinF11.lean#L61) vs `ArkLib.CodingTheory.TinyInteriorK3.D` [ArkLib\Data\CodingTheory\ProximityGap\ListInteriorPinF11K3.lean:84](../../../ArkLib\Data\CodingTheory\ProximityGap\ListInteriorPinF11K3.lean#L84)
    - a: The evaluation domain: all eleven points of `F₁₁`, indexed by `Fin 11` via `DD i = i`.
    - b: The evaluation domain: all eleven points of `F₁₁`, indexed by `Fin 11` via `D i = i`.
- **1.00** `ArkLib.CodingTheory.TinyInteriorF11.L11_subset_code` [ArkLib\Data\CodingTheory\ProximityGap\ListInteriorPinF11.lean:187](../../../ArkLib\Data\CodingTheory\ProximityGap\ListInteriorPinF11.lean#L187) vs `ArkLib.CodingTheory.TinyInteriorPin.L_subset_code` [ArkLib\Data\CodingTheory\ProximityGap\ListInteriorDataPointF7.lean:127](../../../ArkLib\Data\CodingTheory\ProximityGap\ListInteriorDataPointF7.lean#L127)
    - a: **Every element of `L₁₁` is a Reed–Solomon codeword of degree `< 2`.** This is the non-vacuity witne
    - b: **Every element of `L` is a Reed–Solomon codeword of degree `< 2`.** This is the non-vacuity witness
- **1.00** `ArkLib.CodingTheory.TinyInteriorK3.fact_prime_eleven` [ArkLib\Data\CodingTheory\ProximityGap\ListInteriorPinF11K3.lean:81](../../../ArkLib\Data\CodingTheory\ProximityGap\ListInteriorPinF11K3.lean#L81) vs `ArkLib.CodingTheory.TinyInteriorPin.fact_prime_seven` [ArkLib\Data\CodingTheory\ProximityGap\ListInteriorDataPointF7.lean:65](../../../ArkLib\Data\CodingTheory\ProximityGap\ListInteriorDataPointF7.lean#L65)
    - a: `11` is prime, so `ZMod 11` is a field. This is what makes `RS[F₁₁, F₁₁, 3]` a genuine Reed–Solomon
    - b: `7` is prime, so `ZMod 7` is a field. This is what makes `RS[F₇, F₇, 2]` a genuine Reed–Solomon code
- **1.00** `ArkLib.CodingTheory.TinyInteriorK3.six_elevenths_strictly_interior` [ArkLib\Data\CodingTheory\ProximityGap\ListInteriorPinF11K3.lean:256](../../../ArkLib\Data\CodingTheory\ProximityGap\ListInteriorPinF11K3.lean#L256) vs `ArkLib.CodingTheory.TinyInteriorPin.four_sevenths_strictly_interior` [ArkLib\Data\CodingTheory\ProximityGap\ListInteriorDataPointF7.lean:215](../../../ArkLib\Data\CodingTheory\ProximityGap\ListInteriorDataPointF7.lean#L215)
    - a: **Gap placement.** The relative radius `δ = 6/11` (agreement `a = 5` out of `n = 11`) is strictly be
    - b: **Gap placement.** The relative radius `δ = 4/7` (agreement `a = 3` out of `n = 7`) is strictly betw
- **1.00** `Binius.BinaryBasefold.FullBinaryBasefold.fullOracleProof` [ArkLib\ProofSystem\Binius\BinaryBasefold\General.lean:102](../../../ArkLib\ProofSystem\Binius\BinaryBasefold\General.lean#L102) vs `Binius.FRIBinius.FullFRIBinius.fullOracleProof` [ArkLib\ProofSystem\Binius\FRIBinius\General.lean:171](../../../ArkLib\ProofSystem\Binius\FRIBinius\General.lean#L171)
    - a: The full Binary Basefold protocol as a Proof
    - b: The full Binary Basefold protocol as a Proof
- **1.00** `Binius.BinaryBasefold.FullBinaryBasefold.fullOracleProof` [ArkLib\ProofSystem\Binius\BinaryBasefold\General.lean:102](../../../ArkLib\ProofSystem\Binius\BinaryBasefold\General.lean#L102) vs `RingSwitching.FullRingSwitching.fullOracleProof` [ArkLib\ProofSystem\RingSwitching\General.lean:96](../../../ArkLib\ProofSystem\RingSwitching\General.lean#L96)
    - a: The full Binary Basefold protocol as a Proof
    - b: The full Binary Basefold protocol as a Proof
- **1.00** `Binius.BinaryBasefold.FullBinaryBasefold.fullOracleReduction` [ArkLib\ProofSystem\Binius\BinaryBasefold\General.lean:74](../../../ArkLib\ProofSystem\Binius\BinaryBasefold\General.lean#L74) vs `Binius.FRIBinius.FullFRIBinius.fullOracleReduction` [ArkLib\ProofSystem\Binius\FRIBinius\General.lean:140](../../../ArkLib\ProofSystem\Binius\FRIBinius\General.lean#L140)
    - a: The reduction for the full Binary Basefold protocol
    - b: The reduction for the full Binary Basefold protocol
- **1.00** `Binius.BinaryBasefold.FullBinaryBasefold.fullOracleReduction` [ArkLib\ProofSystem\Binius\BinaryBasefold\General.lean:74](../../../ArkLib\ProofSystem\Binius\BinaryBasefold\General.lean#L74) vs `RingSwitching.FullRingSwitching.fullOracleReduction` [ArkLib\ProofSystem\RingSwitching\General.lean:84](../../../ArkLib\ProofSystem\RingSwitching\General.lean#L84)
    - a: The reduction for the full Binary Basefold protocol
    - b: The reduction for the full Binary Basefold protocol
- **1.00** `Binius.BinaryBasefold.FullBinaryBasefold.fullOracleReduction_perfectCompleteness` [ArkLib\ProofSystem\Binius\BinaryBasefold\General.lean:117](../../../ArkLib\ProofSystem\Binius\BinaryBasefold\General.lean#L117) vs `Binius.FRIBinius.FullFRIBinius.fullOracleReduction_perfectCompleteness` [ArkLib\ProofSystem\Binius\FRIBinius\General.lean:191](../../../ArkLib\ProofSystem\Binius\FRIBinius\General.lean#L191)
    - a: Perfect completeness for the full Binary Basefold protocol (reduction)
    - b: Perfect completeness for the full Binary Basefold protocol (reduction)
- **1.00** `Binius.BinaryBasefold.FullBinaryBasefold.fullOracleVerifier` [ArkLib\ProofSystem\Binius\BinaryBasefold\General.lean:51](../../../ArkLib\ProofSystem\Binius\BinaryBasefold\General.lean#L51) vs `Binius.FRIBinius.FullFRIBinius.fullOracleVerifier` [ArkLib\ProofSystem\Binius\FRIBinius\General.lean:114](../../../ArkLib\ProofSystem\Binius\FRIBinius\General.lean#L114)
    - a: The oracle verifier for the full Binary Basefold protocol
    - b: The oracle verifier for the full Binary Basefold protocol
- **1.00** `Binius.BinaryBasefold.FullBinaryBasefold.fullOracleVerifier` [ArkLib\ProofSystem\Binius\BinaryBasefold\General.lean:51](../../../ArkLib\ProofSystem\Binius\BinaryBasefold\General.lean#L51) vs `RingSwitching.FullRingSwitching.fullOracleVerifier` [ArkLib\ProofSystem\RingSwitching\General.lean:60](../../../ArkLib\ProofSystem\RingSwitching\General.lean#L60)
    - a: The oracle verifier for the full Binary Basefold protocol
    - b: The oracle verifier for the full Binary Basefold protocol
- **1.00** `Binius.BinaryBasefold.witnessStructuralInvariant` [ArkLib\ProofSystem\Binius\BinaryBasefold\Basic.lean:1154](../../../ArkLib\ProofSystem\Binius\BinaryBasefold\Basic.lean#L1154) vs `RingSwitching.witnessStructuralInvariant` [ArkLib\ProofSystem\RingSwitching\Prelude.lean:452](../../../ArkLib\ProofSystem\RingSwitching\Prelude.lean#L452)
    - a: This condition ensures that the witness polynomial `H` has the correct structure `eq(...) * t(...)`
    - b: This condition ensures that the witness polynomial `H` has the correct structure `A(...) * t'(...)`
- **1.00** `Binius.FRIBinius.CoreInteractionPhase.finalSumcheckKnowledgeError` [ArkLib\ProofSystem\Binius\FRIBinius\CoreInteractionPhase.lean:1308](../../../ArkLib\ProofSystem\Binius\FRIBinius\CoreInteractionPhase.lean#L1308) vs `RingSwitching.SumcheckPhase.finalSumcheckRbrKnowledgeError` [ArkLib\ProofSystem\RingSwitching\SumcheckPhase.lean:1512](../../../ArkLib\ProofSystem\RingSwitching\SumcheckPhase.lean#L1512)
    - a: RBR knowledge error for the final sumcheck step
    - b: RBR knowledge error for the final sumcheck step
- **1.00** `Binius.FRIBinius.CoreInteractionPhase.finalSumcheckOracleReduction` [ArkLib\ProofSystem\Binius\FRIBinius\CoreInteractionPhase.lean:667](../../../ArkLib\ProofSystem\Binius\FRIBinius\CoreInteractionPhase.lean#L667) vs `RingSwitching.SumcheckPhase.finalSumcheckOracleReduction` [ArkLib\ProofSystem\RingSwitching\SumcheckPhase.lean:1306](../../../ArkLib\ProofSystem\RingSwitching\SumcheckPhase.lean#L1306)
    - a: The oracle reduction for the final sumcheck step
    - b: The oracle reduction for the final sumcheck step
- **1.00** `Binius.FRIBinius.CoreInteractionPhase.finalSumcheckRbrExtractor` [ArkLib\ProofSystem\Binius\FRIBinius\CoreInteractionPhase.lean:1319](../../../ArkLib\ProofSystem\Binius\FRIBinius\CoreInteractionPhase.lean#L1319) vs `RingSwitching.SumcheckPhase.finalSumcheckRbrExtractor` [ArkLib\ProofSystem\RingSwitching\SumcheckPhase.lean:1515](../../../ArkLib\ProofSystem\RingSwitching\SumcheckPhase.lean#L1515)
    - a: The round-by-round extractor for the final sumcheck step
    - b: The round-by-round extractor for the final sumcheck step
- **1.00** `Binius.FRIBinius.FullFRIBinius.fullOracleProof` [ArkLib\ProofSystem\Binius\FRIBinius\General.lean:171](../../../ArkLib\ProofSystem\Binius\FRIBinius\General.lean#L171) vs `RingSwitching.FullRingSwitching.fullOracleProof` [ArkLib\ProofSystem\RingSwitching\General.lean:96](../../../ArkLib\ProofSystem\RingSwitching\General.lean#L96)
    - a: The full Binary Basefold protocol as a Proof
    - b: The full Binary Basefold protocol as a Proof
- **1.00** `Binius.FRIBinius.FullFRIBinius.fullOracleReduction` [ArkLib\ProofSystem\Binius\FRIBinius\General.lean:140](../../../ArkLib\ProofSystem\Binius\FRIBinius\General.lean#L140) vs `RingSwitching.FullRingSwitching.fullOracleReduction` [ArkLib\ProofSystem\RingSwitching\General.lean:84](../../../ArkLib\ProofSystem\RingSwitching\General.lean#L84)
    - a: The reduction for the full Binary Basefold protocol
    - b: The reduction for the full Binary Basefold protocol
- **1.00** `Binius.FRIBinius.FullFRIBinius.fullOracleVerifier` [ArkLib\ProofSystem\Binius\FRIBinius\General.lean:114](../../../ArkLib\ProofSystem\Binius\FRIBinius\General.lean#L114) vs `RingSwitching.FullRingSwitching.fullOracleVerifier` [ArkLib\ProofSystem\RingSwitching\General.lean:60](../../../ArkLib\ProofSystem\RingSwitching\General.lean#L60)
    - a: The oracle verifier for the full Binary Basefold protocol
    - b: The oracle verifier for the full Binary Basefold protocol
- **1.00** `CodingTheory.span_inf_ker_proj_of_eq_zero` [ArkLib\Data\CodingTheory\SubspaceDesign.lean:115](../../../ArkLib\Data\CodingTheory\SubspaceDesign.lean#L115) vs `CodingTheory.um_span_inf_ker_proj_of_eq_zero` [ArkLib\ToMathlib\UMSubspaceDesignProof.lean:263](../../../ArkLib\ToMathlib\UMSubspaceDesignProof.lean#L263)
    - a: The 1-dimensional subspace `span{a}` meets `ker(proj i)` in itself when `a i = 0`.
    - b: The 1-dimensional subspace `span{a}` meets `ker(proj i)` in itself when `a i = 0`.
- **1.00** `CodingTheory.span_inf_ker_proj_of_ne_zero` [ArkLib\Data\CodingTheory\SubspaceDesign.lean:124](../../../ArkLib\Data\CodingTheory\SubspaceDesign.lean#L124) vs `CodingTheory.um_span_inf_ker_proj_of_ne_zero` [ArkLib\ToMathlib\UMSubspaceDesignProof.lean:272](../../../ArkLib\ToMathlib\UMSubspaceDesignProof.lean#L272)
    - a: The 1-dimensional subspace `span{a}` meets `ker(proj i)` trivially when `a i ≠ 0`.
    - b: The 1-dimensional subspace `span{a}` meets `ker(proj i)` trivially when `a i ≠ 0`.
- **1.00** `Commitment.perfectCorrectness` [ArkLib\CommitmentScheme\Basic.lean:109](../../../ArkLib\CommitmentScheme\Basic.lean#L109) vs `CommitmentScheme.perfectCorrectness` [ArkLib\CommitmentScheme\CommitmentScheme.lean:74](../../../ArkLib\CommitmentScheme\CommitmentScheme.lean#L74)
    - a: A commitment scheme satisfies **perfect correctness** if it satisfies correctness with no error.
    - b: A commitment scheme satisfies **perfect correctness** if it satisfies correctness with no error.
- **1.00** `GSHasse.gsSupport` [ArkLib\Data\CodingTheory\ProximityGap\GSHasseMultiplicity.lean:69](../../../ArkLib\Data\CodingTheory\ProximityGap\GSHasseMultiplicity.lean#L69) vs `GSInterp.gsSupport` [ArkLib\Data\CodingTheory\ProximityGap\GSInterpolationExistence.lean:55](../../../ArkLib\Data\CodingTheory\ProximityGap\GSInterpolationExistence.lean#L55)
    - a: Monomial support of the GS interpolation space: pairs `(i, j)` with `i + (k-1)·j < D`, organized as
    - b: Monomial support of the GS interpolation space: pairs `(i, j)` with `i + (k-1)·j < D`, organized as
- **1.00** `GSInterp.evalAtPoints` [ArkLib\Data\CodingTheory\ProximityGap\GSInterpolationExistence.lean:133](../../../ArkLib\Data\CodingTheory\ProximityGap\GSInterpolationExistence.lean#L133) vs `R15.evalAtPoints` [ArkLib\Data\CodingTheory\ProximityGap\SudanListBound.lean:140](../../../ArkLib\Data\CodingTheory\ProximityGap\SudanListBound.lean#L140)
    - a: The linear map sending a coefficient vector supported on `S` to the values of the associated bivaria
    - b: The linear map sending a coefficient vector supported on `S` to the values of the associated bivaria
- **1.00** `GSInterp.evalAtPoints` [ArkLib\Data\CodingTheory\ProximityGap\GSInterpolationExistence.lean:133](../../../ArkLib\Data\CodingTheory\ProximityGap\GSInterpolationExistence.lean#L133) vs `R15.evalAtPoints` [ArkLib\Data\CodingTheory\ProximityGap\SudanListBoundFull.lean:140](../../../ArkLib\Data\CodingTheory\ProximityGap\SudanListBoundFull.lean#L140)
    - a: The linear map sending a coefficient vector supported on `S` to the values of the associated bivaria
    - b: The linear map sending a coefficient vector supported on `S` to the values of the associated bivaria
- **1.00** `Groups.exists_zmod_power_of_generator` [ArkLib\CommitmentScheme\KZG\Algebra.lean:105](../../../ArkLib\CommitmentScheme\KZG\Algebra.lean#L105) vs `KZG.CommitmentScheme.binding_exists_zmod_power_of_generator` [ArkLib\CommitmentScheme\KZG\Binding.lean:167](../../../ArkLib\CommitmentScheme\KZG\Binding.lean#L167)
    - a: Every element of a prime-order group is a `ZMod p` power of a nontrivial generator.
    - b: Every element of a prime-order group is a `ZMod p` power of a nontrivial generator.
- **1.00** `Groups.orderOf_eq_prime_of_ne_one` [ArkLib\CommitmentScheme\KZG\Algebra.lean:61](../../../ArkLib\CommitmentScheme\KZG\Algebra.lean#L61) vs `KZG.CommitmentScheme.binding_order_of_eq_prime_of_ne_one` [ArkLib\CommitmentScheme\KZG\Binding.lean:157](../../../ArkLib\CommitmentScheme\KZG\Binding.lean#L157)
    - a: A nontrivial element of a prime-order group has order `p`.
    - b: A nontrivial element of a prime-order group has order `p`.
- **1.00** `KZG.CommitmentScheme.map_binding_instance_drag` [ArkLib\CommitmentScheme\KZG\Binding.lean:639](../../../ArkLib\CommitmentScheme\KZG\Binding.lean#L639) vs `KZG.CommitmentScheme.map_instance_drag` [ArkLib\CommitmentScheme\KZG\FunctionBinding\Basic.lean:534](../../../ArkLib\CommitmentScheme\KZG\FunctionBinding\Basic.lean#L534)
    - a: Transition 3: dragging the map into the probability event.
    - b: Transition 3: dragging the map into the probability event
- **1.00** `Logup.simulateQ_optionT_failure'` [ArkLib\ProofSystem\Logup\Security\OuterRun.lean:52](../../../ArkLib\ProofSystem\Logup\Security\OuterRun.lean#L52) vs `ToyProblem.Spec.simulateQ_optionT_failure` [ArkLib\ProofSystem\ToyProblem\Spec\General.lean:643](../../../ArkLib\ProofSystem\ToyProblem\Spec\General.lean#L643)
    - a: `simulateQ` commutes with `OptionT` `failure`.
    - b: `simulateQ` commutes with `OptionT` `failure`.
- **1.00** `Logup.simulateQ_optionT_pure'` [ArkLib\ProofSystem\Logup\Security\OuterRun.lean:44](../../../ArkLib\ProofSystem\Logup\Security\OuterRun.lean#L44) vs `ToyProblem.Spec.simulateQ_optionT_pure` [ArkLib\ProofSystem\ToyProblem\Spec\General.lean:636](../../../ArkLib\ProofSystem\ToyProblem\Spec\General.lean#L636)
    - a: `simulateQ` commutes with `OptionT.pure`.
    - b: `simulateQ` commutes with `OptionT.pure`.
- **1.00** `Logup.simulateQ_simOracle2_leftQuery_oc'` [ArkLib\ProofSystem\Logup\Security\OuterRun.lean:129](../../../ArkLib\ProofSystem\Logup\Security\OuterRun.lean#L129) vs `ToyProblem.Spec.simulateQ_simOracle2_leftQuery_oc` [ArkLib\ProofSystem\ToyProblem\Spec\General.lean:733](../../../ArkLib\ProofSystem\ToyProblem\Spec\General.lean#L733)
    - a: `simOracle2` oracle-statement-query collapse (`OracleComp` form), LEFT (oracle) family.
    - b: `simOracle2` oracle-statement-query collapse (`OracleComp` form), LEFT (oracle) family.
- **1.00** `Pr_badStack_eq_one` [ArkLib\MCAGSRefutationCore_keep.lean:63](../../../ArkLib\MCAGSRefutationCore_keep.lean#L63) vs `ProximityGap.MCAGSPrizeRefutation.Pr_badStack_eq_one` [ArkLib\Data\CodingTheory\ProximityGap\MCAGSPrizeRefutation.lean:64](../../../ArkLib\Data\CodingTheory\ProximityGap\MCAGSPrizeRefutation.lean#L64)
    - a: **The bad event has probability 1.** Since `mcaEventGSrow_badStack` holds for every `γ`, the event i
    - b: **The bad event has probability 1.** Since `mcaEventGSrow_badStack` holds for every `γ`, the event i
- **1.00** `Probability.uniformSizeSubset_apply_mapEquiv` [ArkLib\Data\Probability\Combinatorial.lean:168](../../../ArkLib\Data\Probability\Combinatorial.lean#L168) vs `Probability.uniformSizedSubset_apply_mapEquiv` [ArkLib\Data\Probability\UniformSubset.lean:115](../../../ArkLib\Data\Probability\UniformSubset.lean#L115)
    - a: Uniform fixed-size subset sampling is invariant under equivalence of ambient finite types.
    - b: Uniform fixed-size subset sampling is invariant under equivalence of ambient finite types.
- **1.00** `Prover.processRoundDSFS` [ArkLib\OracleReduction\FiatShamir\DuplexSponge\Defs.lean:491](../../../ArkLib\OracleReduction\FiatShamir\DuplexSponge\Defs.lean#L491) vs `Prover.processRoundFS` [ArkLib\OracleReduction\FiatShamir\Basic.lean:80](../../../ArkLib\OracleReduction\FiatShamir\Basic.lean#L80)
    - a: Prover's function for processing the next round, given the current result of the previous round. Thi
    - b: Prover's function for processing the next round, given the current result of the previous round. Thi
- **1.00** `Prover.runToRound` [ArkLib\OracleReduction\Execution.lean:60](../../../ArkLib\OracleReduction\Execution.lean#L60) vs `Prover.runToRoundDSFS` [ArkLib\OracleReduction\FiatShamir\DuplexSponge\Defs.lean:524](../../../ArkLib\OracleReduction\FiatShamir\DuplexSponge\Defs.lean#L524)
    - a: Run the prover in an interactive reduction up to round index `i`, via first inputting the statement
    - b: Run the prover in an interactive reduction up to round index `i`, via first inputting the statement
- **1.00** `Prover.runToRound` [ArkLib\OracleReduction\Execution.lean:60](../../../ArkLib\OracleReduction\Execution.lean#L60) vs `Prover.runToRoundFS` [ArkLib\OracleReduction\FiatShamir\Basic.lean:102](../../../ArkLib\OracleReduction\FiatShamir\Basic.lean#L102)
    - a: Run the prover in an interactive reduction up to round index `i`, via first inputting the statement
    - b: Run the prover in an interactive reduction up to round index `i`, via first inputting the statement
- **1.00** `Prover.runToRoundDSFS` [ArkLib\OracleReduction\FiatShamir\DuplexSponge\Defs.lean:524](../../../ArkLib\OracleReduction\FiatShamir\DuplexSponge\Defs.lean#L524) vs `Prover.runToRoundFS` [ArkLib\OracleReduction\FiatShamir\Basic.lean:102](../../../ArkLib\OracleReduction\FiatShamir\Basic.lean#L102)
    - a: Run the prover in an interactive reduction up to round index `i`, via first inputting the statement
    - b: Run the prover in an interactive reduction up to round index `i`, via first inputting the statement
- **1.00** `ProximityGap.GrandChallengesLattice.prizeRates_le_half` [ArkLib\Data\CodingTheory\ProximityGap\GrandChallengeInteriorJ1.lean:626](../../../ArkLib\Data\CodingTheory\ProximityGap\GrandChallengeInteriorJ1.lean#L626) vs `ProximityGap.prizeRates_le_half` [ArkLib\Data\CodingTheory\ProximityGap\GrandChallengeLDFourRate.lean:208](../../../ArkLib\Data\CodingTheory\ProximityGap\GrandChallengeLDFourRate.lean#L208)
    - a: Every ABF26 prize rate is at most `1/2`.
    - b: Every ABF26 prize rate is at most `1/2`.
- **1.00** `ProximityGap.MCAGSPrizeRefutation.epsMCAgs_badList_eq_one` [ArkLib\Data\CodingTheory\ProximityGap\MCAGSPrizeRefutation.lean:82](../../../ArkLib\Data\CodingTheory\ProximityGap\MCAGSPrizeRefutation.lean#L82) vs `epsMCAgs_badList_eq_one` [ArkLib\MCAGSRefutationCore_keep.lean:81](../../../ArkLib\MCAGSRefutationCore_keep.lean#L81)
    - a: **`epsMCAgs = 1` for the adversarial list family.** This is the refutation kernel: a non-faithful `L
    - b: **`epsMCAgs = 1` for the adversarial list family.** This is the refutation kernel: a non-faithful `L
- **1.00** `ProximityGap.MCAGSPrizeRefutation.mcaEventGSrow_badStack` [ArkLib\Data\CodingTheory\ProximityGap\MCAGSPrizeRefutation.lean:36](../../../ArkLib\Data\CodingTheory\ProximityGap\MCAGSPrizeRefutation.lean#L36) vs `mcaEventGSrow_badStack` [ArkLib\MCAGSRefutationCore_keep.lean:35](../../../ArkLib\MCAGSRefutationCore_keep.lean#L35)
    - a: **Key lemma.** For any nonzero codeword `w₀ ∈ C` and any `δ ≤ 1`, the GS-row bad event fires at the
    - b: **Key lemma.** For any nonzero codeword `w₀ ∈ C` and any `δ ≤ 1`, the GS-row bad event fires at the
- **1.00** `ProximityGap.MCAGSPrizeRefutation.not_uniformEpsMCAgsPrizeBoundConjecture` [ArkLib\Data\CodingTheory\ProximityGap\MCAGSPrizeRefutation.lean:102](../../../ArkLib\Data\CodingTheory\ProximityGap\MCAGSPrizeRefutation.lean#L102) vs `not_uniformEpsMCAgsPrizeBoundConjecture` [ArkLib\MCAGSRefutationCore_keep.lean:101](../../../ArkLib\MCAGSRefutationCore_keep.lean#L101)
    - a: **MAIN THEOREM (#141): the formalized uniform prize conjecture is FALSE.** `uniformEpsMCAgsPrizeBoun
    - b: **MAIN THEOREM (#141): the formalized uniform prize conjecture is FALSE.** `uniformEpsMCAgsPrizeBoun
- **1.00** `ProximityGap.RS_goodCoeffsCurve_finCongr` [ArkLib\Data\CodingTheory\ProximityGap\BCIKS20\Curves\Assembly.lean:194](../../../ArkLib\Data\CodingTheory\ProximityGap\BCIKS20\Curves\Assembly.lean#L194) vs `ProximityGap.RS_goodCoeffsCurve_finCongr_core` [ArkLib\Data\CodingTheory\ProximityGap\BCIKS20\Curves.lean:1082](../../../ArkLib\Data\CodingTheory\ProximityGap\BCIKS20\Curves.lean#L1082)
    - a: `RS_goodCoeffsCurve` is unchanged by a definitional reindexing of its `Fin (k + 1)` coefficient word
    - b: `RS_goodCoeffsCurve` is unchanged by a definitional reindexing of its `Fin (k + 1)` coefficient word
- **1.00** `ProximityPrize.HenselExistence.coeff_S_succ_of_le` [ArkLib\Data\Polynomial\HenselExistence.lean:197](../../../ArkLib\Data\Polynomial\HenselExistence.lean#L197) vs `ProximityPrize.HenselSeriesCoeff.coeff_S_succ_of_le` [ArkLib\Data\Polynomial\HenselSeriesCoeff.lean:275](../../../ArkLib\Data\Polynomial\HenselSeriesCoeff.lean#L275)
    - a: Adding the order-`(t+1)` monomial leaves coefficients `≤ t` unchanged.
    - b: Adding the order-`(t+1)` monomial leaves coefficients `≤ t` unchanged.
- **1.00** `ProximityPrize.HenselExistence.coeff_γ_eq_S` [ArkLib\Data\Polynomial\HenselExistence.lean:236](../../../ArkLib\Data\Polynomial\HenselExistence.lean#L236) vs `ProximityPrize.HenselSeriesCoeff.coeff_γ_eq_S` [ArkLib\Data\Polynomial\HenselSeriesCoeff.lean:312](../../../ArkLib\Data\Polynomial\HenselSeriesCoeff.lean#L312)
    - a: `γ` agrees with the `t`-th partial sum below order `t + 1`.
    - b: `γ` agrees with the `t`-th partial sum below order `t + 1`.
- **1.00** `ProximityPrize.HenselExistence.constantCoeff_γ` [ArkLib\Data\Polynomial\HenselExistence.lean:231](../../../ArkLib\Data\Polynomial\HenselExistence.lean#L231) vs `ProximityPrize.HenselSeriesCoeff.constantCoeff_γ` [ArkLib\Data\Polynomial\HenselSeriesCoeff.lean:307](../../../ArkLib\Data\Polynomial\HenselSeriesCoeff.lean#L307)
    - a: The constant coefficient of the Newton root is the prescribed root `c`.
    - b: The constant coefficient of the Newton root is the prescribed root `c`.
- **1.00** `R12.linearIndependent_pow_le` [ArkLib\Data\CodingTheory\ProximityGap\LamLeungUnconditionalGeneral.lean:62](../../../ArkLib\Data\CodingTheory\ProximityGap\LamLeungUnconditionalGeneral.lean#L62) vs `R12J.linearIndependent_pow_le` [ArkLib\Data\CodingTheory\ProximityGap\JointT2Unconditional.lean:93](../../../ArkLib\Data\CodingTheory\ProximityGap\JointT2Unconditional.lean#L93)
    - a: UNCONDITIONAL: over a field `K`, the first `N` powers of `ζ` are `K`-linearly independent whenever `
    - b: UNCONDITIONAL: over a field `K`, the first `N` powers of `ζ` are `K`-linearly independent whenever `
- **1.00** `Reduction.hcoh_right` [ArkLib\OracleReduction\Composition\Sequential\AppendSeamBridges.lean:149](../../../ArkLib\OracleReduction\Composition\Sequential\AppendSeamBridges.lean#L149) vs `Reduction.hcoh_right'` [ArkLib\OracleReduction\Composition\Sequential\AppendSeamBridges2.lean:128](../../../ArkLib\OracleReduction\Composition\Sequential\AppendSeamBridges2.lean#L128)
    - a: **`OptionT`-level lift transitivity through the `pSpec₂` challenge seam.** The `pSpec₂` analogue of
    - b: **`OptionT`-level lift transitivity through the `pSpec₂` challenge seam.** The `pSpec₂` analogue of
- **1.00** `Round20CliqueKernel.cliqueLocator` [ArkLib\Data\CodingTheory\ProximityGap\Conjecture41CliqueKernelStructure.lean:60](../../../ArkLib\Data\CodingTheory\ProximityGap\Conjecture41CliqueKernelStructure.lean#L60) vs `Round21Relations.cliqueLocator` [ArkLib\Data\CodingTheory\ProximityGap\Conjecture41CliqueRelationModule.lean:56](../../../ArkLib\Data\CodingTheory\ProximityGap\Conjecture41CliqueRelationModule.lean#L56)
    - a: The clique error locator at vertex `α`: `Λ_{W∖{α}} = ∏_{β ∈ W.erase α} (X − β)`.
    - b: The clique error locator at vertex `α`: `Λ_{W∖{α}} = ∏_{β ∈ W.erase α} (X − β)`.
- **1.00** `Spartan.Spec.foldl_add_eq_sum` [ArkLib\ProofSystem\Spartan\FirstSumcheckMulVec.lean:36](../../../ArkLib\ProofSystem\Spartan\FirstSumcheckMulVec.lean#L36) vs `Sumcheck.Spec.SingleRound.foldl_add_eq_sum` [ArkLib\ProofSystem\Sumcheck\Spec\SimpleRoundCoherent.lean:78](../../../ArkLib\ProofSystem\Sumcheck\Spec\SimpleRoundCoherent.lean#L78)
    - a: A left fold that accumulates `acc + g y` over a list equals `acc` plus the list sum of `g`.
    - b: A left fold that accumulates `acc + g y` over a list equals `acc` plus the list sum of `g`.
- **1.00** `Spartan.Spec.foldl_add_eq_sum` [ArkLib\ProofSystem\Spartan\FirstSumcheckZeroEval.lean:39](../../../ArkLib\ProofSystem\Spartan\FirstSumcheckZeroEval.lean#L39) vs `Sumcheck.Spec.SingleRound.foldl_add_eq_sum` [ArkLib\ProofSystem\Sumcheck\Spec\SimpleRoundCoherent.lean:78](../../../ArkLib\ProofSystem\Sumcheck\Spec\SimpleRoundCoherent.lean#L78)
    - a: A left fold that accumulates `acc + g y` over a list equals `acc` plus the list sum of `g`.
    - b: A left fold that accumulates `acc + g y` over a list equals `acc` plus the list sum of `g`.
- **1.00** `StirIOP.OracleStatement` [ArkLib\ProofSystem\Stir\MainThm.lean:84](../../../ArkLib\ProofSystem\Stir\MainThm.lean#L84) vs `WhirIOP.OracleStatement` [ArkLib\ProofSystem\Whir\RBRSoundness.lean:146](../../../ArkLib\ProofSystem\Whir\RBRSoundness.lean#L146)
    - a: `OracleStatement` defines the oracle message type for a multi-indexed setting: given base input type
    - b: `OracleStatement` defines the oracle message type for a multi-indexed setting: given base input type
- **1.00** `StirIOP.Params` [ArkLib\ProofSystem\Stir\MainThm.lean:35](../../../ArkLib\ProofSystem\Stir\MainThm.lean#L35) vs `WhirIOP.Params` [ArkLib\ProofSystem\Whir\RBRSoundness.lean:54](../../../ArkLib\ProofSystem\Whir\RBRSoundness.lean#L54)
    - a: **Per‑round protocol parameters:** For a fixed depth `M`, the reduction runs `M + 1` rounds. In roun
    - b: ** Per‑round protocol parameters. ** For a fixed depth `M`, the reduction runs `M + 1` rounds. In ro
- **0.93** `ArkLib.CodingTheory.Round5Unconditional.headline_hypotheses_satisfiable` [ArkLib\Data\CodingTheory\ProximityGap\ListInteriorUnconditionalT1.lean:272](../../../ArkLib\Data\CodingTheory\ProximityGap\ListInteriorUnconditionalT1.lean#L272) vs `ArkLib.CodingTheory.Round6DeeperT2.headline_hypotheses_satisfiable_t2` [ArkLib\Data\CodingTheory\ProximityGap\ListInteriorUnconditionalT2.lean:340](../../../ArkLib\Data\CodingTheory\ProximityGap\ListInteriorUnconditionalT2.lean#L340)
    - a: **The headline hypotheses are jointly satisfiable (non-vacuity).** At `k = 50` and `n = 104` (rate `
    - b: **The headline hypotheses are jointly satisfiable (non-vacuity).** At `k = 50` and `n = 220` (rate `
- **0.93** `ArkLib.CodingTheory.Round3SmoothF17.L_subset_code` [ArkLib\Data\CodingTheory\ProximityGap\ListInteriorPinF17Subgroup.lean:162](../../../ArkLib\Data\CodingTheory\ProximityGap\ListInteriorPinF17Subgroup.lean#L162) vs `ArkLib.CodingTheory.TinyInteriorF11.L11_subset_code` [ArkLib\Data\CodingTheory\ProximityGap\ListInteriorPinF11.lean:187](../../../ArkLib\Data\CodingTheory\ProximityGap\ListInteriorPinF11.lean#L187)
    - a: **Every element of `L` is a smooth-domain Reed–Solomon codeword of degree `< 2`.** This is the non-v
    - b: **Every element of `L₁₁` is a Reed–Solomon codeword of degree `< 2`.** This is the non-vacuity witne
- **0.93** `ArkLib.CodingTheory.Round3SmoothF17.L_subset_code` [ArkLib\Data\CodingTheory\ProximityGap\ListInteriorPinF17Subgroup.lean:162](../../../ArkLib\Data\CodingTheory\ProximityGap\ListInteriorPinF17Subgroup.lean#L162) vs `ArkLib.CodingTheory.TinyInteriorPin.L_subset_code` [ArkLib\Data\CodingTheory\ProximityGap\ListInteriorDataPointF7.lean:127](../../../ArkLib\Data\CodingTheory\ProximityGap\ListInteriorDataPointF7.lean#L127)
    - a: **Every element of `L` is a smooth-domain Reed–Solomon codeword of degree `< 2`.** This is the non-v
    - b: **Every element of `L` is a Reed–Solomon codeword of degree `< 2`.** This is the non-vacuity witness
- **0.92** `BCIKS20.HenselNumerator.coeff_succ_eval_βHenselAssembled_of_WfreeForm` [ArkLib\Data\CodingTheory\ProximityGap\BCIKS20\P2MonicWfreeConsumers.lean:51](../../../ArkLib\Data\CodingTheory\ProximityGap\BCIKS20\P2MonicWfreeConsumers.lean#L51) vs `BCIKS20.HenselNumerator.coeff_succ_eval_βHenselAssembled_of_rangeWfreeMatchAt` [ArkLib\Data\CodingTheory\ProximityGap\BCIKS20\P2MonicWfreeRangeConsumers.lean:70](../../../ArkLib\Data\CodingTheory\ProximityGap\BCIKS20\P2MonicWfreeRangeConsumers.lean#L70)
    - a: A single fixed-order W-free equation implies the corresponding assembled-root coefficient vanishing
    - b: A single fixed-order range-indexed W-free equation implies the corresponding assembled-root coeffici
- **0.92** `BCIKS20.HenselNumerator.coeff_succ_eval_βHenselAssembled_of_WfreeMatch` [ArkLib\Data\CodingTheory\ProximityGap\BCIKS20\P2MonicWfreeConsumers.lean:76](../../../ArkLib\Data\CodingTheory\ProximityGap\BCIKS20\P2MonicWfreeConsumers.lean#L76) vs `BCIKS20.HenselNumerator.coeff_succ_eval_βHenselAssembled_of_rangeWfreeMatch` [ArkLib\Data\CodingTheory\ProximityGap\BCIKS20\P2MonicWfreeRangeConsumers.lean:93](../../../ArkLib\Data\CodingTheory\ProximityGap\BCIKS20\P2MonicWfreeRangeConsumers.lean#L93)
    - a: The global W-free predicate implies every assembled-root successor coefficient vanishes under monic
    - b: The global range-indexed W-free predicate implies every assembled-root successor coefficient vanishe
- **0.91** `R11.antipodal_of_sum_zero` [ArkLib\Data\CodingTheory\ProximityGap\LamLeungUnconditionalQ.lean:91](../../../ArkLib\Data\CodingTheory\ProximityGap\LamLeungUnconditionalQ.lean#L91) vs `R12.antipodal_of_sum_zero` [ArkLib\Data\CodingTheory\ProximityGap\LamLeungUnconditionalGeneral.lean:95](../../../ArkLib\Data\CodingTheory\ProximityGap\LamLeungUnconditionalGeneral.lean#L95)
    - a: **General unconditional antipodal tightness.** If the first `N` powers of `ζ` are `K`-linearly indep
    - b: **General antipodal tightness.** If the first `N` powers of `ζ` are `K`-linearly independent (UNCOND
- **0.91** `BCIKS20.HenselNumerator.FaaDiBrunoSuccSumZeroResidual.of_WfreeMatch` [ArkLib\Data\CodingTheory\ProximityGap\BCIKS20\P2MonicWfreeGlobal.lean:127](../../../ArkLib\Data\CodingTheory\ProximityGap\BCIKS20\P2MonicWfreeGlobal.lean#L127) vs `BCIKS20.HenselNumerator.FaaDiBrunoSuccSumZeroResidual.of_rangeWfreeMatch` [ArkLib\Data\CodingTheory\ProximityGap\BCIKS20\P2MonicWfreeRangeConsumers.lean:47](../../../ArkLib\Data\CodingTheory\ProximityGap\BCIKS20\P2MonicWfreeRangeConsumers.lean#L47)
    - a: Build the legacy successor-sum P2 residual from the global W-free target under monic `H`.
    - b: Build the legacy successor-sum residual from the global range-indexed W-free target under monic `H`.
- **0.91** `BCIKS20.HenselNumerator.RestrictedFaaDiBrunoMatch.of_WfreeMatch` [ArkLib\Data\CodingTheory\ProximityGap\BCIKS20\P2MonicWfreeGlobal.lean:85](../../../ArkLib\Data\CodingTheory\ProximityGap\BCIKS20\P2MonicWfreeGlobal.lean#L85) vs `BCIKS20.HenselNumerator.RestrictedFaaDiBrunoMatch.of_rangeWfreeMatch` [ArkLib\Data\CodingTheory\ProximityGap\BCIKS20\P2MonicWfreeRangeConsumers.lean:37](../../../ArkLib\Data\CodingTheory\ProximityGap\BCIKS20\P2MonicWfreeRangeConsumers.lean#L37)
    - a: Build the carved all-order P2 residual from the global W-free target under monic `H`.
    - b: Build the carved all-order P2 residual from the global range-indexed W-free target under monic `H`.
- **0.91** `BCIKS20.HenselNumerator.RestrictedFaaDiBrunoRangeWfreeMatchAt.of_monic` [ArkLib\Data\CodingTheory\ProximityGap\BCIKS20\P2MonicWfreeRange.lean:203](../../../ArkLib\Data\CodingTheory\ProximityGap\BCIKS20\P2MonicWfreeRange.lean#L203) vs `BCIKS20.HenselNumerator.WfreeForm_eq_of_monic` [ArkLib\Data\CodingTheory\ProximityGap\BCIKS20\P2MonicWfreeGlobal.lean:109](../../../ArkLib\Data\CodingTheory\ProximityGap\BCIKS20\P2MonicWfreeGlobal.lean#L109)
    - a: The proved monic carved match supplies each fixed range-indexed W-free equation directly.
    - b: The proved monic carved match supplies each fixed W-free equation directly.
- **0.91** `BCIKS20.HenselNumerator.trunc_defect_cancel_assembled_at_of_WfreeForm` [ArkLib\Data\CodingTheory\ProximityGap\BCIKS20\P2MonicWfreeConsumers.lean:36](../../../ArkLib\Data\CodingTheory\ProximityGap\BCIKS20\P2MonicWfreeConsumers.lean#L36) vs `BCIKS20.HenselNumerator.trunc_defect_cancel_assembled_at_of_rangeWfreeMatchAt` [ArkLib\Data\CodingTheory\ProximityGap\BCIKS20\P2MonicWfreeRangeConsumers.lean:57](../../../ArkLib\Data\CodingTheory\ProximityGap\BCIKS20\P2MonicWfreeRangeConsumers.lean#L57)
    - a: A single fixed-order W-free equation implies the corresponding truncated-defect cancellation under m
    - b: A single fixed-order range-indexed W-free equation implies the corresponding truncated-defect cancel
- **0.91** `GSHasse.gsSupport` [ArkLib\Data\CodingTheory\ProximityGap\GSHasseMultiplicity.lean:69](../../../ArkLib\Data\CodingTheory\ProximityGap\GSHasseMultiplicity.lean#L69) vs `R15.gsSupport` [ArkLib\Data\CodingTheory\ProximityGap\SudanListBound.lean:69](../../../ArkLib\Data\CodingTheory\ProximityGap\SudanListBound.lean#L69)
    - a: Monomial support of the GS interpolation space: pairs `(i, j)` with `i + (k-1)·j < D`, organized as
    - b: Monomial support of the Sudan interpolation space: pairs `(i, j)` with `i + (k-1)·j < D`, organized
- **0.91** `GSHasse.gsSupport` [ArkLib\Data\CodingTheory\ProximityGap\GSHasseMultiplicity.lean:69](../../../ArkLib\Data\CodingTheory\ProximityGap\GSHasseMultiplicity.lean#L69) vs `R15.gsSupport` [ArkLib\Data\CodingTheory\ProximityGap\SudanListBoundFull.lean:69](../../../ArkLib\Data\CodingTheory\ProximityGap\SudanListBoundFull.lean#L69)
    - a: Monomial support of the GS interpolation space: pairs `(i, j)` with `i + (k-1)·j < D`, organized as
    - b: Monomial support of the Sudan interpolation space: pairs `(i, j)` with `i + (k-1)·j < D`, organized
- **0.91** `GSInterp.gsSupport` [ArkLib\Data\CodingTheory\ProximityGap\GSInterpolationExistence.lean:55](../../../ArkLib\Data\CodingTheory\ProximityGap\GSInterpolationExistence.lean#L55) vs `R15.gsSupport` [ArkLib\Data\CodingTheory\ProximityGap\SudanListBound.lean:69](../../../ArkLib\Data\CodingTheory\ProximityGap\SudanListBound.lean#L69)
    - a: Monomial support of the GS interpolation space: pairs `(i, j)` with `i + (k-1)·j < D`, organized as
    - b: Monomial support of the Sudan interpolation space: pairs `(i, j)` with `i + (k-1)·j < D`, organized
- **0.91** `GSInterp.gsSupport` [ArkLib\Data\CodingTheory\ProximityGap\GSInterpolationExistence.lean:55](../../../ArkLib\Data\CodingTheory\ProximityGap\GSInterpolationExistence.lean#L55) vs `R15.gsSupport` [ArkLib\Data\CodingTheory\ProximityGap\SudanListBoundFull.lean:69](../../../ArkLib\Data\CodingTheory\ProximityGap\SudanListBoundFull.lean#L69)
    - a: Monomial support of the GS interpolation space: pairs `(i, j)` with `i + (k-1)·j < D`, organized as
    - b: Monomial support of the Sudan interpolation space: pairs `(i, j)` with `i + (k-1)·j < D`, organized
- **0.90** `ProximityPrize.HenselExistence.S` [ArkLib\Data\Polynomial\HenselExistence.lean:189](../../../ArkLib\Data\Polynomial\HenselExistence.lean#L189) vs `ProximityPrize.HenselSeriesCoeff.S` [ArkLib\Data\Polynomial\HenselSeriesCoeff.lean:267](../../../ArkLib\Data\Polynomial\HenselSeriesCoeff.lean#L267)
    - a: The Newton partial-sum sequence. `S 0 := C c`, and at each step we add the order-`(t+1)` correction
    - b: The Newton partial-sum sequence for `Q`. `S 0 := C c`; at each step we add the order-`(t+1)` correct
- **0.90** `ArkLib.BetaToCurveCoeffPolys.mk_eq_trunc_of_tail_zero` [ArkLib\ToMathlib\BetaToCurveCoeffPolysOffcentre.lean:86](../../../ArkLib\ToMathlib\BetaToCurveCoeffPolysOffcentre.lean#L86) vs `PowerSeries.mk_eq_trunc_of_tail_zero` [ArkLib\ToMathlib\ExtractedIssueBricks.lean:77](../../../ArkLib\ToMathlib\ExtractedIssueBricks.lean#L77)
    - a: A power series whose coefficients vanish from index `k` on **is** (the coercion of) its `k`-truncati
    - b: A power series whose coefficients vanish from index `k` on equals the coercion of its `k`-truncation
- **0.90** `ArkLib.CodingTheory.TinyInteriorF11.eight_elevenths_strictly_interior` [ArkLib\Data\CodingTheory\ProximityGap\ListInteriorPinF11.lean:304](../../../ArkLib\Data\CodingTheory\ProximityGap\ListInteriorPinF11.lean#L304) vs `ArkLib.CodingTheory.TinyInteriorK3.six_elevenths_strictly_interior` [ArkLib\Data\CodingTheory\ProximityGap\ListInteriorPinF11K3.lean:256](../../../ArkLib\Data\CodingTheory\ProximityGap\ListInteriorPinF11K3.lean#L256)
    - a: **Gap placement.** The relative radius `δ = 8/11` (agreement `a = 3` out of `n = 11`) is strictly be
    - b: **Gap placement.** The relative radius `δ = 6/11` (agreement `a = 5` out of `n = 11`) is strictly be
- **0.90** `ArkLib.CodingTheory.TinyInteriorF11.eight_elevenths_strictly_interior` [ArkLib\Data\CodingTheory\ProximityGap\ListInteriorPinF11.lean:304](../../../ArkLib\Data\CodingTheory\ProximityGap\ListInteriorPinF11.lean#L304) vs `ArkLib.CodingTheory.TinyInteriorPin.four_sevenths_strictly_interior` [ArkLib\Data\CodingTheory\ProximityGap\ListInteriorDataPointF7.lean:215](../../../ArkLib\Data\CodingTheory\ProximityGap\ListInteriorDataPointF7.lean#L215)
    - a: **Gap placement.** The relative radius `δ = 8/11` (agreement `a = 3` out of `n = 11`) is strictly be
    - b: **Gap placement.** The relative radius `δ = 4/7` (agreement `a = 3` out of `n = 7`) is strictly betw
- **0.90** `BCIKS20.HenselNumerator.RestrictedFaaDiBrunoRangeWfreeMatch.of_monic` [ArkLib\Data\CodingTheory\ProximityGap\BCIKS20\P2MonicWfreeRange.lean:195](../../../ArkLib\Data\CodingTheory\ProximityGap\BCIKS20\P2MonicWfreeRange.lean#L195) vs `BCIKS20.HenselNumerator.RestrictedFaaDiBrunoWfreeMatch.of_monic` [ArkLib\Data\CodingTheory\ProximityGap\BCIKS20\P2MonicWfreeGlobal.lean:101](../../../ArkLib\Data\CodingTheory\ProximityGap\BCIKS20\P2MonicWfreeGlobal.lean#L101)
    - a: The proved monic carved match supplies the global range-indexed W-free target directly.
    - b: The proved monic carved match supplies the global W-free target directly.
- **0.90** `BCIKS20.HenselNumerator.assembledSeries_isRoot_of_WfreeMatch` [ArkLib\Data\CodingTheory\ProximityGap\BCIKS20\P2MonicWfreeConsumers.lean:85](../../../ArkLib\Data\CodingTheory\ProximityGap\BCIKS20\P2MonicWfreeConsumers.lean#L85) vs `BCIKS20.HenselNumerator.assembledSeries_isRoot_of_rangeWfreeMatch` [ArkLib\Data\CodingTheory\ProximityGap\BCIKS20\P2MonicWfreeRangeConsumers.lean:103](../../../ArkLib\Data\CodingTheory\ProximityGap\BCIKS20\P2MonicWfreeRangeConsumers.lean#L103)
    - a: The global W-free predicate gives the assembled-series root statement under monic `H`.
    - b: The global range-indexed W-free predicate gives the assembled-series root statement under monic `H`.
- **0.90** `BCIKS20.HenselNumerator.trunc_defect_cancel_assembled_of_WfreeMatch` [ArkLib\Data\CodingTheory\ProximityGap\BCIKS20\P2MonicWfreeConsumers.lean:63](../../../ArkLib\Data\CodingTheory\ProximityGap\BCIKS20\P2MonicWfreeConsumers.lean#L63) vs `BCIKS20.HenselNumerator.trunc_defect_cancel_assembled_of_rangeWfreeMatch` [ArkLib\Data\CodingTheory\ProximityGap\BCIKS20\P2MonicWfreeRangeConsumers.lean:81](../../../ArkLib\Data\CodingTheory\ProximityGap\BCIKS20\P2MonicWfreeRangeConsumers.lean#L81)
    - a: The global W-free predicate implies every truncated-defect cancellation under monic `H`.
    - b: The global range-indexed W-free predicate implies every truncated-defect cancellation under monic `H
- **0.89** `Logup.forIn_guard_eq'` [ArkLib\ProofSystem\Logup\Security\OuterRun.lean:93](../../../ArkLib\ProofSystem\Logup\Security\OuterRun.lean#L93) vs `ToyProblem.Spec.forIn_guard_eq` [ArkLib\ProofSystem\ToyProblem\Spec\General.lean:684](../../../ArkLib\ProofSystem\ToyProblem\Spec\General.lean#L684)
    - a: A `forIn` over a list whose body is `guard (Q a)` then `yield ()` collapses to `if (∀ a ∈ l, Q a) th
    - b: A `forIn` over a list whose body is `guard (Q a)` then `yield ()` collapses to `if (∀ a ∈ l, Q a) th
- **0.89** `BCIKS20.HenselNumerator.P2_closed_of_WfreeMatch` [ArkLib\Data\CodingTheory\ProximityGap\BCIKS20\P2MonicWfreeConsumers.lean:106](../../../ArkLib\Data\CodingTheory\ProximityGap\BCIKS20\P2MonicWfreeConsumers.lean#L106) vs `BCIKS20.HenselNumerator.P2_closed_of_rangeWfreeMatch` [ArkLib\Data\CodingTheory\ProximityGap\BCIKS20\P2MonicWfreeRangeConsumers.lean:125](../../../ArkLib\Data\CodingTheory\ProximityGap\BCIKS20\P2MonicWfreeRangeConsumers.lean#L125)
    - a: The global W-free predicate closes the packaged P2 endpoint under monic `H`.
    - b: The global range-indexed W-free predicate closes the packaged P2 endpoint under monic `H`.
- **0.89** `CodingTheory.frs_list_decoding_capacity_cz25_of_coordFiberCap_orderOf_ge_of_cosetSep_eta_eq_one_div_nat_prop` [ArkLib\Data\CodingTheory\ListDecoding\Bounds.lean:2506](../../../ArkLib\Data\CodingTheory\ListDecoding\Bounds.lean#L2506) vs `CodingTheory.frs_list_decoding_capacity_cz25_of_coordFiberCap_orderOf_ge_of_inter_eta_eq_one_div_nat_prop` [ArkLib\Data\CodingTheory\ListDecoding\Bounds\SubspaceDesign.lean:383](../../../ArkLib\Data\CodingTheory\ListDecoding\Bounds\SubspaceDesign.lean#L383)
    - a: Prop-level C3.5 endpoint from coordinate-fiber cap plus the order/coset-separation T2.18 front door,
    - b: Prop-level C3.5 endpoint from coordinate-fiber cap plus the order/inter T2.18 front door, using the

